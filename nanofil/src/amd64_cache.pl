/* Opt-in block-local caching of private integer frame homes in r10/r11.
   This is not instruction selection or general register allocation.
   All eight bytes of a home stay together, even when a read uses only
   its low word. Every alias must be w/l. Pointers, roots, phi shadows,
   local storage and ABI bookkeeping retain their original homes.

   Each region starts and ends with synchronized memory. Calls, control
   flow, frame changes and non-rewritable memory accesses separate regions.
   Loads whose complete destination value is already present are removed
   first; a low-word load still has to zero its destination's high half.
   A linear scan assigns a home's entire first-to-last reference interval;
   every intervening store replaces its cached version. There is no
   eviction: intervals under pressure keep their stack representation.
   The fixed register order and interval order make output deterministic.

   Unknown original forms or explicit uses of the cache bank keep the
   whole implementation unchanged. A translation-check failure is an
   error, never a reason to silently hide an allocator bug. */
:- module(amd64_cache, [cache_asm/5]).
:- use_module(amd64_contract).
:- use_module(amd64_cache_check).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(library(dcgs)).

% Report is stack, excluded(setjmp|unsupported), or cached(Homes,Regions).
% Regions counts regions changed by load removal or an assigned interval.
cache_asm(stack, _, Lines, Lines, stack).
cache_asm(local, Meta, Before, After, Report) :-
    Meta = cache_metadata(Setjmp,Homes),
    ( Setjmp == true -> After = Before, Report = excluded(setjmp)
    ; \+ maplist(audited,Before) -> After = Before, Report = excluded(unsupported)
    ; findall(D-true, (member(home(D,Ks),Homes), Ks = [_|_],
                      maplist(integer_class,Ks)), Pairs),
      list_to_assoc(Pairs,Eligible), length(Pairs,N),
      maplist(classify(Eligible),Before,Classified),
      phrase(regions(Classified,Eligible,Count),After),
      Report = cached(N,Count)
    ),
    ( check_cache(Meta,Before,After) -> true
    ; throw(nanofil_error('scalar stack cache translation check failed')) ).

integer_class(w). integer_class(l).
audited(Line) :-
    once(instruction_effects(Line,_)), explicit_registers(Line,Rs),
    \+ (member(R,Rs), memberchk(R,[r10,r11])).

classify(Eligible,Line,Kind-Line) :-
    once(instruction_effects(Line,effect(_,Writes,_,Memory,Flow))),
    ( Flow == next, \+ memberchk(write(rbp,_),Writes),
      \+ memberchk(write(rsp,_),Writes),
      ( Memory == [] ; home_move(Line,Eligible,_,_) )
    -> Kind = inside
    ; Kind = boundary ).

home_move(ins(mov,q,[reg(R),mem(D,rbp)]),Es,D,write) :-
    get_assoc(D,Es,_), register(R,_,64).
home_move(ins(mov,S,[mem(D,rbp),reg(R)]),Es,D,read) :-
    get_assoc(D,Es,_), move_width(S,W), register(R,_,W).
move_width(q,64). move_width(l,32).

regions([],_,0) --> [].
regions([boundary-L|Ls],Es,N) --> [L], regions(Ls,Es,N).
regions([inside-L|Ls],Es,N) -->
    { region(Ls,More,Rest),
      Region = [L|More], retained_loads(Region,Es,[],Clean),
      region_plan(Clean,Es,Plan),
      ( Clean == Region, empty_assoc(Plan) -> Here = 0 ; Here = 1 ) },
    cached_lines(Clean,Es,Plan,0), regions(Rest,Es,N1),
    { N is N1+Here }.
region([inside-L|Ls],[L|More],Rest) :- !, region(Ls,More,Rest).
region(Rest,[],Rest).

% At most one association per ordinary register: part of a current home,
% and whether the register's upper half is zero. A store invalidates all
% associations with that physical home, even if its temporary has changed.
% This bounded forward analysis is separate from the checker's symbols.
retained_loads([],_,_,[]).
retained_loads([L|Ls],Es,Rs,Out) :-
    ( redundant_load(L,Es,Rs) -> Out = Rest, Next = Rs
    ; Out = [L|Rest], register_contents(L,Es,Rs,Next) ),
    retained_loads(Ls,Es,Next,Rest).

redundant_load(ins(mov,S,[mem(D,rbp),reg(R)]),Es,Rs) :-
    get_assoc(D,Es,_), move_width(S,W), register(R,F,W),
    memberchk(F-content(home(D),Bits,Zero),Rs),
    ( W =:= 64 -> Bits =:= 64 ; Zero == true ).

register_contents(L,Es,Rs,Next) :-
    ( home_move(L,Es,D,write)
    -> L = ins(mov,q,[reg(F),_]),
       contents(F,Rs,content(_,_,Zero)),
       invalidate_home(Rs,D,Fresh),
       replace_contents(F,content(home(D),64,Zero),Fresh,Next)
    ; home_move(L,Es,D,read)
    -> L = ins(mov,S,[_,reg(R)]), move_width(S,W), register(R,F,W),
       ( W =:= 32 -> Zero = true ; Zero = false ),
       replace_contents(F,content(home(D),W,Zero),Rs,Next)
    ; once(instruction_effects(L,effect(_,Writes,_,_,_))),
      written_contents(Writes,Rs,Next) ).

contents(F,Rs,C) :-
    ( memberchk(F-Value,Rs) -> C = Value ; C = content(none,0,false) ).
replace_contents(F,C,Rs,[F-C|Rest]) :-
    ( select(F-_,Rs,Rest) -> true ; Rest = Rs ).
invalidate_home([],_,[]).
invalidate_home([F-content(H,W,Z)|Rs],D,[F-C|Next]) :-
    ( H == home(D) -> C = content(none,0,Z) ; C = content(H,W,Z) ),
    invalidate_home(Rs,D,Next).
written_contents([],Rs,Rs).
written_contents([write(F,W)|Ws],Rs,Next) :-
    ( W =:= 32 -> Zero = true ; Zero = false ),
    replace_contents(F,content(none,0,Zero),Rs,Fresh),
    written_contents(Ws,Fresh,Next).

region_plan(Lines,Es,Plan) :-
    findall(D-(I-Access), (nth0(I,Lines,L), home_move(L,Es,D,Access)), Events),
    keysort(Events,Sorted), group_pairs_by_key(Sorted,Groups),
    findall(Start-span(D,Start,End,First,Dirty),
            (member(D-Uses,Groups), Uses = [Start-First|_],
             last(Uses,End-_), length(Uses,Count),
             ( memberchk(_-write,Uses) -> Dirty = true, Spill = 1
             ; Dirty = false, Spill = 0 ),
             ( First == read -> Fill = 1 ; Fill = 0 ),
             Count > Fill+Spill), Spans),
    keysort(Spans,Ordered),
    assign(Ordered,[r10-(-1),r11-(-1)],Assignments),
    list_to_assoc(Assignments,Plan).

assign([],_,[]).
assign([Start-span(D,Start,End,First,Dirty)|Ss],Bank,Plan) :-
    ( free_register(Bank,Start,End,R,Next)
    -> Plan = [D-entry(R,Start,End,First,Dirty)|Ps]
    ; Next = Bank, Plan = Ps ),
    assign(Ss,Next,Ps).
free_register([R-Until|Rs],Start,End,R,[R-End|Rs]) :- Until < Start, !.
free_register([B|Rs],Start,End,R,[B|Next]) :- free_register(Rs,Start,End,R,Next).

cached_lines([],_,_,_) --> [].
cached_lines([L|Ls],Es,Plan,I) -->
    ( { home_move(L,Es,D,_), get_assoc(D,Plan,entry(R,Start,End,First,Dirty)) }
    -> ( { I =:= Start, First == read }
       -> [ins(mov,q,[mem(D,rbp),reg(R)])] ; [] ),
       { replace_home(L,R,New) }, [New],
       ( { I =:= End, Dirty == true }
       -> [ins(mov,q,[reg(R),mem(D,rbp)])] ; [] )
    ; [L] ),
    { J is I+1 }, cached_lines(Ls,Es,Plan,J).
replace_home(ins(mov,q,[reg(S),mem(_,rbp)]),R,ins(mov,q,[reg(S),reg(R)])).
replace_home(ins(mov,S,[mem(_,rbp),reg(D)]),R,ins(mov,S,[reg(N),reg(D)])) :-
    move_width(S,W), register(N,R,W).

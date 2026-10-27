/* Opt-in whole-function register homes for scalar temporaries
   (`--registers=function`, docs/perf.md item 3, step 3a). A fixed map
   puts frame homes in registers for the whole function: homes live
   across a call in the callee-saved rbx and r12-r15, the others also in
   r10/r11. Accesses stay the moves the reference emits, with a register
   in place of the slot; no instruction is selected differently.

   A home is a candidate when it is a scalar (w/l) home, every access to
   it is a whole move of that home (amd64_regs_check:substitute/3), its
   address is never taken, it is not live at entry, and no 32-bit store
   to it leaves its high half live. Homes interfere when one is written
   while the other is live; a greedy colouring by estimated execution
   count (references weighted by the depth of the backward jumps around
   them) assigns registers. Homes that get none stay in their slots.

   The emitter reserves a save slot per callee-saved register in this
   mode; the registers the map uses are saved after the stack check and
   restored before every leave. amd64_regs_check validates the result;
   a failed check is an error, never a silent fallback. */
:- module(amd64_regs, [regs_asm/5]).
:- use_module(amd64_contract, [instruction_effects/2]).
:- use_module(amd64_regs_check).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).

%! regs_asm(+Metadata, +Before, -After, -Checked, -Report) is det.
%
%  Metadata is regs_metadata(Setjmp, Impl, Homes, Saves) with a save slot
%  for every callee-saved register. Checked is the metadata and map the
%  checker validated: checked(Metadata1, Map). Report is
%  excluded(setjmp|unsupported) or allocated(Homes, Registers).
regs_asm(regs_metadata(Setjmp, Impl, Homes, Saves), Before, After,
         checked(Meta, Map), Report) :-
    empty_assoc(None),
    (   Setjmp == true
    ->  After = Before, Map = [], Used = [], Report = excluded(setjmp)
    ;   \+ ( impl_body(Impl, Before, _, Body),
             findall(S, member(save(_,S), Saves), Ss),
             preflight_regs(Body, None, Ss),
             allocated_stream(Body, None, [], _),
             home_liveness(Body, [], _, _) )
    ->  After = Before, Map = [], Used = [], Report = excluded(unsupported)
    ;   impl_body(Impl, Before, Pre, Body),
        allocation(Body, Homes, Map),
        findall(save(R,S), (member(save(R,S), Saves), memberchk(_-R, Map)), Used),
        (   Map == []
        ->  After = Before
        ;   list_to_assoc(Map, Mapped),
            once(allocated_stream(Body, Mapped, Used, Body1)),
            append(Pre, [label(Impl)|Body1], After)
        ),
        length(Map, NH), length(Used, NR), Report = allocated(NH, NR)
    ),
    Meta = regs_metadata(Setjmp, Impl, Homes, Used),
    (   check_regs(Meta, Map, Before, After) -> true
    ;   throw(nanofil_error('register home translation check failed'))
    ).

% allocation(+Body, +Homes, -Map): Map assigns candidate homes registers.
allocation(Body, Homes, Map) :-
    findall(D, (member(home(D,Ks), Homes), Ks = [_|_],
                forall(member(K,Ks), memberchk(K,[w,l]))), Scalar),
    list_to_assoc_keys(Scalar, ScalarSet),
    depths(Body, Depths),
    foldl(home_refs(ScalarSet), Body, Depths, [], Refs),
    keysort(Refs, Sorted), group_pairs_by_key(Sorted, Groups),
    findall(D-W, ( member(D-Ws, Groups), \+ memberchk(bad, Ws),
                   sum_list(Ws, W) ), Weighted),
    pairs_keys(Weighted, Candidates0),
    (   Candidates0 == []
    ->  Map = []
    ;   home_liveness(Body, Candidates0, Outs, In0),
        numbered(Candidates0, 0, Numbered),
        list_to_assoc(Numbered, Index),
        list_to_assoc(Weighted, Weights),
        foldl(home_facts(Index), Body, Outs, f(0,0)-[], f(Cross,Wide)-Edges),
        Excluded is In0 \/ Wide,
        findall(W-D, ( member(D-K, Numbered), Excluded /\ (3 << (2*K)) =:= 0,
                       get_assoc(D, Weights, W) ), ByWeight0),
        keysort(ByWeight0, Ascending), reverse(Ascending, ByWeight),
        neighbours(Edges, Neighbours),
        findall(K-D, member(D-K, Numbered), Back), list_to_assoc(Back, Owners),
        empty_assoc(Colours0),
        foldl(colour(Index, Owners, Cross, Neighbours), ByWeight, Colours0, Colours),
        assoc_to_list(Colours, Map)
    ).

list_to_assoc_keys(Ks, A) :-
    findall(K-true, member(K, Ks), Ps), list_to_assoc(Ps, A).

numbered([], _, []).
numbered([H|Hs], K, [H-K|Ps]) :- K1 is K+1, numbered(Hs, K1, Ps).

% home_refs(+Scalar, +Line, +Depth, +Refs0, -Refs): each reference to a
% scalar home gives Home-Weight, or Home-bad when the line is not a whole
% move of exactly that home.
home_refs(Scalar, Line, Depth, Refs0, Refs) :-
    findall(H-Ref, line_home_ref(Scalar, Line, Depth, H, Ref), New),
    append(New, Refs0, Refs).

line_home_ref(Scalar, Line, Depth, H, Ref) :-
    rbp_access(Line, D, N),
    H0 is D-7, H1 is D+N-1, between(H0, H1, H), get_assoc(H, Scalar, _),
    (   Line \= ins(lea,_,_), H =:= D, single(H, Map),
        once(substitute(Line, Map, _))
    ->  Ref is 1 << (3 * min(Depth, 5))
    ;   Ref = bad
    ).
line_home_ref(Scalar, ins(lea,_,[mem(D,rbp),_]), _, H, bad) :-
    H0 is D-7, between(H0, D, H), get_assoc(H, Scalar, _).

single(H, Map) :- list_to_assoc([H-rbx], Map).

% depths(+Body, -Depths): for each line, how many backward jumps span it.
depths(Body, Depths) :-
    % GNU as numeric labels repeat; their jumps are short and ignored here.
    findall(L-I, ( nth0(I, Body, label(L)), \+ atom_number(L, _) ), Ls),
    list_to_assoc(Ls, Labels),
    findall(T-I, ( nth0(I, Body, ins(Op,none,[sym(L)])), atom_concat(j, _, Op),
                   get_assoc(L, Labels, T), T < I ), Loops),
    findall(T-1, member(T-_, Loops), Opens),
    findall(E-(-1), (member(_-I, Loops), E is I+1), Closes),
    append(Opens, Closes, Events0), keysort(Events0, Events),
    length(Body, N),
    running(0, N, Events, 0, Depths).

running(I, N, _, _, []) :- I >= N, !.
running(I, N, Events, D0, [D|Ds]) :-
    take_events(Events, I, D0, D, Rest),
    J is I+1, running(J, N, Rest, D, Ds).
take_events([E-X|Es], I, D0, D, Rest) :- E =< I, !,
    D1 is D0+X, take_events(Es, I, D1, D, Rest).
take_events(Es, _, D, D, Es).

% home_facts: homes live across a call (Cross), homes whose 32-bit store
% leaves the high half live (Wide), and the interference edges of each
% write: K-LiveOthers.
home_facts(Index, Line, Out, f(C0,W0)-E0, f(C,W)-E) :-
    (   Line = ins(call,_,_)
    ->  C is C0 \/ Out, W = W0, E = E0
    ;   rbp_access(Line, D, _), Line = ins(mov,S,[_,mem(D,rbp)]),
        get_assoc(D, Index, K)
    ->  C = C0,
        Own is 3 << (2*K),
        ( S == l, Out /\ (2 << (2*K)) =\= 0 -> W is W0 \/ Own ; W = W0 ),
        Others is Out /\ \ Own,
        ( Others =:= 0 -> E = E0 ; E = [K-Others|E0] )
    ;   C = C0, W = W0, E = E0
    ).

% neighbours(+Edges, +Index, -Neighbours): an assoc from home number to
% the bitset of home numbers it interferes with (symmetric).
neighbours(Edges, Neighbours) :-
    findall(K-M, ( member(K-Others, Edges), halves_homes(Others, M) ), Ps0),
    findall(M2-B, ( member(K-M, Ps0), bit_members(M, M2), B is 1 << K ), Ps1),
    findall(K-B, ( member(K-M, Ps0), B = M ), Ps2),
    append(Ps1, Ps2, Ps), keysort(Ps, Sorted), group_pairs_by_key(Sorted, Groups),
    findall(K-All, (member(K-Bs, Groups), foldl(or_int, Bs, 0, All)), Pairs),
    ( Pairs == [] -> empty_assoc(Neighbours) ; list_to_assoc(Pairs, Neighbours) ).

or_int(B, A0, A) :- A is A0 \/ B.

% halves_homes(+Halves, -Homes): the bitset of homes with a half in Halves.
halves_homes(Halves, Homes) :-
    findall(B, (bit_members(Halves, H), K is H >> 1, B is 1 << K), Bs),
    foldl(or_int, Bs, 0, Homes).

bit_members(M, I) :- M > 0, Low is M /\ (-M), I0 is msb(Low),
    ( I = I0 ; Rest is M /\ \ Low, bit_members(Rest, I) ).

colour(Index, Owners, Cross, Neighbours, _-D, Colours0, Colours) :-
    get_assoc(D, Index, K),
    ( Cross /\ (3 << (2*K)) =\= 0
    -> Registers = [rbx,r12,r13,r14,r15]
    ;  Registers = [r10,r11,rbx,r12,r13,r14,r15] ),
    ( get_assoc(K, Neighbours, N) -> true ; N = 0 ),
    findall(R, ( bit_members(N, J), get_assoc(J, Owners, DJ),
                 get_assoc(DJ, Colours0, R) ), Taken),
    (   member(R, Registers), \+ memberchk(R, Taken)
    ->  put_assoc(D, Colours0, R, Colours)
    ;   Colours = Colours0
    ).

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
:- module(amd64_regs, [regs_asm/6]).
:- use_module(amd64_contract, [instruction_effects/2, register/3,
                                explicit_registers/2]).
:- use_module(amd64_regs_check).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).

%! regs_asm(+Mode, +Metadata, +Before, -After, -Checked, -Report) is det.
%
%  Mode is function (step 3a) or operands (3a, then step 3b's operand
%  rewrite). Metadata is regs_metadata(Setjmp, Impl, Homes, Saves) with a
%  save slot for every callee-saved register. Checked is the metadata
%  and map the checker validated: checked(Metadata1, Map). Report is
%  excluded(setjmp|unsupported) or allocated(Homes, Registers).
regs_asm(Mode, regs_metadata(Setjmp, Impl, Homes, Saves), Before, Final,
         checked(Meta, Map), Report) :-
    empty_assoc(None),
    (   Setjmp == true
    ->  After = Before, Map = [], Used = [], Report = excluded(setjmp),
        Analysis = none
    ;   impl_body(Impl, Before, Pre, Body),
        maplist(line_effect, Body, Effects),
        findall(S, member(save(_,S), Saves), Ss),
        preflight_regs(Body, None, Ss, Effects),
        once(allocated_stream(Body, None, [], _)),
        successors(Body, Effects, _)
    ->  allocation(Body, Effects, Homes, Map, Analysis0),
        findall(save(R,S), (member(save(R,S), Saves), memberchk(_-R, Map)), Used),
        (   Map == []
        ->  After = Before
        ;   list_to_assoc(Map, Mapped),
            once(allocated_stream(Body, Mapped, Used, Body1)),
            append(Pre, [label(Impl)|Body1], After)
        ),
        length(Map, NH), length(Used, NR), Report = allocated(NH, NR),
        (   Analysis0 == none, Mode == operands
        ->  body_analysis(Body, Effects, [], Analysis)
        ;   Analysis = Analysis0
        )
    ;   After = Before, Map = [], Used = [], Report = excluded(unsupported),
        Analysis = none
    ),
    Meta = regs_metadata(Setjmp, Impl, Homes, Used),
    (   check_regs(Meta, Map, Before, After, Analysis) -> true
    ;   throw(nanofil_error('register home translation check failed'))
    ),
    (   Mode == operands, Report = allocated(_, _)
    ->  impl_body(Impl, After, PreA, A),
        operand_lives(Analysis, Used, A, Lives),
        operands_rewrite(A, Lives, B),
        (   check_operands(A, B, Lives) -> true
        ;   throw(nanofil_error('register operand translation check failed'))
        ),
        append(PreA, [label(Impl)|B], Final)
    ;   Final = After
    ).

% allocation(+Body, +Effects, +Homes, -Map, -Analysis): Map assigns
% candidate homes registers. Analysis is body_analysis/4's result for
% the candidates (a superset of Map's homes), or none when there are none.
allocation(Body, Effects, Homes, Map, Analysis) :-
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
    ->  Map = [], Analysis = none
    ;   body_analysis(Body, Effects, Candidates0, Analysis),
        Analysis = analysis(_, _, _, _, Outs, In0, _),
        numbered(Candidates0, 0, Numbered),
        list_to_assoc(Numbered, Index),
        list_to_assoc(Weighted, Weights),
        length(Candidates0, NC), HomeBits is (1 << (2*NC)) - 1,
        foldl(home_facts(Index, HomeBits), Body, Outs, f(0,0)-[], f(Cross,Wide)-Edges),
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
% write: K-LiveOthers. HomeBits masks off the analysis's scratch and
% flags bits.
home_facts(Index, HomeBits, Line, Out, f(C0,W0)-E0, f(C,W)-E) :-
    (   Line = ins(call,_,_)
    ->  C is C0 \/ Out, W = W0, E = E0
    ;   rbp_access(Line, D, _), Line = ins(mov,S,[_,mem(D,rbp)]),
        get_assoc(D, Index, K)
    ->  C = C0,
        Own is 3 << (2*K),
        ( S == l, Out /\ (2 << (2*K)) =\= 0 -> W is W0 \/ Own ; W = W0 ),
        Others is Out /\ HomeBits /\ \ Own,
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

%% Step 3b: register operands (docs/perf.md)

/* Untrusted: check_operands/3 validates the result against A. Within
   each region (lines between boundaries), a forward pass propagates
   register and immediate copies into the moves and source operands that
   read them; then moves into dead scratch registers are deleted, a
   scratch result copied into a register is written there directly, and
   dead moves are deleted again. Liveness at a region's end is the
   reference's (operand_lives/4); inside, it is recomputed on the
   rewritten lines. The passes carry each line with its audited effects,
   Line-Effect, so a line's effects are computed once. */

%! operands_rewrite(+A, +Lives, -B) is det.
operands_rewrite(A, Lives, B) :-
    operand_regions(A, Lives, Regions),
    maplist(region_rewrite, Regions, Parts),
    append(Parts, B).

operand_regions([], [], []) :- !.
operand_regions(As, Ls, [region(Lines, End, Boundary)|Rs]) :-
    region_lines(As, Ls, Lines, End, Boundary, As1, Ls1),
    operand_regions(As1, Ls1, Rs).

region_lines([], [], [], 0, [], [], []).
region_lines([L|As], [live(In,_)|Ls], Lines, End, Boundary, As1, Ls1) :-
    line_effect(L, E),
    (   boundary_line(L, E)
    ->  Lines = [], End is In /\ 127, Boundary = [L], As1 = As, Ls1 = Ls
    ;   Lines = [L-E|Lines1],
        region_lines(As, Ls, Lines1, End, Boundary, As1, Ls1)
    ).

region_rewrite(region(Lines, End, Boundary), Out) :-
    empty_assoc(C0),
    forward(Lines, C0, L1),
    dead_moves(L1, End, L2),
    retarget(L2, End, L3),
    dead_moves(L3, End, L4),
    pairs_keys(L4, Ls4),
    append(Ls4, Boundary, Out).

with_effect(L, L-E) :- line_effect(L, E).

% forward(+Lines, +Contents, -Out): Contents maps a register family to
% what it holds: copy(G, W), G's value (W = 64) or its low half
% zero-extended (W = 32), or imm(V), the 64-bit value V.
forward([], _, []).
forward([L-E|Ls], C0, Out) :-
    (   operand_move(L, move(F, Src, W))
    ->  move_content(Src, W, C0, Content),
        forget(F, C0, C1),
        (   Content = copy(F, 64) -> Emit = []
        ;   Src = reg(G), get_assoc(G, C0, _)
        ->  materialize(Content, F, Line), with_effect(Line, LE), Emit = [LE]
        ;   Emit = [L-E]
        ),
        (   ( Content == none ; Content = copy(F, _) ) -> C = C1
        ;   put_assoc(F, C1, Content, C)
        )
    ;   forward_line(L, C0, L1),
        ( L1 == L -> E1 = E ; line_effect(L1, E1) ),
        Emit = [L1-E1], E1 = effect(_,Ws,_,_,_),
        foldl(forget_written, Ws, C0, C)
    ),
    append(Emit, Rest, Out),
    forward(Ls, C, Rest).

move_content(imm(I), W, _, imm(V)) :- V is I mod (1 << W).
move_content(reg(G), W, C0, Content) :-
    (   get_assoc(G, C0, C), renames(G, C) -> compose(C, W, Content)
    ;   memberchk(G, [rsp,rbp]) -> Content = none
    ;   Content = copy(G, W)
    ).

% A home register's name is never replaced by a scratch one: that would
% keep the scratch register live, and its producer unretargeted.
renames(_, imm(_)).
renames(G, copy(H, _)) :- ( scratch_family(H, _) -> scratch_family(G, _) ; true ).

compose(copy(H,W0), W, copy(H,W1)) :- W1 is min(W0, W).
compose(imm(V), W, imm(V1)) :- V1 is V /\ ((1 << W) - 1).

materialize(copy(G,W), F, ins(mov,S,[reg(GN),reg(FN)])) :-
    memberchk(S-W, [l-32,q-64]), register(GN, G, W), register(FN, F, W).
materialize(imm(V), F, Line) :-
    (   V < 1 << 32
    ->  register(FN, F, 32), signed(V, 32, I), Line = ins(mov,l,[imm(I),reg(FN)])
    ;   register(FN, F, 64), signed(V, 64, I),
        (   I >= -(1<<31), I < 1<<31
        ->  Line = ins(mov,q,[imm(I),reg(FN)])
        ;   Line = ins(movabs,q,[imm(I),reg(FN)])
        )
    ).

signed(V, W, I) :- ( V >= 1 << (W-1) -> I is V - (1 << W) ; I = V ).

forget_written(write(F,_), C0, C) :- !, forget(F, C0, C).
forget_written(_, C, C).

% forget(+F, +C0, -C): F changes; drop what it held and every copy of it.
forget(F, C0, C) :-
    assoc_to_list(C0, Ps),
    exclude(depends_on(F), Ps, Kept),
    list_to_assoc(Kept, C).
depends_on(F, F-_).
depends_on(F, _-copy(F,_)).

% forward_line(+L, +C, -L1): source operands that read a copy or an
% immediate read the original; memory operands address through the
% original register. Each replacement must leave an audited form.
forward_line(L, C, L1) :-
    (   L = ins(Op,S,Os), once(operand_roles(Op, S, Roles))
    ->  numbered_list(Os, 1, Ns),
        foldl(forward_operand(C, Op, Roles), Ns, L, L1)
    ;   L1 = L
    ).

numbered_list([], _, []).
numbered_list([O|Os], K, [K-O|Ns]) :- K1 is K+1, numbered_list(Os, K1, Ns).

forward_operand(C, Op, Roles, K-O, L0, L) :-
    nth1(K, Roles, Role),
    (   forwarded(Role, Op, C, O, O1), O1 \== O,
        L0 = ins(Op,S,Os0), replace_nth(K, Os0, O1, Os1), L1 = ins(Op,S,Os1),
        line_effect(L1, E), \+ boundary_line(L1, E)
    ->  L = L1
    ;   L = L0
    ).

forwarded(src(_), Op, C, reg(N), O) :-
    register(N, F, W), W < 128, get_assoc(F, C, Content), renames(F, Content),
    (   Content = copy(G, Wc) -> ( W =< 32 ; Wc =:= 64 ), register(N1, G, W), O = reg(N1)
    ;   Content = imm(V), Op \== btc, imm_for(V, W, I), O = imm(I)
    ).
forwarded(_, _, C, mem(D,B), mem(D,B1)) :- base_original(C, B, B1).
forwarded(_, _, C, mem(D,B,X), mem(D,B1,X1)) :-
    base_original(C, B, B1), base_original(C, X, X1).

base_original(C, B, B1) :-
    (   register(B, F, 64), get_assoc(F, C, copy(G, 64)), renames(F, copy(G, 64))
    ->  register(B1, G, 64)
    ;   B1 = B
    ).

imm_for(V, 64, I) :- signed(V, 64, I), I >= -(1<<31), I < 1<<31.
imm_for(V, 32, I) :- V32 is V /\ 0xffffffff, signed(V32, 32, I).
imm_for(V, 16, I) :- I is V /\ 0xffff.
imm_for(V, 8, I) :- I is V /\ 0xff.

replace_nth(1, [_|Xs], Y, [Y|Xs]) :- !.
replace_nth(K, [X|Xs], Y, [X|Ys]) :- K1 is K-1, replace_nth(K1, Xs, Y, Ys).

% dead_moves(+Lines, +End, -Out): moves into scratch registers dead
% after them are deleted.
dead_moves(Lines, End, Out) :-
    reverse(Lines, Rev),
    foldl(dead_move, Rev, End-[], _-Out).
dead_move(L-E, Live0-Acc, Live-Acc1) :-
    (   operand_move(L, move(F,_,_)), scratch_family(F, Bit), Live0 /\ (1 << Bit) =:= 0
    ->  Live = Live0, Acc1 = Acc
    ;   live_before(L-E, Live0, Live), Acc1 = [L-E|Acc]
    ).

live_before(L-E, Out, In) :-
    extra_use_def(L, E, U, D),
    In is (U \/ (Out /\ \ D)) /\ 127.

% live_after(+Lines, +End, -Pairs): each line with the scratch families
% live after it.
live_after(Lines, End, Pairs) :-
    reverse(Lines, Rev),
    foldl(after_pair, Rev, End-[], _-Pairs).
after_pair(L, Out-Acc, In-[L-Out|Acc]) :- live_before(L, Out, In).

% retarget(+Lines, +End, -Out): a scratch result copied into a register
% H is written to H.
retarget(Lines, End, Out) :-
    live_after(Lines, End, Pairs),
    retarget_pairs(Pairs, Out).

retarget_pairs([], []).
retarget_pairs([(L1-_)-_, (L2-_)-_, L3-A3|Ps], Out) :-
    copy_outs([L3-A3|Ps], L2, Outs, A, Ps1),
    two_address(L1, L2, Outs, A, New), !,
    maplist(with_effect, New, NewLEs),
    append(NewLEs, Out1, Out), retarget_pairs(Ps1, Out1).
retarget_pairs([(L1-_)-_, L2-A2|Ps], Out) :-
    copy_outs([L2-A2|Ps], L1, Outs, A, Ps1),
    direct_result(L1, Outs, A, New), !,
    maplist(with_effect, New, NewLEs),
    append(NewLEs, Out1, Out), retarget_pairs(Ps1, Out1).
retarget_pairs([LE-_|Ps], [LE|Out]) :- retarget_pairs(Ps, Out).

% copy_outs(+Pairs, +Producer, -Moves, -After, -Rest): the moves that
% follow, each copying the producer's last operand register (S) into
% another one, and the scratch set live after the last. The later moves
% read the first one's destination H instead, so none may write H.
copy_outs(Pairs, ins(_,_,Os), [M|Ms], After, Rest) :-
    last(Os, reg(N)), register(N, S, _),
    Pairs = [(M-_)-A0|Ps], operand_move(M, move(H, reg(S), _)), H \== S,
    more_copy_outs(Ps, S, H, Ms, A0, After, Rest).
more_copy_outs([(M-_)-A|Ps], S, H, [M|Ms], _, After, Rest) :-
    operand_move(M, move(D, reg(S), _)), D \== S, D \== H, !,
    more_copy_outs(Ps, S, H, Ms, A, After, Rest).
more_copy_outs(Ps, _, _, [], After, After, Ps).

% The later copies, reading H at their width.
copies_from(H, Ms, New) :- maplist(copy_from(H), Ms, New).
copy_from(H, ins(mov,Sz,[reg(_),reg(D)]), ins(mov,Sz,[reg(HN),reg(D)])) :-
    memberchk(Sz-W, [l-32,q-64]), register(HN, H, W).

% mov Src,%S; op X,%S; mov %S,%H  ->  mov Src,%H; op X,%H
two_address(L1, L2, [L3|More], A3, New) :-
    operand_move(L1, move(S, Src, W1)), scratch_family(S, Bit),
    L2 = ins(Op,Sz,Os), memberchk(Op, [add,sub,and,or,xor,imul,neg,shl,shr,sar]),
    once(operand_roles(Op, Sz, Roles)), nth1(K, Roles, srcdst(W)),
    memberchk(W, [32,64]), nth1(K, Os, reg(N)), register(N, S, W),
    operand_move(L3, move(H, reg(S), W3)), H \== S,
    ( W3 =:= W ; W =:= 32 ),
    A3 /\ (1 << Bit) =:= 0,
    explicit_registers(L2, Rs),
    \+ memberchk(H, Rs),
    selectchk(S, Rs, Others), \+ memberchk(S, Others),
    register(HN, H, W), replace_nth(K, Os, reg(HN), Os1), L2a = ins(Op,Sz,Os1),
    line_effect(L2a, E), \+ boundary_line(L2a, E),
    copies_from(H, More, Copies),
    (   Src == reg(H), ( W1 =:= 64 ; W =:= 32 )
    ->  New = [L2a|Copies]
    ;   Src = reg(G) -> materialize(copy(G, W1), H, L1a), New = [L1a, L2a|Copies]
    ;   L1 = ins(Mv,Sz1,[imm(I),_]), register(HN1, H, W1),
        New = [ins(Mv,Sz1,[imm(I),reg(HN1)]), L2a|Copies]
    ).

% op ...,%S; mov %S,%H  ->  op ...,%H, for a form whose last operand is a
% pure 32- or 64-bit destination.
direct_result(L1, [L2|More], A2, [L|Copies]) :-
    L1 = ins(Op,Sz,Os), \+ operand_move(L1, _),
    line_effect(L1, E1), \+ boundary_line(L1, E1),
    once(operand_roles(Op, Sz, Roles)), last(Roles, dst(_)), last(Os, reg(N)),
    register(N, S, Wop), memberchk(Wop, [32,64]), scratch_family(S, Bit),
    operand_move(L2, move(H, reg(S), Wc)), H \== S,
    ( Wc =:= Wop ; Wop =:= 32 ),
    A2 /\ (1 << Bit) =:= 0,
    register(HN, H, Wop), append(Front, [_], Os), append(Front, [reg(HN)], Os1),
    L = ins(Op,Sz,Os1), line_effect(L, E), \+ boundary_line(L, E),
    copies_from(H, More, Copies).

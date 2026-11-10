/* Whole-function register homes for scalar temporaries (docs/perf.md
   item 3, step 3a), with step 3b's operand rewrite and 5a-loads' frame
   cells: `--registers=temps`, and `--registers=pointers`, the -O default. A fixed map
   puts frame homes in registers for the whole function: homes live
   across a call in the callee-saved rbx and r12-r15, the others also in
   r10/r11. Accesses stay the moves the reference emits, with a register
   in place of the slot; no instruction is selected differently.

   A home is a candidate when it is a scalar (w/l) home, or under
   pointers a pointer's address word (class a), every access to
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
                                explicit_registers/2, preserving_call/1]).
:- use_module(amd64_regs_check).
:- use_module(list_partition).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).

%! regs_asm(+Mode, +Metadata, +Before, -After, -Checked, -Report) is det.
%
%  Mode is map (3a's map alone, unchecked, for a layout choice; Final
%  is then not to be emitted) or frame(Cells) (step 3a, then step 3b's
%  operand rewrite with the frame cells of docs/perf.md 5a-loads). Metadata is regs_metadata(Setjmp, Impl, Homes, Saves) with a
%  save slot for every callee-saved register. Checked is the metadata
%  and map the checker validated: checked(Metadata1, Map). Report is
%  excluded(setjmp|unsupported) or allocated(Homes, Registers).
regs_asm(map, regs_metadata(Setjmp, Impl, Homes, _), Before, Before,
         checked(none, Map), map) :- !,
    % Map mode only proposes the map, for a layout choice (temps mode's
    % first lowering): its stream is never emitted, so neither the
    % preflight nor the checker runs. A body the real run would exclude
    % still gets one; the run on the final layout excludes it.
    (   Setjmp \== true, impl_body(Impl, Before, _, Body0),
        maplist(line_effect, Body0, Effects0),
        home_lines(Body0, Effects0, Body, Effects),
        allocation(Body, Effects, Homes, Map, _)
    ->  true
    ;   Map = []
    ).

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
        (   Analysis0 == none
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
    (   operand_cells(Mode, Cells0), Report = allocated(_, _)
    ->  impl_body(Impl, After, PreA, A),
        (   operand_lives(Analysis, Map, Used, A, Lives) -> true
        ;   throw(nanofil_error('register operand liveness failed'))
        ),
        valid_cells(Cells0, A, Cells),
        findall(R, member(save(R,_), Used), Saved),
        append([rax,rcx,rdx,rsi,rdi,r8,r9,r10,r11], Saved, Usable),
        (   operand_selection(regions)
        ->  alloc_rewrite(A, Lives, Cells, Usable, B)
        ;   operands_rewrite(A, Lives, Cells, B)
        ),
        (   check_operands(A, B, Lives, Cells0) -> true
        ;   throw(nanofil_error('register operand translation check failed'))
        ),
        append(PreA, [label(Impl)|B], Final)
    ;   Final = After
    ).

% home_lines(+Body0, +Effects0, -Body, -Effects): the lines the map
% depends on: labels, control flow, calls, and lines with a memory
% operand or a lea. A line left out falls through and touches no home,
% so home liveness, interference, loop depths and references are the
% same as on the whole body; only scratch and flags liveness, which the
% allocation masks off, differ.
home_lines([], [], [], []).
home_lines([L|Ls], [E|Es], Body, Effects) :-
    E = effect(_,_,_,Ms,Flow),
    (   Ms == [], memberchk(Flow, [next,frame,directive]),
        L \= ins(lea,_,_), L \= ins(call,_,_)
    ->  Body = Body1, Effects = Effects1
    ;   Body = [L|Body1], Effects = [E|Effects1]
    ),
    home_lines(Ls, Es, Body1, Effects1).

% allocation(+Body, +Effects, +Homes, -Map, -Analysis): Map assigns
% candidate homes registers. Analysis is body_analysis/4's result for
% the candidates (a superset of Map's homes), or none when there are none.
allocation(Body, Effects, Homes, Map, Analysis) :-
    findall(D, (member(home(D,Ks), Homes), Ks = [_|_],
                forall(member(K,Ks), memberchk(K,[w,l,a]))), Scalar),
    findall(W-H, ( member(H, Scalar), W is H >> 3 ), WHs0),
    keysort(WHs0, WHs), group_pairs_by_key(WHs, Words), list_to_assoc(Words, ScalarSet),
    depths(Body, Depths),
    foldl(home_refs(ScalarSet), Body, Effects, Depths, [], Refs),
    keysort(Refs, Sorted), group_pairs_by_key(Sorted, Groups),
    findall(D-W, ( member(D-Ws, Groups), \+ memberchk(bad, Ws),
                   sum_list(Ws, W) ), Weighted),
    length(Body, NL),
    heaviest(Weighted, NL, Candidates0),
    (   Candidates0 == []
    ->  Map = [], Analysis = none
    ;   body_analysis(Body, Effects, Candidates0, Analysis),
        Analysis = analysis(_, _, _, _, Outs, In0, _),
        numbered(Candidates0, 0, Numbered),
        list_to_assoc(Numbered, Index),
        list_to_assoc(Weighted, Weights),
        length(Candidates0, NC), HomeBits is ((1 << (2*NC)) - 1) << 8,
        empty_assoc(Rows0),
        foldl(home_facts(Index, HomeBits), Body, Outs, f(0,0)-Rows0, f(Cross,Wide)-Rows),
        Excluded is In0 \/ Wide,
        findall(W-D, ( member(D-K, Numbered), home_shift(K, S), Excluded /\ (3 << S) =:= 0,
                       get_assoc(D, Weights, W) ), ByWeight0),
        keysort(ByWeight0, Ascending), reverse(Ascending, ByWeight),
        empty_assoc(Colours0),
        findall(R-taken(0,0), member(R, [r10,r11,rbx,r12,r13,r14,r15]), Taken0),
        foldl(colour(Index, Cross, Rows), ByWeight, Colours0-Taken0, Colours-_),
        assoc_to_list(Colours, Map)
    ).

numbered([], _, []).
numbered([H|Hs], K, [H-K|Ps]) :- K1 is K+1, numbered(Hs, K1, Ps).

% heaviest(+Weighted, +Lines, -Candidates): the homes of Weighted (D-W,
% by offset) that the allocator considers, by offset. The liveness sets
% cost a bit per candidate half per line, so a function whose candidates
% times lines exceeds the budget (2^29 bits, a 64 MB set) keeps only its
% heaviest homes, ties going to the lower offset. At most seven
% registers go round, so the light ones seldom get one anyway. No bench
% function reaches the budget (sqlite3VdbeExec, the largest, is at 0.68);
% netcdf's tst_h_atts.c main (14156 homes, 285k lines) and openssh's
% libcrux (3054, 116k) do.
heaviest(Weighted, Lines, Candidates) :-
    length(Weighted, N), Cap is max(256, (1 << 29) // max(1, 2*Lines)),
    (   N =< Cap
    ->  pairs_keys(Weighted, Candidates)
    ;   findall(NW-D, (member(D-W, Weighted), NW is -W), ByWeight0),
        keysort(ByWeight0, ByWeight), length(Top, Cap), append(Top, _, ByWeight),
        pairs_values(Top, Ds), msort(Ds, Candidates)
    ).

% home_refs(+Scalar, +Line, +Effect, +Depth, +Refs0, -Refs): each
% reference to a scalar home gives Home-Weight, or Home-bad when the line
% is not a whole move of exactly that home.
home_refs(Scalar, Line, effect(_,_,_,Ms,_), Depth, Refs0, Refs) :-
    (   Ms == [], Line \= ins(lea,_,_)
    ->  Refs = Refs0
    ;   findall(H-Ref, line_home_ref(Scalar, Line, Ms, Depth, H, Ref), New),
        append(New, Refs0, Refs)
    ).

% scalar_home(+Words, +H0, +H1, -H): a scalar home H within H0..H1;
% Words buckets the homes by 8-byte word.
scalar_home(Words, H0, H1, H) :-
    W0 is H0 >> 3, W1 is H1 >> 3, between(W0, W1, W),
    get_assoc(W, Words, Hs), member(H, Hs), H >= H0, H =< H1.

line_home_ref(Scalar, Line, Ms, Depth, H, Ref) :-
    effect_access(Ms, D, N),
    H0 is D-7, H1 is D+N-1, scalar_home(Scalar, H0, H1, H),
    (   Line \= ins(lea,_,_), H =:= D, single(H, Map),
        once(substitute(Line, Map, _))
    ->  Ref is 1 << (3 * min(Depth, 5))
    ;   Ref = bad
    ).
line_home_ref(Scalar, ins(lea,_,[mem(D,rbp),_]), _, _, H, bad) :-
    H0 is D-7, scalar_home(Scalar, H0, D, H).

single(H, Map) :- empty_assoc(E), put_assoc(H, E, rbx, Map).

% depths(+Body, -Depths): for each line, how many backward jumps span it.
depths(Body, Depths) :-
    % GNU as numeric labels repeat; their jumps are short and ignored here.
    findall(L-I, ( nth0(I, Body, label(L)), \+ numeric_label(L) ), Ls),
    list_to_assoc(Ls, Labels),
    findall(T-I, ( nth0(I, Body, ins(Op,none,[sym(L)])), atom_concat(j, _, Op),
                   get_assoc(L, Labels, T), T < I ), Loops),
    findall(T-1, member(T-_, Loops), Opens),
    findall(E-(-1), (member(_-I, Loops), E is I+1), Closes),
    append(Opens, Closes, Events0), keysort(Events0, Events),
    length(Body, N),
    running(0, N, Events, 0, Depths).

% Numeric GNU as labels are nonempty decimal digit sequences, not
% arbitrary Prolog numbers. Trealla's atom_number/2 throws on symbols.
numeric_label(L) :-
    atom_codes(L, [C|Cs]),
    forall(member(D, [C|Cs]), (D >= 0'0, D =< 0'9)).

running(I, N, _, _, []) :- I >= N, !.
running(I, N, Events, D0, [D|Ds]) :-
    take_events(Events, I, D0, D, Rest),
    J is I+1, running(J, N, Rest, D, Ds).
take_events([E-X|Es], I, D0, D, Rest) :- E =< I, !,
    D1 is D0+X, take_events(Es, I, D1, D, Rest).
take_events(Es, _, D, D, Es).

% home_facts: homes live across a call (Cross), homes whose 32-bit store
% leaves the high half live (Wide), and each home's interference row:
% an assoc from home number K to the halves live at any write of K,
% K's own excluded. HomeBits masks off the analysis's scratch and flags
% bits.
home_facts(Index, HomeBits, Line, Out, f(C0,W0)-E0, f(C,W)-E) :-
    (   Line = ins(call,_,_), \+ preserving_call(Line)
    ->  C is C0 \/ Out, W = W0, E = E0
    ;   Line = ins(mov,S,[_,mem(D,rbp)]), rbp_access(Line, D, _),
        get_assoc(D, Index, K)
    ->  C = C0,
        home_shift(K, Sh), Own is 3 << Sh,
        ( S == l, Out /\ (2 << Sh) =\= 0 -> W is W0 \/ Own ; W = W0 ),
        Others is Out /\ xor(HomeBits, HomeBits /\ Own),
        (   Others =:= 0 -> E = E0
        ;   ( get_assoc(K, E0, Row0) -> true ; Row0 = 0 ),
            Row is Row0 \/ Others, put_assoc(K, E0, Row, E)
        )
    ;   C = C0, W = W0, E = E0
    ).

% colour(+Index, +Cross, +Rows, +W-D, +Colours0-Taken0, -Colours-Taken):
% home D gets the first register of its list that no interfering home
% has. Homes J and K interfere when one's row has a half of the other.
% Taken holds, per register, the halves of the homes it was given and
% the union of their rows, so neither direction lists pairs: those are
% quadratic in the homes (netcdf's tst_h_atts.c had 12 million).
colour(Index, Cross, Rows, _-D, Colours0-Taken0, Colours-Taken) :-
    get_assoc(D, Index, K), home_shift(K, S), Own is 3 << S,
    ( Cross /\ Own =\= 0
    -> Registers = [rbx,r12,r13,r14,r15]
    ;  Registers = [r10,r11,rbx,r12,r13,r14,r15] ),
    ( get_assoc(K, Rows, Row) -> true ; Row = 0 ),
    (   member(R, Registers), memberchk(R-taken(Set, Union), Taken0),
        Row /\ Set =:= 0, Union /\ Own =:= 0
    ->  put_assoc(D, Colours0, R, Colours),
        Set1 is Set \/ Own, Union1 is Union \/ Row,
        give(Taken0, R, taken(Set1, Union1), Taken)
    ;   Colours = Colours0, Taken = Taken0
    ).

give([R0-T0|Ts0], R, T, Ts) :-
    (   R0 == R -> Ts = [R-T|Ts0]
    ;   Ts = [R0-T0|Ts1], give(Ts0, R, T, Ts1)
    ).

%% Step 3b: register operands (docs/perf.md)

/* Untrusted: check_operands/3 validates the result against A. Within
   each region (lines between boundaries), a forward pass propagates
   register and immediate copies into the moves and source operands that
   read them; then moves into dead scratch registers are deleted, a
   scratch result copied into a register is written there directly, and
   dead moves are deleted again. Liveness at a region's end is the
   reference's (operand_lives/4); inside, it is recomputed on the
   rewritten lines. The passes carry each line as Line-inf(Effect, Use,
   Def, Move): its audited effects, the scratch and flags sets it uses
   and defines, and its operand_move/2 reading or none, computed once. */

% operand_cells(+Mode, -Cells): the frame cells whose loads the rewrite
% may forward, the emitter's (docs/perf.md, 5a-loads).
operand_cells(frame(Cells), Cells).

%! operands_rewrite(+A, +Lives, +Cells, -B) is det.
operands_rewrite(A, Lives, Cells, B) :-
    operand_regions(A, Lives, Regions),
    maplist(region_rewrite(Cells), Regions, Parts),
    append(Parts, B).

operand_regions([], [], []) :- !.
operand_regions(As, Ls, [region(Lines, End, Boundary)|Rs]) :-
    region_lines(As, Ls, Lines, End, Boundary, As1, Ls1),
    operand_regions(As1, Ls1, Rs).

region_lines([], [], [], 0, [], [], []).
region_lines([L|As], [live(In,_,E)|Ls], Lines, End, Boundary, As1, Ls1) :-
    (   boundary_line(L, E)
    ->  Lines = [], End is In /\ 127, Boundary = [L], As1 = As, Ls1 = Ls
    ;   effect_info(L, E, I), Lines = [L-I|Lines1],
        region_lines(As, Ls, Lines1, End, Boundary, As1, Ls1)
    ).

region_rewrite(Cells, region(Lines0, End, Boundary), Out) :-
    empty_assoc(C0),
    (   empty_assoc(Cells) -> Lines = Lines0
    ;   cell_forward(Lines0, Cells, C0, Lines)
    ),
    forward(Lines, C0, L1),
    dead_moves(L1, End, L2),
    retarget(L2, End, L3),
    dead_moves(L3, End, L4),
    pairs_keys(L4, Ls4),
    append(Ls4, Boundary, Out).

with_effect(L, L-I) :- line_effect(L, E), effect_info(L, E, I).

% cell_forward(+Lines, +Cells, +Held, -Out): a load of a cell that a
% register still holds whole (Held maps the cell to the register family
% that loaded or stored it, unchanged since) reads that register
% instead. forward/3 then propagates the copy like any other.
cell_forward([], _, _, []).
cell_forward([L-I|Ls], Cells, H0, Out) :-
    (   L = ins(mov,S,[mem(D,rbp),reg(Y)]), get_assoc(D, Cells, _),
        memberchk(S-W, [l-32,q-64]), register(Y, F, W), \+ memberchk(F, [rsp,rbp])
    ->  (   get_assoc(D, H0, G)
        ->  (   S == q, G == F -> Emit = [], H = H0
            ;   register(GN, G, W), L1 = ins(mov,S,[reg(GN),reg(Y)]),
                with_effect(L1, LE), Emit = [LE], drop_held(F, H0, H)
            )
        ;   Emit = [L-I], drop_held(F, H0, H1),
            ( S == q -> put_assoc(D, H1, F, H) ; H = H1 )
        )
    ;   L = ins(mov,q,[reg(X),mem(D,rbp)]), get_assoc(D, Cells, _),
        register(X, G, 64), \+ memberchk(G, [rsp,rbp])
    ->  Emit = [L-I], put_assoc(D, H0, G, H)
    ;   Emit = [L-I], I = inf(effect(_,Ws,_,Ms,_),_,_,_),
        foldl(drop_written, Ws, H0, H1),
        foldl(drop_stored, Ms, H1, H)
    ),
    append(Emit, Rest, Out),
    cell_forward(Ls, Cells, H, Rest).

% drop_held(+F, +H0, -H): F changes; no cell is held in it any more.
drop_held(F, H0, H) :-
    assoc_to_list(H0, Ps),
    (   memberchk(_-F, Ps) -> exclude(held_in(F), Ps, Kept), list_to_assoc(Kept, H)
    ;   H = H0
    ).
held_in(F, _-G) :- G == F.
drop_written(write(F,_), H0, H) :- !, drop_held(F, H0, H).
drop_written(_, H, H).
% A store overlapping a cell drops it.
drop_stored(write(mem(D0,rbp),N), H0, H) :- !,
    assoc_to_list(H0, Ps),
    (   member(P, Ps), overlaps(D0, N, P)
    ->  exclude(overlaps(D0, N), Ps, Kept), list_to_assoc(Kept, H)
    ;   H = H0
    ).
drop_stored(_, H, H).
overlaps(D0, N, D-_) :- D < D0+N, D0 < D+8.

effect_info(L, E, inf(E, U, D, M)) :-
    extra_use_def(L, E, U, D),
    ( operand_move(L, M0) -> M = M0 ; M = none ).

% forward(+Lines, +Contents, -Out): Contents maps a register family to
% what it holds: copy(G, W), G's value (W = 64) or its low half
% zero-extended (W = 32), or imm(V), the 64-bit value V.
forward([], _, []).
forward([L-I|Ls], C0, Out) :-
    (   I = inf(_,_,_,move(F, Src, W))
    ->  move_content(Src, W, C0, Content),
        forget(F, C0, C1),
        (   Content = copy(F, 64) -> Emit = []
        ;   Src = reg(G), get_assoc(G, C0, _)
        ->  materialize(Content, F, Line), with_effect(Line, LE), Emit = [LE]
        ;   Emit = [L-I]
        ),
        (   ( Content == none ; Content = copy(F, _) ) -> C = C1
        ;   put_assoc(F, C1, Content, C)
        )
    ;   forward_line(L, C0, L1),
        ( L1 == L -> I1 = I ; with_effect(L1, L1-I1) ),
        Emit = [L1-I1], I1 = inf(effect(_,Ws,_,_,_),_,_,_),
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
forget(_, C0, C) :- empty_assoc(C0), !, C = C0.
forget(F, C0, C) :-
    assoc_to_list(C0, Ps),
    (   member(P, Ps), depends_on(F, P)
    ->  exclude(depends_on(F), Ps, Kept), list_to_assoc(Kept, C)
    ;   C = C0
    ).
depends_on(F, F-_).
depends_on(F, _-copy(F,_)).

% forward_line(+L, +C, -L1): source operands that read a copy or an
% immediate read the original; memory operands address through the
% original register. Each replacement must leave an audited form.
forward_line(L, C, L1) :-
    (   \+ empty_assoc(C), L = ins(Op,S,Os), once(operand_roles(Op, S, Roles))
    ->  forward_operands(Roles, Os, 1, C, Op, L, L1)
    ;   L1 = L
    ).

forward_operands([], _, _, _, _, L, L).
forward_operands([Role|Roles], [O|Os], K, C, Op, L0, L) :-
    (   forwarded(Role, Op, C, O, O1), O1 \== O,
        L0 = ins(Op,S,Os0), replace_nth(K, Os0, O1, Os1), L1 = ins(Op,S,Os1),
        line_effect(L1, E), \+ boundary_line(L1, E)
    ->  true
    ;   L1 = L0
    ),
    K1 is K+1,
    forward_operands(Roles, Os, K1, C, Op, L1, L).

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
dead_move(L-I, Live0-Acc, Live-Acc1) :-
    (   I = inf(_,_,_,move(F,_,_)), scratch_family(F, Bit), Live0 /\ (1 << Bit) =:= 0
    ->  Live = Live0, Acc1 = Acc
    ;   live_before(L-I, Live0, Live), Acc1 = [L-I|Acc]
    ).

live_before(_-inf(_,U,D,_), Out, In) :-
    In is (U \/ xor(Out, Out /\ D)) /\ 127.

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

%% Region allocation (docs/perf.md item 19, lever 1)

%! operand_selection(-Selection) is det.
%
%  Selection is how operands are chosen after step 3a (main.pl's
%  --operands=, NANOFIL_OPERANDS): rewrite, step 3b's copy forwarding,
%  or regions, the default, alloc_rewrite/5.
operand_selection(S) :-
    (   getenv('NANOFIL_OPERANDS', S0), memberchk(S0, [rewrite, regions]) -> S = S0
    ;   S = regions
    ).

/* Untrusted, like step 3b's rewrite, and validated by the same
   check_operands/4. Within a region, A's moves are not executed at all:
   the checker only needs B's paired lines to read A's values and B's
   registers to hold A's at the region's end where they are live. So
   each region is allocated again from A's symbolic values, computed by
   the checker's own step relations (paired/7, move_state/3):

   - every paired line's register operands read any register that holds
     A's value, or an immediate where A's form takes one;
   - a destination is the register where the result is needed at the
     region's end, else A's register, else any register whose value is
     not needed after the line (a value is needed while a later line or
     the region's end reads it and no other register holds it);
   - a two-address destination is a register that already holds the
     input and can be overwritten, or gets a copy of it first;
   - lines this does not model (division, partial register writes, SSE,
     shifts by %cl, setcc) keep A's registers, which first get A's
     values;
   - at the region's end, live registers get A's values by a parallel
     move.

   Home registers are free inside a region and dead ones at its end
   too (operand_lives/5). Moves are the only lines it inserts, so the
   flags are never touched. A region it cannot allocate, or allocates
   into more lines than step 3b's rewrite, gets step 3b's rewrite. */

%! alloc_rewrite(+A, +Lives, +Cells, +Usable, -B) is det.
%
%  B is the implementation body A with each region allocated again
%  (above). Lives are operand_lives/5's sets for A's lines, Cells the
%  valid frame cells, Usable the registers B may write: the scratch
%  families, r10, r11 and the callee-saved registers the map saves.
alloc_rewrite(A, Lives, Cells, Usable, B) :-
    shared_state(S0),
    empty_assoc(None),
    alloc_regions(A, Lives, env(S0, Cells, None), Usable, shared, B).

alloc_regions([], [], _, _, _, []) :- !.
alloc_regions(As, Ls, Env, Usable, Start, Out) :-
    region_split(As, Ls, Lines, LLs, Bound, As1, Ls1),
    (   Bound = [BL-live(In,BOut,BE)]
    ->  End = In, Bs = [BL],
        ( no_fallthrough(BL, BE) -> Start1 = none ; Start1 = live(BOut) )
    ;   End = 0, Bs = [], Start1 = none
    ),
    region_choice(Start, Lines, LLs, End, Env, Usable, New),
    append(New, Bs, Part), append(Part, Rest, Out),
    alloc_regions(As1, Ls1, Env, Usable, Start1, Rest).

region_split([], [], [], [], [], [], []).
region_split([L|As], [Lv|Ls], Lines, LLs, Bound, As1, Ls1) :-
    Lv = live(_,_,E),
    (   boundary_line(L, E)
    ->  Lines = [], LLs = [], Bound = [L-Lv], As1 = As, Ls1 = Ls
    ;   Lines = [L|Lines1], LLs = [Lv|LLs1],
        region_split(As, Ls, Lines1, LLs1, Bound, As1, Ls1)
    ).

% region_choice(+Start, +Lines, +LLs, +End, +Env, +Usable, -New):
% unreachable lines stay, and so does a region without moves (nothing to
% remove); otherwise the allocation, unless it fails or step 3b's
% rewrite is shorter. An allocation of only A's paired lines is
% shortest, so the rewrite is not built for it.
region_choice(none, Lines, _, _, _, _, Lines) :- !.
region_choice(Start, Lines, LLs, End, Env, Usable, New) :-
    Env = env(S0, Cells, _),
    include(move_like, Lines, Moves), length(Moves, NM),
    (   NM =:= 0
    ->  New = Lines
    ;   start_states(Start, S0, SA, SB),
        once(alloc_region(Lines, LLs, End, Env, Usable, SA, SB, Alloc))
    ->  length(Alloc, NA), length(Lines, NL),
        (   NA =< NL - NM
        ->  New = Alloc
        ;   region_rewrite_of(Cells, Lines, LLs, End, Old), length(Old, NO),
            ( NA =< NO -> New = Alloc ; New = Old )
        )
    ;   region_rewrite_of(Cells, Lines, LLs, End, New)
    ).

region_rewrite_of(Cells, Lines, LLs, End, Out) :-
    maplist(live_info, Lines, LLs, Infos),
    End3b is End /\ 127,
    region_rewrite(Cells, region(Infos, End3b, []), Out).

% move_like(+Line): a register or immediate move, or a load from the
% frame, which a cell may make one.
move_like(L) :- operand_move(L, _), !.
move_like(ins(mov,S,[mem(_,rbp),reg(_)])) :- memberchk(S, [l,q]).

live_info(L, live(_,_,E), L-I) :- effect_info(L, E, I).

start_states(shared, S0, S0, S0).
start_states(live(Out), S0, SA, SB) :- region_start(Out, S0, SA, SB).

alloc_region(Lines, LLs, End, Env, Usable, SA0, SB0, Out) :-
    empty_assoc(CS0),
    a_sim(Lines, LLs, Env, SA0, CS0, 0, Ps0, SAend, CSend),
    Flags0 is End /\ 128,
    flags_after(Ps0, Flags0, Ps),
    end_targets(End, SAend, Targets),
    empty_assoc(Cnt00),
    foldl(count_line, Ps, Cnt00, Cnt01),
    foldl(count_target, Targets, Cnt01, Cnt0),
    Ctx = ctx(Usable, Env, Targets),
    b_walk(Ps, Ctx, SB0, Cnt0, Out, Tail, SB1, Cnt1),
    resolve(Targets, Ctx, CSend, Cnt1, SB1, _, Tail, []).

% a_sim: A's region on the checker's symbolic values. Each paired line
% is p(J, Line, Effect, Mode, Pre, Post, Cells, Demands, FlagsLive), the
% last bound by flags_after/3.
a_sim([], [], _, SA, CS, _, [], SA, CS).
a_sim([L|Ls], [live(_,_,E)|LLs], Env, SA, CS, J, Ps, SAe, CSe) :-
    (   stream_move(L, Env, CS, M)
    ->  move_state(M, SA, SA1), CS1 = CS, J1 = J, Ps = Ps1
    ;   paired(L, L, J, SA, SA, SA1, _),
        Env = env(_, Cells, _),
        cell_writes(E, L, J, SA, Cells, CS, CS1),
        line_mode(L, Mode),
        line_demands(Mode, L, E, SA, Ds),
        Ps = [p(J, L, E, Mode, SA, SA1, CS, Ds, _)|Ps1], J1 is J+1
    ),
    a_sim(Ls, LLs, Env, SA1, CS1, J1, Ps1, SAe, CSe).

% The registers B may hold values in, in the order they are tried.
gprs([rax,rcx,rdx,rsi,rdi,r8,r9,r10,r11,rbx,r12,r13,r14,r15]).

end_targets(End, st(R,_,_), Targets) :-
    gprs(Gs),
    findall(F-V, ( member(F, Gs), alloc_live_bit(F, Bit), End /\ (1 << Bit) =\= 0,
                   reg_get(F, R, V) ), Targets).

alloc_live_bit(F, Bit) :- scratch_family(F, Bit).
alloc_live_bit(F, Bit) :- home_register_bit(F, Bit).

% line_mode(+Line, -Mode): flex(Roles) when every register operand is a
% general register other than rsp and rbp, every register destination
% is written whole (32 or 64 bits) and the form has no implicit or
% fixed register; otherwise fixed.
line_mode(ins(Op,S,[reg(X),reg(X)]), zero(W)) :-
    memberchk(Op, [xor,sub]), memberchk(S-W, [l-32,q-64]),
    register(X, F, W), \+ memberchk(F, [rsp,rbp]), !.
line_mode(ins(Op,S,Os), flex(Roles)) :-
    \+ memberchk(Op, [div,idiv,cltd,cqto,'lock cmpxchg',btc,mfence,movd,movq,
                      ucomiss,ucomisd,cvtss2sd,cvtsd2ss,sqrtss,sqrtsd,cvttss2si,cvttsd2si,
                      cvtsi2ss,cvtsi2sd]),
    \+ atom_concat(set, _, Op),
    \+ memberchk(S, [ss,sd]),
    once(operand_roles(Op, S, Roles)),
    \+ ( memberchk(Op, [shl,shr,sar]), Os = [reg(_)|_] ),
    maplist(flex_operand, Roles, Os), !.
line_mode(_, fixed).

flex_operand(_, imm(_)) :- !.
flex_operand(_, M) :- mem_operand(M), !.
flex_operand(src(W), reg(N)) :- register(N, F, W), W < 128, \+ memberchk(F, [rsp,rbp]).
flex_operand(dst(W), reg(N)) :- memberchk(W, [32,64]), register(N, F, W), \+ memberchk(F, [rsp,rbp]).
flex_operand(srcdst(W), reg(N)) :- memberchk(W, [32,64]), register(N, F, W), \+ memberchk(F, [rsp,rbp]).

mem_operand(mem(_,_)). mem_operand(mem(_,_,_)). mem_operand(rip(_)). mem_operand(gotpcrel(_)).

% line_demands(+Mode, +Line, +Effect, +Pre, -Keys): the values Line reads
% from registers: lo(Lo) for a read of 32 bits or less, full(Lo, Hi) for
% 64 bits and addressing. A fixed line needs every register it reads or
% partly writes whole.
line_demands(fixed, _, effect(Rs,Ws,_,_,_), st(R,_,_), Ks) :-
    findall(F, ( member(F, Rs), alloc_gpr(F) ), Fs1),
    findall(F, ( member(write(F,W), Ws), W < 32, alloc_gpr(F) ), Fs2),
    append(Fs1, Fs2, Fs0), sort(Fs0, Fs),
    findall(full(Lo,Hi), ( member(F, Fs), reg_get(F, R, v(Lo,Hi)) ), Ks).
line_demands(zero(_), _, _, _, []).
line_demands(flex(Roles), ins(_,_,Os), _, st(R,_,_), Ks) :-
    foldl(operand_demands(R), Roles, Os, [], Ks).

operand_demands(R, Role, reg(N), Ks0, Ks) :-
    memberchk(Role, [src(_), srcdst(_)]), !,
    register(N, F, W), reg_get(F, R, V), key_at(W, V, K), Ks = [K|Ks0].
operand_demands(R, _, M, Ks0, Ks) :-
    findall(full(Lo,Hi), ( address_register(M, F), \+ memberchk(F, [rsp,rbp]),
                           reg_get(F, R, v(Lo,Hi)) ), New),
    append(New, Ks0, Ks).

address_register(mem(_,B), F) :- register(B, F, 64).
address_register(mem(_,B,_), F) :- register(B, F, 64).
address_register(mem(_,_,I), F) :- register(I, F, 64).

alloc_gpr(F) :- gprs(Gs), memberchk(F, Gs).

key_at(64, v(L,H), full(L,H)) :- !.
key_at(_, v(L,_), lo(L)).

count_line(p(_,_,_,_,_,_,_,Ds,_), C0, C) :- foldl(inc, Ds, C0, C).
count_target(_-v(L,H), C0, C) :- inc(full(L,H), C0, C).
inc(K, C0, C) :- ( get_assoc(K, C0, N) -> N1 is N+1 ; N1 = 1 ), put_assoc(K, C0, N1, C).
dec(K, C0, C) :- get_assoc(K, C0, N), N1 is N-1, put_assoc(K, C0, N1, C).
needed(K, C) :- get_assoc(K, C, N), N > 0.

% provides(+V, +K): register value V gives K directly or by one move.
provides(v(L2,_), lo(L)) :- L2 == L.
provides(v(L2,H2), full(L,H)) :- L2 == L, ( H2 == H -> true ; H == const(0) ).
constant_key(lo(const(_))).
constant_key(full(const(_),const(_))).

% dispensable(+T, +Clobbered, +Cnt, +S): no value T holds is needed
% (Cnt) unless a register outside Clobbered or a constant also gives it.
dispensable(T, Clob, Cnt, st(R,_,_)) :-
    reg_get(T, R, v(Lo,Hi)),
    \+ ( held_key(Lo, Hi, K), needed(K, Cnt), \+ constant_key(K),
         \+ ( gprs(Gs), member(G, Gs), \+ memberchk(G, Clob),
              reg_get(G, R, VG), provides(VG, K) ) ).
held_key(Lo, _, lo(Lo)).
held_key(Lo, Hi, full(Lo,Hi)).
held_key(Lo, Hi, full(Lo,const(0))) :- Hi \== const(0).

% obtain_line(+K, +T, +Env, +CS, +S, -Line): a move that puts K in T.
obtain_line(K, T, Env, CS, st(R,_,_), Line) :-
    gprs(Gs),
    (   member(G, Gs), G \== T, reg_get(G, R, VG), exact(VG, K, Size)
    ->  copy_line(Size, G, T, Line)
    ;   K = full(L, const(0)), member(G, Gs), G \== T, reg_get(G, R, v(L2,_)), L2 == L
    ->  copy_line(l, G, T, Line)
    ;   constant_key(K)
    ->  key_imm(K, V), materialize(imm(V), T, Line)
    ;   key_cell(K, Env, CS, D, Size)
    ->  copy_line(Size, mem(D,rbp), T, Line)
    ).

% key_cell(+K, +Env, +CS, -D, -Size): frame cell D holds K. A cell not
% stored in this region holds its start value, which names the cell; a
% stored one is in CS.
key_cell(K, env(_, Cells, _), CS, D, Size) :-
    (   K = lo(L) ; K = full(L, _) ),
    nonvar(L), L = in(cell(D), lo, shared),
    get_assoc(D, Cells, _), \+ get_assoc(D, CS, _),
    cell_holds(D, CS, V), cell_gives(V, K, Size), !.
key_cell(K, _, CS, D, Size) :-
    assoc_to_list(CS, Ps), member(D-V, Ps), cell_gives(V, K, Size), !.

exact(v(L2,H2), full(L,H), q) :- L2 == L, H2 == H.
exact(v(L2,_), lo(L), l) :- L2 == L.

cell_holds(D, CS, V) :-
    (   get_assoc(D, CS, V0) -> V = V0
    ;   V = v(in(cell(D),lo,shared), in(cell(D),hi,shared))
    ).
cell_gives(V, K, q) :- exact(V, K, q), !.
cell_gives(v(L2,_), K, l) :- ( K = lo(L) ; K = full(L, const(0)) ), L2 == L.

copy_line(q, reg(G), T, ins(mov,q,[reg(G),reg(T)])) :- !.
copy_line(q, mem(D,rbp), T, ins(mov,q,[mem(D,rbp),reg(T)])) :- !.
copy_line(q, G, T, ins(mov,q,[reg(G),reg(T)])) :- atom(G), !.
copy_line(l, mem(D,rbp), T, ins(mov,l,[mem(D,rbp),reg(TN)])) :- !, register(TN, T, 32).
copy_line(l, G, T, ins(mov,l,[reg(GN),reg(TN)])) :- register(GN, G, 32), register(TN, T, 32).

key_imm(lo(const(L)), L).
key_imm(full(const(L),const(H)), V) :- V is (H << 32) \/ L.

% flags_after(+Ps0, +Live, -Ps): binds each line's FlagsLive, whether a
% later line or the region's end reads the flags it leaves.
flags_after(Ps0, Live, Ps) :-
    reverse(Ps0, Rev),
    foldl(flags_line, Rev, Live, _),
    Ps = Ps0.
flags_line(p(_,_,effect(_,_,Fl,_,_),_,_,_,_,_,After), After, Before) :-
    (   Fl == write -> Before = 0
    ;   Fl == read -> Before = 128
    ;   Before = After
    ).

% emit(+Line, +Env, +CS, +S0, -S, ?Out0, ?Out): Line is a move; S is S0
% after it.
emit(Line, Env, CS, S0, S, [Line|Out], Out) :-
    stream_move(Line, Env, CS, M), move_state(M, S0, S).

% resolve(+Targets, +Ctx, +CS, +Cnt, +S0, -S, ?Out0, ?Out): moves that
% give each register F of Targets (F-V) the value V, keeping every value
% Cnt needs. A cycle goes through a free register.
resolve(Ts, Ctx, CS, Cnt, S0, S, Out0, Out) :-
    resolve(Ts, Ctx, CS, Cnt, 64, S0, S, Out0, Out).
resolve(Ts, Ctx, CS, Cnt, N, S0, S, Out0, Out) :-
    S0 = st(R,_,_),
    findall(F-V, ( member(F-V, Ts), reg_get(F, R, V0), V0 \== V ), Pend),
    (   Pend == []
    ->  S = S0, Out0 = Out
    ;   N > 0, N1 is N-1,
        Ctx = ctx(Usable, Env, _),
        foldl(count_target, Pend, Cnt, CntP),
        (   member(F-v(L,H), Pend), dispensable(F, [F], CntP, S0),
            obtain_line(full(L,H), F, Env, CS, S0, Line)
        ->  true
        ;   Pend = [F-_|_],
            member(T, Usable), \+ memberchk(T-_, Ts), dispensable(T, [T], CntP, S0)
        ->  Line = ins(mov,q,[reg(F),reg(T)])
        ),
        emit(Line, Env, CS, S0, S1, Out0, Out1),
        resolve(Ts, Ctx, CS, Cnt, N1, S1, S, Out1, Out)
    ).

b_walk([], _, SB, Cnt, Out, Out, SB, Cnt).
b_walk([P|Ps], Ctx, SB0, Cnt0, Out0, Out, SB, Cnt) :-
    P = p(_,_,_,_,_,_,_,Ds,_),
    foldl(dec, Ds, Cnt0, Cnt1),
    b_line(P, Ctx, SB0, Cnt0, Cnt1, Out0, Out1, SB1),
    b_walk(Ps, Ctx, SB1, Cnt1, Out1, Out, SB, Cnt).

% A fixed line: its registers get A's values, values it overwrites and
% that are still needed are copied away, then it is A's line.
b_line(p(J,LA,E,fixed,SA,_,CS,_,_), Ctx, SB0, _, Cnt1, Out0, Out, SB) :-
    Ctx = ctx(Usable, Env, _),
    E = effect(Rs, Ws, _, _, _),
    SA = st(RA,_,_),
    findall(F, ( member(F, Rs), alloc_gpr(F) ), Fs1),
    findall(F, ( member(write(F,W), Ws), W < 32, alloc_gpr(F) ), Fs2),
    append(Fs1, Fs2, Fs0), sort(Fs0, Fs),
    findall(F-V, ( member(F, Fs), reg_get(F, RA, V) ), Need),
    resolve(Need, Ctx, CS, Cnt1, SB0, SB1, Out0, Out1),
    findall(F, ( member(write(F,_), Ws), alloc_gpr(F) ), Cl0), sort(Cl0, Clob),
    foldl(evict(Clob, Fs, Usable, Env, CS, Cnt1), Clob, SB1-Out1, SB2-Out2),
    paired(LA, LA, J, SA, SB2, _, SB),
    Out2 = [LA|Out].

% A zero idiom: any register that can be overwritten.
b_line(p(J,LA,_,zero(W),SA,_,_,_,_), ctx(Usable,_,Targets), SB0, _, Cnt1, Out0, Out, SB) :-
    LA = ins(Op,S,[reg(NA),_]), register(NA, FA, W),
    dest_order(FA, const(0), Usable, Targets, SB0, Order),
    member(T, Order), dispensable(T, [T], Cnt1, SB0), !,
    register(TN, T, W), LB = ins(Op,S,[reg(TN),reg(TN)]),
    paired(LA, LB, J, SA, SB0, _, SB),
    Out0 = [LB|Out].

% A flex line: its destination, then its sources. A two-address
% destination is, by the first register of dest_order/6 that allows
% one: a register holding the input (or, for a commutative form, the
% other input) that can be overwritten, or a lea of an add or a sub
% of an immediate into it when the flags it leaves are dead; failing
% all, a register given the input by a move.
b_line(p(J,LA,_,flex(Roles),SA,SA1,CS,_,Flags), Ctx, SB00, Cnt0, Cnt1, Out00, Out, SB) :-
    Ctx = ctx(Usable, Env, Targets),
    LA = ins(Op,S,OsA),
    (   nth1(K, Roles, Role), memberchk(Role, [dst(_), srcdst(_)]), nth1(K, OsA, reg(NA))
    ->  register(NA, FA, W),
        SA1 = st(RA1,_,_), reg_get(FA, RA1, v(LoR,_)),
        dest_order(FA, LoR, Usable, Targets, SB00, Order),
        make_room(Order, LoR, Ctx, CS, Cnt1, SB00, SB0, Out00, Out0),
        SB0 = st(RB,_,_),
        (   Role = srcdst(_)
        ->  SA = st(RA,_,_), reg_get(FA, RA, VIn), key_at(W, VIn, Kin),
            (   member(T, Order), dispensable(T, [T], Cnt1, SB0),
                two_address(T, RB, Kin, W, LA, SA, Flags, Form)
            ->  SB1 = SB0, Out1 = Out0
            ;   member(T, Order), dispensable(T, [T], Cnt0, SB0),
                obtain_line(Kin, T, Env, CS, SB0, Copy)
            ->  emit(Copy, Env, CS, SB0, SB1, Out0, Out1), Form = same
            )
        ;   member(T, Order), dispensable(T, [T], Cnt1, SB0)
        ->  SB1 = SB0, Out1 = Out0, Form = same
        ),
        register(TN, T, W), Taken0 = [T]
    ;   Form = same, SB1 = SB00, Out1 = Out00, Taken0 = []
    ),
    form_line(Form, LA, SA, Roles, TN, K, Op, S, LA1, Roles1, Dest),
    LA1 = ins(Op1,S1,OsA1),
    sources(Roles1, OsA1, 1, Dest, Op1, SA, Ctx, CS, Cnt0, Taken0, SB1, SB2, Out1, Out2, OsB),
    LB = ins(Op1,S1,OsB),
    line_effect(LB, EB), \+ boundary_line(LB, EB),
    paired(LA, LB, J, SA, SB2, _, SB),
    Out2 = [LB|Out].

% two_address(+T, +RB, +Kin, +W, +LA, +SA, +Flags, -Form): T can take
% LA's result without a move: it holds the input (same), the other input
% of a commutative form (swap), or a lea computes it (lea).
two_address(T, RB, Kin, _, _, _, _, same) :-
    reg_get(T, RB, VT), exact(VT, Kin, _), !.
two_address(T, RB, _, W, ins(Op,S,[reg(X),_]), st(RA,_,_), _, swap) :-
    memberchk(Op, [add,and,or,xor,imul]), memberchk(S, [l,q]),
    register(X, FX, W), reg_get(FX, RA, VX), key_at(W, VX, Kx),
    reg_get(T, RB, VT), exact(VT, Kx, _), !.
two_address(_, _, _, _, ins(Op,S,[Src,_]), _, 0, lea) :-
    memberchk(S, [l,q]),
    (   Op == add, ( Src = reg(_) ; Src = imm(D), integer(D), D >= -(1<<31), D < 1<<31 )
    ;   Op == sub, Src = imm(D), integer(D), D > -(1<<31), D =< 1<<31
    ).

% form_line(+Form, +LA, +Roles, +TN, +K, +Op, +S, -LA1, -Roles1, -Dest):
% the line whose operands sources/15 finds in B, and where the
% destination goes. A swap reads A's second operand first; a lea reads
% A's two addends as an address.
form_line(same, LA, _, Roles, TN, K, _, _, LA, Roles, Dest) :-
    ( var(TN) -> Dest = none ; Dest = K-reg(TN) ).
form_line(swap, ins(Op,S,[X,Y]), _, Roles, TN, K, _, _, ins(Op,S,[Y,X]), Roles, K-reg(TN)).
% A register addend that holds a constant becomes the displacement.
form_line(lea, ins(add,S,[reg(X),reg(Y)]), SA, _, TN, _, _, _,
          ins(lea,S,[mem(D,Y),reg(TN)]), [lea(W),dst(W)], 2-reg(TN)) :-
    memberchk(S-W, [l-32,q-64]), register(X, FX, W),
    read_value(FX, W, SA, V), imm_of(V, W, D), !.
form_line(lea, ins(add,S,[reg(X),reg(Y)]), _, _, TN, _, _, _,
          ins(lea,S,[mem(0,X,Y),reg(TN)]), [lea(W),dst(W)], 2-reg(TN)) :- !,
    memberchk(S-W, [l-32,q-64]).
form_line(lea, ins(add,S,[imm(D),reg(Y)]), _, _, TN, _, _, _,
          ins(lea,S,[mem(D,Y),reg(TN)]), [lea(W),dst(W)], 2-reg(TN)) :- !,
    memberchk(S-W, [l-32,q-64]).
form_line(lea, ins(sub,S,[imm(D),reg(Y)]), _, _, TN, _, _, _,
          ins(lea,S,[mem(ND,Y),reg(TN)]), [lea(W),dst(W)], 2-reg(TN)) :-
    ND is -D, memberchk(S-W, [l-32,q-64]).

% dest_order(+FA, +LoR, +Usable, +Targets, +S, -Order): where a result
% goes: the register it is needed in at the region's end, A's register,
% then the others; registers that already hold their end value last.
dest_order(FA, LoR, Usable, Targets, st(R,_,_), Order) :-
    findall(G, ( member(G-v(L,_), Targets), L == LoR ), Homes),
    gprs(Gs),
    append([Homes, [FA], Gs], All0),
    include(usable(Usable), All0, All1),
    list_to_set(All1, All),
    partition(holds_end(Targets, R), All, Done, Free),
    append(Free, Done, Order).
usable(Usable, G) :- memberchk(G, Usable).
holds_end(Targets, R, G) :- memberchk(G-V, Targets), reg_get(G, R, V0), V0 == V.

% sources(...): each operand of B. A register source reads a register
% holding A's value, else an immediate, else a register given the value
% by a move; an address's registers likewise hold A's whole values.
sources([], [], _, _, _, _, _, _, _, _, S, S, Out, Out, []).
sources([Role|Roles], [OA|OsA], K, Dest, Op, SA, Ctx, CS, Cnt, Taken0, S0, S, Out0, Out, [OB|OsB]) :-
    (   Dest = K-OB0
    ->  OB = OB0, S1 = S0, Out1 = Out0, Taken1 = Taken0
    ;   Role = lea(W), OA = mem(D, X)
    ->  lea_source(X, W, SA, Ctx, CS, Cnt, Taken0, S0, S1, Out0, Out1, G, Taken1),
        OB = mem(D, G)
    ;   Role = lea(W), OA = mem(D, X, Y)
    ->  lea_source(X, W, SA, Ctx, CS, Cnt, Taken0, S0, S2, Out0, Out2, G1, Taken2),
        lea_source(Y, W, SA, Ctx, CS, Cnt, Taken2, S2, S1, Out2, Out1, G2, Taken1),
        OB = mem(D, G1, G2)
    ;   OA = reg(N), memberchk(Role, [src(_)])
    ->  register(N, FA, W), read_value(FA, W, SA, VA),
        source_register(FA, W, VA, K, Op, SA, Ctx, CS, Cnt, Taken0, S0, S1, Out0, Out1, OB, Taken1)
    ;   OA = mem(D, B)
    ->  base_register(B, SA, Ctx, CS, Cnt, Taken0, S0, S1, Out0, Out1, B1, Taken1),
        OB = mem(D, B1)
    ;   OA = mem(D, B, I)
    ->  base_register(B, SA, Ctx, CS, Cnt, Taken0, S0, S2, Out0, Out2, B1, Taken2),
        base_register(I, SA, Ctx, CS, Cnt, Taken2, S2, S1, Out2, Out1, I1, Taken1),
        OB = mem(D, B1, I1)
    ;   OB = OA, S1 = S0, Out1 = Out0, Taken1 = Taken0
    ),
    K1 is K+1,
    sources(Roles, OsA, K1, Dest, Op, SA, Ctx, CS, Cnt, Taken1, S1, S, Out1, Out, OsB).

source_register(FA, W, VA, K, Op, SA, Ctx, CS, Cnt, Taken, S0, S, Out0, Out, OB, [G|Taken]) :-
    gprs(Gs),
    (   member(G, [FA|Gs]), read_value(G, W, S0, VB), VB == VA
    ->  register(GN, G, W), OB = reg(GN), S = S0, Out = Out0
    ;   K =:= 1, memberchk(Op, [add,sub,and,or,xor,imul,cmp,test,mov]),
        imm_of(VA, W, I)
    ->  OB = imm(I), S = S0, Out = Out0, G = none
    ;   SA = st(RA,_,_), reg_get(FA, RA, V), key_at(W, V, Key0),
        ( W =< 32 -> Key = Key0 ; Key = Key0 ),
        Ctx = ctx(Usable, Env, _),
        member(G, Usable), \+ memberchk(G, Taken), dispensable(G, [G], Cnt, S0),
        obtain_line(Key, G, Env, CS, S0, Line)
    ->  emit(Line, Env, CS, S0, S, Out0, Out),
        register(GN, G, W), OB = reg(GN)
    ).

imm_of([const(L),const(H)], 64, I) :- !, V is (H << 32) \/ L, imm_for(V, 64, I).
imm_of([const(V)], W, I) :- imm_for(V, W, I).

base_register(B, SA, Ctx, CS, Cnt, Taken, S0, S, Out0, Out, B1, [G|Taken]) :-
    register(B, FA, 64),
    (   memberchk(FA, [rsp,rbp])
    ->  G = FA, B1 = B, S = S0, Out = Out0
    ;   SA = st(RA,_,_), reg_get(FA, RA, VA), S0 = st(RB,_,_), gprs(Gs),
        (   member(G, [FA|Gs]), reg_get(G, RB, VB), VB == VA
        ->  B1 = G, S = S0, Out = Out0
        ;   Ctx = ctx(Usable, Env, _), VA = v(L,H),
            member(G, Usable), \+ memberchk(G, Taken), dispensable(G, [G], Cnt, S0),
            obtain_line(full(L,H), G, Env, CS, S0, Line)
        ->  emit(Line, Env, CS, S0, S, Out0, Out), B1 = G
        )
    ).

evict(Clob, Reads, Usable, Env, CS, Cnt, F, S0-Out0, S-Out) :-
    (   dispensable(F, Clob, Cnt, S0)
    ->  S = S0, Out = Out0
    ;   member(T, Usable), \+ memberchk(T, Clob), \+ memberchk(T, Reads),
        dispensable(T, [T], Cnt, S0)
    ->  emit(ins(mov,q,[reg(F),reg(T)]), Env, CS, S0, S, Out0, Out)
    ).

% lea_source(+N, +W, ...): a 64-bit register whose low W bits are A's
% register N's, for a lea that reads them as an address.
lea_source(N, W, SA, Ctx, CS, Cnt, Taken, S0, S, Out0, Out, G, [G|Taken]) :-
    register(N, FA, _), read_value(FA, W, SA, VA), gprs(Gs),
    (   member(G, [FA|Gs]), read_value(G, W, S0, VB), VB == VA
    ->  S = S0, Out = Out0
    ;   SA = st(RA,_,_), reg_get(FA, RA, V), key_at(W, V, Key),
        Ctx = ctx(Usable, Env, _),
        member(G, Usable), \+ memberchk(G, Taken), dispensable(G, [G], Cnt, S0),
        obtain_line(Key, G, Env, CS, S0, Line)
    ->  emit(Line, Env, CS, S0, S, Out0, Out)
    ).

% make_room(+Order, +LoR, +Ctx, +CS, +Cnt, +S0, -S, ?Out0, ?Out): when
% the first register of Order is where the result LoR is needed at the
% region's end but still holds a needed value, that value moves on to
% the register it is needed in at the end, if that one is free or can be
% freed the same way (at most three deep). Otherwise nothing changes.
make_room([T|_], LoR, Ctx, CS, Cnt, S0, S, Out0, Out) :-
    Ctx = ctx(_, _, Targets),
    member(T-v(L,_), Targets), L == LoR,
    \+ dispensable(T, [T], Cnt, S0),
    room(T, 3, [T], Ctx, CS, Cnt, S0, S1, Out0, Out1),
    dispensable(T, [T], Cnt, S1), !,
    S = S1, Out = Out1.
make_room(_, _, _, _, _, S, S, Out, Out).

room(T, N, Seen, Ctx, CS, Cnt, S0, S, Out0, Out) :-
    N > 0, Ctx = ctx(Usable, Env, Targets),
    S0 = st(R,_,_), reg_get(T, R, VT),
    member(G-VG, Targets), VG == VT, G \== T, \+ memberchk(G, Seen),
    memberchk(G, Usable),
    (   dispensable(G, [G], Cnt, S0)
    ->  S1 = S0, Out1 = Out0
    ;   N1 is N-1, room(G, N1, [G|Seen], Ctx, CS, Cnt, S0, S1, Out0, Out1),
        dispensable(G, [G], Cnt, S1)
    ), !,
    emit(ins(mov,q,[reg(T),reg(G)]), Env, CS, S1, S, Out1, Out).

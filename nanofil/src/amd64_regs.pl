/* Whole-function register homes for scalar temporaries
   (`--registers=function`, docs/perf.md item 3, step 3a; with step 3b's
   operand rewrite, `--registers=operands`, and frame cells,
   `--registers=cells`, the -O default). A fixed map
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
:- module(amd64_regs, [regs_asm/6, operands_rewrite/6]).
:- use_module(amd64_contract, [instruction_effects/2, register/3,
                                explicit_registers/2]).
:- use_module(amd64_regs_check).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).

%! regs_asm(+Mode, +Metadata, +Before, -After, -Checked, -Report) is det.
%
%  Mode is map (3a's map alone, unchecked, for a layout choice; Final
%  is then not to be emitted), function (step 3a), operands (3a, then
%  step 3b's operand rewrite) or frame(Cells) (operands with the frame cells of
%  docs/perf.md 5a-loads). Metadata is regs_metadata(Setjmp, Impl, Homes, Saves) with a
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
        (   Analysis0 == none, Mode \== function
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
    (   operand_cells(Mode, Cells0, Flow), Report = allocated(_, _)
    ->  impl_body(Impl, After, PreA, A),
        (   operand_lives(Analysis, Used, A, Lives) -> true
        ;   throw(nanofil_error('register operand liveness failed'))
        ),
        valid_cells(Cells0, A, Cells),
        operands_rewrite(Flow, A, Lives, Cells, B, Checked),
        (   check_operands(A, B, Lives, Cells0, Checked) -> true
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
                forall(member(K,Ks), memberchk(K,[w,l]))), Scalar),
    findall(W-H, ( member(H, Scalar), W is H >> 3 ), WHs0),
    keysort(WHs0, WHs), group_pairs_by_key(WHs, Words), list_to_assoc(Words, ScalarSet),
    depths(Body, Depths),
    foldl(home_refs(ScalarSet), Body, Effects, Depths, [], Refs),
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

numbered([], _, []).
numbered([H|Hs], K, [H-K|Ps]) :- K1 is K+1, numbered(Hs, K1, Ps).

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
   rewritten lines. The passes carry each line as Line-inf(Effect, Use,
   Def, Move): its audited effects, the scratch and flags sets it uses
   and defines, and its operand_move/2 reading or none, computed once. */

% operand_cells(+Mode, -Cells, -Flow): the frame cells whose loads the
% rewrite may forward: none in operands mode, the emitter's in frame
% mode (docs/perf.md, 5a-loads) and flow mode (5b-1), where Flow is flow
% and regions continue past conditional jumps; cells otherwise.
operand_cells(operands, cells([], []), cells).
operand_cells(frame(Cells), Cells, cells).
operand_cells(flow(Cells), Cells, flow).

%! operands_rewrite(+A, +Lives, +Cells, -B) is det.
operands_rewrite(A, Lives, Cells, B) :-
    operands_rewrite(cells, A, Lives, Cells, B).

%! operands_rewrite(+Flow, +A, +Lives, +Cells, -B) is det.
operands_rewrite(Flow, A, Lives, Cells, B) :-
    operands_rewrite(Flow, A, Lives, Cells, B, _).

%! operands_rewrite(+Flow, +A, +Lives, +Cells, -B, -Checked) is det.
%  Checked is the Flow argument for check_operands/5: cells, or
%  flow(Facts) with the label facts B relies on (docs/perf.md 5b-1).
operands_rewrite(cells, A, Lives, Cells, B, cells) :-
    operand_regions(cells, A, Lives, Regions),
    empty_assoc(H0),
    maplist(region_rewrite(Cells, H0), Regions, Parts),
    append(Parts, B).
operands_rewrite(flow, A, Lives, Cells, B, flow(Facts)) :-
    operand_regions(flow, A, Lives, Regions),
    flow_facts(Regions, A, Cells, Facts),
    flow_parts(Regions, none, Facts, Cells, Parts),
    append(Parts, B).

/* Label facts (untrusted; check_operands/5 verifies every edge). The
   held map of cell_forward/6 flows across the regions: a region starts
   from its label's facts, or from nothing after any other boundary, and
   passes its held map to the label it falls into or jumps to, and to
   the targets of the conditional jumps it continues past. A label's
   facts are the cell-register pairs held on all its incoming edges, in
   scratch families not live in the reference there; labels that may
   not carry facts (fact_labels/2) get none. Optimistic iteration from
   "everything" (top) to a fixpoint. */
flow_facts(Regions, A, Cells, Facts) :-
    fact_labels(A, Labels),
    empty_assoc(F0),
    label_ins(Regions, Ins),
    flow_iterate(Regions, Labels, Ins, Cells, F0, 0, Facts1),
    assoc_to_list(Facts1, Ps0),
    findall(L-Fs, ( member(L-H, Ps0), H \== top, assoc_to_list(H, DFs),
                    findall(F-D, member(D-F, DFs), Fs0), msort(Fs0, Fs), Fs \== [] ), Ps),
    list_to_assoc(Ps, Facts).

% Facts maps a label to top (no edge seen yet) or a held map; a label
% missing from it is top.
flow_iterate(Regions, Labels, Ins, Cells, F0, N, F) :-
    flow_edges(Regions, none, Labels, F0, Cells, Edges),
    findall(L-H, ( member(L-H0, Edges), get_assoc(L, Labels, _),
                   ( H0 == top -> H = top ; H = H0 ) ), LHs0),
    keysort(LHs0, LHs), group_pairs_by_key(LHs, Groups),
    findall(L-H, ( member(L-Hs, Groups), meet(Hs, H1), restrict(H1, L, Ins, H) ), Ps0),
    % A label no edge reaches holds nothing (the checker starts it from
    % the shared state and checks its edges out).
    empty_assoc(E), pairs_keys(Groups, Gs), ord_label_set(Gs, Reached),
    findall(L-E, ( gen_assoc(L, Labels, _), \+ get_assoc(L, Reached, _) ), Ps1),
    append(Ps0, Ps1, Ps2), keysort(Ps2, Ps),
    list_to_assoc(Ps, F1),
    % Compare contents: equal held maps may differ in their trees.
    (   facts_list(F1, L1), facts_list(F0, L0), L1 == L0 -> F = F1
    ;   N >= 64 -> empty_assoc(F)
    ;   N1 is N+1, flow_iterate(Regions, Labels, Ins, Cells, F1, N1, F)
    ).

ord_label_set(Ls, Set) :- findall(L-t, member(L, Ls), Ps), list_to_assoc(Ps, Set).

facts_list(F, Ps) :-
    assoc_to_list(F, Ps0),
    findall(L-V, ( member(L-H, Ps0), ( H == top -> V = top ; assoc_to_list(H, V) ) ), Ps).

% meet(+Hs, -H): the pairs every non-top map holds; top if all are top.
meet(Hs, H) :-
    exclude(==(top), Hs, Ms),
    (   Ms = [] -> H = top
    ;   Ms = [M|Rest], assoc_to_list(M, Ps),
        include(held_by_all(Rest), Ps, Kept), list_to_assoc(Kept, H)
    ).
held_by_all(Ms, D-F) :- forall(member(M, Ms), ( get_assoc(D, M, G), G == F )).

% restrict(+H0, +L, +Ins, -H): only families dead in the reference at L,
% one cell each.
restrict(top, _, _, top) :- !.
restrict(H0, L, Ins, H) :-
    ( get_assoc(L, Ins, In) -> true ; In = 127 ),
    assoc_to_list(H0, Ps),
    include(dead_at(In), Ps, Kept0),
    one_per_family(Kept0, [], Kept), list_to_assoc(Kept, H).

% one_per_family(+Ps, +Seen, -Kept): a family holds one cell's value in
% a fact; keep the first cell (lowest offset) for each.
one_per_family([], _, []).
one_per_family([D-F|Ps], Seen, Kept) :-
    (   memberchk(F, Seen) -> Kept = Kept1
    ;   Kept = [D-F|Kept1]
    ),
    one_per_family(Ps, [F|Seen], Kept1).
dead_at(In, _-F) :- scratch_family(F, Bit), In /\ (1 << Bit) =:= 0.

% label_ins(+Regions, -Ins): each label's reference liveness, the End of
% the region it ends.
label_ins(Regions, Ins) :-
    findall(L-In, member(region(_, In, [label(L)]), Regions), Ps0),
    sort(Ps0, Ps1), first_per_label(Ps1, Ps), list_to_assoc(Ps, Ins).
first_per_label([], []).
first_per_label([L-I|Ps], [L-I|Qs]) :- skip_same(L, Ps, Ps1), first_per_label(Ps1, Qs).
skip_same(L, [M-_|Ps], Rest) :- M == L, !, skip_same(L, Ps, Rest).
skip_same(_, Ps, Ps).

% flow_edges(+Regions, +Prev, +Labels, +Facts, +Cells, -Edges):
% Label-Held for every edge, Held top when its region starts at a top
% label. Prev is the boundary before the region, none for the first.
flow_edges([], _, _, _, _, []).
flow_edges([region(Lines, _, Boundary)|Rs], Prev, Labels, Facts, Cells, Edges) :-
    region_start_held(Prev, Labels, Facts, H0),
    (   H0 == top
    ->  findall(T-top, ( member(L-_, Lines), jcc_target(L, T) ), Es0),
        Hend = top
    ;   cell_forward(Lines, Cells, H0, _, Hend, Es0)
    ),
    boundary_edges(Boundary, Hend, Es1),
    append(Es0, Es1, Es),
    ( Boundary = [B] -> Prev1 = B ; Prev1 = none ),
    flow_edges(Rs, Prev1, Labels, Facts, Cells, Es2),
    append(Es, Es2, Edges).

% region_start_held(+Prev, +Labels, +Facts, -H): the held map a region
% starts from: its label's facts, top for a label with no edge yet,
% nothing at a label that may not carry facts (it never gets an entry,
% so top would hide its region's edges from the meet for good), after
% any other boundary or at the function's start.
region_start_held(label(L), Labels, Facts, H) :- get_assoc(L, Labels, _), !,
    ( get_assoc(L, Facts, H) -> true ; H = top ).
region_start_held(_, _, _, H) :- empty_assoc(H).

boundary_edges([label(L)], H, [L-H]) :- !.
boundary_edges([ins(jmp,none,[sym(T)])], H, [T-H]) :- !.
boundary_edges(_, _, []).

jcc_target(ins(Op,none,[sym(T)]), T) :- Op \== jmp, atom_concat(j, _, Op).

% flow_parts(+Regions, +Prev, +Facts, +Cells, -Parts): each region
% rewritten from its start facts, its end liveness and its continued
% jumps' uses extended by the fact registers of their targets.
flow_parts([], _, _, _, []).
flow_parts([region(Lines0, End0, Boundary)|Rs], Prev, Facts, Cells, [Part|Parts]) :-
    (   Prev = label(L), get_assoc(L, Facts, Fs)
    ->  findall(D-F, member(F-D, Fs), DFs), list_to_assoc(DFs, H0)
    ;   empty_assoc(H0)
    ),
    maplist(jump_uses(Facts), Lines0, Lines),
    (   ( Boundary = [label(T)] ; Boundary = [ins(jmp,none,[sym(T)])] )
    ->  fact_bits(T, Facts, Bits), End is End0 \/ Bits
    ;   End = End0
    ),
    region_rewrite(Cells, H0, region(Lines, End, Boundary), Part),
    ( Boundary = [B] -> Prev1 = B ; Prev1 = none ),
    flow_parts(Rs, Prev1, Facts, Cells, Parts).

jump_uses(Facts, L-inf(E,U0,D,M), L-inf(E,U,D,M)) :-
    (   jcc_target(L, T) -> fact_bits(T, Facts, Bits), U is U0 \/ Bits
    ;   U = U0
    ).

fact_bits(T, Facts, Bits) :-
    (   get_assoc(T, Facts, Fs)
    ->  foldl(fact_bit, Fs, 0, Bits)
    ;   Bits = 0
    ).
fact_bit(F-_, B0, B) :- scratch_family(F, Bit), B is B0 \/ (1 << Bit).

operand_regions(_, [], [], []) :- !.
operand_regions(Flow, As, Ls, [region(Lines, End, Boundary)|Rs]) :-
    region_lines(Flow, As, Ls, Lines, End, Boundary, As1, Ls1),
    operand_regions(Flow, As1, Ls1, Rs).

% In flow mode a conditional jump to a local label stays in its region
% (continued_jump/3), as a line that reads every scratch family live
% before it in the reference, so the moves its taken edge needs stay.
region_lines(_, [], [], [], 0, [], [], []).
region_lines(Flow, [L|As], [live(In,_,E)|Ls], Lines, End, Boundary, As1, Ls1) :-
    (   continued_jump(Flow, L, E)
    ->  effect_info(L, E, inf(E, U0, D, M)), U is U0 \/ (In /\ 127),
        Lines = [L-inf(E, U, D, M)|Lines1],
        region_lines(Flow, As, Ls, Lines1, End, Boundary, As1, Ls1)
    ;   boundary_line(L, E)
    ->  Lines = [], End is In /\ 127, Boundary = [L], As1 = As, Ls1 = Ls
    ;   effect_info(L, E, I), Lines = [L-I|Lines1],
        region_lines(Flow, As, Ls, Lines1, End, Boundary, As1, Ls1)
    ).

region_rewrite(Cells, H0, region(Lines0, End, Boundary), Out) :-
    empty_assoc(C0),
    (   empty_assoc(Cells) -> Lines = Lines0
    ;   cell_forward(Lines0, Cells, H0, Lines, _, _)
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
cell_forward(Lines, Cells, H0, Out) :-
    cell_forward(Lines, Cells, H0, Out, _, _).

% cell_forward(+Lines, +Cells, +Held, -Out, -HeldAfter, -Edges): also the
% held map after the lines, and Target-Held at each conditional jump.
cell_forward([], _, H, [], H, []).
cell_forward([L-I|Ls], Cells, H0, Out, Hend, Edges) :-
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
    ( jcc_target(L, T) -> Edges = [T-H0|Edges1] ; Edges = Edges1 ),
    append(Emit, Rest, Out),
    cell_forward(Ls, Cells, H, Rest, Hend, Edges1).

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
    exclude(depends_on(F), Ps, Kept),
    list_to_assoc(Kept, C).
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

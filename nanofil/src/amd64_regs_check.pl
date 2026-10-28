/* Translation validation for whole-function scalar register homes
   (`--registers=function`, docs/perf.md item 3). The allocator proposes
   a fixed map from frame homes to registers; nothing about how it chose
   the map is trusted here.

   The allocated stream is determined by the reference stream, the map
   and the save slots: every access to a mapped home is the same move
   with the home's register in place of its slot (substitute/3), the
   callee-saved registers the map uses are stored to their save slots
   right after the stack check and reloaded before every `leave`, and
   nothing else changes. The checker rebuilds that stream and requires
   the proposal to equal it, so flags, failure arguments, control flow
   and every unmapped location are unchanged by construction.

   What remains to prove is that each mapped register holds its home's
   value wherever the reference could read it. The invariant: at every
   point, every live half (low or high 32 bits) of a mapped home equals
   the same half of its register. Liveness is computed here, per half,
   on the reference stream's control-flow graph, which must be complete:
   every jump names a label of the function or the stack-overflow exit,
   and no instruction falls off the end. The obligations:

   | Event | Obligation |
   | --- | --- |
   | function entry | no mapped half is live |
   | a write to home H in register R | every other home in R is dead after it |
   | a 32-bit write to H | H's high half is dead after it (a register write zero-extends) |
   | a `call` | homes in r10/r11 are dead after it (the callee may clobber them) |
   | a `leave` | no mapped half is live (the restores replace the registers) |

   Byte and word writes preserve the rest of a register as they do of
   memory; liveness treats them as reads. Callee-saved registers keep
   their values across calls by the SysV ABI, which every callee obeys:
   C runtime functions, clang code and nanofil functions, which save
   what they use here. The reference stream must not name an allocatable
   register or %rbp outside the prologue, must not take the address of
   a mapped home or save slot, and must not touch a save slot.

   Trusted, as in amd64_cache_check: the emitter's home classes, and
   that only %rbp-relative operands reach a home (homes and save slots
   never escape; the frame record and local storage the code does expose
   lie elsewhere in the frame). */
:- module(amd64_regs_check,
          [check_regs/4, check_regs/5, substitute/3, impl_body/4,
           preflight_regs/3, preflight_regs/4, body_analysis/3,
           allocated_stream/4, home_liveness/4, successors/2, successors/3, rbp_access/3,
           effect_access/3, line_effect/2, body_analysis/4,
           allocatable/1, callee_saved/1, scratch_family/2,
           check_operands/3, check_operands/4, valid_cells/3, operand_lives/4, operand_move/2,
           operand_roles/3, boundary_line/2, extra_use_def/4]).

:- use_module(amd64_contract,
              [instruction_effects/2, register/3, explicit_registers/2]).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).

%! check_regs(+Metadata, +Map, +Before, +After) is semidet.
%
%  Metadata is regs_metadata(Setjmp, Impl, Homes, Saves): Homes lists
%  home(Offset, Classes) as for the scalar cache, Saves lists save(R,
%  Offset) for each callee-saved register in Map, in callee_saved/1
%  order. Map lists Offset-Register. An empty map or a setjmp function
%  admits only identity.
check_regs(Meta, Map, Before, After) :-
    Meta = regs_metadata(_, Impl, _, _),
    (   impl_body(Impl, Before, _, Body), pairs_offsets(Map, Homes),
        body_analysis(Body, Homes, Analysis)
    ->  true
    ;   Analysis = none
    ),
    check_regs(Meta, Map, Before, After, Analysis).

%! check_regs(+Metadata, +Map, +Before, +After, +Analysis) is semidet.
%
%  As check_regs/4, with the effects, CFG and home liveness of Before's
%  implementation body already computed by body_analysis/3 (the driver
%  computes it once and shares it with the allocator). The analysis
%  must be of that very body and cover every mapped home; liveness bits
%  are independent per home, so extra homes change nothing.
check_regs(regs_metadata(Setjmp, Impl, Homes, Saves), Map, Before, After, Analysis) :-
    ground(Setjmp-Impl-Homes-Saves-Map-Before-After),
    (   ( Setjmp == true ; Map == [] )
    ->  Before == After
    ;   valid_map(Map, Homes, Saves),
        impl_body(Impl, Before, Pre, Body),
        Analysis = analysis(Body0, Effects, _, _, _, _, _),
        Body0 == Body,
        list_to_assoc(Map, Mapped),
        preflight_regs(Body, Mapped, Saves, Effects),
        allocated_stream(Body, Mapped, Saves, Expected),
        append(Pre, [label(Impl)|Expected], After),
        obligations(Body, Mapped, Analysis)
    ).

allocatable(R) :- callee_saved(R).
allocatable(r10).
allocatable(r11).
callee_saved(rbx). callee_saved(r12). callee_saved(r13).
callee_saved(r14). callee_saved(r15).

% Mapped homes are disjoint 8-byte scalar homes, every description of
% each one scalar; save slots match the callee-saved registers used, in
% order, and lie outside every home.
valid_map(Map, Homes, Saves) :-
    is_list(Map), Map = [_|_],
    pairs_offsets(Map, Offsets), msort(Offsets, Sorted), sort(Offsets, Sorted),
    apart(Sorted),
    forall(member(D-R, Map),
           ( memberchk(home(D, _), Homes),
             forall(member(home(D, Ks), Homes),
                    ( Ks = [_|_], forall(member(K, Ks), memberchk(K, [w,l])) )),
             allocatable(R) )),
    findall(R, (callee_saved(R), memberchk(_-R, Map)), Used),
    findall(R, member(save(R,_), Saves), Used),
    forall(member(save(_,S), Saves),
           ( integer(S), S < 0, S mod 8 =:= 0,
             \+ (member(home(H,_), Homes), S < H+8, H < S+8) )),
    findall(S, member(save(_,S), Saves), Ss), sort(Ss, SSet), length(Ss, N), length(SSet, N).

apart([]).
apart([_]).
apart([A,B|Os]) :- B - A >= 8, apart([B|Os]).

pairs_offsets([], []).
pairs_offsets([D-_|Ps], [D|Ds]) :- integer(D), pairs_offsets(Ps, Ds).

%! impl_body(+Impl, +Lines, -Pre, -Body) is semidet.
%  Body follows label(Impl) in Lines; Pre is everything before it.
impl_body(Impl, Lines, Pre, Body) :-
    append(Pre, [label(Impl)|Body], Lines), !.

%! preflight_regs(+Body, +Mapped, +Saves) is semidet.
%  Every line has audited effects; no allocatable register is named;
%  %rbp appears as a register only in the prologue; no indexed %rbp
%  operand; no lea of a mapped home or save slot; no access to a save
%  slot; an access that touches a mapped home is a substitutable move
%  of that exact home.
preflight_regs(Body, Mapped, Saves) :-
    maplist(line_effect, Body, Effects),
    preflight_regs(Body, Mapped, Saves, Effects).

%! preflight_regs(+Body, +Mapped, +Saves, +Effects) is semidet.
%  As preflight_regs/3, with Effects the lines' audited effects.
preflight_regs(Body, Mapped, Saves, Effects) :-
    Body = [ins(push,q,[reg(rbp)]), ins(mov,q,[reg(rsp),reg(rbp)])|Rest],
    Effects = [_,_|RestEffects],
    findall(S, member(save(_,S), Saves), SaveOffsets),
    maplist(preflight_line(Mapped, SaveOffsets), Rest, RestEffects).

preflight_line(Mapped, Saves, Line, effect(_,_,_,Ms,_)) :-
    explicit_registers(Line, Rs),
    \+ (member(R, Rs), allocatable(R)),
    \+ (Line = ins(_,_,Os), member(O, Os), rbp_register(O)),
    \+ (Line = ins(_,_,Os), member(mem(_,rbp,_), Os)),
    \+ (Line = ins(lea,_,[mem(D,rbp),_]), touches(D, 1, Mapped, Saves)),
    \+ (effect_access(Ms, D, N), member(S, Saves), D < S+8, S < D+N),
    (   Line \= ins(lea,_,_), effect_access(Ms, D, N), mapped_overlap(D, N, Mapped)
    ->  once(substitute(Line, Mapped, _))
    ;   true
    ).

rbp_register(reg(R)) :- register(R, rbp, _).
rbp_register(ind(reg(R))) :- register(R, rbp, _).

touches(D, N, Mapped, Saves) :-
    ( mapped_overlap(D, N, Mapped) -> true ; member(S, Saves), D < S+8, S < D+N ).

mapped_overlap(D, N, Mapped) :-
    H0 is D-7, H1 is D+N-1, between(H0, H1, H), get_assoc(H, Mapped, _), !.

% rbp_access(+Line, -D, -Bytes): Line reads or writes Bytes at D(%rbp).
rbp_access(Line, D, N) :-
    once(instruction_effects(Line, effect(_,_,_,Ms,_))),
    effect_access(Ms, D, N).
effect_access(Ms, D, N) :-
    member(M, Ms), ( M = read(mem(D,rbp),N) ; M = write(mem(D,rbp),N) ).

%! substitute(+Line, +Mapped, -New) is semidet.
%  New is the move Line with its mapped home operand replaced by the
%  home's register at the same width. Only moves are substituted.
substitute(ins(mov,S,[mem(D,rbp),reg(X)]), Mapped, ins(mov,S,[reg(N),reg(X)])) :-
    get_assoc(D, Mapped, R), move_bits(S, W), register(N, R, W).
substitute(ins(mov,S,[reg(X),mem(D,rbp)]), Mapped, ins(mov,S,[reg(X),reg(N)])) :-
    get_assoc(D, Mapped, R), move_bits(S, W), register(N, R, W).
% A q immediate must fit a sign-extended imm32, as the memory form must;
% the register form would otherwise assemble as movabs.
substitute(ins(mov,S,[imm(I),mem(D,rbp)]), Mapped, ins(mov,S,[imm(I),reg(N)])) :-
    integer(I), ( S == q -> I >= -(1<<31), I < 1<<31 ; true ),
    get_assoc(D, Mapped, R), move_bits(S, W), register(N, R, W).
substitute(ins(Op,S,[mem(D,rbp),reg(X)]), Mapped, ins(Op,S,[reg(N),reg(X)])) :-
    extension_bits(Op, W),
    get_assoc(D, Mapped, R), register(N, R, W).

move_bits(b,8). move_bits(w,16). move_bits(l,32). move_bits(q,64).
extension_bits(movzb,8). extension_bits(movsb,8).
extension_bits(movzw,16). extension_bits(movsw,16). extension_bits(movsl,32).

%! allocated_stream(+Body, +Mapped, +Saves, -After) is semidet.
%  After is the implementation body Body with the map applied: mapped
%  moves substituted, saves after the stack check, restores before
%  every leave. Fails if Body has no stack check, if anything before it
%  is a label, a transfer or an access to a mapped home (the saves must
%  run once, on every path, before any mapped register changes), or if a
%  leave is not followed by ret.
allocated_stream(Body, Mapped, Saves, Expected) :-
    append(Prologue, [Check|Rest], Body),
    Check == ins(jae,none,[plt(filc_stack_overflow_failure)]), !,
    maplist(straight_prologue(Mapped), Prologue),
    findall(ins(mov,q,[reg(R),mem(S,rbp)]), member(save(R,S),Saves), Stores),
    findall(ins(mov,q,[mem(S,rbp),reg(R)]), member(save(R,S),Saves), Loads),
    maplist(expected_line(Mapped), Prologue, Prologue1),
    expected_rest(Rest, Mapped, Loads, Rest1),
    append([Prologue1, [Check], Stores, Rest1], Expected).

straight_prologue(Mapped, Line) :-
    once(instruction_effects(Line, effect(_,_,_,_,Flow))),
    memberchk(Flow, [next,frame]),
    \+ ( rbp_access(Line, D, N), mapped_overlap(D, N, Mapped) ).

% Every leave is followed by ret; the restores come before the leave.
expected_rest([], _, _, []).
expected_rest([ins(leave,none,[]), ins(ret,none,[])|Ls], Mapped, Loads, Out) :- !,
    append(Loads, [ins(leave,none,[]), ins(ret,none,[])|Out1], Out),
    expected_rest(Ls, Mapped, Loads, Out1).
expected_rest([L|Ls], Mapped, Loads, [L1|Out]) :-
    L \= ins(leave,_,_), L \= ins(ret,_,_),
    expected_line(Mapped, L, L1),
    expected_rest(Ls, Mapped, Loads, Out).

expected_line(Mapped, L, L1) :-
    ( substitute(L, Mapped, New) -> L1 = New ; L1 = L ).

%% Control flow and liveness

% The successors of each line of Body by index, or failure when a
% transfer is unknown or the last line falls through.
successors(Body, Succs) :-
    maplist(line_effect, Body, Effects),
    successors(Body, Effects, Succs).

line_effect(Line, Effect) :- once(instruction_effects(Line, Effect)).

successors(Body, Effects, Succs) :-
    length(Body, N),
    findall(L-I, nth0(I, Body, label(L)), Ls0), keysort(Ls0, Ls1),
    group_pairs_by_key(Ls1, Ls), list_to_assoc(Ls, Labels),
    numlist_from(0, N, Is),
    maplist(line_successors(Labels, N), Is, Body, Effects, Succs).

numlist_from(I, N, []) :- I >= N, !.
numlist_from(I, N, [I|Is]) :- J is I+1, numlist_from(J, N, Is).

line_successors(Labels, N, I, Line, effect(_,_,_,_,Flow), Ss) :-
    J is I+1,
    flow_successors(Flow, Line, Labels-I, J, Ss0),
    \+ (member(S, Ss0), S >= N),
    Ss = Ss0.

% target(+Labels-I, +Name, -T): T is the index of the label Name jumped
% to from line I. GNU as numeric labels: `1f` is the next `1`, `1b` the
% previous one.
target(Labels-I, Name, T) :-
    % The last character first: splitting every name with atom_concat/3
    % costs its length per jump.
    sub_atom(Name, _, 1, 0, Dir), memberchk(Dir, [f,b]),
    sub_atom(Name, 0, _, 1, Digits),
    atom_chars(Digits, [C|Cs]), maplist(digit, [C|Cs]), !,
    get_assoc(Digits, Labels, Is),
    (   Dir == f
    ->  once((member(T, Is), T > I))
    ;   reverse(Is, Rs), once((member(T, Rs), T < I))
    ).
target(Labels-_, Name, T) :-
    get_assoc(Name, Labels, [T]).

digit(C) :- memberchk(C, ['0','1','2','3','4','5','6','7','8','9']).

flow_successors(next, _, _, J, [J]).
flow_successors(frame, _, _, J, [J]).
% A call into the body itself would return into the wrong context.
flow_successors(call, ins(call,_,[T]), Labels-_, J, [J]) :-
    \+ ( T = sym(L), get_assoc(L, Labels, _) ).
flow_successors(label, _, _, J, [J]).
flow_successors(directive, _, _, J, [J]).
flow_successors(terminal, _, _, _, []).
flow_successors(branch, ins(jmp,none,[sym(L)]), Labels, _, [T]) :- !,
    target(Labels, L, T).
flow_successors(branch, ins(Op,none,[sym(L)]), Labels, J, [T,J]) :-
    Op \== jmp, !, target(Labels, L, T).
flow_successors(branch, ins(Op,none,[plt(S)]), _, J, [J]) :-
    Op \== jmp, noreturn(S).

noreturn(filc_stack_overflow_failure).

%! home_liveness(+Body, +Homes, -LiveOut, -LiveIn0) is semidet.
%  Homes is a list of home offsets. LiveOut lists, per line of Body, the
%  set of live halves after it as a bitset: bit 2K is home K's low half,
%  2K+1 its high half. LiveIn0 is the set live at Body's first line.
%  Dataflow runs on basic blocks: a block ends at a line whose only
%  successor is not the next line, and starts at a label.
home_liveness(Body, Homes, LiveOut, LiveIn0) :-
    body_analysis(Body, Homes, analysis(_, _, _, _, LiveOut0, LiveIn00, _)),
    length(Homes, N), Mask is (1 << (2*N)) - 1,
    maplist(and_mask(Mask), LiveOut0, LiveOut), LiveIn0 is LiveIn00 /\ Mask.

and_mask(M, X, Y) :- Y is X /\ M.

%! body_analysis(+Body, +Homes, -Analysis) is semidet.
%  Analysis = analysis(Body, Effects, Homes, Index, LiveOut, LiveIn0, UDs):
%  each line's audited effects, the home offsets and their bit numbers
%  (Index), the live sets after each line (LiveOut) and at the first,
%  and each line's ud(Use, Def). Home K's halves are bits 2K and 2K+1
%  (home_liveness/4); above them, from bit 2N for N homes, are one bit
%  per scratch family (scratch_family/2) and one for the flags, which
%  only the operand checker reads (docs/perf.md, step 3b). Fails when a
%  line has no audited effects or the CFG is incomplete. The one
%  whole-function analysis the allocator and both checkers share.
body_analysis(Body, Homes, Analysis) :-
    maplist(line_effect, Body, Effects),
    body_analysis(Body, Effects, Homes, Analysis).

%! body_analysis(+Body, +Effects, +Homes, -Analysis) is semidet.
%  As body_analysis/3, with Effects the lines' audited effects.
body_analysis(Body, Effects, Homes,
              analysis(Body, Effects, Homes, Index, LiveOut, LiveIn0, UDs)) :-
    successors(Body, Effects, Succs),
    numbered(Homes, 0, Pairs), list_to_assoc(Pairs, Index),
    length(Homes, NH), Base is 2*NH,
    home_lookup(Pairs, Lookup),
    maplist(line_use_def(Lookup, Base), Body, Effects, UDs),
    lines(Body, 0, Succs, UDs, Lines),
    blocks(Lines, Blocks),
    findall(S-B, nth0(B, Blocks, block(S,_,_)), Starts), list_to_assoc(Starts, Ids),
    maplist(block_summary(Ids), Blocks, Summaries),
    Sum =.. [b|Summaries],
    length(Blocks, NB),
    empty_assoc(In0),
    fixpoint(NB, Sum, In0, In),
    maplist(block_live_out(Ids, In), Blocks, PerBlock),
    append(PerBlock, LiveOut),
    ( get_assoc(0, In, LiveIn0) -> true ; LiveIn0 = 0 ).

numbered([], _, []).
numbered([H|Hs], K, [H-K|Ps]) :- K1 is K+1, numbered(Hs, K1, Ps).

lines([], _, [], [], []).
lines([L|Ls], I, [S|Ss], [UD|UDs], [line(I,L,S,UD)|Rest]) :-
    J is I+1, lines(Ls, J, Ss, UDs, Rest).

% blocks(+Lines, -Blocks): block(Start, Lines, Succs) with the successor
% line indices of its last line.
blocks([], []).
blocks([L|Ls], [block(I, [L|More], Succs)|Bs]) :-
    L = line(I,_,_,_),
    block_rest(L, Ls, More, Succs, Rest),
    blocks(Rest, Bs).

block_rest(line(I,_,Ss,_), Ls, More, Succs, Rest) :-
    J is I+1,
    (   Ss == [J], Ls = [N|Ls1], N = line(J,Line,_,_), Line \= label(_)
    ->  More = [N|More1], block_rest(N, Ls1, More1, Succs, Rest)
    ;   More = [], Succs = Ss, Rest = Ls
    ).

% A block's gen and kill sets, composed backward over its lines.
block_summary(Ids, block(_, Lines, Succs), sum(G, K, SuccIds)) :-
    reverse(Lines, Rev),
    foldl(compose, Rev, 0-0, G-K),
    maplist(block_id(Ids), Succs, SuccIds).
compose(line(_,_,_,ud(U,D)), G0-K0, G-K) :-
    G is U \/ (G0 /\ \ D), K is K0 \/ D.
block_id(Ids, S, B) :- get_assoc(S, Ids, B).

% Backward passes over the blocks until no live-in set changes.
fixpoint(NB, Sum, In0, In) :-
    pass(NB, Sum, In0, In1, false, Changed),
    ( Changed == true -> fixpoint(NB, Sum, In1, In) ; In = In1 ).

pass(0, _, In, In, C, C) :- !.
pass(B1, Sum, In0, In, C0, C) :-
    B is B1-1, arg(B1, Sum, sum(G, K, Ss)),
    foldl(or_live(In0), Ss, 0, Out),
    New is G \/ (Out /\ \ K),
    ( get_assoc(B, In0, Old) -> true ; Old = 0 ),
    ( New =:= Old -> In1 = In0, C1 = C0 ; put_assoc(B, In0, New, In1), C1 = true ),
    pass(B, Sum, In1, In, C1, C).

or_live(In, B, A0, A) :- ( get_assoc(B, In, X) -> true ; X = 0 ), A is A0 \/ X.

% The live-out set of each line of a block, in order.
block_live_out(Ids, In, block(_, Lines, Succs), Outs) :-
    maplist(block_id(Ids), Succs, SuccIds),
    foldl(or_live(In), SuccIds, 0, Out),
    reverse(Lines, Rev),
    line_outs(Rev, Out, [], Outs).
line_outs([], _, Outs, Outs).
line_outs([line(_,_,_,ud(U,D))|Ls], Out, Acc, Outs) :-
    In is U \/ (Out /\ \ D),
    line_outs(Ls, In, [Out|Acc], Outs).

% Uses and definitions of home halves by one line. A write covering a
% whole half defines it; a partial write reads it too.
line_use_def(Lookup, Base, Line, Effect, ud(Use, Def)) :-
    Effect = effect(_,_,_,Ms,_),
    foldl(memory_use_def(Lookup), Ms, 0-0, Use0-Def0),
    extra_use_def(Line, Effect, EU, ED),
    Use is Use0 \/ (EU << Base), Def1 is Def0 \/ (ED << Base),
    Def is Def1 /\ \ Use.

%! scratch_family(?Family, ?Bit) is nondet.
%  The scratch families whose liveness the analysis tracks, by bit; the
%  flags are bit 7.
scratch_family(rax, 0). scratch_family(rcx, 1). scratch_family(rdx, 2).
scratch_family(rsi, 3). scratch_family(rdi, 4). scratch_family(r8, 5).
scratch_family(r9, 6).

% extra_use_def(+Line, +Effect, -Use, -Def): the scratch families and
% flags Line uses and defines, as 8-bit sets. A read at any width uses a
% family, a 32- or 64-bit write defines it, a narrower one uses and
% defines it. A call uses every scratch family (its arity is not known
% here), ret uses rax, rcx and rdx (the fast ABI returns two words in
% rdx and rcx, filc_amd64.pl's return_registers), and the stack-overflow
% jump uses all.
extra_use_def(Line, effect(Rs,Ws,Fl,_,_), Use, Def) :-
    foldl(read_bit, Rs, 0, U0),
    foldl(write_bits, Ws, U0-0, U1-D0),
    % A shift's flags output (read_write: a zero count keeps them) is
    % shared only if its inputs are (flags_after/8), so it need not keep
    % them live: unequal inputs give unequal outputs, which a later read
    % rejects.
    (   Fl == read -> U2 is U1 \/ 128 ; U2 = U1 ),
    (   memberchk(Fl, [write,read_write]) -> Def is D0 \/ 128 ; Def = D0 ),
    (   ( Line = ins(call,_,_) ; Line = ins(jae,none,[plt(filc_stack_overflow_failure)]) )
    ->  Use is U2 \/ 127
    ;   Line = ins(ret,none,[])
    ->  Use is U2 \/ 7
    ;   Use = U2
    ).

read_bit(F, U0, U) :- ( scratch_family(F, B) -> U is U0 \/ (1 << B) ; U = U0 ).
write_bits(write(F,W), U0-D0, U-D) :-
    (   scratch_family(F, B)
    ->  D is D0 \/ (1 << B), ( W < 32 -> U is U0 \/ (1 << B) ; U = U0 )
    ;   U = U0, D = D0
    ).

% home_lookup(+Pairs, -Lookup): the homes' offset-to-number pairs
% bucketed by 8-byte word, so halves/5 looks up the two or three words
% an access can overlap rather than each of its byte offsets.
home_lookup(Pairs, words(Words)) :-
    findall(W-(D-K), ( member(D-K, Pairs), W is D >> 3 ), WPs0),
    keysort(WPs0, WPs), group_pairs_by_key(WPs, Grouped),
    list_to_assoc(Grouped, Words).

memory_use_def(Lookup, read(mem(D,rbp),N), U0-D0, U-D0) :- !,
    halves(Lookup, D, N, _, Touched), U is U0 \/ Touched.
memory_use_def(Lookup, write(mem(D,rbp),N), U0-D0, U-Df) :- !,
    halves(Lookup, D, N, Covered, Touched),
    U is U0 \/ (Touched /\ \ Covered), Df is D0 \/ Covered.
memory_use_def(_, _, UD, UD).

% halves(+Lookup, +D, +N, -Covered, -Touched): bitsets of the home halves
% that bytes [D, D+N) cover entirely and touch at all.
halves(words(Words), D, N, Covered, Touched) :-
    E is D+N, W0 is (D-7) >> 3, W1 is (E-1) >> 3,
    halves_words(W0, W1, Words, D, E, 0, Touched, 0, Covered).
halves_words(W, W1, Words, D, E, T0, T, C0, C) :-
    (   W > W1
    ->  T = T0, C = C0
    ;   (   get_assoc(W, Words, Hs)
        ->  foldl(home_halves(D, E), Hs, T0-C0, T1-C1)
        ;   T1 = T0, C1 = C0
        ),
        W2 is W+1,
        halves_words(W2, W1, Words, D, E, T1, T, C1, C)
    ).

% A home at H overlaps [D, E) when H is within D-7..E-1.
home_halves(D, E, H-K, T0-C0, T-C) :-
    (   H >= D-7, H < E
    ->  half_bits(0, H, K, D, E, T0, T1, C0, C1),
        half_bits(1, H, K, D, E, T1, T, C1, C)
    ;   T = T0, C = C0
    ).

half_bits(Half, H, K, D, E, T0, T, C0, C) :-
    S is H + 4*Half,
    (   S < E, D < S+4
    ->  B is 1 << (2*K+Half), T is T0 \/ B,
        ( D =< S, S+4 =< E -> C is C0 \/ B ; C = C0 )
    ;   T = T0, C = C0
    ).

%% The obligations

obligations(Body, Mapped, analysis(_, _, _, Index, LiveOut, LiveIn0, _)) :-
    assoc_to_list(Mapped, Pairs),
    forall(member(H-_, Pairs), get_assoc(H, Index, _)),
    findall(B, (member(H-_, Pairs), get_assoc(H, Index, K), B is 3 << (2*K)), Bs),
    foldl(or_bits, Bs, 0, All),
    LiveIn0 /\ All =:= 0,
    register_masks(Pairs, Index, Masks),
    scratch_mask(Pairs, Index, Scratch),
    maplist(line_obligation(Mapped, Index, Masks, Scratch, All), Body, LiveOut).

% Each register's mask: both halves of every home mapped to it.
register_masks(Pairs, Index, Masks) :-
    findall(R-M, ( allocatable(R),
                   findall(B, (member(H-R, Pairs), get_assoc(H, Index, K),
                               B is 3 << (2*K)), Bs),
                   foldl(or_bits, Bs, 0, M) ), Masks).
scratch_mask(Pairs, Index, M) :-
    findall(B, (member(H-R, Pairs), memberchk(R, [r10,r11]),
                get_assoc(H, Index, K), B is 3 << (2*K)), Bs),
    foldl(or_bits, Bs, 0, M).
or_bits(B, A0, A) :- A is A0 \/ B.

line_obligation(Mapped, Index, Masks, Scratch, All, Line, Out) :-
    (   substitute(Line, Mapped, _), Line = ins(_,S,[_,mem(D,rbp)])
    ->  get_assoc(D, Mapped, R), get_assoc(D, Index, K),
        memberchk(R-M, Masks),
        Own is 3 << (2*K),
        Out /\ (M /\ \ Own) =:= 0,
        ( S == l -> Out /\ (1 << (2*K+1)) =:= 0 ; true )
    ;   Line = ins(call,_,_)
    ->  Out /\ Scratch =:= 0
    ;   Line = ins(leave,none,[])
    ->  Out /\ All =:= 0
    ;   true
    ).

%% The operand checker (docs/perf.md, step 3b)

%! operand_lives(+Analysis, +Saves, +A, -Lives) is det.
%
%  Lives lists live(In, Out, Effect) for each line of A: the scratch and
%  flags bits before and after it, and its audited effects (line_effect/2,
%  shared with the analysis when the line is the reference's). A is the
%  3a stream of the reference body the shared Analysis is of. A is that body with mapped moves substituted, which
%  changes no scratch or flags use, and with the save and restore moves
%  of Saves inserted (check_regs/5 proved it is exactly that stream);
%  an inserted line touches neither, so it takes the set live before the
%  next reference line.
operand_lives(analysis(Body, Effects, Homes, _, LiveOut, _, UDs), Saves, A, Lives) :-
    length(Homes, N), Base is 2*N,
    ref_lives(Body, Effects, LiveOut, UDs, Base, RLives),
    a_lives(A, RLives, Saves, Lives).

ref_lives([], [], [], [], _, []).
ref_lives([R|Rs], [E|Es], [O|Os], [UD|UDs], Base, [Lv|Lvs]) :-
    line_lives(Base, R, E, O, UD, Lv),
    ref_lives(Rs, Es, Os, UDs, Base, Lvs).

% live(In, Out, R, E): R is the reference line, E its effects.
line_lives(Base, R, E, Out, ud(U,D), live(I8, O8, R, E)) :-
    In is U \/ (Out /\ \ D),
    I8 is (In >> Base) /\ 255, O8 is (Out >> Base) /\ 255.

% Each line of A gets live(In, Out, Effect): a line equal to its reference
% line shares its effects; a substituted or inserted one gets its own.
a_lives([], [], _, []).
a_lives([L|As], RLs, Saves, [live(I,I,E)|Ls]) :-
    save_move(L, Saves), !,
    RLs = [live(I,_,_,_)|_], line_effect(L, E),
    a_lives(As, RLs, Saves, Ls).
a_lives([L|As], [live(I,O,R,E0)|RLs], Saves, [live(I,O,E)|Ls]) :-
    ( L == R -> E = E0 ; line_effect(L, E) ),
    a_lives(As, RLs, Saves, Ls).

save_move(ins(mov,q,[reg(R),mem(S,rbp)]), Saves) :- memberchk(save(R,S), Saves).
save_move(ins(mov,q,[mem(S,rbp),reg(R)]), Saves) :- memberchk(save(R,S), Saves).

%! check_operands(+A, +B, +Lives) is semidet.
%
%  B, the operand rewrite of the implementation body A, makes the same
%  paired lines in the same order on equal values (docs/perf.md, step
%  3b's contract). Lives lists live(In, Out, Effect) for each line of A:
%  the scratch families and flags (8 bits, scratch_family/2) live before
%  and after it, from the shared analysis of the reference
%  (operand_lives/4), and its audited effects. The walk takes A's
%  boundaries from those effects, and B's from its own unless the line
%  is identical to A's. Moves (operand_move/2) execute in their own stream
%  only; boundary lines must be identical, and at each boundary A and B
%  agree on every register compared there.
check_operands(A, B, Lives) :-
    check_operands(A, B, Lives, cells([], [])).

%! check_operands(+A, +B, +Lives, +Cells) is semidet.
%
%  As check_operands/3, with frame cells (docs/perf.md, 5a-loads). Cells
%  is cells(Ds, Others): the rbp displacements of the 8-byte frame words
%  the emitter lists as cells, and the Disp-Bytes ranges of the other
%  frame storage (locals, wide and save slots) they must stay apart from.
%  Stores to cells stay paired lines, so frame memory is the same in A
%  and B at every instruction; a whole 32- or 64-bit load of a cell into
%  a general register is a move in its own stream, reading the cell's
%  symbolic value. The value is shared by A and B, set by paired stores
%  and reset at every region start. A word whose address a `lea`
%  computes is not a cell.
check_operands(A, B, Lives, Cells0) :-
    valid_cells(Cells0, A, Cells),
    shared_state(S0),
    empty_assoc(None),
    operands_walk(A, B, Lives, 0, S0, S0, None, env(S0, Cells, None)).

% valid_cells(+Cells0, +A, -Cells): the cells are distinct, 8-aligned and
% outside every other range; Cells maps those no lea in A addresses.
valid_cells(cells(Ds, Others), A, Cells) :-
    msort(Ds, Ds), sort(Ds, Ds),
    % Distinct multiples of 8 are 8 apart.
    forall(member(D, Ds), ( integer(D), D < 0, D mod 8 =:= 0 )),
    forall(( member(D, Ds), member(O-N, Others) ), ( D+8 =< O ; O+N =< D )),
    findall(E, ( member(ins(lea,_,[M|_]), A), lea_base(M, E) ), Es0), sort(Es0, Es),
    findall(D-cell, ( member(D, Ds),
                      \+ ( member(E, Es), E < D+8, D < E+8 ) ), Ps),
    list_to_assoc(Ps, Cells).
lea_base(mem(E,rbp), E).
lea_base(mem(E,rbp,_), E).

% Lines after a ret, ud2 or jmp and before the next boundary are
% unreachable (state none): they must pair, but nothing is compared.
% CS is the cells' values (cell_value/3), shared by A and B.
operands_walk([], [], [], _, _, _, _, _) :- !.
operands_walk([LA|As], Bs, [_|Ls], J, SA, SB, CS, Env) :-
    stream_move(LA, Env, CS, M), !,
    move_state(M, SA, SA1),
    operands_walk(As, Bs, Ls, J, SA1, SB, CS, Env).
operands_walk(As, [LB|Bs], Ls, J, SA, SB, CS, Env) :-
    stream_move(LB, Env, CS, M), !,
    move_state(M, SB, SB1),
    operands_walk(As, Bs, Ls, J, SA, SB1, CS, Env).
operands_walk([LA|As], [LB|Bs], [live(In,Out,EA)|Ls], J, SA, SB, CS, Env) :-
    Env = env(S0, Cells, None),
    % An identical line has A's effect; line_effect/2 is a function.
    (   LA == LB -> EB = EA ; line_effect(LB, EB) ),
    (   ( boundary_line(LA, EA) ; LA \== LB, boundary_line(LB, EB) )
    ->  LA == LB, CS1 = None,
        ( SA == none -> true ; region_end(In, SA, SB) ),
        (   no_fallthrough(LA, EA)
        ->  SA1 = none, SB1 = none
        ;   region_start(Out, S0, SA1, SB1)
        )
    ;   SA == none
    ->  LA = ins(Op,S,_), LB = ins(Op,S,_), SA1 = none, SB1 = none, CS1 = CS
    ;   paired(LA, LB, J, SA, SB, SA1, SB1),
        cell_writes(EA, LA, J, SA, Cells, CS, CS1)
    ),
    J1 is J+1,
    operands_walk(As, Bs, Ls, J1, SA1, SB1, CS1, Env).

% stream_move(+Line, +Env, +CS, -Move): Line is a move (operand_move/2)
% or a whole load of a cell into a general register other than rsp or
% rbp, as a move of the cell's value.
stream_move(Line, _, _, M) :- operand_move(Line, M), !.
stream_move(ins(mov,S,[mem(D,rbp),reg(Y)]), env(_, Cells, _), CS, move(F, value(V), W)) :-
    get_assoc(D, Cells, _),
    memberchk(S-W, [l-32, q-64]),
    register(Y, F, W), gpr(F), \+ memberchk(F, [rsp,rbp]),
    cell_value(D, CS, V).

% cell_value(+D, +CS, -V): the cell's halves, v(Lo, Hi); a cell not
% written in this region holds its shared start value.
cell_value(D, CS, V) :-
    (   get_assoc(D, CS, V0) -> V = V0
    ;   V = v(in(cell(D),lo,shared), in(cell(D),hi,shared))
    ).

% cell_writes(+Effect, +Line, +J, +SA0, +Cells, +CS0, -CS): the paired
% line J writes the same memory in A and B. A whole store of a register
% or immediate sets the cell from A's source (equal to B's): 64 bits
% both halves, 32 bits the low half, keeping the high half. Any other
% write overlapping a cell gives it a fresh shared value.
cell_writes(effect(_,_,_,Ms,_), Line, J, SA0, Cells, CS0, CS) :-
    foldl(cell_write(Line, J, SA0, Cells), Ms, CS0, CS).

cell_write(Line, J, SA0, Cells, write(mem(D0,rbp),N), CS0, CS) :- !,
    findall(C, ( Lo is D0-7, Hi is D0+N-1, between(Lo, Hi, C), get_assoc(C, Cells, _) ), Cs),
    foldl(cell_store(Line, J, SA0, D0, N), Cs, CS0, CS).
cell_write(_, _, _, _, _, CS, CS).

cell_store(ins(mov,q,[Src,mem(D,rbp)]), _, SA0, D, 8, D, CS0, CS) :-
    store_source(Src, 64, SA0, [Lo,Hi]), !,
    put_assoc(D, CS0, v(Lo,Hi), CS).
cell_store(ins(mov,l,[Src,mem(D,rbp)]), _, SA0, D, 4, D, CS0, CS) :-
    store_source(Src, 32, SA0, [Lo]), !,
    cell_value(D, CS0, v(_,Hi)),
    put_assoc(D, CS0, v(Lo,Hi), CS).
cell_store(_, J, _, _, _, C, CS0, CS) :-
    put_assoc(C, CS0, v(res(J,cell(C),lo), res(J,cell(C),hi)), CS).

store_source(reg(N), W, SA0, V) :- register(N, F, W), gpr(F), read_value(F, W, SA0, V).
store_source(imm(I), W, _, V) :- integer(I), imm_range(W, I), imm_value(I, W, V).

no_fallthrough(_, effect(_,_,_,_,terminal)).
no_fallthrough(ins(jmp,_,_), _).

%! operand_move(+Line, -Move) is semidet.
%  Line is a move: a 32- or 64-bit mov of a general register or an
%  integer immediate into a general register other than rsp or rbp, or
%  a movabs, with its immediate in range. Move is move(Dest, Src, Bits).
operand_move(ins(Op,S,Os), Move) :- move_form(Op, S, Os, Move).

move_form(mov, S, [Src,reg(Y)], move(F, Src1, W)) :-
    memberchk(S-W, [l-32, q-64]),
    register(Y, F, W), gpr(F), \+ memberchk(F, [rsp,rbp]),
    (   Src = reg(X) -> register(X, G, W), gpr(G), Src1 = reg(G)
    ;   Src = imm(I), integer(I), imm_range(W, I), Src1 = imm(I)
    ).
move_form(movabs, q, [imm(I),reg(Y)], move(F, imm(I), 64)) :-
    integer(I), I >= -(1<<63), I < 1<<64,
    register(Y, F, 64), gpr(F), \+ memberchk(F, [rsp,rbp]).

% Facts, so a bound query is deterministic and an unbound one enumerates.
gpr(rax). gpr(rcx). gpr(rdx). gpr(rbx). gpr(rsp). gpr(rbp). gpr(rsi). gpr(rdi).
gpr(r8). gpr(r9). gpr(r10). gpr(r11). gpr(r12). gpr(r13). gpr(r14). gpr(r15).
xmm(xmm0). xmm(xmm1). xmm(xmm2). xmm(xmm3). xmm(xmm4). xmm(xmm5). xmm(xmm6). xmm(xmm7).

% Immediate ranges by operation width; q is a sign-extended imm32.
imm_range(8, I) :- I >= -128, I < 256.
imm_range(16, I) :- I >= -32768, I < 65536.
imm_range(32, I) :- I >= -(1<<31), I < 1<<32.
imm_range(64, I) :- I >= -(1<<31), I < 1<<31.

% The state: st(GPRs, XMMs, Flags); a GPR is v(Low, High).
move_state(_, none, none) :- !.
move_state(move(F, reg(G), 64), st(R0,X,Fl), st(R,X,Fl)) :- !,
    reg_get(G, R0, V), reg_put(F, R0, V, R).
move_state(move(F, reg(G), 32), st(R0,X,Fl), st(R,X,Fl)) :- !,
    reg_get(G, R0, v(Lo,_)), reg_put(F, R0, v(Lo,const(0)), R).
move_state(move(F, value(v(Lo,Hi)), 64), st(R0,X,Fl), st(R,X,Fl)) :- !,
    reg_put(F, R0, v(Lo,Hi), R).
move_state(move(F, value(v(Lo,_)), 32), st(R0,X,Fl), st(R,X,Fl)) :- !,
    reg_put(F, R0, v(Lo,const(0)), R).
move_state(move(F, imm(I), W), st(R0,X,Fl), st(R,X,Fl)) :-
    imm_halves(W, I, Lo, Hi), reg_put(F, R0, v(Lo,Hi), R).

% A 32-bit immediate write zero-extends; a 64-bit one is I mod 2^64.
imm_halves(32, I, const(Lo), const(0)) :- Lo is I mod (1<<32).
imm_halves(64, I, const(Lo), const(Hi)) :-
    U is I mod (1<<64), Lo is U /\ 0xffffffff, Hi is U >> 32.

boundary_line(Line, effect(_,Ws,_,_,Flow)) :-
    (   Flow \== next -> true
    ;   member(write(F,_), Ws), memberchk(F, [rsp,rbp]) -> true
    ;   Line \= ins(_,_,_)
    ).

shared_state(st(R, X, in(flags,shared))) :-
    findall(v(in(F,lo,shared),in(F,hi,shared)), gpr(F), Rs), R =.. [r|Rs],
    findall(in(F,shared), xmm(F), Xs), X =.. [x|Xs].

% The registers of a state are the arguments of r/16 and x/8, in gpr/1's
% and xmm/1's order. put_slot/4 (r/16) and put_xslot/4 (x/8) are
% separate so that a bound index leaves no choicepoint.
reg_get(F, T, V) :- reg_index(F, I), arg(I, T, V).
reg_put(F, T0, V, T) :- reg_index(F, I), put_slot(I, T0, V, T).
put_slot(1, r(_,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16), V, r(V,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(2, r(A1,_,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16), V, r(A1,V,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(3, r(A1,A2,_,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16), V, r(A1,A2,V,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(4, r(A1,A2,A3,_,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16), V, r(A1,A2,A3,V,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(5, r(A1,A2,A3,A4,_,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16), V, r(A1,A2,A3,A4,V,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(6, r(A1,A2,A3,A4,A5,_,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16), V, r(A1,A2,A3,A4,A5,V,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(7, r(A1,A2,A3,A4,A5,A6,_,A8,A9,A10,A11,A12,A13,A14,A15,A16), V, r(A1,A2,A3,A4,A5,A6,V,A8,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(8, r(A1,A2,A3,A4,A5,A6,A7,_,A9,A10,A11,A12,A13,A14,A15,A16), V, r(A1,A2,A3,A4,A5,A6,A7,V,A9,A10,A11,A12,A13,A14,A15,A16)).
put_slot(9, r(A1,A2,A3,A4,A5,A6,A7,A8,_,A10,A11,A12,A13,A14,A15,A16), V, r(A1,A2,A3,A4,A5,A6,A7,A8,V,A10,A11,A12,A13,A14,A15,A16)).
put_slot(10, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,_,A11,A12,A13,A14,A15,A16), V, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,V,A11,A12,A13,A14,A15,A16)).
put_slot(11, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,_,A12,A13,A14,A15,A16), V, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,V,A12,A13,A14,A15,A16)).
put_slot(12, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,_,A13,A14,A15,A16), V, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,V,A13,A14,A15,A16)).
put_slot(13, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,_,A14,A15,A16), V, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,V,A14,A15,A16)).
put_slot(14, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,_,A15,A16), V, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,V,A15,A16)).
put_slot(15, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,_,A16), V, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,V,A16)).
put_slot(16, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,_), V, r(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,V)).
put_xslot(1, x(_,A2,A3,A4,A5,A6,A7,A8), V, x(V,A2,A3,A4,A5,A6,A7,A8)).
put_xslot(2, x(A1,_,A3,A4,A5,A6,A7,A8), V, x(A1,V,A3,A4,A5,A6,A7,A8)).
put_xslot(3, x(A1,A2,_,A4,A5,A6,A7,A8), V, x(A1,A2,V,A4,A5,A6,A7,A8)).
put_xslot(4, x(A1,A2,A3,_,A5,A6,A7,A8), V, x(A1,A2,A3,V,A5,A6,A7,A8)).
put_xslot(5, x(A1,A2,A3,A4,_,A6,A7,A8), V, x(A1,A2,A3,A4,V,A6,A7,A8)).
put_xslot(6, x(A1,A2,A3,A4,A5,_,A7,A8), V, x(A1,A2,A3,A4,A5,V,A7,A8)).
put_xslot(7, x(A1,A2,A3,A4,A5,A6,_,A8), V, x(A1,A2,A3,A4,A5,A6,V,A8)).
put_xslot(8, x(A1,A2,A3,A4,A5,A6,A7,_), V, x(A1,A2,A3,A4,A5,A6,A7,V)).

reg_index(rax,1). reg_index(rcx,2). reg_index(rdx,3). reg_index(rbx,4).
reg_index(rsp,5). reg_index(rbp,6). reg_index(rsi,7). reg_index(rdi,8).
reg_index(r8,9). reg_index(r9,10). reg_index(r10,11). reg_index(r11,12).
reg_index(r12,13). reg_index(r13,14). reg_index(r14,15). reg_index(r15,16).
reg_index(xmm0,1). reg_index(xmm1,2). reg_index(xmm2,3). reg_index(xmm3,4).
reg_index(xmm4,5). reg_index(xmm5,6). reg_index(xmm6,7). reg_index(xmm7,8).

% region_start(+Out, +Shared, -SA, -SB): after a boundary, live scratch families
% and live flags are shared, dead ones distinct per stream; the rest is
% shared.
region_start(Out, st(R0,X,_), st(RA,X,FA), st(RB,X,FB)) :-
    foldl(dead_scratch(Out), [rax,rcx,rdx,rsi,rdi,r8,r9], R0-R0, RA-RB),
    (   Out /\ 128 =\= 0
    ->  FA = in(flags,shared), FB = FA
    ;   FA = in(flags,a), FB = in(flags,b)
    ).
dead_scratch(Out, F, RA0-RB0, RA-RB) :-
    scratch_family(F, Bit),
    (   Out /\ (1 << Bit) =\= 0
    ->  RA = RA0, RB = RB0
    ;   reg_put(F, RA0, v(in(F,lo,a),in(F,hi,a)), RA),
        reg_put(F, RB0, v(In,Hi), RB), In = in(F,lo,b), Hi = in(F,hi,b)
    ).

% region_end(+In, +SA, +SB): at a boundary, A and B agree on both halves
% of every home register, rsp and rbp, every XMM register, each live
% scratch family, and the flags if live.
region_end(In, st(RA,XA,FA), st(RB,XB,FB)) :-
    RA == RB, XA == XB, !,
    ( In /\ 128 =\= 0 -> FA == FB ; true ).
region_end(In, st(RA,XA,FA), st(RB,XB,FB)) :-
    XA == XB,
    % rbx, rsp, rbp and r10-r15 (arguments 4-6 and 11-16) always.
    RA = r(_,_,_,X4,X5,X6,_,_,_,_,X11,X12,X13,X14,X15,X16),
    RB = r(_,_,_,Y4,Y5,Y6,_,_,_,_,Y11,Y12,Y13,Y14,Y15,Y16),
    f(X4,X5,X6,X11,X12,X13,X14,X15,X16) == f(Y4,Y5,Y6,Y11,Y12,Y13,Y14,Y15,Y16),
    forall(( scratch_family(F, Bit), In /\ (1 << Bit) =\= 0 ),
           ( reg_get(F, RA, V), reg_get(F, RB, W), V == W )),
    ( In /\ 128 =\= 0 -> FA == FB ; true ).

%! operand_roles(+Op, +Size, -Roles) is semidet.
%  The role of each explicit operand of an audited non-boundary form:
%  src(W), dst(W), srcdst(W) (a two-address destination) or addr (a
%  memory operand not accessed). W is the operand's width in bits, or
%  unbound when its register gives it (SSE forms).
% Facts, indexed on the mnemonic.
operand_roles(mov, b, [src(8), dst(8)]).
operand_roles(mov, w, [src(16), dst(16)]).
operand_roles(mov, l, [src(32), dst(32)]).
operand_roles(mov, q, [src(64), dst(64)]).
operand_roles(movabs, q, [src(64), dst(64)]).
operand_roles(movzb, b, [src(8), dst(8)]).
operand_roles(movzb, w, [src(8), dst(16)]).
operand_roles(movzb, l, [src(8), dst(32)]).
operand_roles(movzb, q, [src(8), dst(64)]).
operand_roles(movsb, b, [src(8), dst(8)]).
operand_roles(movsb, w, [src(8), dst(16)]).
operand_roles(movsb, l, [src(8), dst(32)]).
operand_roles(movsb, q, [src(8), dst(64)]).
operand_roles(movzw, b, [src(16), dst(8)]).
operand_roles(movzw, w, [src(16), dst(16)]).
operand_roles(movzw, l, [src(16), dst(32)]).
operand_roles(movzw, q, [src(16), dst(64)]).
operand_roles(movsw, b, [src(16), dst(8)]).
operand_roles(movsw, w, [src(16), dst(16)]).
operand_roles(movsw, l, [src(16), dst(32)]).
operand_roles(movsw, q, [src(16), dst(64)]).
operand_roles(movsl, b, [src(32), dst(8)]).
operand_roles(movsl, w, [src(32), dst(16)]).
operand_roles(movsl, l, [src(32), dst(32)]).
operand_roles(movsl, q, [src(32), dst(64)]).
operand_roles(lea, q, [addr, dst(64)]).
operand_roles(add, b, [src(8), srcdst(8)]).
operand_roles(add, w, [src(16), srcdst(16)]).
operand_roles(add, l, [src(32), srcdst(32)]).
operand_roles(add, q, [src(64), srcdst(64)]).
operand_roles(sub, b, [src(8), srcdst(8)]).
operand_roles(sub, w, [src(16), srcdst(16)]).
operand_roles(sub, l, [src(32), srcdst(32)]).
operand_roles(sub, q, [src(64), srcdst(64)]).
operand_roles(and, b, [src(8), srcdst(8)]).
operand_roles(and, w, [src(16), srcdst(16)]).
operand_roles(and, l, [src(32), srcdst(32)]).
operand_roles(and, q, [src(64), srcdst(64)]).
operand_roles(or, b, [src(8), srcdst(8)]).
operand_roles(or, w, [src(16), srcdst(16)]).
operand_roles(or, l, [src(32), srcdst(32)]).
operand_roles(or, q, [src(64), srcdst(64)]).
operand_roles(xor, b, [src(8), srcdst(8)]).
operand_roles(xor, w, [src(16), srcdst(16)]).
operand_roles(xor, l, [src(32), srcdst(32)]).
operand_roles(xor, q, [src(64), srcdst(64)]).
operand_roles(imul, b, [src(8), srcdst(8)]).
operand_roles(imul, w, [src(16), srcdst(16)]).
operand_roles(imul, l, [src(32), srcdst(32)]).
operand_roles(imul, q, [src(64), srcdst(64)]).
operand_roles(btc, b, [src(8), srcdst(8)]).
operand_roles(btc, w, [src(16), srcdst(16)]).
operand_roles(btc, l, [src(32), srcdst(32)]).
operand_roles(btc, q, [src(64), srcdst(64)]).
operand_roles(cmp, b, [src(8), src(8)]).
operand_roles(cmp, w, [src(16), src(16)]).
operand_roles(cmp, l, [src(32), src(32)]).
operand_roles(cmp, q, [src(64), src(64)]).
operand_roles(test, b, [src(8), src(8)]).
operand_roles(test, w, [src(16), src(16)]).
operand_roles(test, l, [src(32), src(32)]).
operand_roles(test, q, [src(64), src(64)]).
operand_roles(neg, b, [srcdst(8)]).
operand_roles(neg, w, [srcdst(16)]).
operand_roles(neg, l, [srcdst(32)]).
operand_roles(neg, q, [srcdst(64)]).
operand_roles(shl, b, [src(8), srcdst(8)]).
operand_roles(shl, w, [src(8), srcdst(16)]).
operand_roles(shl, l, [src(8), srcdst(32)]).
operand_roles(shl, q, [src(8), srcdst(64)]).
operand_roles(shr, b, [src(8), srcdst(8)]).
operand_roles(shr, w, [src(8), srcdst(16)]).
operand_roles(shr, l, [src(8), srcdst(32)]).
operand_roles(shr, q, [src(8), srcdst(64)]).
operand_roles(sar, b, [src(8), srcdst(8)]).
operand_roles(sar, w, [src(8), srcdst(16)]).
operand_roles(sar, l, [src(8), srcdst(32)]).
operand_roles(sar, q, [src(8), srcdst(64)]).
operand_roles(sete, none, [dst(8)]).
operand_roles(setne, none, [dst(8)]).
operand_roles(setz, none, [dst(8)]).
operand_roles(setnz, none, [dst(8)]).
operand_roles(setb, none, [dst(8)]).
operand_roles(setbe, none, [dst(8)]).
operand_roles(seta, none, [dst(8)]).
operand_roles(setae, none, [dst(8)]).
operand_roles(setl, none, [dst(8)]).
operand_roles(setle, none, [dst(8)]).
operand_roles(setg, none, [dst(8)]).
operand_roles(setge, none, [dst(8)]).
operand_roles(sets, none, [dst(8)]).
operand_roles(setns, none, [dst(8)]).
operand_roles(setp, none, [dst(8)]).
operand_roles(setnp, none, [dst(8)]).
operand_roles(cltd, none, []).
operand_roles(cqto, none, []).
% A fence pairs with itself, in its place among the memory accesses.
operand_roles(mfence, none, []).
operand_roles(div, b, [src(8)]).
operand_roles(div, w, [src(16)]).
operand_roles(div, l, [src(32)]).
operand_roles(div, q, [src(64)]).
operand_roles(idiv, b, [src(8)]).
operand_roles(idiv, w, [src(16)]).
operand_roles(idiv, l, [src(32)]).
operand_roles(idiv, q, [src(64)]).
% lock cmpxchg: New, then the memory it compares and writes.
operand_roles('lock cmpxchg', b, [src(8), srcdst(8)]).
operand_roles('lock cmpxchg', w, [src(16), srcdst(16)]).
operand_roles('lock cmpxchg', l, [src(32), srcdst(32)]).
operand_roles('lock cmpxchg', q, [src(64), srcdst(64)]).
operand_roles(movd, none, [src(_), dst(_)]).
operand_roles(movq, none, [src(_), dst(_)]).
operand_roles(add, ss, [src(128), srcdst(128)]).
operand_roles(add, sd, [src(128), srcdst(128)]).
operand_roles(sub, ss, [src(128), srcdst(128)]).
operand_roles(sub, sd, [src(128), srcdst(128)]).
operand_roles(mul, ss, [src(128), srcdst(128)]).
operand_roles(mul, sd, [src(128), srcdst(128)]).
operand_roles(div, ss, [src(128), srcdst(128)]).
operand_roles(div, sd, [src(128), srcdst(128)]).
operand_roles(ucomiss, none, [src(128), src(128)]).
operand_roles(ucomisd, none, [src(128), src(128)]).
operand_roles(cvtss2sd, none, [src(128), srcdst(128)]).
operand_roles(cvtsd2ss, none, [src(128), srcdst(128)]).
operand_roles(cvttss2si, b, [src(128), dst(8)]).
operand_roles(cvttss2si, w, [src(128), dst(16)]).
operand_roles(cvttss2si, l, [src(128), dst(32)]).
operand_roles(cvttss2si, q, [src(128), dst(64)]).
operand_roles(cvttsd2si, b, [src(128), dst(8)]).
operand_roles(cvttsd2si, w, [src(128), dst(16)]).
operand_roles(cvttsd2si, l, [src(128), dst(32)]).
operand_roles(cvttsd2si, q, [src(128), dst(64)]).
operand_roles(cvtsi2ss, b, [src(8), srcdst(128)]).
operand_roles(cvtsi2ss, w, [src(16), srcdst(128)]).
operand_roles(cvtsi2ss, l, [src(32), srcdst(128)]).
operand_roles(cvtsi2ss, q, [src(64), srcdst(128)]).
operand_roles(cvtsi2sd, b, [src(8), srcdst(128)]).
operand_roles(cvtsi2sd, w, [src(16), srcdst(128)]).
operand_roles(cvtsi2sd, l, [src(32), srcdst(128)]).
operand_roles(cvtsi2sd, q, [src(64), srcdst(128)]).

% Implicit operands, read and written at a width, by mnemonic.
implicit(cltd, _, [rax-32], [rdx-32]).
implicit(cqto, _, [rax-64], [rdx-64]).
implicit(div, b, [rax-8,rdx-8], [rax-8,rdx-8]).
implicit(div, w, [rax-16,rdx-16], [rax-16,rdx-16]).
implicit(div, l, [rax-32,rdx-32], [rax-32,rdx-32]).
implicit(div, q, [rax-64,rdx-64], [rax-64,rdx-64]).
implicit(idiv, b, [rax-8,rdx-8], [rax-8,rdx-8]).
implicit(idiv, w, [rax-16,rdx-16], [rax-16,rdx-16]).
implicit(idiv, l, [rax-32,rdx-32], [rax-32,rdx-32]).
implicit(idiv, q, [rax-64,rdx-64], [rax-64,rdx-64]).
% lock cmpxchg reads %rax at its width and writes it: wholly at 32 and
% 64 bits (amd64_contract.pl), the width's part at 8 and 16.
implicit('lock cmpxchg', b, [rax-8], [rax-8]).
implicit('lock cmpxchg', w, [rax-16], [rax-16]).
implicit('lock cmpxchg', l, [rax-32], [rax-64]).
implicit('lock cmpxchg', q, [rax-64], [rax-64]).

% The flags a form defines from its inputs (res), or leaves partly
% undefined or preserved (distinct per stream).
% The SSE arithmetic forms (add, sub, mul, div with ss/sd) preserve them.
% Facts, indexed on the mnemonic.
flags_out(add, b, defined).
flags_out(add, w, defined).
flags_out(add, l, defined).
flags_out(add, q, defined).
flags_out(sub, b, defined).
flags_out(sub, w, defined).
flags_out(sub, l, defined).
flags_out(sub, q, defined).
flags_out(and, b, defined).
flags_out(and, w, defined).
flags_out(and, l, defined).
flags_out(and, q, defined).
flags_out(or, b, defined).
flags_out(or, w, defined).
flags_out(or, l, defined).
flags_out(or, q, defined).
flags_out(xor, b, defined).
flags_out(xor, w, defined).
flags_out(xor, l, defined).
flags_out(xor, q, defined).
flags_out(cmp, b, defined).
flags_out(cmp, w, defined).
flags_out(cmp, l, defined).
flags_out(cmp, q, defined).
flags_out(test, b, defined).
flags_out(test, w, defined).
flags_out(test, l, defined).
flags_out(test, q, defined).
flags_out(neg, b, defined).
flags_out(neg, w, defined).
flags_out(neg, l, defined).
flags_out(neg, q, defined).
flags_out(ucomiss, none, defined).
flags_out(ucomisd, none, defined).
flags_out(shl, b, shift).
flags_out(shl, w, shift).
flags_out(shl, l, shift).
flags_out(shl, q, shift).
flags_out(shr, b, shift).
flags_out(shr, w, shift).
flags_out(shr, l, shift).
flags_out(shr, q, shift).
flags_out(sar, b, shift).
flags_out(sar, w, shift).
flags_out(sar, l, shift).
flags_out(sar, q, shift).
flags_out(imul, b, undefined).
flags_out(imul, w, undefined).
flags_out(imul, l, undefined).
flags_out(imul, q, undefined).
flags_out(btc, b, undefined).
flags_out(btc, w, undefined).
flags_out(btc, l, undefined).
flags_out(btc, q, undefined).
flags_out(div, b, undefined).
flags_out(div, w, undefined).
flags_out(div, l, undefined).
flags_out(div, q, undefined).
flags_out(idiv, b, undefined).
flags_out(idiv, w, undefined).
flags_out(idiv, l, undefined).
flags_out(idiv, q, undefined).
flags_out('lock cmpxchg', b, defined).
flags_out('lock cmpxchg', w, defined).
flags_out('lock cmpxchg', l, defined).
flags_out('lock cmpxchg', q, defined).

%! paired(+LA, +LB, +J, +SA0, +SB0, -SA, -SB) is semidet.
paired(ins(Op,S,OsA), ins(Op,S,OsB), J, SA0, SB0, SA, SB) :-
    once(operand_roles(Op, S, Roles)),
    sources(Roles, OsA, OsB, Op, SA0, SB0),
    (   implicit(Op, S, Reads, _)
    ->  forall(member(F-W, Reads), ( read_value(F, W, SA0, V), read_value(F, W, SB0, V1), V == V1 ))
    ;   true
    ),
    (   flags_read(Op) -> SA0 = st(_,_,FA0), SB0 = st(_,_,FB0), FA0 == FB0 ; true ),
    writes(Roles, OsA, 1, J, SA0, SA1),
    writes(Roles, OsB, 1, J, SB0, SB1),
    (   implicit(Op, S, _, Writes)
    ->  foldl(implicit_write(J), Writes, SA1, SA2), foldl(implicit_write(J), Writes, SB1, SB2)
    ;   SA2 = SA1, SB2 = SB1
    ),
    flags_after(Op, S, J, SA0, SB0, SA2, SB2, SA, SB).

% sources(+Roles, +OsA, +OsB, +Op, +SA, +SB): one role per operand of
% both lines, and each operand pair matches in the pre-states.
sources([], [], [], _, _, _).
sources([R|Rs], [OA|OsA], [OB|OsB], Op, SA, SB) :-
    role_sources(R, Op, SA, SB, OA, OB),
    sources(Rs, OsA, OsB, Op, SA, SB).

% writes(+Roles, +Os, +P, +J, +S0, -S): register destinations at
% positions P.. get res(J,P).
writes([], [], _, _, S, S).
writes([R|Rs], [O|Os], P, J, S0, S) :-
    role_write(R, O, P, J, S0, S1),
    P1 is P+1,
    writes(Rs, Os, P1, J, S1, S).

role_write(dst(_), O, P, J, S0, S) :- !, register_write(O, P, J, S0, S).
role_write(srcdst(_), O, P, J, S0, S) :- !, register_write(O, P, J, S0, S).
role_write(_, _, _, _, S, S).

register_write(reg(N), P, J, S0, S) :- !,
    register(N, F, W), write_value(F, W, res(J,P), S0, S).
register_write(_, _, _, S, S).

% setcc reads the flags; a shift's flags output depends on its input
% (flags_after/9), jcc is a boundary.
flags_read(Op) :- atom_concat(set, _, Op).

flags_after(Op, S, J, st(_,_,FA0), st(_,_,FB0), st(RA,XA,_), st(RB,XB,_),
            st(RA,XA,FA), st(RB,XB,FB)) :-
    (   flags_out(Op, S, K) -> true ; K = preserve ),
    (   K == defined -> FA = res(J,flags), FB = FA
    ;   K == shift, FA0 == FB0 -> FA = res(J,flags), FB = FA
    ;   K \== preserve -> FA = res(J,flags,a), FB = res(J,flags,b)
    ;   FA = FA0, FB = FB0
    ).

% Sources: equal values at the role's width; memory operands of the same
% form on equal addressing registers; other operands identical.

role_sources(dst(W), _, SA, SB, OA, OB) :- place_match(W, SA, SB, OA, OB).
role_sources(addr, _, SA, SB, OA, OB) :- memory_match(SA, SB, OA, OB).
role_sources(src(W), Op, SA, SB, OA, OB) :- source_match(Op, W, SA, SB, OA, OB).
role_sources(srcdst(W), Op, SA, SB, OA, OB) :-
    source_match(Op, W, SA, SB, OA, OB), place_match(W, SA, SB, OA, OB).

% A destination: registers of the same width (any register), or the
% same memory operand.
place_match(W, SA, SB, OA, OB) :-
    (   OA = reg(A), OB = reg(B)
    ->  register(A, FA, W), register(B, FB, W), \+ memberchk(FA, [rsp,rbp]),
        \+ memberchk(FB, [rsp,rbp])
    ;   memory_match(SA, SB, OA, OB)
    ).

source_match(Op, W, SA, SB, OA, OB) :-
    (   memory_match(SA, SB, OA, OB) -> true
    ;   operand_value(OA, Op, W, SA, VA), operand_value(OB, Op, W, SB, VB), VA == VB
    ).

operand_value(reg(N), _, W, S, V) :- register(N, F, W), read_value(F, W, S, V).
operand_value(imm(I), Op, W, _, V) :-
    integer(W),
    (   integer(I)
    ->  ( Op == movabs -> I >= -(1<<63), I < 1<<64 ; imm_range(W, I) ),
        imm_value(I, W, V)
    ;   V = [sym(I)]
    ).

imm_value(I, 64, [const(Lo),const(Hi)]) :- !,
    U is I mod (1<<64), Lo is U /\ 0xffffffff, Hi is U >> 32.
imm_value(I, W, [const(V)]) :- V is I mod (1<<W).

% read_value(+F, +W, +S, -V): register family F read at W bits.
read_value(F, W, S, V) :- width_read(W, F, S, V).

width_read(128, F, st(_,X,_), [V]) :- reg_get(F, X, V).
width_read(64, F, st(R,_,_), [Lo,Hi]) :- reg_get(F, R, v(Lo,Hi)).
width_read(32, F, st(R,_,_), [Lo]) :- reg_get(F, R, v(Lo,_)).
width_read(16, F, st(R,_,_), [V]) :- reg_get(F, R, v(Lo,_)), narrow(word, Lo, V).
width_read(8, F, st(R,_,_), [V]) :- reg_get(F, R, v(Lo,_)), narrow(byte, Lo, V).

narrow(byte, const(N), const(M)) :- !, M is N /\ 255.
narrow(word, const(N), const(M)) :- !, M is N /\ 65535.
narrow(byte, merge8(_,N), N) :- !.
narrow(word, merge16(_,N), N) :- !.
narrow(byte, merge16(_,N), V) :- !, narrow(byte, N, V).
narrow(K, X, V) :- V =.. [K,X].

% memory_match(+SA, +SB, +OA, +OB): the same memory operand on equal
% addressing registers, or the same non-register, non-immediate operand.
memory_match(SA, SB, OA, OB) :-
    (   OA = mem(D,BA), OB = mem(D,BB)
    ->  same_base(SA, SB, BA, BB)
    ;   OA = mem(D,BA,IA), OB = mem(D,BB,IB)
    ->  same_base(SA, SB, BA, BB), same_base(SA, SB, IA, IB)
    ;   OA \= reg(_), OA \= imm(_), OA \= mem(_,_), OA \= mem(_,_,_), OA == OB
    ).
same_base(SA, SB, A, B) :-
    register(A, FA, 64), register(B, FB, 64),
    read_value(FA, 64, SA, V), read_value(FB, 64, SB, W), V == W.

implicit_write(J, F-W, S0, S) :- write_value(F, W, res(J,F), S0, S).

% write_value(+F, +W, +V, +S0, -S): V written to F at W bits.
write_value(F, 128, V, st(R,X0,Fl), st(R,X,Fl)) :- !, reg_index(F, I), put_xslot(I, X0, V, X).
write_value(F, W, V, st(R0,X,Fl), st(R,X,Fl)) :-
    reg_index(F, I), arg(I, R0, Old),
    written(W, V, Old, New),
    put_slot(I, R0, New, R).

written(64, V, _, v(lo(V),hi(V))).
written(32, V, _, v(lo(V),const(0))).
written(16, V, v(Lo0,Hi0), v(merge16(Lo0,lo(V)),Hi0)).
written(8, V, v(Lo0,Hi0), v(merge8(Lo0,lo(V)),Hi0)).

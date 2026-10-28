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
           allocatable/1, callee_saved/1]).

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
        Analysis = analysis(Body0, Effects, _, _, _, _),
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
    body_analysis(Body, Homes, analysis(_, _, _, _, LiveOut, LiveIn0)).

%! body_analysis(+Body, +Homes, -Analysis) is semidet.
%  Analysis = analysis(Body, Effects, Homes, Index, LiveOut, LiveIn0):
%  each line's audited effects, the home offsets and their bit numbers
%  (Index), and home_liveness/4's results. Fails when a line has no
%  audited effects or the CFG is incomplete. The one whole-function
%  analysis the allocator and the checker share.
body_analysis(Body, Homes, Analysis) :-
    maplist(line_effect, Body, Effects),
    body_analysis(Body, Effects, Homes, Analysis).

%! body_analysis(+Body, +Effects, +Homes, -Analysis) is semidet.
%  As body_analysis/3, with Effects the lines' audited effects.
body_analysis(Body, Effects, Homes,
              analysis(Body, Effects, Homes, Index, LiveOut, LiveIn0)) :-
    successors(Body, Effects, Succs),
    numbered(Homes, 0, Pairs), list_to_assoc(Pairs, Index),
    maplist(line_use_def(Index), Effects, UDs),
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
line_use_def(Index, effect(_,_,_,Ms,_), ud(Use, Def)) :-
    foldl(memory_use_def(Index), Ms, 0-0, Use-Def0),
    Def is Def0 /\ \ Use.

memory_use_def(Index, read(mem(D,rbp),N), U0-D0, U-D0) :- !,
    halves(Index, D, N, _, Touched), U is U0 \/ Touched.
memory_use_def(Index, write(mem(D,rbp),N), U0-D0, U-Df) :- !,
    halves(Index, D, N, Covered, Touched),
    U is U0 \/ (Touched /\ \ Covered), Df is D0 \/ Covered.
memory_use_def(_, _, UD, UD).

% halves(+Index, +D, +N, -Covered, -Touched): bitsets of the home halves
% that bytes [D, D+N) cover entirely and touch at all.
halves(Index, D, N, Covered, Touched) :-
    E is D+N, H0 is D-7, H1 is E-1,
    findall(B-C, ( between(H0, H1, H), get_assoc(H, Index, K),
                   between(0, 1, Half), S is H + 4*Half, S < E, D < S+4,
                   B is 1 << (2*K+Half),
                   ( D =< S, S+4 =< E -> C = B ; C = 0 ) ), BCs),
    foldl(or_pair, BCs, 0-0, Touched-Covered).

or_pair(B-C, T0-C0, T-C1) :- T is T0 \/ B, C1 is C0 \/ C.

%% The obligations

obligations(Body, Mapped, analysis(_, _, _, Index, LiveOut, LiveIn0)) :-
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

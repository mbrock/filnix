/** <module> Lifting annotated x86-64 assembly to nanofil IR

    swipl lift.pl FILE.s >FILE.ir

reads the integer subset of x86-64 that memcmp.s and
../ct-bn-add/bn_add.s use and prints nanofil's unchecked IR for each function that has a SaRCAsm signature.
nanofil then inserts the checks, validates the result and emits its own
assembly, so nothing here has to be trusted for memory safety: a wrong
row in the table gives a wrong answer, never an unchecked access.

The lifter is driven by the effect table of table.pl. A row's register
reads and writes say which registers must hold what on entry and what
they hold afterwards, its flags say whether ZF and CF are available to
a later instruction, its control says where the block ends, and its
action says which IR instructions compute the value.

  - A register is a temporary named after it and the source line that
    wrote it. Each block starts with a phi for every register that has
    one type on every way in; unused and single-valued phis are removed.
  - A register holds a pointer, a 64-bit integer, or an integer of
    which only the low byte is defined (a byte write to a register that
    was not a 64-bit integer). Reading more than a register holds is an
    error, so a register read before it is written is an error.
  - A byte write to a 64-bit integer keeps the other 56 bits.
  - ZF is remembered as the two values whose difference it tests, and
    becomes a `cmp` where a branch or conditional move reads it. It
    does not cross a block boundary.
  - CF is remembered as the unsigned comparisons that are true when it
    is set, and becomes a 0 or 1 in a temporary where `adc`, `sbb` or a
    branch reads it. A block that reads the CF it is entered with has
    a phi for it, and each block before it computes the temporary.
  - The conditions translated are `e` and `ne` (ZF) and `b` and `ae`
    (CF).
  - A conditional move is a `select`.
*/
:- module(lift, [lift_file/2, print_functions/1]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(yall)).
:- use_module(asm).
:- use_module(table).

:- initialization(main, main).

main :-
    current_prolog_flag(argv, Argv),
    (   Argv = [Path]
    ->  catch(lift_file(Path, Functions), error(E),
              ( format(user_error, "lift: ~w: ~q~n", [Path, E]), halt(1) )),
        file_base_name(Path, Base),
        format("% ~w lifted by experiments/ct-memcmp/lift/lift.pl. The number after a~n", [Base]),
        format("% line is the line of ~w it comes from.~n", [Base]),
        print_functions(Functions)
    ;   format(user_error, "usage: swipl lift.pl FILE.s~n", []),
        halt(2)
    ).

%! lift_file(+Path, -Functions) is det.
%
%  Functions are the functions of the assembly file at Path as nanofil
%  IR: `func(Name, Linkage, Class, Params, Blocks)` as nanofil reads
%  it, except that each instruction is `Line-Instruction` and each
%  terminator `Line-Terminator`. Throws `error(at(Line, Reason))`, or
%  `error(Reason)`, for assembly outside the subset.
lift_file(Path, Functions) :-
    parse_file(Path, Statements),
    findall(N, member(located(_, directive('.globl', [N])), Statements), Globals),
    exclude([located(_, directive(_, _))]>>true, Statements, Code),
    sources(Code, Globals, Sources),
    maplist(lift_function, Sources, Functions).

% sources(+Code, +Globals, -Sources): the code split at the labels that
% have a signature.
sources([], _, []).
sources([located(_, label(Name)), located(_, signature(Result, Args))|Code0], Globals,
        [source(Name, Linkage, Result, Args, Body)|Sources]) :- !,
    ( memberchk(Name, Globals) -> Linkage = export ; Linkage = local ),
    body(Code0, Body, Code),
    sources(Code, Globals, Sources).
sources([located(L, S)|_], _, _) :- throw(error(at(L, outside_a_function(S)))).

body([S1, S2|Code], [], [S1, S2|Code]) :-
    S1 = located(_, label(_)), S2 = located(_, signature(_, _)), !.
body([S|Code0], [S|Body], Code) :- body(Code0, Body, Code).
body([], [], []).

lift_function(source(Name, Linkage, Result, Args, Body), func(Name, Linkage, Class, Params, Blocks)) :-
    (   memberchk(Result-Class, [int-w, long-l, size_t-l])
    ->  true
    ;   throw(error(result_type(Name, Result)))
    ),
    parameters(Args, [rdi, rsi, rdx, rcx, r8, r9], Name, Params, Types0),
    sort(Types0, Types),
    blocks(start, Body, Blocks0),
    check_blocks(Name, Blocks0),
    entry_types(Blocks0, Types, Ins),
    carry_in(Blocks0, Carries),
    maplist(translate_block(Ins, Carries), Blocks0, Blocks1),
    maplist(with_phis(Ins, Blocks1), Blocks1, Blocks2),
    remove_dead_phis(Blocks2, Blocks3),
    remove_trivial_phis(Blocks3, Blocks).

parameters([], _, _, [], []).
parameters([T|Ts], [R|Rs], Name, [param(Class, tmp(P))|Ps], [R-Type|Types]) :-
    (   memberchk(T-Class-Type, [ptr-p-pointer, size_t-l-integer(64), long-l-integer(64)])
    ->  true
    ;   throw(error(parameter_type(Name, T)))
    ),
    temporary(R, 0, P),
    parameters(Ts, Rs, Name, Ps, Types).

%  ## Blocks

% blocks(+Name, +Statements, -Blocks): the statements as
% block(Name, Items, exit(Line, Semantics, Successors)). An Item is
% Line-Semantics for an instruction that goes on to the next one;
% Semantics is `fallthrough` where a label ends the block.
blocks(Name, Stmts, [block(Name, Items, Exit)|Blocks]) :-
    straight(Stmts, Items, Exit, Next, Rest),
    ( Next == none -> Blocks = [] ; blocks(Next, Rest, Blocks) ).

straight([], _, _, _, _) :- throw(error(falls_off_the_end)).
straight([located(L, label(Label))|Rest], [], exit(L, fallthrough, [Name]), Name, Rest) :- !,
    block_name(Label, Name).
straight([located(L, instruction(M, Os))|Rest0], Items, Exit, Next, Rest) :-
    catch(semantics(instruction(M, Os), Sem), error(E), throw(error(at(L, E)))),
    Sem = semantics(_, effects(_, _, _, control(Control), _)),
    (   Control == next
    ->  Items = [L-Sem|Items1],
        straight(Rest0, Items1, Exit, Next, Rest)
    ;   Items = [],
        Exit = exit(L, Sem, Succs),
        after(Control, L, Rest0, Succs, Next, Rest)
    ).

% after(+Control, +Line, +Rest0, -Successors, -Next, -Rest): where a
% control instruction goes, and the block the following statements make.
after(branch(_, Label), L, Rest0, [Then, Next], Next, Rest) :- !,
    block_name(Label, Then),
    (   Rest0 = [located(_, label(Label1))|Rest]
    ->  block_name(Label1, Next)
    ;   Rest0 = [_|_]
    ->  atom_concat(after, L, Next), Rest = Rest0
    ;   throw(error(at(L, falls_off_the_end)))
    ).
after(Control, _, Rest0, Succs, Next, Rest) :-
    ( Control = jump(Label) -> block_name(Label, Target), Succs = [Target] ; Succs = [] ),
    (   Rest0 = [located(_, label(Label1))|Rest]
    ->  block_name(Label1, Next)
    ;   Rest0 = []
    ->  Next = none, Rest = []
    ;   Rest0 = [located(L1, S)|_],
        throw(error(at(L1, unreachable(S))))
    ).

% .Loop_cmp is the block loop_cmp.
block_name(Label, Name) :-
    ( atom_concat('.', Rest, Label) -> true ; Rest = Label ),
    downcase_atom(Rest, Name).

check_blocks(Fn, Blocks) :-
    maplist([block(N, _, _), N]>>true, Blocks, Names),
    (   msort(Names, Sorted), sort(Names, Sorted)
    ->  true
    ;   throw(error(duplicate_block(Fn, Names)))
    ),
    forall(( member(block(_, _, exit(L, _, Succs)), Blocks), member(S, Succs) ),
           (   memberchk(S, Names), S \== start
           ->  true
           ;   throw(error(at(L, no_such_block(S))))
           )).

%  ## What each register holds on entry to a block

% entry_types(+Blocks, +Params, -Ins): Ins pairs each block name with
% the sorted Register-Type list that holds on every way into it: the
% greatest fixpoint, starting from `top` (not reached yet). A Type is
% `pointer`, `integer(64)`, or `integer(8)`.
entry_types(Blocks, Params, Ins) :-
    maplist([block(N, _, _), N-top]>>true, Blocks, Ins0),
    entry_types_(Blocks, Params, Ins0, Ins),
    (   member(N-top, Ins)
    ->  throw(error(unreachable_block(N)))
    ;   true
    ).

entry_types_(Blocks, Params, Ins0, Ins) :-
    maplist(in_types(Blocks, Params, Ins0), Ins0, Ins1),
    ( Ins1 == Ins0 -> Ins = Ins0 ; entry_types_(Blocks, Params, Ins1, Ins) ).

in_types(_, Params, _, start-_, start-Params) :- !.
in_types(Blocks, _, Ins0, Name-_, Name-Types) :-
    findall(Out,
            ( member(block(P, Items, exit(_, _, Succs)), Blocks),
              memberchk(Name, Succs),
              memberchk(P-In, Ins0),
              In \== top,
              foldl(item_types, Items, In, Out) ),
            Outs),
    ( Outs = [O|Os] -> foldl(meet, Os, O, Types) ; Types = top ).

item_types(_-semantics(_, effects(registers(_, Writes), _, _, _, _)), Types0, Types) :-
    foldl(write_type, Writes, Types0, Types).

write_type(Write, Types0, Types) :-
    written(Write, [R, T]>>memberchk(R-T, Types0), Register, Type),
    exclude([R-_]>>(R == Register), Types0, Types1),
    ( Type == none -> Types = Types1 ; sort([Register-Type|Types1], Types) ).

% written(+Write, :TypeOf, -Register, -Type): what a write of the table
% leaves in Register, `none` for a copy of an undefined register.
written(write(register(R, _), Kind, Mode), TypeOf, R, Type) :-
    (   Mode == keep_upper
    ->  ( call(TypeOf, R, integer(64)) -> Type = integer(64) ; Type = integer(8) )
    ;   Kind = same_type_as(register(S, _))
    ->  ( call(TypeOf, S, Type0) -> Type = Type0 ; Type = none )
    ;   Kind == pointer
    ->  Type = pointer
    ;   Type = integer(64)
    ).

meet(A, B, M) :-
    findall(R-T, ( member(R-Ta, A), memberchk(R-Tb, B), meet_type(Ta, Tb, T) ), M).

meet_type(T, T, T) :- !.
meet_type(integer(_), integer(_), integer(8)).

%  ## The blocks that are entered with a carry

% carry_in(+Blocks, -Names): the blocks that read CF as it is on entry,
% themselves or in a block they go on to: the least fixpoint.
carry_in(Blocks, Names) :- carry_in_(Blocks, [], Names).

carry_in_(Blocks, Names0, Names) :-
    findall(N,
            ( member(block(N, Items, exit(_, Exit, Succs)), Blocks),
              pairs_values(Items, Sems0),
              ( Exit == fallthrough -> Sems = Sems0 ; append(Sems0, [Exit], Sems) ),
              carry_use(Sems, Use),
              (   Use == reads
              ->  true
              ;   Use == passes, member(S, Succs), memberchk(S, Names0)
              ->  true
              ) ),
            Names1),
    ( Names1 == Names0 -> Names = Names0 ; carry_in_(Blocks, Names1, Names) ).

% carry_use(+Rows, -Use): whether the rows read the CF they start with
% (`reads`), leave it as it was (`passes`), or change it first (`kills`).
carry_use([], passes).
carry_use([semantics(_, effects(_, _, flags(reads(Reads), _, _, _, preserved(Preserved)), _, _))|Sems], Use) :-
    (   memberchk(cf, Reads)
    ->  Use = reads
    ;   memberchk(cf, Preserved)
    ->  carry_use(Sems, Use)
    ;   Use = kills
    ).

%  ## Translation

% translate_block(+Ins, +Carries, +Block, -Translated): Translated is
% block(Name, Registers, Instructions, Line-Terminator, Env): the
% registers that get a phi, and the environment at the end. An
% environment pairs a register with val(Operand, Type). The carry a
% block is entered with, or leaves to a block of Carries, is the
% register `cf`, a 64-bit integer.
%
% The flags between two instructions are fl(Zf, Cf). Zf is `none` or
% zf(Width, A, B): ZF is set when the low Width bits of A and B are
% equal. Cf is `none`, known(V) for a V that is 0 or 1, or below(Pairs):
% CF is set when A is below B, unsigned, for some A-B of Pairs.
translate_block(Ins, Carries, block(Name, Items, Exit), block(Name, Registers, Insts, Term, Env)) :-
    memberchk(Name-Types, Ins),
    ( Name == start -> Suffix = 0, Registers0 = [] ; Suffix = Name, Registers0 = Types ),
    maplist({Suffix}/[R-T, R-val(tmp(V), T)]>>temporary(R, Suffix, V), Types, Env0),
    (   Name \== start, memberchk(Name, Carries)
    ->  temporary(cf, Name, Carry),
        Cf0 = known(tmp(Carry)),
        append(Registers0, [cf-integer(64)], Registers)
    ;   Cf0 = none,
        Registers = Registers0
    ),
    Exit = exit(Line, _, Succs),
    phrase(( items(Items, Env0, fl(none, Cf0), Env1, F1),
             terminator(Exit, Env1, F1, F, Term),
             carry_out(Succs, Carries, Line, F, Env1, Env) ),
           Insts).

items([], E, F, E, F) --> [].
items([L-semantics(Action, effects(registers(Reads, Writes), _, Flags, _, _))|Items], E0, F0, E, F) -->
    { maplist(check_read(E0, L), Reads),
      check_flag_reads(Flags, F0, L) },
    translation(Action, L, E0, F0, Value, Computed),
    { foldl(write_env(Value), Writes, E0, E1),
      next_flags(Flags, Computed, F0, L, F1) },
    items(Items, E1, F1, E, F).

% carry_out(+Successors, +Carries, +Line, +Flags, +Env0, -Env)//: the
% carry in a temporary, as the register `cf` of Env, when a successor
% is entered with it.
carry_out(Succs, Carries, L, fl(_, Cf), E0, E) -->
    (   { member(S, Succs), memberchk(S, Carries) }
    ->  carry(Cf, L, V),
        { E = [cf-val(V, integer(64))|E0] }
    ;   { E = E0 }
    ).

check_read(E, L, read(register(R, W), Kind)) :-
    ( memberchk(R-val(_, T), E) -> true ; T = undefined ),
    (   readable(Kind, W, T)
    ->  true
    ;   throw(error(at(L, register(R, needs(Kind, W), holds(T)))))
    ).

readable(integer, 64, integer(64)).
readable(integer, 8, integer(_)).
readable(pointer, 64, pointer).
readable(value, 64, integer(64)).
readable(value, 64, pointer).

check_flag_reads(flags(reads(Reads), _, _, _, _), fl(Z, C), L) :-
    forall(member(Flag, Reads),
           (   memberchk(Flag-Held, [zf-Z, cf-C])
           ->  ( Held == none -> throw(error(at(L, unavailable_flag(Flag)))) ; true )
           ;   throw(error(at(L, unsupported_flags(Reads))))
           )).

% next_flags(+Flags, +Computed, +F0, +Line, -F): the flags after an
% instruction whose action computes them as Computed, by the row's
% partition of the flags. A CF the action has no recipe for is
% unavailable to the instructions after it.
next_flags(flags(_, defined(Defined), cleared(Cleared), _, preserved(Preserved)),
           fl(Zf, Cf), fl(Z0, C0), L, fl(Z, C)) :-
    (   memberchk(zf, Defined)
    ->  ( Zf == none -> throw(error(at(L, missing_flag_recipe))) ; Z = Zf )
    ;   memberchk(zf, Preserved)
    ->  Z = Z0
    ;   Z = none
    ),
    (   memberchk(cf, Defined)
    ->  C = Cf
    ;   memberchk(cf, Cleared)
    ->  C = known(const(0))
    ;   memberchk(cf, Preserved)
    ->  C = C0
    ;   C = none
    ).

write_env(Value, Write, E0, E) :-
    written(Write, [R, T]>>memberchk(R-val(_, T), E0), Register, Type),
    exclude([R-_]>>(R == Register), E0, E1),
    ( Type == none -> E = E1 ; E = [Register-val(Value, Type)|E1] ).

% translation(+Action, +Line, +Env, +Flags0, -Value, -Flags)//: the IR
% instructions of Action; Value is what its register write stores and
% Flags are the ZF and CF it computes, which next_flags/5 keeps for the
% flags the row says it defines.
translation(Action, L, E, F0, Value, F) --> action(Action, L, E, F0, Value, F), !.
translation(Action, L, _, _, _, _) --> { throw(error(at(L, no_translation(Action)))) }.

% A move's flags are read only for `xor` or `sub` of a register with
% itself.
action(move(immediate(N), _), _, _, _, V, fl(zf(64, V, const(0)), known(const(0)))) -->
    { constant(N, V) }.
action(copy(S, _), _, E, _, V, fl(none, none)) -->
    { value(S, E, V) }.
action(load(A, 8, register(R, 64)), L, E, _, tmp(T), fl(none, none)) -->
    address(A, L, E, P),
    { temporary(R, L, T) },
    [L-let(tmp(T), l, load(l), [P])].
action(load(A, 1, register(R, 8)), L, E, _, tmp(T), fl(none, none)) -->
    address(A, L, E, P),
    { temporary(R, L, T) },
    (   { memberchk(R-val(Old, integer(64)), E) }
    ->  { temporary(m, L, M), temporary(h, L, H), Mask is (1 << 64) - 256 },
        [L-let(tmp(M), l, load(ub), [P]),
         L-let(tmp(H), l, and, [Old, const(Mask)]),
         L-let(tmp(T), l, or, [tmp(H), tmp(M)])]
    ;   [L-let(tmp(T), l, load(ub), [P])]
    ).
action(store(A, 8, S), L, E, _, none, fl(none, none)) -->
    address(A, L, E, P),
    source(S, L, E, V),
    [L-store(l, V, P)].
action(offset(address(register(B, 64), immediate(0), 1, Offset), register(R, 64)), L, E, _, tmp(T), fl(none, none)) -->
    { memberchk(B-val(V, Type), E), temporary(R, L, T),
      ( Type == pointer -> Class = p ; Class = l ) },
    [L-let(tmp(T), Class, add, [V, const(Offset)])].
% A byte `xor` or `or` with a zero-extended source leaves the other 56
% bits as they were, so it is the 64-bit operation.
action(binary(K, S, register(R, W)), L, E, _, tmp(T), fl(zf(W, tmp(T), const(0)), Cf)) -->
    { ( W =:= 64 -> memberchk(K, [add, sub, and, or, xor]) ; memberchk(K, [or, xor]) ),
      value(register(R, W), E, Old), temporary(R, L, T) },
    source(S, L, E, V0),
    low(W, S, V0, L, V),
    [L-let(tmp(T), l, K, [Old, V])],
    { binary_carry(K, Old, V, tmp(T), Cf) }.
action(with_carry(K, S, register(R, 64)), L, E, fl(_, Cf0), tmp(T), fl(zf(64, tmp(T), const(0)), below(Pairs))) -->
    { value(register(R, 64), E, Old), temporary(R, L, T), temporary(t, L, T1) },
    carry(Cf0, L, C),
    source(S, L, E, V),
    [L-let(tmp(T1), l, K, [Old, V]),
     L-let(tmp(T), l, K, [tmp(T1), C])],
    { with_carry_pairs(K, Old, V, tmp(T1), C, tmp(T), Pairs) }.
action(compare(sub, S, register(R, W)), L, E, _, none, fl(zf(W, Old, V), Cf)) -->
    { value(register(R, W), E, Old) },
    source(S, L, E, V),
    { W =:= 64 -> Cf = below([Old-V]) ; Cf = none }.
action(shift(K, Count, register(R, 64)), L, E, _, tmp(T), fl(zf(64, tmp(T), const(0)), none)) -->
    { memberchk(K, [shl, shr]), value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, K, [Old, const(Count)])].
action(unary(dec, register(R, 64)), L, E, _, tmp(T), fl(zf(64, tmp(T), const(0)), none)) -->
    { value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, sub, [Old, const(1)])].
% neg sets CF unless the operand is 0.
action(unary(neg, register(R, 64)), L, E, _, tmp(T), fl(zf(64, tmp(T), const(0)), below([const(0)-Old]))) -->
    { value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, neg, [Old])].
action(conditional_move(C, S, register(R, 64)), L, E, F0, tmp(T), fl(none, none)) -->
    condition(C, F0, L, Cond, _),
    { value(S, E, V), value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, select, [Cond, V, Old])].

% binary_carry(+K, +Old, +V, +Result, -Cf): CF after the 64-bit Result
% of Old K V. A sum wrapped if it is below an addend; a difference
% borrowed if the subtrahend is above. `and`, `or` and `xor` clear CF,
% which their rows say.
binary_carry(add, Old, _, Sum, below([Sum-Old])) :- !.
binary_carry(sub, Old, V, _, below([Old-V])) :- !.
binary_carry(_, _, _, _, none).

% with_carry_pairs(+K, +Old, +V, +First, +C, +Result, -Pairs): CF after
% Result = (Old K V) K C, where First = Old K V: either step can wrap,
% and at most one does.
with_carry_pairs(add, Old, _, First, _, Sum, [First-Old, Sum-First]).
with_carry_pairs(sub, Old, V, First, C, _, [Old-V, First-C]).

% carry(+Cf, +Line, -V)//: V is CF as a 64-bit 0 or 1.
carry(none, L, _) --> { throw(error(at(L, unavailable_flag(cf)))) }.
carry(known(V), _, V) --> [].
carry(below([A-B]), L, tmp(T)) --> !,
    { temporary(cf, L, T) },
    [L-let(tmp(T), l, cmp(ult, l), [A, B])].
carry(below([A1-B1, A2-B2]), L, tmp(T)) -->
    { temporary(cf1, L, T1), temporary(cf2, L, T2), temporary(cf, L, T) },
    [L-let(tmp(T1), l, cmp(ult, l), [A1, B1]),
     L-let(tmp(T2), l, cmp(ult, l), [A2, B2]),
     L-let(tmp(T), l, or, [tmp(T1), tmp(T2)])].

source(immediate(N), _, _, V) --> { constant(N, V) }.
source(register(S, W), _, E, V) --> { value(register(S, W), E, V) }.
source(memory(A, Bytes), L, E, tmp(M)) -->
    address(A, L, E, P),
    { temporary(m, L, M), memberchk(Bytes-Width, [8-l, 1-ub]) },
    [L-let(tmp(M), l, load(Width), [P])].

% low(+Width, +Source, +V0, +Line, -V)//: V is V0 for a 64-bit
% operation and its low byte, zero-extended, for a byte one. A byte
% load is already that.
low(64, _, V, _, V) --> [].
low(8, memory(_, _), V, _, V) --> [].
low(8, immediate(N), _, _, const(B)) --> { B is N /\ 255 }.
low(8, register(_, _), V0, L, tmp(B)) -->
    { temporary(b, L, B) },
    [L-let(tmp(B), l, and, [V0, const(255)])].

% The address Base + Index * Scale + Offset.
address(address(Base, Index, Scale, Offset), L, E, P) -->
    { value(Base, E, P0) },
    (   { Index == immediate(0) }
    ->  { P1 = P0 }
    ;   { value(Index, E, I0), temporary(q, L, Q), P1 = tmp(Q) },
        (   { Scale =:= 1 }
        ->  { I = I0 }
        ;   { temporary(i, L, X), I = tmp(X), Shift is msb(Scale) },
            [L-let(tmp(X), l, shl, [I0, const(Shift)])]
        ),
        [L-let(tmp(Q), p, add, [P0, I])]
    ),
    (   { Offset =:= 0 }
    ->  { P = P1 }
    ;   { temporary(a, L, A), P = tmp(A) },
        [L-let(tmp(A), p, add, [P1, const(Offset)])]
    ).

% condition(+C, +Flags0, +Line, -Cond, -Flags)//: Cond is not 0 when
% the condition C holds. Flags are Flags0 with the carry in the
% temporary this made for it, if it made one.
condition(C, fl(zf(W, A, B), Cf), L, tmp(T), fl(zf(W, A, B), Cf)) -->
    { memberchk(C-Rel, [e-eq, ne-ne]), !, temporary(c, L, T) },
    (   { W =:= 64 }
    ->  [L-let(tmp(T), w, cmp(Rel, l), [A, B])]
    ;   { temporary(x, L, X), temporary(z, L, Z) },
        [L-let(tmp(X), l, xor, [A, B]),
         L-let(tmp(Z), l, and, [tmp(X), const(255)]),
         L-let(tmp(T), w, cmp(Rel, l), [tmp(Z), const(0)])]
    ).
condition(C, fl(Z, Cf), L, tmp(T), fl(Z, known(V))) -->
    { memberchk(C-Rel, [b-ne, ae-eq]), !, temporary(c, L, T) },
    carry(Cf, L, V),
    [L-let(tmp(T), w, cmp(Rel, l), [V, const(0)])].
condition(C, _, L, _, _) --> { throw(error(at(L, unsupported_condition(C)))) }.

terminator(exit(L, fallthrough, [Next]), _, F, F, L-goto(Next)) --> !.
terminator(exit(L, semantics(Action, effects(registers(Reads, _), _, Flags, _, _)), Succs), E, F0, F, L-Term) -->
    { maplist(check_read(E, L), Reads),
      check_flag_reads(Flags, F0, L) },
    (   { Action = branch(C, _) }
    ->  condition(C, F0, L, Cond, F),
        { Succs = [Then, Else], Term = branch(Cond, Then, Else) }
    ;   { Action = jump(_) }
    ->  { Succs = [Target], Term = goto(Target), F = F0 }
    ;   { Action = return(R), value(R, E, V), Term = ret(V), F = F0 }
    ).

value(register(R, _), E, V) :- memberchk(R-val(V, _), E).

constant(N, const(M)) :- M is N mod (1 << 64).

temporary(Prefix, Suffix, Name) :- atomic_list_concat([Prefix, '_', Suffix], Name).

%  ## Phis

% with_phis(+Ins, +Blocks, +Block, -Block1): the block with a phi for
% each of its registers, reading each predecessor's final environment.
with_phis(_, Blocks, block(Name, Registers, Insts, Term, _), block(Name, Phis, Insts, Term)) :-
    findall(P-Env,
            ( member(block(P, _, _, _-T, Env), Blocks), successor(T, Name) ),
            Preds),
    maplist({Name, Preds}/[R-Type, phi(tmp(V), Class, Args)]>>(
                temporary(R, Name, V),
                ( Type == pointer -> Class = p ; Class = l ),
                maplist({R}/[P-Env, P-A]>>memberchk(R-val(A, _), Env), Preds, Args)
            ), Registers, Phis).

successor(goto(B), B).
successor(branch(_, B, _), B).
successor(branch(_, _, B), B).

% A phi is dead unless an instruction, a terminator or a live phi reads
% it.
remove_dead_phis(Blocks0, Blocks) :-
    findall(X,
            ( member(block(_, _, Insts, _-Term), Blocks0),
              (   member(_-Inst, Insts), operands(Inst, Args), member(tmp(X), Args)
              ;   sub_term(Sub, Term), nonvar(Sub), Sub = tmp(X)
              ) ),
            Roots0),
    sort(Roots0, Roots),
    live(Blocks0, Roots, Live),
    maplist({Live}/[block(N, Phis0, I, T), block(N, Phis, I, T)]>>
                include({Live}/[phi(tmp(V), _, _)]>>memberchk(V, Live), Phis0, Phis),
            Blocks0, Blocks).

operands(let(_, _, _, Args), Args).
operands(store(_, Value, Pointer), [Value, Pointer]).

live(Blocks, Live0, Live) :-
    findall(X,
            ( member(block(_, Phis, _, _), Blocks),
              member(phi(tmp(V), _, Args), Phis),
              memberchk(V, Live0),
              member(_-tmp(X), Args) ),
            More),
    append(Live0, More, Live1),
    sort(Live1, Live2),
    ( Live2 == Live0 -> Live = Live0 ; live(Blocks, Live2, Live) ).

% A phi whose arguments, itself aside, are one value is that value.
remove_trivial_phis(Blocks0, Blocks) :-
    (   member(block(_, Phis, _, _), Blocks0),
        member(phi(tmp(V), _, Args), Phis),
        pairs_values(Args, Values),
        exclude(==(tmp(V)), Values, Others),
        sort(Others, [Value])
    ->  maplist({V}/[block(N, Ps0, I, T), block(N, Ps, I, T)]>>
                    exclude({V}/[phi(tmp(W), _, _)]>>(W == V), Ps0, Ps),
                Blocks0, Blocks1),
        substitute(tmp(V), Value, Blocks1, Blocks2),
        remove_trivial_phis(Blocks2, Blocks)
    ;   Blocks = Blocks0
    ).

substitute(From, To, T0, T) :-
    (   T0 == From
    ->  T = To
    ;   compound(T0)
    ->  T0 =.. [F|Args0],
        maplist(substitute(From, To), Args0, Args),
        T =.. [F|Args]
    ;   T = T0
    ).

%  ## Printing

%! print_functions(+Functions) is det.
%
%  Prints the Functions of lift_file/2 as an IR file nanofil reads, the
%  source line of each instruction in a comment after it.
print_functions(Functions) :-
    forall(member(func(Name, Linkage, Class, Params, Blocks), Functions),
           ( text(Params, ParamText),
             format("~nfunc(~q, ~q, ~q, ~w, [~n", [Name, Linkage, Class, ParamText]),
             print_list(Blocks, print_block),
             format("]).~n") )).

print_block(block(Name, Phis, Insts, L-Term), End) :-
    format("    block(~q, ", [Name]),
    (   Phis == []
    ->  format("[], ")
    ;   format("[~n"),
        print_list(Phis, [Phi, E]>>( text(Phi, T), format("        ~w~w~n", [T, E]) )),
        format("    ], ")
    ),
    (   Insts == []
    ->  format("[], ")
    ;   format("[~n"),
        print_list(Insts, [Line-Inst, E]>>( text(Inst, T), format("        ~w~w~t~72|% ~d~n", [T, E, Line]) )),
        format("    ], ")
    ),
    text(Term, TermText),
    format("~w)~w~t~72|% ~d~n", [TermText, End, L]).

% print_list(+Items, :Print): call(Print, Item, End) on each item, End
% the comma that follows all but the last.
print_list([], _).
print_list([X], Print) :- !, call(Print, X, "").
print_list([X|Xs], Print) :- call(Print, X, ","), print_list(Xs, Print).

text(Term, Text) :-
    with_output_to(string(Text), write_term(Term, [quoted(true), spacing(next_argument)])).

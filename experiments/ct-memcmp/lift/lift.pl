/** <module> Lifting annotated x86-64 assembly to nanofil IR

    swipl lift.pl FILE.s >FILE.ir

reads the integer subset of x86-64 that memcmp.s uses and prints
nanofil's unchecked IR for each function that has a SaRCAsm signature.
nanofil then inserts the checks, validates the result and emits its own
assembly, so nothing here has to be trusted for memory safety: a wrong
row in the table gives a wrong answer, never an unchecked access.

The lifter is driven by the effect table of table.pl. A row's register
reads and writes say which registers must hold what on entry and what
they hold afterwards, its flags say whether ZF is available to a later
branch or conditional move, its control says where the block ends, and
its action says which IR instruction computes the value.

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
    does not cross a block boundary. Only `e` and `ne` are translated.
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
    maplist(translate_block(Ins), Blocks0, Blocks1),
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

%  ## Translation

% translate_block(+Ins, +Block, -Translated): Translated is
% block(Name, Registers, Instructions, Line-Terminator, Env): the
% registers that get a phi, and the environment at the end. An
% environment pairs a register with val(Operand, Type).
translate_block(Ins, block(Name, Items, Exit), block(Name, Registers, Insts, Term, Env)) :-
    memberchk(Name-Types, Ins),
    ( Name == start -> Suffix = 0, Registers = [] ; Suffix = Name, Registers = Types ),
    maplist({Suffix}/[R-T, R-val(tmp(V), T)]>>temporary(R, Suffix, V), Types, Env0),
    phrase(( items(Items, Env0, none, Env, Zf), terminator(Exit, Env, Zf, Term) ), Insts).

items([], E, Z, E, Z) --> [].
items([L-semantics(Action, effects(registers(Reads, Writes), _, Flags, _, _))|Items], E0, Z0, E, Z) -->
    { maplist(check_read(E0, L), Reads),
      check_flag_reads(Flags, Z0, L) },
    translation(Action, L, E0, Z0, Value, Zf),
    { foldl(write_env(Value), Writes, E0, E1),
      next_zf(Flags, Zf, Z0, L, Z1) },
    items(Items, E1, Z1, E, Z).

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

check_flag_reads(flags(reads(Reads), _, _, _, _), Z, L) :-
    (   Reads == []
    ->  true
    ;   Reads == [zf]
    ->  ( Z == none -> throw(error(at(L, unavailable_flag(zf)))) ; true )
    ;   throw(error(at(L, unsupported_flags(Reads))))
    ).

% next_zf(+Flags, +Zf, +Z0, +Line, -Z): ZF after an instruction whose
% action computes it as Zf, by the row's partition of the flags.
next_zf(flags(_, defined(Defined), _, _, preserved(Preserved)), Zf, Z0, L, Z) :-
    (   memberchk(zf, Defined)
    ->  ( Zf == none -> throw(error(at(L, missing_flag_recipe))) ; Z = Zf )
    ;   memberchk(zf, Preserved)
    ->  Z = Z0
    ;   Z = none
    ).

write_env(Value, Write, E0, E) :-
    written(Write, [R, T]>>memberchk(R-val(_, T), E0), Register, Type),
    exclude([R-_]>>(R == Register), E0, E1),
    ( Type == none -> E = E1 ; E = [Register-val(Value, Type)|E1] ).

% translation(+Action, +Line, +Env, +Zf0, -Value, -Zf)//: the IR
% instructions of Action; Value is what its register write stores and
% Zf is zf(Width, A, B): ZF is set when the low Width bits of A and B
% are equal.
translation(Action, L, E, Z, Value, Zf) --> action(Action, L, E, Z, Value, Zf), !.
translation(Action, L, _, _, _, _) --> { throw(error(at(L, no_translation(Action)))) }.

% A move's Zf is read only for `xor` of a register with itself.
action(move(immediate(N), _), _, _, _, V, zf(64, V, const(0))) -->
    { constant(N, V) }.
action(copy(S, _), _, E, _, V, none) -->
    { value(S, E, V) }.
action(load(A, 8, register(R, 64)), L, E, _, tmp(T), none) -->
    address(A, L, E, P),
    { temporary(R, L, T) },
    [L-let(tmp(T), l, load(l), [P])].
action(load(A, 1, register(R, 8)), L, E, _, tmp(T), none) -->
    address(A, L, E, P),
    { temporary(R, L, T) },
    (   { memberchk(R-val(Old, integer(64)), E) }
    ->  { temporary(m, L, M), temporary(h, L, H), Mask is (1 << 64) - 256 },
        [L-let(tmp(M), l, load(ub), [P]),
         L-let(tmp(H), l, and, [Old, const(Mask)]),
         L-let(tmp(T), l, or, [tmp(H), tmp(M)])]
    ;   [L-let(tmp(T), l, load(ub), [P])]
    ).
action(pointer_offset(address(B, immediate(0), 1, Offset), register(R, 64)), L, E, _, tmp(T), none) -->
    { value(B, E, P), temporary(R, L, T) },
    [L-let(tmp(T), p, add, [P, const(Offset)])].
% A byte `xor` or `or` with a zero-extended source leaves the other 56
% bits as they were, so it is the 64-bit operation.
action(binary(K, S, register(R, W)), L, E, _, tmp(T), zf(W, tmp(T), const(0))) -->
    { ( W =:= 64 -> memberchk(K, [add, and, or, xor]) ; memberchk(K, [or, xor]) ),
      value(register(R, W), E, Old), temporary(R, L, T) },
    source(S, L, E, V0),
    low(W, S, V0, L, V),
    [L-let(tmp(T), l, K, [Old, V])].
action(compare(sub, S, register(R, W)), L, E, _, none, zf(W, Old, V)) -->
    { value(register(R, W), E, Old) },
    source(S, L, E, V).
action(shift(K, Count, register(R, 64)), L, E, _, tmp(T), zf(64, tmp(T), const(0))) -->
    { memberchk(K, [shl, shr]), value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, K, [Old, const(Count)])].
action(unary(dec, register(R, 64)), L, E, _, tmp(T), zf(64, tmp(T), const(0))) -->
    { value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, sub, [Old, const(1)])].
action(unary(neg, register(R, 64)), L, E, _, tmp(T), zf(64, tmp(T), const(0))) -->
    { value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, neg, [Old])].
action(conditional_move(C, S, register(R, 64)), L, E, Z, tmp(T), none) -->
    condition(C, Z, L, Cond),
    { value(S, E, V), value(register(R, 64), E, Old), temporary(R, L, T) },
    [L-let(tmp(T), l, select, [Cond, V, Old])].

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

address(address(Base, immediate(0), 1, Offset), L, E, P) --> !,
    { value(Base, E, P0) },
    (   { Offset =:= 0 }
    ->  { P = P0 }
    ;   { temporary(a, L, A), P = tmp(A) },
        [L-let(tmp(A), p, add, [P0, const(Offset)])]
    ).
address(Address, L, _, _) --> { throw(error(at(L, no_translation(Address)))) }.

condition(C, zf(W, A, B), L, tmp(T)) -->
    { ( memberchk(C-Rel, [e-eq, ne-ne]) -> true ; throw(error(at(L, unsupported_condition(C)))) ),
      temporary(c, L, T) },
    (   { W =:= 64 }
    ->  [L-let(tmp(T), w, cmp(Rel, l), [A, B])]
    ;   { temporary(x, L, X), temporary(z, L, Z) },
        [L-let(tmp(X), l, xor, [A, B]),
         L-let(tmp(Z), l, and, [tmp(X), const(255)]),
         L-let(tmp(T), w, cmp(Rel, l), [tmp(Z), const(0)])]
    ).

terminator(exit(L, fallthrough, [Next]), _, _, L-goto(Next)) --> !.
terminator(exit(L, semantics(Action, effects(registers(Reads, _), _, Flags, _, _)), Succs), E, Z, L-Term) -->
    { maplist(check_read(E, L), Reads),
      check_flag_reads(Flags, Z, L) },
    (   { Action = branch(C, _) }
    ->  condition(C, Z, L, Cond),
        { Succs = [Then, Else], Term = branch(Cond, Then, Else) }
    ;   { Action = jump(_) }
    ->  { Succs = [Target], Term = goto(Target) }
    ;   { Action = return(R), value(R, E, V), Term = ret(V) }
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
              (   member(_-let(_, _, _, Args), Insts), member(tmp(X), Args)
              ;   sub_term(Sub, Term), nonvar(Sub), Sub = tmp(X)
              ) ),
            Roots0),
    sort(Roots0, Roots),
    live(Blocks0, Roots, Live),
    maplist({Live}/[block(N, Phis0, I, T), block(N, Phis, I, T)]>>
                include({Live}/[phi(tmp(V), _, _)]>>memberchk(V, Live), Phis0, Phis),
            Blocks0, Blocks).

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

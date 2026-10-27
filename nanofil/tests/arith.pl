/*  One arithmetic, three readings (docs/arith.md).

    Run through tests/arith.sh, which supplies the work directory:
      ../bin/nanofil --script ../tests/arith.pl DIR slice
      ../bin/nanofil --script ../tests/arith.pl DIR complete
      ../bin/nanofil --script ../tests/arith.pl DIR random SEED COUNT DEPTH

    The generator describes well-typed C integer expressions over the
    twelve integer types: a tree's type comes from c_types' own typing
    relations (binary_operands/6, unary_operand/3,
    usual_arith_conversion/3), so the space is the one the elaborator
    accepts. Each expression is printed as C text once, and that text is
    read three ways:

    | Reading | Is |
    |---|---|
    | `const` | c_types:const_eval/4 on the parsed text: `v(V)`, `ub`, or `not_constant` |
    | `ir` | the interpreter on c_lower's IR of `return E;`, leaves as constants |
    | `ir_params` | the same with every leaf a parameter, so the IR does the conversions |
    | `ice` | clang -std=c11 -pedantic-errors accepts `_Static_assert((E) || 1, "")` |
    | `fold` | clang's value of E as a static initializer (GNU folding, warnings off), or `none` |

    agreement/2 states where the readings must agree and what each
    class of disagreement outside that overlap means. Any expression
    outside every class is a bug, printed with its readings; the run
    then fails. */
:- use_module('../src/c_lex').
:- use_module('../src/c_parse').
:- use_module('../src/c_types').
:- use_module('../src/c_lower').
:- use_module('../src/interp').
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(pio)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).

:- initialization(main).

main :-
    current_prolog_flag(argv, Argv0),
    maplist(arg_atom, Argv0, [Dir|Space]),
    catch(( space_trees(Space, Trees), run_space(Dir, Trees, Bugs) ),
          E, ( format(user_error, "arith.pl: ~W~n", [E, [max_depth(12)]]), halt(2) )),
    ( Bugs =:= 0 -> halt(0) ; halt(1) ).

arg_atom(A, A) :- atom(A), !.
arg_atom(Cs, A) :- atom_chars(A, Cs).

%% The type universe

% spelling(?T, ?Text): the integer type T is spelled Text in C.
spelling(bool, "_Bool").
spelling(char, "char").
spelling(schar, "signed char").
spelling(uchar, "unsigned char").
spelling(short, "short").
spelling(ushort, "unsigned short").
spelling(int, "int").
spelling(uint, "unsigned").
spelling(long, "long").
spelling(ulong, "unsigned long").
spelling(llong, "long long").
spelling(ullong, "unsigned long long").

% type_range(+T, -Min, -Max): T's values, from c_types' integer_type/4.
type_range(bool, 0, 1) :- !.
type_range(T, Min, Max) :-
    integer_type(T, Size, Sign, _),
    Bits is 8 * Size,
    (   Sign == signed
    ->  Min is -(1 << (Bits - 1)), Max is (1 << (Bits - 1)) - 1
    ;   Min = 0, Max is (1 << Bits) - 1
    ).

% boundary(+T, -V): V is a value of T at a boundary: 0, 1, -1, the
% maximum and the minimum, each once.
boundary(T, V) :-
    type_range(T, Min, Max),
    sort([0, 1, -1, Max, Min], Vs),
    member(V, Vs),
    V >= Min, V =< Max.

%% Trees and their types

/*  A tree is one of

    | Tree | C |
    |---|---|
    | `leaf(T, V)` | the value V of type T, written as a cast of a literal |
    | `un(Op, X)` | a unary operator: `neg`, `plus`, `bnot` or `not` |
    | `bin(Op, X, Y)` | a binary operator of c_parse's c_operator/4 |
    | `cond(C, X, Y)` | `C ? X : Y` |
    | `cast(T, X)` | `(T)X` |

    form/4 relates a tree to its type through c_types' relations. */

% form(?Tree, ?Kids, ?KidTypes, -T): Tree, whose subtrees Kids have the
% types KidTypes, has type T. Enumerates the operators when Tree is
% unbound.
form(un(Op, X), [X], [TX], T) :-                         % 6.5.3.3
    member(Op, [neg, plus, bnot, not]),
    unary_operand(Op, TX, T).
form(bin(Op, X, Y), [X, Y], [TX, TY], T) :-
    c_operator(_, _, Op, Kind),
    (   Kind == logical -> T = int                         % 6.5.13p3, 6.5.14p3
    ;   binary_operands(Op, TX, TY, _, _, T)
    ).
form(cond(C, X, Y), [C, X, Y], [_, TX, TY], T) :-        % 6.5.15p5
    usual_arith_conversion(TX, TY, T).
form(cast(T, X), [X], [_], T) :-                         % 6.5.4
    spelling(T, _).

expr_type(leaf(T, _), T).
expr_type(un(Op, X), T) :- expr_type(X, TX), form(un(Op, X), _, [TX], T).
expr_type(bin(Op, X, Y), T) :-
    expr_type(X, TX), expr_type(Y, TY), form(bin(Op, X, Y), _, [TX, TY], T).
expr_type(cond(C, X, Y), T) :-
    expr_type(X, TX), expr_type(Y, TY), form(cond(C, X, Y), _, [_, TX, TY], T).
expr_type(cast(T, _), T).

%% The spaces

% space_trees(+Space, -Trees)
space_trees([slice], Trees) :-
    slice_leaves(Ls),
    findall(Tree, depth1(Ls, [leaf(int, 0), leaf(int, 1)], Tree), Trees0),
    random_trees(1, 400, 3, Trees1),
    append(Trees0, Trees1, Trees).
space_trees([complete], Trees) :-
    findall(L, ( spelling(T, _), boundary(T, V), L = leaf(T, V) ), Ls0),
    findall(leaf(int, C), member(C, [2, 7, 31, 32, 63, 64]), Counts),
    append(Ls0, Counts, Ls),
    findall(Tree, depth1(Ls, [leaf(int, 0), leaf(int, 1)], Tree), Trees).
space_trees([random, Seed0, Count0, Depth0], Trees) :-
    maplist(atom_number, [Seed0, Count0, Depth0], [Seed, Count, Depth]),
    random_trees(Seed, Count, Depth, Trees).

% The Nix check's slice: the values where signedness, width and the
% undefined cases differ, every operator on every pair of them.
slice_leaves([leaf(int, 0), leaf(int, 1), leaf(int, -1), leaf(int, 2147483647),
              leaf(int, -2147483648), leaf(int, 31), leaf(int, 32),
              leaf(uint, 1), leaf(uint, 4294967295), leaf(long, -1),
              leaf(long, 9223372036854775807), leaf(long, -9223372036854775808),
              leaf(ulong, 18446744073709551615), leaf(schar, -128),
              leaf(uchar, 255), leaf(ushort, 65535), leaf(bool, 1),
              leaf(llong, 64)]).

% depth1(+Leaves, +Conds, -Tree): Tree is a leaf, or one operator or
% cast over leaves; a conditional's first operand is one of Conds.
depth1(Ls, _, L) :- member(L, Ls).
depth1(Ls, _, Tree) :-
    Tree = un(_, X), member(X, Ls), expr_type(Tree, _).
depth1(Ls, _, cast(T, X)) :- spelling(T, _), member(X, Ls).
depth1(Ls, _, Tree) :-
    c_operator(_, _, Op, _), Tree = bin(Op, X, Y),
    member(X, Ls), member(Y, Ls), expr_type(Tree, _).
depth1(Ls, Cs, cond(C, X, Y)) :- member(C, Cs), member(X, Ls), member(Y, Ls).

%% Random trees: splitmix64, as tests/gen.pl, so a seed is portable

random_trees(Seed, Count, Depth, Trees) :-
    length(Trees, Count),
    foldl(random_tree(Depth), Trees, Seed, _).

random_tree(Depth, Tree, R0, R) :- tree(Depth, Tree, R0, R).

tree(0, Tree, R0, R) :- !, random_leaf(Tree, R0, R).
tree(D, Tree, R0, R) :-
    D1 is D - 1,
    between_(0, 9, K, R0, R1),
    (   K =:= 0 -> random_leaf(Tree, R1, R)
    ;   K =:= 1 -> unary_ops(Ops), choose(Ops, Op, R1, R2),
                   tree(D1, X, R2, R), Tree = un(Op, X)
    ;   K =:= 2 -> findall(T, spelling(T, _), Ts), choose(Ts, T, R1, R2),
                   tree(D1, X, R2, R), Tree = cast(T, X)
    ;   K =:= 3 -> tree(D1, C, R1, R2), tree(D1, X, R2, R3),
                   tree(D1, Y, R3, R), Tree = cond(C, X, Y)
    ;   findall(Op, c_operator(_, _, Op, _), Ops), choose(Ops, Op, R1, R2),
        tree(D1, X, R2, R3), tree(D1, Y, R3, R), Tree = bin(Op, X, Y)
    ).

unary_ops([neg, plus, bnot, not]).

% A leaf is a boundary value or, a third of the time, a shift count.
random_leaf(leaf(T, V), R0, R) :-
    between_(0, 2, K, R0, R1),
    (   K =:= 0
    ->  choose([0, 1, 2, 7, 15, 16, 31, 32, 33, 63, 64], V, R1, R2),
        choose([int, uint, long, uchar], T, R2, R)
    ;   findall(T0, spelling(T0, _), Ts), choose(Ts, T, R1, R2),
        findall(V0, boundary(T, V0), Vs), choose(Vs, V, R2, R)
    ).

choose(Xs, X, R0, R) :-
    length(Xs, N), Hi is N - 1,
    between_(0, Hi, I, R0, R),
    nth0(I, Xs, X).

between_(Lo, Hi, X, R0, R) :-
    splitmix64(R0, R1, A),
    splitmix64(R1, R, B),
    X is Lo + ((A << 64) \/ B) mod (Hi - Lo + 1).

splitmix64(S0, S, X) :-
    S is (S0 + 0x9E3779B97F4A7C15) mod (1 << 64),
    Z1 is (xor(S, S >> 30) * 0xBF58476D1CE4E5B9) mod (1 << 64),
    Z2 is (xor(Z1, Z1 >> 27) * 0x94D049BB133111EB) mod (1 << 64),
    X is xor(Z2, Z2 >> 31).

%% C text

% text(+Tree, +Leaves)//: Tree in C, fully parenthesized. Leaves is
% `const`, writing each leaf as a cast of a literal, or a list of
% parameter names, one per leaf from left to right (abstracted/3).
text(leaf(T, V), const) --> !, { spelling(T, S) }, "((", seq(S), ")", literal(T, V), ")".
text(p(N), _) --> !, format_("p~d", [N]).
text(un(Op, X), M) --> { un_spelling(Op, S) }, "(", seq(S), text(X, M), ")".
text(bin(Op, X, Y), M) -->
    { c_operator(S, _, Op, _), atom_chars(S, Cs) },
    "(", text(X, M), " ", seq(Cs), " ", text(Y, M), ")".
text(cond(C, X, Y), M) -->
    "(", text(C, M), " ? ", text(X, M), " : ", text(Y, M), ")".
text(cast(T, X), M) --> { spelling(T, S) }, "((", seq(S), ")", text(X, M), ")".

un_spelling(neg, "-").
un_spelling(plus, "+").
un_spelling(bnot, "~").
un_spelling(not, "!").

% literal(+T, +V)//: a literal of value V that converts to T without
% changing it: the minimum of a signed type as -Max-1, and a value too
% large for long long with a u suffix.
literal(T, V) -->
    (   { V < 0, type_range(T, V, Max) } -> format_("(-~d-1)", [Max])
    ;   { V < 0 } -> format_("-~d", [-V])
    ;   { V > 9223372036854775807 } -> format_("~du", [V])
    ;   format_("~d", [V])
    ).

% abstracted(+Tree0, -Tree, -Params): Tree is Tree0 with each leaf
% p(N), and Params the leaves in order.
abstracted(Tree0, Tree, Params) :-
    phrase(abstract(Tree0, Tree), [0-[]], [_-Rev]),
    reverse(Rev, Params).

abstract(leaf(T, V), p(N)), [N1-[leaf(T, V)|Ps]] --> [N-Ps], { N1 is N + 1 }.
abstract(un(Op, X0), un(Op, X)) --> abstract(X0, X).
abstract(cast(T, X0), cast(T, X)) --> abstract(X0, X).
abstract(bin(Op, X0, Y0), bin(Op, X, Y)) --> abstract(X0, X), abstract(Y0, Y).
abstract(cond(C0, X0, Y0), cond(C, X, Y)) -->
    abstract(C0, C), abstract(X0, X), abstract(Y0, Y).

tree_chars(Tree, M, Cs) :- phrase(text(Tree, M), Cs).

%% nanofil's readings

% readings(+Tree, -Item): Item is i(Text, T, Const, IR, IRParams).
readings(Tree, i(Atom, T, Const, IR, IRParams)) :-
    expr_type(Tree, T),
    tree_chars(Tree, const, Text),
    atom_chars(Atom, Text),
    const_reading(Text, T, Const),
    ir_readings(Tree, T, Text, IR, IRParams).

% const_reading(+Text, +T, -Const): const_eval/4 of the parsed Text,
% whose elaborated type must be T, the generator's.
const_reading(Text, T, Const) :-
    c_tokens(Text, arith, Toks),
    c_constant_expression(Toks, E),
    empty_env(Env),
    catch(( c_types:const_eval(E, Env, V, T1)
          ->  ( T1 == T -> true ; throw(type_mismatch(T, T1)) ),
              ( integer(V) -> Const = v(V) ; Const = V )
          ;   Const = not_constant
          ),
          Err, Const = error(Err)).

% ir_readings(+Tree, +T, +Text, -IR, -IRParams): the outcomes of
% `return E;` interpreted, with constant leaves and with parameters.
ir_readings(Tree, T, Text, IR, IRParams) :-
    abstracted(Tree, PTree, Leaves),
    tree_chars(PTree, params, PText),
    return_spelling(T, RT),
    length(Leaves, NP),
    numlist(1, NP, Ns),
    maplist(param_decl, Ns, Leaves, Decls),
    join(Decls, ", ", DeclText),
    phrase(( seq(RT), " g(void) { return ", seq(Text), "; }\n",
             seq(RT), " f(", seq(DeclText), ") { return ", seq(PText), "; }\n" ),
           Unit),
    maplist(leaf_arg, Leaves, Args),
    catch(( c_tokens(Unit, arith, Toks), c_parse(Toks, Items),
            c_module(Items, M),
            run_outcome(M, g, [], T, IR),
            run_outcome(M, f, Args, T, IRParams) ),
          Err, ( IR = error(Err), IRParams = error(Err) )).

param_decl(N0, leaf(T, _), Decl) :-
    N is N0 - 1, spelling(T, S),
    phrase(( seq(S), format_(" p~d", [N]) ), Decl).

join([], _, []).
join([X], _, X) :- !.
join([X|Xs], Sep, Cs) :- join(Xs, Sep, Cs1), append([X, Sep, Cs1], Cs).

% The return converts the value of E to long long, or for a 64-bit
% unsigned type to unsigned long long, which keeps it (6.8.6.4p3).
return_spelling(T, "unsigned long long") :- memberchk(T, [ulong, ullong]), !.
return_spelling(_, "long long").

% leaf_arg(+Leaf, -Arg): the argument bits for a parameter of the leaf's
% type: its value modulo the IR class, as the caller passes it.
leaf_arg(leaf(T, V), A) :-
    integer_type(T, Size, _, _),
    ( Size =:= 8 -> M is 1 << 64 ; M is 1 << 32 ),
    A is V mod M.

run_outcome(M, Fn, Args, T, R) :-
    (   once(run(M, Fn, Args, 1000, O)) -> outcome(O, T, R)
    ;   R = no_outcome
    ).

outcome(ret(B), T, v(V)) :- !,
    (   memberchk(T, [ulong, ullong]) -> V = B
    ;   B >= 1 << 63 -> V is B - (1 << 64)
    ;   V = B
    ).
outcome(O, _, O).

%% clang's readings

% clang_readings(+Dir, +Items, -Clang): Clang has c(Ice, Fold) for each
% item, from two files with one item per line.
clang_readings(Dir, Items, Clang) :-
    ( getenv('FILCC', CC) -> true ; CC = clang ),
    atom_concat(Dir, '/ice.c', IceFile),
    write_lines(IceFile, ice_line, Items),
    format(atom(IceCmd), "~w -std=c11 -pedantic-errors -fsyntax-only -fno-caret-diagnostics -ferror-limit=0 ~w 2>~w.err",
           [CC, IceFile, IceFile]),
    shell(IceCmd, _),
    error_lines(IceFile, NotIce0),
    keyed(NotIce0, NotIce),
    % Folding: the static initializers clang rejects are left out of a
    % second file it compiles, whose data holds the folded values.
    atom_concat(Dir, '/fold.c', FoldFile),
    write_lines(FoldFile, fold_line(all), Items),
    format(atom(FoldCmd0), "~w -std=c11 -w -fsyntax-only -fno-caret-diagnostics -ferror-limit=0 ~w 2>~w.err",
           [CC, FoldFile, FoldFile]),
    shell(FoldCmd0, _),
    error_lines(FoldFile, NoFold0),
    keyed(NoFold0, NoFold),
    atom_concat(Dir, '/fold2.c', Fold2File),
    write_lines(Fold2File, fold_line(except(NoFold)), Items),
    atom_concat(Dir, '/fold2.ll', LL),
    atom_concat(Dir, '/fold2.values', Values),
    format(atom(FoldCmd), "~w -std=c11 -w -S -emit-llvm -o ~w ~w && grep '^@pizlonatedDO_v' ~w >~w",
           [CC, LL, Fold2File, LL, Values]),
    shell(FoldCmd, Status),
    ( Status =:= 0 -> true ; throw(clang_failed(FoldCmd)) ),
    folded_values(Values, Folds0),
    list_to_assoc(Folds0, Folds),
    length(Items, N), N1 is N - 1, numlist(0, N1, Is),
    maplist(clang_item(NotIce, Folds), Is, Items, Clang).

ice_line(_, i(Atom, _, _, _, _)) -->
    { atom_chars(Atom, Text) },
    "_Static_assert((", seq(Text), ") || 1, \"\");".
fold_line(Which, I, i(Atom, T, _, _, _)) -->
    { atom_chars(Atom, Text) },
    (   { Which = except(Ls), L is I + 1, get_assoc(L, Ls, _) } -> []
    ;   { return_spelling(T, RT) },
        seq(RT), format_(" v~d = ", [I]), seq(Text), ";"
    ).

clang_item(NotIce, Folds, I, i(_, T, _, _, _), c(Ice, Fold)) :-
    L is I + 1,
    ( get_assoc(L, NotIce, _) -> Ice = not_ice ; Ice = ice ),
    (   get_assoc(I, Folds, B)
    ->  ( memberchk(T, [ulong, ullong]) -> V is B mod (1 << 64) ; V = B ),
        Fold = v(V)
    ;   Fold = none
    ).

% keyed(+Xs, -Assoc): Assoc has the key X for each of Xs.
keyed(Xs, Assoc) :-
    findall(X-x, member(X, Xs), Ps),
    list_to_assoc(Ps, Assoc).

% write_lines(+File, :Line, +Items): File has the line Line//2 of each
% item and its index, one per line, so line I+1 is item I.
write_lines(File, Line, Items) :-
    open(File, write, S),
    foldl(write_line(S, Line), Items, 0, _),
    close(S).
write_line(S, Line, Item, I, I1) :-
    phrase(call(Line, I, Item), Cs),
    format(S, "~s~n", [Cs]),
    I1 is I + 1.

% error_lines(+File, -Ls): Ls are the lines of File that clang reports
% an error on, in File.err.
error_lines(File, Ls) :-
    atom_concat(File, '.err', Err),
    atom_chars(File, FCs),
    file_lines(Err, Lines),
    findall(L, ( member(Line, Lines), error_line(FCs, L, Line) ), Ls0),
    sort(Ls0, Ls).

error_line(F, L, Line) :-
    append(F, [':'|Rest], Line),
    phrase((digits(Ds), ":", digits(_), ": error:", seq(_)), Rest),
    number_chars(L, Ds).

digits([D|Ds]) --> [D], { member(D, "0123456789") }, digits_(Ds).
digits_([D|Ds]) --> [D], { member(D, "0123456789") }, !, digits_(Ds).
digits_([]) --> [].

file_lines(File, Lines) :-
    phrase_from_file(seq(Cs), File),
    phrase(lines(Lines), Cs).

lines([]) --> [].
lines([L|Ls]) --> line(L), lines(Ls).
line([]) --> "\n", !.
line([C|Cs]) --> [C], line(Cs).

% folded_values(+File, -Folds): Folds are I-V for each global v<I> of
% the LLVM lines in File, whose initializer ends in the value: Fil-C's
% object `{ ptr, ptr, i64 } { ..., i64 V }`.
folded_values(File, Folds) :-
    file_lines(File, Lines),
    findall(I-V, ( member(Line, Lines), folded_line(I, V, Line) ), Folds).

folded_line(I, V, Line) :-
    append("@pizlonatedDO_v", Rest, Line),
    phrase((digits(Ds), " =", seq(_)), Rest),
    append(_, [i, '6', '4', ' '|Vs], Line), append(VCs, [' ', '}'|_], Vs),
    \+ memberchk(' ', VCs), !,
    number_chars(I, Ds), number_chars(V, VCs).

%% Where the readings agree

/*  agreement(+Readings, -Class): r(Ice, Fold, Const, IR, IRParams), one
    expression's readings, belong to Class. No class means a bug.

    | Class | Readings |
    |---|---|
    | `overlap` | clang accepts an ICE: const_eval, the IR and clang's value all agree |
    | `fold_extension` | const_eval folds what clang -pedantic-errors rejects; the value is clang's folded value and the IR's |
    | `rejected(Ir)` | neither clang -pedantic-errors nor const_eval accepts a constant; Ir says how the IR reads it |

    and Ir is `traps` (the IR's division ub), `wraps_as_clang` (the IR's
    value is clang's folded value) or `differs` (it is not, or clang
    does not fold). Both IR readings must always agree. */
agreement(r(_, _, _, IR, IRP), _) :- IR \== IRP, !, fail.
agreement(r(_, _, error(_), _, _), _) :- !, fail.
agreement(r(_, _, _, error(_), _), _) :- !, fail.
agreement(r(ice, Fold, Const, IR, _), overlap) :- !,
    Const = v(V), Fold = v(V), IR = v(V).
agreement(r(not_ice, Fold, v(V), IR, _), fold_extension) :- !,
    Fold = v(V), IR = v(V).
agreement(r(not_ice, Fold, Const, IR, _), rejected(How)) :-
    memberchk(Const, [ub, not_constant]),
    (   IR = ub(_) -> How = traps
    ;   IR = v(V), Fold == v(V) -> How = wraps_as_clang
    ;   How = differs
    ).

%% Running a space

run_space(Dir, Trees, Bugs) :-
    findall(Item, ( member(Tree, Trees), readings(Tree, Item) ), Items),
    clang_readings(Dir, Items, Clang),
    maplist(classified, Items, Clang, Classes),
    msort(Classes, Sorted),
    clumped_(Sorted, Counts),
    length(Items, N),
    format("~d expressions~n", [N]),
    forall(member(C-K, Counts), format("  ~w ~d~n", [C, K])),
    maplist(root, Trees, Roots),
    forall(( member(C-_, Counts), C \== overlap ),
           ( findall(R, ( nth1(K, Classes, C), nth1(K, Roots, R) ), Rs0),
             msort(Rs0, Rs), clumped_(Rs, ByRoot),
             format("  ~w by operator: ~w~n", [C, ByRoot]) )),
    findall(x, member(bug, Classes), Bs), length(Bs, Bugs),
    forall(( nth0(I, Items, Item), nth0(I, Classes, bug) ),
           report(Item, Clang, I)),
    examples(Items, Clang, Classes).

classified(i(_, _, Const, IR, IRP), c(Ice, Fold), Class) :-
    (   agreement(r(Ice, Fold, Const, IR, IRP), Class) -> true
    ;   Class = bug
    ).

report(i(Text, T, Const, IR, IRP), Clang, I) :-
    nth0(I, Clang, c(Ice, Fold)),
    format("DISAGREE ~w : ~w~n  const ~q, ir ~q, ir_params ~q, clang ~w fold ~q~n",
           [Text, T, Const, IR, IRP, Ice, Fold]).

% The first few expressions of each class outside the overlap.
examples(Items, Clang, Classes) :-
    sort(Classes, Cs),
    forall(( member(C, Cs), C \== overlap, C \== bug ),
           ( format("~w, for example:~n", [C]),
             findall(I, nth0(I, Classes, C), Is0),
             length(Is0, K), Take is min(3, K), length(Is, Take),
             append(Is, _, Is0),
             forall(member(I, Is),
                    ( nth0(I, Items, i(Text, _, Const, IR, _)),
                      nth0(I, Clang, c(_, Fold)),
                      format("  ~w  const ~q, ir ~q, fold ~q~n", [Text, Const, IR, Fold]) ))
           )).

% root(+Tree, -Op): the operator at the root of Tree.
root(leaf(_, _), leaf).
root(un(Op, _), Op).
root(bin(Op, _, _), Op).
root(cond(_, _, _), cond).
root(cast(_, _), cast).

clumped_(Sorted, Counts) :-
    foldl(count, Sorted, [], Rev), reverse(Rev, Counts).
count(X, [X-N0|Cs], [X-N|Cs]) :- !, N is N0 + 1.
count(X, Cs, [X-1|Cs]).

/*  A regex compiler that emits nanofil's unchecked IR: an exploration.

    regex_ast/3 parses a PCRE subset into a tree, and regex_func/3 turns
    the tree into one IR function (nanofil/src/ir.pl)

        w NAME(p subject, l length, l start, p ovector, p stack, l slimit)

    that returns 1 with PCRE2's ovector filled in (every group, -1 for an
    unset one), 0 for no match at or after start, or -1 when the
    backtrack stack of slimit longs is too small. nanofil then does what
    it does for C: promotes the slots to SSA, inserts the Fil-C checks
    (pizlonate), removes the redundant ones, and prints x86-64 assembly.
    The compiler is outside the memory-safety argument: a bug here is a
    wrong match or a Fil-C panic, never a wild access.

    ## The subset

    Bytes, not UTF. Literals, `.`, classes with ranges and `\d \w \s`
    (and their negations), `^ $ \b \B`, alternation, capturing and
    `(?:)` groups, `(?=)` and `(?!)`, greedy, lazy and (on one character)
    possessive `* + ? {n} {n,} {n,m}`, and the caseless option. Anything
    else throws unsupported(Why), and the caller keeps PCRE2's
    interpreter for that pattern.

    ## The code it makes

    gen//4 compiles a node to code that falls through when the node
    matches at the slot `pos` and jumps to Fail0 when it cannot. It
    returns Fail1, the label later code jumps to when it fails, which
    makes the node try its next way of matching:

    ```diagram
            ┌──────┐ ok  ┌──────┐ ok  ┌──────┐ ok
    ───────▶│  A   ├────▶│  B   ├────▶│  C   ├────▶ ...
     Fail0 ◀┤      │◀────┤      │◀────┤      │◀──── Fail1 of C
            └──────┘ FA  └──────┘ FB  └──────┘
    ```

    A node's choice state lives in slots (8-byte allocs that promotion
    turns into temporaries): a greedy one-character loop keeps where it
    started and how far it may still give back, an alternation which arm
    matched. Only a loop over a group needs memory that grows: each
    finished iteration pushes its start and its body's slots on the
    backtrack stack, and backing into the loop pops them and resumes the
    body. This is the shape of .NET's compiled regexes, not of sljit's
    PCRE2 JIT, which keeps return addresses on a machine stack.

    The dialect is Trealla's, as nanofil's: run it with either host.
*/
:- module(rx, [regex_ast/3, regex_func/3, rx_file/1]).
:- set_prolog_flag(double_quotes, chars).

:- use_module(library(lists)).
:- use_module(library(dcgs)).

%% Parsing

%! regex_ast(+Chars, +Options, -Regex) is det.
%
%  Regex is re(Ast, Groups) for the pattern Chars: its tree and the
%  number of its capturing groups. Options is a list that may hold
%  `caseless`. Throws unsupported(Why) for syntax outside the subset.
%
%  | Node | Matches |
%  |---|---|
%  | `class(Ranges)` | one byte in the sorted, disjoint `Lo-Hi` Ranges |
%  | `seq(Nodes)` | each in turn |
%  | `alt(Nodes)` | the first that lets the rest match |
%  | `group(N, A)` | A, as capture N |
%  | `star(A, Min, Max, Mode)` | Min to Max (`inf`) of A; Mode `greedy`, `lazy` or `possessive` |
%  | `look(pos, A)`, `look(neg, A)` | here, if A does or does not match |
%  | `bol`, `eol`, `wordb(yes)`, `wordb(no)` | `^`, `$`, `\b`, `\B` |
regex_ast(Chars, Options, re(Ast, Groups)) :-
    ( memberchk(caseless, Options) -> F = fold ; F = exact ),
    (   phrase(alt(F, 1, N, Ast), Chars) -> Groups is N - 1
    ;   throw(unsupported(syntax))
    ).

alt(F, N0, N, A) -->
    seq(F, N0, N1, S), alt_rest(F, N1, N, Ss),
    { Ss == [] -> A = S ; A = alt([S|Ss]) }.

alt_rest(F, N0, N, [S|Ss]) --> "|", !, seq(F, N0, N1, S), alt_rest(F, N1, N, Ss).
alt_rest(_, N, N, []) --> [].

seq(F, N0, N, A) --> items(F, N0, N, Is), { Is = [X] -> A = X ; A = seq(Is) }.

items(F, N0, N, [I|Is]) --> item(F, N0, N1, I), !, items(F, N1, N, Is).
items(_, N, N, []) --> [].

item(F, N0, N, I) --> piece(F, N0, N, A), quant(A, I).

quant(A, star(A, Min, Max, Mode)) --> rep(Min, Max), !, mode(Mode).
quant(A, A) --> [].

rep(0, inf) --> "*".
rep(1, inf) --> "+".
rep(0, 1) --> "?".
rep(Min, Max) -->
    "{", digits(Ds), { Ds \== [], number_chars(Min, Ds) },
    (   "}" -> { Max = Min }
    ;   ",", digits(Es), "}",
        { Es == [] -> Max = inf ; number_chars(Max, Es), Max >= Min }
    ).

mode(lazy) --> "?", !.
mode(possessive) --> "+", !.
mode(greedy) --> [].

digits([D|Ds]) --> [D], { char_type_digit(D) }, !, digits(Ds).
digits([]) --> [].

char_type_digit(D) :- char_code(D, C), C >= 0'0, C =< 0'9.

piece(F, N0, N, A) --> "(", !, group(F, N0, N, A).
piece(_, N, N, bol) --> "^", !.
piece(_, N, N, eol) --> "$", !.
piece(_, N, N, class(Rs)) --> ".", !, { complement([10-10], Rs) }.
piece(F, N, N, class(Rs)) --> "[", !, class_body(F, Rs).
piece(F, N, N, A) --> "\\", !, [C], { escape(F, C, A) }.
piece(F, N, N, A) --> [C], { \+ memberchk(C, "|)*+?") }, { literal(F, C, A) }.

group(F, N0, N, A) --> "?:", !, alt(F, N0, N, A), ")".
group(F, N0, N, look(neg, A)) --> "?!", !, alt(F, N0, N, A), ")".
group(F, N0, N, look(pos, A)) --> "?=", !, alt(F, N0, N, A), ")".
group(_, _, _, _) --> "?", !, { throw(unsupported(group_syntax)) }.
group(F, N0, N, group(N0, A)) --> { N1 is N0 + 1 }, alt(F, N1, N, A), ")".

literal(F, Ch, class(Rs)) :-
    char_code(Ch, C),
    ( C > 127 -> throw(unsupported(non_ascii)) ; true ),
    folded(F, [C-C], Rs).

escape(F, Ch, A) :-
    (   class_escape(Ch, bytes(Rs)) -> A = class(Rs)
    ;   Ch == b -> A = wordb(yes)
    ;   Ch == 'B' -> A = wordb(no)
    ;   control_escape(Ch, C) -> A = class([C-C])
    ;   char_code(Ch, C), alnum(C) -> throw(unsupported(escape(Ch)))
    ;   literal(F, Ch, A)
    ).

control_escape(n, 10).
control_escape(t, 9).
control_escape(r, 13).
control_escape(f, 12).
control_escape(e, 27).
control_escape(a, 7).

alnum(C) :- ( C >= 0'0, C =< 0'9 ; C >= 0'a, C =< 0'z ; C >= 0'A, C =< 0'Z ), !.

class_escape(d, bytes([48-57])).
class_escape(w, bytes([48-57, 65-90, 95-95, 97-122])).
class_escape(s, bytes([9-13, 32-32])).
class_escape('D', bytes(Rs)) :- complement([48-57], Rs).
class_escape('W', bytes(Rs)) :- complement([48-57, 65-90, 95-95, 97-122], Rs).
class_escape('S', bytes(Rs)) :- complement([9-13, 32-32], Rs).

class_body(F, Rs) -->
    ( "^" -> { Neg = true } ; { Neg = false } ),
    class_first(Rs0),
    { normal(Rs0, Rs1), folded(F, Rs1, Rs2),
      ( Neg == true -> complement(Rs2, Rs) ; Rs = Rs2 ) }.

% A `]` straight after the opening is a literal.
class_first([93-93|Rs]) --> "]", !, class_items(Rs).
class_first(Rs) --> class_items(Rs).

class_items([]) --> "]", !.
class_items(Rs) --> class_atom(A), class_after(A, Rs).

class_after(code(Lo), [Lo-Hi|Rs]) -->
    "-", class_atom(code(Hi)), !, { Lo =< Hi }, class_items(Rs).
class_after(code(C), [C-C|Rs]) --> !, class_items(Rs).
class_after(bytes(S), Rs) --> class_items(Rs1), { append(S, Rs1, Rs) }.

class_atom(A) --> "\\", !, [Ch], { class_atom_escape(Ch, A) }.
class_atom(_) --> "[", ":", !, { throw(unsupported(posix_class)) }.
class_atom(code(C)) -->
    [Ch], { Ch \== ']', char_code(Ch, C) },
    { C > 127 -> throw(unsupported(non_ascii)) ; true }.

class_atom_escape(Ch, A) :-
    (   class_escape(Ch, A) -> true
    ;   control_escape(Ch, C) -> A = code(C)
    ;   Ch == b -> A = code(8)
    ;   char_code(Ch, C), alnum(C) -> throw(unsupported(escape(Ch)))
    ;   char_code(Ch, C), A = code(C)
    ).

%% Byte sets: sorted lists of disjoint, non-adjacent Lo-Hi ranges in 0..255.

normal(Rs0, Rs) :- msort(Rs0, Rs1), merged(Rs1, Rs).

merged([], []).
merged([R], [R]) :- !.
merged([A-B, C-D|Rs], Out) :-
    (   C =< B + 1 -> E is max(B, D), merged([A-E|Rs], Out)
    ;   Out = [A-B|Out1], merged([C-D|Rs], Out1)
    ).

complement(Rs, Cs) :- complement(Rs, 0, Cs).

complement([], Lo, Cs) :- ( Lo =< 255 -> Cs = [Lo-255] ; Cs = [] ).
complement([A-B|Rs], Lo, Cs) :-
    ( A > Lo -> A1 is A - 1, Cs = [Lo-A1|Cs1] ; Cs = Cs1 ),
    Lo1 is B + 1,
    complement(Rs, Lo1, Cs1).

set_union(As, Bs, Cs) :- append(As, Bs, Ds), normal(Ds, Cs).

% folded(+F, +Rs0, -Rs): with F fold, Rs also has the other case of each
% ASCII letter of Rs0.
folded(exact, Rs, Rs).
folded(fold, Rs0, Rs) :-
    other_case(Rs0, 97, 122, -32, Us),
    other_case(Rs0, 65, 90, 32, Ls),
    append([Rs0, Us, Ls], Rs1),
    normal(Rs1, Rs).

other_case([], _, _, _, []).
other_case([A-B|Rs], Lo, Hi, D, Out) :-
    L is max(A, Lo), H is min(B, Hi),
    (   L =< H -> L1 is L + D, H1 is H + D, Out = [L1-H1|Out1]
    ;   Out = Out1
    ),
    other_case(Rs, Lo, Hi, D, Out1).

%% What a node can start with

% firsts(+Node, -Rs, -Empty): Rs holds every byte a match of Node can
% start with, and Empty is true if Node can match without consuming one.
firsts(class(Rs), Rs, false).
firsts(bol, [], true).
firsts(eol, [], true).
firsts(wordb(_), [], true).
firsts(look(_, _), [], true).
firsts(group(_, A), Rs, E) :- firsts(A, Rs, E).
firsts(star(A, Min, _, _), Rs, E) :-
    firsts(A, Rs, E0),
    ( Min =:= 0 -> E = true ; E = E0 ).
firsts(seq([]), [], true).
firsts(seq([A|As]), Rs, E) :-
    firsts(A, Rs1, E1),
    (   E1 == true -> firsts(seq(As), Rs2, E), set_union(Rs1, Rs2, Rs)
    ;   Rs = Rs1, E = false
    ).
firsts(alt([A]), Rs, E) :- !, firsts(A, Rs, E).
firsts(alt([A|As]), Rs, E) :-
    firsts(A, Rs1, E1), firsts(alt(As), Rs2, E2),
    set_union(Rs1, Rs2, Rs),
    ( ( E1 == true ; E2 == true ) -> E = true ; E = false ).

% groups_in(+Node, -Ns): the capture numbers inside Node.
groups_in(group(N, A), [N|Ns]) :- !, groups_in(A, Ns).
groups_in(star(A, _, _, _), Ns) :- !, groups_in(A, Ns).
groups_in(look(_, A), Ns) :- !, groups_in(A, Ns).
groups_in(seq(As), Ns) :- !, maplist(groups_in, As, Nss), append(Nss, Ns).
groups_in(alt(As), Ns) :- !, maplist(groups_in, As, Nss), append(Nss, Ns).
groups_in(_, []).

anchored(bol).
anchored(seq([bol|_])).

%% Emission state
%
% s(Counter, Current, Blocks, Slots): Current is the open block
% b(Label, ReversedInsts) or `none`, Blocks the finished ones, newest
% first, and Slots the slot temporaries, newest first. The rules below
% are DCG rules over this state rather than over a list.

fresh(Prefix, Name, s(N0, C, B, L), s(N, C, B, L)) :-
    N is N0 + 1,
    atom_codes(Prefix, Ps), number_codes(N0, Ds), append(Ps, Ds, Cs),
    atom_codes(Name, Cs).

tmp(tmp(T)) --> fresh(t, T).
lab(L) --> fresh(b, L).

slot(tmp(T), S0, S) :-
    fresh(s, T, S0, s(N, C, B, L)),
    S = s(N, C, B, [tmp(T)|L]).

slots(L, S, S) :- S = s(_, _, _, L).

emit(I, s(N, b(Lb, Is), B, L), s(N, b(Lb, [I|Is]), B, L)).

jump(J, s(N, b(Lb, Is), B, L), s(N, none, [block(Lb, [], Insts, J)|B], L)) :-
    reverse(Is, Insts).

begin(Lb, s(N, none, B, L), s(N, b(Lb, []), B, L)).

rd(Slot, V) --> tmp(V), emit(let(V, l, load(l), [Slot])).
wr(Slot, V) --> emit(store(l, V, Slot)).
calc(Op, A, B, V) --> tmp(V), emit(let(V, l, Op, [A, B])).

% cond(Cond, K, A, B, Yes, No): end the block on the comparison.
cond(Cond, K, A, B, Yes, No) -->
    tmp(V), emit(let(V, w, cmp(Cond, K), [A, B])), jump(branch(V, Yes, No)).

% check(Cond, K, A, B, Fail): go on if the comparison holds, else to Fail.
check(Cond, K, A, B, Fail) --> lab(L), cond(Cond, K, A, B, L, Fail), begin(L).

% byte(P, C): C is the subject's byte at offset P, which the caller knows
% is below the length (Fil-C checks it against the capability anyway).
byte(P, C) -->
    tmp(Q), emit(let(Q, p, add, [tmp(subject), P])),
    tmp(C), emit(let(C, w, load(ub), [Q])).

% test1(Rs, P, Yes, No): to Yes if the byte at P is in Rs, to No if it is
% not or P is the end.
test1(Rs, P, Yes, No) -->
    check(ult, l, P, tmp(length), No),
    byte(P, C),
    class_test(Rs, C, Yes, No).

class_test(Rs, C, Yes, No) -->
    { complement(Rs, Cs), length(Rs, N1), length(Cs, N2) },
    ( { N2 < N1 } -> ranges(Cs, C, No, Yes) ; ranges(Rs, C, Yes, No) ).

ranges([], _, _, No) --> jump(goto(No)).
ranges([Lo-Hi], C, Yes, No) --> !, range(Lo, Hi, C, Yes, No).
ranges([Lo-Hi|Rs], C, Yes, No) -->
    lab(Next), range(Lo, Hi, C, Yes, Next), begin(Next), ranges(Rs, C, Yes, No).

range(Lo, Lo, C, Yes, No) --> !, cond(eq, w, C, const(Lo), Yes, No).
range(Lo, Hi, C, Yes, No) -->
    tmp(D), emit(let(D, w, sub, [C, const(Lo)])),
    { W is Hi - Lo },
    cond(ule, w, D, const(W), Yes, No).

% push(Slots, X), pop(Slots, X): the slots' values to and from the
% backtrack stack, whose depth in longs is the slot Sp.
push(Slots, ctx(_, Sp, _)) -->
    { length(Slots, N) },
    rd(Sp, S), calc(add, S, const(N), S1),
    check(ule, l, S1, tmp(slimit), overflow),
    push_each(Slots, S, 0),
    wr(Sp, S1).

push_each([], _, _) --> [].
push_each([Slot|Slots], S, I) -->
    rd(Slot, V), stack_address(S, I, Q), emit(store(l, V, Q)),
    { I1 is I + 1 },
    push_each(Slots, S, I1).

pop(Slots, ctx(_, Sp, _)) -->
    { length(Slots, N) },
    rd(Sp, S), calc(sub, S, const(N), S1), wr(Sp, S1),
    pop_each(Slots, S1, 0).

pop_each([], _, _) --> [].
pop_each([Slot|Slots], S, I) -->
    stack_address(S, I, Q), tmp(V), emit(let(V, l, load(l), [Q])), wr(Slot, V),
    { I1 is I + 1 },
    pop_each(Slots, S, I1).

stack_address(S, I, Q) -->
    calc(add, S, const(I), Ix),
    tmp(Off), emit(let(Off, l, shl, [Ix, const(3)])),
    tmp(Q), emit(let(Q, p, add, [tmp(stack), Off])).

%% Code generation

% gen(Node, X, Fail0, Fail1): see the header. X is ctx(Pos, Sp, Caps):
% the position and stack depth slots and a cap(N, Start, End) of slots
% for each group.
gen(class(Rs), X, F, F) --> !,
    { X = ctx(Pos, _, _) },
    rd(Pos, P), lab(Ok), test1(Rs, P, Ok, F),
    begin(Ok), calc(add, P, const(1), P1), wr(Pos, P1).
gen(seq([]), _, F, F) --> !.
gen(seq([A|As]), X, F, F1) --> !, gen(A, X, F, FA), gen(seq(As), X, FA, F1).
gen(alt(As), X, F, Resume) --> !,
    { X = ctx(Pos, _, _) },
    slot(Save), slot(Which), rd(Pos, P), wr(Save, P),
    lab(Join), lab(Resume),
    arms(As, 1, X, Save, Which, Join, F, Fs),
    begin(Resume), rd(Which, W), dispatch(Fs, W),
    begin(Join).
gen(group(N, A), X, F, Undo) --> !,
    { X = ctx(Pos, _, Caps), memberchk(cap(N, CS, CE), Caps) },
    slot(GS), slot(OS), slot(OE),
    rd(Pos, P), wr(GS, P),
    gen(A, X, F, FA),
    rd(CS, S0), wr(OS, S0), rd(CE, E0), wr(OE, E0),
    rd(GS, G), wr(CS, G), rd(Pos, P1), wr(CE, P1),
    lab(Undo), lab(Next), jump(goto(Next)),
    begin(Undo), rd(OS, S1), wr(CS, S1), rd(OE, E1), wr(CE, E1), jump(goto(FA)),
    begin(Next).
gen(look(Sense, A), X, F, F1) --> !,
    { X = ctx(Pos, Sp, Caps), groups_in(A, Ns) },
    slot(LPos), slot(LSp), rd(Pos, P), wr(LPos, P), rd(Sp, S), wr(LSp, S),
    snapshot(Ns, Caps, Snap),
    look(Sense, A, X, F, F1, LPos, LSp, Snap).
gen(bol, ctx(Pos, _, _), F, F) --> !, rd(Pos, P), check(eq, l, P, const(0), F).
gen(eol, ctx(Pos, _, _), F, F) --> !,
    % The end, or the newline that ends the subject.
    rd(Pos, P), lab(Ok), lab(Inside), lab(Last),
    cond(eq, l, P, tmp(length), Ok, Inside),
    begin(Inside), calc(add, P, const(1), P1), cond(eq, l, P1, tmp(length), Last, F),
    begin(Last), byte(P, C), cond(eq, w, C, const(10), Ok, F),
    begin(Ok).
gen(wordb(Want), ctx(Pos, _, _), F, F) --> !,
    { class_escape(w, bytes(Word)) },
    slot(Before), slot(After), rd(Pos, P),
    wr(Before, const(0)), lab(B1), lab(B2), lab(B3),
    cond(ugt, l, P, const(0), B1, B3),
    begin(B1), calc(sub, P, const(1), P0), byte(P0, C0), class_test(Word, C0, B2, B3),
    begin(B2), wr(Before, const(1)), jump(goto(B3)),
    begin(B3), wr(After, const(0)), lab(A1), lab(A2),
    test1(Word, P, A1, A2),
    begin(A1), wr(After, const(1)), jump(goto(A2)),
    begin(A2), rd(Before, VB), rd(After, VA),
    ( { Want == yes } -> check(ne, l, VB, VA, F) ; check(eq, l, VB, VA, F) ).
gen(star(A, Min, Max, lazy), X, F, F1) --> { Min > 0 }, !,
    % X{m,n}? is X{m} then X{0,n-m}?.
    { ( Max == inf -> Max1 = inf ; Max1 is Max - Min ) },
    gen(seq([star(A, Min, Min, greedy), star(A, 0, Max1, lazy)]), X, F, F1).
gen(star(class(Rs), Min, Max, Mode), X, F, F1) --> { Mode \== lazy }, !,
    { X = ctx(Pos, _, _) },
    slot(Start), rd(Pos, P0), wr(Start, P0),
    lab(Scan), lab(Adv), lab(Done),
    jump(goto(Scan)),
    begin(Scan), rd(Pos, P),
    (   { Max == inf } -> []
    ;   rd(Start, S1), calc(sub, P, S1, N1), check(ult, l, N1, const(Max), Done)
    ),
    test1(Rs, P, Adv, Done),
    begin(Adv), calc(add, P, const(1), P1), wr(Pos, P1), jump(goto(Scan)),
    begin(Done), rd(Pos, P2), rd(Start, S2),
    (   { Min =:= 0 } -> []
    ;   calc(sub, P2, S2, N2), check(uge, l, N2, const(Min), F)
    ),
    (   { Mode == possessive ; Max == Min } -> { F1 = F }
    ;   % Give back one byte at a time, down to Min.
        slot(Cur), wr(Cur, P2), lab(Next), lab(Back), jump(goto(Next)),
        begin(Back), rd(Cur, C), rd(Start, S3), calc(add, S3, const(Min), M),
        check(ugt, l, C, M, F),
        calc(sub, C, const(1), C1), wr(Cur, C1), wr(Pos, C1), jump(goto(Next)),
        begin(Next), { F1 = Back }
    ).
gen(star(class(Rs), 0, Max, lazy), X, F, Back) --> !,
    { X = ctx(Pos, _, _) },
    slot(Start), slot(Cur), rd(Pos, P0), wr(Start, P0), wr(Cur, P0),
    lab(Next), lab(Back), lab(Adv), jump(goto(Next)),
    begin(Back), rd(Cur, C),
    (   { Max == inf } -> []
    ;   rd(Start, S), calc(sub, C, S, N), check(ult, l, N, const(Max), F)
    ),
    test1(Rs, C, Adv, F),
    begin(Adv), calc(add, C, const(1), C1), wr(Cur, C1), wr(Pos, C1), jump(goto(Next)),
    begin(Next).
gen(star(A, Min, Max, Mode), X, F, F1) --> !,
    { firsts(A, _, Empty) },
    (   { Empty == true } -> { throw(unsupported(loop_of_empty_match)) }
    ;   { Mode == possessive } -> { throw(unsupported(possessive_group)) }
    ;   { Mode == lazy } -> lazy_loop(A, Max, X, F, F1)
    ;   greedy_loop(A, Min, Max, X, F, F1)
    ).

arms([A], K, X, _, Which, Join, F, [K-FA]) --> !,
    gen(A, X, F, FA), wr(Which, const(K)), jump(goto(Join)).
arms([A|As], K, X, Save, Which, Join, F, [K-FA|Fs]) -->
    { X = ctx(Pos, _, _) },
    lab(Try), gen(A, X, Try, FA), wr(Which, const(K)), jump(goto(Join)),
    begin(Try), rd(Save, P), wr(Pos, P),
    { K1 is K + 1 },
    arms(As, K1, X, Save, Which, Join, F, Fs).

dispatch([_-FA], _) --> !, jump(goto(FA)).
dispatch([K-FA|Fs], W) --> lab(L), cond(eq, l, W, const(K), FA, L), begin(L), dispatch(Fs, W).

% A lookaround keeps nothing of A but its captures: the position and the
% stack depth go back to what they were. Failing past a positive one
% undoes the captures it set.
look(neg, A, X, F, F, LPos, LSp, Snap) -->
    { X = ctx(Pos, Sp, _) },
    lab(No), gen(A, X, No, _),
    restore_caps(Snap), rd(LSp, S), wr(Sp, S), jump(goto(F)),
    begin(No), rd(LPos, P), wr(Pos, P).
look(pos, A, X, F, F1, LPos, LSp, Snap) -->
    { X = ctx(Pos, Sp, _) },
    gen(A, X, F, _),
    rd(LPos, P), wr(Pos, P), rd(LSp, S), wr(Sp, S),
    (   { Snap == [] } -> { F1 = F }
    ;   lab(Undo), lab(Next), jump(goto(Next)),
        begin(Undo), restore_caps(Snap), jump(goto(F)),
        begin(Next), { F1 = Undo }
    ).

snapshot([], _, []) --> [].
snapshot([N|Ns], Caps, [CS-S1, CE-E1|Snap]) -->
    { memberchk(cap(N, CS, CE), Caps) },
    slot(S1), slot(E1), rd(CS, VS), wr(S1, VS), rd(CE, VE), wr(E1, VE),
    snapshot(Ns, Caps, Snap).

restore_caps([]) --> [].
restore_caps([Slot-Saved|Snap]) --> rd(Saved, V), wr(Slot, V), restore_caps(Snap).

% body(A, X, F, FB, IStart, Saved): the loop body A, and the slots one
% iteration must save to be resumed later: its start, and A's own slots
% if A can be resumed at all.
body(A, X, F, FB, IStart, Saved) -->
    slots(Old), gen(A, X, F, FB), slots(Now),
    { FB == F -> Saved = [IStart] ; append(New, Old, Now), Saved = [IStart|New] }.

/*  A greedy loop over a group. Count iterations are on the stack.

    ```diagram
    Iter:     istart = pos; A        A fails ─▶ IterFail
              push; count++; again
    IterFail: pos = istart           with count iterations ─▶ Next,
                                     or too few ─▶ Back
    Back:     none left ─▶ Fail0
              pop; count--           resume the last iteration ─▶ FB:
                                     it matches another way ─▶ push ...
                                     or cannot ─▶ IterFail, one fewer
    ```
*/
greedy_loop(A, Min, Max, X, F, Back) -->
    { X = ctx(Pos, _, _) },
    slot(Count), slot(IStart), wr(Count, const(0)),
    lab(Iter), lab(IterFail), lab(Back), lab(Next),
    jump(goto(Iter)),
    begin(Iter), rd(Pos, P), wr(IStart, P),
    body(A, X, IterFail, FB, IStart, Saved),
    push(Saved, X), rd(Count, C), calc(add, C, const(1), C1), wr(Count, C1),
    ( { Max == inf } -> jump(goto(Iter)) ; cond(ult, l, C1, const(Max), Iter, Next) ),
    begin(IterFail), rd(IStart, I), wr(Pos, I),
    (   { Min =:= 0 } -> jump(goto(Next))
    ;   rd(Count, C2), cond(uge, l, C2, const(Min), Next, Back)
    ),
    begin(Back), rd(Count, C3), check(ne, l, C3, const(0), F),
    pop(Saved, X), calc(sub, C3, const(1), C4), wr(Count, C4), jump(goto(FB)),
    begin(Next).

/*  A lazy loop over a group, from zero iterations. LPos is where the
    iterations so far end.

    ```diagram
    Back: at Max ─▶ Into
          pos = istart = lpos; A     A fails ─▶ Into
          push; count++; lpos = pos ─▶ Next
    Into: none left ─▶ Fail0
          pop; count--               resume the last iteration ─▶ FB
    ```
*/
lazy_loop(A, Max, X, F, Back) -->
    { X = ctx(Pos, _, _) },
    slot(Count), slot(IStart), slot(LPos),
    wr(Count, const(0)), rd(Pos, P0), wr(LPos, P0),
    lab(Next), lab(Back), lab(Into), jump(goto(Next)),
    begin(Back),
    ( { Max == inf } -> [] ; rd(Count, C0), check(ult, l, C0, const(Max), Into) ),
    rd(LPos, L), wr(Pos, L), wr(IStart, L),
    body(A, X, Into, FB, IStart, Saved),
    push(Saved, X), rd(Count, C), calc(add, C, const(1), C1), wr(Count, C1),
    rd(Pos, P1), wr(LPos, P1), jump(goto(Next)),
    begin(Into), rd(Count, C3), check(ne, l, C3, const(0), F),
    pop(Saved, X), calc(sub, C3, const(1), C4), wr(Count, C4), jump(goto(FB)),
    begin(Next).

%% The function

%! regex_func(+Name, +Regex, -Func) is det.
%
%  Func is the IR function Name that matches Regex, a re(Ast, Groups) of
%  regex_ast/3, with the signature and results the header gives. It
%  tries each start offset in turn, skipping offsets whose byte cannot
%  begin a match (with memchr when only one byte can).
regex_func(Name, re(Ast, Groups), Func) :-
    top(Ast, Groups, s(0, b(init, []), [], []), s(_, none, Blocks0, Slots0)),
    reverse(Blocks0, Blocks1), reverse(Slots0, Slots),
    findall(let(S, p, alloc(8), [const(8)]), member(S, Slots), Allocs),
    reachable([block(entry, [], Allocs, goto(init))|Blocks1], Blocks),
    Func = func(Name, export, w,
                [param(p, tmp(subject)), param(l, tmp(length)), param(l, tmp(start)),
                 param(p, tmp(ovector)), param(p, tmp(stack)), param(l, tmp(slimit))],
                Blocks).

top(Ast, Groups) -->
    slot(Pos), slot(Sp), slot(Scan),
    caps(0, Groups, Caps),
    { X = ctx(Pos, Sp, Caps) },
    wr(Scan, tmp(start)),
    lab(Try), lab(Go), lab(Fail), lab(Stop),
    jump(goto(Try)),
    begin(Try), rd(Scan, S),
    % No match can start at a byte outside First, or at the end.
    (   { firsts(Ast, [B-B], false) }
    ->  % One possible byte: libc finds the next one.
        check(ult, l, S, tmp(length), Stop),
        tmp(Q), emit(let(Q, p, add, [tmp(subject), S])),
        calc(sub, tmp(length), S, Left),
        tmp(R), emit(call(result(R, p), global(memchr), [arg(p, Q), arg(w, const(B)), arg(l, Left)])),
        tmp(RA), emit(let(RA, l, ptoi, [R])),
        check(ne, l, RA, const(0), Stop),
        tmp(QA), emit(let(QA, l, ptoi, [Q])),
        calc(sub, RA, QA, D), calc(add, S, D, S0), wr(Scan, S0),
        jump(goto(Go))
    ;   { firsts(Ast, First, false), First \== [0-255] }
    ->  lab(Skip), check(ult, l, S, tmp(length), Stop),
        byte(S, C), class_test(First, C, Go, Skip),
        begin(Skip), calc(add, S, const(1), S0), wr(Scan, S0), jump(goto(Try))
    ;   jump(goto(Go))
    ),
    begin(Go), rd(Scan, S9), wr(Pos, S9), wr(Sp, const(0)),
    gen(group(0, Ast), X, Fail, _),
    results(Caps), jump(ret(const(1))),
    begin(Fail),
    (   { anchored(Ast) } -> jump(goto(Stop))
    ;   rd(Scan, S1), calc(add, S1, const(1), S2), wr(Scan, S2),
        cond(ule, l, S2, tmp(length), Try, Stop)
    ),
    begin(Stop), jump(ret(const(0))),
    begin(overflow), jump(ret(const(-1))).

caps(N, Groups, []) --> { N > Groups }, !.
caps(N, Groups, [cap(N, CS, CE)|Caps]) -->
    slot(CS), slot(CE), wr(CS, const(-1)), wr(CE, const(-1)),
    { N1 is N + 1 },
    caps(N1, Groups, Caps).

results([]) --> [].
results([cap(N, CS, CE)|Caps]) -->
    { O1 is 16 * N, O2 is O1 + 8 },
    rd(CS, S), tmp(Q1), emit(let(Q1, p, add, [tmp(ovector), const(O1)])), emit(store(l, S, Q1)),
    rd(CE, E), tmp(Q2), emit(let(Q2, p, add, [tmp(ovector), const(O2)])), emit(store(l, E, Q2)),
    results(Caps).

% reachable(+Blocks0, -Blocks): Blocks0 without the blocks no path from
% the first reaches (a Fail1 nothing came back to).
reachable(Blocks0, Blocks) :-
    Blocks0 = [block(Entry, _, _, _)|_],
    reach([Entry], Blocks0, [], Seen),
    include(seen_block(Seen), Blocks0, Blocks).

seen_block(Seen, block(L, _, _, _)) :- memberchk(L, Seen).

reach([], _, Seen, Seen).
reach([L|Ls], Blocks, Seen0, Seen) :-
    (   memberchk(L, Seen0) -> reach(Ls, Blocks, Seen0, Seen)
    ;   memberchk(block(L, _, _, J), Blocks),
        targets(J, Ts), append(Ts, Ls, Ls1),
        reach(Ls1, Blocks, [L|Seen0], Seen)
    ).

targets(goto(L), [L]).
targets(branch(_, L1, L2), [L1, L2]).
targets(ret(_), []).

%% Driver

%! rx_file(+File) is det.
%
%  Prints the IR text of one function per line of File, which is
%  `NAME<tab>OPTIONS<tab>REGEX` with OPTIONS `i` for caseless or `-`.
%  The function is `rx_NAME`. A pattern outside the subset prints a
%  comment instead.
rx_file(File) :-
    open(File, read, S),
    once(rx_lines(S)),
    close(S).

rx_lines(S) :-
    read_line(S, Line),
    (   Line == end -> true
    ;   rx_line(Line), rx_lines(S)
    ).

rx_line(Line) :-
    append(NameCs, ['\t'|Rest], Line), append(OptCs, ['\t'|Regex], Rest), !,
    atom_chars(Name, NameCs),
    ( memberchk(i, OptCs) -> Options = [caseless] ; Options = [] ),
    atom_concat(rx_, Name, Fn),
    catch(( regex_ast(Regex, Options, Re), regex_func(Fn, Re, Func),
            writeq(Func), write('.'), nl ),
          unsupported(Why),
          ( write('% '), write(Name), write(': unsupported: '), writeq(Why), nl )).

read_line(S, Line) :-
    get_char(S, C),
    (   C == end_of_file -> Line = end
    ;   line_rest(C, S, Line)
    ).

line_rest('\n', _, []) :- !.
line_rest(end_of_file, _, []) :- !.
line_rest(C, S, [C|Cs]) :- get_char(S, C1), line_rest(C1, S, Cs).

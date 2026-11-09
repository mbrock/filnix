/*  A regex compiler that emits nanofil's unchecked IR: an exploration.

    It does not read regex syntax. Its input is the bytecode that
    pcre2_compile made of the pattern, so PCRE2 still parses, numbers the
    groups, folds case into classes, expands counted groups, makes
    repeats possessive where that is safe, and finds where a match can
    start. code_regex/4 decodes the bytecode into a tree, and
    regex_func/3 turns the tree into one IR function (nanofil/src/ir.pl)

        w NAME(p subject, l length, l start, p ovector, p stack, l slimit)

    that returns 1 with PCRE2's ovector filled in (every group, -1 for an
    unset one), 0 for no match at or after start, or -1 when the
    backtrack stack of slimit longs is too small. nanofil then does what
    it does for C: promotes the slots to SSA, inserts the Fil-C checks
    (pizlonate), removes the redundant ones, and prints x86-64 assembly.
    The compiler is outside the memory-safety argument: a bug here is a
    wrong match or a Fil-C panic, never a wild access.

    ## What it compiles

    An 8-bit pattern without UTF or UCP, with the LF newline and PCRE2's
    built-in character tables, matched with no match options. The
    opcodes are the ones dump.c names: characters, classes and `\d \w \s`
    with their repeats, `.`, `^ $ \A \z \Z \b \B` in either line mode,
    alternation, capturing, plain and atomic groups and their greedy,
    lazy and possessive repeats, and lookahead and fixed-length
    lookbehind. Any other opcode (a backreference, a Unicode property,
    recursion, a condition, a verb, a callout) throws unsupported(Why),
    and the caller keeps PCRE2's interpreter for that pattern.

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
:- module(rx, [code_regex/4, regex_func/3, rx_file/1]).
:- set_prolog_flag(double_quotes, chars).

:- use_module(library(lists)).
:- use_module(library(dcgs)).

%% Decoding
%
% The bytecode is a list of bytes. An opcode byte is named through Ops,
% the list dump.c prints (nth0 of the byte), so no opcode number appears
% here. Links are two bytes and are skipped: the nesting of brackets,
% alts and kets says the same. Counts and group numbers are two bytes,
% high first.

%! code_regex(+Ops, +Header, +Bytes, -Regex) is det.
%
%  Regex is re(Ast, Groups, Start) for the compiled pattern that dump.c
%  printed as `rx(_, Header, Bytes)` after `ops(Ops)`: its tree, the
%  number of its capturing groups, and where a match can start
%  (`anchored`, `any`, or `set(Ranges)` of the bytes one can begin
%  with). Throws unsupported(Why) for what the header of this file
%  excludes.
%
%  | Node | Matches |
%  |---|---|
%  | `class(Ranges)` | one byte in the sorted, disjoint `Lo-Hi` Ranges |
%  | `seq(Nodes)` | each in turn |
%  | `alt(Nodes)` | the first that lets the rest match |
%  | `group(N, A)` | A, as capture N |
%  | `once(A)` | A's first match, with no way back into it |
%  | `star(A, Min, Max, Mode)` | Min to Max (`inf`) of A; Mode `greedy`, `lazy` or `possessive` |
%  | `look(pos, A)`, `look(neg, A)` | here, if A does or does not match |
%  | `back(N)` | N bytes back, at the start of a lookbehind branch |
%  | `bol`, `eol`, `eod` | `^`, `$`, `\z` |
%  | `mbol`, `meol` | `^` and `$` in multiline mode |
%  | `wordb(yes)`, `wordb(no)` | `\b`, `\B` |
%
%  A loop over anything but one byte has Min 0 or 1 and Max `inf`:
%  pcre2_compile writes the other counts out as copies.
code_regex(Ops, Header, [B|Bytes], re(Ast, Groups, Start)) :-
    memberchk(unsupported(Us), Header),
    ( Us = [U|_] -> throw(unsupported(U)) ; true ),
    memberchk(groups(Groups), Header),
    memberchk(dollar(Dollar), Header),
    memberchk(start(Start0), Header),
    start_set(Start0, Start),
    D = d(Ops, Dollar),
    opcode(D, B, bra(plain)),
    bracket(plain, Bytes, [E|_], D, Ast, single),
    opcode(D, E, end), !.

start_set(anchored, anchored).
start_set(any, any).
start_set(first(B, exact), set([B-B])).
start_set(first(B, caseless), set(Rs)) :- folded([B-B], Rs).
start_set(bitmap(Map), set(Rs)) :- bitmap_set(Map, Rs).

opcode(d(Ops, _), B, Op) :- nth0(B, Ops, Op), !.

% nodes(+Bs0, -Bs, +D, -Nodes): the nodes of a branch, up to the alt or
% ket that Bs begins with.
nodes(Bs0, Bs, D, Ns) :-
    Bs0 = [B|Bs1], opcode(D, B, Op),
    (   ( Op == alt ; Op = ket(_) ) -> Bs = Bs0, Ns = []
    ;   node(Op, Bs1, Bs2, D, N) -> Ns = [N|Ns1], nodes(Bs2, Bs, D, Ns1)
    ;   Op = x(Name) -> throw(unsupported(Name))
    ;   throw(unsupported(Op))
    ).

% node(+Op, +Bs0, -Bs, +D, -Node): the node of opcode Op, whose operands
% Bs0 begins with.
node(char, [C|Bs], Bs, _, class([C-C])).
node(chari, [C|Bs], Bs, _, class(Rs)) :- folded([C-C], Rs).
node(not, [C|Bs], Bs, _, class(Rs)) :- complement([C-C], Rs).
node(noti, [C|Bs], Bs, _, class(Rs)) :- folded([C-C], Rs0), complement(Rs0, Rs).
node(type(T, Sense), Bs, Bs, _, class(Rs)) :- type_set(T, Sense, Rs).
node(rep(Set, Min0, Max0, Mode), Bs0, Bs, D, star(class(Rs), Min, Max, Mode)) :-
    ( Max0 == n -> count(Bs0, Bs1, Max) ; Max = Max0, Bs1 = Bs0 ),
    ( Min0 == n -> Min = Max ; Min = Min0 ),
    Bs1 = [B|Bs],
    (   Set == type -> opcode(D, B, Op), node(Op, [], [], D, class(Rs))
    ;   node(Set, [B], [], D, class(Rs))
    ).
node(class, Bs0, Bs, D, Node) :-
    length(Map, 32), append(Map, Bs1, Bs0),
    bitmap_set(Map, Rs),
    Bs1 = [B|Bs2], opcode(D, B, Op),
    (   Op = crep(Min, Max, Mode) -> Node = star(class(Rs), Min, Max, Mode), Bs = Bs2
    ;   Op = crange(Mode)
    ->  count(Bs2, Bs3, Min), count(Bs3, Bs, Max0),
        ( Max0 =:= 0 -> Max = inf ; Max = Max0 ),
        Node = star(class(Rs), Min, Max, Mode)
    ;   Node = class(Rs), Bs = Bs1
    ).
node(bol, Bs, Bs, _, bol).
node(mbol, Bs, Bs, _, mbol).
node(doll, Bs, Bs, d(_, Dollar), Dollar).
node(eol, Bs, Bs, _, eol).
node(eod, Bs, Bs, _, eod).
node(meol, Bs, Bs, _, meol).
node(wordb(W), Bs, Bs, _, wordb(W)).
node(reverse, Bs0, Bs, _, back(N)) :- count(Bs0, Bs, N).
node(bra(Kind), Bs0, Bs, D, Node) :-
    bracket(Kind, Bs0, Bs, D, A, Ket),
    repeated(none, Ket, A, Node).
node(zero(Zero), [B|Bs0], Bs, D, Node) :-
    opcode(D, B, bra(Kind)),
    bracket(Kind, Bs0, Bs, D, A, Ket),
    repeated(Zero, Ket, A, Node).

count([H, L|Bs], Bs, N) :- N is H * 256 + L.

% bracket(+Kind, +Bs0, -Bs, +D, -Node, -Ket): the group whose opening
% opcode of Kind precedes Bs0, and how its ket repeats it.
bracket(Kind, [_, _|Bs0], Bs, D, Node, Ket) :-
    ( Kind == capture -> count(Bs0, Bs1, N) ; Bs1 = Bs0 ),
    branches(Bs1, Bs, D, As, Ket),
    ( As = [A] -> true ; A = alt(As) ),
    wrapped(Kind, N, A, Node).

branches(Bs0, Bs, D, [A|As], Ket) :-
    nodes(Bs0, [B, _, _|Bs1], D, Ns),
    ( Ns = [A] -> true ; A = seq(Ns) ),
    opcode(D, B, Op),
    (   Op == alt -> branches(Bs1, Bs, D, As, Ket)
    ;   Op = ket(Ket), As = [], Bs = Bs1
    ).

wrapped(plain, _, A, A).
wrapped(capture, N, A, group(N, A)).
wrapped(once, _, A, once(A)).
wrapped(look(Sense), _, A, look(Sense, A)).

% repeated(+Zero, +Ket, +A, -Node): A under the zero-repeat opcode
% before its bracket (or `none`) and the ket after it. An optional
% group is an alternation with nothing.
repeated(none, single, A, A).
repeated(none, greedy, A, star(A, 1, inf, greedy)).
repeated(none, lazy, A, star(A, 1, inf, lazy)).
repeated(none, possessive, A, star(A, 1, inf, possessive)).
repeated(greedy, single, A, alt([A, seq([])])).
repeated(greedy, greedy, A, star(A, 0, inf, greedy)).
repeated(lazy, single, A, alt([seq([]), A])).
repeated(lazy, lazy, A, star(A, 0, inf, lazy)).
repeated(possessive, possessive, A, star(A, 0, inf, possessive)).
repeated(skip, _, _, seq([])).

%% Byte sets: sorted lists of disjoint, non-adjacent Lo-Hi ranges in 0..255.

% The sets of PCRE2's built-in tables, which are the C locale's.
type_bytes(digit, [48-57]).
type_bytes(word, [48-57, 65-90, 95-95, 97-122]).
type_bytes(space, [9-13, 32-32]).
type_bytes(newline, [10-10]).
type_bytes(none, []).

type_set(T, yes, Rs) :- type_bytes(T, Rs).
type_set(T, no, Rs) :- type_bytes(T, Rs0), complement(Rs0, Rs).

% bitmap_set(+Map, -Rs): the set of a 32-byte class bitmap, which has
% bit C mod 8 of byte C // 8 set for each member C.
bitmap_set(Map, Rs) :- bitmap_bytes(Map, 0, Cs), normal(Cs, Rs).

bitmap_bytes([], _, []).
bitmap_bytes([M|Ms], Base, Cs) :-
    byte_bits(0, M, Base, Cs, Cs1),
    Base1 is Base + 8,
    bitmap_bytes(Ms, Base1, Cs1).

byte_bits(8, _, _, Cs, Cs) :- !.
byte_bits(I, M, Base, Cs0, Cs) :-
    ( M /\ (1 << I) =\= 0 -> C is Base + I, Cs0 = [C-C|Cs1] ; Cs0 = Cs1 ),
    I1 is I + 1,
    byte_bits(I1, M, Base, Cs1, Cs).

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

% folded(+Rs0, -Rs): Rs also has the other case of each ASCII letter of
% Rs0.
folded(Rs0, Rs) :-
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

% groups_in(+Node, -Ns): the capture numbers inside Node.
groups_in(group(N, A), [N|Ns]) :- !, groups_in(A, Ns).
groups_in(star(A, _, _, _), Ns) :- !, groups_in(A, Ns).
groups_in(look(_, A), Ns) :- !, groups_in(A, Ns).
groups_in(once(A), Ns) :- !, groups_in(A, Ns).
groups_in(seq(As), Ns) :- !, maplist(groups_in, As, Nss), append(Nss, Ns).
groups_in(alt(As), Ns) :- !, maplist(groups_in, As, Nss), append(Nss, Ns).
groups_in(_, []).

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
gen(once(A), X, F, F1) --> !,
    % What A pushed is dropped, so nothing can resume it.
    { X = ctx(_, Sp, Caps), groups_in(A, Ns) },
    slot(LSp), rd(Sp, S0), wr(LSp, S0),
    snapshot(Ns, Caps, Snap),
    gen(A, X, F, _),
    rd(LSp, S), wr(Sp, S),
    undo_caps(Snap, F, F1).
gen(back(N), ctx(Pos, _, _), F, F) --> !,
    rd(Pos, P), check(uge, l, P, const(N), F), calc(sub, P, const(N), P1), wr(Pos, P1).
gen(bol, ctx(Pos, _, _), F, F) --> !, rd(Pos, P), check(eq, l, P, const(0), F).
gen(mbol, ctx(Pos, _, _), F, F) --> !,
    % The start, or after a newline that does not end the subject.
    rd(Pos, P), lab(Ok), lab(Inside),
    cond(eq, l, P, const(0), Ok, Inside),
    begin(Inside), check(ult, l, P, tmp(length), F),
    calc(sub, P, const(1), P0), byte(P0, C), cond(eq, w, C, const(10), Ok, F),
    begin(Ok).
gen(eod, ctx(Pos, _, _), F, F) --> !, rd(Pos, P), check(eq, l, P, tmp(length), F).
gen(meol, ctx(Pos, _, _), F, F) --> !,
    rd(Pos, P), lab(Ok), lab(Inside),
    cond(eq, l, P, tmp(length), Ok, Inside),
    begin(Inside), byte(P, C), cond(eq, w, C, const(10), Ok, F),
    begin(Ok).
gen(eol, ctx(Pos, _, _), F, F) --> !,
    % The end, or the newline that ends the subject.
    rd(Pos, P), lab(Ok), lab(Inside), lab(Last),
    cond(eq, l, P, tmp(length), Ok, Inside),
    begin(Inside), calc(add, P, const(1), P1), cond(eq, l, P1, tmp(length), Last, F),
    begin(Last), byte(P, C), cond(eq, w, C, const(10), Ok, F),
    begin(Ok).
gen(wordb(Want), ctx(Pos, _, _), F, F) --> !,
    { type_bytes(word, Word) },
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
gen(star(class(Rs), Min, Max, lazy), X, F, F1) --> { Min > 0 }, !,
    % X{m,n}? is X{m} then X{0,n-m}?.
    { ( Max == inf -> Max1 = inf ; Max1 is Max - Min ) },
    gen(seq([star(class(Rs), Min, Min, greedy), star(class(Rs), 0, Max1, lazy)]), X, F, F1).
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
gen(star(A, Min, inf, possessive), X, F, F1) --> !, gen(once(star(A, Min, inf, greedy)), X, F, F1).
gen(star(A, Min, inf, greedy), X, F, F1) --> !, greedy_loop(A, Min, X, F, F1).
gen(star(A, Min, inf, lazy), X, F, F1) --> !, lazy_loop(A, Min, X, F, F1).

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
    undo_caps(Snap, F, F1).

% undo_caps(Snap, F, F1): failing to F1 puts the captures of Snap back
% and goes on to F.
undo_caps([], F, F) --> !.
undo_caps(Snap, F, Undo) -->
    lab(Undo), lab(Next), jump(goto(Next)),
    begin(Undo), restore_caps(Snap), jump(goto(F)),
    begin(Next).

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
    { FB == F -> Saved = [IStart] ; once(append(New, Old, Now)), Saved = [IStart|New] }.

/*  A greedy loop over a group, of at least Min (0 or 1) iterations.
    Count iterations are on the stack. An iteration that matched nothing
    is the last one, as in PCRE2, or the loop would not end.

    ```diagram
    Iter:     istart = pos; A        A fails ─▶ IterFail
              push; count++          it matched nothing ─▶ Next,
                                     or again ─▶ Iter
    IterFail: pos = istart           with count iterations ─▶ Next,
                                     or too few ─▶ Back
    Back:     none left ─▶ Fail0
              pop; count--           resume the last iteration ─▶ FB:
                                     it matches another way ─▶ push ...
                                     or cannot ─▶ IterFail, one fewer
    ```
*/
greedy_loop(A, Min, X, F, Back) -->
    { X = ctx(Pos, _, _) },
    slot(Count), slot(IStart), wr(Count, const(0)),
    lab(Iter), lab(IterFail), lab(Back), lab(Next),
    jump(goto(Iter)),
    begin(Iter), rd(Pos, P), wr(IStart, P),
    body(A, X, IterFail, FB, IStart, Saved),
    push(Saved, X), rd(Count, C), calc(add, C, const(1), C1), wr(Count, C1),
    rd(Pos, P1), rd(IStart, I1), cond(ne, l, P1, I1, Iter, Next),
    begin(IterFail), rd(IStart, I), wr(Pos, I),
    (   { Min =:= 0 } -> jump(goto(Next))
    ;   rd(Count, C2), cond(uge, l, C2, const(Min), Next, Back)
    ),
    begin(Back), rd(Count, C3), check(ne, l, C3, const(0), F),
    pop(Saved, X), calc(sub, C3, const(1), C4), wr(Count, C4), jump(goto(FB)),
    begin(Next).

/*  A lazy loop over a group, of at least Min (0 or 1) iterations. LPos
    is where the iterations so far end, and IStart where the last one
    began: when they are equal it matched nothing, and no further
    iteration follows it.

    ```diagram
    Back: the last one matched nothing ─▶ Into
    Iter: pos = istart = lpos; A     A fails ─▶ Into
          push; count++; lpos = pos ─▶ Next
    Into: none left ─▶ Fail0
          pop; count--               resume the last iteration ─▶ FB
    ```
*/
lazy_loop(A, Min, X, F, Back) -->
    { X = ctx(Pos, _, _) },
    slot(Count), slot(IStart), slot(LPos),
    wr(Count, const(0)), rd(Pos, P0), wr(LPos, P0), wr(IStart, const(-1)),
    lab(Next), lab(Back), lab(Iter), lab(Into),
    ( { Min =:= 0 } -> jump(goto(Next)) ; jump(goto(Iter)) ),
    begin(Back), rd(LPos, L0), rd(IStart, I0), cond(ne, l, L0, I0, Iter, Into),
    begin(Iter), rd(LPos, L), wr(Pos, L), wr(IStart, L),
    body(A, X, Into, FB, IStart, Saved),
    push(Saved, X), rd(Count, C), calc(add, C, const(1), C1), wr(Count, C1),
    rd(Pos, P1), wr(LPos, P1), jump(goto(Next)),
    begin(Into), rd(Count, C3), check(ne, l, C3, const(0), F),
    pop(Saved, X), calc(sub, C3, const(1), C4), wr(Count, C4), jump(goto(FB)),
    begin(Next).

%% The function

%! regex_func(+Name, +Regex, -Func) is det.
%
%  Func is the IR function Name that matches Regex, a re(Ast, Groups,
%  Start) of code_regex/4, with the signature and results the header
%  gives. It tries each start offset in turn, or only the first for an
%  anchored pattern, skipping offsets whose byte cannot begin a match
%  (with memchr when only one byte can).
regex_func(Name, re(Ast, Groups, Start), Func) :-
    top(Ast, Groups, Start, s(0, b(init, []), [], []), s(_, none, Blocks0, Slots0)),
    reverse(Blocks0, Blocks1), reverse(Slots0, Slots),
    findall(let(S, p, alloc(8), [const(8)]), member(S, Slots), Allocs),
    reachable([block(entry, [], Allocs, goto(init))|Blocks1], Blocks),
    Func = func(Name, export, w,
                [param(p, tmp(subject)), param(l, tmp(length)), param(l, tmp(start)),
                 param(p, tmp(ovector)), param(p, tmp(stack)), param(l, tmp(slimit))],
                Blocks).

top(Ast, Groups, Start) -->
    slot(Pos), slot(Sp), slot(Scan),
    caps(0, Groups, Caps),
    { X = ctx(Pos, Sp, Caps) },
    wr(Scan, tmp(start)),
    lab(Try), lab(Go), lab(Fail), lab(Stop),
    jump(goto(Try)),
    begin(Try), rd(Scan, S),
    % No match can start at a byte outside First, or at the end.
    (   { Start = set([B-B]) }
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
    ;   { Start = set(First) }
    ->  lab(Skip), check(ult, l, S, tmp(length), Stop),
        byte(S, C), class_test(First, C, Go, Skip),
        begin(Skip), calc(add, S, const(1), S0), wr(Scan, S0), jump(goto(Try))
    ;   jump(goto(Go))
    ),
    begin(Go), rd(Scan, S9), wr(Pos, S9), wr(Sp, const(0)),
    gen(group(0, Ast), X, Fail, _),
    results(Caps), jump(ret(const(1))),
    begin(Fail),
    (   { Start == anchored } -> jump(goto(Stop))
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
%  Prints the IR text of one function per pattern of File, which holds
%  the terms dump.c prints: `ops(Ops)`, then an `rx(Name, Header,
%  Bytes)` for each pattern. The function is `rx_Name`. A pattern this
%  does not compile prints a comment instead.
rx_file(File) :-
    open(File, read, S),
    read(S, ops(Ops)),
    rx_terms(S, Ops),
    close(S).

rx_terms(S, Ops) :-
    read(S, T),
    (   T == end_of_file -> true
    ;   T = rx(Name, Header, Bytes), rx_term(Ops, Name, Header, Bytes), rx_terms(S, Ops)
    ).

rx_term(Ops, Name, Header, Bytes) :-
    atom_concat(rx_, Name, Fn),
    catch(( code_regex(Ops, Header, Bytes, Re), regex_func(Fn, Re, Func),
            writeq(Func), write('.'), nl ),
          unsupported(Why),
          ( write('% '), write(Name), write(': unsupported: '), writeq(Why), nl )).

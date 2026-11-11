/** <module> The assembly the lifter reads

A reader for the AT&T x86-64 assembly of memcmp.s and of
../ct-bn-add/bn_add.s: labels, SaRCAsm signatures (`#!`), directives,
and instructions whose operands are registers, immediates, memory
references with a base and an optional scaled index, and symbols. It
gives the statement terms of experiments/sarcasm-prolog/parser.pl, so
the prototype's effect table reads its instructions; that parser itself
accepts only `unsigned long(...)` signatures and runs on Trealla.
*/
:- module(lift_asm, [parse_file/2]).
:- use_module(library(lists)).
:- use_module(library(readutil)).

%! parse_file(+Path, -Statements) is det.
%
%  Statements are the statements of the file at Path, each
%  `located(Line, Statement)`:
%
%    | `label(Name)` | `Name:` |
%    | `signature(Result, Args)` | `#! Result(Arg, ...)` after a label; types are atoms |
%    | `directive(Name, Words)` | a line starting with `.Name`; Words are its comma-separated operands as atoms |
%    | `instruction(Mnemonic, Operands)` | Operands are `reg(Name)`, `imm(const(N))`, `mem(const(Disp), Base, Index, const(Scale))` with Index `none` for no index, or `symbol(Name)` |
%
%  Throws `error(syntax(Line, Text))` for a line it cannot read.
parse_file(Path, Statements) :-
    read_file_to_string(Path, Text, []),
    split_string(Text, "\n", "", Lines),
    findall(Located,
            ( nth1(N, Lines, Line),
              line_statements(N, Line, Stmts),
              member(Stmt, Stmts),
              Located = located(N, Stmt) ),
            Statements).

line_statements(N, Line, Stmts) :-
    string_chars(Line, Chars),
    (   phrase(line(Stmts), Chars)
    ->  true
    ;   throw(error(syntax(N, Line)))
    ).

line(Stmts) -->
    blanks, label(Label), blanks, body(Body), blanks, tail(Tail),
    { append([Label, Body, Tail], Stmts) }.

label([label(Name)]) --> identifier(Name), [':'], !.
label([]) --> [].

body([Stmt]) --> identifier(Name), !, blanks,
    (   { atom_chars(Name, ['.'|_]) }
    ->  words(Words), { Stmt = directive(Name, Words) }
    ;   operands(Operands), { Stmt = instruction(Name, Operands) }
    ).
body([]) --> [].

tail([signature(Result, Args)]) --> ['#', '!'], !, blanks,
    type(Result), blanks, ['('], types(Args), [')'], blanks.
tail([]) --> ['#'], !, rest(_).
tail([]) --> [].

types([T|Ts]) --> blanks, type(T), blanks, ( [','] -> types(Ts) ; { Ts = [] } ).
type(T) --> identifier(T).

% A directive's operands are kept as text: the lifter reads only .globl.
words([W|Ws]) --> word(Cs), { Cs \== [], atom_chars(W, Cs) }, !, blanks,
    ( [','] -> blanks, words(Ws) ; { Ws = [] } ).
words([]) --> [].
word([C|Cs]) --> [C], { \+ memberchk(C, [',', '#', ' ', '\t']) }, !, word(Cs).
word([]) --> [].

operands([O|Os]) --> operand(O), !, blanks, ( [','] -> blanks, operands(Os) ; { Os = [] } ).
operands([]) --> [].

operand(reg(R)) --> ['%'], identifier(R).
operand(imm(const(N))) --> ['$'], integer(N).
operand(mem(const(D), Base, Index, const(Scale))) -->
    ( integer(D) -> [] ; { D = 0 } ), ['(', '%'], identifier(Base),
    (   [',', '%']
    ->  identifier(Index), [','], natural(Scale)
    ;   { Index = none, Scale = 1 }
    ),
    [')'].
operand(symbol(S)) --> identifier(S).

integer(N) --> ['-'], !, natural(M), { N is -M }.
integer(N) --> natural(N).
natural(N) --> ['0', X], { memberchk(X, [x, 'X']) }, !, digits(16, Ds), { Ds \== [], value(16, Ds, N) }.
natural(N) --> digits(10, Ds), { Ds \== [], value(10, Ds, N) }.
digits(Base, [D|Ds]) --> [C], { char_type(C, xdigit(D)), D < Base }, !, digits(Base, Ds).
digits(_, []) --> [].
value(Base, Ds, N) :- foldl([D, A0, A]>>(A is A0*Base + D), Ds, 0, N).

identifier(Name) --> [C], { initial(C) }, subsequent(Cs), { atom_chars(Name, [C|Cs]) }.
subsequent([C|Cs]) --> [C], { char_type(C, csym) ; C == '.' }, !, subsequent(Cs).
subsequent([]) --> [].
initial(C) :- char_type(C, csymf) ; C == '.'.

blanks --> [C], { memberchk(C, [' ', '\t', '\r']) }, !, blanks.
blanks --> [].
rest([C|Cs]) --> [C], !, rest(Cs).
rest([]) --> [].

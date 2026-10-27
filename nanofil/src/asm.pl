/*  x86-64 assembly as terms, and their printer as GNU as (AT&T) text.
    The backends build a list of lines; this module is the only place
    that knows AT&T syntax.

    ## Lines

    | Line | Prints as |
    |---|---|
    | `label(S)` | `S:` |
    | `ins(Op, Suffix, Operands)` | Op, then Suffix unless it is `none`, then the operands in AT&T order (sources first) |
    | a directive | the directive, below |

    | Directive | Prints as |
    |---|---|
    | `section(S)` | the section S: `text`, `data`, `rodata`, `bss`, `data_rel_ro` or `note_gnu_stack` |
    | `p2align(N)` `balign(N)` | `.p2align N`, `.balign N` |
    | `globl(S)` `weak(S)` `hidden(S)` | `.globl S`, `.weak S`, `.hidden S` |
    | `type(S, T)` | `.type S, @T`, T `function` or `object` |
    | `size(S)` | `.size S, .-S` |
    | `size(S, N)` | `.size S, N` |
    | `set(S, E)` | `.set S, E` |
    | `quad(E)` | `.quad E` |
    | `long(N)` `int(N)` `short(N)` | `.long N`, `.int N`, `.short N` |
    | `byte(Ns)` | `.byte` and the non-empty list Ns |
    | `zero(N)` | `.zero N` |
    | `ascii(Chars)` | `.ascii` and the characters, escaped |
    | `asciz(Atom)` | `.asciz` and the atom, as it is |

    ## Operands

    Operands name concrete registers, so mixed widths such as
    `movzbl %al, %eax` need no width bookkeeping.

    | Operand | Prints as |
    |---|---|
    | `imm(E)` | `$E` |
    | `reg(R)` | `%R`, for example `reg(eax)`, `reg(cl)`, `reg(r9d)` |
    | `mem(D, B)` | `D(%B)`, D omitted when 0 |
    | `mem(D, B, I)` | `D(%B,%I)`, D omitted when 0 |
    | `rip(E)` | `E(%rip)` |
    | `gotpcrel(S)` | `S@GOTPCREL(%rip)` |
    | `plt(S)` | `S@PLT` |
    | `sym(E)` | `E`, a jump or call target |
    | `ind(O)` | `*O` |

    An expression E is an integer, a symbol atom or `E1+E2`; a left
    operand that is itself a sum is parenthesized.
*/
:- module(asm, [print_asm/1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).

%! print_asm(+Lines) is det.
%
%  Print Lines, a list of asm.pl lines, to the current output as GNU as
%  text. Throws nanofil_error(bad_asm_line(Line)) for a line it cannot
%  print.
print_asm(Lines) :-
    % Line by line: SQLite's 100 MB of text as one code list would not
    % fit the default stack.
    forall(member(Line, Lines),
           ( phrase(line(Line), Cs), format("~s", [Cs]) )).

% The text of one line, committed to its first parse.
line(Line) -->
    {   line_chars(Line, Cs) -> true
    ;   throw(nanofil_error(bad_asm_line(Line)))
    },
    seq(Cs).

line_chars(Line, Cs) :-
    phrase(line_text(Line), Cs).

% line_text(+Line)//: the text of Line. directive//1 has no clause for
% label/1 or ins/3, so the cases are disjoint; line//1 commits to the
% first parse.
line_text(label(S)) -->
    literal(S),
    ":\n".
line_text(ins(Op, Suffix, Operands)) -->
    "\t",
    literal(Op),
    suffix(Suffix),
    operands(Operands),
    "\n".
line_text(Directive) -->
    "\t",
    directive(Directive),
    "\n".

% The cut is for the default case: a suffix is none or any other atom
% (a defaulty term shared with the backends).
suffix(none) --> !.
suffix(S) --> literal(S).

operands([]) --> [].
operands([O|Os]) -->
    " ",
    operand(O),
    more_operands(Os).

more_operands([]) --> [].
more_operands([O|Os]) -->
    ", ",
    operand(O),
    more_operands(Os).

operand(imm(E)) --> "$", expr(E).
operand(reg(R)) --> "%", literal(R).
operand(mem(D, B)) --> disp(D), "(%", literal(B), ")".
operand(mem(D, B, I)) --> disp(D), "(%", literal(B), ",%", literal(I), ")".
operand(rip(E)) --> expr(E), "(%rip)".
operand(gotpcrel(S)) --> literal(S), "@GOTPCREL(%rip)".
operand(plt(S)) --> literal(S), "@PLT".
operand(sym(E)) --> expr(E).
operand(ind(O)) --> "*", operand(O).

% A displacement of 0 is omitted; the cut is for the default case.
disp(0) --> !.
disp(D) --> literal(D).

% A sum whose left operand is itself a sum parenthesizes it. The cut is
% for the default case, an integer or symbol (a defaulty term shared
% with the backends; literal//1 would throw on a sum).
expr(A+B) -->
    !,
    (   { A = _+_ } -> "(", expr(A), ")"
    ;   expr(A)
    ),
    "+",
    expr(B).
expr(E) --> literal(E).

directive(section(S)) --> { section_name(S, Name) }, seq(Name).
directive(p2align(N)) --> ".p2align ", literal(N).
directive(balign(N)) --> ".balign ", literal(N).
directive(globl(S)) --> ".globl ", literal(S).
directive(weak(S)) --> ".weak ", literal(S).
directive(hidden(S)) --> ".hidden ", literal(S).
directive(type(S, T)) --> ".type ", literal(S), ", @", literal(T).
directive(size(S)) --> ".size ", literal(S), ", .-", literal(S).
directive(size(S, N)) --> ".size ", literal(S), ", ", literal(N).
directive(set(S, E)) --> ".set ", literal(S), ", ", expr(E).
directive(quad(E)) --> ".quad ", expr(E).
directive(long(N)) --> ".long ", literal(N).
directive(int(N)) --> ".int ", literal(N).
directive(short(N)) --> ".short ", literal(N).
directive(byte([N|Ns])) --> ".byte ", literal(N), more_bytes(Ns).
directive(zero(N)) --> ".zero ", literal(N).
directive(ascii(Cs)) --> ".ascii \"", ascii_chars(Cs), "\"".
directive(asciz(A)) --> ".asciz \"", literal(A), "\"".

% ascii_chars(+Cs)//: the bytes Cs, one per character, inside an .ascii
% string: printable ASCII as itself except quote and backslash, which
% are escaped, newline and tab as \n and \t, any other byte as three
% octal digits.
ascii_chars([]) --> [].
ascii_chars([C|Cs]) --> ascii_char(C), ascii_chars(Cs).

ascii_char('"') --> !, "\\\"".
ascii_char('\\') --> !, "\\\\".
ascii_char('\n') --> !, "\\n".
ascii_char('\t') --> !, "\\t".
ascii_char(C) --> { char_code(C, N), N >= 32, N =< 126 }, !, [C].
ascii_char(C) -->
    { char_code(C, N),
      maplist(octal_char(N), [6, 3, 0], Os) },
    "\\", seq(Os).

% octal_char(+N, +Shift, -O): O is the octal digit of N at bit Shift.
octal_char(N, Shift, O) :- D is (N >> Shift) /\ 7 + 0'0, char_code(O, D).

more_bytes([]) --> [].
more_bytes([N|Ns]) -->
    ", ",
    literal(N),
    more_bytes(Ns).

% section_name(?Section, ?Name): Name is the directive text of Section.
section_name(text, ".text").
section_name(data, ".data").
section_name(rodata, ".section .rodata").
section_name(bss, ".bss").
section_name(data_rel_ro, ".section .data.rel.ro,\"aw\",@progbits").
section_name(note_gnu_stack, ".section .note.GNU-stack,\"\",@progbits").

% The text of an atom or number.
literal(X) -->
    {   atom(X)
    ->  atom_chars(X, Cs)
    ;   number_chars(X, Cs)
    },
    seq(Cs).

/*  x86-64 assembly terms and their GNU as (AT&T) printer.

    The backends build a list of lines; this module is the only place that
    knows AT&T syntax. A line is

      label(S)                    S:
      ins(Op, Suffix, Operands)   Op, then Suffix unless none, operands in
                                  AT&T order (sources first)
      a directive                 section(text | data | rodata |
                                  data_rel_ro | note_gnu_stack),
                                  p2align(N), balign(N), globl(S),
                                  type(S, function | object), size(S)
                                  (.-S), size(S, N), set(S, E), quad(E),
                                  long(N), int(N), short(N), byte(Ns),
                                  zero(N), ascii(Chars), asciz(Atom)

    Operands name concrete registers, so mixed widths such as
    movzbl %al, %eax need no width bookkeeping:

      imm(E)                      $E
      reg(R)                      %R, e.g. reg(eax), reg(cl), reg(r9d)
      mem(D, B)  mem(D, B, I)     D(%B)  D(%B,%I), D omitted when 0
      rip(E)                      E(%rip)
      gotpcrel(S)                 S@GOTPCREL(%rip)
      plt(S)                      S@PLT
      sym(E)                      E, a jump or call target
      ind(O)                      *O

    An expression E is an integer, a symbol atom or E1+E2; a left operand
    that is itself a sum is parenthesized.
*/
:- module(asm, [print_asm/1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).

print_asm(Lines) :-
    phrase(lines(Lines), Cs),
    format("~s", [Cs]).

lines([]) --> [].
lines([L|Ls]) --> line(L), lines(Ls).

line(L) --> { line_chars(L, Cs) -> true ; throw(nanofil_error(bad_asm_line(L))) }, seq(Cs).

line_chars(L, Cs) :- phrase(line_(L), Cs).

line_(label(S)) --> !, w(S), ":\n".
line_(ins(Op, S, Args)) --> !, "\t", w(Op), suffix(S), operands(Args), "\n".
line_(D) --> "\t", directive(D), "\n".

suffix(none) --> !.
suffix(S) --> w(S).

operands([]) --> [].
operands([A|As]) --> " ", operand(A), more(As).

more([]) --> [].
more([A|As]) --> ", ", operand(A), more(As).

operand(imm(E)) --> "$", expr(E).
operand(reg(R)) --> "%", w(R).
operand(mem(D, B)) --> disp(D), "(%", w(B), ")".
operand(mem(D, B, I)) --> disp(D), "(%", w(B), ",%", w(I), ")".
operand(rip(E)) --> expr(E), "(%rip)".
operand(gotpcrel(S)) --> w(S), "@GOTPCREL(%rip)".
operand(plt(S)) --> w(S), "@PLT".
operand(sym(E)) --> expr(E).
operand(ind(O)) --> "*", operand(O).

disp(0) --> !.
disp(D) --> w(D).

expr(A+B) --> !, ( { A = _+_ } -> "(", expr(A), ")" ; expr(A) ), "+", expr(B).
expr(E) --> w(E).

directive(section(S)) --> { section_name(S, N) }, seq(N).
directive(p2align(N)) --> ".p2align ", w(N).
directive(balign(N)) --> ".balign ", w(N).
directive(globl(S)) --> ".globl ", w(S).
directive(type(S, T)) --> ".type ", w(S), ", @", w(T).
directive(size(S)) --> ".size ", w(S), ", .-", w(S).
directive(size(S, N)) --> ".size ", w(S), ", ", w(N).
directive(set(S, E)) --> ".set ", w(S), ", ", expr(E).
directive(quad(E)) --> ".quad ", expr(E).
directive(long(N)) --> ".long ", w(N).
directive(int(N)) --> ".int ", w(N).
directive(short(N)) --> ".short ", w(N).
directive(byte([N|Ns])) --> ".byte ", w(N), commas(Ns).
directive(zero(N)) --> ".zero ", w(N).
directive(ascii(Cs)) --> ".ascii \"", seq(Cs), "\"".
directive(asciz(A)) --> ".asciz \"", w(A), "\"".

commas([]) --> [].
commas([N|Ns]) --> ", ", w(N), commas(Ns).

section_name(text, ".text").
section_name(data, ".data").
section_name(rodata, ".section .rodata").
section_name(data_rel_ro, ".section .data.rel.ro,\"aw\",@progbits").
section_name(note_gnu_stack, ".section .note.GNU-stack,\"\",@progbits").

w(X) --> { atom(X) -> atom_chars(X, Cs) ; number_chars(X, Cs) }, seq(Cs).

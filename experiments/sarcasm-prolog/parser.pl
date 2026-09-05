:- module(sp_parser, [parse_file/2, parse_chars/2]).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(lists)).

% Locations survive tokenization and every later representation.
parse_file(Path, Statements) :- phrase_from_file(characters(Chars), Path), parse_chars(Chars, Statements).
characters([C|Cs]) --> [C], !, characters(Cs).
characters([]) --> [].
parse_chars(Chars, Statements) :- phrase(tokens(1, Tokens), Chars), phrase(statements(Statements), Tokens).

tokens(_, []) --> [].
tokens(L, Ts) --> [X], { memberchk(X, [' ', '\t', '\r']) }, !, tokens(L, Ts).
tokens(L, [at(L, newline)|Ts]) --> ['\n'], !, { L1 is L+1 }, tokens(L1, Ts).
tokens(L, [at(L, annotation(Text))|Ts]) --> ['#','!'], !, line_text(Text), tokens(L, Ts).
tokens(L, [at(L, annotation(Text))|Ts]) --> [';','!'], !, line_text(Text), tokens(L, Ts).
tokens(L, Ts) --> ['#'], !, line_text(_), tokens(L, Ts).
tokens(L, [at(L, T)|Ts]) --> token(T), !, tokens(L, Ts).
tokens(L, _) --> [X], { throw(error(lexical(L, X))) }.
line_text([X|Xs]) --> [X], { X \= '\n' }, !, line_text(Xs).
line_text([]) --> [].

token(string(S)) --> ['"'], quoted(S).
token(num(N)) --> ['0',X], { memberchk(X,['x','X']) }, hex_digits(Ds), { Ds \= [], digits_value(Ds, 16, N) }.
token(num(N)) --> digits(Ds), { Ds \= [], integer_digits(Ds, N) }.
token(id(A)) --> [C], { initial(C) }, identifier(Cs), { atom_chars(A, [C|Cs]) }.
token(P) --> [P], { memberchk(P, [';',':',',','(',')','%','$','@','+','-','*']) }.
quoted([]) --> ['"'], !.
quoted([C|Cs]) --> ['\\',C], { memberchk(C, ['"','\\']) }, !, quoted(Cs).
quoted([C|Cs]) --> [C], { C \= '"', C \= '\\', C \= '\n' }, quoted(Cs).
identifier([C|Cs]) --> [C], { subsequent(C) }, !, identifier(Cs).
identifier([]) --> [].
initial(C) :- char_code(C,N), (N >= 65, N =< 90; N >= 97, N =< 122; memberchk(C, ['_', '.'])).
subsequent(C) :- initial(C); digit(C,_).
digit(C,N) :- char_code(C,K), K >= 48, K =< 57, N is K-48.
hex_digit(C,N) :- digit(C,N); char_code(C,K), K >= 65, K =< 70, N is K-55; char_code(C,K), K >= 97, K =< 102, N is K-87.
digits([N|Ns]) --> [C], { digit(C,N) }, !, digits(Ns).
digits([]) --> [].
hex_digits([N|Ns]) --> [C], { hex_digit(C,N) }, !, hex_digits(Ns).
hex_digits([]) --> [].
integer_digits([0,D|Ds],N) :- !, maplist(octal_digit,[D|Ds]), digits_value([D|Ds],8,N).
integer_digits(Ds,N) :- digits_value(Ds,10,N).
octal_digit(N) :- N>=0, N=<7.
digits_value(Ds, Base, N) :- digits_value(Ds, Base, 0, N).
digits_value([], _, N, N).
digits_value([D|Ds], B, A, N) :- A1 is A*B+D, digits_value(Ds,B,A1,N).

statements([]) --> [].
statements(Ss) --> [at(_,Sep)], { memberchk(Sep,[newline,';']) }, !, statements(Ss).
statements([located(L,label(Name))|Ss]) --> [at(L,id(Name)),at(_,':')], !, statements(Ss).
statements([located(L,signature(R,Args))|Ss]) --> [at(L,annotation(Text))], !,
    { phrase(tokens(L,Ts), Text), (phrase(signature(R,Args),Ts) -> true; throw(error(signature_syntax(L)))) }, statements(Ss).
statements([located(L,directive('.section',[symbol(Name)|Ops]))|Ss]) -->
    [at(L,id('.section'))], section_name(Name), more_operands(Ops), boundary, !, statements(Ss).
statements([located(L,Stmt)|Ss]) --> [at(L,id(Name))], operands(Ops), boundary, !,
    { (atom_chars(Name,['.'|_]) -> Stmt=directive(Name,Ops); Stmt=instruction(Name,Ops)) }, statements(Ss).
statements(_) --> [at(L,T)], { throw(error(statement_syntax(L,T))) }.
section_name(Name) --> [at(_,id(A))], section_parts(As), { atomic_list_concat([A|As],'-',Name) }.
section_parts([A|As]) --> [at(_,'-'),at(_,id(A))], !, section_parts(As).
section_parts([]) --> [].
boundary, [at(L,T)] --> [at(L,T)], { memberchk(T,[newline,';']); T=annotation(_) }.
boundary([], []).
operands([X|Xs]) --> operand(X), !, more_operands(Xs).
operands([]) --> [].
more_operands([X|Xs]) --> [at(_,',')], !, operand(X), more_operands(Xs).
more_operands([]) --> [].
operand(reg(R)) --> [at(_,'%'),at(_,id(R))].
operand(imm(E)) --> [at(_,'$')], expr(E).
operand(kind(K)) --> [at(_,'@'),at(_,id(K))].
operand(string(S)) --> [at(_,string(S))].
operand(mem(D,B,I,S)) --> displacement(D), [at(_,'('),at(_,'%'),at(_,id(B))], index(I,S), [at(_,')')].
operand(E) --> expr(E).
displacement(E) --> expr(E).
displacement(const(0)) --> [].
index(I,S) --> [at(_,','),at(_,'%'),at(_,id(I)),at(_,',')], expr(S).
index(I,const(1)) --> [at(_,','),at(_,'%'),at(_,id(I))].
index(none,const(1)) --> [].
expr(E) --> product(A), sum_tail(A,E).
sum_tail(A,E) --> [at(_,'+')], product(B), !, sum_tail(add(A,B),E).
sum_tail(A,E) --> [at(_,'-')], product(B), !, sum_tail(sub(A,B),E).
sum_tail(A,A) --> [].
product(E) --> unary(A), product_tail(A,E).
product_tail(A,E) --> [at(_,'*')], unary(B), !, product_tail(mul(A,B),E).
product_tail(A,A) --> [].
unary(neg(E)) --> [at(_,'-')], !, unary(E).
unary(E) --> [at(_,'+')], !, unary(E).
unary(const(N)) --> [at(_,num(N))].
unary(symbol(A)) --> [at(_,id(A))].
unary(E) --> [at(_,'(')], expr(E), [at(_,')')].
signature(u64,Args) --> [at(_,id(unsigned)),at(_,id(long)),at(_,'(')], types(Args), [at(_,')')].
types([T|Ts]) --> type(T), more_types(Ts).
more_types([T|Ts]) --> [at(_,',')], type(T), more_types(Ts).
more_types([]) --> [].
type(ptr) --> [at(_,id(ptr))].
type(u64) --> [at(_,id(unsigned)),at(_,id(long))].

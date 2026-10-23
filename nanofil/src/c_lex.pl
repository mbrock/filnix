/*  C lexer (milestone 4a).

    Input is preprocessed text: `# N "file"` line markers set the location,
    other directive lines (#pragma, #ident) are skipped. Comments are also
    skipped, so hand-written test input works without a preprocessor.

    Tokens are tok(T, File:Line), with T one of

      id(Atom)            identifier
      kw(Atom)            keyword; GNU spellings are folded, so
                          __restrict__ is kw(restrict), __asm__ is kw(asm)
      int(Value, S-R)     suffix S in none, u, l, ul, ll, ull; radix R is
                          dec or other (hex and octal type differently)
      float(Chars)        floating constant, rejected by the lowering
      chr(Value)          character constant, as an int
      str(Bytes)          string literal, bytes without the terminator
      p(Atom)             punctuator, e.g. p('->'), p('<<=')
*/
:- module(c_lex, [c_tokens/3, keyword/2]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(charsio)).

% c_tokens(+Chars, +File, -Tokens)
c_tokens(Cs, File, Ts) :-
    (   phrase(toks(Ts, File:1, bol), Cs) -> true
    ;   throw(nanofil_error('C lexer failed'))
    ).

toks(Ts, L, _) --> ['\n'], !, { next_line(L, L1) }, toks(Ts, L1, bol).
toks(Ts, L, bol) --> ['#'], !, directive(L, L1), toks(Ts, L1, bol).
toks(Ts, L, B) --> [C], { blank(C) }, !, toks(Ts, L, B).
toks(Ts, L, B) --> ['/', '*'], !, block_comment(L, L1), toks(Ts, L1, B).
toks(Ts, L, _) --> ['/', '/'], !, skip_line, toks(Ts, L, mid).
toks([tok(T, L)|Ts], L, _) --> token(T, L), !, toks(Ts, L, mid).
toks([], _, _) --> [].
toks(_, L, _) --> [C], { loc_error(L, 'unexpected character ~q', [C]) }.

next_line(F:N, F:N1) :- N1 is N + 1.

blank(' '). blank('\t'). blank('\r'). blank('\f'). blank('\v').

skip_line, ['\n'] --> ['\n'], !.
skip_line --> [_], !, skip_line.
skip_line --> [].

block_comment(L, L) --> ['*', '/'], !.
block_comment(L0, L) --> ['\n'], !, { next_line(L0, L1) }, block_comment(L1, L).
block_comment(L0, L) --> [_], !, block_comment(L0, L).
block_comment(L, _) --> { loc_error(L, 'unterminated comment', []) }.

% A line marker `# N "file" flags` or `#line N "file"` says the next line
% is line N of file. Any other directive is skipped.
directive(L0, L) -->
    spaces, ( "line" -> spaces ; [] ),
    (   digits1(Ds), spaces, { number_chars(N, Ds), N0 is N - 1 }
    ->  (   ['"'] -> marker_file(Fs), { atom_chars(F, Fs) }
        ;   { L0 = F:_ }
        ),
        { L = F:N0 }
    ;   { L = L0 }
    ),
    skip_line.

marker_file([]) --> ['"'], !.
marker_file([C|Cs]) --> [C], marker_file(Cs).

spaces --> [C], { blank(C) }, !, spaces.
spaces --> [].

digits1([D|Ds]) --> [D], { decimal(D) }, digits0(Ds).
digits0([D|Ds]) --> [D], { decimal(D) }, !, digits0(Ds).
digits0([]) --> [].

decimal(D) :- char_type(D, decimal_digit).

%% Tokens

token(T, _) --> [C], { ident_start(C) }, !, ident_rest(Cs),
    { atom_chars(A, [C|Cs]), ( keyword(A, K) -> T = kw(K) ; T = id(A) ) }.
token(T, L) --> [C], { decimal(C) }, !, number([C], T, L).
token(T, L) --> ['.', D], { decimal(D) }, !, number(['.', D], T, L).
token(chr(V), L) --> ['\''], !, char_body(L, Bs), { char_value(Bs, V, L) }.
token(str(Bs), L) --> ['"'], !, str_body(L, Bs).
token(p(P), _) --> punct(P).

ident_start(C) :- char_type(C, alpha), !.
ident_start('_').
ident_start('$').

ident_rest([C|Cs]) --> [C], { ident_char(C) }, !, ident_rest(Cs).
ident_rest([]) --> [].

ident_char(C) :- char_type(C, alnum), !.
ident_char('_').
ident_char('$').

% A pp-number, then classified: integer with suffix or floating.
number(Cs0, T, L) --> pp_rest(Cs1), { append(Cs0, Cs1, Cs), classify(Cs, T, L) }.

pp_rest([E, S|Cs]) --> [E, S], { memberchk(E, [e, 'E', p, 'P']), memberchk(S, ['+', '-']) }, !, pp_rest(Cs).
pp_rest([C|Cs]) --> [C], { ident_char(C) ; C == '.' }, !, pp_rest(Cs).
pp_rest([]) --> [].

classify(Cs, T, L) :-
    (   phrase(int_body(V, Sfx), Cs) -> T = int(V, Sfx)
    ;   phrase(float_ok, Cs) -> T = float(Cs)
    ;   atom_chars(A, Cs), loc_error(L, 'bad number ~w', [A])
    ).

int_body(V, S-R) -->
    (   ['0', X], { memberchk(X, [x, 'X']) } -> hex_digits(Ds), { Ds \== [], base_value(Ds, 16, V), R = other }
    ;   ['0'] -> oct_digits(Ds), { base_value(Ds, 8, V), R = other }
    ;   dec_digits(Ds), { Ds \== [], base_value(Ds, 10, V), R = dec }
    ),
    int_suffix(S).

hex_digits([D|Ds]) --> [D], { weight(D, _) }, !, hex_digits(Ds).
hex_digits([]) --> [].
oct_digits([D|Ds]) --> [D], { char_type(D, decimal_digit), D @< '8' }, !, oct_digits(Ds).
oct_digits([]) --> [].
dec_digits([D|Ds]) --> [D], { decimal(D) }, !, dec_digits(Ds).
dec_digits([]) --> [].

base_value(Ds, B, V) :- foldl(digit_acc(B), Ds, 0, V).
digit_acc(B, D, V0, V) :- weight(D, W), V is V0 * B + W.

weight(D, W) :- sub_atom('0123456789abcdef', W, 1, _, D), !.
weight(D, W) :- sub_atom('ABCDEF', W0, 1, _, D), W is W0 + 10.

int_suffix(S) --> suffix_chars(Cs), { maplist(lower, Cs, Ls), atom_chars(A, Ls), suffix_norm(A, S) }.
suffix_chars([C|Cs]) --> [C], !, suffix_chars(Cs).
suffix_chars([]) --> [].

lower(C, L) :- ( sub_atom('ULX', I, 1, _, C) -> sub_atom(ulx, I, 1, _, L) ; L = C ).

suffix_norm('', none). suffix_norm(u, u). suffix_norm(l, l). suffix_norm(ll, ll).
suffix_norm(ul, ul). suffix_norm(lu, ul). suffix_norm(ull, ull). suffix_norm(llu, ull).

float_ok --> float_chars.
float_chars --> [C], { decimal(C) ; memberchk(C, ['.', e, 'E', '+', '-', f, 'F', l, 'L', x, 'X', p, 'P'])
                       ; weight(C, _) }, !, float_chars.
float_chars --> [].

%% Character and string bodies: lists of byte values.

char_body(L, []) --> ['\''], !, { loc_error(L, 'empty character constant', []) }.
char_body(L, Bs) --> lit_chars('\'', L, Bs).

str_body(L, Bs) --> lit_chars('"', L, Bs).

lit_chars(Q, _, []) --> [Q], !.
lit_chars(_, L, _) --> ['\n'], !, { loc_error(L, 'unterminated literal', []) }.
lit_chars(Q, L, Bs) --> ['\\'], !, escape(L, B), lit_chars(Q, L, Bs0), { Bs = [B|Bs0] }.
lit_chars(Q, L, Bs) --> [C], !, { char_code(C, K), utf8(K, Us) }, lit_chars(Q, L, Bs0), { append(Us, Bs0, Bs) }.
lit_chars(_, L, _) --> { loc_error(L, 'unterminated literal', []) }.

escape(_, B) --> [C], { simple_escape(C, B) }, !.
escape(_, B) --> ['x'], !, hex_digits(Ds), { Ds \== [], base_value(Ds, 16, V), B is V /\ 255 }.
escape(_, B) --> [D], { char_type(D, decimal_digit), D @< '8' }, !, oct_upto(2, Ds), { base_value([D|Ds], 8, V), B is V /\ 255 }.
escape(L, _) --> [C], { loc_error(L, 'unknown escape \\~w', [C]) }.

oct_upto(0, []) --> !.
oct_upto(N, [D|Ds]) --> [D], { char_type(D, decimal_digit), D @< '8' }, !, { N1 is N - 1 }, oct_upto(N1, Ds).
oct_upto(_, []) --> [].

simple_escape(n, 10). simple_escape(t, 9). simple_escape(r, 13). simple_escape(a, 7).
simple_escape(b, 8). simple_escape(f, 12). simple_escape(v, 11). simple_escape('\\', 92).
simple_escape('\'', 39). simple_escape('"', 34). simple_escape('?', 63). simple_escape(e, 27).

% A multi-character constant is rejected; one byte is the value, as a
% (signed) char promoted to int.
char_value([B], V, _) :- !, ( B >= 128 -> V is B - 256 ; V = B ).
char_value(_, _, L) :- loc_error(L, 'multi-character constant', []).

utf8(K, [K]) :- K < 128, !.
utf8(K, [B1, B2]) :- K < 2048, !, B1 is 192 \/ (K >> 6), B2 is 128 \/ (K /\ 63).
utf8(K, [B1, B2, B3]) :- K < 65536, !,
    B1 is 224 \/ (K >> 12), B2 is 128 \/ ((K >> 6) /\ 63), B3 is 128 \/ (K /\ 63).
utf8(K, [B1, B2, B3, B4]) :-
    B1 is 240 \/ (K >> 18), B2 is 128 \/ ((K >> 12) /\ 63),
    B3 is 128 \/ ((K >> 6) /\ 63), B4 is 128 \/ (K /\ 63).

%% Punctuators, longest first.

punct(P) --> [A, B, C], { atom_chars(P, [A, B, C]), memberchk(P, ['...', '<<=', '>>=']) }, !.
punct(P) --> [A, B], { atom_chars(P, [A, B]), memberchk(P, ['->', '++', '--', '<<', '>>', '<=', '>=', '==', '!=',
                                                      '&&', '||', '*=', '/=', '%=', '+=', '-=', '&=',
                                                      '^=', '|=', '##']) }, !.
punct(P) --> [C], { memberchk(C, ['[', ']', '(', ')', '{', '}', '.', '&', '*', '+', '-', '~', '!',
                                  '/', '%', '<', '>', '^', '|', '?', ':', ';', '=', ',', '#']),
                    atom_chars(P, [C]) }.

%% Keywords, with GNU alternate spellings folded.

keyword(A, K) :- kw(A, K).

kw(auto, auto). kw(break, break). kw(case, case). kw(char, char).
kw(const, const). kw(continue, continue). kw(default, default). kw(do, do).
kw(double, double). kw(else, else). kw(enum, enum). kw(extern, extern).
kw(float, float). kw(for, for). kw(goto, goto). kw(if, if). kw(inline, inline).
kw(int, int). kw(long, long). kw(register, register). kw(restrict, restrict).
kw(return, return). kw(short, short). kw(signed, signed). kw(sizeof, sizeof).
kw(static, static). kw(struct, struct). kw(switch, switch). kw(typedef, typedef).
kw(union, union). kw(unsigned, unsigned). kw(void, void). kw(volatile, volatile).
kw(while, while).
kw('_Alignas', alignas). kw('_Alignof', alignof). kw('_Atomic', atomic).
kw('_Bool', bool). kw('_Complex', complex). kw('_Generic', generic).
kw('_Imaginary', imaginary). kw('_Noreturn', noreturn).
kw('_Static_assert', static_assert). kw('_Thread_local', thread_local).
kw('__restrict', restrict). kw('__restrict__', restrict).
kw('__inline', inline). kw('__inline__', inline).
kw('__const', const). kw('__const__', const).
kw('__volatile', volatile). kw('__volatile__', volatile).
kw('__signed', signed). kw('__signed__', signed).
kw(asm, asm). kw('__asm', asm). kw('__asm__', asm).
kw('__attribute', attribute). kw('__attribute__', attribute).
kw('__extension__', extension).
kw('__typeof', typeof). kw('__typeof__', typeof). kw(typeof, typeof).
kw('__alignof', alignof). kw('__alignof__', alignof).
kw('__int128', int128). kw('__thread', thread_local).

loc_error(F:N, Fmt, Args) :-
    format(atom(M0), Fmt, Args),
    format(atom(M), '~w:~w: ~w', [F, N, M0]),
    throw(nanofil_error(M)).

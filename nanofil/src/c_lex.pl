/*  The C lexer (milestone 4a): it turns preprocessed C text into a list
    of tokens, each with its file and line.

    ## Input

    The input is preprocessed text. A line marker `# N "file"` or
    `#line N "file"` sets the location of the next line, and
    `#pragma weak` and `#pragma pack` are tokens; any other directive line, such as
    another `#pragma` or `#ident`, is skipped. Comments
    are skipped too, so hand-written test input works without a
    preprocessor.

    ## Tokens

    A token is `tok(T, File:Line)`, with T one of:

    | T | Is |
    |---|---|
    | `id(Atom)` | an identifier |
    | `kw(Atom)` | a keyword; GNU spellings are folded, so `__restrict__` is `kw(restrict)` and `__asm__` is `kw(asm)` |
    | `int(Value, Suffix-Radix)` | an integer constant: Suffix is `none`, `u`, `l`, `ul`, `ll` or `ull`; Radix is `dec`, or `other` for hex and octal, which type differently |
    | `float(Chars)` | a floating constant, its characters as written |
    | `chr(Value)` | a character constant, as an int |
    | `str(Bytes)` | a string literal, its bytes without the terminator (`u8"..."` too, as UTF-8 bytes) |
    | `wstr(Type, Codes)` | `L"..."`, `u"..."` or `U"..."`: Type is the element type, `int` (wchar_t), `ushort` (char16_t) or `uint` (char32_t), and Codes the elements without the 0 |
    | `p(Atom)` | a punctuator, such as `p('->')` or `p('<<=')` |
    | `pragma_weak(Name, Target)` | `#pragma weak Name`, Target `none`, or `#pragma weak Name = Target` |

    A `#pragma pack` line is consumed by pack_tokens/2, which c_tokens/3
    and c_pp apply to a whole token list: each `struct` or `union`
    keyword under `#pragma pack(N)` is followed by the attribute
    `__attribute__((__nanofil_pack__(N)))`, which c_types' su_layout/5
    honors. GCC and clang apply the pragma to the definitions after it.
*/
:- module(c_lex, [c_tokens/3, i_file_tokens/2, c23_tokens/2, keyword/2, decimal/1, ident_start/1,
                  ident_char/1, ident_rest//1, punctuator/1, digraph/1,
                  pack_op/2, pack_tokens/2]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(charsio)).
:- use_module(library(readutil)).

%! c_tokens(+Chars, +File, -Tokens) is det.
%
%  Tokens are the tok(T, File:Line) terms of the C text Chars, read as
%  file File from line 1. Throws nanofil_error/1 on a lexical error.
c_tokens(Cs, File, Tokens) :-
    (   phrase(tokens(Tokens0, File:1, bol), Cs)
    ->  pack_tokens(Tokens0, Tokens)
    ;   throw(nanofil_error('C lexer failed'))
    ).

%! i_file_tokens(+File, -Tokens) is det.
%
%  Tokens are c_tokens/3's tokens of the preprocessed (.i) File, lexed
%  a line at a time, so that a line's characters are garbage once it is
%  lexed: the characters of a whole file, 24 bytes each, would sit
%  beside its tokens (a 31 MB tree-sitter parser's are 750 MB). A line
%  marker sets the next line's location, as in c_tokens/3; a block
%  comment that spans lines, which `cc -E` never leaves, is lexed with
%  the lines up to its end.
i_file_tokens(File, Tokens) :-
    setup_call_cleanup(open(File, read, S, [encoding(octet)]),
                       i_lines(S, File:1, Tokens0, []),
                       close(S)),
    pack_tokens(Tokens0, Tokens).

i_lines(S, Loc, Ts0, Ts) :-
    line_chars(S, Cs),
    (   Cs == []
    ->  Ts0 = Ts
    ;   i_line(S, Cs, Loc, Loc1, Ts0, Ts1),
        i_lines(S, Loc1, Ts1, Ts)
    ).

% i_line(+S, +Cs, +Loc, -Loc1, -Ts0, ?Ts): Ts0-Ts are the tokens of
% line Cs at Loc (with the lines after it while a comment is open);
% Loc1 is the location after them.
i_line(S, Cs, Loc, Loc1, Ts0, Ts) :-
    catch(( once(phrase(tokens(LTs, Loc, bol, Loc1), Cs)), Open = no ),
          nanofil_error(M),
          (   sub_atom(M, _, _, _, 'unterminated comment')
          ->  Open = M
          ;   throw(nanofil_error(M))
          )),
    (   Open == no
    ->  append(LTs, Ts, Ts0)
    ;   line_chars(S, More),
        (   More == []
        ->  throw(nanofil_error(Open))
        ;   append(Cs, More, Cs1),
            i_line(S, Cs1, Loc, Loc1, Ts0, Ts)
        )
    ).

% line_chars(+S, -Cs): Cs are the characters of S's next line, with its
% newline; [] at the end of the file.
line_chars(S, Cs) :-
    read_line_to_codes(S, Codes, []),
    string_codes(Str, Codes),
    string_chars(Str, Cs).

%! pack_tokens(+Tokens0, -Tokens) is det.
%
%  Tokens are Tokens0 without their pragma_pack(Op) tokens, each struct
%  or union keyword under a #pragma pack(N) followed by the attribute
%  __nanofil_pack__(N). Tokens0 is not copied when it has no pragma
%  (GLib's resource blobs are millions of tokens).
pack_tokens(Tokens0, Tokens) :-
    (   memberchk(tok(pragma_pack(_), _), Tokens0)
    ->  once(phrase(packed_tokens(Tokens0, [none]), Tokens))
    ;   Tokens = Tokens0
    ).

packed_tokens([], _) --> [].
packed_tokens([tok(pragma_pack(Op), _)|Ts], Packs0) --> !,
    { pack_stack(Op, Packs0, Packs) },
    packed_tokens(Ts, Packs).
packed_tokens([tok(kw(K), Loc)|Ts], Packs) -->
    { Packs = [N|_], integer(N), memberchk(K, [struct, union]) }, !,
    { format(chars(Cs), '__attribute__((__nanofil_pack__(~w)))', [N]),
      phrase(tokens(Attr0, Loc, mid), Cs) },
    [tok(kw(K), Loc)], seq(Attr0),
    packed_tokens(Ts, Packs).
packed_tokens([T|Ts], Packs) --> [T], packed_tokens(Ts, Packs).

% pack_stack(+Op, +Packs0, -Packs): the #pragma pack stack after Op:
% the current value, then the saved entries s(Label, Value), Label none
% for an unnamed push. A pop restores the latest entry, or with a label
% the latest entry of that label, dropping those above it; a pop that
% finds none changes nothing (clang warns), except that an unnamed pop
% of an empty stack restores the default, as GCC's.
pack_stack(set(N), [_|S], [N|S]).
pack_stack(push(L, keep), [C|S], [C, s(L, C)|S]).
pack_stack(push(L, N), [C|S], [N, s(L, C)|S]) :- N \== keep.
pack_stack(pop(none), [_|S], Packs) :-
    ( S = [s(_, V)|S1] -> Packs = [V|S1] ; Packs = [none] ).
pack_stack(pop(L), [C|S], Packs) :-
    L \== none,
    ( append(_, [s(L, V)|S1], S) -> Packs = [V|S1] ; Packs = [C|S] ).
pack_stack(show, Packs, Packs).

%! pack_op(+Args, -Op) is semidet.
%
%  Op is the pragma_pack operation of #pragma pack(Args), Args its
%  operands as atoms and integers: pack() sets the default, pack(N)
%  sets N, pack(push[, Label][, N]) saves the current value first,
%  pack(pop[, Label]) restores it, and pack(show) changes nothing. N is
%  a power of two up to 16. Fails for any other form, which nanofil
%  refuses.
pack_op([], set(none)) :- !.
pack_op([push], push(none, keep)) :- !.
pack_op([pop], pop(none)) :- !.
pack_op([show], show) :- !.
pack_op([push, ',', N], push(none, N)) :- integer(N), !, pack_value(N).
pack_op([push, ',', L], push(L, keep)) :- pack_label(L), !.
pack_op([push, ',', L, ',', N], push(L, N)) :- !, pack_label(L), pack_value(N).
pack_op([pop, ',', L], pop(L)) :- !, pack_label(L).
pack_op([N], set(N)) :- pack_value(N).

pack_value(N) :- memberchk(N, [1, 2, 4, 8, 16]).
pack_label(L) :- atom(L), atom_chars(L, [C|_]), ident_start(C).

%% Lines, blanks and comments

% tokens(-Tokens, +Loc, +Where)//: Tokens are the tokens of the rest of
% the input, which starts at Loc. Where is bol at the beginning of a
% line, where `#` starts a directive, and mid elsewhere. tokens//4 also
% gives the location End at the end of the input.
tokens(Ts, Loc, Where) --> tokens(Ts, Loc, Where, _).

tokens(Ts, Loc, _, End) -->
    ['\n'], !,
    { loc_next_line(Loc, Loc1) },
    tokens(Ts, Loc1, bol, End).
tokens([tok(T, Loc)|Ts], Loc, bol, End) -->
    ['#'], spaces, pragma_weak(T), !,
    tokens(Ts, Loc, mid, End).
tokens([tok(pragma_pack(Op), Loc)|Ts], Loc, bol, End) -->
    ['#'], spaces, "pragma", [C], { blank(C) }, spaces, "pack", !,
    pack_line(Cs),
    {   catch(phrase(tokens(Args0, Loc, mid), Cs), _, fail),
        maplist(pack_arg, Args0, Args),
        Args = ['('|Rest], append(Inner, [')'], Rest),
        pack_op(Inner, Op)
    ->  true
    ;   format(atom(M), '~w: this #pragma pack is not supported', [Loc]),
        throw(nanofil_error(M))
    },
    tokens(Ts, Loc, mid, End).
tokens(Ts, Loc, bol, End) -->
    ['#'], !,
    directive(Loc, Loc1),
    tokens(Ts, Loc1, bol, End).
tokens(Ts, Loc, Where, End) -->
    [C], { blank(C) }, !,
    tokens(Ts, Loc, Where, End).
tokens(Ts, Loc, Where, End) -->
    ['/', '*'], !,
    block_comment(Loc, Loc1),
    tokens(Ts, Loc1, Where, End).
tokens(Ts, Loc, _, End) -->
    ['/', '/'], !,
    line_rest,
    tokens(Ts, Loc, mid, End).
tokens([tok(T, Loc)|Ts], Loc, _, End) -->
    token(T, Loc), !,
    tokens(Ts, Loc, mid, End).
tokens([], Loc, _, Loc) --> [].
tokens(_, Loc, _, _) -->
    [C],
    { loc_error(Loc, 'unexpected character ~q', [C]) }.

loc_next_line(File:N, File:N1) :- N1 is N + 1.

blank(' ').
blank('\t').
blank('\r').
blank('\f').
blank('\v').

% line_rest//: the rest of the line, leaving its newline in the input.
line_rest, ['\n'] --> ['\n'], !.
line_rest --> [_], !, line_rest.
line_rest --> [].

% block_comment(+Loc0, -Loc)//: the rest of a comment after its /*;
% Loc is Loc0 advanced past the comment's newlines.
block_comment(Loc, Loc) --> ['*', '/'], !.
block_comment(Loc0, Loc) -->
    ['\n'], !,
    { loc_next_line(Loc0, Loc1) },
    block_comment(Loc1, Loc).
block_comment(Loc0, Loc) -->
    [_], !,
    block_comment(Loc0, Loc).
block_comment(Loc, _) --> { loc_error(Loc, 'unterminated comment', []) }.

% directive(+Loc0, -Loc)//: a directive line after its `#`; Loc is the
% location of the line that ends it. A line marker `# N "file" flags` or
% `#line N "file"` says the next line is line N of file. Any other
% directive is skipped.
directive(Loc0, Loc) -->
    spaces,
    ( "line" -> spaces ; [] ),
    (   digits1(Ds), spaces, { number_chars(N, Ds), N0 is N - 1 }
    ->  (   ['"']
        ->  marker_file(Fs),
            { atom_chars(File, Fs) }
        ;   { Loc0 = File:_ }
        ),
        { Loc = File:N0 }
    ;   { Loc = Loc0 }
    ),
    line_rest.

% pack_line(-Cs)//: the rest of a #pragma pack line, before its newline.
pack_line([]), ['\n'] --> ['\n'], !.
pack_line([C|Cs]) --> [C], !, pack_line(Cs).
pack_line([]) --> [].

pack_arg(tok(id(A), _), A).
pack_arg(tok(p(A), _), A).
pack_arg(tok(int(N, _), _), N).

% pragma_weak(-T)//: `pragma weak Name` or `pragma weak Name = Target`
% after the line's `#`, up to its newline.
pragma_weak(pragma_weak(Name, Target)) -->
    "pragma", [C], { blank(C) }, spaces, "weak", [D], { blank(D) }, spaces,
    identifier(Name), spaces,
    (   ['='] -> spaces, identifier(Target), spaces ; { Target = none } ),
    pragma_end.
pragma_end, ['\n'] --> ['\n'], !.
pragma_end([], []).
identifier(Name) -->
    [C], { ident_start(C) }, ident_rest(Cs), { atom_chars(Name, [C|Cs]) }.

marker_file([]) --> ['"'], !.
marker_file([C|Cs]) --> [C], marker_file(Cs).

spaces -->
    [C], { blank(C) }, !,
    spaces.
spaces --> [].

digits1([D|Ds]) --> [D], { decimal(D) }, digits0(Ds).

digits0([D|Ds]) -->
    [D], { decimal(D) }, !,
    digits0(Ds).
digits0([]) --> [].

% Character classes as ASCII ranges: char_type/2's classes differ
% between Prolog hosts, and C and IR source only need these.

%! decimal(+C) is semidet.
%
%  C is a decimal digit character, '0' to '9'.
decimal(D) :- D @>= '0', D @=< '9'.

letter(C) :- ( C @>= a, C @=< z -> true ; C @>= 'A', C @=< 'Z' ).

%% Tokens

% token(-T, +Loc)//: one token, the T of a tok(T, Loc) term. Wide and
% u8 prefixes are tried before identifiers, which they would start.
token(str(Bs), Loc) -->
    ['u', '8', '"'], !,
    str_body(Loc, Bs).
token(chr(V), Loc) -->
    [P, '\''], { wide_prefix(P, Type) }, !,
    wide_lit_chars('\'', Loc, Vs),
    { wide_char_value(Vs, Type, V, Loc) }.
token(wstr(Type, Vs), Loc) -->
    [P, '"'], { wide_prefix(P, Type) }, !,
    wide_lit_chars('"', Loc, Vs),
    { wide_fits(Type, Vs, Loc) }.
token(T, _) -->
    [C], { ident_start(C) }, !,
    ident_rest(Cs),
    {   atom_chars(A, [C|Cs]),
        ( keyword(A, K) -> T = kw(K) ; T = id(A) )
    }.
token(T, Loc) -->
    [C], { decimal(C) }, !,
    number([C], T, Loc).
token(T, Loc) -->
    ['.', D], { decimal(D) }, !,
    number(['.', D], T, Loc).
token(chr(V), Loc) -->
    ['\''], !,
    char_body(Loc, Bs),
    { char_value(Bs, V, Loc) }.
token(str(Bs), Loc) -->
    ['"'], !,
    str_body(Loc, Bs).
token(p(P), _) --> punct(P).

%! ident_start(+C) is semidet.
%
%  C may begin an identifier: an ASCII letter, '_' or '$' (a GNU
%  extension).
ident_start(C) :- letter(C), !.
ident_start('_').
ident_start('$').

%! ident_rest(-Cs)// is det.
%
%  Cs is the longest run of identifier characters (ident_char/1) next
%  in the input.
ident_rest([C|Cs]) -->
    [C], { ident_char(C) }, !,
    ident_rest(Cs).
ident_rest([]) --> [].

%! ident_char(+C) is semidet.
%
%  C may continue an identifier: an ASCII letter, a digit, '_' or '$'.
ident_char(C) :- ( letter(C) ; decimal(C) ), !.
ident_char('_').
ident_char('$').

%% Numbers

% number(+Prefix, -T, +Loc)//: T is the int or float token of the
% pp-number that starts with the already-read characters Prefix.
number(Cs0, T, Loc) -->
    pp_number_rest(Cs1),
    {   append(Cs0, Cs1, Cs),
        number_token(Cs, T, Loc)
    }.

pp_number_rest([E, S|Cs]) -->
    [E, S],
    { memberchk(E, [e, 'E', p, 'P']), memberchk(S, ['+', '-']) }, !,
    pp_number_rest(Cs).
pp_number_rest([C|Cs]) -->
    [C], { ident_char(C) ; C == '.' }, !,
    pp_number_rest(Cs).
pp_number_rest([]) --> [].

% number_token(+Chars, -T, +Loc): T is int(Value, Suffix-Radix) or
% float(Chars) for the pp-number Chars; anything else is an error.
number_token(Cs, T, Loc) :-
    (   phrase(integer_literal(V, Suffix), Cs)
    ->  T = int(V, Suffix)
    ;   phrase(float_chars, Cs)
    ->  T = float(Cs)
    ;   atom_chars(A, Cs),
        loc_error(Loc, 'bad number ~w', [A])
    ).

integer_literal(V, Suffix-Radix) -->
    (   ['0', X], { memberchk(X, [x, 'X']) }
    ->  hex_digits(Ds),
        { Ds \== [], base_value(Ds, 16, V), Radix = other }
    ;   ['0', X], { memberchk(X, [b, 'B']) }
    ->  % A binary constant (C23 6.4.4.1, a GNU extension before it;
        % PureDOOM's MUS decoder masks events with 0b01110000) is typed
        % as an octal or hexadecimal one is.
        bin_digits(Ds),
        { Ds \== [], base_value(Ds, 2, V), Radix = other }
    ;   ['0']
    ->  oct_digits(Ds),
        { base_value(Ds, 8, V), Radix = other }
    ;   dec_digits(Ds),
        { Ds \== [], base_value(Ds, 10, V), Radix = dec }
    ),
    int_suffix(Suffix).

hex_digits([D|Ds]) -->
    [D], { digit_weight(D, _) }, !,
    hex_digits(Ds).
hex_digits([]) --> [].

bin_digits([D|Ds]) -->
    [D], { memberchk(D, ['0', '1']) }, !,
    bin_digits(Ds).
bin_digits([]) --> [].

oct_digits([D|Ds]) -->
    [D], { decimal(D), D @< '8' }, !,
    oct_digits(Ds).
oct_digits([]) --> [].

dec_digits([D|Ds]) -->
    [D], { decimal(D) }, !,
    dec_digits(Ds).
dec_digits([]) --> [].

% base_value(+Digits, +Base, -Value): Value is the number Digits spell
% in Base.
base_value(Ds, Base, V) :- foldl(add_digit(Base), Ds, 0, V).

add_digit(Base, D, V0, V) :-
    digit_weight(D, W),
    V is V0 * Base + W.

% digit_weight(Char, Weight): the value of a hexadecimal digit.
digit_weight(D, W) :- sub_atom('0123456789abcdef', W, 1, _, D), !.
digit_weight(D, W) :- sub_atom('ABCDEF', W0, 1, _, D), W is W0 + 10.

% int_suffix(-Suffix)//: Suffix names the rest of the pp-number, an
% integer suffix in either case and order (u, l, ll, ul, ull or none).
% It fails if the rest is not such a suffix.
int_suffix(Suffix) -->
    suffix_chars(Cs),
    {   maplist(suffix_lower, Cs, Ls),
        atom_chars(A, Ls),
        suffix_name(A, Suffix)
    }.

suffix_chars([C|Cs]) -->
    [C], !,
    suffix_chars(Cs).
suffix_chars([]) --> [].

suffix_lower(C, L) :-
    (   sub_atom('ULX', I, 1, _, C)
    ->  sub_atom(ulx, I, 1, _, L)
    ;   L = C
    ).

suffix_name('', none).
suffix_name(u, u).
suffix_name(l, l).
suffix_name(ll, ll).
suffix_name(ul, ul).
suffix_name(lu, ul).
suffix_name(ull, ull).
suffix_name(llu, ull).

% Only the characters are checked here; the lowering rejects floats.
float_chars -->
    [C],
    {   decimal(C)
    ;   memberchk(C, ['.', e, 'E', '+', '-', f, 'F', l, 'L', x, 'X', p, 'P'])
    ;   digit_weight(C, _)
    }, !,
    float_chars.
float_chars --> [].

%% Character and string bodies: lists of byte values.

char_body(Loc, []) -->
    ['\''], !,
    { loc_error(Loc, 'empty character constant', []) }.
char_body(Loc, Bs) --> lit_chars('\'', Loc, Bs).

str_body(Loc, Bs) --> lit_chars('"', Loc, Bs).

% lit_chars(+Quote, +Loc, -Bytes)//: Bytes is the literal body up to the
% closing Quote, with escapes decoded. The source is read as bytes
% (main and c_pp read files so), and a narrow literal keeps them as
% written, as clang does, valid UTF-8 or not (oniguruma's EUC-JP
% tests); a code point above 255, from text that was not read as
% bytes, is encoded as UTF-8.
lit_chars(Q, _, []) --> [Q], !.
lit_chars(_, Loc, _) -->
    ['\n'], !,
    { loc_error(Loc, 'unterminated literal', []) }.
lit_chars(Q, Loc, Bs) -->                       % C11 6.4.3: \u, \U
    ['\\'], ucn(K), !,
    { utf8_bytes(K, Us),       % clang's execution character set is UTF-8
      append(Us, Bs0, Bs) },
    lit_chars(Q, Loc, Bs0).
lit_chars(Q, Loc, [B|Bs]) -->
    ['\\'], !,
    escape(Loc, B),
    lit_chars(Q, Loc, Bs).
lit_chars(Q, Loc, Bs) -->
    [C], !,
    { char_code(C, K), ( K < 256 -> Bs = [K|Bs0] ; utf8_bytes(K, Us), append(Us, Bs0, Bs) ) },
    lit_chars(Q, Loc, Bs0).
lit_chars(_, Loc, _) --> { loc_error(Loc, 'unterminated literal', []) }.

% escape(+Loc, -Byte)//: Byte is the value of an escape after its
% backslash, reduced to 8 bits.
escape(_, B) --> [C], { simple_escape(C, B) }, !.
escape(_, B) -->
    ['x'], !,
    hex_digits(Ds),
    { Ds \== [], base_value(Ds, 16, V), B is V /\ 255 }.
escape(_, B) -->
    [D], { decimal(D), D @< '8' }, !,
    oct_upto(2, Ds),
    { base_value([D|Ds], 8, V), B is V /\ 255 }.
% An unknown escape is the character itself, as clang has it with only
% a warning (C11 6.4.4.4p8 leaves it undefined): btrfs-progs prints
% "\(".
escape(_, B) --> [C], { C \== '\n', char_code(C, B) }, !.
escape(Loc, _) --> { loc_error(Loc, 'unterminated literal', []) }.

% ucn(-Code)//: a universal character name after its backslash.
ucn(K) --> ['u'], hex_exactly(4, Ds), { base_value(Ds, 16, K) }.
ucn(K) --> ['U'], hex_exactly(8, Ds), { base_value(Ds, 16, K) }.

% oct_upto(+N, -Digits)//: Digits are at most N octal digits, as many as
% there are.
oct_upto(0, []) --> !.
oct_upto(N, [D|Ds]) -->
    [D], { decimal(D), D @< '8' }, !,
    { N1 is N - 1 },
    oct_upto(N1, Ds).
oct_upto(_, []) --> [].

simple_escape(n, 10).
simple_escape(t, 9).
simple_escape(r, 13).
simple_escape(a, 7).
simple_escape(b, 8).
simple_escape(f, 12).
simple_escape(v, 11).
simple_escape('\\', 92).
simple_escape('\'', 39).
simple_escape('"', 34).
simple_escape('?', 63).
simple_escape(e, 27).                   % GNU: ESC
simple_escape('E', 27).

%% Wide literals: elements are code points, not UTF-8 bytes.

wide_prefix('L', int).
wide_prefix(u, ushort).
wide_prefix('U', uint).

% wide_lit_chars(+Quote, +Loc, -Codes)//: like lit_chars//3, but Codes
% are the body's code points: the source's bytes decoded as UTF-8 (a
% byte that starts no valid sequence stands for itself).
wide_lit_chars(Q, _, []) --> [Q], !.
wide_lit_chars(_, Loc, _) -->
    ['\n'], !,
    { loc_error(Loc, 'unterminated literal', []) }.
wide_lit_chars(Q, Loc, [V|Vs]) -->
    ['\\'], !,
    wide_escape(Loc, V),
    wide_lit_chars(Q, Loc, Vs).
wide_lit_chars(Q, Loc, [K|Vs]) -->
    utf8_char(K), !,
    wide_lit_chars(Q, Loc, Vs).
wide_lit_chars(Q, Loc, [K|Vs]) -->
    [C], !,
    { char_code(C, K) },
    wide_lit_chars(Q, Loc, Vs).
wide_lit_chars(_, Loc, _) -->
    { loc_error(Loc, 'unterminated literal', []) }.

wide_escape(_, B) --> [C], { simple_escape(C, B) }, !.
wide_escape(_, V) -->
    ['x'], !,
    hex_digits(Ds),
    { Ds \== [], base_value(Ds, 16, V) }.
wide_escape(_, V) -->
    ['u'], !,
    hex_exactly(4, Ds),
    { base_value(Ds, 16, V) }.
wide_escape(_, V) -->
    ['U'], !,
    hex_exactly(8, Ds),
    { base_value(Ds, 16, V) }.
wide_escape(_, V) -->
    [D], { decimal(D), D @< '8' }, !,
    oct_upto(2, Ds),
    { base_value([D|Ds], 8, V) }.
wide_escape(_, V) --> utf8_char(V), { V =\= 10 }, !.
wide_escape(_, V) --> [C], { C \== '\n', char_code(C, V) }, !.
wide_escape(Loc, _) --> { loc_error(Loc, 'unterminated literal', []) }.

% hex_exactly(+N, -Digits)//: Digits are exactly N hexadecimal digits.
hex_exactly(0, []) --> !.
hex_exactly(N, [D|Ds]) -->
    [D], { digit_weight(D, W), W < 16 }, !,
    { N1 is N - 1 },
    hex_exactly(N1, Ds).

% wide_fits(+Type, +Codes, +Loc): each element of Codes fits Type (no
% surrogate pairs for char16_t); an error otherwise.
wide_fits(Type, Vs, Loc) :-
    (   wide_max(Type, Max), member(V, Vs), V > Max
    ->  loc_error(Loc, 'wide literal element ~w does not fit ~w', [V, Type])
    ;   true
    ).

wide_max(int, 2147483647).
wide_max(ushort, 65535).
wide_max(uint, 4294967295).

% wide_char_value(+Codes, +Type, -Value, +Loc): Value is the single
% element of a wide character constant, as an int; wchar_t is int here.
wide_char_value([], _, _, Loc) :- multi_char_error(Loc).
wide_char_value([V|Vs], Type, Value, Loc) :-
    wide_char_value(Vs, V, Type, Value, Loc).

% wide_char_value(+Codes, +V, +Type, -Value, +Loc): like
% wide_char_value/4 for [V|Codes].
wide_char_value([], V, Type, V, Loc) :-
    char_fit_type(Type, FitType),
    wide_fits(FitType, [V], Loc).
wide_char_value([_|_], _, _, _, Loc) :- multi_char_error(Loc).

% char_fit_type(?Type, ?FitType): a wide character constant of element
% type Type must fit FitType; U'x' has type char32_t but value as int.
char_fit_type(int, int).
char_fit_type(ushort, ushort).
char_fit_type(uint, int).

% char_value(+Bytes, -Value, +Loc): Value is the single byte of a
% character constant, as a (signed) char promoted to int. A
% multi-character constant is rejected.
char_value([], _, Loc) :- multi_char_error(Loc).
char_value([B|Bs], V, Loc) :- char_value(Bs, B, V, Loc).

% char_value(+Bytes, +B, -Value, +Loc): like char_value/3 for [B|Bytes].
char_value([], B, V, _) :-
    (   B >= 128
    ->  V is B - 256
    ;   V = B
    ).
char_value([_|_], _, _, Loc) :- multi_char_error(Loc).

multi_char_error(Loc) :- loc_error(Loc, 'multi-character constant', []).

% utf8_char(-Code)//: the next bytes are the UTF-8 encoding of Code, of
% two to four bytes.
utf8_char(K) -->
    [C0], { char_code(C0, B0), B0 >= 0xC2, B0 =< 0xF4,
            ( B0 < 0xE0 -> N = 1, K0 is B0 /\ 0x1F
            ; B0 < 0xF0 -> N = 2, K0 is B0 /\ 0x0F
            ; N = 3, K0 is B0 /\ 0x07 ) },
    utf8_continuation(N, K0, K),
    { utf8_bytes(K, Bs), length(Bs, L), L =:= N + 1 }.   % not overlong

utf8_continuation(0, K, K) --> !.
utf8_continuation(N, K0, K) -->
    [C], { char_code(C, B), B /\ 0xC0 =:= 0x80, K1 is K0 << 6 \/ (B /\ 0x3F),
           N1 is N - 1 },
    utf8_continuation(N1, K1, K).

% utf8_bytes(+Code, -Bytes): Bytes is the UTF-8 encoding of Code.
utf8_bytes(K, [K]) :- K < 128, !.
utf8_bytes(K, [B1, B2]) :-
    K < 2048, !,
    B1 is 192 \/ (K >> 6),
    B2 is 128 \/ (K /\ 63).
utf8_bytes(K, [B1, B2, B3]) :-
    K < 65536, !,
    B1 is 224 \/ (K >> 12),
    B2 is 128 \/ ((K >> 6) /\ 63),
    B3 is 128 \/ (K /\ 63).
utf8_bytes(K, [B1, B2, B3, B4]) :-
    B1 is 240 \/ (K >> 18),
    B2 is 128 \/ ((K >> 12) /\ 63),
    B3 is 128 \/ ((K >> 6) /\ 63),
    B4 is 128 \/ (K /\ 63).

%% Punctuators, longest first.

punct(P) -->
    [A, B, C], { atom_chars(P, [A, B, C]), punctuator(P) }, !.
punct(P) -->
    [A, B], { atom_chars(P, [A, B]), punctuator(P) }, !.
punct(P) -->
    [C],
    {   memberchk(C, ['[', ']', '(', ')', '{', '}', '.', '&', '*', '+', '-',
                      '~', '!', '/', '%', '<', '>', '^', '|', '?', ':', ';',
                      '=', ',', '#']),
        atom_chars(P, [C])
    }.

%! punctuator(?Spelling) is nondet.
%
%  Spelling is one of C's punctuators of two or three characters
%  (C11 6.4.6), digraphs aside; the one-character ones are punct//1's.
punctuator('...').  punctuator('<<=').  punctuator('>>=').
punctuator('->').  punctuator('++').  punctuator('--').  punctuator('<<').
punctuator('>>').  punctuator('<=').  punctuator('>=').  punctuator('==').
punctuator('!=').  punctuator('&&').  punctuator('||').  punctuator('*=').
punctuator('/=').  punctuator('%=').  punctuator('+=').  punctuator('-=').
punctuator('&=').  punctuator('^=').  punctuator('|=').  punctuator('##').

%! digraph(?Spelling) is nondet.
%
%  Spelling is a digraph (C11 6.4.6p3), a preprocessing token that
%  stands for [, ], {, } or #.
digraph('<:').  digraph(':>').  digraph('<%').  digraph('%>').  digraph('%:').

%% Keywords, with GNU alternate spellings folded.

%! keyword(?Spelling, ?Keyword) is nondet.
%! keyword(+Spelling, -Keyword) is semidet.
%
%  Keyword is the kw/1 name of the C or GNU keyword spelled Spelling.
keyword(auto, auto).
keyword(break, break).
keyword(case, case).
keyword(char, char).
keyword(const, const).
keyword(continue, continue).
keyword(default, default).
keyword(do, do).
keyword(double, double).
keyword(else, else).
keyword(enum, enum).
keyword(extern, extern).
keyword(float, float).
keyword(for, for).
keyword(goto, goto).
keyword(if, if).
keyword(inline, inline).
keyword(int, int).
keyword(long, long).
keyword(register, register).
keyword(restrict, restrict).
keyword(return, return).
keyword(short, short).
keyword(signed, signed).
keyword(sizeof, sizeof).
keyword(static, static).
keyword(struct, struct).
keyword(switch, switch).
keyword(typedef, typedef).
keyword(union, union).
keyword(unsigned, unsigned).
keyword(void, void).
keyword(volatile, volatile).
keyword(while, while).
keyword('_Alignas', alignas).
keyword('_Alignof', alignof).
keyword('_Atomic', atomic).
keyword('_Bool', bool).
keyword('_Complex', complex).
keyword('_Generic', generic).
keyword('_Imaginary', imaginary).
keyword('_Noreturn', noreturn).
keyword('_Static_assert', static_assert).
keyword('_Thread_local', thread_local).
keyword('__restrict', restrict).
keyword('__restrict__', restrict).
keyword('__inline', inline).
keyword('__inline__', inline).
keyword('__const', const).
keyword('__const__', const).
keyword('__volatile', volatile).
keyword('__volatile__', volatile).
keyword('__signed', signed).
keyword('__signed__', signed).
keyword(asm, asm).
keyword('__asm', asm).
keyword('__asm__', asm).
keyword('__attribute', attribute).
keyword('__attribute__', attribute).
keyword('__extension__', extension).
keyword('__auto_type', auto_type).
keyword('__typeof', typeof).
keyword('__typeof__', typeof).
keyword(typeof, typeof).
keyword('__alignof', alignof).
keyword('__alignof__', alignof).
keyword('__int128', int128).
keyword('_Float16', float16).
keyword('__bf16', bf16).
keyword('__thread', thread_local).

%! c23_tokens(+Tokens0, -Tokens) is det.
%
%  Tokens are Tokens0 read as C23, where bool, true, false, nullptr,
%  static_assert, alignas, alignof and thread_local are keywords (C23
%  6.4.1p1); C17 spells the type-like ones _Bool, _Static_assert, ...
%  and has no true, false or nullptr keywords. main applies it when
%  NANOFIL_STD is c23 (nanofil-cc sets it for -std=c23 or gnu23).
c23_tokens(Ts0, Ts) :- maplist(c23_token, Ts0, Ts).

c23_token(tok(id(A), Loc), tok(kw(K), Loc)) :- c23_keyword(A, K), !.
c23_token(T, T).

c23_keyword(bool, bool).
c23_keyword(true, true).
c23_keyword(false, false).
c23_keyword(nullptr, nullptr).
c23_keyword(static_assert, static_assert).
c23_keyword(alignas, alignas).
c23_keyword(alignof, alignof).
c23_keyword(thread_local, thread_local).

% loc_error(+Loc, +Format, +Args): throw a nanofil_error/1 located at Loc.
loc_error(File:Line, Fmt, Args) :-
    format(atom(Msg0), Fmt, Args),
    format(atom(Msg), '~w:~w: ~w', [File, Line, Msg0]),
    throw(nanofil_error(Msg)).

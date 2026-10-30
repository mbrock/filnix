/*  IEEE 754 binary32 and binary64 arithmetic with integers only, rounding
    to nearest, ties to even.

    Operands and results are unsigned bit patterns, never host floats.
    Finite intermediates are exact rationals, and round_ratio is the
    single rounding boundary, gradual underflow and overflow included.
    All public inputs must be concrete.

    ## Predicates

    K is `s` (binary32), `d` (binary64) or `x` (the x87 80-bit extended
    format of C's `long double` on x86-64: a sign, 15 exponent bits and
    a 64-bit significand whose integer bit is explicit, in the low 80
    bits of the pattern). An x NaN operand follows the x87's rule
    instead of SSE's: when both operands are NaNs, a quiet one wins over
    a signaling one, else the one with the larger significand, else the
    first.

    | Predicate | Notes |
    |---|---|
    | `ieee_binary(K, Op, A, B, R)` | Op is `add`, `sub`, `mul` or `div` |
    | `ieee_neg(K, A, B)` | flips the sign bit |
    | `ieee_convert(From, To, A, B)` | between the two formats |
    | `ieee_from_int(K, N, B)` | N any integer |
    | `ieee_to_int(K, B, N)` | truncates; fails for nonfinite inputs, and the caller checks the destination integer's range |
    | `ieee_compare(K, Cond, A, B, R)` | R is 1 or 0; Cond is `eq`, `ne`, `lt`, `le`, `gt`, `ge`, `o` (ordered) or `uo` (unordered) |
    | `ieee_parse(K, Chars, B)` | a decimal or C hexadecimal significand, without a C type suffix: the frontend selects K after removing the suffix |
    | `ieee_decimal(K, B, Chars)` | an exact decimal, not necessarily the shortest; fails for nonfinite inputs |
*/
:- module(ieee, [ieee_binary/5, ieee_neg/3, ieee_convert/4,
                 ieee_from_int/3, ieee_to_int/3, ieee_compare/5,
                 ieee_parse/3, ieee_decimal/3]).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(error)).

% format(K, fraction bits, exponent bits, bias): the fraction excludes
% the integer bit, which x stores explicitly (integer_bit/2).
format(s, 23, 8, 127).
format(d, 52, 11, 1023).
format(x, 63, 15, 16383).

% integer_bit(K, Bits): the bits of the explicit integer bit, if any;
% the exponent starts above it.
integer_bit(s, 0).
integer_bit(d, 0).
integer_bit(x, 1).
exponent_shift(K, Sh) :- format(K, F, _, _), integer_bit(K, I), Sh is F + I.

decode(K, B, S, T) :-
    must_be(integer, B), format(K, F, E, Bias), exponent_shift(K, Sh),
    S is B >> (Sh + E), M is B /\ ((1 << F) - 1),
    X is (B >> Sh) /\ ((1 << E) - 1), Max is (1 << E) - 1,
    ( X =:= Max -> ( M =:= 0 -> T = inf ; T = nan )
    ; X =:= 0 -> P is 1 - Bias - F, Sig is B /\ ((1 << Sh) - 1), T = finite(Sig, P)
    ; N is (1 << F) + M, P is X - Bias - F, T = finite(N, P) ).

sign_bits(K, S, B) :- format(K, _, E, _), exponent_shift(K, Sh), B is S << (Sh + E).
infinity(K, S, B) :-
    format(K, F, E, _), exponent_shift(K, Sh), sign_bits(K, S, SB),
    integer_bit(K, I), B is SB + (((1 << E) - 1) << Sh) + (I << F).
quiet(K, A, B) :- format(K, F, _, _), B is A \/ (1 << (F - 1)).
invalid(K, B) :- infinity(K, 1, I), quiet(K, I, B).

% floor(log2(N)), for positive integers, without host logarithms.
ilog(N, L) :- ilog(N, -1, L).
ilog(0, L, L) :- !.
ilog(N, A, L) :- N1 is N >> 1, A1 is A + 1, ilog(N1, A1, L).

scale(N, D, E, A, B) :-
    ( E >= 0 -> A is N << E, B = D ; A = N, B is D << (-E) ).

% Rounding an exact positive quotient, including the halfway parity bit.
round_even(N, D, Q) :-
    Q0 is N // D, R is N mod D, Twice is 2 * R,
    ( Twice > D ; Twice =:= D, Q0 mod 2 =:= 1 ), !,
    Q is Q0 + 1.
round_even(N, D, Q) :- Q is N // D.

round_ratio(K, S, 0, _, B) :- !, sign_bits(K, S, B).
round_ratio(K, S, N, D, B) :-
    format(K, F, _, Bias), ilog(N, LN), ilog(D, LD), E0 is LN - LD,
    scale(N, D, -E0, A0, B0),
    ( A0 < B0 -> E is E0 - 1 ; E = E0 ),
    Emin is 1 - Bias, Step is max(E, Emin) - F,
    scale(N, D, -Step, A, C), round_even(A, C, Q),
    ( Q >= 1 << (F + 1) -> Q1 is Q >> 1, E1 is E + 1
    ; Q1 = Q, E1 is max(E, Emin) ),
    integer_bit(K, I), exponent_shift(K, Sh),
    ( E1 > Bias -> infinity(K, S, B)
    ; Q1 < 1 << F -> Exp = 0, Mant = Q1
    ; Exp is E1 + Bias, Mant is Q1 - ((1 - I) << F) ),
    ( E1 =< Bias -> sign_bits(K, S, SB), B is SB + (Exp << Sh) + Mant
    ; true ).

finite_ratio(finite(N, E), A, B) :- scale(N, 1, E, A, B).
signed_ratio(S, T, N, D) :-
    finite_ratio(T, A, D), N is (1 - 2 * S) * A.

%! ieee_from_int(+K, +N, -B) is det.
%
%  B is the format-K bit pattern nearest the integer N, ties to even.
ieee_from_int(K, N, B) :-
    must_be(integer, N), ( N < 0 -> S = 1 ; S = 0 ),
    magnitude_integer(N, A), round_ratio(K, S, A, 1, B).

% Trealla's abs/1 and unary minus wrap a computed native INT64_MIN;
% binary subtraction promotes it to a bignum on both hosts.
magnitude_integer(N, A) :- ( N < 0 -> A is 0 - N ; A = N ).

%! ieee_to_int(+K, +B, -N) is semidet.
%
%  N is the finite float B truncated toward zero. Fails for an infinity
%  or NaN; the caller checks that N fits the destination integer.
ieee_to_int(K, B, N) :-
    decode(K, B, S, T), T = finite(_, _),
    finite_ratio(T, A, D), N is (1 - 2 * S) * (A // D).

%! ieee_neg(+K, +A, -B) is det.
%
%  B is A with its sign bit flipped, NaNs included.
ieee_neg(K, A, B) :-
    must_be(integer, A), sign_bits(K, 1, S), B is xor(A, S).

%! ieee_binary(+K, +Op, +A, +B, -R) is det.
%
%  R is A Op B in format K, Op add, sub, mul or div, rounded to nearest,
%  ties to even, with SSE's NaN rules (x87's for K = x, header).
ieee_binary(K, Op, A, B, R) :-
    decode(K, A, SA, TA), decode(K, B, SB, TB),
    ( TA == nan, TB == nan, K == x -> x87_nan(A, B, R)
    ; TA == nan -> quiet(K, A, R)
    ; TB == nan -> quiet(K, B, R)
    ; binary(Op, K, SA, TA, SB, TB, R) ).

% The x87 picks between two NaN operands (Intel SDM vol. 1, 4.8.3.5).
x87_nan(A, B, R) :-
    QA is (A >> 62) /\ 1, QB is (B >> 62) /\ 1,
    MA is A /\ ((1 << 64) - 1), MB is B /\ ((1 << 64) - 1),
    ( QA > QB -> W = A ; QB > QA -> W = B ; MB > MA -> W = B ; W = A ),
    quiet(x, W, R).

binary(sub, K, SA, TA, SB, TB, R) :-
    SC is 1 - SB, binary(add, K, SA, TA, SC, TB, R).
binary(add, K, SA, TA, SB, TB, R) :-
    ( TA == inf, TB == inf, SA =\= SB -> invalid(K, R)
    ; TA == inf -> infinity(K, SA, R)
    ; TB == inf -> infinity(K, SB, R)
    ; signed_ratio(SA, TA, A, C), signed_ratio(SB, TB, B, D),
      N is A * D + B * C, Den is C * D,
      ( N < 0 -> S = 1
      ; N =:= 0, SA =:= 1, SB =:= 1 -> S = 1
      ; S = 0 ),
      magnitude_integer(N, Abs), round_ratio(K, S, Abs, Den, R) ).
binary(mul, K, SA, TA, SB, TB, R) :-
    S is xor(SA, SB),
    ( (TA == inf, TB = finite(0, _) ; TB == inf, TA = finite(0, _))
    -> invalid(K, R)
    ; (TA == inf ; TB == inf) -> infinity(K, S, R)
    ; finite_ratio(TA, A, C), finite_ratio(TB, B, D),
      N is A * B, Den is C * D, round_ratio(K, S, N, Den, R) ).
binary(div, K, SA, TA, SB, TB, R) :-
    S is xor(SA, SB),
    ( (TA == inf, TB == inf ; TA = finite(0, _), TB = finite(0, _))
    -> invalid(K, R)
    ; TA == inf -> infinity(K, S, R)
    ; TB == inf -> sign_bits(K, S, R)
    ; TB = finite(0, _) -> infinity(K, S, R)
    ; finite_ratio(TA, A, C), finite_ratio(TB, B, D),
      N is A * D, Den is C * B, round_ratio(K, S, N, Den, R) ).

%! ieee_convert(+From, +To, +A, -B) is det.
%
%  B is the format-From float A converted to format To, rounded to
%  nearest; a NaN keeps as much of its payload as fits, aligned at the
%  top, and is quieted.
ieee_convert(From, To, A, B) :-
    decode(From, A, S, T),
    ( T == inf -> infinity(To, S, B)
    ; T == nan ->
      format(From, FF, _, _), format(To, FT, _, _),
      Payload is A /\ ((1 << FF) - 1), Shift is FT - FF,
      ( Shift >= 0 -> P is Payload << Shift ; P is Payload >> (-Shift) ),
      infinity(To, S, I), U is I \/ P, quiet(To, U, B)
    ; finite_ratio(T, N, D), round_ratio(To, S, N, D, B) ).

%! ieee_compare(+K, +Cond, +A, +B, -R) is det.
%
%  R is 1 when A Cond B holds for format-K floats, else 0. When either
%  operand is a NaN only ne and uo hold, as C's != and SSE's unordered
%  compare give.
ieee_compare(K, Cond, A, B, R) :-
    decode(K, A, SA, TA), decode(K, B, SB, TB),
    ( (TA == nan ; TB == nan) -> Order = unordered
    ; TA == inf, TB == inf -> compare(Order, SB, SA)
    ; TA == inf -> ( SA =:= 1 -> Order = (<) ; Order = (>) )
    ; TB == inf -> ( SB =:= 1 -> Order = (>) ; Order = (<) )
    ; signed_ratio(SA, TA, N, D), signed_ratio(SB, TB, M, C),
      X is N * C, Y is M * D, compare(Order, X, Y) ),
    ( condition(Cond, Order) -> R = 1 ; R = 0 ).
condition(eq, =).
condition(ne, O) :- O \== (=).
condition(lt, <).
condition(le, O) :- memberchk(O, [<, =]).
condition(gt, >).
condition(ge, O) :- memberchk(O, [>, =]).
condition(o, O) :- O \== unordered.
condition(uo, unordered).

%! ieee_parse(+K, +Cs, -B) is semidet.
%
%  B is the format-K float nearest the decimal or C hexadecimal literal
%  Cs, without a type suffix. Literals are parsed into a rational before
%  rounding: no double rounding through binary64 for a binary32 literal.
ieee_parse(K, Cs, B) :-
    phrase(literal(S, N, Radix, E), Cs),
    ( E >= 0 -> A is N * Radix ^ E, D = 1
    ; A = N, D is Radix ^ (-E) ),
    round_ratio(K, S, A, D, B).

literal(S, N, R, E) --> sign(S), magnitude(N, R, E).
sign(1) --> "-", !.
sign(0) --> "+", !.
sign(0) --> [].
magnitude(N, 2, E) -->
    "0", [X], { memberchk(X, [x, 'X']) }, !,
    significand(16, N, Places), [P], { memberchk(P, [p, 'P']) },
    exponent_value(EX), { E is EX - 4 * Places }.
magnitude(N, 10, E) -->
    significand(10, N, Places), decimal_exponent(EX), { E is EX - Places }.
decimal_exponent(E) --> [C], { memberchk(C, [e, 'E']) }, !, exponent_value(E).
decimal_exponent(0) --> [].
exponent_value(E) -->
    sign(S), digit_list(10, Ds), { Ds \== [], digits_number(Ds, 10, 0, N),
                                E is (1 - 2 * S) * N }.
significand(Base, N, Places) -->
    digit_list(Base, Before), fraction(Base, After),
    { append(Before, After, All), All \== [], length(After, Places),
      digits_number(All, Base, 0, N) }.
fraction(Base, Ds) --> ".", !, digit_list(Base, Ds).
fraction(_, []) --> [].
digit_list(Base, [N|Ns]) -->
    [C], { digit_value(C, N), N < Base }, !, digit_list(Base, Ns).
digit_list(_, []) --> [].
digit_value(C, N) :-
    char_code(C, V),
    ( V >= 48, V =< 57 -> N is V - 48
    ; V >= 97, V =< 102 -> N is V - 87
    ; V >= 65, V =< 70 -> N is V - 55 ).
digits_number([], _, N, N).
digits_number([D|Ds], Base, A, N) :-
    A1 is A * Base + D, digits_number(Ds, Base, A1, N).

%! ieee_decimal(+K, +B, -Cs) is semidet.
%
%  Cs is an exact decimal for the finite float B, not necessarily the
%  shortest; fails for an infinity or NaN. Every finite binary float has
%  a terminating decimal expansion. Writing N*5^k e-k avoids padding and
%  is exactly representable by strtof/strtod.
ieee_decimal(K, B, Cs) :-
    decode(K, B, S, finite(N, E)),
    ( E >= 0 -> M is N << E, P = 0
    ; M is N * 5 ^ (-E), P = E ),
    number_chars(M, MC), number_chars(P, PC),
    ( S =:= 1 -> Prefix = ['-'] ; Prefix = [] ),
    append([Prefix, MC, [e], PC], Cs).

/*  Parser for the phase-one QBE subset: integer classes w and l, data
    definitions with integer, string, symbol and zero items. Everything
    else is rejected with a line number.

    Text is lexed into tok(Token, Line) terms; the grammar runs over those.
*/
:- module(qbe_parse, [parse_qbe_file/2, parse_qbe_chars/2]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(charsio)).

parse_qbe_file(File, M) :-
    phrase_from_file(all_chars(Cs), File),
    parse_qbe_chars(Cs, M).

all_chars([]) --> [].
all_chars([C|Cs]) --> [C], all_chars(Cs).

parse_qbe_chars(Cs, module(Items)) :-
    (   phrase(tokens(Ts, 1), Cs) -> true
    ;   throw(nanofil_error('lexer failed'))
    ),
    (   phrase(items(Items), Ts) -> true
    ;   throw(nanofil_error('parse failed'))
    ).

%% Lexer

tokens([tok(nl, L)|Ts], L) --> [C], { C == '\n' }, !, { L1 is L + 1 }, tokens(Ts, L1).
tokens(Ts, L) --> [C], { C == '#' }, !, skip_line, tokens(Ts, L).
tokens(Ts, L) --> [C], { blank(C) }, !, tokens(Ts, L).
tokens([tok(T, L)|Ts], L) --> token(T), !, tokens(Ts, L).
tokens([], _) --> [].
tokens(_, L) --> [C], { format(atom(M), 'line ~w: unexpected character ~q', [L, C]), throw(nanofil_error(M)) }.

blank(' ').
blank('\t').
blank('\r').

skip_line, [C] --> [C], { C == '\n' }, !.
skip_line --> [_], !, skip_line.
skip_line --> [].

token(tmp(N)) --> ['%'], !, name_chars(Cs), { Cs \== [], atom_chars(N, Cs) }.
token(glo(N)) --> ['$'], !, name_chars(Cs), { Cs \== [], atom_chars(N, Cs) }.
token(lbl(N)) --> ['@'], !, name_chars(Cs), { Cs \== [], atom_chars(N, Cs) }.
token(typ(N)) --> [':'], !, name_chars(Cs), { atom_chars(N, Cs) }.
token(str(Cs)) --> ['"'], !, str_chars(Cs).
token(int(N)) --> ['-'], digit(D), !, digits(Ds), { number_chars(P, [D|Ds]), N is -P }.
token(int(N)) --> digit(D), !, digits(Ds), { number_chars(N, [D|Ds]) }.
token(dots) --> ['.', '.', '.'], !.
token(id(A)) --> ident_start(C), !, name_chars(Cs), { atom_chars(A, [C|Cs]) }.
token(P) --> [C], { memberchk(C-P, ['='-eq, ','-comma, '('-lp, ')'-rp,
                                     '{'-lb, '}'-rb, ('+')-plus]) }.

digit(D) --> [D], { char_type(D, decimal_digit) }.
digits([D|Ds]) --> digit(D), !, digits(Ds).
digits([]) --> [].

ident_start(C) --> [C], { char_type(C, alpha) ; C == '_' }.

name_chars([C|Cs]) --> [C], { name_char(C) }, !, name_chars(Cs).
name_chars([]) --> [].

name_char(C) :- char_type(C, alnum).
name_char('_').
name_char('.').

% Strings keep their escapes as written; QBE hands them to the assembler.
str_chars([]) --> ['"'], !.
str_chars(['\\', C|Cs]) --> ['\\', C], !, str_chars(Cs).
str_chars([C|Cs]) --> [C], str_chars(Cs).

%% Grammar

items(Is) --> nls, items_(Is).
items_([I|Is]) --> item(I), !, nls, items_(Is).
items_([]) --> [].
items_(_) --> [tok(T, L)], { fail_at(L, 'unexpected ~w at top level', [T]) }.

item(F) --> linkage(Lk), function(Lk, F).
item(D) --> linkage(Lk), data(Lk, D).
item(_) --> [tok(id(type), L)], { fail_at(L, 'aggregate types are not supported', []) }.

linkage(export) --> [tok(id(export), _)], !, nls.
linkage(local) --> [].

function(Lk, func(Name, Lk, Ret, Params, Blocks)) -->
    [tok(id(function), L)],
    ret_class(Ret, L),
    expect(glo(Name), 'function name'),
    expect(lp, '('), params(Params), expect(rp, ')'),
    nls, expect(lb, '{'), expect(nl, 'newline'), nls,
    blocks(Bs0),
    expect(rb, '}'),
    { fallthrough(Bs0, Name, Blocks) }.

ret_class(K, _) --> [tok(id(K), _)], { memberchk(K, [w, l, p]) }, !.
ret_class(void, _), [tok(glo(N), L)] --> [tok(glo(N), L)], !.
ret_class(_, L) --> { fail_at(L, 'only w, l and p return classes are supported', []) }.

params([]), [tok(rp, L)] --> [tok(rp, L)], !.
params([P|Ps]) --> param(P), params_(Ps).
params_([P|Ps]) --> [tok(comma, _)], !, param(P), params_(Ps).
params_([]) --> [].

param(par(K, t(N))) --> [tok(id(K), _)], { memberchk(K, [w, l, p]) }, !, expect(tmp(N), 'parameter').
param(_) --> [tok(T, L)], { fail_at(L, 'unsupported parameter ~w', [T]) }.

% Blocks as parsed: b(Label, Phis, Insts, MaybeJump), MaybeJump = none | J.
blocks([B|Bs]) --> block(B), !, blocks(Bs).
blocks([]) --> [].

block(b(Lab, Phis, Insts, J)) -->
    [tok(lbl(Lab), _)], expect(nl, 'newline after label'), nls,
    phis(Phis), insts(Insts), maybe_jump(J).

phis([P|Ps]) --> phi(P), !, nls, phis(Ps).
phis([]) --> [].

phi(phi(t(D), K, Args)) -->
    [tok(tmp(D), _), tok(eq, _), tok(id(K), _), tok(id(phi), _)],
    phi_args(Args), expect(nl, 'newline').

phi_args([L-V|As]) -->
    expect(lbl(L), 'phi label'), value(V),
    (   [tok(comma, _)] -> phi_args(As) ; { As = [] } ).

insts([I|Is]) --> inst(I), !, nls, insts(Is).
insts([]) --> [].

inst(I) --> [tok(tmp(D), L), tok(eq, _), tok(id(K), _)], !,
    { memberchk(K, [w, l, p]) -> true ; fail_at(L, 'unsupported class ~w', [K]) },
    def_rhs(t(D), K, I, L), expect(nl, 'newline').
inst(store(W, V, A)) -->
    [tok(id(Op), _)], { store_op(Op, W) }, !,
    value(V), expect(comma, ','), value(A), expect(nl, 'newline').
inst(call(void, Callee, Args)) -->
    [tok(id(call), _)], !, call_rest(Callee, Args), expect(nl, 'newline').

store_op(storeb, b).
store_op(storeh, h).
store_op(storew, w).
store_op(storel, l).
store_op(storep, p).

def_rhs(D, K, call(to(D, K), Callee, Args), _) -->
    [tok(id(call), _)], !, call_rest(Callee, Args).
def_rhs(D, K, ins(D, K, Op, Args), L) -->
    [tok(id(Name), _)],
    { (   op_name(Name, Op) -> true
      ;   fail_at(L, 'unsupported instruction ~w', [Name])
      ) },
    args(Args).

call_rest(glo(F), Args) -->
    expect(glo(F), 'direct callee'), expect(lp, '('), call_args(Args), expect(rp, ')').

call_args([]), [tok(rp, L)] --> [tok(rp, L)], !.
call_args([A|As]) --> call_arg(A), call_args_(As).
call_args_([A|As]) --> [tok(comma, _)], !, call_arg(A), call_args_(As).
call_args_([]) --> [].

call_arg(arg(K, V)) --> [tok(id(K), _)], { memberchk(K, [w, l, p]) }, !, value(V).
call_arg(_) --> [tok(T, L)], { fail_at(L, 'unsupported call argument ~w', [T]) }.

args([V|Vs]) --> value(V), !, args_(Vs).
args([]) --> [].
args_([V|Vs]) --> [tok(comma, _)], !, value(V), args_(Vs).
args_([]) --> [].

value(t(N)) --> [tok(tmp(N), _)], !.
value(c(N)) --> [tok(int(N), _)], !.
value(glo(N)) --> [tok(glo(N), _)], !.

maybe_jump(jmp(L)) --> [tok(id(jmp), _)], !, expect(lbl(L), 'label'), expect(nl, 'newline'), nls.
maybe_jump(jnz(V, L1, L2)) -->
    [tok(id(jnz), _)], !, value(V), expect(comma, ','), expect(lbl(L1), 'label'),
    expect(comma, ','), expect(lbl(L2), 'label'), expect(nl, 'newline'), nls.
maybe_jump(R) --> [tok(id(ret), _)], !, ( value(V) -> { R = ret(V) } ; { R = ret } ),
    expect(nl, 'newline'), nls.
maybe_jump(hlt) --> [tok(id(hlt), _)], !, expect(nl, 'newline'), nls.
maybe_jump(none) --> [].

fallthrough([], Fn, []) :-
    format(atom(M), 'in $~w: no blocks', [Fn]), throw(nanofil_error(M)).
fallthrough([b(L, P, I, J0)|Bs], Fn, [blk(L, P, I, J)|Rest]) :-
    (   J0 \== none -> J = J0
    ;   Bs = [b(Next, _, _, _)|_] -> J = jmp(Next)
    ;   format(atom(M), 'in $~w: last block @~w has no jump', [Fn, L]),
        throw(nanofil_error(M))
    ),
    (   Bs == [] -> Rest = [] ; fallthrough(Bs, Fn, Rest) ).

op_name(Name, Op) :- memberchk(Name, [add, sub, mul, div, udiv, rem, urem, and, or,
                                      xor, sar, shr, shl, neg, copy, ptoi, itop]), !, Op = Name.
op_name(Name, cmp(Cond, K)) :-
    atom_chars(Name, ['c'|Cs]), append(CondCs, [KC], Cs),
    atom_chars(Cond, CondCs), atom_chars(K, [KC]),
    memberchk(K, [w, l]),
    memberchk(Cond, [eq, ne, sle, slt, sge, sgt, ule, ult, uge, ugt]), !.
op_name(Name, ext(T)) :-
    atom_concat(ext, TA, Name), memberchk(TA, [sw, uw, sh, uh, sb, ub]), !, T = TA.
op_name(loadw, load(sw)) :- !.
op_name(Name, load(T)) :-
    atom_concat(load, TA, Name), memberchk(TA, [l, sw, uw, sh, uh, sb, ub, p]), !, T = TA.
op_name(Name, alloc(N)) :-
    atom_concat(alloc, NA, Name), memberchk(NA-N, ['4'-4, '8'-8, '16'-16]).

data(Lk, data(Name, Lk, Align, Items)) -->
    [tok(id(data), _)], expect(glo(Name), 'data name'), expect(eq, '='),
    (   [tok(id(align), _)] -> expect(int(Align), 'alignment') ; { Align = 8 } ),
    nls, expect(lb, '{'), nls, data_items(Items), nls, expect(rb, '}').

data_items(Is) --> data_item(I0), !, { append(I0, Rest, Is) }, data_items_(Rest).
data_items([]) --> [].
data_items_(Is) --> nls, [tok(comma, _)], !, nls, data_item(I0), { append(I0, Rest, Is) }, data_items_(Rest).
data_items_([]) --> [].

data_item([zero(N)]) --> [tok(id(z), _)], !, expect(int(N), 'size').
data_item(Is) --> [tok(id(W), L)], { memberchk(W, [b, h, w, l]) }, !,
    data_vals(W, L, Is).

data_vals(W, L, [I|Is]) --> data_val(W, L, I), !, ( data_vals(W, L, Is) -> [] ; { Is = [] } ).

data_val(W, _, item(W, c(N))) --> [tok(int(N), _)], !.
data_val(b, _, item(b, str(Cs))) --> [tok(str(Cs), _)], !.
data_val(l, _, item(l, sym(S, Off))) --> [tok(glo(S), _)], !,
    (   [tok(plus, _)] -> expect(int(Off), 'offset') ; { Off = 0 } ).
data_val(W, L, _) --> [tok(T, _)], { T \== comma, T \== rb, T \== nl,
    fail_at(L, 'unsupported ~w data item ~w', [W, T]) }.

nls --> [tok(nl, _)], !, nls.
nls --> [].

expect(T, _) --> [tok(T, _)], !.
expect(_, What) --> [tok(T, L)], !, { fail_at(L, 'expected ~w, found ~w', [What, T]) }.
expect(_, What) --> { format(atom(M), 'expected ~w at end of input', [What]), throw(nanofil_error(M)) }.

fail_at(L, Fmt, Args) :-
    format(atom(M0), Fmt, Args),
    format(atom(M), 'line ~w: ~w', [L, M0]),
    throw(nanofil_error(M)).

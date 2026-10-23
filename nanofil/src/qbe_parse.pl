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

parse_qbe_file(File, Module) :-
    phrase_from_file(all_chars(Cs), File),
    parse_qbe_chars(Cs, Module).

all_chars([]) --> [].
all_chars([C|Cs]) --> [C], all_chars(Cs).

parse_qbe_chars(Cs, module(Items)) :-
    (   phrase(tokens(Tokens, 1), Cs) -> true
    ;   throw(nanofil_error('lexer failed'))
    ),
    (   phrase(items(Items), Tokens) -> true
    ;   throw(nanofil_error('parse failed'))
    ).

%% Lexer

% tokens(-Tokens, +Line): newlines are tokens, # comments and blanks are
% dropped.
tokens([tok(nl, Line)|Tokens], Line) -->
    [C], { C == '\n' }, !,
    { Line1 is Line + 1 },
    tokens(Tokens, Line1).
tokens(Tokens, Line) --> [C], { C == '#' }, !, skip_line, tokens(Tokens, Line).
tokens(Tokens, Line) --> [C], { blank(C) }, !, tokens(Tokens, Line).
tokens([tok(Token, Line)|Tokens], Line) --> token(Token), !, tokens(Tokens, Line).
tokens([], _) --> [].
tokens(_, Line) -->
    [C],
    { format(atom(Msg), 'line ~w: unexpected character ~q', [Line, C]),
      throw(nanofil_error(Msg)) }.

blank(' ').
blank('\t').
blank('\r').

% Skip to the end of the line, leaving the newline.
skip_line, [C] --> [C], { C == '\n' }, !.
skip_line --> [_], !, skip_line.
skip_line --> [].

token(tmp(N)) --> ['%'], !, name_chars(Cs), { Cs \== [], atom_chars(N, Cs) }.
token(glo(N)) --> ['$'], !, name_chars(Cs), { Cs \== [], atom_chars(N, Cs) }.
token(lbl(N)) --> ['@'], !, name_chars(Cs), { Cs \== [], atom_chars(N, Cs) }.
token(typ(N)) --> [':'], !, name_chars(Cs), { atom_chars(N, Cs) }.
token(str(Cs)) --> ['"'], !, str_chars(Cs).
token(int(N)) -->
    ['-'], digit(D), !, digits(Ds),
    { number_chars(Abs, [D|Ds]), N is -Abs }.
token(int(N)) --> digit(D), !, digits(Ds), { number_chars(N, [D|Ds]) }.
token(dots) --> ['.', '.', '.'], !.
token(id(A)) --> ident_start(C), !, name_chars(Cs), { atom_chars(A, [C|Cs]) }.
token(Punct) -->
    [C],
    { memberchk(C-Punct, ['='-eq, ','-comma, '('-lp, ')'-rp,
                          '{'-lb, '}'-rb, ('+')-plus]) }.

digit(D) --> [D], { decimal(D) }.

digits([D|Ds]) --> digit(D), !, digits(Ds).
digits([]) --> [].

ident_start(C) --> [C], { letter(C) ; C == '_' }.

name_chars([C|Cs]) --> [C], { name_char(C) }, !, name_chars(Cs).
name_chars([]) --> [].

name_char(C) :- letter(C) ; decimal(C).
name_char('_').
name_char('.').

% ASCII classes; char_type/2's differ between Prolog hosts.
decimal(D) :- D @>= '0', D @=< '9'.
letter(C) :- ( C @>= a, C @=< z -> true ; C @>= 'A', C @=< 'Z' ).

% Strings keep their escapes as written; QBE hands them to the assembler.
str_chars([]) --> ['"'], !.
str_chars(['\\', C|Cs]) --> ['\\', C], !, str_chars(Cs).
str_chars([C|Cs]) --> [C], str_chars(Cs).

%% Grammar: top level

items(Items) --> nls, top_items(Items).

top_items([Item|Items]) --> item(Item), !, nls, top_items(Items).
top_items([]) --> [].
top_items(_) -->
    [tok(T, Line)],
    { fail_at(Line, 'unexpected ~w at top level', [T]) }.

item(Func) --> linkage(Linkage), function(Linkage, Func).
item(Data) -->
    linkage(Linkage0),
    section(Linkage0, Linkage),
    data(Linkage, Data).
item(_) -->
    [tok(id(type), Line)],
    { fail_at(Line, 'aggregate types are not supported', []) }.

linkage(export) --> [tok(id(export), _)], !, nls.
linkage(local) --> [].

section(Linkage, ro(Linkage)) -->
    [tok(id(section), _), tok(str(['.', r, o, d, a, t, a]), _)], !,
    nls.
section(_, _) -->
    [tok(id(section), Line)], !,
    { fail_at(Line, 'only section \".rodata\" is supported', []) }.
section(Linkage, Linkage) --> [].

%% Grammar: functions

function(Linkage, func(Name, Linkage, Ret, Params, Blocks)) -->
    [tok(id(function), Line)],
    ret_class(Ret, Line),
    expect(glo(Name), 'function name'),
    expect(lp, '('),
    params(Params),
    expect(rp, ')'),
    nls,
    expect(lb, '{'),
    expect(nl, 'newline'),
    nls,
    raw_blocks(RawBlocks),
    expect(rb, '}'),
    { add_fallthrough_jumps(RawBlocks, Name, Blocks) }.

% No class before the function name means void; the name is pushed back.
ret_class(K, _) --> [tok(id(K), _)], { memberchk(K, [w, l, p]) }, !.
ret_class(tuple(Ks), _) --> [tok(lb, _)], !, word_classes(Ks), expect(rb, '}').
ret_class(void, _), [tok(glo(N), Line)] --> [tok(glo(N), Line)], !.
ret_class(_, Line) -->
    { fail_at(Line, 'only w, l and p return classes are supported', []) }.

params([]), [tok(rp, Line)] --> [tok(rp, Line)], !.
params([P|Ps]) --> param(P), more_params(Ps).

more_params([P|Ps]) --> [tok(comma, _)], !, param(P), more_params(Ps).
more_params([]) --> [].

param(par(K, t(N))) -->
    [tok(id(K), _)], { memberchk(K, [w, l, p]) }, !,
    expect(tmp(N), 'parameter').
param(_) --> [tok(T, Line)], { fail_at(Line, 'unsupported parameter ~w', [T]) }.

% Blocks as parsed: raw_blk(Label, Phis, Insts, MaybeJump), where
% MaybeJump is none when the block falls through.
raw_blocks([B|Bs]) --> raw_block(B), !, raw_blocks(Bs).
raw_blocks([]) --> [].

raw_block(raw_blk(Label, Phis, Insts, MaybeJump)) -->
    [tok(lbl(Label), _)],
    expect(nl, 'newline after label'),
    nls,
    phis(Phis),
    insts(Insts),
    maybe_jump(MaybeJump).

phis([P|Ps]) --> phi(P), !, nls, phis(Ps).
phis([]) --> [].

phi(phi(t(D), K, Incoming)) -->
    [tok(tmp(D), _), tok(eq, _), tok(id(K), _), tok(id(phi), _)],
    phi_args(Incoming),
    expect(nl, 'newline').

phi_args([Label-V|Incoming]) -->
    expect(lbl(Label), 'phi label'),
    value(V),
    (   [tok(comma, _)] -> phi_args(Incoming) ; { Incoming = [] } ).

insts([I|Is]) --> inst(I), !, nls, insts(Is).
insts([]) --> [].

inst(Inst) -->
    [tok(tmp(D), Line), tok(eq, _), tok(id(K), _)], !,
    {   memberchk(K, [w, l, p]) -> true
    ;   fail_at(Line, 'unsupported class ~w', [K])
    },
    def_rhs(t(D), K, Inst, Line),
    expect(nl, 'newline').
inst(store(W, V, Addr)) -->
    [tok(id(Op), _)], { store_op(Op, W) }, !,
    value(V),
    expect(comma, ','),
    value(Addr),
    expect(nl, 'newline').
inst(call(void, Callee, Args)) -->
    [tok(id(call), _)], !,
    call_rest(Callee, Args),
    expect(nl, 'newline').
% A tuple result: {%a, %b} ={l, p} call ...
inst(call(tuple(Tos), Callee, Args)) -->
    [tok(lb, Line)], !,
    tuple_temps(Ds),
    expect(rb, '}'),
    expect(eq, '='),
    expect(lb, '{'),
    word_classes(Ks),
    expect(rb, '}'),
    {   length(Ds, N), length(Ks, N) -> true
    ;   fail_at(Line, 'tuple arity mismatch', [])
    },
    { maplist(tuple_to, Ds, Ks, Tos) },
    expect(id(call), 'call'),
    call_rest(Callee, Args),
    expect(nl, 'newline').

tuple_to(D, K, to(t(D), K)).

tuple_temps([D|Ds]) -->
    expect(tmp(D), 'temporary'),
    (   [tok(comma, _)] -> tuple_temps(Ds) ; { Ds = [] } ).

word_classes([K|Ks]) -->
    [tok(id(K), Line)],
    {   memberchk(K, [l, p]) -> true
    ;   fail_at(Line, 'tuple words are l or p', [])
    },
    (   [tok(comma, _)] -> word_classes(Ks) ; { Ks = [] } ).

store_op(storeb, b).
store_op(storeh, h).
store_op(storew, w).
store_op(storel, l).
store_op(storep, p).

% def_rhs(+Dest, +Class, -Inst, +Line): what follows "%d =k".
def_rhs(D, K, call(to(D, K), Callee, Args), _) -->
    [tok(id(call), _)], !,
    call_rest(Callee, Args).
def_rhs(D, K, ins(D, K, Op, Args), Line) -->
    [tok(id(Name), _)],
    {   op_name(Name, Op) -> true
    ;   fail_at(Line, 'unsupported instruction ~w', [Name])
    },
    args(Args).

call_rest(Callee, Args) -->
    (   [tok(glo(F), _)] -> { Callee = glo(F) }
    ;   expect(tmp(T), 'callee'), { Callee = t(T) }
    ),
    expect(lp, '('),
    call_args(Args),
    expect(rp, ')').

call_args([]), [tok(rp, Line)] --> [tok(rp, Line)], !.
call_args([A|As]) --> call_arg(A), more_call_args(As).

more_call_args([A|As]) --> [tok(comma, _)], !, call_arg(A), more_call_args(As).
more_call_args([]) --> [].

call_arg(arg(K, V)) --> [tok(id(K), _)], { memberchk(K, [w, l, p]) }, !, value(V).
call_arg(_) -->
    [tok(T, Line)],
    { fail_at(Line, 'unsupported call argument ~w', [T]) }.

args([V|Vs]) --> value(V), !, more_args(Vs).
args([]) --> [].

more_args([V|Vs]) --> [tok(comma, _)], !, value(V), more_args(Vs).
more_args([]) --> [].

tuple_values([V|Vs]) -->
    value(V),
    (   [tok(comma, _)] -> tuple_values(Vs) ; { Vs = [] } ).

value(t(N)) --> [tok(tmp(N), _)], !.
value(c(N)) --> [tok(int(N), _)], !.
value(glo(N)) --> [tok(glo(N), _)], !.

maybe_jump(jmp(Label)) -->
    [tok(id(jmp), _)], !,
    expect(lbl(Label), 'label'),
    expect(nl, 'newline'),
    nls.
maybe_jump(jnz(V, IfTrue, IfFalse)) -->
    [tok(id(jnz), _)], !,
    value(V),
    expect(comma, ','),
    expect(lbl(IfTrue), 'label'),
    expect(comma, ','),
    expect(lbl(IfFalse), 'label'),
    expect(nl, 'newline'),
    nls.
maybe_jump(Ret) -->
    [tok(id(ret), _)], !,
    (   [tok(lb, _)] -> tuple_values(Vs), expect(rb, '}'), { Ret = rets(Vs) }
    ;   value(V) -> { Ret = ret(V) }
    ;   { Ret = ret }
    ),
    expect(nl, 'newline'),
    nls.
maybe_jump(hlt) --> [tok(id(hlt), _)], !, expect(nl, 'newline'), nls.
maybe_jump(none) --> [].

% add_fallthrough_jumps(+RawBlocks, +Fn, -Blocks): a block without a jump
% falls through to the next one; the last block must have a jump.
add_fallthrough_jumps([], Fn, []) :-
    format(atom(Msg), 'in $~w: no blocks', [Fn]),
    throw(nanofil_error(Msg)).
add_fallthrough_jumps([raw_blk(Label, Phis, Insts, MaybeJump)|RawBlocks], Fn,
                      [blk(Label, Phis, Insts, Jump)|Blocks]) :-
    (   MaybeJump \== none -> Jump = MaybeJump
    ;   RawBlocks = [raw_blk(Next, _, _, _)|_] -> Jump = jmp(Next)
    ;   format(atom(Msg), 'in $~w: last block @~w has no jump', [Fn, Label]),
        throw(nanofil_error(Msg))
    ),
    (   RawBlocks == [] -> Blocks = []
    ;   add_fallthrough_jumps(RawBlocks, Fn, Blocks)
    ).

% op_name(+Name, -Op): the IR operation an instruction name denotes.
op_name(Name, Op) :-
    memberchk(Name, [add, sub, mul, div, udiv, rem, urem, and, or,
                     xor, sar, shr, shl, neg, copy, ptoi, itop]), !,
    Op = Name.
op_name(Name, cmp(Cond, K)) :-
    atom_chars(Name, ['c'|Cs]),
    append(CondCs, [KC], Cs),
    atom_chars(Cond, CondCs),
    atom_chars(K, [KC]),
    memberchk(K, [w, l]),
    memberchk(Cond, [eq, ne, sle, slt, sge, sgt, ule, ult, uge, ugt]), !.
op_name(Name, ext(Type)) :-
    atom_concat(ext, Suffix, Name),
    memberchk(Suffix, [sw, uw, sh, uh, sb, ub]), !,
    Type = Suffix.
op_name(loadw, load(sw)) :- !.
op_name(Name, load(Type)) :-
    atom_concat(load, Suffix, Name),
    memberchk(Suffix, [l, sw, uw, sh, uh, sb, ub, p]), !,
    Type = Suffix.
op_name(Name, alloc(Align)) :-
    atom_concat(alloc, Suffix, Name),
    memberchk(Suffix-Align, ['4'-4, '8'-8, '16'-16]).

%% Grammar: data

data(Linkage, data(Name, Linkage, Align, Items)) -->
    [tok(id(data), _)],
    expect(glo(Name), 'data name'),
    expect(eq, '='),
    (   [tok(id(align), _)] -> expect(int(Align), 'alignment')
    ;   { Align = 8 }
    ),
    nls,
    expect(lb, '{'),
    nls,
    data_items(Items),
    nls,
    expect(rb, '}').

% A data item such as "w 1 2 3" stands for several IR items.
data_items(Items) -->
    data_item(Items0), !,
    { append(Items0, Rest, Items) },
    more_data_items(Rest).
data_items([]) --> [].

more_data_items(Items) -->
    nls, [tok(comma, _)], !, nls,
    data_item(Items0),
    { append(Items0, Rest, Items) },
    more_data_items(Rest).
more_data_items([]) --> [].

data_item([zero(N)]) --> [tok(id(z), _)], !, expect(int(N), 'size').
data_item(Items) -->
    [tok(id(W), Line)], { memberchk(W, [b, h, w, l, p]) }, !,
    data_values(W, Line, Items).

data_values(W, Line, [Item|Items]) -->
    data_value(W, Line, Item), !,
    (   data_values(W, Line, Items) -> [] ; { Items = [] } ).

data_value(W, _, item(W, c(N))) --> [tok(int(N), _)], !.
data_value(b, _, item(b, str(Cs))) --> [tok(str(Cs), _)], !.
data_value(W, _, item(W, sym(S, Off))) -->
    { memberchk(W, [l, p]) },
    [tok(glo(S), _)], !,
    (   [tok(plus, _)] -> expect(int(Off), 'offset') ; { Off = 0 } ).
data_value(W, Line, _) -->
    [tok(T, _)],
    { T \== comma, T \== rb, T \== nl,
      fail_at(Line, 'unsupported ~w data item ~w', [W, T]) }.

%% Helpers

nls --> [tok(nl, _)], !, nls.
nls --> [].

expect(T, _) --> [tok(T, _)], !.
expect(_, What) -->
    [tok(T, Line)], !,
    { fail_at(Line, 'expected ~w, found ~w', [What, T]) }.
expect(_, What) -->
    { format(atom(Msg), 'expected ~w at end of input', [What]),
      throw(nanofil_error(Msg)) }.

fail_at(Line, Format, Args) :-
    format(atom(Msg0), Format, Args),
    format(atom(Msg), 'line ~w: ~w', [Line, Msg0]),
    throw(nanofil_error(Msg)).

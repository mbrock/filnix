/*  C parser (milestone 4a): tokens from c_lex to a syntax tree.

    The only semantic state is the set of typedef names in scope, which
    the grammar needs to tell declarations from expressions. Types,
    constants and tags are resolved later, in c_sema.

    Translation unit: a list of
      decl(Loc, Specs, [init(Dcl, Init)])       Init is none, an expression
                                                or list(Entries)
      fundef(Loc, Specs, Dcl, Body)
      static_assert(Loc, Expr, Message)
    Dcl = dcl(Name, Type, Asm): Name is none in abstract declarators, Asm
    is asm(Symbol) or none. Type is a declarator type built around the
    atom base, which stands for the type the Specs give:
      base | ptr(T, Quals) | array(T, Size) | func(T, Params)
      Size: none or an expression. Params: unspecified, or
      params([param(Specs, Dcl)], fixed | variadic)
    Specs: storage(S), tspec(K), qual(Q), fspec(F), tname(Name),
      su(struct | union, Tag, Members, Attrs), enum(Tag, Enumerators),
      attr(Tokens), alignas(type(Specs, Type) | expr(E)), typeof(...)
      Members: none or [field(Specs, Dcl, Width)], Width none or an
      expression; Enumerators: none or [enumerator(Name, Expr | none)].
    Statements are at(Loc, S), S one of
      block(Items) expr(E) null if(C, T, E) while(C, S) do(S, C)
      for(Init, C, Step, S) switch(E, S) case(E, S) default(S)
      break continue return(E | none) goto(L) label(L, S)
      Block items are statements or decl/static_assert terms; Init is
      none, expr(E) or a decl term; C and Step may be none.
    Expressions: id(N) num(V, Suffix) chr(V) str(Bytes) float(Chars)
      wstr(ElemType, Codes) (wide string)
      bin(Op, A, B) assign(Op, A, B) (Op = for plain assignment)
      un(Op, A) for neg plus bnot not deref addr preinc predec postinc
      postdec; cond(C, A, B) gcond(C, B) (GNU C ?: B) comma(A, B) call(F, Args) index(A, I)
      member(A, F) arrow(A, F) cast(TypeName, E) sizeof_type(TypeName)
      sizeof_expr(E) alignof(TypeName) complit(TypeName, Init)
      offsetof(TypeName, Path)
    TypeName = type(Specs, Type).
*/
:- module(c_parse, [c_parse/2]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(assoc)).

c_parse(Ts, Items) :-
    list_to_assoc(['__builtin_va_list'-t], Env),
    phrase(unit(Env, Items), Ts).

unit(_, []) --> eos, !.
unit(Env0, Is) --> ext_decl(Env0, Env, I), !,
    { I == none -> Is = Is1 ; Is = [I|Is1] }, unit(Env, Is1).
unit(_, _) --> err('expected a declaration').

eos([], []).

%% Tokens

t(T) --> [tok(T, _)].
p(P) --> [tok(p(P), _)].
k(K) --> [tok(kw(K), _)].

peek(T), [tok(T, L)] --> [tok(T, L)].
loc(L), [tok(T, L)] --> [tok(T, L)].
loc(eof) --> eos.

expect(P) --> p(P), !.
expect(P) --> { format(atom(M), 'expected ~w', [P]) }, err(M).

err(Msg), [tok(T, L)] --> [tok(T, L)], !,
    { tok_text(T, X), format(atom(M), '~w: ~w, at ~w', [L, Msg, X]), throw(nanofil_error(M)) }.
err(Msg) --> { format(atom(M), 'end of input: ~w', [Msg]), throw(nanofil_error(M)) }.

tok_text(p(P), P) :- !.
tok_text(kw(K), K) :- !.
tok_text(id(N), N) :- !.
tok_text(T, T).

%% External declarations

ext_decl(Env, Env, none) --> p(';'), !.
ext_decl(Env0, Env, I) --> k(extension), !, ext_decl(Env0, Env, I).
ext_decl(Env, Env, I) --> loc(L), k(static_assert), !, static_assert_rest(Env, L, I).
ext_decl(_, _, _) --> k(asm), !, err('top-level asm is not supported').
ext_decl(Env0, Env, I) -->
    loc(L), decl_specs(Env0, Ss), !,
    (   p(';') -> { I = decl(L, Ss, []), Env = Env0 }
    ;   full_declarator(Env0, D, As0),
        (   { D = dcl(Name, func(_, Ps), _) }, peek(p('{'))
        ->  { del_names([Name], Env0, Env), params_env(Ps, Env, BEnv) },
            block(BEnv, Body),
            { append(Ss, As0, Ss1), I = fundef(L, Ss1, D, Body) }
        ;   init_rest(Env0, D, Ds, As0, As), expect(';'),
            { append(Ss, As, Ss1), I = decl(L, Ss1, Ds), decl_env(Ss, Ds, Env0, Env) }
        )
    ).

static_assert_rest(Env, L, static_assert(L, E, Msg)) -->
    expect('('), cond(Env, E),
    ( p(',') -> strs(Msg) ; { Msg = [] } ),
    expect(')'), expect(';').

% The typedef names a declaration adds or (for ordinary names) hides.
decl_env(Ss, Ds, Env0, Env) :-
    findall(N, ( member(init(dcl(N, _, _), _), Ds), N \== none ), Ns),
    (   memberchk(storage(typedef), Ss)
    ->  foldl(add_name, Ns, Env0, Env)
    ;   del_names(Ns, Env0, Env)
    ).

add_name(N, E0, E) :- put_assoc(N, E0, t, E).
del_names(Ns, E0, E) :- foldl(del_name, Ns, E0, E).
del_name(N, E0, E) :- ( del_assoc(N, E0, _, E1) -> E = E1 ; E = E0 ).

params_env(params(Ps, _), E0, E) :- !,
    findall(N, ( member(param(_, dcl(N, _, _)), Ps), N \== none ), Ns),
    del_names(Ns, E0, E).
params_env(_, E, E).

% init_rest(Env, D, Inits, As0, As): the declarators' attributes are
% collected into As and apply to the whole declaration.
init_rest(Env, D, [init(D, I)|Ds], As0, As) -->
    ( p('=') -> initializer(Env, I) ; { I = none } ),
    (   p(',') -> full_declarator(Env, D1, As1), { append(As0, As1, As2) }, init_rest(Env, D1, Ds, As2, As)
    ;   { Ds = [], As = As0 }
    ).

%% Declaration specifiers

decl_specs(Env, Ss) --> specs(Env, no, Ss), { Ss \== [] }.

specs(Env, Seen, [S|Ss]) --> spec(Env, Seen, S), !,
    { type_spec(S) -> Seen1 = yes ; Seen1 = Seen }, specs(Env, Seen1, Ss).
specs(_, _, []) --> [].

type_spec(tspec(_)). type_spec(tname(_)). type_spec(su(_, _, _, _)).
type_spec(enum(_, _)). type_spec(typeof(_)).

spec(_, _, storage(S)) --> k(S), { memberchk(S, [typedef, extern, static, auto, register, thread_local]) }, !.
spec(_, _, tspec(K)) --> k(K), { memberchk(K, [void, char, short, int, long, float, double, signed,
                                              unsigned, bool, complex, int128]) }, !.
spec(_, _, _) --> k(atomic), p('('), !, err('_Atomic types are not supported').
spec(_, _, qual(Q)) --> k(Q), { memberchk(Q, [const, volatile, restrict, atomic]) }, !.
spec(_, _, fspec(F)) --> k(F), { memberchk(F, [inline, noreturn]) }, !.
spec(_, _, attr(A)) --> gnu_attr(A), !.
spec(_, _, attr(extension)) --> k(extension), !.
spec(Env, _, alignas(A)) --> k(alignas), !, expect('('),
    ( type_name(Env, T) -> { A = type(T) } ; cond(Env, E), { A = expr(E) } ), expect(')').
spec(Env, _, S) --> k(K), { memberchk(K, [struct, union]) }, !, su_spec(Env, K, S).
spec(Env, _, S) --> k(enum), !, enum_spec(Env, S).
spec(Env, _, typeof(A)) --> k(typeof), !, expect('('),
    ( type_name(Env, T) -> { A = type(T) } ; expr(Env, E), { A = expr(E) } ), expect(')').
spec(Env, no, tname(N)) --> t(id(N)), { get_assoc(N, Env, t) }.

gnu_attr(A) --> k(attribute), expect('('), balanced(A0), { A = A0 }.

% balanced(Toks): tokens up to the ')' matching an already-consumed '('.
balanced([]) --> p(')'), !.
balanced([T|Ts]) --> [tok(p('('), _)], !, balanced(Inner), { T = group(Inner) }, balanced(Ts).
balanced([T|Ts]) --> [tok(T, _)], !, balanced(Ts).
balanced(_) --> err('unbalanced parentheses').

attrs --> gnu_attr(_), !, attrs.
attrs --> [].

su_spec(Env, K, su(K, Tag, Ms, As)) -->
    attr_list(As0),
    ( t(id(Tag0)) -> { Tag = Tag0 } ; { Tag = none } ),
    (   p('{') -> members(Env, Ms), attr_list(As1)
    ;   { Tag \== none, Ms = none, As1 = [] }
    ),
    { append(As0, As1, As) }.

attr_list([A|As]) --> gnu_attr(A), !, attr_list(As).
attr_list([]) --> [].

members(_, []) --> p('}'), !.
members(Env, Ms) --> p(';'), !, members(Env, Ms).
members(Env, [static_assert(L, E, M)|Ms]) --> loc(L), k(static_assert), !,
    expect('('), cond(Env, E), ( p(',') -> strs(M) ; { M = [] } ), expect(')'), expect(';'),
    members(Env, Ms).
members(Env, Ms) --> decl_specs(Env, Ss), !,
    (   p(';') -> { Ms = [field(Ss, dcl(none, base, none), none)|Ms1] }
    ;   field_decls(Env, Ss, Ms, Ms1), expect(';')
    ),
    members(Env, Ms1).
members(_, _) --> err('expected a member declaration').

field_decls(Env, Ss, [field(FSs, D, W)|Ms], Ms0) -->
    (   p(':') -> { D = dcl(none, base, none), As = [] }, cond(Env, W)
    ;   full_declarator(Env, D, As), ( p(':') -> cond(Env, W) ; { W = none } )
    ),
    attr_list(As1),
    { findall(attr(X), member(X, As1), As2), append([Ss, As, As2], FSs) },
    ( p(',') -> field_decls(Env, Ss, Ms, Ms0) ; { Ms = Ms0 } ).

enum_spec(Env, enum(Tag, Es)) -->
    attrs,
    ( t(id(Tag0)) -> { Tag = Tag0 } ; { Tag = none } ),
    (   p('{') -> enumerators(Env, Es)
    ;   { Tag \== none, Es = none }
    ),
    attrs.

enumerators(_, []) --> p('}'), !.
enumerators(Env, [enumerator(N, V)|Es]) -->
    t(id(N)), !, attrs,
    ( p('=') -> cond(Env, V0), { V = V0 } ; { V = none } ),
    ( p(',') -> enumerators(Env, Es) ; expect('}'), { Es = [] } ).
enumerators(_, _) --> err('expected an enumerator').

%% Declarators. declarator(Env, Name, Type, Base) builds Type around Base.

% Attributes after a declarator come back as attr(Tokens) specifiers.
full_declarator(Env, dcl(N, T, Asm), As) --> declarator(Env, N, T, base), gnu_suffix(Asm, As).

gnu_suffix(Asm, As) -->
    attr_list(As0),
    ( k(asm) -> expect('('), strs(Bs), expect(')'), { atom_codes(A, Bs), Asm = asm(A) } ; { Asm = none } ),
    attr_list(As1),
    { append(As0, As1, As2), findall(attr(X), member(X, As2), As) }.

declarator(Env, N, T, B) --> p('*'), !, quals(Qs), declarator(Env, N, T, ptr(B, Qs)).
declarator(Env, N, T, B) --> attrs, direct(Env, N, T, B).

direct(Env, N, T, B) --> t(id(N)), !, suffixes(Env, B, T).
direct(Env, N, T, B) --> p('('), declarator(Env, N, T, Mid), expect(')'), suffixes(Env, B, Mid).

quals(Qs) --> k(Q), { memberchk(Q, [const, volatile, restrict, atomic]) }, !, { Qs = [Q|Qs1] }, quals(Qs1).
quals(Qs) --> gnu_attr(_), !, quals(Qs).
quals([]) --> [].

abstract(Env, T, B) --> p('*'), !, quals(Qs), abstract(Env, T, ptr(B, Qs)).
abstract(Env, T, B) --> [tok(p('('), _)], peek(p('*')), !,
    abstract(Env, T, Mid), expect(')'), suffixes(Env, B, Mid).
abstract(Env, T, B) --> suffixes(Env, B, T).

suffixes(Env, B, T) --> p('['), !, array_size(Env, S), expect(']'), suffixes(Env, B, T1), { T = array(T1, S) }.
suffixes(Env, B, T) --> p('('), !, params(Env, Ps), suffixes(Env, B, T1), { T = func(T1, Ps) }.
suffixes(_, B, B) --> [].

array_size(_, none), [tok(p(']'), L)] --> [tok(p(']'), L)], !.
array_size(_, _) --> p('*'), peek(p(']')), !, err('variable length arrays are not supported').
array_size(Env, S) --> k(static), !, array_size(Env, S).
array_size(Env, S) --> k(Q), { memberchk(Q, [const, volatile, restrict]) }, !, array_size(Env, S).
array_size(Env, S) --> assign(Env, S).

params(_, unspecified) --> p(')'), !.
params(_, params([], fixed)) --> k(void), p(')'), !.
params(Env, params(Ps, V)) --> param_list(Env, Ps, V), expect(')').

param_list(_, [], variadic) --> p('...'), !.
param_list(Env, [P|Ps], V) --> param(Env, P), ( p(',') -> param_list(Env, Ps, V) ; { Ps = [], V = fixed } ).

param(Env, param(Ss, dcl(N, T, none))) -->
    decl_specs(Env, Ss), !,
    (   declarator(Env, N, T, base) -> []
    ;   abstract(Env, T, base), { N = none }
    ),
    attrs.
param(_, _) --> t(id(_)), !, err('K&R-style parameter lists are not supported').
param(_, _) --> err('expected a parameter declaration').

type_name(Env, type(Ss, T)) --> decl_specs(Env, Ss), abstract(Env, T, base).

starts_type(Env), [tok(X, L)] --> [tok(X, L)],
    {   X = kw(K) -> memberchk(K, [void, char, short, int, long, float, double, signed, unsigned, bool,
                                   complex, int128, struct, union, enum, const, volatile, restrict,
                                   atomic, typeof, attribute, alignas, extension])
    ;   X = id(N), get_assoc(N, Env, t)
    }.

%% Initializers

initializer(Env, list(Es)) --> p('{'), !, init_entries(Env, Es).
initializer(Env, E) --> assign(Env, E).

init_entries(_, []) --> p('}'), !.
init_entries(Env, [entry(Ds, I)|Es]) -->
    ( designators(Env, Ds0), { Ds0 \== [] } -> expect('='), { Ds = Ds0 } ; { Ds = [] } ),
    initializer(Env, I),
    ( p(',') -> init_entries(Env, Es) ; expect('}'), { Es = [] } ).

designators(Env, [D|Ds]) --> designator(Env, D), !, designators(Env, Ds).
designators(_, []) --> [].

designator(_, field(N)) --> p('.'), t(id(N)).
designator(Env, index(E)) --> p('['), cond(Env, E), ( p('...') -> err('GNU range designators are not supported') ; expect(']') ).

%% Statements

block(Env, at(L, block(Items))) --> loc(L), p('{'), block_items(Env, Items).

block_items(_, []) --> p('}'), !.
block_items(Env0, [I|Is]) --> block_item(Env0, Env, I), block_items(Env, Is).

block_item(Env, Env, I) --> loc(L), k(static_assert), !, static_assert_rest(Env, L, I).
block_item(Env0, Env, I) --> starts_decl(Env0), !, local_decl(Env0, Env, I).
block_item(Env, Env, S) --> stmt(Env, S).

% Lookahead only: the next tokens begin a declaration, not a label.
starts_decl(Env, S, S) :-
    \+ phrase(label_start, S, _),
    (   phrase(starts_type(Env), S, _) -> true
    ;   S = [tok(kw(K), _)|_],
        memberchk(K, [typedef, extern, static, auto, register, thread_local, inline, noreturn])
    ).

label_start, [A, B] --> [A, B], { A = tok(id(_), _), B = tok(p(':'), _) }.

local_decl(Env0, Env, decl(L, Ss1, Ds)) -->
    loc(L), decl_specs(Env0, Ss),
    (   p(';') -> { Ds = [], As = [] }
    ;   full_declarator(Env0, D, As0), init_rest(Env0, D, Ds, As0, As), expect(';')
    ),
    { append(Ss, As, Ss1), decl_env(Ss, Ds, Env0, Env) }.

stmt(Env, at(L, S)) --> loc(L), stmt_(Env, S), !.
stmt(_, _) --> err('expected a statement').

stmt_(Env, S) --> peek(p('{')), !, block(Env, at(_, S)).
stmt_(_, null) --> p(';'), !.
stmt_(Env, if(C, T, E)) --> k(if), !, expect('('), expr(Env, C), expect(')'), stmt(Env, T),
    ( k(else) -> stmt(Env, E0), { E = E0 } ; { E = none } ).
stmt_(Env, while(C, S)) --> k(while), !, expect('('), expr(Env, C), expect(')'), stmt(Env, S).
stmt_(Env, do(S, C)) --> k(do), !, stmt(Env, S), ( k(while) -> [] ; err('expected while') ),
    expect('('), expr(Env, C), expect(')'), expect(';').
stmt_(Env, for(I, C, St, S)) --> k(for), !, expect('('),
    (   starts_decl(Env) -> local_decl(Env, Env1, I)
    ;   opt_expr(Env, E0), expect(';'), { Env1 = Env, ( E0 == none -> I = none ; I = expr(E0) ) }
    ),
    opt_expr(Env1, C), expect(';'), opt_expr(Env1, St), expect(')'), stmt(Env1, S).
stmt_(Env, switch(E, S)) --> k(switch), !, expect('('), expr(Env, E), expect(')'), stmt(Env, S).
stmt_(Env, case(E, S)) --> k(case), !, cond(Env, E),
    ( p('...') -> err('GNU case ranges are not supported') ; expect(':') ), stmt(Env, S).
stmt_(Env, default(S)) --> k(default), !, expect(':'), stmt(Env, S).
stmt_(_, break) --> k(break), !, expect(';').
stmt_(_, continue) --> k(continue), !, expect(';').
stmt_(Env, return(E)) --> k(return), !, opt_expr(Env, E), expect(';').
stmt_(_, goto(N)) --> k(goto), !, ( t(id(N0)) -> { N = N0 } ; err('computed goto is not supported') ), expect(';').
stmt_(_, _) --> k(asm), !, err('inline asm is not supported').
stmt_(Env, label(N, S)) --> label_start, !, [tok(id(N), _), _], stmt(Env, S).
stmt_(Env, expr(E)) --> expr(Env, E), expect(';').

opt_expr(_, none), [tok(p(P), L)] --> [tok(p(P), L)], { memberchk(P, [';', ')']) }, !.
opt_expr(Env, E) --> expr(Env, E).

%% Expressions

expr(Env, E) --> assign(Env, E0), ( p(',') -> expr(Env, E1), { E = comma(E0, E1) } ; { E = E0 } ).

assign(Env, E) --> cond(Env, L),
    ( p(Op), { assign_op(Op) } -> assign(Env, R), { E = assign(Op, L, R) } ; { E = L } ).

assign_op('='). assign_op('*='). assign_op('/='). assign_op('%='). assign_op('+=').
assign_op('-='). assign_op('<<='). assign_op('>>='). assign_op('&='). assign_op('^=').
assign_op('|=').

cond(Env, E) --> bin(Env, 1, C),
    (   p('?') -> ( p(':') -> cond(Env, B), { E = gcond(C, B) }
                   ; expr(Env, A), expect(':'), cond(Env, B), { E = cond(C, A, B) } )
    ;   { E = C }
    ).

bin(Env, 11, E) --> !, cast(Env, E).
bin(Env, N, E) --> { N1 is N + 1 }, bin(Env, N1, L), bin_rest(Env, N, L, E).

bin_rest(Env, N, L, E) --> p(P), { binop(P, N, Op) }, !,
    { N1 is N + 1 }, bin(Env, N1, R), bin_rest(Env, N, bin(Op, L, R), E).
bin_rest(_, _, E, E) --> [].

binop('||', 1, lor). binop('&&', 2, land). binop('|', 3, or). binop('^', 4, xor).
binop('&', 5, and). binop('==', 6, eq). binop('!=', 6, ne).
binop('<', 7, lt). binop('>', 7, gt). binop('<=', 7, le). binop('>=', 7, ge).
binop('<<', 8, shl). binop('>>', 8, shr). binop('+', 9, add). binop('-', 9, sub).
binop('*', 10, mul). binop('/', 10, div). binop('%', 10, mod).

cast(Env, E) --> [tok(p('('), _)], starts_type(Env), !, type_name(Env, T), expect(')'),
    (   p('{') -> init_entries(Env, Es), postfix(Env, complit(T, list(Es)), E)
    ;   cast(Env, E0), { E = cast(T, E0) }
    ).
cast(Env, E) --> unary(Env, E).

unary(Env, un(preinc, E)) --> p('++'), !, unary(Env, E).
unary(Env, un(predec, E)) --> p('--'), !, unary(Env, E).
unary(Env, un(Op, E)) --> p(P), { unop(P, Op) }, !, cast(Env, E).
unary(Env, E) --> k(sizeof), !,
    (   [tok(p('('), _)], starts_type(Env) -> type_name(Env, T), expect(')'), { E = sizeof_type(T) }
    ;   unary(Env, E0), { E = sizeof_expr(E0) }
    ).
unary(Env, alignof(T)) --> k(alignof), !, expect('('), type_name(Env, T), expect(')').
unary(Env, E) --> k(extension), !, cast(Env, E).
unary(_, _) --> p('&&'), !, err('label addresses are not supported').
unary(Env, E) --> primary(Env, P), postfix(Env, P, E).

unop('&', addr). unop('*', deref). unop('+', plus). unop('-', neg).
unop('~', bnot). unop('!', not).

postfix(Env, A, E) --> p('['), !, expr(Env, I), expect(']'), postfix(Env, index(A, I), E).
postfix(Env, A, E) --> p('('), !, args(Env, As), postfix(Env, call(A, As), E).
postfix(Env, A, E) --> p('.'), !, field_name(F), postfix(Env, member(A, F), E).
postfix(Env, A, E) --> p('->'), !, field_name(F), postfix(Env, arrow(A, F), E).
postfix(Env, A, E) --> p('++'), !, postfix(Env, un(postinc, A), E).
postfix(Env, A, E) --> p('--'), !, postfix(Env, un(postdec, A), E).
postfix(_, E, E) --> [].

field_name(F) --> t(id(F)), !.
field_name(_) --> err('expected a member name').

args(_, []) --> p(')'), !.
args(Env, [A|As]) --> assign(Env, A), ( p(',') -> args(Env, As) ; expect(')'), { As = [] } ).

primary(Env, offsetof(T, Path)) --> t(id('__builtin_offsetof')), !,
    expect('('), type_name(Env, T), expect(','), field_name(F), offsetof_path(Env, Ps), expect(')'),
    { Path = [field(F)|Ps] }.
primary(_, _) --> t(id(N)), { memberchk(N, ['__builtin_va_arg', '__builtin_va_start', '__builtin_va_end',
                                            '__builtin_va_copy', '__builtin_types_compatible_p']) }, !,
    { format(atom(M), '~w is not supported', [N]) }, err(M).
primary(_, id(N)) --> t(id(N)), !.
primary(_, num(V, S)) --> t(int(V, S)), !.
primary(_, float(Cs)) --> t(float(Cs)), !.
primary(_, chr(V)) --> t(chr(V)), !.
primary(_, S) --> ( peek(str(_)) ; peek(wstr(_, _)) ), !, lit_strs(Ps), { concat_strs(Ps, S) }.
primary(_, _) --> p('('), peek(p('{')), !, err('statement expressions are not supported').
primary(_, _) --> k(generic), !, err('_Generic is not supported').
primary(Env, E) --> p('('), !, expr(Env, E), expect(')').
primary(_, _) --> err('expected an expression').

offsetof_path(Env, [field(F)|Ps]) --> p('.'), !, field_name(F), offsetof_path(Env, Ps).
offsetof_path(Env, [index(E)|Ps]) --> p('['), !, expr(Env, E), expect(']'), offsetof_path(Env, Ps).
offsetof_path(_, []) --> [].

% Adjacent string literals concatenate; if one is wide, all are, and a
% plain one's bytes become elements (exact for ASCII).
lit_strs([S|Ss]) --> ( t(str(B)) -> { S = str(B) } ; t(wstr(T, Vs)) -> { S = wstr(T, Vs) } ; { fail } ), !,
    ( lit_strs(Ss) -> [] ; { Ss = [] } ).

strs(Bs) --> t(str(B0)), !, ( strs(B1) -> { append(B0, B1, Bs) } ; { Bs = B0 } ).

concat_strs(Ps, S) :-
    findall(T, member(wstr(T, _), Ps), Ts0), sort(Ts0, Ts),
    findall(Vs, ( member(P, Ps), ( P = str(Vs) ; P = wstr(_, Vs) ) ), Vss), append(Vss, All),
    (   Ts == [] -> S = str(All)
    ;   Ts = [T] -> S = wstr(T, All)
    ;   throw(nanofil_error('concatenating string literals of different wide types'))
    ).

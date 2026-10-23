/*  C parser (milestone 4a): tokens from c_lex to a syntax tree.

    The only semantic state is the set of typedef names in scope, which
    the grammar needs to tell declarations from expressions; it is the
    assoc Env (name to t) threaded through the nonterminals. Types,
    constants and tags are resolved later, in c_types and c_lower.

    Translation unit: a list of
      decl(Loc, Specs, [init(Dcl, Init)])       Init is none, an expression
                                                or list(Entries)
      fundef(Loc, Specs, Dcl, Body)
      static_assert(Loc, Expr, Message)
    Entries: [entry(Designators, Init)], each designator field(Name) or
    index(Expr).
    Dcl = dcl(Name, Type, Asm): Name is some(Identifier), or none in
    abstract declarators; Asm is asm(Symbol) or none. Type is a declarator type built around the
    atom base, which stands for the type the Specs give:
      base | ptr(T, Quals) | array(T, Size) | func(T, Params)
      Size: none or an expression. Params: unspecified, or
      params([param(Specs, Dcl)], fixed | variadic)
    Specs: storage(S), tspec(K), qual(Q), fspec(F), tname(Name),
      su(struct | union, Tag, Members, Attrs), enum(Tag, Enumerators),
      Tag some(Identifier) or none, attr(Tokens), alignas(type(TypeName) | expr(E)), typeof(...)
      Members: none or [field(Specs, Dcl, Width)] (and static_assert
      terms), Width none or an expression; Enumerators: none or
      [enumerator(Name, Expr | none)].
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
      postdec; cond(C, A, B) gcond(C, B) (GNU C ?: B) comma(A, B)
      call(F, Args) index(A, I) member(A, F) arrow(A, F)
      cast(TypeName, E) sizeof_type(TypeName) sizeof_expr(E)
      alignof(TypeName) complit(TypeName, Init) offsetof(TypeName, Path)
    TypeName = type(Specs, Type).
*/
:- module(c_parse, [c_parse/2]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(assoc)).

%! c_parse(+Tokens, -Items) is det.
%
%  Items is the translation unit of the c_lex Tokens, as described above.
%  Throws nanofil_error/1 on a syntax error or unsupported construct.
c_parse(Tokens, Items) :-
    list_to_assoc(['__builtin_va_list'-t], Env),
    phrase(unit(Env, Items), Tokens).

% unit(+Env, -Items)//: the external declarations up to the end of input.
% The cut commits to the first parse of each declaration.
unit(_, []) --> eos, !.
unit(Env0, Items) -->
    external_decl(Env0, Env, Items, Items1), !,
    unit(Env, Items1).
unit(_, _) --> parse_error('expected a declaration').

eos([], []).

%% Tokens

token(T) --> [tok(T, _)].
punct(P) --> [tok(p(P), _)].
kw(K) --> [tok(kw(K), _)].

% Lookahead: the next token, left in the input.
peek(T), [tok(T, Loc)] --> [tok(T, Loc)].

% The next token's location, or eof.
loc(Loc), [tok(T, Loc)] --> [tok(T, Loc)].
loc(eof) --> eos.

% expect(+P)//: the punctuator P, or a syntax error.
expect(P) --> punct(P), !.
expect(P) --> { format(atom(Msg), 'expected ~w', [P]) }, parse_error(Msg).

% parse_error(+Msg)//: throw a syntax error at the next token.
parse_error(Msg), [tok(T, Loc)] -->
    [tok(T, Loc)], !,
    {   token_text(T, Text),
        format(atom(M), '~w: ~w, at ~w', [Loc, Msg, Text]),
        throw(nanofil_error(M))
    }.
parse_error(Msg) -->
    {   format(atom(M), 'end of input: ~w', [Msg]),
        throw(nanofil_error(M))
    }.

% token_text(+T, -Text): Text shows the c_lex token T in a message.
token_text(p(P), P).
token_text(kw(K), K).
token_text(id(N), N).
token_text(int(V, S), int(V, S)).
token_text(float(Cs), float(Cs)).
token_text(chr(V), chr(V)).
token_text(str(Bs), str(Bs)).
token_text(wstr(T, Vs), wstr(T, Vs)).

%% External declarations

% external_decl(+Env0, -Env, -Items, ?Items1)//: one external
% declaration; Items is Items1 with its item in front, or Items1 itself
% for a stray ';'. Env is Env0 with its typedef names.
external_decl(Env, Env, Items, Items) --> punct(';'), !.
external_decl(Env0, Env, Items, Items1) -->
    kw(extension), !,
    external_decl(Env0, Env, Items, Items1).
external_decl(Env, Env, [Item|Items], Items) -->
    loc(Loc),
    kw(static_assert), !,
    static_assert_rest(Env, Loc, Item).
external_decl(_, _, _, _) -->
    kw(asm), !,
    parse_error('top-level asm is not supported').
external_decl(Env0, Env, [Item|Items], Items) -->
    loc(Loc),
    decl_specs(Env0, Specs), !,
    (   punct(';')
    ->  { Item = decl(Loc, Specs, []), Env = Env0 }
    ;   full_declarator(Env0, Dcl, Attrs0),
        (   { Dcl = dcl(some(Name), func(_, Params), _) }, peek(p('{'))
        ->  {   typedefs_hidden([Name], Env0, Env),
                params_env(Params, Env, BodyEnv)
            },
            block(BodyEnv, Body),
            {   append(Specs, Attrs0, Specs1),
                Item = fundef(Loc, Specs1, Dcl, Body)
            }
        ;   init_declarators(Env0, Dcl, Inits, Attrs0, Attrs),
            expect(';'),
            {   append(Specs, Attrs, Specs1),
                Item = decl(Loc, Specs1, Inits),
                decl_env(Specs, Inits, Env0, Env)
            }
        )
    ).

% static_assert_rest(+Env, +Loc, -Item)//: a _Static_assert after its
% keyword.
static_assert_rest(Env, Loc, static_assert(Loc, Expr, Msg)) -->
    expect('('),
    conditional(Env, Expr),
    ( punct(',') -> string_bytes(Msg) ; { Msg = [] } ),
    expect(')'),
    expect(';').

% decl_env(+Specs, +Inits, +Env0, -Env): Env is Env0 with the typedef
% names the declaration adds or (for ordinary names) hides.
decl_env(Specs, Inits, Env0, Env) :-
    findall(N, member(init(dcl(some(N), _, _), _), Inits), Names),
    (   memberchk(storage(typedef), Specs)
    ->  foldl(typedef_declared, Names, Env0, Env)
    ;   typedefs_hidden(Names, Env0, Env)
    ).

% typedef_declared(+Name, +Env0, -Env): Env is Env0 with typedef Name.
typedef_declared(Name, Env0, Env) :- put_assoc(Name, Env0, t, Env).

% typedefs_hidden(+Names, +Env0, -Env): Env is Env0 where none of Names
% is a typedef name; typedef_hidden/3 is the same for one Name.
typedefs_hidden(Names, Env0, Env) :- foldl(typedef_hidden, Names, Env0, Env).

typedef_hidden(Name, Env0, Env) :-
    ( del_assoc(Name, Env0, _, Env1) -> Env = Env1 ; Env = Env0 ).

% params_env(+Params, +Env0, -Env): Env is Env0 for a function body,
% where parameter names hide typedefs.
params_env(params(Params, _), Env0, Env) :-
    findall(N, member(param(_, dcl(some(N), _, _)), Params), Names),
    typedefs_hidden(Names, Env0, Env).
params_env(unspecified, Env, Env).

% init_declarators(+Env, +Dcl, -Inits, +Attrs0, -Attrs)//: Inits are the
% init(Dcl, Init) of the declarator list whose first declarator Dcl is
% already read. The declarators' attributes are collected into Attrs
% and apply to the whole declaration.
init_declarators(Env, Dcl, [init(Dcl, Init)|Inits], Attrs0, Attrs) -->
    ( punct('=') -> initializer(Env, Init) ; { Init = none } ),
    (   punct(',')
    ->  full_declarator(Env, Dcl1, Attrs1),
        { append(Attrs0, Attrs1, Attrs2) },
        init_declarators(Env, Dcl1, Inits, Attrs2, Attrs)
    ;   { Inits = [], Attrs = Attrs0 }
    ).

%% Declaration specifiers

% decl_specs(+Env, -Specs)//: nonempty declaration specifiers.
decl_specs(Env, Specs) -->
    specifiers(Env, no, Specs),
    { Specs \== [] }.

% specifiers(+Env, +TypeSeen, -Specs)//: once a type specifier is seen, an
% identifier is the declarator, not a typedef name.
specifiers(Env, TypeSeen, [Spec|Specs]) -->
    specifier(Env, TypeSeen, Spec), !,
    { spec_type_seen(Spec, TypeSeen, TypeSeen1) },
    specifiers(Env, TypeSeen1, Specs).
specifiers(_, _, []) --> [].

% spec_type_seen(+Spec, +TypeSeen0, -TypeSeen): TypeSeen is yes if Spec
% is a type specifier, else TypeSeen0.
spec_type_seen(storage(_), TypeSeen, TypeSeen).
spec_type_seen(tspec(_), _, yes).
spec_type_seen(qual(_), TypeSeen, TypeSeen).
spec_type_seen(fspec(_), TypeSeen, TypeSeen).
spec_type_seen(attr(_), TypeSeen, TypeSeen).
spec_type_seen(alignas(_), TypeSeen, TypeSeen).
spec_type_seen(su(_, _, _, _), _, yes).
spec_type_seen(enum(_, _), _, yes).
spec_type_seen(typeof(_), _, yes).
spec_type_seen(tname(_), _, yes).

specifier(_, _, storage(S)) -->
    kw(S),
    { memberchk(S, [typedef, extern, static, auto, register, thread_local]) },
    !.
specifier(_, _, tspec(K)) -->
    kw(K),
    {   memberchk(K, [void, char, short, int, long, float, double, signed,
                      unsigned, bool, complex, int128])
    }, !.
specifier(_, _, _) -->
    kw(atomic),
    punct('('), !,
    parse_error('_Atomic types are not supported').
specifier(_, _, qual(Q)) -->
    kw(Q), { memberchk(Q, [const, volatile, restrict, atomic]) }, !.
specifier(_, _, fspec(F)) -->
    kw(F), { memberchk(F, [inline, noreturn]) }, !.
specifier(_, _, attr(A)) --> gnu_attr(A), !.
specifier(_, _, attr(c23)) --> c23_attr, !.
specifier(_, _, attr(extension)) --> kw(extension), !.
specifier(Env, _, alignas(A)) -->
    kw(alignas), !,
    expect('('),
    (   type_name(Env, T)
    ->  { A = type(T) }
    ;   conditional(Env, E),
        { A = expr(E) }
    ),
    expect(')').
specifier(Env, _, Spec) -->
    kw(K), { memberchk(K, [struct, union]) }, !,
    struct_spec(Env, K, Spec).
specifier(Env, _, Spec) -->
    kw(enum), !,
    enum_spec(Env, Spec).
specifier(Env, _, typeof(A)) -->
    kw(typeof), !,
    expect('('),
    (   type_name(Env, T)
    ->  { A = type(T) }
    ;   expr(Env, E),
        { A = expr(E) }
    ),
    expect(')').
specifier(Env, no, tname(N)) -->
    token(id(N)),
    { get_assoc(N, Env, t) }.

% gnu_attr(-Tokens)//: __attribute__((...)), Tokens its balanced//1
% contents.
gnu_attr(A) -->
    kw(attribute),
    expect('('),
    balanced(A0),
    { A = A0 }.

% balanced(-Toks)//: tokens up to the ')' matching an already-consumed '(';
% nested parentheses become group(Toks).
balanced([]) --> punct(')'), !.
balanced([T|Ts]) -->
    punct('('), !,
    balanced(Inner),
    { T = group(Inner) },
    balanced(Ts).
balanced([T|Ts]) -->
    [tok(T, _)], !,
    balanced(Ts).
balanced(_) --> parse_error('unbalanced parentheses').

% c23_attr//: a standard attribute specifier. Do not confuse its opening
% '[[' with an array suffix. Arguments are balanced token sequences, not
% C expressions (unknown vendors may use their own argument language).
c23_attr -->
    punct('['), punct('['), !,
    c23_attr_entries,
    expect(']'), expect(']').

c23_attrs --> c23_attr, !, c23_attrs.
c23_attrs --> [].

c23_attr_entries -->
    (   attribute_word(Prefix)
    ->  (   punct(':')
        ->  expect(':'),
            attribute_word(Name),
            c23_attribute_semantics(Prefix, Name)
        ;   []
        ),
        ( punct('(') -> attribute_argument(')') ; [] )
    ;   []
    ),
    ( punct(',') -> c23_attr_entries ; [] ).

attribute_word(N) --> token(id(N)), !.
attribute_word(N) --> token(kw(N)).

% Like their GNU spellings, layout-changing attributes cannot be ignored.
% Reject here also at positions (e.g. pointers) whose attributes we discard.
c23_attribute_semantics(Prefix, Name) -->
    { memberchk(Prefix, [gnu, '__gnu__']),
      memberchk(Name, [packed, '__packed__', aligned, '__aligned__']) }, !,
    parse_error('alignment attributes are not supported').
c23_attribute_semantics(_, _) --> [].

attribute_argument(Close) --> punct(Close), !.
attribute_argument(Close) -->
    punct(Open), { attribute_delimiter(Open, End) }, !,
    attribute_argument(End),
    attribute_argument(Close).
attribute_argument(Close) -->
    token(T),
    { \+ memberchk(T, [p(')'), p(']'), p('}')]) }, !,
    attribute_argument(Close).
attribute_argument(_) --> parse_error('unbalanced attribute argument').

attribute_delimiter('(', ')').
attribute_delimiter('[', ']').
attribute_delimiter('{', '}').

% attrs//: GNU and C23 attributes, ignored.
attrs -->
    gnu_attr(_), !,
    attrs.
attrs --> c23_attr, !, attrs.
attrs --> [].

struct_spec(Env, Kind, su(Kind, Tag, Members, Attrs)) -->
    attr_list(Attrs0),
    ( token(id(Tag0)) -> { Tag = some(Tag0) } ; { Tag = none } ),
    (   punct('{')
    ->  members(Env, Members),
        attr_list(Attrs1)
    ;   { Tag = some(_), Members = none, Attrs1 = [] }
    ),
    { append(Attrs0, Attrs1, Attrs) }.

attr_list([A|As]) -->
    gnu_attr(A), !,
    attr_list(As).
attr_list(As) --> c23_attr, !, attr_list(As).
attr_list([]) --> [].

% members(+Env, -Members)//: the member declarations of a struct or
% union up to its '}'.
members(_, []) --> punct('}'), !.
members(Env, Members) -->
    punct(';'), !,
    members(Env, Members).
members(Env, [static_assert(Loc, E, Msg)|Members]) -->
    loc(Loc),
    kw(static_assert), !,
    expect('('),
    conditional(Env, E),
    ( punct(',') -> string_bytes(Msg) ; { Msg = [] } ),
    expect(')'),
    expect(';'),
    members(Env, Members).
members(Env, Members) -->
    decl_specs(Env, Specs), !,
    (   punct(';')
    ->  { Members = [field(Specs, dcl(none, base, none), none)|Members1] }
    ;   field_decls(Env, Specs, Members, Members1),
        expect(';')
    ),
    members(Env, Members1).
members(_, _) --> parse_error('expected a member declaration').

% field_decls(+Env, +Specs, -Fields, ?Rest)//: Fields-Rest is the
% difference list of fields one member declaration declares.
field_decls(Env, Specs, [field(FieldSpecs, Dcl, Width)|Fields], Rest) -->
    (   punct(':')
    ->  { Dcl = dcl(none, base, none), Attrs = [] },
        conditional(Env, Width)
    ;   full_declarator(Env, Dcl, Attrs),
        ( punct(':') -> conditional(Env, Width) ; { Width = none } )
    ),
    attr_list(Attrs1),
    {   findall(attr(X), member(X, Attrs1), Attrs2),
        append([Specs, Attrs, Attrs2], FieldSpecs)
    },
    (   punct(',')
    ->  field_decls(Env, Specs, Fields, Rest)
    ;   { Fields = Rest }
    ).

enum_spec(Env, enum(Tag, Enumerators)) -->
    attrs,
    ( token(id(Tag0)) -> { Tag = some(Tag0) } ; { Tag = none } ),
    (   punct('{')
    ->  enumerators(Env, Enumerators)
    ;   { Tag = some(_), Enumerators = none }
    ),
    attrs.

% enumerators(+Env, -Enumerators)//: the enumerators up to the '}'.
enumerators(_, []) --> punct('}'), !.
enumerators(Env, [enumerator(Name, Value)|Es]) -->
    token(id(Name)), !,
    attrs,
    ( punct('=') -> conditional(Env, V0), { Value = V0 } ; { Value = none } ),
    ( punct(',') -> enumerators(Env, Es) ; expect('}'), { Es = [] } ).
enumerators(_, _) --> parse_error('expected an enumerator').

%% Declarators

% full_declarator(+Env, -Dcl, -Attrs)//: a declarator with its GNU
% suffix. Attributes after a declarator come back as attr(Tokens)
% specifiers in Attrs.
full_declarator(Env, dcl(some(Name), Type, Asm), Attrs) -->
    declarator(Env, Name, Type, base),
    gnu_suffix(Asm, Attrs).

% gnu_suffix(-Asm, -Attrs)//: attributes and an asm("symbol") label.
gnu_suffix(Asm, Attrs) -->
    attr_list(Attrs0),
    (   kw(asm)
    ->  expect('('),
        string_bytes(Bytes),
        expect(')'),
        { atom_codes(Symbol, Bytes), Asm = asm(Symbol) }
    ;   { Asm = none }
    ),
    attr_list(Attrs1),
    {   append(Attrs0, Attrs1, Attrs2),
        findall(attr(X), member(X, Attrs2), Attrs)
    }.

% declarator(+Env, -Name, -Type, +Base)//: a declarator of Name; Type is
% built around Base.
declarator(Env, Name, Type, Base) -->
    punct('*'), !,
    qualifiers(Quals),
    declarator(Env, Name, Type, ptr(Base, Quals)).
declarator(Env, Name, Type, Base) -->
    attrs,
    direct_declarator(Env, Name, Type, Base).

direct_declarator(Env, Name, Type, Base) -->
    token(id(Name)), !,
    suffixes(Env, Base, Type).
direct_declarator(Env, Name, Type, Base) -->
    punct('('),
    declarator(Env, Name, Type, Mid),
    expect(')'),
    suffixes(Env, Base, Mid).

qualifiers(Quals) -->
    kw(Q), { memberchk(Q, [const, volatile, restrict, atomic]) }, !,
    { Quals = [Q|Quals1] },
    qualifiers(Quals1).
qualifiers(Quals) -->
    gnu_attr(_), !,
    qualifiers(Quals).
qualifiers(Quals) --> c23_attr, !, qualifiers(Quals).
qualifiers([]) --> [].

% abstract_declarator(+Env, -Type, +Base)//: like declarator//4 without
% a name. A '(' starts a nested declarator only before a '*'; otherwise
% it is a parameter list.
abstract_declarator(Env, Type, Base) -->
    punct('*'), !,
    qualifiers(Quals),
    abstract_declarator(Env, Type, ptr(Base, Quals)).
abstract_declarator(Env, Type, Base) -->
    punct('('),
    peek(p('*')), !,
    abstract_declarator(Env, Type, Mid),
    expect(')'),
    suffixes(Env, Base, Mid).
abstract_declarator(Env, Type, Base) --> suffixes(Env, Base, Type).

% suffixes(+Env, +Base, -Type)//: array and function suffixes, applied
% inside out: Type is Base with them.
suffixes(Env, Base, Type) -->
    c23_attr, !,
    suffixes(Env, Base, Type).
suffixes(Env, Base, Type) -->
    punct('['), !,
    array_size(Env, Size),
    expect(']'),
    suffixes(Env, Base, Type1),
    { Type = array(Type1, Size) }.
suffixes(Env, Base, Type) -->
    punct('('), !,
    params(Env, Params),
    suffixes(Env, Base, Type1),
    { Type = func(Type1, Params) }.
suffixes(_, Base, Base) --> [].

% array_size(+Env, -Size)//: the size between '[' and ']', or none; the
% ']' stays in the input.
array_size(_, none), [tok(p(']'), Loc)] --> [tok(p(']'), Loc)], !.
array_size(_, _) -->
    punct('*'),
    peek(p(']')), !,
    parse_error('variable length arrays are not supported').
array_size(Env, Size) -->
    kw(static), !,
    array_size(Env, Size).
array_size(Env, Size) -->
    kw(Q), { memberchk(Q, [const, volatile, restrict]) }, !,
    array_size(Env, Size).
array_size(Env, Size) --> assignment(Env, Size).

% params(+Env, -Params)//: a parameter list after its '(', through ')'.
params(_, unspecified) --> punct(')'), !.
params(_, params([], fixed)) -->
    kw(void),
    punct(')'), !.
params(Env, params(Params, Variadic)) -->
    param_list(Env, Params, Variadic),
    expect(')').

param_list(_, [], variadic) --> punct('...'), !.
param_list(Env, [Param|Params], Variadic) -->
    param(Env, Param),
    (   punct(',')
    ->  param_list(Env, Params, Variadic)
    ;   { Params = [], Variadic = fixed }
    ).

param(Env, param(Specs, dcl(Name, Type, none))) -->
    decl_specs(Env, Specs), !,
    (   declarator(Env, Name0, Type, base)
    ->  { Name = some(Name0) }
    ;   abstract_declarator(Env, Type, base),
        { Name = none }
    ),
    attrs.
param(_, _) -->
    token(id(_)), !,
    parse_error('K&R-style parameter lists are not supported').
param(_, _) --> parse_error('expected a parameter declaration').

% type_name(+Env, -TypeName)//: a type name, type(Specs, Type).
type_name(Env, type(Specs, Type)) -->
    decl_specs(Env, Specs),
    abstract_declarator(Env, Type, base).

% starts_type(+Env)//: lookahead: the next token begins a type name.
starts_type(Env), [tok(X, Loc)] -->
    [tok(X, Loc)],
    { type_start_token(X, Env) }.

type_start_token(kw(K), _) :-
    memberchk(K, [void, char, short, int, long, float, double, signed,
                  unsigned, bool, complex, int128, struct, union, enum,
                  const, volatile, restrict, atomic, typeof, attribute,
                  alignas, extension]).
type_start_token(id(N), Env) :-
    get_assoc(N, Env, t).

%% Initializers

% initializer(+Env, -Init)//: an expression or a braced list(Entries).
initializer(Env, list(Entries)) -->
    punct('{'), !,
    init_entries(Env, Entries).
initializer(Env, E) --> assignment(Env, E).

% init_entries(+Env, -Entries)//: the entries of a braced initializer
% after its '{', through '}'.
init_entries(_, []) --> punct('}'), !.
init_entries(Env, [entry(Designators, Init)|Entries]) -->
    (   designators(Env, Ds0), { Ds0 \== [] }
    ->  expect('='),
        { Designators = Ds0 }
    ;   { Designators = [] }
    ),
    initializer(Env, Init),
    (   punct(',')
    ->  init_entries(Env, Entries)
    ;   expect('}'),
        { Entries = [] }
    ).

designators(Env, [D|Ds]) -->
    designator(Env, D), !,
    designators(Env, Ds).
designators(_, []) --> [].

designator(_, field(Name)) -->
    punct('.'),
    token(id(Name)).
designator(Env, index(E)) -->
    punct('['),
    conditional(Env, E),
    (   punct('...')
    ->  parse_error('GNU range designators are not supported')
    ;   expect(']')
    ).

%% Statements

block(Env, at(Loc, block(Items))) -->
    loc(Loc),
    punct('{'),
    block_items(Env, Items).

% block_items(+Env, -Items)//: the items of a block through its '}'.
block_items(_, []) --> punct('}'), !.
block_items(Env0, [Item|Items]) -->
    block_item(Env0, Env, Item),
    block_items(Env, Items).

% block_item(+Env0, -Env, -Item)//: a declaration or statement in a
% block; Env is Env0 with the declaration's typedef names.
block_item(Env, Env, Item) -->
    loc(Loc),
    kw(static_assert), !,
    static_assert_rest(Env, Loc, Item).
block_item(Env0, Env, Item) -->
    starts_decl(Env0), !,
    local_decl(Env0, Env, Item).
block_item(Env, Env, Stmt) --> statement(Env, Stmt).

% starts_decl(+Env)//: lookahead only: the next tokens begin a
% declaration, not a label.
starts_decl(Env, S, S) :-
    phrase(c23_attrs, S, Rest),
    \+ phrase(label_start, Rest, _),
    (   phrase(starts_type(Env), Rest, _)
    ->  true
    ;   Rest = [tok(kw(K), _)|_],
        memberchk(K, [typedef, extern, static, auto, register, thread_local,
                      inline, noreturn])
    ).

% label_start//: lookahead: the next tokens are an identifier and ':'.
label_start, [A, B] -->
    [A, B],
    { A = tok(id(_), _), B = tok(p(':'), _) }.

% local_decl(+Env0, -Env, -Decl)//: a declaration in a block or for.
local_decl(Env0, Env, decl(Loc, Specs1, Inits)) -->
    loc(Loc),
    decl_specs(Env0, Specs),
    (   punct(';')
    ->  { Inits = [], Attrs = [] }
    ;   full_declarator(Env0, Dcl, Attrs0),
        init_declarators(Env0, Dcl, Inits, Attrs0, Attrs),
        expect(';')
    ),
    {   append(Specs, Attrs, Specs1),
        decl_env(Specs, Inits, Env0, Env)
    }.

% statement(+Env, -Stmt)//: a statement at(Loc, S). The cut commits to
% the first parse; if there is none, it is a syntax error.
statement(Env, at(Loc, S)) -->
    loc(Loc),
    c23_attrs,
    statement_body(Env, S), !.
statement(_, _) --> parse_error('expected a statement').

statement_body(Env, S) -->
    peek(p('{')), !,
    block(Env, at(_, S)).
statement_body(_, null) --> punct(';'), !.
statement_body(Env, if(C, Then, Else)) -->
    kw(if), !,
    expect('('),
    expr(Env, C),
    expect(')'),
    statement(Env, Then),
    (   kw(else)
    ->  statement(Env, Else0),
        { Else = Else0 }
    ;   { Else = none }
    ).
statement_body(Env, while(C, S)) -->
    kw(while), !,
    expect('('),
    expr(Env, C),
    expect(')'),
    statement(Env, S).
statement_body(Env, do(S, C)) -->
    kw(do), !,
    statement(Env, S),
    ( kw(while) -> [] ; parse_error('expected while') ),
    expect('('),
    expr(Env, C),
    expect(')'),
    expect(';').
statement_body(Env, for(Init, C, Step, S)) -->
    kw(for), !,
    expect('('),
    (   starts_decl(Env)
    ->  local_decl(Env, Env1, Init)
    ;   opt_expr(Env, E0),
        expect(';'),
        {   Env1 = Env,
            ( E0 == none -> Init = none ; Init = expr(E0) )
        }
    ),
    opt_expr(Env1, C),
    expect(';'),
    opt_expr(Env1, Step),
    expect(')'),
    statement(Env1, S).
statement_body(Env, switch(E, S)) -->
    kw(switch), !,
    expect('('),
    expr(Env, E),
    expect(')'),
    statement(Env, S).
statement_body(Env, case(E, S)) -->
    kw(case), !,
    conditional(Env, E),
    (   punct('...')
    ->  parse_error('GNU case ranges are not supported')
    ;   expect(':')
    ),
    statement(Env, S).
statement_body(Env, default(S)) -->
    kw(default), !,
    expect(':'),
    statement(Env, S).
statement_body(_, break) -->
    kw(break), !,
    expect(';').
statement_body(_, continue) -->
    kw(continue), !,
    expect(';').
statement_body(Env, return(E)) -->
    kw(return), !,
    opt_expr(Env, E),
    expect(';').
statement_body(_, goto(Label)) -->
    kw(goto), !,
    (   token(id(Label0))
    ->  { Label = Label0 }
    ;   parse_error('computed goto is not supported')
    ),
    expect(';').
statement_body(_, _) -->
    kw(asm), !,
    parse_error('inline asm is not supported').
statement_body(Env, label(Label, S)) -->
    label_start, !,
    [tok(id(Label), _), _],
    statement(Env, S).
statement_body(Env, expr(E)) -->
    expr(Env, E),
    expect(';').

% opt_expr(+Env, -E)//: an expression, or none before ';' or ')', which
% stays in the input.
opt_expr(_, none), [tok(p(P), Loc)] -->
    [tok(p(P), Loc)], { memberchk(P, [';', ')']) }, !.
opt_expr(Env, E) --> expr(Env, E).

%% Expressions

% expr(+Env, -E)//: an expression, commas included.
expr(Env, E) -->
    assignment(Env, E0),
    (   punct(',')
    ->  expr(Env, E1),
        { E = comma(E0, E1) }
    ;   { E = E0 }
    ).

assignment(Env, E) -->
    conditional(Env, Lhs),
    (   punct(Op), { assign_op(Op) }
    ->  assignment(Env, Rhs),
        { E = assign(Op, Lhs, Rhs) }
    ;   { E = Lhs }
    ).

assign_op('=').
assign_op('*=').
assign_op('/=').
assign_op('%=').
assign_op('+=').
assign_op('-=').
assign_op('<<=').
assign_op('>>=').
assign_op('&=').
assign_op('^=').
assign_op('|=').

conditional(Env, E) -->
    binary(Env, 1, C),
    (   punct('?')
    ->  (   punct(':')
        ->  conditional(Env, B),
            { E = gcond(C, B) }
        ;   expr(Env, A),
            expect(':'),
            conditional(Env, B),
            { E = cond(C, A, B) }
        )
    ;   { E = C }
    ).

% binary(+Env, +Level, -E)//: binary operators of precedence Level and up;
% level 11 is a cast expression.
binary(Env, 11, E) --> !, cast(Env, E).
binary(Env, Level, E) -->
    { Level1 is Level + 1 },
    binary(Env, Level1, Lhs),
    binary_rest(Env, Level, Lhs, E).

binary_rest(Env, Level, Lhs, E) -->
    punct(P), { binop(P, Level, Op) }, !,
    { Level1 is Level + 1 },
    binary(Env, Level1, Rhs),
    binary_rest(Env, Level, bin(Op, Lhs, Rhs), E).
binary_rest(_, _, E, E) --> [].

binop('||', 1, lor).
binop('&&', 2, land).
binop('|', 3, or).
binop('^', 4, xor).
binop('&', 5, and).
binop('==', 6, eq).
binop('!=', 6, ne).
binop('<', 7, lt).
binop('>', 7, gt).
binop('<=', 7, le).
binop('>=', 7, ge).
binop('<<', 8, shl).
binop('>>', 8, shr).
binop('+', 9, add).
binop('-', 9, sub).
binop('*', 10, mul).
binop('/', 10, div).
binop('%', 10, mod).

% cast(+Env, -E)//: a cast expression or compound literal, else a unary
% expression.
cast(Env, E) -->
    punct('('),
    starts_type(Env), !,
    type_name(Env, Type),
    expect(')'),
    (   punct('{')
    ->  init_entries(Env, Entries),
        postfix(Env, complit(Type, list(Entries)), E)
    ;   cast(Env, E0),
        { E = cast(Type, E0) }
    ).
cast(Env, E) --> unary(Env, E).

unary(Env, un(preinc, E)) -->
    punct('++'), !,
    unary(Env, E).
unary(Env, un(predec, E)) -->
    punct('--'), !,
    unary(Env, E).
unary(Env, un(Op, E)) -->
    punct(P), { unop(P, Op) }, !,
    cast(Env, E).
unary(Env, E) -->
    kw(sizeof), !,
    (   punct('('), starts_type(Env)
    ->  type_name(Env, Type),
        expect(')'),
        { E = sizeof_type(Type) }
    ;   unary(Env, E0),
        { E = sizeof_expr(E0) }
    ).
unary(Env, alignof(Type)) -->
    kw(alignof), !,
    expect('('),
    type_name(Env, Type),
    expect(')').
unary(Env, E) -->
    kw(extension), !,
    cast(Env, E).
unary(_, _) -->
    punct('&&'), !,
    parse_error('label addresses are not supported').
unary(Env, E) -->
    primary(Env, P),
    postfix(Env, P, E).

unop('&', addr).
unop('*', deref).
unop('+', plus).
unop('-', neg).
unop('~', bnot).
unop('!', not).

% postfix(+Env, +A, -E)//: E is A with the postfix operators that follow.
postfix(Env, A, E) -->
    punct('['), !,
    expr(Env, I),
    expect(']'),
    postfix(Env, index(A, I), E).
postfix(Env, A, E) -->
    punct('('), !,
    args(Env, Args),
    postfix(Env, call(A, Args), E).
postfix(Env, A, E) -->
    punct('.'), !,
    field_name(F),
    postfix(Env, member(A, F), E).
postfix(Env, A, E) -->
    punct('->'), !,
    field_name(F),
    postfix(Env, arrow(A, F), E).
postfix(Env, A, E) -->
    punct('++'), !,
    postfix(Env, un(postinc, A), E).
postfix(Env, A, E) -->
    punct('--'), !,
    postfix(Env, un(postdec, A), E).
postfix(_, E, E) --> [].

field_name(F) --> token(id(F)), !.
field_name(_) --> parse_error('expected a member name').

% args(+Env, -Args)//: call arguments after '(', through ')'.
args(_, []) --> punct(')'), !.
args(Env, [A|As]) -->
    assignment(Env, A),
    (   punct(',')
    ->  args(Env, As)
    ;   expect(')'),
        { As = [] }
    ).

% primary(+Env, -E)//: a primary expression.
primary(Env, offsetof(Type, Path)) -->
    token(id('__builtin_offsetof')), !,
    expect('('),
    type_name(Env, Type),
    expect(','),
    field_name(F),
    offsetof_path(Env, Steps),
    expect(')'),
    { Path = [field(F)|Steps] }.
primary(_, _) -->
    token(id(N)),
    {   memberchk(N, ['__builtin_va_arg', '__builtin_va_start',
                      '__builtin_va_end', '__builtin_va_copy',
                      '__builtin_types_compatible_p'])
    }, !,
    { format(atom(Msg), '~w is not supported', [N]) },
    parse_error(Msg).
primary(_, id(N)) --> token(id(N)), !.
primary(_, num(V, S)) --> token(int(V, S)), !.
primary(_, float(Cs)) --> token(float(Cs)), !.
primary(_, chr(V)) --> token(chr(V)), !.
primary(_, S) -->
    ( peek(str(_)) ; peek(wstr(_, _)) ), !,
    string_literals(Parts),
    { parts_string(Parts, S) }.
primary(Env, stmtexpr(Block)) -->
    punct('('),
    peek(p('{')), !,
    block(Env, Block),
    expect(')').
primary(_, _) -->
    kw(generic), !,
    parse_error('_Generic is not supported').
primary(Env, E) -->
    punct('('), !,
    expr(Env, E),
    expect(')').
primary(_, _) --> parse_error('expected an expression').

offsetof_path(Env, [field(F)|Steps]) -->
    punct('.'), !,
    field_name(F),
    offsetof_path(Env, Steps).
offsetof_path(Env, [index(E)|Steps]) -->
    punct('['), !,
    expr(Env, E),
    expect(']'),
    offsetof_path(Env, Steps).
offsetof_path(_, []) --> [].

% string_literals(-Parts)//: one or more adjacent string literals, each
% str(Bytes) or wstr(Type, Codes). They concatenate; if one is wide, all
% are, and a plain one's bytes become elements (exact for ASCII).
string_literals([S|Ss]) -->
    string_literal(S), !,
    ( string_literals(Ss) -> [] ; { Ss = [] } ).

string_literal(str(B)) --> token(str(B)).
string_literal(wstr(T, Vs)) --> token(wstr(T, Vs)).

% string_bytes(-Bytes)//: adjacent plain string literals as one list of
% bytes.
string_bytes(Bs) -->
    token(str(B0)), !,
    ( string_bytes(B1) -> { append(B0, B1, Bs) } ; { Bs = B0 } ).

% parts_string(+Parts, -S): S is the string literal Parts concatenate.
parts_string(Parts, S) :-
    findall(T, member(wstr(T, _), Parts), Types0),
    sort(Types0, Types),
    findall(Vs,
            ( member(P, Parts), ( P = str(Vs) ; P = wstr(_, Vs) ) ),
            Vss),
    append(Vss, All),
    types_string(Types, All, S).

% types_string(+WideTypes, +Elements, -S): S is the literal of Elements:
% plain if no part is wide, else of the one wide type.
types_string([], All, str(All)).
types_string([T|Ts], All, S) :- wide_string(Ts, T, All, S).

wide_string([], T, All, wstr(T, All)).
wide_string([_|_], _, _, _) :-
    throw(nanofil_error(
        'concatenating string literals of different wide types')).

/*  C's types as terms: specifiers and declarators become type terms,
    and from those come sizes and layouts, the integer conversions and
    the values of constant expressions (milestone 4a).

    ## Types

    | Type | Means |
    |---|---|
    | `void` `bool` | as in C |
    | `char` `schar` `uchar` | `char`, `signed char`, `unsigned char` |
    | `short` `int` `long` `llong` | the signed integer types |
    | `ushort` `uint` `ulong` `ullong` | their unsigned counterparts |
    | `float` `double` `ldouble` | the floating types |
    | `ptr(T)` | a pointer to T |
    | `array(T, N)` | N elements of T, or `array(T, none)` of unknown length |
    | `array(T, vla(E))` | a variable length array whose size expression E is not yet evaluated; E is `star` for `[*]` |
    | `array(T, dyn(V))` | a variable length array whose length lowering evaluated into the IR value V |
    | `func(Ret, Params, Arity)` | Params a list of types, or `unspecified`; Arity `fixed` or `variadic` |
    | `struct(Id)` `union(Id)` | the struct or union Id of the environment's Defs |
    | `bad(Reason)` | a type the frontend cannot handle yet |

    Parameter types are already adjusted: arrays and functions become
    pointers. A type with a `vla` or `dyn` length somewhere inside is
    variably modified (`vm_type/1`); lowering evaluates each `vla(E)`
    where C evaluates it, which makes it `dyn(V)`. Qualifiers are dropped, and an enum type is its underlying
    integer type. A `bad(Reason)` is an error only when a declaration
    uses it, so headers that mention such types still parse.

    ## The environment

    The semantic environment `e(Ords, Tags, Defs, Next)` has four parts:

    | Part | From | To |
    |---|---|---|
    | Ords | an ordinary identifier | `typedef(T)`, `enumconst(V, T)`, or what lowering stores for a variable or function |
    | Tags | a tag | `tag(Kind, Id)`, Kind `struct` or `union`, or `enum(T)` |
    | Defs | a struct or union Id | its definition, below |
    | Next | | the next Id |

    A definition is one of:

    | Definition | Means |
    |---|---|
    | `incomplete(Tag)` | declared, not yet defined; Tag is `some(Name)`, or `none` when anonymous |
    | `def(Kind, Members, Size, Align)` | complete: Members in order, and the layout |
    | `partial(Reason, Members)` | only the members whose offsets are known: no usable layout |
    | `bad(Reason)` | a definition the frontend cannot handle yet |

    and a member one of:

    | Member | Means |
    |---|---|
    | `m(some(Field), Type, Offset)` | Field, of Type, Offset bytes in |
    | `m(none, Type, Offset)` | an anonymous struct or union member |
    | `m(some(Field), Type, Offset, bits(Pos, Width))` | a bit-field: Width bits from bit Pos of the Type at Offset |

    Lowering keeps entries of its own in Defs too. A block scope saves
    Ords and Tags and restores them when it ends; Defs and Next only
    grow. A predicate that changes the environment takes Env0 and gives
    Env as its last two arguments, so it threads through foldl/4,6.
*/
:- module(c_types, [empty_env/1, specs_type/4, apply_declarator/5,
                    type_size_align/4, arith_size/3, classify_builtin/1, complete_type/2, int_type/1, int_info/3,
                    integer_promotion/2, usual_arith_conversion/3,
                    float_type/1, arithmetic_type/1, default_promotion/2,
                    constant_value/4, const_convert/4, float_literal/3,
                    float_builtin/3, libm_builtin/2, object_size/4, compatible_type/2, composite_type/3, inherited_alignment/4,
                    convert_int/3, const_value/4, pp_value/2, num_type/3,
                    scalar_type/1, type_class/2, member_type_offset/5, type_name_type/4,
                    lookup_ordinary/3, bind_ordinary/4, env_scope/3,
                    env_restore/3, sema_error/3, enum_underlying/2,
                    decl_types/5, elaborate/3, elaborate/4, expression_type/3,
                    vm_type/1, vla_type/1, unsupported_type/3, value_type/2,
                    generic_selection/5, reflect_type/4, reflect_params/4,
                    conditional_type/3, unqualified/2,
                    overflow_builtin/3, bit_builtin/3, builtin_type/2, binary_operands/6,
                    unary_operand/3, assigned/4,
                    castable/2, expression_category/3, modifiable_lvalue/2,
                    integer_type/4, elaborate/3, tree_type/2, value/2,
                    lowered/2, folded/3, member_layout/6,
                    bitfield_promotion/3, unaligned_type/2, underaligned_member/4, atomic_qualified/1,
                    rmw_builtin/4]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ieee).

% Documentation is a relation of the module, doc(Head, Det, Props)
% (docs/dterm.md); tests/unit.pl runs every example.
:- discontiguous(doc/3).
:- use_module(c_parse, [c_operator/4, compound_assignment/2, c_constant_expression/2]).

%% Environment

%! empty_env(-Env) is det.
%
%  Env has no user identifiers or tags, and the builtin va_list record.

empty_env(e(Ords, Tags, Defs, 0)) :-
    empty_assoc(Ords),
    empty_assoc(Tags),
    va_list_def(Def),
    list_to_assoc(['builtin.va_list'-Def], Defs).

va_list_def(def(struct, [m(some(gp_offset), uint, 0),
                        m(some(fp_offset), uint, 4),
                        m(some(overflow_arg_area), ptr(void), 8),
                        m(some(reg_save_area), ptr(void), 16)], 24, 8)).

%! lookup_ordinary(+Env, +Name, ?Value) is semidet.
%
%  Value is what the ordinary identifier Name stands for in Env.

lookup_ordinary(e(Ords, _, _, _), Name, Value) :-
    get_assoc(Name, Ords, Value).

%! bind_ordinary(+Name, +Value, +Env0, -Env) is det.
%
%  Env is Env0 with the ordinary identifier Name standing for Value,
%  replacing any binding it had.

bind_ordinary(Name, Value, e(Ords0, Tags, Defs, Next),
              e(Ords, Tags, Defs, Next)) :-
    put_assoc(Name, Ords0, Value, Ords).

%! env_scope(+Env, -Scope, ?Unused) is det.
%
%  Scope is the scoped part of Env (its ordinary identifiers and tags),
%  for env_restore/3. The third argument is unused.

env_scope(e(Ords, Tags, _, _), s(Ords, Tags), _).

%! env_restore(+Scope, +Env0, -Env) is det.
%
%  Env is Env0 with its scoped part replaced by Scope: the identifiers
%  and tags of an inner scope are gone, its definitions stay.

env_restore(s(Ords, Tags), e(_, _, Defs, Next), e(Ords, Tags, Defs, Next)).

%! sema_error(+Loc, +Fmt, +Args)
%
%  Throw nanofil_error with the message Fmt/Args, prefixed with Loc.
%  Never succeeds.

sema_error(Loc, Fmt, Args) :-
    format(atom(Msg0), Fmt, Args),
    format(atom(Msg), '~w: ~w', [Loc, Msg0]),
    throw(nanofil_error(Msg)).

%% Declarations

%! decl_types(+Specs, +Inits, -Decls, +Env0, -Env) is det.
%
%  Decls are d(Name, Type, Storage, Asm, Init) for the declarators Inits
%  under the specifiers Specs, Storage as decl_storage/2 gives it. A
%  typedef declares no Decls; Env is Env0 with its names bound instead.
%  Env also has any struct, union or enum Specs defines, and each
%  object's alignment request (object_alignment/5). Throws
%  not_constant when an enumerator's value is not constant.

decl_types(Specs0, Inits, Decls, Env0, Env) :-
    decl_storage(Specs0, Storage),
    partition(alignment_request, Specs0, Requests, Specs),
    specs_type(Specs, Base, Env0, Env1),
    foldl(declarator_type(Specs, Requests, Base, Storage), Inits, Decls0, Env1, Env),
    exclude(==(none), Decls0, Decls).

doc(decl_storage(+Specs, -Storage), det, [
    Specs: "a declaration's specifiers",
    Storage: "none, typedef, static, extern, auto or register, or thread_local(S) with S one of none, static or extern",
    "Storage is the declaration's storage-class specifier. _Thread_local",
    "(also spelled thread_local and GNU __thread) may appear with static or",
    "extern, and then gives the object thread storage duration instead of",
    "static: one instance per thread, created and initialized when the",
    "thread first uses it (Fil-C creates it lazily, as clang's getter does).",
    "Where it may appear is the lowering's to check.",
    cites('C11 6.7.1p2-3'),
    cites('C11 6.2.4p4'),
    example(decl_storage([storage(static), tspec(int)], S), S = static),
    example(decl_storage([tspec(int)], S), S = none),
    example(decl_storage([storage(thread_local), storage(static), tspec(int)], S),
            S = thread_local(static)),
    example(decl_storage([storage(extern), storage(thread_local), tspec(int)], S),
            S = thread_local(extern)),
    example(decl_storage([storage(thread_local), tspec(int)], S), S = thread_local(none))
]).
decl_storage(Specs, Storage) :-
    (   member(storage(S0), Specs), S0 \== (thread_local) -> S = S0
    ;   S = none
    ),
    (   memberchk(storage(thread_local), Specs) -> Storage = thread_local(S)
    ;   Storage = S
    ).

% declarator_type(+Specs, +Requests, +Base, +Storage, +Init, -Decl, +Env0, -Env):
% Decl is the d/5 term Init declares, or none for a typedef, which binds
% the name. An object's alignment beyond its type's (object_alignment/5,
% from the alignment Requests and its typedef's) is bound to
% qalign(Name), none when it has none and an outer declaration did. A
% typedef's alignment (typedef_alignment/5) is bound to talign(Name).
declarator_type(Specs, Requests0, Base, Storage, init(dcl(some(Name), SyntaxType, Asm), Init),
                Decl, Env0, Env) :-
    apply_declarator(SyntaxType, Base, Type0, Env0, Env1),
    reflect_type(type(Specs, SyntaxType), Type0, Env1, Reflected),
    bind_ordinary(qtype(Name), Reflected, Env1, Env2),
    inherited_alignment(Specs, SyntaxType, Env2, Inherited),
    (   Storage == typedef
    ->  typedef_alignment(Requests0, Inherited, Type0, Env2, TA),
        ( TA = bad(Why) -> Type1 = bad(Why), TA1 = none ; Type1 = Type0, TA1 = TA ),
        bind_ordinary(Name, typedef(Type1), Env2, Env3),
        (   TA1 == none, \+ lookup_ordinary(Env3, talign(Name), _) -> Env4 = Env3
        ;   bind_ordinary(talign(Name), TA1, Env3, Env4)
        ),
        transparent_typedef(Specs, Type1, Env4, Env),
        Decl = none
    ;   ( Inherited = [align(IA)] -> Requests = [alignas(value(IA))|Requests0]
        ; Requests = Requests0 ),
        object_alignment(Requests, Type0, Env2, Type, A),
        (   A == none, lookup_ordinary(Env2, qalign(Name), _)
        ->  bind_ordinary(qalign(Name), none, Env2, Env)
        ;   A == none -> Env = Env2
        ;   bind_ordinary(qalign(Name), A, Env2, Env)
        ),
        Decl = d(Name, Type, Storage, Asm, Init)
    ).

doc(object_alignment(+Requests, +Type0, +Env, -Type, -A), det, [
    Requests: "the _Alignas specifiers and GNU aligned attributes of an object's declaration",
    Type0: "the declared type",
    Env: "the scope",
    Type: "Type0, or bad(Reason) for a request nanofil cannot honor",
    A: "the alignment the object needs beyond its type's, or none",
    "An alignment specifier or aligned attribute on an object declaration",
    "aligns that object, not its type: the strictest request, or the",
    "type's own alignment if stricter, is the object's. _Alignas(0) and",
    "a request no stricter than the type's change nothing; aligned with",
    "no argument is 16, x86-64's largest alignment (__BIGGEST_ALIGNMENT__).",
    "Lowering honors up to 4096 bytes, the most an alloc or a data item",
    "aligns to (above 16 as Fil-C's filc_allocate_with_alignment and its",
    "padded data objects do); a stricter request, or one on a function,",
    "is refused (bad). The type, and so sizeof and _Alignof of it, is",
    "unchanged.",
    cites('C11 6.7.5p2'),
    cites('C11 6.7.5p6'),
    cites('GCC manual, Common Variable Attributes, aligned'),
    example(( empty_env(E),
              object_alignment([attr([group([id(aligned), group([int(8, none-dec)])])])],
                               array(char, 4), E, T, A) ),
            (T = array(char, 4), A = 8)),
    example(( empty_env(E), object_alignment([alignas(expr(num(2, none-dec)))], int, E, T, A) ),
            (T = int, A = none)),
    example(( empty_env(E), object_alignment([alignas(type(type([tspec(long)], base)))], char, E, T, A) ),
            (T = char, A = 8)),
    example(( empty_env(E), object_alignment([attr([group([id('__aligned__')])])], char, E, _, A) ),
            A = 16),
    example(( empty_env(E), object_alignment([alignas(expr(num(64, none-dec)))], int, E, T, A) ),
            (T = int, A = 64)),
    example(( empty_env(E), object_alignment([alignas(expr(num(8192, none-dec)))], int, E, T, _) ),
            T = bad('an alignment above 4096'))
]).
object_alignment([], Type, _, Type, none) :- !.
object_alignment(_, func(_, _, _), _, bad('alignment attributes'), none) :- !.
object_alignment(Requests, Type0, Env, Type, A) :-
    (   innermost_element(Type0, Elem),       % a VLA has no constant size
        catch(type_size_align(Elem, Env, _, Natural), _, fail),
        maplist(request_alignment(Env), Requests, As),
        max_list([Natural|As], Max)
    ->  (   Max =:= Natural -> Type = Type0, A = none
        ;   max_alignment(M), Max =< M -> Type = Type0, A = Max
        ;   Type = bad('an alignment above 4096'), A = none
        )
    ;   Type = bad('alignment attributes'), A = none
    ).

% max_alignment(-A): the strictest alignment nanofil gives an object.
max_alignment(4096).

doc(typedef_alignment(+Requests, +Inherited, +Type, +Env, -A), det, [
    Requests: "the aligned attributes of a typedef declaration",
    Inherited: "[align(I)] if it names a typedef of alignment I (inherited_alignment/4), else []",
    Type: "the type it declares",
    Env: "the scope",
    A: "the typedef's alignment, none for its type's own, or bad(Reason)",
    "GNU aligned on a typedef sets the alignment of the typedef, not of",
    "its type, and may lower it as well as raise it; sizeof is unchanged",
    "(clang gives typedef struct { long a[3]; } B __attribute__((aligned))",
    "size 24, alignment 16). Without one, a typedef of a typedef keeps",
    "its alignment. _Alignas may not be applied to a typedef, and an",
    "alignment above 4096 or one that is not a constant power of two is",
    "refused.",
    cites('GCC manual, Common Type Attributes, aligned'),
    cites('C11 6.7.5p2'),
    example(( empty_env(E),
              typedef_alignment([attr([group([id('__aligned__')])])], [], long, E, A) ),
            A = 16),
    example(( empty_env(E),
              typedef_alignment([attr([group([id(aligned), group([int(1, none-dec)])])])],
                                [], int, E, A) ),
            A = 1),
    example(( empty_env(E), typedef_alignment([], [align(64)], int, E, A) ), A = 64),
    example(( empty_env(E), typedef_alignment([], [], int, E, A) ), A = none),
    example(( empty_env(E),
              typedef_alignment([attr([group([id(aligned), group([int(8192, none-dec)])])])],
                                [], int, E, A) ),
            A = bad('an alignment above 4096'))
]).
typedef_alignment([], Inherited, _, _, A) :- !,
    ( Inherited = [align(A)] -> true ; A = none ).
typedef_alignment(Requests, _, _, _, bad('_Alignas on a typedef')) :-
    memberchk(alignas(_), Requests), !.
typedef_alignment(Requests, _, _, Env, A) :-
    (   maplist(request_alignment(Env), Requests, As)
    ->  max_list(As, A0),
        (   max_alignment(M), A0 > M -> A = bad('an alignment above 4096')
        ;   A = A0
        )
    ;   A = bad('alignment attributes')
    ).

doc(inherited_alignment(+Specs, +SyntaxType, +Env, -Inherited), det, [
    Specs: "a declaration's specifiers",
    SyntaxType: "its declarator's type syntax",
    Env: "the scope",
    Inherited: "[align(A)] if Specs name a typedef of alignment A (typedef_alignment/5) and the declarator declares an object or array of it, else []",
    cites('GCC manual, Common Type Attributes, aligned'),
    example(( empty_env(E0), c_types:bind_ordinary(talign('B'), 64, E0, E),
              inherited_alignment([tname('B')], array(base, none), E, I) ),
            I = [align(64)]),
    example(( empty_env(E0), c_types:bind_ordinary(talign('B'), 64, E0, E),
              inherited_alignment([tname('B')], ptr(base, []), E, I) ),
            I = [])
]).
inherited_alignment(Specs, SyntaxType, Env, Inherited) :-
    (   memberchk(tname(N), Specs), object_declarator(SyntaxType),
        lookup_ordinary(Env, talign(N), A), integer(A)
    ->  Inherited = [align(A)]
    ;   Inherited = []
    ).

object_declarator(base).
object_declarator(array(S, _)) :- object_declarator(S).

innermost_element(array(T, _), E) :- !, innermost_element(T, E).
innermost_element(T, T).

% request_alignment(+Env, +Request, -A): the constant alignment Request
% asks for, a power of two or 0 (none).
request_alignment(_, alignas(value(A)), A) :- !.
request_alignment(Env, alignas(type(TN)), A) :- !,
    (   TN = type(Specs, Syntax),
        inherited_alignment(Specs, Syntax, Env, [align(IA)])
    ->  A = IA
    ;   type_name_type(TN, T, Env, Env1), type_size_align(T, Env1, _, A)
    ).
request_alignment(Env, alignas(expr(E)), A) :- !,
    catch(const_value(E, Env, A, _), not_constant, fail),
    ( A =:= 0 -> true ; A > 0, A /\ (A - 1) =:= 0 ).
request_alignment(Env, attr([group(Attr)]), A) :- !,   % __attribute__((...))
    request_alignment(Env, attr(Attr), A).
request_alignment(_, attr([Word]), 16) :-
    memberchk(Word, [id(aligned), id('__aligned__')]), !.
request_alignment(Env, attr([Word, group(Ts)]), A) :-
    memberchk(Word, [id(aligned), id('__aligned__')]),
    phrase(flat_tokens(Ts), Flat),
    catch(c_constant_expression(Flat, E), nanofil_error(_), fail),
    catch(const_value(E, Env, A, _), not_constant, fail),
    A > 0, A /\ (A - 1) =:= 0.

% Keep qualification for type reflection without changing the unqualified
% code-generation types. These entries share ordinary identifier scope,
% including shadowing and typedefs. Lvalue conversion removes only the
% outer qualification, never the qualification of a pointer's target.
% reflect_declarator/5 is deterministic; a choicepoint left by each
% declaration would keep its terms alive to the end of the file.
reflect_type(type(Specs, Syntax), Type, Env, Reflected) :-
    once(reflect_declarator(Syntax, Specs, Type, Env, Reflected)).

reflect_declarator(base, Specs, Type, Env, Reflected) :-
    ( memberchk(tname(Name), Specs), lookup_ordinary(Env, qtype(Name), T)
    -> Base = T
    ; memberchk(typeof(expr(E)), Specs), expression_type(E, Env, T)
    -> Base = T
    ; memberchk(typeof(type(TN)), Specs), type_name_type(TN, T0, Env, _)
    -> reflect_type(TN, T0, Env, Base)
    ; memberchk(atomic(TN), Specs), type_name_type(TN, T0, Env, _)
    -> reflect_type(TN, T0, Env, B0), qualify([atomic], B0, Base)
    ; Base = Type
    ),
    findall(Q, member(qual(Q), Specs), Qs), qualify(Qs, Base, Reflected).
reflect_declarator(ptr(S, Qs), Specs, ptr(T), Env, R) :-
    reflect_declarator(S, Specs, T, Env, RT), qualify(Qs, ptr(RT), R).
reflect_declarator(array(S, _), Specs, array(T, N), Env, array(RT, N)) :-
    reflect_declarator(S, Specs, T, Env, RT).
reflect_declarator(func(S, Params), Specs, func(T, Ps, V), Env, func(RT, RPs, V)) :-
    reflect_declarator(S, Specs, T, Env, RT),
    reflect_param_types(Params, Ps, Env, RPs).
reflect_declarator(_, _, bad(Why), _, bad(Why)).

reflect_param_types(unspecified, unspecified, _, unspecified).
reflect_param_types(params(Params, _), Ts, Env, RTs) :-
    maplist(reflect_param_type(Env), Params, Ts, RTs).

reflect_param_type(Env, param(Specs, dcl(_, Syntax, _)), T, RT) :-
    parameter_syntax(Syntax, Adjusted),
    reflect_type(type(Specs, Adjusted), T, Env, R0),
    value_type(R0, R1),
    ( transparent_first(R1, Env, _, RFirst) -> RT = RFirst ; RT = R1 ).

parameter_syntax(array(S, _), ptr(S, [])) :- !.
parameter_syntax(func(S, P), ptr(func(S, P), [])) :- !.
parameter_syntax(S, S).

qualify(Qs0, qualified(Qs1, T), R) :- !,
    append(Qs0, Qs1, Qs), qualify(Qs, T, R).
qualify(Qs, array(T0, N), array(T, N)) :- Qs \== [], !,   % C11 6.7.3p9
    qualify(Qs, T0, T).
qualify(Qs0, T, R) :-
    sort(Qs0, Qs), ( Qs == [] -> R = T ; R = qualified(Qs, T) ).

reflect_params(func(_, params(Params, _)), Types, Env0, Env) :- !,
    foldl(reflect_param, Params, Types, Env0, Env).
reflect_params(_, _, Env, Env).

reflect_param(Param, T, Env0, Env) :-
    Param = param(_, dcl(some(Name), _, _)), !,
    reflect_param_type(Env0, Param, T, RT),
    bind_ordinary(qtype(Name), RT, Env0, Env).
reflect_param(_, _, Env, Env).

%% Specifiers

%! specs_type(+Specs, -Type, +Env0, -Env) is det.
%
%  Type is the type the declaration specifiers Specs name, bad(Reason)
%  if the frontend cannot handle it. Env is Env0 with the struct, union
%  and enum definitions in Specs entered.

specs_type(Specs, Type, Env0, Env) :-
    base_type(Specs, Type0, Env0, Env),
    (   member(attr(Tokens), Specs), vector_attr(Tokens)
    ->  Type = bad('vector types')
    ;   memberchk(qual(atomic), Specs), Type0 \= bad(_), \+ atomic_object_type(Type0)
    ->  Type = bad('_Atomic on a type other than an integer, pointer, float or double')
    ;   member(Spec, Specs), layout_attr(Spec)
    ->  Type = bad('alignment attributes')
    ;   Type = Type0
    ).

doc(vector_attr(+Tokens), semidet, [
    Tokens: "the tokens of a GNU attribute",
    "The attribute is vector_size, which makes the declared type a",
    "vector of its specifiers' type (immintrin.h's __m128i). nanofil",
    "has no vector types: the type is refused (bad), an error only where",
    "it is used, so a header declaring vector typedefs and inline",
    "functions it never calls still compiles. Ignoring the attribute",
    "would give the vector the size of one element.",
    cites('GCC manual, Using Vector Instructions through Built-in Functions'),
    example(vector_attr([group([id('__vector_size__'), group([int(16, none-dec)])])])),
    fails(vector_attr([group([id(aligned), group([int(16, none-dec)])])]))
]).
vector_attr(Tokens) :-
    is_list(Tokens),
    attr_word(Tokens, Word),
    memberchk(Word, [vector_size, '__vector_size__', ext_vector_type]), !.

% layout_attr(+Spec): Spec is an attribute that changes layout, which
% the frontend does not model. The cut commits to the first such word.
layout_attr(alignas(_)).
layout_attr(attr(Tokens)) :-
    is_list(Tokens),
    attr_word(Tokens, Word),
    memberchk(Word, [aligned, '__aligned__', packed, '__packed__']),
    !.

% packed_attr(+Tokens), aligned_attr(+Tokens): the attribute tokens
% name packed, or aligned.
packed_attr(Tokens) :-
    is_list(Tokens), attr_word(Tokens, Word),
    memberchk(Word, [packed, '__packed__']), !.
aligned_attr(Tokens) :-
    is_list(Tokens), attr_word(Tokens, Word),
    memberchk(Word, [aligned, '__aligned__']), !.

% attr_word(+Tokens, -Word) is nondet: Word is an identifier anywhere in
% an attribute's tokens, looking into groups.
attr_word(Tokens, Word) :-
    member(Token, Tokens),
    (   Token = id(Word)
    ;   Token = group(Group),
        attr_word(Group, Word)
    ).

% base_type(+Specs, -Type, +Env0, -Env): Type from the type specifiers
% alone: either keywords or one named type, never both.
base_type(Specs, Type, Env0, Env) :-
    findall(K, member(tspec(K), Specs), Keywords),
    findall(S, ( member(S, Specs), other_type_spec(S) ), Others),
    (   Others = [Other], Keywords == []
    ->  named_type(Other, Type, Env0, Env)
    ;   Others == []
    ->  keyword_type(Keywords, Type),
        Env = Env0
    ;   Type = bad('conflicting type specifiers'),
        Env = Env0
    ).

other_type_spec(tname(_)).
other_type_spec(su(_, _, _, _)).
other_type_spec(enum(_, _)).
other_type_spec(typeof(_)).
other_type_spec(atomic(_)).

% Clang retains the SysV va_list array/record layout; Fil-C stores its
% capability-bearing cursor in the first word and ignores the rest.
named_type(tname('__builtin_va_list'), array(struct('builtin.va_list'), 1),
           Env, Env) :- !.
named_type(tname(Name), Type, Env, Env) :-
    (   lookup_ordinary(Env, Name, typedef(Type0)) -> Type = Type0
    ;   Type = bad('unknown typedef')
    ).
named_type(typeof(Arg), Type, Env0, Env) :-
    typeof_type(Arg, Type, Env0, Env).
named_type(atomic(TN), Type, Env0, Env) :-
    type_name_type(TN, Type0, Env0, Env),
    reflect_type(TN, Type0, Env, Reflected),
    (   Type0 = bad(_) -> Type = Type0
    ;   Reflected = qualified(_, _)                        % 6.7.2.4p3
    ->  Type = bad('_Atomic of a qualified type')
    ;   atomic_object_type(Type0) -> Type = Type0
    ;   Type = bad('_Atomic of a type other than an integer, pointer, float or double')
    ).

named_type(su(Kind, Tag, Members, Attrs), Type, Env0, Env) :-
    su_type(Members, Kind, Tag, Attrs, Type, Env0, Env).
named_type(enum(Tag, Enumerators), Type, Env0, Env) :-
    enum_type(Enumerators, Tag, Type, Env0, Env).

doc(atomic_object_type(+T), semidet, [
    T: "the unqualified type an _Atomic specifier or qualifier applies to",
    "_Atomic(T) and _Atomic T are the atomic version of T. nanofil takes",
    "an integer, a pointer, float or double: on x86-64 each has the size",
    "and alignment of T, a power of two of at most 8 bytes, which clang",
    "keeps for its atomic version, so the layout is T's. An array or",
    "function type is not allowed; a struct, union or long double, whose",
    "atomic version clang may pad, realign or make a library call, is",
    "refused (bad). Lvalue conversion of an atomic object is an atomic",
    "load and simple assignment an atomic store, both sequentially",
    "consistent; a compound assignment or increment is an atomic",
    "read-modify-write, a cas loop in lowering. Initialization is not",
    "atomic. An _Atomic bit-field, which C leaves to the implementation",
    "and clang rejects, is refused (bad).",
    cites('C11 6.2.5p27'),
    cites('C11 6.2.6.1p9'),
    cites('C11 6.7.2.4p3'),
    cites('C11 6.7.3p3'),
    cites('C11 6.5.16.2p3'),
    cites('C11 7.17.2.1p2'),
    cites('C11 6.7.2.1p5'),
    example(atomic_object_type(int)),
    example(atomic_object_type(ptr(void))),
    example(atomic_object_type(double)),
    fails(atomic_object_type(ldouble)),
    fails(atomic_object_type(struct(1))),
    fails(atomic_object_type(array(int, 2)))
]).
atomic_object_type(T) :- int_type(T), !.
atomic_object_type(ptr(_)).
atomic_object_type(float).
atomic_object_type(double).

% atomic_qualified(+T): the (reflected) type T is atomic at its top.
atomic_qualified(qualified(Qs, _)) :- memberchk(atomic, Qs).

doc(typeof_type(+Arg, -Type, +Env0, -Env), det, [
    Arg: "a typeof specifier's argument: expr(E) or type(TypeName)",
    Type: "the unqualified type it names, as code generation has it",
    Env0: "the scope it is read in",
    Env: "Env0 with any struct, union or enum TypeName defines",
    "The type of expression E, which is not evaluated, or of TypeName",
    "(GNU typeof, C23 typeof). An array or function keeps its type: no",
    "conversion applies. Reflection (reflect_type/4) keeps its",
    "qualifiers. A variably modified type would need E evaluated for its",
    "size, and is refused.",
    cites('C23 6.7.2.5p4'),
    example(( empty_env(E0), bind_ordinary(a, var(none, array(int, 4)), E0, E),
              typeof_type(expr(id(a)), T, E, _) ),
            T = array(int, 4)),
    example(( empty_env(E0), typeof_type(expr(bin(add, num(1, none-dec), chr(65))), T, E0, _) ),
            T = int)
]).
typeof_type(expr(E), Type, Env, Env) :-
    (   expression_type(E, Env, T0)
    ->  (   vm_type(T0) -> Type = bad('typeof a variably modified type')
        ;   unqualified(T0, Type)
        )
    ;   Type = bad('typeof an expression that cannot be typed')
    ).
typeof_type(type(TN), Type, Env0, Env) :-
    type_name_type(TN, Type0, Env0, Env),
    ( vm_type(Type0) -> Type = bad('typeof a variably modified type') ; Type = Type0 ).

% keyword_type(+Keywords, -Type): the type a list of type keywords names.
keyword_type([], int).   % implicit int, as in old headers' K&R style
keyword_type([Keyword|Keywords], Type) :-
    msort([Keyword|Keywords], Sorted),
    (   keyword_combo(Sorted, Type0) -> Type = Type0
    ;   Type = bad('invalid type specifiers')
    ).

% keyword_combo(+SortedKeywords, -Type): the msorted keywords name Type.
keyword_combo([void], void).
keyword_combo([bool], bool).
keyword_combo([char], char).
keyword_combo([char, signed], schar).
keyword_combo([char, unsigned], uchar).
keyword_combo(S, short) :-
    member(S, [[short], [short, signed], [int, short], [int, short, signed]]).
keyword_combo(S, ushort) :-
    member(S, [[short, unsigned], [int, short, unsigned]]).
keyword_combo(S, int) :-
    member(S, [[int], [signed], [int, signed]]).
keyword_combo(S, uint) :-
    member(S, [[unsigned], [int, unsigned]]).
keyword_combo(S, long) :-
    member(S, [[long], [long, signed], [int, long], [int, long, signed]]).
keyword_combo(S, ulong) :-
    member(S, [[long, unsigned], [int, long, unsigned]]).
keyword_combo(S, llong) :-
    member(S, [[long, long], [long, long, signed], [int, long, long],
               [int, long, long, signed]]).
keyword_combo(S, ullong) :-
    member(S, [[long, long, unsigned], [int, long, long, unsigned]]).
keyword_combo([float], float).
keyword_combo([double], double).
keyword_combo([double, long], ldouble).
keyword_combo(S, bad('_Complex')) :- memberchk(complex, S).
keyword_combo(S, bad('__int128')) :- memberchk(int128, S).
keyword_combo(S, bad('_Float16')) :- memberchk(float16, S).
keyword_combo(S, bad('__bf16')) :- memberchk(bf16, S).

%% Structs and unions

% su_type(+Members, +Kind, +Tag, +Attrs, -Type, +Env0, -Env): Members is
% none for a reference to the tag, which declares it if it is not yet
% visible, and otherwise the list of member declarations that define it.
% Tag is some(Name), or none for an anonymous struct or union; a
% reference always has a tag.
su_type([], Kind, Tag, Attrs, Type, Env0, Env) :-
    su_definition([], Kind, Tag, Attrs, Type, Env0, Env).
su_type([Member|Members], Kind, Tag, Attrs, Type, Env0, Env) :-
    su_definition([Member|Members], Kind, Tag, Attrs, Type, Env0, Env).
su_type(none, Kind, some(Name), _, Type, Env0, Env) :-
    (   Env0 = e(_, Tags, _, _),
        get_assoc(Name, Tags, tag(Kind, Id))
    ->  Env = Env0
    ;   new_tag(Kind, some(Name), Id, Env0, Env)
    ),
    Type =.. [Kind, Id].

% su_definition(+Members, +Kind, +Tag, +Attrs, -Type, +Env0, -Env): Type
% is the struct or union Members define, laid out in Env.
su_definition(Members, Kind, Tag, Attrs, Type, Env0, Env) :-
    (   forward_declared(Tag, Kind, Env0, Id)
    ->  Env1 = Env0       % completes a forward declaration in this scope
    ;   new_tag(Kind, Tag, Id, Env0, Env1)
    ),
    Type =.. [Kind, Id],
    foldl(member_decl, Members, Fieldss, Reflectss, Env1, Env2),
    append(Fieldss, Fields),
    append(Reflectss, Reflected),
    (   member(Attr, Attrs), packed_attr(Attr) -> Packing = packed
    ;   Packing = natural
    ),
    (   \+ definition_alignment(Attrs, Env2, _)
    ->  Def = bad('alignment attributes')
    ;   memberchk(bad(Why), Fields)
    ->  known_field_prefix(Fields, Prefix),
        su_layout(Kind, Packing, Prefix, Env2, PrefixDef),
        (   PrefixDef = def(_, Known, _, _)
        ->  Def = partial(Why, Known)
        ;   Def = bad(Why)
        )
    ;   su_layout(Kind, Packing, Fields, Env2, Def0),
        definition_alignment(Attrs, Env2, Request),
        aligned_def(Def0, Request, Def)
    ),
    Env2 = e(Ords, Tags2, Defs0, Next),
    put_assoc(Id, Defs0, Def, Defs1),
    put_assoc(qmembers(Id), Defs1, Reflected, Defs2),
    Env = e(Ords, Tags2, Defs2, Next).

doc(definition_alignment(+Attrs, +Env, -Align), semidet, [
    Attrs: "the attributes of a struct or union definition",
    Env: "the scope it is defined in",
    Align: "the alignment its aligned attributes request, 1 if none",
    "GNU's aligned(N) on a struct or union definition makes its",
    "alignment the larger of N and its members' (packed or not); bare",
    "aligned means the target's biggest alignment, 16 on x86-64 (clang's",
    "__BIGGEST_ALIGNMENT__). N must be a constant power of two. Fails",
    "for an alignment above 4096, which nanofil does not give objects",
    "(max_alignment/1), or a non-constant N.",
    cites('GCC manual, Common Type Attributes, aligned'),
    cites('C11 6.2.8p4'),
    example(( empty_env(E),
              definition_alignment([[group([id(packed), p(','), id(aligned),
                                            group([int(4, none-dec)])])]], E, A) ),
            A = 4),
    example(( empty_env(E), definition_alignment([[group([id('__aligned__')])]], E, A) ),
            A = 16),
    example(( empty_env(E), definition_alignment([], E, A) ), A = 1),
    fails(( empty_env(E),
            definition_alignment([[group([id(aligned), group([int(8192, none-dec)])])]], E, _) )),
    fails(( empty_env(E),
            definition_alignment([[group([id(aligned), group([int(12, none-dec)])])]], E, _) ))
]).
definition_alignment(Attrs, Env, Align) :-
    findall(R, ( member(Attr, Attrs), aligned_entry(Attr, R) ), Requests),
    foldl(requested_alignment(Env), Requests, 1, Align).

% aligned_entry(+Tokens, -Request) is nondet: Request is bare, or
% arg(Ts) with the argument tokens Ts, for each aligned in an
% attribute's Tokens, looking into the __attribute__((...)) groups.
aligned_entry(Tokens, Request) :-
    append(_, [id(Word)|Rest], Tokens),
    memberchk(Word, [aligned, '__aligned__']),
    ( Rest = [group(Ts)|_] -> Request = arg(Ts) ; Request = bare ).
aligned_entry(Tokens, Request) :-
    member(group(Group), Tokens),
    aligned_entry(Group, Request).

requested_alignment(_, bare, A0, A) :- A is max(A0, 16).
requested_alignment(Env, arg(Ts), A0, A) :-
    phrase(flat_tokens(Ts), Flat),
    catch(c_constant_expression(Flat, E), nanofil_error(_), fail),
    catch(const_value(E, Env, N, _), not_constant, fail),
    N > 0, N /\ (N - 1) =:= 0, max_alignment(M), N =< M,
    A is max(A0, N).

% aligned_def(+Def0, +Align, -Def): Def is the definition Def0 with its
% alignment at least Align and its size rounded up to that.
aligned_def(def(Kind, Members, Size0, Align0), Request, def(Kind, Members, Size, Align)) :- !,
    Align is max(Align0, Request),
    Size is (Size0 + Align - 1) // Align * Align.
aligned_def(Def, _, Def).

doc(bit_castable(+From, +To, +Env), semidet, [
    From: "the type of __builtin_bit_cast's operand, after conversion",
    To: "the type it names",
    Env: "the scope",
    "Both are complete object types of one size, and To is not an",
    "array (clang's rule; C has no __builtin_bit_cast). The result has",
    "the operand's bytes, as memcpy into a To would give it (C11 7.24.2.1):",
    "a pointer's bytes keep its address and leave its capability, and",
    "a pointer made from bytes has none, as in Fil-C's clang.",
    cites('C11 6.2.6.1p4'),
    cites('Clang Language Extensions, __builtin_bit_cast'),
    example(( empty_env(E), bit_castable(float, uint, E) )),
    fails(( empty_env(E), bit_castable(int, long, E) )),
    fails(( empty_env(E), bit_castable(long, array(char, 8), E) ))
]).
bit_castable(From, To, Env) :-
    To \= array(_, _), To \= func(_, _, _), To \== void,
    catch(( type_size_align(From, Env, Size, _),
            type_size_align(To, Env, Size, _) ), bad(_), fail).

% A later unsupported member (notably glibc FILE's _flags2 bitfield)
% does not change preceding offsets. Never infer offsets beyond it, or
% a size/alignment for the whole object; those uses must still reject.
known_field_prefix([], []).
known_field_prefix([bad(_)|_], []) :- !.
known_field_prefix([Field|Fields], [Field|Prefix]) :-
    known_field_prefix(Fields, Prefix).

% forward_declared(+Tag, +Kind, +Env, -Id): Tag names the Kind with Id,
% which is declared but not yet defined. An anonymous one never is.
forward_declared(some(Name), Kind, e(_, Tags, Defs, _), Id) :-
    get_assoc(Name, Tags, tag(Kind, Id)),
    get_assoc(Id, Defs, incomplete(_)).

new_tag(Kind, Tag, Id, e(Ords, Tags0, Defs0, Id), e(Ords, Tags, Defs, Next)) :-
    Next is Id + 1,
    tag_bound(Tag, tag(Kind, Id), Tags0, Tags),
    put_assoc(Id, Defs0, incomplete(Tag), Defs).

% tag_bound(+Tag, +Value, +Tags0, -Tags): Tags is Tags0 with the name of
% Tag bound to Value; an anonymous Tag binds nothing.
tag_bound(none, _, Tags, Tags).
tag_bound(some(Name), Value, Tags0, Tags) :- put_assoc(Name, Tags0, Value, Tags).

% member_decl(+Decl, -Fields, -Reflected, +Env0, -Env): Fields are the
% f(Name, Type) or bit-fields b(Name, Type, Width) the member
% declaration Decl declares ([] for a static assertion), or [bad(Why)];
% Name is some(Field), or none for an anonymous member or an unnamed
% bit-field. Reflected are the q(Name, QType) of the named members,
% QType keeping the qualifiers that Type drops.
member_decl(static_assert(Loc, Expr, _), [], [], Env, Env) :-    % C11 6.7.10p2
    (   catch(const_value(Expr, Env, V, _), not_constant, fail)
    ->  ( V =\= 0 -> true ; sema_error(Loc, 'static assertion failed', []) )
    ;   sema_error(Loc, 'static assertion is not a constant', [])
    ).
member_decl(field(Specs0, dcl(Name, SyntaxType, _), Width), Fields,
            Reflected, Env0, Env) :-
    partition(alignment_request, Specs0, Requests, Specs),
    specs_type(Specs, Base, Env0, Env1),
    apply_declarator(SyntaxType, Base, Type, Env1, Env),
    inherited_alignment(Specs, SyntaxType, Env, Inherited),
    member_alignment(Requests, Inherited, Env, MA),
    (   bad_type(Type, Why) -> Fields = [bad(Why)], Reflected = []
    ;   MA = bad(Why) -> Fields = [bad(Why)], Reflected = []
    ;   Width \== none, MA \== none
    ->  Fields = [bad('alignment attributes')], Reflected = []
    ;   vm_type(Type)                                       % 6.7.2.1p9
    ->  Fields = [bad('variably modified member')], Reflected = []
    ;   Width \== none, \+ bitfield_width(Width, Name, Type, Env, _)
    ->  Fields = [bad('invalid bit-field')], Reflected = []
    ;   Width \== none,                                     % 6.7.2.1p5
        reflect_type(type(Specs, SyntaxType), Type, Env, QT), atomic_qualified(QT)
    ->  Fields = [bad('_Atomic bit-field')], Reflected = []
    ;   (   Width == none, MA == none -> Fields = [f(Name, Type)]
        ;   Width == none -> Fields = [f(Name, Type, MA)]
        ;   bitfield_width(Width, Name, Type, Env, W),
            Fields = [b(Name, Type, W)]
        ),
        (   Width \== none, Name == none -> Reflected = []
        ;   reflect_type(type(Specs, SyntaxType), Type, Env, QType),
            Reflected = [q(Name, QType)]
        )
    ).

doc(member_alignment(+Requests, +Inherited, +Env, -MA), det, [
    Requests: "a member's _Alignas specifiers and aligned attributes",
    Inherited: "[align(I)] if its type is a typedef of alignment I (inherited_alignment/4), else []",
    Env: "the scope it is declared in",
    MA: "none, a(Base, Explicit) or bad(Reason)",
    "The member's alignment is Explicit, the strictest request (1 if",
    "none), or Base if that is stricter: its typedef's alignment, or",
    "natural, its type's own. _Alignas and aligned cannot weaken a",
    "member (6.7.5p4), but a typedef's alignment can (GCC's aligned",
    "typedefs). In a packed struct only Explicit counts. Above 4096, or",
    "with a request that is not a constant power of two, the member is",
    "refused (bad).",
    cites('C11 6.7.5p4'),
    cites('GCC manual, Common Type Attributes, aligned'),
    cites('GCC manual, Common Variable Attributes, aligned'),
    example(( empty_env(E), member_alignment([], [], E, MA) ), MA = none),
    example(( empty_env(E),
              member_alignment([attr([group([id(aligned), group([int(32, none-dec)])])])],
                               [], E, MA) ),
            MA = a(natural, 32)),
    example(( empty_env(E), member_alignment([], [align(1)], E, MA) ), MA = a(1, 1)),
    example(( empty_env(E), member_alignment([alignas(expr(num(8192, none-dec)))], [], E, MA) ),
            MA = bad('an alignment above 4096'))
]).
member_alignment([], [], _, none) :- !.
member_alignment(Requests, Inherited, Env, MA) :-
    ( Inherited = [align(B)] -> Base = B ; Base = natural ),
    (   maplist(request_alignment(Env), Requests, As)
    ->  max_list([1|As], Explicit),
        (   max_alignment(M), Explicit > M -> MA = bad('an alignment above 4096')
        ;   MA = a(Base, Explicit)
        )
    ;   MA = bad('alignment attributes')
    ).

alignment_request(alignas(_)).
alignment_request(attr(Tokens)) :- aligned_attr(Tokens).

% flat_tokens(+Tokens)//: attribute Tokens, groups parenthesized again,
% as c_lex tokens.
flat_tokens([]) --> [].
flat_tokens([group(Ts)|Rest]) --> !,
    [tok(p('('), attr)], flat_tokens(Ts), [tok(p(')'), attr)], flat_tokens(Rest).
flat_tokens([T|Rest]) --> [tok(T, attr)], flat_tokens(Rest).

% bitfield_width(+Expr, +Name, +Type, +Env, -W): a bit-field Name of
% Type may have the width Expr, of value W: an integer constant no wider
% than Type, and 0 only without a name (6.7.2.1p4).
bitfield_width(Expr, Name, Type, Env, W) :-
    int_type(Type),
    catch(const_value(Expr, Env, W, _), not_constant, fail),
    int_info(Type, Size, _),
    ( Type == bool -> Max = 1 ; Max is 8 * Size ),
    W >= 0, W =< Max,
    ( W =:= 0 -> Name == none ; true ).

doc(su_layout(+Kind, +Packing, +Fields, +Env, -Def), det, [
    Kind: "struct or union",
    Packing: "natural, or packed for GNU's packed attribute",
    Fields: "the f(Name, Type) and bit-fields b(Name, Type, Width) in order",
    Env: "the scope defining the members' types",
    Def: "the definition: def(Kind, Members, Size, Align), or bad(Why)",
    "The SysV rules: each member at the next multiple of its alignment;",
    "size rounded up to the alignment. A trailing flexible array member",
    "has size 0. A bit-field follows the bits before it unless it would",
    "cross a boundary of its type's size, where it starts instead; a",
    "zero-width one only moves to that boundary. Unnamed bit-fields do not",
    "align the struct. Packed, every member has alignment 1, and so has",
    "the struct; nanofil refuses packed bit-fields, and packed pointers,",
    "whose capabilities Fil-C keeps only at 8-aligned addresses.",
    cites('C11 6.7.2.1p15'),
    example(( empty_env(E), su_layout(struct, natural, [f(some(a), char), f(some(b), int)], E, D) ),
            D = def(struct, [m(some(a), char, 0), m(some(b), int, 4)], 8, 4)),
    example(( empty_env(E), su_layout(struct, packed, [f(some(a), char), f(some(b), int)], E, D) ),
            D = def(struct, [m(some(a), char, 0), m(some(b), int, 1)], 5, 1)),
    example(( empty_env(E), su_layout(union, packed, [f(some(a), char), f(some(b), long)], E, D) ),
            D = def(union, [m(some(a), char, 0), m(some(b), long, 0)], 8, 1)),
    example(( empty_env(E), su_layout(struct, packed, [f(some(p), ptr(int))], E, D) ),
            D = bad('packed pointers')),
    example(( empty_env(E), su_layout(struct, packed, [b(some(x), int, 3)], E, D) ),
            D = bad('packed bit-fields'))
]).
su_layout(Kind, Packing, Fields, Env, Def) :-
    catch(fields_layout(Kind, Packing, Fields, Env, Layout), bad(Why),
          Layout = bad(Why)),
    layout_def(Layout, Kind, Def).

% fields_layout(+Kind, +Packing, +Fields, +Env, -Layout): Layout is
% placed(Members, End, Align) for Fields laid out in Env, or incomplete
% when a field has no size. Throws bad(Why) as type_size_align/4.
fields_layout(_, packed, Fields, _, _) :-
    member(b(_, _, _), Fields), throw(bad('packed bit-fields')).
fields_layout(_, packed, Fields, Env, _) :-
    ( member(f(_, T), Fields) ; member(f(_, T, _), Fields) ),
    holds_pointer(T, Env), throw(bad('packed pointers')).
fields_layout(Kind, Packing, Fields, Env, Layout) :-
    (   foldl(field_member(Kind, Packing, Env), Fields, Memberss, 0-1, EndBits-Align)
    ->  append(Memberss, Members),
        End is (EndBits + 7) // 8,
        Layout = placed(Members, End, Align)
    ;   Layout = incomplete
    ).

% layout_def(+Layout, +Kind, -Def): Def is the definition of a struct or
% union of Kind with Layout, its size rounded up to its alignment.
layout_def(placed(Members, End, Align), Kind, def(Kind, Members, Size, Align)) :-
    Size is (End + Align - 1) // Align * Align.
layout_def(incomplete, _, bad('incomplete member')).
layout_def(bad(Why), _, bad(Why)).

% field_member(+Kind, +Env, +Field, -Members, +End0-Align0, -End-Align):
% Members, the member Field declares or none for an unnamed bit-field,
% are placed after members ending at bit End0 with alignment Align0; End
% and Align include them. Throws bad(Why) as type_size_align/4. Any type
% but a flexible array (array(_, none)) has its own size, so the
% if-then-else keeps that default case.
field_member(Kind, Packing, Env, f(Name, Type), [m(Name, Type, Off)], End0-Align0,
             End-Align) :-
    (   Type = array(ElemType, none)
    ->  type_size_align(ElemType, Env, _, NaturalAlign),
        FieldSize = 0
    ;   type_size_align(Type, Env, FieldSize, NaturalAlign)
    ),
    ( Packing == packed -> FieldAlign = 1 ; FieldAlign = NaturalAlign ),
    member_offset_end(Kind, End0, FieldSize, FieldAlign, Off, End),
    Align is max(Align0, FieldAlign).
field_member(Kind, Packing, Env, f(Name, Type, a(Base, Explicit)), [m(Name, Type, Off)],
             End0-Align0, End-Align) :-
    (   Type = array(ElemType, none)
    ->  type_size_align(ElemType, Env, _, NaturalAlign),
        FieldSize = 0
    ;   type_size_align(Type, Env, FieldSize, NaturalAlign)
    ),
    ( Base == natural -> BaseAlign = NaturalAlign ; BaseAlign = Base ),
    (   Packing == packed -> FieldAlign = Explicit
    ;   FieldAlign is max(BaseAlign, Explicit)
    ),
    (   FieldAlign < 8, holds_pointer(Type, Env)
    ->  throw(bad('underaligned pointers'))
    ;   true
    ),
    member_offset_end(Kind, End0, FieldSize, FieldAlign, Off, End),
    Align is max(Align0, FieldAlign).
field_member(Kind, natural, Env, b(Name, Type, W), Members, End0-Align0, End-Align) :-
    type_size_align(Type, Env, Size, FieldAlign),
    UnitBits is 8 * Size,
    bitfield_start_end(Kind, End0, W, UnitBits, Start, End),
    (   Name == none -> Members = [], Align = Align0
    ;   Unit is Start // UnitBits * Size,
        Pos is Start mod UnitBits,
        Members = [m(Name, Type, Unit, bits(Pos, W))],
        Align is max(Align0, FieldAlign)
    ).

% holds_pointer(+T, +Env): an object of type T holds a pointer.
holds_pointer(ptr(_), _).
holds_pointer(array(T, _), Env) :- holds_pointer(T, Env).
holds_pointer(SU, e(_, _, Defs, _)) :-
    ( SU = struct(Id) ; SU = union(Id) ), !,
    get_assoc(Id, Defs, def(_, Members, _, _)),
    member(M, Members), arg(2, M, T), holds_pointer(T, e(_, _, Defs, _)), !.

doc(unaligned_type(+T, +Env), semidet, [
    T: "a struct or union type",
    Env: "the scope defining it",
    "T has a member, perhaps nested, at an offset that is not a multiple",
    "of its type's alignment, as only a packed struct can. The SysV ABI",
    "then classifies T as MEMORY: passed and returned in memory.",
    cites('SysV x86-64 psABI 3.2.3'),
    example(( empty_env(E0), su_definition([field([tspec(char)], dcl(some(a), base, none), none),
                                            field([tspec(int)], dcl(some(b), base, none), none)],
                                           struct, none, [[group([id(packed)])]], T, E0, E),
              unaligned_type(T, E) )),
    fails(( empty_env(E0), su_definition([field([tspec(int)], dcl(some(b), base, none), none),
                                          field([tspec(char)], dcl(some(a), base, none), none)],
                                         struct, none, [[group([id(packed)])]], T, E0, E),
            unaligned_type(T, E) )),
    fails(( empty_env(E), unaligned_type(struct('builtin.va_list'), E) ))
]).
unaligned_type(SU, e(O, Tg, Defs, N)) :-
    ( SU = struct(Id) ; SU = union(Id) ), !,
    get_assoc(Id, Defs, def(_, Members, _, _)),
    member(M, Members), M = m(_, T, Off),
    catch(type_size_align(T, e(O, Tg, Defs, N), _, Align), bad(_), fail),
    (   Off mod Align =\= 0 -> true ; unaligned_type(T, e(O, Tg, Defs, N)) ), !.
unaligned_type(array(T, _), Env) :- unaligned_type(T, Env).

doc(underaligned_member(+X, +Env, +Width, -Name), semidet, [
    X: "an object tree",
    Env: "the scope of X",
    Width: "the byte width of an atomic access to X",
    Name: "the member, perhaps containing X, that may be misaligned",
    "X is a member, perhaps nested, of a struct or union aligned to less",
    "than Width, or at an offset that is not a multiple of it, as only a",
    "packed one can be: clang then lowers an atomic read-modify-write of",
    "X to libatomic's lock-based calls, which nanofil does not have, so",
    "lowering refuses it rather than trap on Fil-C's alignment check.",
    cites('C11 7.17.6p1'),
    example(( empty_env(E0), su_definition([field([tspec(char)], dcl(some(c), base, none), none),
                                            field([tspec(int)], dcl(some(x), base, none), none)],
                                           struct, none, [[group([id(packed)])]], T, E0, E),
              underaligned_member(obj(int, member(obj(T, id(ps)), x)), E, 4, N) ),
            N = x),
    fails(( empty_env(E0), su_definition([field([tspec(char)], dcl(some(c), base, none), none),
                                          field([tspec(int)], dcl(some(x), base, none), none)],
                                         struct, none, [], T, E0, E),
            underaligned_member(obj(int, member(obj(T, id(s)), x)), E, 4, _) ))
]).
underaligned_member(obj(_, member(XS, F)), Env, W, Name) :-
    tree_type(XS, SU0), unqualified(SU0, SU),
    (   catch(type_size_align(SU, Env, _, A), bad(_), fail), A < W -> Name = F
    ;   member_layout(SU, F, Env, _, Off, _), Off mod W =\= 0 -> Name = F
    ;   underaligned_member(XS, Env, W, Name)
    ).

% member_offset_end(+Kind, +End0, +Size, +Align, -Off, -End): a member of
% Size and Align after members ending at bit End0 is at byte Off and
% ends the struct or union so far at bit End.
member_offset_end(struct, End0, Size, Align, Off, End) :-
    Off is ((End0 + 7) // 8 + Align - 1) // Align * Align,
    End is 8 * (Off + Size).
member_offset_end(union, End0, Size, _, 0, End) :-
    End is max(End0, 8 * Size).

% bitfield_start_end(+Kind, +End0, +W, +UnitBits, -Start, -End): a
% bit-field of W bits, in units of UnitBits, after bits ending at End0
% occupies bits Start to End.
bitfield_start_end(union, End0, W, _, 0, End) :- End is max(End0, W).
bitfield_start_end(struct, End0, W, UnitBits, Start, End) :-
    (   W > 0, End0 // UnitBits =:= (End0 + W - 1) // UnitBits
    ->  Start = End0
    ;   Start is (End0 + UnitBits - 1) // UnitBits * UnitBits
    ),
    End is Start + W.

%% Enums

% enum_type(+Enumerators, +Tag, -Type, +Env0, -Env): Type is the enum's
% underlying type. Enumerators is none for a reference to Tag, and
% otherwise the list that defines it; a reference to an unknown enum tag
% has type uint. Tag is some(Name) or none, as in su_type/7.
enum_type([], Tag, Type, Env0, Env) :-
    enum_definition([], Tag, Type, Env0, Env).
enum_type([Enumerator|Enumerators], Tag, Type, Env0, Env) :-
    enum_definition([Enumerator|Enumerators], Tag, Type, Env0, Env).
enum_type(none, some(Name), Type, Env, Env) :-
    (   Env = e(_, Tags, _, _),
        get_assoc(Name, Tags, enum(Type0))
    ->  Type = Type0
    ;   Type = uint
    ).

% enum_definition(+Enumerators, +Tag, -Type, +Env0, -Env): Type is the
% underlying type of the enum Enumerators define; Env binds its
% constants and its tag.
enum_definition(Enumerators, Tag, Type, Env0, Env) :-
    foldl(enumerator, Enumerators, Values, Env0-0, Env1-_),
    enum_underlying(Values, Type),
    Env1 = e(Ords, Tags0, Defs, Next),
    tag_bound(Tag, enum(Type), Tags0, Tags),
    Env = e(Ords, Tags, Defs, Next).

% enumerator(+Enumerator, -V, +Env0-Next0, -Env-Next): V is the
% constant's value, Next0 when it has no expression, and Env binds it.
% Each constant has type int when it fits, as C requires of constants
% whose values fit; the enum's own type follows clang.
enumerator(enumerator(Name, Expr), V, Env0-Next, Env-Next1) :-
    (   Expr == none -> V = Next
    ;   const_value(Expr, Env0, V, _)
    ),
    Next1 is V + 1,
    (   V >= -2147483648, V =< 2147483647 -> ConstType = int
    ;   ConstType = long
    ),
    bind_ordinary(Name, enumconst(V, ConstType), Env0, Env).

%! enum_underlying(+Values, -Type) is det.
%
%  Type is the type clang gives an enum whose constants have Values: the
%  first of uint, int, ulong and long that holds them all (uint when
%  there are none).

enum_underlying([], uint).
enum_underlying([V|Vs], Type) :-
    min_list([V|Vs], Lo),
    max_list([V|Vs], Hi),
    (   Lo >= 0, Hi =< 4294967295 -> Type = uint
    ;   Lo >= -2147483648, Hi =< 2147483647 -> Type = int
    ;   Lo >= 0 -> Type = ulong
    ;   Type = long
    ).

%% Declarators

doc(apply_declarator(+SyntaxType, +Base, -Type, +Env0, -Env), det, [
    SyntaxType: "a declarator's type, built by the parser outermost first around the atom base",
    Base: "the type the declaration specifiers name",
    Type: "the declared type",
    Env0: "the scope",
    Env: "Env0 with the struct and union definitions of any parameter list",
    "Array sizes are evaluated and parameter types resolved. A size that",
    "is not an integer constant expression, or `[*]`, makes a variable",
    "length array, whose size expression lowering evaluates; a negative",
    "constant size is bad. Parameter names are in scope for the size",
    "expressions of the parameters after them, and only there.",
    cites('C11 6.7.6.2p4'),
    cites('C11 6.2.1p4'),
    example(( empty_env(E), apply_declarator(array(base, num(3, none-dec)), int, T, E, _) ),
            T = array(int, 3)),
    example(( empty_env(E), apply_declarator(array(base, id(n)), int, T, E, _) ),
            T = array(int, vla(id(n)))),
    example(( empty_env(E), apply_declarator(ptr(array(base, star), []), int, T, E, _) ),
            T = ptr(array(int, vla(star)))),
    example(( empty_env(E), apply_declarator(array(base, un(neg, num(1, none-dec))), int, T, E, _) ),
            T = bad('negative array size')),
    example(( empty_env(E0), bind_ordinary(n, enumconst(4, int), E0, E),
              apply_declarator(func(base, params([param([tspec(int)], dcl(some(n), base, none)),
                                                  param([tspec(int)], dcl(some(a), ptr(array(base, id(n)), []), none))],
                                                 fixed)),
                               int, T, E, _) ),
            T = func(int, [int, ptr(array(int, vla(id(n))))], fixed))
]).
apply_declarator(base, Base, Base, Env, Env).
apply_declarator(ptr(Syntax, _), Base, ptr(Type), Env0, Env) :-
    apply_declarator(Syntax, Base, Type, Env0, Env).
apply_declarator(array(Syntax, SizeExpr), Base, Type, Env0, Env) :-
    apply_declarator(Syntax, Base, ElemType, Env0, Env),
    (   SizeExpr == none
    ->  Type = array(ElemType, none)
    ;   SizeExpr == star
    ->  Type = array(ElemType, vla(star))
    ;   catch(const_value(SizeExpr, Env, N, _), not_constant, fail)
    ->  ( N >= 0 -> Type = array(ElemType, N) ; Type = bad('negative array size') )
    ;   Type = array(ElemType, vla(SizeExpr))
    ).
apply_declarator(func(Syntax, Params), Base, func(Ret, ParamTypes, Variadic),
          Env0, Env) :-
    apply_declarator(Syntax, Base, Ret, Env0, Env1),
    param_types(Params, ParamTypes, Variadic, Env1, Env).

% param_types(+Params, -Types, -Variadic, +Env0, -Env): Types are the
% adjusted parameter types. Parameter declarations are scoped to the
% parameter list.
param_types(unspecified, unspecified, fixed, Env, Env).
param_types(params(Params, Variadic), Types, Variadic, Env0, Env) :-
    env_scope(Env0, Scope, _),
    foldl(param_type, Params, Types, Env0, Env1),
    env_restore(Scope, Env1, Env).

param_type(param(Specs, dcl(Name, SyntaxType, _)), Type, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    apply_declarator(SyntaxType, Base, Type0, Env1, Env2),
    type_adjusted(Type0, Type1),
    ( transparent_first(Type1, Env2, First, _) -> Type = First ; Type = Type1 ),
    (   Name = some(N) -> bind_ordinary(N, var(none, Type), Env2, Env)
    ;   Env = Env2
    ).

doc(transparent_first(+Union, +Env, -First, -Reflected), semidet, [
    Union: "a parameter's type, a union marked transparent_union",
    Env: "the scope",
    First: "the type of its first member, which the parameter has instead",
    Reflected: "First with its qualifiers, as reflection keeps them",
    "GNU C passes a transparent union argument as its first member, and",
    "accepts an argument of any member's type. nanofil supports the",
    "unions glibc's socket functions take with _GNU_SOURCE, whose members",
    "are all pointers: the parameter is a pointer, and any member's",
    "pointer converts to it. A union with a non-pointer member stays a",
    "union, so an argument of a member's type is refused.",
    cites('GCC manual, Common Type Attributes, transparent_union')
]).
transparent_first(union(Id), e(_, _, Defs, _), First, Reflected) :-
    get_assoc(transparent(Id), Defs, t),
    get_assoc(Id, Defs, def(union, [m(_, First, 0)|Ms], _, _)),
    First = ptr(_),
    \+ ( member(m(_, T, _), Ms), T \= ptr(_) ),
    get_assoc(qmembers(Id), Defs, [q(_, Reflected0)|_]),
    value_type(Reflected0, Reflected).

% transparent_typedef(+Specs, +Type, +Env0, -Env): a typedef of a union
% with the transparent_union attribute marks the union so.
transparent_typedef(Specs, union(Id), e(O, T, Defs0, N), e(O, T, Defs, N)) :-
    member(attr(Tokens), Specs), is_list(Tokens), attr_word(Tokens, Word),
    memberchk(Word, [transparent_union, '__transparent_union__']), !,
    put_assoc(transparent(Id), Defs0, t, Defs).
transparent_typedef(_, _, Env, Env).

% type_adjusted(+Type0, -Type): a parameter declared with Type0 has
% Type. Every other type is its own adjustment: a default case over the
% exported type terms, so the cuts stay.
type_adjusted(array(T, _), ptr(T)) :- !.
type_adjusted(func(R, P, V), ptr(func(R, P, V))) :- !.
type_adjusted(T, T).

%! type_name_type(+TypeName, -Type, +Env0, -Env) is det.
%
%  Type is the type the type name TypeName (as in a cast or sizeof)
%  denotes; Env is Env0 with any tag it defines.

type_name_type(type(Specs, SyntaxType), Type, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    apply_declarator(SyntaxType, Base, Type, Env1, Env).

doc(arith_size(+Elem, +Env, -Size), det, [
    Elem: "the pointed-to type of a pointer in arithmetic",
    Env: "the scope",
    Size: "the bytes one step of the pointer moves",
    "The size of Elem, as type_size_align/4 gives it (and throws). GNU C",
    "also lets a pointer to void step by one byte, as clang does with a",
    "warning; dash's stackblock() + n relies on it. ISO C requires a",
    "complete object type.",
    cites('C11 6.5.6p2'),
    cites('GCC manual, Pointer Arithmetic'),
    example(( empty_env(E), arith_size(void, E, S) ), S = 1),
    example(( empty_env(E), arith_size(long, E, S) ), S = 8)
]).
arith_size(Elem, Env, Size) :-
    (   unqualified(Elem, void) -> Size = 1
    ;   type_size_align(Elem, Env, Size, _)
    ).

doc(vm_type(+T), semidet, [
    T: "a type",
    "T is variably modified: a variable length array type, or a type",
    "derived from one by pointers, arrays, or a function's return or",
    "parameter types.",
    cites('C11 6.7.6p3'),
    example(vm_type(ptr(array(int, vla(id(n)))))),
    example(vm_type(func(int, [int, ptr(array(int, dyn(tmp(v1))))], fixed))),
    example(vm_type(qualified([const], array(array(int, vla(star)), 2)))),
    fails(vm_type(ptr(array(int, 3)))),
    fails(vm_type(array(int, none)))
]).
vm_type(qualified(_, T)) :- vm_type(T).
vm_type(ptr(T)) :- vm_type(T).
vm_type(array(T, N)) :- ( variable_size(N) -> true ; vm_type(T) ).
vm_type(func(Ret, Params, _)) :-
    (   vm_type(Ret)
    ;   is_list(Params),
        member(Param, Params),
        vm_type(Param)
    ),
    !.

% variable_size(+N): array length N is not a constant: unevaluated or
% evaluated at run time.
variable_size(vla(_)).
variable_size(dyn(_)).

doc(vla_type(+T), semidet, [
    T: "a type",
    "T is a variable length array type: an array whose size is not an",
    "integer constant expression, or whose element type has no constant",
    "size. A pointer to one is variably modified but has a constant size.",
    cites('C11 6.7.6.2p4'),
    example(vla_type(array(int, dyn(tmp(v1))))),
    example(vla_type(array(array(int, vla(id(n))), 3))),
    example(vla_type(qualified([const], array(int, vla(star))))),
    fails(vla_type(ptr(array(int, vla(id(n)))))),
    fails(vla_type(array(int, 3)))
]).
vla_type(qualified(_, T)) :- vla_type(T).
vla_type(array(T, N)) :- ( variable_size(N) -> true ; vla_type(T) ).

doc(unsupported_type(+T, -Format, -Args), semidet, [
    T: "a type an expression or declaration names",
    Format: "the diagnostic's format",
    Args: "its arguments",
    "nanofil does not support T: it has no values nanofil can hold.",
    example(unsupported_type(bad('_Complex'), '~w is not supported', ['_Complex'])),
    fails(unsupported_type(ldouble, _, _)),
    fails(unsupported_type(ptr(bad('_Complex')), _, _)),
    fails(unsupported_type(array(int, vla(id(n))), _, _))
]).
unsupported_type(T, '~w is not supported', [Why]) :-
    unsupported_value_type(T, Why).

% unsupported_value_type(+Type, -Why): nanofil has no values of Type,
% for the reason Why.
unsupported_value_type(bad(Why), Why).
unsupported_value_type(array(T, _), Why) :- unsupported_value_type(T, Why).

% bad_type(+T, -Why): bad(Why) is the first bad type inside T, if any
% (not through pointers, which may point at anything).
bad_type(bad(Why), Why).
bad_type(array(T, _), Why) :- bad_type(T, Why).
bad_type(func(Ret, Params, _), Why) :-
    (   bad_type(Ret, Why) -> true
    ;   is_list(Params),
        member(Param, Params),
        bad_type(Param, Why)
    ).

%% Sizes

%! type_size_align(+Type, +Env, -Size, -Align) is det.
%
%  Size and Align are the size and alignment in bytes of Type in Env.
%  Throws bad(Why) for a bad or incomplete type.
type_size_align(Type, Env, Size, Align) :-
    (   size_align_(Type, Env, Size0, Align0) -> Size = Size0, Align = Align0
    ;   throw(bad(incomplete))
    ).

size_align_(qualified(_, T), Env, Size, Align) :-
    type_size_align(T, Env, Size, Align).
size_align_(bool, _, 1, 1).
size_align_(char, _, 1, 1).
size_align_(schar, _, 1, 1).
size_align_(uchar, _, 1, 1).
size_align_(short, _, 2, 2).
size_align_(ushort, _, 2, 2).
size_align_(int, _, 4, 4).
size_align_(uint, _, 4, 4).
size_align_(long, _, 8, 8).
size_align_(ulong, _, 8, 8).
size_align_(llong, _, 8, 8).
size_align_(ullong, _, 8, 8).
size_align_(float, _, 4, 4).
size_align_(double, _, 8, 8).
size_align_(ldouble, _, 16, 16).
size_align_(ptr(_), _, 8, 8).
size_align_(array(_, N), _, _, _) :-
    variable_size(N),
    throw(bad('variable length array')).
size_align_(array(T, N), Env, Size, Align) :-
    integer(N),
    type_size_align(T, Env, ElemSize, Align),
    Size is ElemSize * N.
size_align_(struct(Id), Env, Size, Align) :- su_size(Id, Env, Size, Align).
size_align_(union(Id), Env, Size, Align) :- su_size(Id, Env, Size, Align).
size_align_(bad(Why), _, _, _) :- throw(bad(Why)).

% su_size(+Id, +Env, -Size, -Align): the struct or union Id has Size and
% Align. Fails when it is incomplete; throws bad(Why) when it is bad.
su_size(Id, e(_, _, Defs, _), Size, Align) :-
    get_assoc(Id, Defs, Def),
    def_size_align(Def, Size, Align).

def_size_align(def(_, _, Size, Align), Size, Align).
def_size_align(partial(Why, _), _, _) :-
    throw(bad(Why)).
def_size_align(bad(Why), _, _) :-
    throw(bad(Why)).

%! complete_type(+Type, +Env) is semidet.
%
%  Type is complete in Env: it has a size.

complete_type(Type, Env) :- catch(type_size_align(Type, Env, _, _), bad(_), fail).

%! member_type_offset(+SU, +Name, +Env, -Type, -Offset) is semidet.
%
%  The struct or union type SU has a member Name of Type at Offset,
%  looking into anonymous members. Fails if it has none, if Name is a
%  bit-field, or if SU is not defined.
member_type_offset(SU, Name, Env, Type, Off) :-
    member_layout(SU, Name, Env, Type, Off, none).

doc(member_layout(+SU, +Name, +Env, -Type, -Off, -Bits), semidet, [
    SU: "an unqualified struct or union type",
    Name: "a member name",
    Env: "the scope that defines SU",
    Type: "the member's type",
    Off: "the byte offset of the member, or of the Type that holds a bit-field",
    Bits: "none, or bits(Pos, Width) for a bit-field of Width bits from bit Pos",
    "Looks into anonymous members. A bit-field follows the bits before it",
    "unless it would cross a boundary of its type's size; a member that is",
    "not a bit-field starts at the next byte its alignment allows.",
    cites('C11 6.7.2.1p11'),
    cites('SysV x86-64 psABI 3.1.2, Bit-Fields'),
    example(( empty_env(E0),
              specs_type([su(struct, none,
                  [field([tspec(char)], dcl(some(c), base, none), none),
                   field([tspec(int)], dcl(some(a), base, none), num(3, none-dec)),
                   field([tspec(int)], dcl(some(b), base, none), num(30, none-dec))],
                  [])], S, E0, E),
              member_layout(S, a, E, T, Off, Bits) ),
            (T = int, Off = 0, Bits = bits(8, 3))),
    example(( empty_env(E0),
              specs_type([su(struct, none,
                  [field([tspec(char)], dcl(some(c), base, none), none),
                   field([tspec(int)], dcl(some(a), base, none), num(3, none-dec)),
                   field([tspec(int)], dcl(some(b), base, none), num(30, none-dec))],
                  [])], S, E0, E),
              member_layout(S, b, E, T, Off, Bits) ),
            (T = int, Off = 4, Bits = bits(0, 30))),
    example(( empty_env(E0),
              specs_type([su(struct, none,
                  [field([tspec(int)], dcl(none, base, none), num(8, none-dec)),
                   field([tspec(char)], dcl(some(c), base, none), none)],
                  [])], S, E0, E),
              member_layout(S, c, E, T, Off, Bits), type_size_align(S, E, Size, Align) ),
            (T = char, Off = 1, Bits = none, Size = 2, Align = 1)),
    fails(( empty_env(E0),
            specs_type([su(struct, none,
                [field([tspec(int)], dcl(some(a), base, none), num(3, none-dec))],
                [])], S, E0, E),
            member_type_offset(S, a, E, _, _) ))
]).
member_layout(SU, Name, Env, Type, Off, Bits) :-
    SU =.. [_, Id],
    Env = e(_, _, Defs, _),
    get_assoc(Id, Defs, Def),
    known_members(Def, Members),
    (   member(M, Members), named_member(M, Name, Type, Off, Bits) -> true
    ;   member(m(none, AnonType, AnonOff), Members),
        member_layout(AnonType, Name, Env, Type, InnerOff, Bits)
    ->  Off is AnonOff + InnerOff
    ).

named_member(m(some(Name), Type, Off), Name, Type, Off, none).
named_member(m(some(Name), Type, Off, Bits), Name, Type, Off, Bits).

known_members(def(_, Members, _, _), Members).
known_members(partial(_, Members), Members).

%% Integers

doc(int_type(+Type), semidet, [
    Type: "a type term",
    also(int_type(-Type), multi),
    "Type is an integer type: bool, the character types, and the standard",
    "signed and unsigned integer types.",
    cites('C11 6.2.5p17'),
    example(int_type(bool)),
    fails(int_type(double)),
    fails(int_type(ptr(int))),
    example(findall(T, int_type(T), Ts), length(Ts, 12))
]).
int_type(T) :- int_info(T, _, _).

doc(integer_type(?(Type), ?(Size), ?(Signedness), ?(Rank)), nondet, [
    Type: "an integer type",
    Size: "its width in bytes",
    Signedness: "signed or unsigned",
    Rank: "its integer conversion rank, from 0 for bool to 5 for long long",
    "C's integer types on x86-64 Linux. Plain char is signed, long is as",
    "wide as long long, and the three character types share a rank.",
    cites('C11 6.3.1.1p1'),
    example(integer_type(long, S, G, R), (S = 8, G = signed, R = 4)),
    example(findall(T, integer_type(T, 8, unsigned, _), Ts), Ts = [ulong, ullong])
]).
integer_type(bool,   1, unsigned, 0).
integer_type(char,   1, signed,   1).
integer_type(schar,  1, signed,   1).
integer_type(uchar,  1, unsigned, 1).
integer_type(short,  2, signed,   2).
integer_type(ushort, 2, unsigned, 2).
integer_type(int,    4, signed,   3).
integer_type(uint,   4, unsigned, 3).
integer_type(long,   8, signed,   4).
integer_type(ulong,  8, unsigned, 4).
integer_type(llong,  8, signed,   5).
integer_type(ullong, 8, unsigned, 5).

doc(int_info(?(Type), ?(Size), ?(Signedness)), nondet, [
    Type: "an integer type",
    Size: "its width in bytes",
    Signedness: "signed or unsigned",
    "integer_type/4 without the rank.",
    example(int_info(uchar, S, G), (S = 1, G = unsigned))
]).
int_info(Type, Size, Sign) :- integer_type(Type, Size, Sign, _).

doc(rank(?(Type), ?(Rank)), nondet, [
    Type: "an integer type",
    Rank: "its integer conversion rank",
    example(rank(schar, R), R = 1)
]).
rank(Type, Rank) :- integer_type(Type, _, _, Rank).

doc(unsigned_of(+Signed, -Unsigned), semidet, [
    Signed: "a signed integer type",
    Unsigned: "the unsigned type of the same rank",
    cites('C11 6.2.5p6'),
    example(unsigned_of(llong, U), U = ullong),
    example(unsigned_of(char, U), U = uchar),
    fails(unsigned_of(uint, _))
]).
unsigned_of(S, U) :-
    integer_type(S, Size, signed, R), integer_type(U, Size, unsigned, R).

doc(scalar_type(+Type), semidet, [
    Type: "a type term",
    "Type is an integer, floating-point or pointer type: one that has an",
    "IR class.",
    cites('C11 6.2.5p21'),
    example(scalar_type(ptr(char))),
    fails(scalar_type(struct(1)))
]).
scalar_type(T) :- type_class(T, _).

doc(float_type(?(Type)), nondet, [
    Type: "a real floating type",
    "The real floating types. long double is the x87 80-bit extended",
    "format, as in clang for x86-64 (class x): sizeof 16, alignment 16,",
    "64 significand bits, LDBL_MANT_DIG (docs/float.md).",
    cites('C11 6.2.5p10'),
    cites('C11 F.2p1'),
    example(float_type(ldouble)),
    fails(float_type(int))
]).
float_type(float).
float_type(double).
float_type(ldouble).

doc(arithmetic_type(+Type), semidet, [
    Type: "a type term",
    "Type is an integer or floating type.",
    cites('C11 6.2.5p18'),
    example(arithmetic_type(bool)),
    fails(arithmetic_type(ptr(int)))
]).
arithmetic_type(T) :- int_type(T).
arithmetic_type(T) :- float_type(T).

doc(default_promotion(+Type, -Promoted), det, [
    Type: "the type of an argument with no parameter type",
    Promoted: "the type it is passed as",
    "The default argument promotions: float becomes double, and the",
    "integer promotions apply to the rest.",
    cites('C11 6.5.2.2p6'),
    example(default_promotion(float, P), P = double),
    example(default_promotion(char, P), P = int),
    example(default_promotion(ptr(int), P), P = ptr(int))
]).
default_promotion(float, double) :- !.
default_promotion(T, P) :- integer_promotion(T, P).

doc(integer_promotion(+Type, -Promoted), det, [
    Type: "the type of an operand",
    Promoted: "its type after the integer promotions",
    "int for an integer type of rank below int, which int can always",
    "represent here, otherwise Type itself, also for a type that is not",
    "an integer.",
    cites('C11 6.3.1.1p2'),
    example(integer_promotion(ushort, P), P = int),
    example(integer_promotion(bool, P), P = int),
    example(integer_promotion(uint, P), P = uint),
    example(integer_promotion(double, P), P = double)
]).
integer_promotion(T, P) :-
    (   rank(T, R), R < 3 -> P = int
    ;   P = T
    ).

doc(usual_arith_conversion(+TypeA, +TypeB, -Type), semidet, [
    TypeA: "the type of one arithmetic operand",
    TypeB: "the type of the other",
    Type: "their common real type",
    "The usual arithmetic conversions. A floating operand wins; otherwise",
    "both are promoted, and when the signedness differs the unsigned type",
    "wins unless the signed one is wider. A signed type exactly as wide",
    "as a higher-ranked unsigned one gives way to its own unsigned type.",
    cites('C11 6.3.1.8p1'),
    example(usual_arith_conversion(int, double, T), T = double),
    example(usual_arith_conversion(double, ldouble, T), T = ldouble),
    example(usual_arith_conversion(ldouble, float, T), T = ldouble),
    example(usual_arith_conversion(float, long, T), T = float),
    example(usual_arith_conversion(char, short, T), T = int),
    example(usual_arith_conversion(int, uint, T), T = uint),
    example(usual_arith_conversion(uint, long, T), T = long),
    example(usual_arith_conversion(long, ullong, T), T = ullong),
    example(usual_arith_conversion(llong, ulong, T), T = ullong),
    fails(usual_arith_conversion(ptr(int), int, _))
]).
usual_arith_conversion(TypeA0, TypeB0, Type) :-
    arithmetic_type(TypeA0), arithmetic_type(TypeB0),
    ( TypeA0 == ldouble ; TypeB0 == ldouble ), !,
    Type = ldouble.
usual_arith_conversion(TypeA0, TypeB0, Type) :-
    arithmetic_type(TypeA0), arithmetic_type(TypeB0),
    ( TypeA0 == double ; TypeB0 == double ), !,
    Type = double.
usual_arith_conversion(TypeA0, TypeB0, float) :-
    arithmetic_type(TypeA0), arithmetic_type(TypeB0),
    ( TypeA0 == float ; TypeB0 == float ), !.
usual_arith_conversion(TypeA0, TypeB0, Type) :-
    integer_promotion(TypeA0, A),
    integer_promotion(TypeB0, B),
    int_info(A, SizeA, SignA),
    int_info(B, SizeB, SignB),
    rank(A, RankA),
    rank(B, RankB),
    (   A == B -> Type = A
    ;   SignA == SignB -> ( RankA >= RankB -> Type = A ; Type = B )
    ;   SignA == unsigned, RankA >= RankB -> Type = A
    ;   SignB == unsigned, RankB >= RankA -> Type = B
    ;   SignA == signed, SizeA > SizeB -> Type = A
    ;   SignB == signed, SizeB > SizeA -> Type = B
    ;   SignA == signed -> unsigned_of(A, Type)
    ;   unsigned_of(B, Type)
    ).

doc(convert_int(+V, +Type, -W), semidet, [
    V: "an integer",
    Type: "an integer type",
    W: "V converted to Type",
    "Conversion wraps modulo the width, as the standard requires for",
    "unsigned types and GCC and clang define for signed ones; bool is",
    "0 or 1. Fails when Type is not an integer type. The cut commits to",
    "bool, which int_info/3 also describes as a byte.",
    cites('C11 6.3.1.2p1'),
    cites('C11 6.3.1.3p2'),
    example(convert_int(300, uchar, W), W = 44),
    example(convert_int(256, bool, W), W = 1),
    example(convert_int(-1, uint, W), W = 4294967295),
    example(convert_int(128, schar, W), W = -128),
    fails(convert_int(1, double, _))
]).
convert_int(V, bool, W) :- !, ( V =:= 0 -> W = 0 ; W = 1 ).
convert_int(V, Type, W) :-
    int_info(Type, Size, Sign),
    M is 1 << (8 * Size),
    U is V mod M,
    signed_word(Sign, U, M, W).

doc(signed_word(+Signedness, +U, +M, -W), det, [
    Signedness: "signed or unsigned",
    U: "a word, 0 =< U < M",
    M: "the modulus of the word",
    W: "the value of U read with Signedness",
    example(signed_word(signed, 255, 256, W), W = -1),
    example(signed_word(unsigned, 255, 256, W), W = 255)
]).
signed_word(signed, U, M, W) :- ( U >= M >> 1 -> W is U - M ; W = U ).
signed_word(unsigned, U, _, U).

doc(type_class(?(Type), ?(Class)), nondet, [
    Type: "a scalar type",
    Class: "its IR class",
    "w for an integer type of at most 4 bytes, l for an 8-byte one, p for",
    "a pointer, s and d for float and double, x for long double.",
    "Deterministic when Type is bound.",
    example(type_class(ushort, K), K = w),
    example(type_class(ullong, K), K = l),
    example(type_class(ptr(void), K), K = p),
    example(type_class(float, K), K = s),
    example(type_class(ldouble, K), K = x),
    fails(type_class(struct(0), _))
]).
type_class(T, K) :- integer_type(T, Size, _, _), ( Size =:= 8 -> K = l ; K = w ).
type_class(float, s).
type_class(double, d).
type_class(ldouble, x).
type_class(ptr(_), p).

%% Arithmetic constant expressions

/*  A constant expression has a type and a value: an integer, IEEE bits
    for float/double, or ub where evaluating it is undefined (integer
    division by zero). Operators propagate ub, except from operands that && ||
    and ?: do not evaluate (C11 6.6p3): 1 || 1/0 is 1, and 1/0 alone is
    not constant. Every operand must still be a constant expression.

    The environment is a c_types environment, or pp for a #if expression,
    where every integer type acts as intmax_t or uintmax_t (6.10.1p4): a
    constant is a long or ulong, and so is the result of ! == && and
    the like. The preprocessor has replaced identifiers by 0. */

%! const_value(+Expr, +Env, -Value, -Type) is det.
%
%  Expr is an integer constant expression with Value of Type in Env.
%  Throws not_constant when Expr is not one.
const_value(Expr, Env, V, T) :-
    constant_value(Expr, Env, V, T),
    ( int_type(T) -> true ; throw(not_constant) ).

% Float constants use their unsigned IEEE bits, never a host float.
constant_value(Expr, Env, V, T) :-
    (   const_eval(Expr, Env, V0, T0), integer(V0) -> V = V0, T = T0
    ;   throw(not_constant)
    ).

float_literal(Cs, Bits, Type) :-
    append(Body, [Suffix], Cs),
    ( memberchk(Suffix, [f, 'F']) -> Type = float, Digits = Body
    ; memberchk(Suffix, [l, 'L']) -> Type = ldouble, Digits = Body
    ; Type = double, Digits = Cs
    ),
    type_class(Type, K), ieee:ieee_parse(K, Digits, Bits).

% glibc's HUGE_VAL and INFINITY are builtin constant expressions, not
% libm calls. Keep the value bits exact, including in static storage.
float_builtin('__builtin_huge_val', double, 0x7ff0000000000000).
float_builtin('__builtin_inf', double, 0x7ff0000000000000).
float_builtin('__builtin_huge_valf', float, 0x7f800000).
float_builtin('__builtin_inff', float, 0x7f800000).
float_builtin('__builtin_huge_vall', ldouble, 0x7fff8000000000000000).
float_builtin('__builtin_infl', ldouble, 0x7fff8000000000000000).
float_builtin(Name, T, V) :- nan_builtin(Name, T, V).

doc(nan_builtin(?(Name), ?(Type), ?(Bits)), nondet, [
    Name: "a GNU NaN builtin",
    Type: "float, double or long double",
    Bits: "the IEEE bits of its value (x87's 80 for long double)",
    "__builtin_nan(\"\"), __builtin_nanf(\"\") and __builtin_nanl(\"\"), glibc's NAN, are",
    "constant expressions: the quiet NaN of Type with a zero payload, as",
    "nan(\"\") is. Only the empty string is accepted; a payload string",
    "would name other bits.",
    cites('GCC manual, Other Built-in Functions'),
    cites('C11 7.12.11.2p2'),
    example(nan_builtin('__builtin_nanf', T, V), (T = float, V = 0x7fc00000)),
    fails(nan_builtin('__builtin_inff', _, _))
]).
nan_builtin('__builtin_nan', double, 0x7ff8000000000000).
nan_builtin('__builtin_nanf', float, 0x7fc00000).
nan_builtin('__builtin_nanl', ldouble, 0x7fffc000000000000000).

doc(const_convert(+V, +From, +To, ?(W)), semidet, [
    V: "a constant's value: an integer, float bits, or ub",
    From: "its arithmetic type",
    To: "an arithmetic type",
    W: "V converted to To",
    "An undefined float-to-int conversion gives ub, like integer division",
    "by zero, and ub stays ub. W may be bound: a null pointer constant is",
    "asked for the value 0, and ub is then not 0.",
    cites('C11 6.3.1.2p1'),
    cites('C11 6.3.1.3p2'),
    cites('C11 6.3.1.4p1'),
    example(const_convert(300, int, uchar, W), W = 44),
    example(const_convert(-1, int, int, W), W = -1),
    example(const_convert(2, int, bool, W), W = 1),
    example(const_convert(0x41200000, float, int, W), W = 10),
    example(const_convert(0x7f800000, float, int, W), W == ub),
    example(const_convert(ub, int, llong, W), W == ub),
    fails(const_convert(ub, int, llong, 0))
]).
const_convert(V0, _, _, V) :- V0 == ub, !, V = ub.
const_convert(V0, T0, T, V) :- T0 == T, !, V = V0.
const_convert(V, From, bool, W) :- !, const_truth(V, From, W).
const_convert(V, From, To, W) :-
    ( int_type(From), int_type(To) -> convert_int(V, To, W)
    ; int_type(From), float_type(To)
    -> type_class(To, K), ieee:ieee_from_int(K, V, W)
    ; float_type(From), float_type(To)
    -> type_class(From, F), type_class(To, K), ieee:ieee_convert(F, K, V, W)
    ; float_type(From), int_type(To)
    -> type_class(From, F),
       ( ieee:ieee_to_int(F, V, I), int_info(To, Size, Sign),
         Bits is 8 * Size, integer_range(Sign, Bits, Lo, Hi), I >= Lo, I =< Hi
       -> W = I
       ; W = ub
       )
    ).

integer_range(signed, Bits, Lo, Hi) :- Lo is -(1 << (Bits-1)), Hi is -Lo-1.
integer_range(unsigned, Bits, 0, Hi) :- Hi is (1 << Bits)-1.

const_truth(ub, _, ub) :- !.
const_truth(V, T, W) :-
    ( float_type(T) -> type_class(T, K), ieee:ieee_compare(K, ne, V, 0, W)
    ; truth(V =\= 0, W)
    ).

%! pp_value(+Expr, -Value) is semidet.
%
%  Value is the value of the #if expression Expr; fails when Expr is not
%  constant.
pp_value(Expr, V) :-
    const_eval(Expr, pp, V, _),
    integer(V).

% const_eval(+Expr, +Env, -V, -T): Expr has value V, an integer, float
% bits or ub, of unqualified type T in Env: its typed tree, used for its
% value, folds to V. Fails when Expr is not a constant expression.
const_eval(Expr, Env, V, T) :-
    elaborate(Expr, Env, X), value(X, XV), lowered(XV, T),
    folded(XV, Env, V).

doc(folded(+XV, +Env, -V), semidet, [
    XV: "a value tree",
    Env: "the scope, or pp in a #if expression",
    V: "its value: an integer, or float bits",
    "XV is a constant expression of value V. Its types are the tree's:",
    "the conversions are those the elaborator chose, so this is",
    "arithmetic only. A node that is not a constant (a load, a call, an",
    "assignment, an address) does not fold. A comma operator folds, as",
    "an extension, only when both operands do: one with an effect on its",
    "left, as in the length of int[(c++, 5)], is not a constant, so that",
    "array has variable length and the effect happens.",
    cites('C11 6.6p3'),
    example(( empty_env(E), folded(val(int, bin(add, val(int, int(2)), val(int, int(3)))), E, V) ),
            V = 5),
    example(( empty_env(E), folded(val(int, comma(val(int, int(1)), val(int, int(5)))), E, V) ),
            V = 5),
    fails(( empty_env(E),
            folded(val(int, comma(val(int, incdec(postinc, obj(int, id(c)))),
                                  val(int, int(5)))), E, _) )),
    fails(( empty_env(E), folded(val(int, load(obj(int, id(c)))), E, _) ))
]).
folded(val(_, int(V)), _, V).                               % 6.4.4.1, 6.4.4.4
folded(val(T, float(Cs)), _, V) :- float_literal(Cs, V, T).  % 6.4.4.2
folded(val(_, builtin(Name, [])), _, V) :- float_builtin(Name, _, V).
folded(val(_, builtin(Name, Args)), Env, V) :- object_size(Name, Args, Env, V).
folded(val(_, un(not, XV)), Env, V) :-                      % 6.5.3.3p5
    operand_value(XV, Env, V0, T0),
    const_truth(V0, T0, B),
    defined([B], V, truth(B =:= 0, V)).
folded(val(T0, un(Op, XV)), Env, V) :-                      % 6.5.3.3p2-4
    Op \== not,
    operand_value(XV, Env, V0, _),
    unqualified(T0, T),
    defined([V0], V, constant_unary(T, Op, V0, V)).
folded(val(T0, bin(Op, XA, XB)), Env, V) :-
    operand_value(XA, Env, VA, TA),
    operand_value(XB, Env, VB, TB),
    unqualified(T0, T),
    binary_kind(Op, Kind),
    kind_binary(Kind, Op, VA-TA, VB-TB, T, V).
folded(val(T0, cond(XC, XA, XB)), Env, V) :-                % 6.5.15p4
    operand_value(XC, Env, VC, TC),
    operand_value(XA, Env, VA, TA),
    operand_value(XB, Env, VB, TB),
    unqualified(T0, T),
    const_truth(VC, TC, Test),
    defined([Test], V,
            ( Test =\= 0 -> const_convert(VA, TA, T, V)
            ; const_convert(VB, TB, T, V) )).
folded(val(T0, cast(_, XV)), Env, V) :-                     % 6.5.4p5
    unqualified(T0, T), arithmetic_type(T),
    operand_value(XV, Env, V0, From),
    const_convert(V0, From, T, V).
folded(val(_, sizeof(type(Specs, Decl))), Env0, V) :- !,    % 6.5.3.4p2
    type_name_type(type(Specs, Decl), T, Env0, Env),
    catch(type_size_align(T, Env, V, _), bad(_), fail).
folded(val(_, sizeof(X)), Env, V) :-
    tree_type(X, T),
    catch(type_size_align(T, Env, V, _), bad(_), fail).
folded(val(_, alignof(TypeName)), Env, V) :-                % 6.5.3.4p3
    type_name_type(TypeName, T, Env, Env1),
    catch(type_size_align(T, Env1, _, V0), bad(_), fail),
    (   TypeName = type(Specs, Syntax),
        inherited_alignment(Specs, Syntax, Env, [align(A)])
    ->  V = A
    ;   V = V0
    ).
folded(val(_, offsetof(TypeName, Path)), Env, V) :-         % 7.19p3
    type_name_type(TypeName, T, Env, Env1),
    offset_path(Path, T, Env1, 0, V).
folded(val(_, comma(XA, XV)), Env, V) :- folded(XA, Env, _), folded(XV, Env, V).

% operand_value(+XV, +Env, -V, -T): value tree XV folds to V, of
% unqualified type T.
operand_value(XV, Env, V, T) :- folded(XV, Env, V), lowered(XV, T).

constant_unary(T, Op, A, V) :-
    ( float_type(T)
    -> type_class(T, K),
       ( Op == plus -> V = A ; Op == neg -> ieee:ieee_neg(K, A, V) ; fail )
    ; unary_arith(Op, A, R), convert_int(R, T, V)
    ).

% offset_path(+Path, +Type, +Env, +Off0, -Off): offsetof's member path.
offset_path([], _, _, Off, Off).
offset_path([field(F)|Path], T, Env, Off0, Off) :-
    member_type_offset(T, F, Env, FieldType, FieldOff),
    Off1 is Off0 + FieldOff,
    offset_path(Path, FieldType, Env, Off1, Off).
offset_path([index(X)|Path], array(ElemType, _), Env, Off0, Off) :-
    const_eval(X, Env, I, _),
    integer(I),
    type_size_align(ElemType, Env, ElemSize, _),
    Off1 is Off0 + I * ElemSize,
    offset_path(Path, ElemType, Env, Off1, Off).

% env_int_type(+Env, +T0, -T): a constant or operator result of type T0
% has type T in Env: T0 itself, or in a #if expression intmax_t or
% uintmax_t (6.10.1p4). A #if expression has no floating constants
% (6.10.1p1), so a float type has none there.
env_int_type(e(_, _, _, _), T, T).
env_int_type(pp, T0, T) :-
    int_info(T0, _, Sign),
    intmax_type(Sign, T).

intmax_type(signed, long).
intmax_type(unsigned, ulong).

% defined(+Values, -V, :Goal): V is ub if one of Values is, and
% otherwise as Goal gives it.
defined(Vs, V, Goal) :-
    (   memberchk(ub, Vs) -> V = ub ; call(Goal) ).

% int_value(+V0, +T, -V): V is the value V0 converted to T.
int_value(V0, T, V) :- defined([V0], V, convert_int(V0, T, V)).

% truth(:Goal, -B): B is 1 if Goal holds, else 0.
truth(Goal, B) :- ( call(Goal) -> B = 1 ; B = 0 ).

% unary_arith(?Op, ?X, ?R): the unary arithmetic operator Op makes the
% arithmetic expression R of its operand X.
unary_arith(neg, X, -X).
unary_arith(plus, X, X).
unary_arith(bnot, X, \X).

% binary_kind(?Op, ?Kind): the binary operator Op converts its operands
% as Kind (arith, shift, compare or logical) names.
binary_kind(Op, Kind) :-
    c_operator(_, _, Op, Kind0),
    ( Kind0 = arith(_) -> Kind = arith ; Kind = Kind0 ).

doc(kind_binary(+Kind, +Op, +A, +B, +T, -V), semidet, [
    Kind: "arith, shift, compare or logical, as binary_kind/2 names Op",
    Op: "a binary operator",
    A: "the left operand, Value-Type",
    B: "the right operand, Value-Type",
    T: "the type of the result",
    V: "the value of the result, or ub",
    "Arithmetic converts both operands to T, a comparison both to their",
    "common type (binary_operands/6), and a shift only the left one, to T.",
    "A shift count that is negative or not below the width of T is",
    "undefined, so it is ub, as is a division by zero or a quotient",
    "that the signed type cannot represent. Other signed overflow wraps,",
    "as clang and GCC fold it (with a warning).",
    cites('C11 6.5.5p5'),
    cites('C11 6.5.5p6'),
    cites('C11 6.5.7p3'),
    cites('C11 6.5.8p3'),
    cites('C11 6.5.13p4'),
    example(kind_binary(arith, sub, 1-uint, 2-int, uint, V), V = 4294967295),
    example(kind_binary(arith, div, 1-int, 0-int, int, V), V == ub),
    example(kind_binary(arith, div, -2147483648-int, -1-int, int, V), V == ub),
    example(kind_binary(arith, mod, -2147483648-int, -1-int, int, V), V == ub),
    example(kind_binary(arith, div, -2147483647-int, -1-int, int, V),
            V = 2147483647),
    example(kind_binary(arith, div, -2147483648-int, -1-long, long, V),
            V = 2147483648),
    example(kind_binary(arith, add, 2147483647-int, 1-int, int, V),
            V = -2147483648),
    example(kind_binary(shift, shl, 1-int, 30-int, int, V), V = 1073741824),
    example(kind_binary(shift, shl, 1-int, 32-int, int, V), V == ub),
    example(kind_binary(shift, shl, 1-long, 32-int, long, V), V = 4294967296),
    example(kind_binary(shift, shl, 1-int, 40-long, int, V), V == ub),
    example(kind_binary(shift, shr, 8-int, -1-int, int, V), V == ub),
    example(kind_binary(shift, shl, 1-int, 18446744073709551615-ullong, int, V),
            V == ub),
    example(kind_binary(compare, lt, -1-int, 0-uint, int, V), V = 0),
    example(kind_binary(logical, land, 0-int, ub-int, int, V), V = 0)
]).
kind_binary(arith, Op, VA-TA, VB-TB, T, V) :-
    defined([VA, VB], V,
            (   const_convert(VA, TA, T, A),
                const_convert(VB, TB, T, B),
                ( float_type(T)
                -> type_class(T, K), memberchk(Op, [add, sub, mul, div]),
                   ieee:ieee_binary(K, Op, A, B, V)
                ; quotient_overflows(Op, A, B, T) -> V = ub
                ; const_arith(Op, A, B, R), int_value(R, T, V)
                )
            )).
kind_binary(shift, Op, VA-_, VB-_, T, V) :-
    defined([VA, VB], V,
            (   int_info(T, Size, _), VB >= 0, VB < 8 * Size
            ->  convert_int(VA, T, A),
                const_shift(Op, A, VB, R),
                convert_int(R, T, V)
            ;   V = ub
            )).
kind_binary(compare, Op, VA-TA, VB-TB, _, V) :-
    binary_operands(Op, TA, TB, CT, CT, _),
    defined([VA, VB], V,
            (   const_convert(VA, TA, CT, A),
                const_convert(VB, TB, CT, B),
                ( float_type(CT)
                -> type_class(CT, K), ieee:ieee_compare(K, Op, A, B, V)
                ; truth(const_compare(Op, A, B), V)
                )
            )).
kind_binary(logical, Op, VA-TA, VB-TB, _, V) :-
    const_truth(VA, TA, A), const_truth(VB, TB, B),
    defined([A], V, const_logical(Op, A, B, V)).

const_shift(shl, A, B, R) :- R is A << B.
const_shift(shr, A, B, R) :- R is A >> B.

% const_logical(+Op, +A, +VB, -V): the right operand VB counts only when
% the left A does not decide.
const_logical(land, A, VB, V) :-
    (   A =:= 0 -> V = 0 ; defined([VB], V, truth(VB =\= 0, V)) ).
const_logical(lor, A, VB, V) :-
    (   A =\= 0 -> V = 1 ; defined([VB], V, truth(VB =\= 0, V)) ).

% quotient_overflows(+Op, +A, +B, +T): A / B of the signed type T is not
% representable, so A / B and A % B are undefined (C11 6.5.5p6): the
% minimum divided by -1.
quotient_overflows(Op, A, -1, T) :-
    memberchk(Op, [div, mod]),
    int_info(T, Size, signed),
    A =:= -(1 << (8 * Size - 1)).

% Division by zero is undefined: R is ub.
const_arith(add, A, B, R) :- R is A + B.
const_arith(sub, A, B, R) :- R is A - B.
const_arith(mul, A, B, R) :- R is A * B.
const_arith(div, A, B, R) :- ( B =:= 0 -> R = ub ; R is A // B ).
const_arith(mod, A, B, R) :- ( B =:= 0 -> R = ub ; R is A rem B ).
const_arith(and, A, B, R) :- R is A /\ B.
const_arith(or, A, B, R) :- R is A \/ B.
const_arith(xor, A, B, R) :- R is xor(A, B).

const_compare(eq, A, B) :- A =:= B.
const_compare(ne, A, B) :- A =\= B.
const_compare(lt, A, B) :- A < B.
const_compare(gt, A, B) :- A > B.
const_compare(le, A, B) :- A =< B.
const_compare(ge, A, B) :- A >= B.

%! num_type(+V, +Suffix-Radix, -Type) is det.
%
%  Type is the type of an integer constant of value V: the first type in
%  the C11 list for its suffix and radix that can represent it, or
%  ullong when none can.
num_type(V, Suffix-Radix, Type) :-
    (   constant_types(Radix, Suffix, Types),
        member(Type, Types),
        fits(V, Type)
    ->  true
    ;   Type = ullong
    ).

constant_types(dec, none, [int, long, llong]).
constant_types(dec, u, [uint, ulong, ullong]).
constant_types(dec, l, [long, llong]).
constant_types(dec, ul, [ulong, ullong]).
constant_types(dec, ll, [llong]).
constant_types(dec, ull, [ullong]).
constant_types(other, none, [int, uint, long, ulong, llong, ullong]).
constant_types(other, u, [uint, ulong, ullong]).
constant_types(other, l, [long, ulong, llong, ullong]).
constant_types(other, ul, [ulong, ullong]).
constant_types(other, ll, [llong, ullong]).
constant_types(other, ull, [ullong]).

% fits(+V, +Type): the non-negative constant V is below Type's maximum.
fits(V, Type) :-
    int_info(Type, Size, Sign),
    Bits is 8 * Size,
    below_max(Sign, V, Bits).

% below_max(+Signedness, +V, +Bits): V is below the maximum of a Bits-wide
% integer with Signedness.
below_max(signed, V, Bits) :- V < 1 << (Bits - 1).
below_max(unsigned, V, Bits) :- V < 1 << Bits.

%% Compatible and composite types

doc(compatible_type(+T, +U), semidet, [
    T: "a type",
    U: "another type",
    "T and U are compatible: the same type, or alike in their parts where",
    "one leaves a part open, an array's size or a function's parameters.",
    "Integer types of the same width are still distinct, and a qualified",
    "type is compatible only with the same qualified type.",
    cites('C11 6.2.7p1'),
    cites('C11 6.7.3p10'),
    example(compatible_type(array(int, none), array(int, 3))),
    fails(compatible_type(long, llong)),
    fails(compatible_type(ptr(int), ptr(qualified([const], int))))
]).
compatible_type(T, U) :- composite_type(T, U, _).

doc(composite_type(+T, +U, -C), semidet, [
    T: "a type",
    U: "a type compatible with T",
    C: "their composite type",
    "The type that says what both say: an array's size where either knows",
    "it (a constant one over a variable one), a function's parameters",
    "where either has a prototype. Fails when T and U are not compatible.",
    "Variable lengths are compatible with any length (6.7.6.2p6).",
    cites('C11 6.7.6.2p6'),
    cites('C11 6.2.7p3'),
    example(composite_type(ptr(array(int, none)), ptr(array(int, 3)), C),
            C = ptr(array(int, 3))),
    example(composite_type(ptr(array(int, vla(id(n)))), ptr(array(int, 3)), C),
            C = ptr(array(int, 3))),
    example(composite_type(array(int, 3), array(int, dyn(tmp(v1))), C),
            C = array(int, 3)),
    example(composite_type(func(int, unspecified, fixed),
                           func(int, [ptr(char)], fixed), C),
            C = func(int, [ptr(char)], fixed)),
    "A parameter's own qualifiers do not count (6.7.6.3p15).",
    cites('C11 6.7.6.3p15'),
    example(composite_type(func(int, [qualified([const], int)], fixed),
                           func(int, [int], fixed), C),
            C = func(int, [int], fixed)),
    fails(composite_type(func(int, [ptr(qualified([const], int))], fixed),
                         func(int, [ptr(int)], fixed), _)),
    fails(composite_type(array(int, 2), array(int, 3), _)),
    fails(composite_type(func(int, [], fixed), func(int, [], variadic), _))
]).
composite_type(T, U, T) :- T == U, !.
composite_type(qualified(Qs, T), qualified(Qs, U), qualified(Qs, C)) :-
    composite_type(T, U, C).
composite_type(ptr(T), ptr(U), ptr(C)) :- composite_type(T, U, C).
composite_type(array(T, N), array(U, M), array(C, K)) :-
    composite_size(N, M, K),
    composite_type(T, U, C).
composite_type(func(R, Ps, V), func(S, Qs, V), func(C, Cs, V)) :-
    composite_type(R, S, C),
    composite_params(Ps, Qs, Cs).

% composite_size(+N, +M, -K): array sizes N and M, each none if unknown,
% agree on K.
composite_size(none, M, M) :- !.
composite_size(N, none, N) :- !.
composite_size(N, M, M) :- variable_size(N), !.
composite_size(N, M, N) :- variable_size(M), !.
composite_size(N, N, N).

% composite_params(+Ps, +Qs, -Cs): parameter lists Ps and Qs, each
% unspecified without a prototype, agree on Cs.
composite_params(unspecified, Qs, Qs) :- !.
composite_params(Ps, unspecified, Ps) :- !.
composite_params(Ps, Qs, Cs) :- maplist(composite_param, Ps, Qs, Cs).

composite_param(P, Q, C) :-
    ( P = qualified(_, P1) -> true ; P1 = P ),
    ( Q = qualified(_, Q1) -> true ; Q1 = Q ),
    composite_type(P1, Q1, C).

doc(unqualified(+T0, -T), det, [
    T0: "a reflected type",
    T: "T0 without qualifiers, at any depth",
    "The type code generation uses: qualifiers say what a program may do",
    "with an object, not how it is stored.",
    example(unqualified(ptr(qualified([const], char)), T), T = ptr(char)),
    example(unqualified(func(qualified([volatile], int), unspecified, fixed), T),
            T = func(int, unspecified, fixed))
]).
unqualified(T, T) :- var(T), !.
unqualified(qualified(_, T0), T) :- !, unqualified(T0, T).
unqualified(ptr(T0), ptr(T)) :- !, unqualified(T0, T).
unqualified(array(T0, N), array(T, N)) :- !, unqualified(T0, T).
unqualified(func(R0, Ps0, V), func(R, Ps, V)) :- !,
    unqualified(R0, R),
    ( Ps0 == unspecified -> Ps = Ps0 ; maplist(unqualified, Ps0, Ps) ).
unqualified(T, T).

%% The typed tree

/*  An expression elaborated is a tree whose every node carries its
    (reflected, qualified) type, with its category the node's principal
    functor:

      X ::= obj(T, F)    an lvalue designating an object of type T
          | fun(T, F)    a function designator of function type T
          | val(T, F)    a value of type T, not an lvalue

    The conversions C applies implicitly are nodes of their own: where an
    operand is used for its value, value/2 wraps it in load(X) or
    decay(X). _Generic is resolved here: its tree is the selected
    association's. Every operand is elaborated but the arguments of a
    builtin, a statement expression's block and a compound literal's
    initializer, which stay as the source has them. */

doc(elaborate(+E, +Env, -X), semidet, [
    E: "a C expression, as c_parse reads it",
    Env: "the scope it is read in",
    X: "its typed tree",
    "X is E as C reads it: each node typed, and lvalues, function",
    "designators and values told apart. Fails when E cannot be typed.",
    cites('C11 6.5p1'),
    example(( empty_env(E0), bind_ordinary(x, var(none, int), E0, E),
              elaborate(un(addr, id(x)), E, X) ),
            X = val(ptr(int), addr(obj(int, id(x))))),
    example(( empty_env(E), elaborate(num(3000000000, none-dec), E, X) ),
            X = val(long, int(3000000000))),
    example(( empty_env(E), elaborate(num(3000000000, none-other), E, X) ),
            X = val(uint, int(3000000000))),
    example(( empty_env(E0), bind_ordinary(a, var(none, array(int, 4)), E0, E),
              elaborate(index(id(a), chr(1)), E, X) ),
            X = obj(int, deref(val(ptr(int),
                    bin(add, val(ptr(int), decay(obj(array(int, 4), id(a)))),
                             val(int, int(1))))))),
    example(( empty_env(E0), bind_ordinary(x, var(none, short), E0, E),
              elaborate(comma(assign(=, id(x), chr(1)), id(x)), E, X) ),
            X = val(short, comma(val(short, assign(=, obj(short, id(x)),
                                                   val(int, int(1)))),
                                 val(short, load(obj(short, id(x))))))),
    example(( empty_env(E), elaborate(str([104, 105]), E, X) ),
            X = obj(array(char, 3), str([104, 105]))),
    fails(( empty_env(E), elaborate(un(deref, chr(1)), E, _) )),
    example(( empty_env(E0), bind_ordinary(f, fn(func(int, [int], variadic), f, extern), E0, E),
              elaborate(call(id(f), [chr(1), chr(2)]), E, X) ),
            X = val(int, call(_, [val(int, int(1)), val(int, int(2))]))),
    fails(( empty_env(E0), bind_ordinary(f, fn(func(int, [int], fixed), f, extern), E0, E),
            elaborate(call(id(f), [chr(1), chr(2)]), E, _) )),
    fails(( empty_env(E0), bind_ordinary(f, fn(func(int, [ptr(int)], fixed), f, extern), E0, E),
            elaborate(call(id(f), [chr(1)]), E, _) )),
    fails(( empty_env(E), elaborate(un(addr, chr(1)), E, _) )),
    fails(( empty_env(E0), bind_ordinary(c, var(none, int), E0, E1),
            bind_ordinary(qtype(c), qualified([const], int), E1, E),
            elaborate(assign(=, id(c), chr(1)), E, _) ))
]).
elaborate(E, Env, X) :- elab(E, Env, X0), !, X = X0.

elab(id(Name), Env, X) :-
    lookup_ordinary(Env, Name, Binding), !,
    identifier_type(Binding, Name, Env, T),
    binding_node(Binding, T, Name, X).
elab(id(Name), _, obj(array(char, none), predefined(Name))) :-   % 6.4.2.2
    memberchk(Name, ['__func__', '__FUNCTION__', '__PRETTY_FUNCTION__']).
elab(num(V0, S), Env, val(T, int(V))) :-
    num_type(V0, S, T0), env_int_type(Env, T0, T), convert_int(V0, T, V).
elab(chr(V), Env, val(T, int(V))) :- env_int_type(Env, int, T).
elab(float(Cs), Env, val(T, float(Cs))) :-
    last(Cs, Suffix),
    ( memberchk(Suffix, [f, 'F']) -> T0 = float
    ; memberchk(Suffix, [l, 'L']) -> T0 = ldouble
    ; T0 = double
    ),
    env_int_type(Env, T0, T).
elab(str(Bytes), _, obj(array(char, N), str(Bytes))) :-
    length(Bytes, M), N is M + 1.
elab(wstr(T, Values), _, obj(array(T, N), wstr(T, Values))) :-
    length(Values, M), N is M + 1.
elab(cast(TN, E), Env, val(T, cast(TN, XV))) :-
    type_name_type(TN, T0, Env, _),
    operand(E, Env, XV, F0), unqualified(F0, F),
    castable(F, T0),
    reflect_type(TN, T0, Env, T).
elab(complit(TN, Init), Env, obj(T, complit(TN, Init))) :-
    type_name_type(TN, T0, Env, _), reflect_type(TN, T0, Env, T).
elab(un(addr, E), Env, val(ptr(T), addr(X))) :-       % 6.5.3.2p1
    elaborate(E, Env, X), X \= val(_, _), X \= obj(_, bitfield(_, _)),
    tree_type(X, T).
elab(un(deref, E), Env, X) :-
    operand(E, Env, XV, ptr(T)),
    designator(T, deref(XV), X).
elab(un(Op, E), Env, val(T, incdec(Op, X))) :-        % 6.5.3.1p1
    memberchk(Op, [preinc, predec, postinc, postdec]),
    elaborate(E, Env, X), modifiable(X, Env),
    value(X, XV), tree_type(XV, T), scalar_type(T).
elab(un(Op, E), Env, val(T, un(Op, XV))) :-
    memberchk(Op, [plus, neg, bnot, not]),
    operand(E, Env, XV, T1),
    unary_operand(Op, T1, T0), env_int_type(Env, T0, T).
elab(index(A, I), Env, X) :-                                % 6.5.2.1p2
    elab(un(deref, bin(add, A, I)), Env, X).
elab(member(E, F), Env, X) :-
    elaborate(E, Env, XS), tree_type(XS, SU), member_type(SU, F, Env, T),
    unqualified(SU, U),
    (   member_layout(U, F, Env, _, _, bits(_, W))          % 6.7.2.1p10
    ->  XS = obj(_, _), X = obj(T, bitfield(member(XS, F), W))
    ;   member_node(XS, F, T, X)
    ).
elab(arrow(E, F), Env, X) :-                                % 6.5.2.3p4
    elab(member(un(deref, E), F), Env, X).
elab(call(id(Name), Args), Env, X) :-
    \+ lookup_ordinary(Env, Name, _),
    library_builtin(Name, F), lookup_ordinary(Env, F, _), !,
    elab(call(id(F), Args), Env, X).
elab(call(id(Name), Args), Env, X) :-
    \+ lookup_ordinary(Env, Name, _),
    checking_builtin(Name, Chk, Plain), !,
    (   lookup_ordinary(Env, Chk, _) -> elab(call(id(Chk), Args), Env, X)
    ;   unchecked_call(Plain, Args, Env, Call), lookup_ordinary(Env, Plain, _),
        elab(Call, Env, X)
    ).
elab(call(id(Name), Args), Env, X) :-
    \+ lookup_ordinary(Env, Name, _),
    atomic_builtin(Name, Args, Env, R), !,
    (   R = expr(E) -> elab(E, Env, X)
    ;   R = builtin(T), X = val(T, builtin(Name, Args))
    ).
elab(call(id(Name), [str([])]), Env, val(T, builtin(Name, []))) :-
    \+ lookup_ordinary(Env, Name, _),
    nan_builtin(Name, T, _), !.
elab(call(id(Name), Args), Env, val(T, builtin(Name, Args))) :-
    \+ lookup_ordinary(Env, Name, _),
    (   Args == [], float_builtin(Name, T, _), \+ nan_builtin(Name, _, _) -> true
    ;   builtin_type(Name, T)
    ).
elab(call(E, Args), Env, val(T, call(XV, XArgs))) :-   % 6.5.2.2p2
    operand(E, Env, XV, ptr(func(T, Ps, V))),
    maplist(argument(Env), Args, XArgs),
    arity_fits(Ps, V, Args),
    passes(Ps, XArgs, Env).
elab(assign(Op, A, B), Env, val(T, assign(Op, X, XB))) :-   % 6.5.16p2
    elaborate(A, Env, X), assignment_type(X, T), modifiable(X, Env),
    argument(Env, B, XB),
    unqualified(T, TA), lowered(XB, TB),
    assigns(Op, TA, XB, TB, Env).
elab(comma(A, B), Env, val(T, comma(XA, XV))) :-
    argument(Env, A, XA),
    operand(B, Env, XV, T).
elab(sizeof_expr(E), Env, val(ulong, sizeof(X))) :-     % 6.5.3.4p1
    elaborate(E, Env, X), X \= obj(_, bitfield(_, _)).
elab(sizeof_type(TN), _, val(ulong, sizeof(TN))).
elab(alignof(TN), _, val(ulong, alignof(TN))).
elab(offsetof(TN, Path), _, val(ulong, offsetof(TN, Path))).
elab(label_addr(Name), Env, X) :-                          % GNU &&label
    label_value(Name, Env, E), elab(E, Env, X).
elab(bin(Op, A, B), Env, val(T, bin(Op, XA, XB))) :-
    operand(A, Env, XA, TA), operand(B, Env, XB, TB),
    expression_binary_type(Op, TA, TB, T0), env_int_type(Env, T0, T).
elab(cond(C, A, B), Env, val(T, cond(XC, XA, XB))) :-   % 6.5.15p2
    argument(Env, C, XC), tree_type(XC, TC), scalar_type(TC),
    arms(A, B, Env, XA, XB, T).
elab(gcond(C, B), Env, val(T, gcond(XC, XB))) :-
    arms(C, B, Env, XC, XB, T), tree_type(XC, TC), scalar_type(TC).
elab(va_arg(A, TN), Env, val(T, va_arg(TN, XA))) :-
    argument(Env, A, XA),
    type_name_type(TN, T0, Env, _), reflect_type(TN, T0, Env, T).
elab(bit_cast(TN, E), Env, val(T, bit_cast(XA))) :-
    argument(Env, E, XA), tree_type(XA, TA),
    type_name_type(TN, T0, Env, _), unqualified(T0, T),
    bit_castable(TA, T, Env).
elab(stmtexpr(at(Loc, block(Items))), Env, val(T, stmtexpr(at(Loc, block(Items))))) :-
    block_value_type(Items, Env, T).
elab(generic(C, As), Env, X) :-                             % 6.5.1.1
    operand(C, Env, _, CT),
    generic_selection(CT, As, Env, constant, E),
    elaborate(E, Env, X).

% argument(+Env, +E, -XV): XV is E elaborated and used for its value: a
% call argument, the source of an assignment, a ?: condition, or the left
% operand of a comma, whose value is discarded after it is evaluated.
argument(Env, E, XV) :- operand(E, Env, XV, _).

% assignment_type(+X, -T): an assignment to X has type T, X's own but
% for a bit-field, whose value has its promoted type (6.5.16p3).
assignment_type(obj(T0, bitfield(_, W)), T) :- !,
    value_type(T0, T1), bitfield_promotion(T1, W, T).
assignment_type(X, T) :- tree_type(X, T).

% lowered(+XV, -T): T is the type of value XV without qualifiers, the
% type lowering gives it.
lowered(XV, T) :- tree_type(XV, T0), unqualified(T0, T).

% assigns(+Op, +TA, +B, +TB, +Env): assignment Op stores B, a value of
% type TB, into an object of unqualified type TA: B as it is (6.5.16.1),
% or the result of the operator applied to the two (6.5.16.2).
assigns(=, TA, XB, TB, Env) :- !, nullness(XB, Env, N), assignable(TB, N, TA).
assigns(Op, TA, _, TB, _) :-
    compound_assignment(Op, BinOp), scalar_type(TA),
    binary_operands(BinOp, TA, TB, _, _, T), assignable(T, value, TA).

% arity_fits(+Ps, +V, +Args): a function with parameters Ps, fixed or
% variadic, takes Args.
arity_fits(unspecified, _, _) :- !.
arity_fits(Ps, V, Args) :-
    length(Ps, NP), length(Args, NA),
    ( V == fixed -> NA =:= NP ; NA >= NP ).

% passes(+Ps, +XArgs, +Env): each argument, elaborated in XArgs,
% may be assigned to the unqualified type of its parameter in Ps.
passes(unspecified, _, _) :- !.
passes([], _, _).
passes([P|Ps], [X|Xs], Env) :-
    lowered(X, T), unqualified(P, TP), nullness(X, Env, N),
    assignable(T, N, TP),
    passes(Ps, Xs, Env).

doc(identifier_type(+Binding, +Name, +Env, -T), det, [
    Binding: "what the identifier Name stands for in Env",
    Name: "an ordinary identifier",
    Env: "the scope, which records Name's reflected type",
    T: "the type it has as an expression",
    "An enumeration constant has its enumeration's type. An object or",
    "function has the type its declaration reflects, qualifiers",
    "included, with array sizes that initializers have since completed.",
    cites('C11 6.5.1p2'),
    example(( empty_env(E0), bind_ordinary(qtype(c), qualified([const], int), E0, E),
              identifier_type(var(none, int), c, E, T) ),
            T = qualified([const], int)),
    example(( empty_env(E0), bind_ordinary(qtype(s), array(char, none), E0, E),
              identifier_type(gvar(array(char, 6), s, static, none), s, E, T) ),
            T = array(char, 6))
]).
identifier_type(enumconst(_, T0), _, _, T) :- !, T = T0.
identifier_type(Binding, Name, Env, T) :-
    binding_type(Binding, T0),
    (   lookup_ordinary(Env, qtype(Name), RT) -> reflected_shape(RT, T0, T)
    ;   T = T0
    ).

binding_type(var(_, T), T).
binding_type(gvar(T, _, _, _), T).
binding_type(fn(T, _, _), T).
binding_type(enumconst(_, T), T).

% reflected_shape(+RT, +T, -S): S is reflected type RT with the array
% dimensions of declared type T, which an initializer may have completed
% since RT was recorded.
reflected_shape(qualified(Qs, R), T, qualified(Qs, S)) :- !,
    reflected_shape(R, T, S).
reflected_shape(array(R, _), array(T, N), array(S, N)) :- !,
    reflected_shape(R, T, S).
reflected_shape(ptr(R), ptr(T), ptr(S)) :- vm_type(T), !,   % evaluated lengths
    reflected_shape(R, T, S).
reflected_shape(R, _, R).

% binding_node(+Binding, +T, +Name, -X): X is the identifier Name, bound
% to Binding, of type T.
binding_node(var(_, _), T, Name, obj(T, id(Name))).
binding_node(gvar(_, _, _, _), T, Name, obj(T, id(Name))).
binding_node(fn(_, _, _), T, Name, fun(T, id(Name))).
binding_node(enumconst(V, _), T, _, val(T, int(V))).

% designator(+T, +F, -X): F, designating something of type T, is a
% function designator or an lvalue (6.5.3.2p4).
designator(T, F, X) :- T = func(_, _, _), !, X = fun(T, F).
designator(T, F, obj(T, F)).

% member_node(+XS, +F, +T, -X): member F, of type T, of struct or union
% XS is an lvalue if XS is (6.5.2.3p3).
member_node(obj(TS, FS), F, T, obj(T, member(obj(TS, FS), F))).
member_node(val(TS, FS), F, T, val(T, member(val(TS, FS), F))).

doc(member_type(+SU, +F, +Env, -T), semidet, [
    SU: "a struct or union type, perhaps qualified",
    F: "a member name",
    Env: "the scope that defines SU",
    T: "the member's reflected type",
    "Looks into anonymous members. A qualified SU qualifies the member.",
    cites('C11 6.5.2.3p3'),
    cites('C11 6.7.2.1p13'),
    example(( empty_env(E), member_type(struct('builtin.va_list'), fp_offset, E, T) ),
            T = uint),
    example(( empty_env(E),
              member_type(qualified([const], struct('builtin.va_list')),
                          reg_save_area, E, T) ),
            T = qualified([const], ptr(void))),
    fails(( empty_env(E), member_type(struct('builtin.va_list'), gp, E, _) ))
]).
member_type(qualified(Qs, SU), F, Env, T) :- !,
    member_type(SU, F, Env, T0), qualify(Qs, T0, T).
member_type(SU, F, Env, T) :-
    SU =.. [_, Id], Env = e(_, _, Defs, _),
    get_assoc(qmembers(Id), Defs, Members), !,
    members_type(Members, F, Env, T).
member_type(SU, F, Env, T) :-                               % built-in va_list
    member_type_offset(SU, F, Env, T, _).

% members_type(+Members, +F, +Env, -T): one of Members, or a member of
% an anonymous one, is F of type T.
members_type(Members, F, _, T) :-
    memberchk(q(some(F), T0), Members), !, T = T0.
members_type(Members, F, Env, T) :-
    member(q(none, Anon), Members), member_type(Anon, F, Env, T), !.

doc(library_builtin(?(Name), ?(F)), nondet, [
    Name: "a GNU builtin spelling of a standard library function",
    F: "that function",
    "An undeclared Name called is a call of F, when F is declared:",
    "GCC treats these builtins as the library functions they name.",
    cites('GCC manual, Other Built-in Functions'),
    cites('C11 7.24.2.1'),
    example(library_builtin('__builtin_memcpy', F), F = memcpy),
    fails(library_builtin(memcpy, _))
]).
library_builtin('__builtin_memcpy', memcpy).
library_builtin('__builtin_memmove', memmove).
library_builtin('__builtin_memset', memset).

doc(label_value(+Name, +Env, -E), semidet, [
    Name: "a label whose address GNU C's &&Name takes",
    Env: "the scope of the function that defines it, where c_lower bound",
    "label_addr(Name) to the label's number N (1, 2, ... in the order the",
    "function takes the addresses)",
    E: "the expression (void *)N, which &&Name stands for",
    "A label's value is a void * that only goto * of the same function",
    "uses. nanofil gives it no capability: the address N is the label's",
    "number, an address constant (so static tables of labels work), and",
    "goto * dispatches on it among the function's address-taken labels,",
    "trapping on any other value. Values of labels of different",
    "functions may compare equal.",
    cites('GCC manual, Labels as Values'),
    example(( empty_env(E0), bind_ordinary(label_addr(l), 3, E0, E),
              label_value(l, E, X) ),
            X = cast(type([tspec(void)], ptr(base, [])), num(3, none-dec))),
    fails(( empty_env(E), label_value(l, E, _) ))
]).
label_value(Name, Env, cast(type([tspec(void)], ptr(base, [])), num(N, none-dec))) :-
    lookup_ordinary(Env, label_addr(Name), N).

doc(checking_builtin(?(Name), ?(Chk), ?(Plain)), nondet, [
    Name: "a GNU object-size checking builtin, which glibc's _FORTIFY_SOURCE headers call",
    Chk: "the library function that checks",
    Plain: "the function it checks",
    "An undeclared Name called is a call of Chk with the same arguments",
    "when Chk is declared (glibc declares the printf family's). Else a",
    "string or memory function's last argument is the destination's",
    "object size, and when it folds to (size_t)-1, unknown, the call is",
    "one of Plain without it, as GCC and clang lower it; any other size",
    "is refused. Fil-C checks every access anyway.",
    cites('GCC manual, Object Size Checking'),
    example(checking_builtin('__builtin___memcpy_chk', C, P),
            (C = '__memcpy_chk', P = memcpy)),
    fails(checking_builtin('__builtin_memcpy', _, _))
]).
checking_builtin(Name, Chk, Plain) :-
    atom(Name),
    atom_concat('__builtin___', Rest, Name), atom_concat(Plain, '_chk', Rest),
    atom_concat('__', Rest, Chk).

% unchecked_call(+Plain, +Args, +Env, -Call): Call is Plain of Args but
% the last, a constant object size of (size_t)-1, for a memory or string
% function.
unchecked_call(Plain, Args, Env, call(id(Plain), Args0)) :-
    memberchk(Plain, [memcpy, memmove, mempcpy, memset, strcpy, stpcpy,
                      strncpy, stpncpy, strcat, strncat]),
    append(Args0, [Size], Args),
    catch(const_value(Size, Env, V, _), not_constant, fail),
    V =:= 0xffffffffffffffff.

doc(object_size(+Name, +Args, +Env, -V), semidet, [
    Name: "__builtin_object_size or __builtin_dynamic_object_size",
    Args: "its pointer and its constant type, 0 to 3",
    Env: "the scope the type is read in",
    V: "the size it answers: (size_t)-1 for types 0 and 1, 0 for 2 and 3",
    "nanofil always answers that the size is unknown, which GCC",
    "documents as a correct answer for any pointer; the pointer is not",
    "evaluated. Fails unless the type is a constant 0 to 3.",
    cites('GCC manual, Object Size Checking'),
    example(( empty_env(E), object_size('__builtin_object_size', [id(p), num(1, none-dec)], E, V) ),
            V = 0xffffffffffffffff),
    example(( empty_env(E), object_size('__builtin_dynamic_object_size', [id(p), num(2, none-dec)], E, V) ),
            V = 0),
    fails(( empty_env(E), object_size('__builtin_object_size', [id(p), num(4, none-dec)], E, _) ))
]).
object_size(Name, [_, Type], Env, V) :-
    memberchk(Name, ['__builtin_object_size', '__builtin_dynamic_object_size']),
    catch(const_value(Type, Env, K, _), not_constant, fail),
    (   memberchk(K, [0, 1]) -> V = 0xffffffffffffffff
    ;   memberchk(K, [2, 3]) -> V = 0
    ).

doc(atomic_builtin(+Name, +Args, +Env, -R), semidet, [
    Name: "a GNU __atomic or clang __c11_atomic builtin",
    Args: "its argument expressions",
    Env: "the scope",
    R: "expr(E), the plain C expression E it is, or builtin(T), a builtin call of type T that lowering makes atomic",
    "On an integer, __atomic_load_n(P, Order) is *P and, for a relaxed or",
    "release Order, __atomic_store_n(P, V, Order) is (void)(*P = V), both",
    "after Order: an aligned integer access is already atomic on x86-64,",
    "and none of those orders needs a fence there. A sequentially",
    "consistent integer store is the store and then a fence (mov; mfence,",
    "where clang emits xchg; both are seq_cst stores against plain-mov",
    "seq_cst loads). On a pointer, whose capability is a second word, both",
    "are builtin(T) at every order: lowering emits IR's atomic_load and",
    "atomic_store, which call Fil-C's helpers as clang does, single-copy",
    "atomic and sequentially consistent (docs/m4.md, Atomic builtins).",
    "*P is an integer or a pointer, and Order a constant: relaxed,",
    "consume, acquire or seq_cst for a load; relaxed, release or seq_cst",
    "for a store. Anything else fails (fault/4 says why).",
    "A store through a pointer to an _Atomic object is builtin(void) at",
    "every order, since assigning the object would be a seq_cst store.",
    cites('GCC manual, __atomic Builtins'),
    cites('C11 7.17.3p1'),
    cites('C11 7.17.7.1p2'),
    cites('C11 7.17.7.2p2'),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(int)), E0, E),
              atomic_builtin('__atomic_load_n', [id(p), chr(0)], E, X) ),
            X = expr(comma(chr(0), un(deref, id(p))))),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(ptr(int))), E0, E),
              atomic_builtin('__atomic_load_n', [id(p), chr(2)], E, X) ),
            X = builtin(ptr(int))),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(int)), E0, E),
              atomic_builtin('__atomic_store_n', [id(p), chr(1), chr(5)], E, X) ),
            X = builtin(void)),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], int))), E0, E),
              atomic_builtin('__atomic_store_n', [id(p), chr(1), chr(0)], E, X) ),
            X = builtin(void)),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(int)), E0, E),
            atomic_builtin('__atomic_store_n', [id(p), chr(1), chr(2)], E, _) )),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(double)), E0, E),
            atomic_builtin('__atomic_load_n', [id(p), chr(0)], E, _) )),
    "<stdatomic.h>'s generic functions are clang's __c11_atomic builtins,",
    "whose pointer must point to an _Atomic object, here of an integer,",
    "pointer, float or double. __c11_atomic_load and __c11_atomic_store",
    "are __atomic_load_n and __atomic_store_n, with the same orders;",
    "__c11_atomic_init(P, V) stores V without atomicity, as clang does.",
    "A thread fence of a constant order is builtin(void), a fence only",
    "when seq_cst (x86-64 orders the rest itself); a signal fence orders",
    "nothing a single thread can observe.",
    cites('C11 7.17.2.2p2'),
    cites('C11 7.17.4.1p2'),
    cites('C11 7.17.4.2p2'),
    "The read-modify-writes are builtin(T) of the type they return, each",
    "one sequentially consistent atomic step whatever its orders, which",
    "lowering makes a loop of IR's cas (docs/m4.md): __c11_atomic_exchange",
    "and __c11_atomic_fetch_OP (add, sub, and, or, xor, nand, max, min) on",
    "an _Atomic integer return the old value, add and sub also on an",
    "_Atomic pointer, by elements, and exchange also on an _Atomic float",
    "or double; __c11_atomic_compare_exchange_strong and _weak, on any of",
    "these, return whether *P equaled *Expected, bit for bit (so 0.0 is",
    "not -0.0, as clang's cmpxchg of the bits has it), and write *P to",
    "*Expected only when not (a weak one never fails spuriously). GCC's",
    "__atomic_exchange_n, __atomic_fetch_OP, __atomic_OP_fetch (the new",
    "value), __atomic_compare_exchange_n, the __sync builtins and",
    "__atomic_test_and_set and __atomic_clear (a byte at any object",
    "pointer) work on a plain integer, or a pointer to exchange or compare",
    "it; their fetch-and-ops on a pointer are refused (clang adds bytes,",
    "not elements, and filcc cannot compile them).",
    cites('C11 7.17.7.2p2'),
    cites('C11 7.17.7.3p2'),
    cites('C11 7.17.7.4p2'),
    cites('C11 7.17.7.5p2'),
    cites('C11 7.17.7.5p3'),
    cites('C11 7.17.8.1p2'),
    cites('GCC manual, __sync Builtins'),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], int))), E0, E),
              atomic_builtin('__c11_atomic_fetch_add', [id(p), chr(1), chr(5)], E, X) ),
            X = builtin(int)),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], ptr(char)))), E0, E),
              bind_ordinary(e, var(none, ptr(ptr(char))), E, E1),
              atomic_builtin('__c11_atomic_compare_exchange_weak',
                             [id(p), id(e), id(e), chr(5), chr(0)], E1, X) ),
            X = builtin(bool)),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(long)), E0, E),
              atomic_builtin('__sync_add_and_fetch', [id(p), chr(1)], E, X) ),
            X = builtin(long)),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(ptr(int))), E0, E),
            atomic_builtin('__atomic_fetch_add', [id(p), chr(1), chr(5)], E, _) )),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], double))), E0, E),
            atomic_builtin('__c11_atomic_fetch_add', [id(p), chr(1), chr(5)], E, _) )),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], double))), E0, E),
              bind_ordinary(e, var(none, ptr(double)), E, E1),
              atomic_builtin('__c11_atomic_compare_exchange_strong',
                             [id(p), id(e), chr(0), chr(5), chr(5)], E1, X) ),
            X = builtin(bool)),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(double)), E0, E),
            atomic_builtin('__atomic_exchange_n', [id(p), chr(0), chr(5)], E, _) )),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], ptr(void)))), E0, E),
              atomic_builtin('__c11_atomic_load', [id(p), chr(0)], E, X) ),
            X = builtin(ptr(void))),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], double))), E0, E),
              atomic_builtin('__c11_atomic_load', [id(p), chr(5)], E, X) ),
            X = expr(comma(chr(5), un(deref, id(p))))),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(qualified([atomic], int))), E0, E),
              atomic_builtin('__c11_atomic_init', [id(p), chr(1)], E, X) ),
            X = builtin(void)),
    example(( empty_env(E),
              atomic_builtin('__c11_atomic_thread_fence', [chr(2)], E, X) ),
            X = builtin(void)),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(int)), E0, E),
            atomic_builtin('__c11_atomic_load', [id(p), chr(0)], E, _) )),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(int)), E0, E),
            atomic_builtin('__c11_atomic_fetch_add', [id(p), chr(1), chr(5)], E, _) ))
]).
atomic_builtin('__atomic_load_n', [P, O], Env, R) :-
    atomic_operands(P, O, Env, [0, 1, 2, 5], T),
    (   T = ptr(_) -> R = builtin(T)
    ;   R = expr(comma(O, un(deref, P)))
    ).
atomic_builtin('__atomic_store_n', [P, V, O], Env, R) :-
    atomic_operands(P, O, Env, [0, 3, 5], T, Order),
    (   ( T = ptr(_) ; Order =:= 5 ; atomic_pointee(P, Env) ) -> R = builtin(void)
    ;   R = expr(cast(type([tspec(void)], base), comma(O, assign(=, un(deref, P), V))))
    ).
atomic_builtin('__c11_atomic_load', [P, O], Env, R) :-
    atomic_pointee(P, Env),
    c11_operands(P, O, Env, [0, 1, 2, 5], T),
    (   T = ptr(_) -> R = builtin(T)
    ;   R = expr(comma(O, un(deref, P)))
    ).
atomic_builtin('__c11_atomic_store', [P, _, O], Env, builtin(void)) :-
    atomic_pointee(P, Env),
    c11_operands(P, O, Env, [0, 3, 5], _).
atomic_builtin('__c11_atomic_init', [P, _], Env, builtin(void)) :-
    atomic_pointee(P, Env),
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T), atomic_object_type(T).
atomic_builtin(Name, [O], Env, builtin(void)) :-
    fence_builtin(Name),
    catch(const_value(O, Env, V, _), not_constant, fail),
    between(0, 5, V).

atomic_builtin(Name, [P, _, O], Env, builtin(T)) :-
    rmw_builtin(Name, c11, Op, _),
    atomic_pointee(P, Env),
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T),
    rmw_operand(Op, T), order_constant(O, Env).
atomic_builtin(Name, [P, E, _, Os, Of], Env, builtin(bool)) :-
    memberchk(Name, ['__c11_atomic_compare_exchange_strong',
                     '__c11_atomic_compare_exchange_weak']),
    atomic_pointee(P, Env),
    cas_operands(P, E, Env),
    order_constant(Os, Env), order_constant(Of, Env).
atomic_builtin(Name, [P, _, O], Env, builtin(T)) :-
    rmw_builtin(Name, gnu, Op, _),
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T),
    gnu_operand(Op, T), order_constant(O, Env).
atomic_builtin('__atomic_compare_exchange_n', [P, E, _, W, Os, Of], Env, builtin(bool)) :-
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T), gnu_operand(xchg, T),
    cas_operands(P, E, Env),
    order_constant(Os, Env), order_constant(Of, Env),
    catch(const_value(W, Env, _, _), not_constant, fail).
atomic_builtin(Name, [P, _|_], Env, builtin(T)) :-
    rmw_builtin(Name, sync, Op, _),
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T), gnu_operand(Op, T).
atomic_builtin(Name, [P, _, _|_], Env, builtin(R)) :-
    memberchk(Name-R0, ['__sync_val_compare_and_swap'-val,
                        '__sync_bool_compare_and_swap'-bool]),
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T), gnu_operand(xchg, T),
    ( R0 == val -> R = T ; R = bool ).
atomic_builtin('__sync_lock_release', [P|_], Env, builtin(void)) :-
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T), gnu_operand(xchg, T).
atomic_builtin('__sync_synchronize', [], _, builtin(void)).
atomic_builtin(Name, [P, O], Env, builtin(R)) :-
    memberchk(Name-R, ['__atomic_test_and_set'-bool, '__atomic_clear'-void]),
    lowered_type(P, Env, ptr(T)), T \= func(_, _, _),
    order_constant(O, Env).

% rmw_builtin(?Name, ?Family, ?Op, ?Result): Name is a read-modify-write
% of Family (c11 on an _Atomic object, gnu or sync on a plain one) that
% combines the old value and its operand by Op (xchg: the operand), and
% returns the old or the new value (Result).
rmw_builtin('__c11_atomic_exchange', c11, xchg, old).
rmw_builtin(Name, c11, Op, old) :-
    rmw_op(Op, _), Op \== xchg, atom_concat('__c11_atomic_fetch_', Op, Name).
rmw_builtin('__atomic_exchange_n', gnu, xchg, old).
rmw_builtin(Name, gnu, Op, old) :-
    rmw_op(Op, _), Op \== xchg, atom_concat('__atomic_fetch_', Op, Name).
rmw_builtin(Name, gnu, Op, new) :-
    rmw_op(Op, _), Op \== xchg, atomic_list_concat(['__atomic_', Op, '_fetch'], Name).
rmw_builtin('__sync_lock_test_and_set', sync, xchg, old).
rmw_builtin(Name, sync, Op, old) :-
    rmw_op(Op, sync), atom_concat('__sync_fetch_and_', Op, Name).
rmw_builtin(Name, sync, Op, new) :-
    rmw_op(Op, sync), atomic_list_concat(['__sync_', Op, '_and_fetch'], Name).

% rmw_op(?Op, ?Sync): an Op of the fetch-and-op builtins; Sync is sync
% for those __sync has too.
rmw_op(xchg, none).
rmw_op(add, sync). rmw_op(sub, sync). rmw_op(and, sync).
rmw_op(or, sync). rmw_op(xor, sync). rmw_op(nand, sync).
rmw_op(max, none). rmw_op(min, none).

% rmw_operand(+Op, +T): an _Atomic T may be combined by Op: any integer
% by any, a pointer by exchange, add or sub, a float or double by
% exchange.
rmw_operand(_, T) :- int_type(T), !.
rmw_operand(Op, ptr(_)) :- memberchk(Op, [xchg, add, sub]).
rmw_operand(xchg, T) :- memberchk(T, [float, double]).

% gnu_operand(+Op, +T): GCC's builtins take an integer, or a pointer
% only to exchange it.
gnu_operand(_, T) :- int_type(T), !.
gnu_operand(xchg, ptr(_)).

% cas_operands(+P, +E, +Env): Expected E points to an object of *P's
% unqualified type, an integer, pointer, float or double.
cas_operands(P, E, Env) :-
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T),
    ( int_type(T) ; T = ptr(_) ; memberchk(T, [float, double]) ),
    lowered_type(E, Env, ptr(U0)), unqualified(U0, U),
    ( U == T -> true ; T = ptr(_), U = ptr(_) ).

order_constant(O, Env) :-
    catch(const_value(O, Env, V, _), not_constant, fail),
    between(0, 5, V).

fence_builtin('__c11_atomic_thread_fence').
fence_builtin('__c11_atomic_signal_fence').
fence_builtin('__atomic_thread_fence').
fence_builtin('__atomic_signal_fence').

% atomic_pointee(+P, +Env): P points to an _Atomic object.
atomic_pointee(P, Env) :-
    expression_type(P, Env, T0), value_type(T0, ptr(T)), atomic_qualified(T).

% c11_operands(+P, +O, +Env, +Orders, -T): as atomic_operands/5, with a
% float or double *P too.
c11_operands(P, O, Env, Orders, T) :-
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T),
    atomic_object_type(T),
    catch(const_value(O, Env, V, _), not_constant, fail),
    memberchk(V, Orders).

atomic_name('__atomic_load_n').
atomic_name('__atomic_store_n').
atomic_name('__c11_atomic_load').
atomic_name('__c11_atomic_store').
atomic_name('__c11_atomic_init').
atomic_name(Name) :- fence_builtin(Name).
atomic_name(Name) :- rmw_atomic(Name).

% rmw_atomic(?Name): an atomic read-modify-write builtin.
rmw_atomic(Name) :- rmw_builtin(Name, _, _, _).
rmw_atomic(Name) :-
    member(Name, ['__c11_atomic_compare_exchange_strong',
                  '__c11_atomic_compare_exchange_weak', '__atomic_compare_exchange_n',
                  '__sync_val_compare_and_swap', '__sync_bool_compare_and_swap',
                  '__sync_lock_release', '__sync_synchronize',
                  '__atomic_test_and_set', '__atomic_clear']).

% atomic_operands(+P, +O, +Env, +Orders, -T[, -Order]): P points to an
% integer or a pointer of unqualified type T and O is a constant memory
% order Order among Orders (__ATOMIC_RELAXED 0, CONSUME 1, ACQUIRE 2,
% RELEASE 3, ACQ_REL 4, SEQ_CST 5).
atomic_operands(P, O, Env, Orders, T) :- atomic_operands(P, O, Env, Orders, T, _).
atomic_operands(P, O, Env, Orders, T, V) :-
    lowered_type(P, Env, ptr(T0)), unqualified(T0, T),
    ( int_type(T) -> true ; T = ptr(_) ),
    catch(const_value(O, Env, V, _), not_constant, fail),
    memberchk(V, Orders).

doc(builtin_type(?(Name), ?(Type)), nondet, [
    Name: "a builtin's name",
    Type: "the type of a call of it",
    "A call of builtin Name, when Name is not declared, has Type. The",
    "bit builtins count trailing or leading zero bits, or one bits, of",
    "an unsigned int, long or long long, giving an int; the byte swaps",
    "give the unsigned type of their width.",
    cites('GCC manual, Other Built-in Functions'),
    example(builtin_type('__builtin_ctzll', T), T = int),
    example(builtin_type('__builtin_bswap16', T), T = ushort),
    example(builtin_type('__builtin_bswap64', T), T = ulong),
    "__builtin_isnan(x) is nonzero for a NaN of any floating type (an",
    "integer converts to double first). __builtin_flt_rounds() is",
    "FLT_ROUNDS, the current rounding direction: 0 toward zero, 1 to",
    "nearest, 2 upward, 3 downward.",
    cites('C11 5.2.4.2.2p8'),
    cites('C11 7.12.3.4p2'),
    example(builtin_type('__builtin_isnan', T), T = int),
    "__builtin_assume_aligned(p, align[, offset]) is p as a void *; the",
    "alignment it promises changes no bounds, so nanofil drops it.",
    example(builtin_type('__builtin_assume_aligned', T), T = ptr(void)),
    fails(builtin_type('__builtin_ctzlll', _))
]).
builtin_type('__builtin_va_start', void).
builtin_type('__builtin_va_copy', void).
builtin_type('__builtin_va_end', void).
builtin_type('__builtin_unreachable', void).
builtin_type('__builtin_alloca', ptr(void)).
builtin_type('__builtin_expect', long).
builtin_type('__builtin_assume_aligned', ptr(void)).
builtin_type('__builtin_constant_p', int).
builtin_type(Name, bool) :- overflow_builtin(Name, _, _).
builtin_type(Name, int) :- bit_builtin(Name, _, _).
builtin_type('__builtin_bswap16', ushort).
builtin_type('__builtin_bswap32', uint).
builtin_type('__builtin_bswap64', ulong).
builtin_type(Name, double) :- libm_builtin(Name, _).
builtin_type('__builtin_isnan', int).
builtin_type('__builtin_flt_rounds', int).
builtin_type('__builtin_object_size', ulong).
builtin_type('__builtin_dynamic_object_size', ulong).
builtin_type(Name, int) :- classify_builtin(Name).

doc(classify_builtin(?(Name)), nondet, [
    Name: "a type-generic classification builtin glibc's math.h uses",
    "__builtin_isinf_sign(x) is 1 for +inf, -1 for -inf, else 0;",
    "__builtin_isfinite, __builtin_isnormal and __builtin_signbit are 1",
    "or 0; __builtin_fpclassify(Nan, Inf, Normal, Subnormal, Zero, x) is",
    "the argument for x's class. A float classifies as itself, an integer",
    "or double as a double; a long double is refused (its narrowing to",
    "double would change its class), except by the signbit builtins:",
    "__builtin_signbitl(x) is __builtin_signbit((long double)x), and",
    "__builtin_signbitf(x) __builtin_signbit((float)x).",
    cites('C11 7.12.3'),
    cites('GCC manual, Other Built-in Functions'),
    example(classify_builtin('__builtin_fpclassify')),
    fails(classify_builtin('__builtin_isinf'))
]).
classify_builtin('__builtin_isinf_sign').
classify_builtin('__builtin_isfinite').
classify_builtin('__builtin_isnormal').
classify_builtin('__builtin_signbit').
classify_builtin('__builtin_signbitl').
classify_builtin('__builtin_signbitf').
classify_builtin('__builtin_fpclassify').

doc(libm_builtin(?(Name), ?(F)), nondet, [
    Name: "a GNU math builtin",
    F: "the libm function it computes",
    "__builtin_ceil(x) and __builtin_floor(x) are ceil(x) and floor(x)",
    "of x converted to double, even with F undeclared. Clang computes",
    "them inline (roundsd); a call of libm's F gives the same exact",
    "result, signed zeros and NaNs included.",
    cites('GCC manual, Other Built-in Functions'),
    cites('C11 7.12.9.1p2'),
    cites('C11 7.12.9.2p2'),
    example(libm_builtin('__builtin_floor', F), F = floor),
    fails(libm_builtin('__builtin_round', _))
]).
libm_builtin('__builtin_ceil', ceil).
libm_builtin('__builtin_floor', floor).

doc(bit_builtin(?(Name), ?(Op), ?(Type)), nondet, [
    Name: "a bit-counting builtin",
    Op: "ctz, clz or popcount",
    Type: "its operand's type: uint, ulong or ullong",
    cites('GCC manual, Other Built-in Functions'),
    example(bit_builtin('__builtin_clzl', Op, T), (Op, T) = (clz, ulong)),
    example(bit_builtin('__builtin_popcount', Op, T), (Op, T) = (popcount, uint)),
    fails(bit_builtin('__builtin_ffs', _, _))
]).
bit_builtin(Name, Op, Type) :-
    member(Op, [ctz, clz, popcount]),
    member(Suffix-Type, [''-uint, l-ulong, ll-ullong]),
    atomic_list_concat(['__builtin_', Op, Suffix], Name).

% overflow_builtin(?Name, ?Op, ?Fixed): builtin Name checks arithmetic Op
% on operands of type Fixed, or of any integer types (generic).
overflow_builtin(Name, Op, Fixed) :-
    member(Op, [add, sub, mul]),
    (   atomic_list_concat(['__builtin_', Op, '_overflow'], Name),
        Fixed = generic
    ;   member(Prefix-Suffix-Fixed,
               [s-''-int, u-''-uint, s-l-long, u-l-ulong,
                s-ll-llong, u-ll-ullong]),
        atomic_list_concat(['__builtin_', Prefix, Op, Suffix, '_overflow'], Name)
    ).

% block_value_type(+Items, +Env, -T): T is the value type of a GNU
% statement expression with block Items: its last item's, once the
% items before it have declared their names.
block_value_type([], _, void).
block_value_type([Item], Env, T) :- !, last_item_type(Item, Env, T).
block_value_type([decl(_, Specs, Inits)|Items], Env0, T) :- !,
    decl_types(Specs, Inits, Decls, Env0, Env1),
    foldl(bind_decl, Decls, Env1, Env),
    block_value_type(Items, Env, T).
block_value_type([_|Items], Env, T) :- block_value_type(Items, Env, T).

bind_decl(d(Name, Type, _, _, _), Env0, Env) :-
    bind_ordinary(Name, var(none, Type), Env0, Env).

last_item_type(at(_, expr(E)), Env, T) :- !, operand(E, Env, _, T).
last_item_type(at(_, label(_, Body)), Env, T) :- !, last_item_type(Body, Env, T).
last_item_type(_, _, void).

%% Lvalues, values and designators

doc(tree_type(+X, -T), det, [
    X: "a typed tree",
    T: "its type",
    example(tree_type(fun(func(int, [], fixed), id(f)), T), T = func(int, [], fixed))
]).
tree_type(X, T) :- arg(1, X, T).

doc(tree_category(+X, -Cat), det, [
    X: "a typed tree",
    Cat: "lvalue, function or value, as its principal functor says",
    cites('C11 6.3.2.1p1'),
    example(tree_category(obj(int, id(x)), C), C = lvalue),
    example(tree_category(val(int, int(1)), C), C = value)
]).
tree_category(obj(_, _), lvalue).
tree_category(fun(_, _), function).
tree_category(val(_, _), value).

doc(value(+X, -V), det, [
    X: "a typed tree",
    V: "X used for its value",
    "An array becomes a pointer to its first element, a function a",
    "pointer to it, and another lvalue the value it holds, unqualified.",
    cites('C11 6.3.2.1p2'),
    cites('C11 6.3.2.1p3'),
    cites('C11 6.3.2.1p4'),
    example(value(obj(qualified([const], int), id(c)), V),
            V = val(int, load(obj(qualified([const], int), id(c))))),
    example(value(obj(array(int, 4), id(a)), V),
            V = val(ptr(int), decay(obj(array(int, 4), id(a))))),
    example(value(fun(func(int, [], fixed), id(f)), V),
            V = val(ptr(func(int, [], fixed)), decay(fun(func(int, [], fixed), id(f))))),
    example(value(val(int, int(7)), V), V = val(int, int(7)))
]).
value(obj(T, bitfield(M, W)), val(V, load(obj(T, bitfield(M, W))))) :- !,
    value_type(T, T1), bitfield_promotion(T1, W, V).
value(obj(T, F), val(V, decay(obj(T, F)))) :- array_type(T), !, value_type(T, V).
value(obj(T, F), val(V, load(obj(T, F)))) :- value_type(T, V).
value(fun(T, F), val(ptr(T), decay(fun(T, F)))).
value(val(T, F), val(V, F)) :- value_type(T, V).

doc(bitfield_promotion(+T, +W, -P), det, [
    T: "the unqualified integer type of a bit-field",
    W: "its width in bits",
    P: "the type of its value",
    "A bit-field's value is an int if an int can represent all its",
    "values, otherwise an unsigned int if that can, otherwise of its own",
    "type. C11 says so for _Bool, int and unsigned int; clang and GCC",
    "treat bit-fields of the other integer types alike.",
    cites('C11 6.3.1.1p2'),
    example(bitfield_promotion(uint, 31, P), P = int),
    example(bitfield_promotion(uint, 32, P), P = uint),
    example(bitfield_promotion(int, 32, P), P = int),
    example(bitfield_promotion(ulong, 32, P), P = uint),
    example(bitfield_promotion(ulong, 33, P), P = ulong),
    example(bitfield_promotion(long, 33, P), P = long),
    example(bitfield_promotion(bool, 1, P), P = int)
]).
bitfield_promotion(T, W, P) :-
    int_info(T, _, Sign),
    (   ( Sign == signed -> W =< 32 ; W < 32 ) -> P = int
    ;   W =< 32 -> P = uint
    ;   P = T
    ).

array_type(qualified(_, T)) :- array_type(T).
array_type(array(_, _)).

doc(value_type(+T, -V), det, [
    T: "the type of an expression",
    V: "the type of its value",
    "value/2 on types alone.",
    example(value_type(qualified([volatile], long), V), V = long),
    example(value_type(array(char, 3), V), V = ptr(char)),
    example(value_type(func(void, unspecified, fixed), V),
            V = ptr(func(void, unspecified, fixed)))
]).
value_type(qualified(_, T), R) :- !, value_type(T, R).
value_type(array(T, _), ptr(T)) :- !.
value_type(func(R, P, V), ptr(func(R, P, V))) :- !.
value_type(T, T).

% operand(+E, +Env, -XV, -T): XV is E elaborated and used for its value,
% of type T.
operand(E, Env, XV, T) :- elaborate(E, Env, X), value(X, XV), tree_type(XV, T).

doc(expression_type(+E, +Env, -T), semidet, [
    E: "a C expression",
    Env: "the scope it is read in",
    T: "its reflected type, unevaluated",
    "Arrays and functions keep their types until a caller asks for value",
    "conversion.",
    example(( empty_env(E0), bind_ordinary(a, var(none, array(int, 4)), E0, E),
              expression_type(id(a), E, T) ),
            T = array(int, 4))
]).
expression_type(E, Env, T) :- elaborate(E, Env, X), tree_type(X, T).

doc(expression_category(+E, +Env, -Cat), semidet, [
    E: "a C expression",
    Env: "the scope it is read in",
    Cat: "lvalue, function or value",
    cites('C11 6.3.2.1p1'),
    example(( empty_env(E0), bind_ordinary(x, var(none, int), E0, E),
              expression_category(id(x), E, C) ),
            C = lvalue),
    example(( empty_env(E0), bind_ordinary(f, fn(func(int, [], fixed), f, extern), E0, E),
              expression_category(id(f), E, C) ),
            C = function),
    example(( empty_env(E0), bind_ordinary(x, var(none, int), E0, E),
              expression_category(bin(add, id(x), chr(0)), E, C) ),
            C = value)
]).
expression_category(E, Env, Cat) :-
    elaborate(E, Env, X), tree_category(X, Cat0), Cat = Cat0.

doc(modifiable_lvalue(+E, +Env), semidet, [
    E: "a C expression",
    Env: "the scope it is read in",
    "E is an lvalue whose type is not const, an array or incomplete, nor",
    "a struct or union with a const member, however deeply contained.",
    cites('C11 6.3.2.1p1'),
    example(( empty_env(E0), bind_ordinary(x, var(none, int), E0, E),
              modifiable_lvalue(id(x), E) )),
    fails(( empty_env(E0), bind_ordinary(c, var(none, int), E0, E1),
            bind_ordinary(qtype(c), qualified([const], int), E1, E),
            modifiable_lvalue(id(c), E) )),
    fails(( empty_env(E0), bind_ordinary(a, var(none, array(int, 4)), E0, E),
            modifiable_lvalue(id(a), E) )),
    fails(( empty_env(E), modifiable_lvalue(chr(0), E) ))
]).
modifiable_lvalue(E, Env) :- elaborate(E, Env, X), modifiable(X, Env).

% modifiable(+X, +Env): typed tree X designates a modifiable object.
modifiable(obj(T, _), Env) :- modifiable_type(T, Env).

modifiable_type(qualified(Qs, T), Env) :- !,
    \+ memberchk(const, Qs), modifiable_type(T, Env).
modifiable_type(array(_, _), _) :- !, fail.
modifiable_type(void, _) :- !, fail.
modifiable_type(T, Env) :- \+ const_within(T, Env).

% const_within(+T, +Env): T is const, or an aggregate or union with a
% const member or element, at any depth.
const_within(qualified(Qs, _), _) :- memberchk(const, Qs), !.
const_within(qualified(_, T), Env) :- const_within(T, Env).
const_within(array(T, _), Env) :- const_within(T, Env).
const_within(SU, Env) :-
    ( SU = struct(Id) ; SU = union(Id) ), Env = e(_, _, Defs, _),
    get_assoc(qmembers(Id), Defs, Members),
    member(q(_, T), Members), const_within(T, Env), !.

%% Operators

doc(unary_operand(+Op, +T0, -T), semidet, [
    Op: "plus, neg, bnot or not",
    T0: "the value type of the operand",
    T: "the type of the result",
    "+ and - need an arithmetic operand and ~ an integer, which they",
    "promote; ! needs a scalar and gives an int.",
    cites('C11 6.5.3.3p1'),
    cites('C11 6.5.3.3p5'),
    example(unary_operand(neg, char, T), T = int),
    example(unary_operand(plus, ullong, T), T = ullong),
    example(unary_operand(not, ptr(int), T), T = int),
    fails(unary_operand(bnot, double, _)),
    fails(unary_operand(neg, ptr(int), _))
]).
unary_operand(Op, T0, T) :-
    memberchk(Op, [plus, neg]), arithmetic_type(T0), integer_promotion(T0, T).
unary_operand(bnot, T0, T) :- int_type(T0), integer_promotion(T0, T).
unary_operand(not, T0, int) :- scalar_type(T0).

% expression_binary_type(+Op, +TA, +TB, -T): binary Op on operands of
% value types TA and TB has type T; && and || give an int (6.5.13-14).
expression_binary_type(Op, A, B, int) :-                  % 6.5.13p2, 6.5.14p2
    memberchk(Op, [land, lor]), !,
    scalar_type(A), scalar_type(B).
expression_binary_type(Op, A, B, T) :- binary_operands(Op, A, B, _, _, T).

doc(binary_operands(+Op, +TA, +TB, -CA, -CB, -T), semidet, [
    Op: "a binary operator, not && or ||",
    TA: "the value type of the left operand",
    TB: "the value type of the right operand",
    CA: "the type the left operand converts to",
    CB: "the type the right operand converts to",
    T: "the type of the result",
    "A shift promotes each operand on its own and has the left one's",
    "type. Other arithmetic operands take their usual arithmetic type,",
    "the result's type unless Op compares; %, &, ^ and | need integers.",
    "A pointer and an integer add, or the pointer subtracts the integer,",
    "as the pointer and a long count of elements; two pointers subtract",
    "to a long count. A comparison with a pointer compares both operands",
    "as addresses, ulong. Fails if Op does not apply.",
    cites('C11 6.5.5p2'),
    cites('C11 6.5.6p2'),
    cites('C11 6.5.6p9'),
    cites('C11 6.5.7p3'),
    cites('C11 6.5.8p6'),
    example(binary_operands(shl, char, ullong, CA, CB, T),
            (CA = int, CB = ullong, T = int)),
    example(binary_operands(add, int, uint, CA, CB, T),
            (CA = uint, CB = uint, T = uint)),
    example(binary_operands(lt, int, double, CA, CB, T),
            (CA = double, CB = double, T = int)),
    example(binary_operands(add, char, ptr(int), CA, CB, T),
            (CA = long, CB = ptr(int), T = ptr(int))),
    example(binary_operands(sub, ptr(int), ptr(int), _, _, T), T = long),
    example(binary_operands(eq, ptr(int), int, CA, CB, T),
            (CA = ulong, CB = ulong, T = int)),
    fails(binary_operands(mod, double, int, _, _, _)),
    fails(binary_operands(sub, int, ptr(int), _, _, _))
]).
binary_operands(Op, TA, TB, CA, CB, CA) :- memberchk(Op, [shl, shr]), !,
    int_type(TA), int_type(TB),
    integer_promotion(TA, CA), integer_promotion(TB, CB).
binary_operands(Op, TA, TB, C, C, T) :-
    arithmetic_operator(Op, Domain),
    call(Domain, TA), call(Domain, TB), !,
    usual_arith_conversion(TA, TB, C),
    ( comparison(Op) -> T = int ; T = C ).
binary_operands(Op, ptr(P), TB, ptr(P), long, ptr(P)) :-
    memberchk(Op, [add, sub]), int_type(TB), !.
binary_operands(add, TA, ptr(P), long, ptr(P), ptr(P)) :- int_type(TA), !.
binary_operands(sub, ptr(P), ptr(_), ptr(P), ptr(P), long) :- !.
binary_operands(Op, TA, TB, ulong, ulong, int) :-
    comparison(Op), ( TA = ptr(_) ; TB = ptr(_) ), !.

% arithmetic_operator(?Op, ?Domain): binary Op applies to two operands
% of Domain types, arithmetic or integer.
arithmetic_operator(Op, Domain) :-
    c_operator(_, _, Op, Kind),
    operand_domain(Kind, Domain).

operand_domain(arith(integer), int_type).
operand_domain(arith(arithmetic), arithmetic_type).
operand_domain(compare, arithmetic_type).

comparison(Op) :- c_operator(_, _, Op, compare).

doc(castable(+From, +To), semidet, [
    From: "the unqualified value type of the operand",
    To: "the type named in the cast",
    "Anything casts to void, and a scalar to a scalar, but a floating",
    "value not to or from a pointer. As in clang and GCC, a struct or",
    "union may also be cast to its own type.",
    cites('C11 6.5.4p2'),
    cites('C11 6.5.4p4'),
    example(castable(struct(1), void)),
    example(castable(ptr(char), long)),
    example(castable(struct(1), struct(1))),
    fails(castable(double, ptr(int))),
    fails(castable(ptr(int), float)),
    fails(castable(int, struct(1)))
]).
castable(_, void) :- !.
castable(A, B) :- arithmetic_type(A), arithmetic_type(B), !.
castable(ptr(_), B) :- ( B = ptr(_) ; int_type(B) ), !.
castable(A, ptr(_)) :- int_type(A), !.
castable(T, U) :- T == U, ( T = struct(_) ; T = union(_) ).

doc(assignable(+From, +Null, +To), semidet, [
    From: "the value type of the right operand",
    Null: "null if the right operand is a null pointer constant, else value",
    To: "the unqualified type of the object assigned",
    "A value of type From may be assigned to an object of type To, and so",
    "passed for a parameter of type To, returned from a function",
    "returning To, or initialize a To. Integers and pointers do not mix,",
    "but for a null pointer constant or a pointer tested as a bool, and",
    "function pointers must be compatible. Clang only warns about the",
    "other pointer pairs (incompatible object types, lost qualifiers,",
    "object and function pointers), and they are accepted.",
    cites('C11 6.5.16.1p1'),
    example(assignable(double, value, char)),
    example(assignable(ptr(int), value, bool)),
    example(assignable(int, null, ptr(int))),
    example(assignable(ptr(int), value, ptr(char))),
    fails(assignable(int, value, ptr(int))),
    fails(assignable(ptr(func(int, [], fixed)), value, ptr(func(void, [], fixed)))),
    fails(assignable(struct(1), value, struct(2)))
]).
assignable(From, _, To) :- arithmetic_type(From), arithmetic_type(To), !.
assignable(T, _, U) :- T == U, !.
assignable(ptr(_), _, bool) :- !.
assignable(_, null, ptr(_)) :- !.
assignable(ptr(A), _, ptr(B)) :-
    ( A = func(_, _, _), B = func(_, _, _) -> compatible_type(A, B) ; true ).

doc(conditional_type(+Arms, +Env, -T), semidet, [
    Arms: "A-B, the second and third operands of ?:",
    Env: "the scope they are read in",
    T: "the type of the result",
    "From the arms' value types; fails if the arms are incompatible or",
    "cannot be typed.",
    cites('C11 6.5.15p5'),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(char)), E0, E),
              conditional_type(chr(0)-id(p), E, T) ),
            T = ptr(char)),
    fails(( empty_env(E0), bind_ordinary(p, var(none, ptr(char)), E0, E),
            conditional_type(chr(1)-id(p), E, _) ))
]).
conditional_type(A-B, Env, T) :- arms(A, B, Env, _, _, T).

% arms(+A, +B, +Env, -XA, -XB, -T): A and B, elaborated as XA and XB,
% used for their values, are ?: arms giving the result type T.
arms(A, B, Env, XA, XB, T) :-
    operand(A, Env, XA, TA), operand(B, Env, XB, TB),
    arm_nullness(TB, XA, Env, NA), arm_nullness(TA, XB, Env, NB),
    arms_type(TA, NA, TB, NB, T).

% arm_nullness(+Other, +XV, +Env, -N): N is arm XV's nullness/3 when the
% other arm has the pointer type Other, the only case arms_type/5 reads
% it; else value. Folding every arm made nested ?: (gnulib's intprops)
% fold each subexpression once per enclosing ?:.
arm_nullness(ptr(_), XV, Env, N) :- !, nullness(XV, Env, N).
arm_nullness(_, _, _, value).

doc(assigned(+E, +Env, +To, +Loc), det, [
    E: "an expression that can be typed",
    Env: "the scope it is read in",
    To: "the type of the object its value initializes",
    Loc: "where E is, for the diagnostic",
    "E's value may be assigned to a To, as a return value or an",
    "initializer is; else the error names the two types. Arguments and",
    "assignment sources are checked where their calls and assignments",
    "elaborate.",
    cites('C11 6.5.16.1p1, 6.8.6.4p3, 6.7.9p11'),
    example(( empty_env(E), assigned(chr(0), E, ptr(int), none) )),
    example(( empty_env(E), assigned(chr(1), E, double, none) ))
]).
assigned(E, Env, To, Loc) :-
    elaborate(E, Env, X), value(X, XV), lowered(XV, T),
    nullness(XV, Env, N),
    (   assignable(T, N, To) -> true
    ;   sema_error(Loc, 'cannot assign ~w to ~w', [T, To])
    ).

% nullness(+XV, +Env, -N): value tree XV is a null pointer constant
% (null) or not (value).
nullness(XV, Env, N) :- null_pointer_constant(XV, Env), !, N = null.
nullness(_, _, value).

doc(null_pointer_constant(+XV, +Env), semidet, [
    XV: "a typed tree, used for its value",
    Env: "the scope it was elaborated in",
    "XV is an integer constant expression of value 0, or one cast to",
    "void * (unqualified void).",
    cites('C11 6.3.2.3p3'),
    example(( empty_env(E), operand(bin(sub, chr(7), chr(7)), E, XV, _),
              null_pointer_constant(XV, E) )),
    example(( empty_env(E), operand(cast(type([tspec(void)], ptr(base, [])), chr(0)), E, XV, _),
              null_pointer_constant(XV, E) )),
    fails(( empty_env(E),
            operand(cast(type([qual(const), tspec(void)], ptr(base, [])), chr(0)), E, XV, _),
            null_pointer_constant(XV, E) )),
    fails(( empty_env(E), operand(chr(1), E, XV, _),
            null_pointer_constant(XV, E) )),
    fails(( empty_env(E0), bind_ordinary(x, var(none, int), E0, E),
            operand(bin(mul, id(x), chr(0)), E, XV, _),
            null_pointer_constant(XV, E) ))
]).
null_pointer_constant(XV, Env) :-
    lowered(XV, T), int_type(T), folded(XV, Env, 0).
null_pointer_constant(val(ptr(void), cast(_, XV)), Env) :-
    null_pointer_constant(XV, Env).

doc(arms_type(+TA, +NA, +TB, +NB, -T), semidet, [
    TA: "the value type of the second operand of ?:",
    NA: "null if it is a null pointer constant, else value",
    TB: "the value type of the third operand",
    NB: "null if it is a null pointer constant, else value",
    T: "the type of the result",
    "Arithmetic arms take their usual arithmetic type, like structs or",
    "unions their own. A null pointer constant takes the other arm's",
    "pointer type. Pointer arms point to the composite of their targets,",
    "qualified with both arms' qualifiers, or to void if either does. As",
    "in clang and GCC, a void arm makes the result void whatever the",
    "other arm, and incompatible pointer arms give void *; a pointer and",
    "a nonnull integer are rejected.",
    cites('C11 6.5.15p3'),
    cites('C11 6.5.15p5'),
    cites('C11 6.5.15p6'),
    example(arms_type(char, value, short, value, T), T = int),
    example(arms_type(void, value, int, value, T), T = void),
    example(arms_type(ptr(int), value, int, null, T), T = ptr(int)),
    example(arms_type(int, null, ptr(char), value, T), T = ptr(char)),
    example(arms_type(ptr(qualified([const], int)), value, ptr(void), value, T),
            T = ptr(qualified([const], void))),
    example(arms_type(ptr(array(int, none)), value, ptr(array(int, 3)), value, T),
            T = ptr(array(int, 3))),
    example(arms_type(ptr(int), value, ptr(long), value, T), T = ptr(void)),
    fails(arms_type(ptr(int), value, int, value, _)),
    fails(arms_type(struct(1), value, struct(2), value, _))
]).
arms_type(TA, _, TB, _, T) :-
    arithmetic_type(TA), arithmetic_type(TB), !,
    usual_arith_conversion(TA, TB, T).
arms_type(void, _, _, _, void) :- !.
arms_type(_, _, void, _, void) :- !.
arms_type(T, _, U, _, T) :- T == U, ( T = struct(_) ; T = union(_) ), !.
arms_type(ptr(P), _, _, null, ptr(P)) :- !.
arms_type(_, null, ptr(P), _, ptr(P)) :- !.
arms_type(ptr(A), _, ptr(B), _, ptr(T)) :-
    target(A, QA, A1), target(B, QB, B1), append(QA, QB, Qs),
    pointed_type(A1, B1, Qs, T).

% target(+T, -Qs, -U): pointer target T is U qualified with Qs.
target(qualified(Qs, U), Qs, U) :- !.
target(U, [], U).

% pointed_type(+A, +B, +Qs, -T): pointer arms to unqualified A and B
% point to T, qualified with Qs (6.5.15p6).
pointed_type(A, B, Qs, T) :- ( A == void ; B == void ), !, qualify(Qs, void, T).
pointed_type(A, B, Qs, T) :- composite_type(A, B, C), !, qualify(Qs, C, T).
pointed_type(_, _, _, void).

%% Generic selection

% The controlling expression undergoes lvalue/array/function conversion,
% not integer promotion. Only the selected expression is evaluated, and
% its value category is retained. Association types must be unique even
% when they do not match the controlling type.
generic_selection(ControlType, Associations, Env, Loc, Selected) :-
    maplist(generic_association(Env, Loc), Associations, Typed),
    generic_unique(Typed, Loc),
    ( member(assoc(T, E), Typed), T \== default, compatible_type(ControlType, T)
    -> Selected = E
    ; memberchk(assoc(default, E), Typed) -> Selected = E
    ; sema_error(Loc, '_Generic has no matching association', [])
    ).

generic_association(_, _, assoc(default, E), assoc(default, E)) :- !.
generic_association(Env, Loc, assoc(TN, E), assoc(T, E)) :-
    type_name_type(TN, T0, Env, _),
    ( complete_type(T0, Env), T0 \= func(_, _, _)
    -> true
    ; sema_error(Loc, '_Generic association requires a complete object type', [])
    ),
    reflect_type(TN, T0, Env, T).

generic_unique([], _).
generic_unique([assoc(T, _)|Rest], Loc) :-
    ( member(assoc(U, _), Rest), compatible_type(T, U)
    -> sema_error(Loc, '_Generic has duplicate compatible associations', [])
    ; generic_unique(Rest, Loc)
    ).

%% Diagnoses

/*  When an expression cannot be typed, fault/4 says why: it finds the
    first operand, in the order lowering evaluates them, that cannot be
    typed, and the rule it breaks. The messages are lowering's, which
    the reject tests hold to. Where lowering would first refuse
    something the elaborator accepts (a type nanofil does not support, a
    struct or union passed by value, a va_arg or a statement expression),
    fault/4 declines rather than misplace the blame, and lowering
    reports. */

doc(elaborate(+E, +Env, +Loc, -X), semidet, [
    E: "a full expression",
    Env: "the scope it is read in",
    Loc: "where it is, for a diagnostic",
    X: "its typed tree",
    "elaborate/3, raising the diagnosis at Loc when E cannot be typed.",
    "Fails, raising nothing, when fault/4 declines to say why.",
    example(( empty_env(E), elaborate(chr(1), E, here, X) ), X = val(int, int(1))),
    example(( empty_env(E),
              catch(elaborate(id(g), E, here, _), nanofil_error(M), true) ),
            M == 'here: undeclared identifier g')
]).
elaborate(E, Env, Loc, X) :-
    (   elaborate(E, Env, X0) -> X = X0
    ;   fault(E, Env, Format, Args) -> sema_error(Loc, Format, Args)
    ).

doc(fault(+E, +Env, -Format, -Args), semidet, [
    E: "an expression that cannot be typed",
    Env: "the scope it is read in",
    Format: "the diagnostic's format",
    Args: "its arguments, with types unqualified as lowering has them",
    "The first fault in E, in evaluation order, or first a type in E",
    "that nanofil does not support. Fails",
    "when it is not one the elaborator diagnoses.",
    example(( empty_env(E), fault(bin(add, chr(1), id(g)), E, F, A) ),
            (F = 'undeclared identifier ~w', A = [g])),
    example(( empty_env(E0), bind_ordinary(x, var(none, double), E0, E1),
              bind_ordinary(qtype(x), qualified([const], double), E1, E),
              fault(bin(mod, id(x), chr(2)), E, F, A) ),
            (F = 'invalid operands to ~w: ~w and ~w', A = [mod, double, int])),
    example(( empty_env(E0), bind_ordinary(p, var(none, ptr(int)), E0, E1),
              bind_ordinary(d, var(none, double), E1, E),
              fault(cond(id(g), id(p), id(d)), E, F, A) ),
            (F = 'incompatible ?: operands ~w and ~w', A = [ptr(int), double])),
    example(( empty_env(E0), bind_ordinary(x, var(none, int), E0, E),
              fault(arrow(id(x), f), E, F, _) ),
            F = '-> on a non-pointer'),
    example(( empty_env(E0), bind_ordinary(c, var(none, int), E0, E1),
              bind_ordinary(qtype(c), qualified([const], int), E1, E),
              fault(assign(=, id(c), id(g)), E, F, A) ),
            (F = '~w a read-only lvalue', A = ['assignment to'])),
    example(( empty_env(E0),
              bind_ordinary(f, fn(func(void, [ptr(char), int], fixed), f, extern), E0, E),
              fault(call(id(f), [chr(0), chr(1), id(g)]), E, F, A) ),
            (F = 'too many arguments to ~w', A = [f])),
    example(( empty_env(E0),
              bind_ordinary(f, fn(func(void, [ptr(char), int], fixed), f, extern), E0, E),
              fault(call(id(f), [chr(1), id(g)]), E, F, A) ),
            (F = 'cannot assign ~w to ~w', A = [int, ptr(char)])),
    example(( empty_env(E0), bind_ordinary(s, var(none, struct('builtin.va_list')), E0, E),
              fault(bin(lor, chr(0), id(s)), E, F, A) ),
            (F = 'a ~w value is not a scalar', A = [struct('builtin.va_list')]))
]).
fault(E, Env, Format, Args) :-
    (   unsupported(E, Env, F, As) -> Format = F, Args = As
    ;   fault_(E, Env, Format, Args)
    ).

fault_(id(Name), _, 'undeclared identifier ~w', [Name]).
fault_(label_addr(Name), _, 'the address of label ~w outside its function', [Name]).
fault_(index(A, I), Env, F, As) :- fault_(un(deref, bin(add, A, I)), Env, F, As).
fault_(un(Op, E), Env, F, As) :-
    (   untyped(E, Env) -> fault_(E, Env, F, As)
    ;   Op == deref -> F = 'dereferencing a non-pointer', As = []
    ;   Op == addr, elaborate(E, Env, obj(_, bitfield(_, _)))
    ->  F = 'cannot take the address of a bit-field', As = []
    ;   Op == addr -> F = '& of a non-lvalue', As = []
    ;   memberchk(Op, [plus, neg, bnot, not])
    ->  lowered_type(E, Env, T), F = 'invalid operand to ~w: ~w', As = [Op, T]
    ;   elaborate(E, Env, X), \+ modifiable(X, Env)
    ->  atom_concat(Op, ' of', What), modifiable_fault(X, What, F, As)
    ;   F = '~w of a non-scalar lvalue', As = [Op]
    ).
fault_(member(E, Field), Env, F, As) :-
    (   untyped(E, Env) -> fault_(E, Env, F, As)
    ;   elaborate(E, Env, XS), member_subject(XS)
    ->  F = 'no member named ~w', As = [Field]
    ;   F = 'member access on a non-lvalue', As = []
    ).
fault_(arrow(E, Field), Env, F, As) :-
    (   untyped(E, Env) -> fault_(E, Env, F, As)
    ;   lowered_type(E, Env, ptr(_)) -> F = 'no member named ~w', As = [Field]
    ;   F = '-> on a non-pointer', As = []
    ).
fault_(cast(TN, E), Env, F, As) :-
    type_name_type(TN, To, Env, _),
    (   untyped(E, Env) -> fault_(E, Env, F, As)
    ;   lowered_type(E, Env, From), F = 'cannot convert ~w to ~w', As = [From, To]
    ).
fault_(bit_cast(TN, E), Env, F, As) :-
    type_name_type(TN, To, Env, _),
    (   untyped(E, Env) -> fault_(E, Env, F, As)
    ;   lowered_type(E, Env, From),
        F = '__builtin_bit_cast from ~w to ~w, which is not an object of the same size that is not an array',
        As = [From, To]
    ).
fault_(call(id(Name), _), Env, F, [Name]) :-
    \+ lookup_ordinary(Env, Name, _), atomic_name(Name), !,
    (   rmw_atomic(Name)
    ->  F = '~w needs a pointer to an integer (an _Atomic one for __c11 builtins), or to a pointer to exchange, compare it or (__c11) add to it, and constant memory orders'
    ;   fence_builtin(Name)
    ->  F = '~w needs a constant memory order'
    ;   atom_concat('__c11', _, Name)
    ->  F = '~w needs a pointer to an _Atomic integer, pointer, float or double and a constant memory order it supports (relaxed, consume, acquire or seq_cst for a load; relaxed, release or seq_cst for a store)'
    ;   F = '~w needs a pointer to an integer or pointer and a constant memory order it supports (relaxed, consume, acquire or seq_cst for a load; relaxed, release or seq_cst for a store)'
    ).
fault_(call(id(Name), _), Env, F, [Name, Chk, Plain]) :-
    \+ lookup_ordinary(Env, Name, _), checking_builtin(Name, Chk, Plain), !,
    F = '~w needs ~w declared, or ~w declared and an object size of (size_t)-1'.
fault_(call(Fn, Args), Env, F, As) :-
    \+ ( Fn = id(Name), \+ lookup_ordinary(Env, Name, _),
         ( builtin_type(Name, _) ; float_builtin(Name, _, _) ) ),
    (   untyped(Fn, Env) -> fault_(Fn, Env, F, As)
    ;   \+ lowered_type(Fn, Env, ptr(func(_, _, _)))
    ->  F = 'called object is not a function', As = []
    ;   lowered_type(Fn, Env, ptr(func(_, Ps, V))),
        callee_name(Fn, Env, Sym),
        (   arity_fault(Ps, V, Args, Sym, F0, As0) -> F = F0, As = As0
        ;   arguments_fault(Ps, Args, Env, F, As)
        )
    ).
fault_(assign(Op, A, B), Env, F, As) :-
    (   untyped(A, Env) -> fault_(A, Env, F, As)
    ;   elaborate(A, Env, X), \+ modifiable(X, Env)
    ->  modifiable_fault(X, 'assignment to', F, As)
    ;   elaborate(A, Env, X), tree_type(X, T0), unqualified(T0, TA),
        ( Op == (=) -> true ; scalar_type(TA) ),
        (   untyped(B, Env) -> fault_(B, Env, F, As)
        ;   lowered_type(B, Env, TB), assignment_fault(Op, TA, TB, F, As)
        )
    ).
fault_(comma(A, B), Env, F, As) :- operands_fault([A, B], Env, F, As).
fault_(sizeof_expr(E), Env, F, As) :-
    (   untyped(E, Env) -> fault_(E, Env, F, As)
    ;   F = 'sizeof of a bit-field', As = []
    ).
fault_(bin(Op, A, B), Env, F, As) :-
    memberchk(Op, [land, lor]), !,
    (   scalar_fault(A, Env, F, As) -> true
    ;   scalar_fault(B, Env, F, As)
    ).
fault_(bin(Op, A, B), Env, F, As) :-
    (   operands_fault([A, B], Env, F, As) -> true
    ;   maplist(lowered_type_in(Env), [A, B], [TA, TB]),
        F = 'invalid operands to ~w: ~w and ~w', As = [Op, TA, TB]
    ).
fault_(cond(C, A, B), Env, F, As) :-
    (   arms_fault(A, B, Env, F, As) -> true
    ;   scalar_fault(C, Env, F, As)
    ).
fault_(gcond(C, B), Env, F, As) :-
    (   arms_fault(C, B, Env, F, As) -> true
    ;   scalar_fault(C, Env, F, As)
    ).
fault_(generic(C, As0), Env, F, As) :-
    (   untyped(C, Env) -> fault_(C, Env, F, As)
    ;   operand(C, Env, _, CT),
        generic_selection(CT, As0, Env, constant, E),
        fault_(E, Env, F, As)
    ).

% arms_fault(+A, +B, +Env, -F, -As): the first fault of ?: arms A and B,
% lowered first, then whether they go together (6.5.15p3).
arms_fault(A, B, Env, F, As) :-
    (   operands_fault([A, B], Env, F, As) -> true
    ;   \+ conditional_type(A-B, Env, _),
        maplist(lowered_type_in(Env), [A, B], [TA, TB]),
        F = 'incompatible ?: operands ~w and ~w', As = [TA, TB]
    ).

% operands_fault(+Es, +Env, -F, -As): the fault of the first of Es that
% cannot be typed.
operands_fault(Es, Env, F, As) :-
    member(E, Es), untyped(E, Env), !,
    fault_(E, Env, F, As).

untyped(E, Env) :- \+ elaborate(E, Env, _).

% scalar_fault(+E, +Env, -F, -As): E, tested for truth, cannot be typed
% or is not a scalar.
scalar_fault(E, Env, F, As) :-
    (   untyped(E, Env) -> fault_(E, Env, F, As)
    ;   lowered_type(E, Env, T), \+ scalar_type(T),
        F = 'a ~w value is not a scalar', As = [T]
    ).

% modifiable_fault(+X, +What, -F, -As): X, the operand of What, is not a
% modifiable lvalue.
modifiable_fault(obj(_, _), What, '~w a read-only lvalue', [What]) :- !.
modifiable_fault(_, What, '~w a non-lvalue', [What]).

% assignment_fault(+Op, +TA, +TB, -F, -As): why assignment Op cannot
% store a value of type TB into an object of type TA.
assignment_fault(=, TA, TB, 'cannot assign ~w to ~w', [TB, TA]) :- !.
assignment_fault(Op, TA, TB, F, As) :-
    compound_assignment(Op, BinOp),
    (   binary_operands(BinOp, TA, TB, _, _, T)
    ->  F = 'cannot assign ~w to ~w', As = [T, TA]
    ;   F = 'invalid operands to ~w: ~w and ~w', As = [BinOp, TA, TB]
    ).

% callee_name(+Fn, +Env, -Sym): lowering names a call's callee by its
% symbol when Fn names a function, else as a function pointer.
callee_name(id(Name), Env, Sym) :- lookup_ordinary(Env, Name, fn(_, Sym, _)), !.
callee_name(_, _, 'function pointer').

% arity_fault(+Ps, +V, +Args, +Sym, -F, -As): Args are too few or too
% many for parameters Ps of callee Sym.
arity_fault(Ps, V, Args, Sym, F, [Sym]) :-
    Ps \== unspecified, length(Ps, NP), length(Args, NA),
    (   NA < NP -> F = 'too few arguments to ~w'
    ;   NA > NP, V == fixed -> F = 'too many arguments to ~w'
    ).

% arguments_fault(+Ps, +Args, +Env, -F, -As): the first argument, in
% order, that cannot be typed or passed for its parameter. Lowering may
% refuse a struct or union argument, or an unpromotable variadic one,
% before it reaches a later one, so those end the search.
arguments_fault(Ps, [A|Args], Env, F, As) :-
    param_split(Ps, P, Ps1),
    (   untyped(A, Env) -> fault_(A, Env, F, As)
    ;   operand(A, Env, XA, _), lowered(XA, T),
        (   P == none
        ->  ( arithmetic_type(T) -> true ; T = ptr(_) ),
            arguments_fault(Ps1, Args, Env, F, As)
        ;   unqualified(P, TP), nullness(XA, Env, N),
            (   \+ assignable(T, N, TP)
            ->  F = 'cannot assign ~w to ~w', As = [T, TP]
            ;   TP \= struct(_), TP \= union(_),
                arguments_fault(Ps1, Args, Env, F, As)
            )
        )
    ).

param_split(unspecified, none, unspecified).
param_split([], none, []).
param_split([P|Ps], P, Ps).

% member_subject(+XS): lowering looks for members in XS, an lvalue or a
% struct or union value; it refuses other values.
member_subject(obj(_, _)).
member_subject(val(T, _)) :- unqualified(T, U), ( U = struct(_) ; U = union(_) ).

% lowered_type(+E, +Env, -T): T is E's value type as lowering has it,
% unqualified.
lowered_type(E, Env, T) :- operand(E, Env, _, T0), unqualified(T0, T).
lowered_type_in(Env, E, T) :- lowered_type(E, Env, T).

% unsupported(+E, +Env, -F, -As): the first type name in E that names a
% type nanofil does not support, and why.
unsupported(E, Env, F, As) :-
    E = type(_, _), !,
    type_name_type(E, T, Env, _),
    unsupported_type(T, F, As).
unsupported(E, Env, F, As) :-
    compound(E), E =.. [_|Xs],
    member(X, Xs), unsupported(X, Env, F, As), !.

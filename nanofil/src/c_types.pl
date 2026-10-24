/*  C types (milestone 4a): specifiers and declarators to type terms,
    sizes and layouts, integer conversions and constant expressions.

    Types:
      void bool char schar uchar short ushort int uint long ulong llong
      ullong float double ldouble
      ptr(T)  array(T, N | none)  func(Ret, Params, fixed | variadic)
      struct(Id)  union(Id)
    Params is a list of types (already adjusted: arrays and functions
    become pointers) or unspecified. Qualifiers are dropped. Enum types are
    their underlying integer type. A type the frontend cannot handle yet
    is bad(Reason); it is only an error when a declaration uses it, so
    headers that mention such types still parse.

    The semantic environment is e(Ords, Tags, Defs, Next):
      Ords  assoc, Name -> typedef(T) | enumconst(V, T) | anything the
            lowering stores (variables and functions)
      Tags  assoc, Name -> tag(struct | union, Id) | enum(T)
      Defs  assoc, Id -> incomplete(Tag) | def(Kind, Members, Size, Align)
            | partial(Reason, Members) | bad(Reason); partial keeps only
            members with known offsets, not a usable object layout.
            The lowering keeps entries of its own here too
            Tag: some(Name), or none for an anonymous struct or union
            Members: [m(Name, Type, Offset)], Name some(Field), or none
            for an anonymous struct or union member
      Next  the next struct id
    Block scopes save Ords and Tags and restore them on exit; Defs and
    Next only grow. Predicates that change the environment take Env0 and
    give Env as their last two arguments, so they thread through
    foldl/4,6.
*/
:- module(c_types, [empty_env/1, specs_type/4, apply_declarator/5,
                    type_size_align/4, complete_type/2, int_type/1, int_info/3,
                    integer_promotion/2, usual_arith_conversion/3,
                    float_type/1, arithmetic_type/1, default_promotion/2,
                    constant_value/4, const_convert/4, float_literal/3,
                    float_builtin/3,
                    convert_int/3, const_value/4, pp_value/2, num_type/3,
                    scalar_type/1, type_class/2, member_type_offset/5, type_name_type/4,
                    lookup_ordinary/3, bind_ordinary/4, env_scope/3,
                    env_restore/3, sema_error/3, enum_underlying/2,
                    decl_types/5, expression_type/3, value_type/2,
                    generic_selection/5, reflect_type/4, reflect_params/4,
                    conditional_type/3, unqualified/2,
                    overflow_builtin/3, binary_operands/6,
                    unary_operand/3, assignable/3, null_pointer_constant/3,
                    castable/2, expression_category/3, modifiable_lvalue/2,
                    integer_type/4, elaborate/3, tree_type/2, value/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ieee).

% Documentation is a relation of the module, doc(Head, Det, Props)
% (docs/dterm.md); tests/unit.pl runs every example.
:- discontiguous(doc/3).
:- use_module(c_parse, [c_operator/4]).

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
%  under the specifiers Specs, Storage one of none, static or extern. A
%  typedef declares no Decls; Env is Env0 with its names bound instead.
%  Env also has any struct, union or enum Specs defines. Throws
%  not_constant when an enumerator's value is not constant.

decl_types(Specs, Inits, Decls, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    (   memberchk(storage(Storage0), Specs) -> Storage = Storage0
    ;   Storage = none
    ),
    foldl(declarator_type(Specs, Base, Storage), Inits, Decls0, Env1, Env),
    exclude(==(none), Decls0, Decls).

% declarator_type(+Specs, +Base, +Storage, +Init, -Decl, +Env0, -Env): Decl is
% the d/5 term Init declares, or none for a typedef, which binds the name.
declarator_type(Specs, Base, Storage, init(dcl(some(Name), SyntaxType, Asm), Init),
                Decl, Env0, Env) :-
    apply_declarator(SyntaxType, Base, Type, Env0, Env1),
    reflect_type(type(Specs, SyntaxType), Type, Env1, Reflected),
    bind_ordinary(qtype(Name), Reflected, Env1, Env2),
    (   Storage == typedef
    ->  bind_ordinary(Name, typedef(Type), Env2, Env),
        Decl = none
    ;   Env = Env2,
        Decl = d(Name, Type, Storage, Asm, Init)
    ).

% Keep qualification for type reflection without changing the unqualified
% code-generation types. These entries share ordinary identifier scope,
% including shadowing and typedefs. Lvalue conversion removes only the
% outer qualification, never the qualification of a pointer's target.
reflect_type(type(Specs, Syntax), Type, Env, Reflected) :-
    reflect_declarator(Syntax, Specs, Type, Env, Reflected).

reflect_declarator(base, Specs, Type, Env, Reflected) :-
    ( memberchk(tname(Name), Specs), lookup_ordinary(Env, qtype(Name), T)
    -> Base = T
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
    value_type(R0, RT).

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
    (   member(Spec, Specs), layout_attr(Spec)
    ->  Type = bad('alignment attributes')
    ;   Type = Type0
    ).

% layout_attr(+Spec): Spec is an attribute that changes layout, which
% the frontend does not model. The cut commits to the first such word.
layout_attr(alignas(_)).
layout_attr(attr(Tokens)) :-
    is_list(Tokens),
    attr_word(Tokens, Word),
    memberchk(Word, [aligned, '__aligned__', packed, '__packed__']),
    !.

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

% Clang retains the SysV va_list array/record layout; Fil-C stores its
% capability-bearing cursor in the first word and ignores the rest.
named_type(tname('__builtin_va_list'), array(struct('builtin.va_list'), 1),
           Env, Env) :- !.
named_type(tname(Name), Type, Env, Env) :-
    (   lookup_ordinary(Env, Name, typedef(Type0)) -> Type = Type0
    ;   Type = bad('unknown typedef')
    ).
named_type(typeof(_), bad('typeof'), Env, Env).
named_type(su(Kind, Tag, Members, Attrs), Type, Env0, Env) :-
    su_type(Members, Kind, Tag, Attrs, Type, Env0, Env).
named_type(enum(Tag, Enumerators), Type, Env0, Env) :-
    enum_type(Enumerators, Tag, Type, Env0, Env).

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
    (   member(Attr, Attrs), layout_attr(attr(Attr))
    ->  Def = bad('alignment attributes')
    ;   memberchk(bad(Why), Fields)
    ->  known_field_prefix(Fields, Prefix),
        su_layout(Kind, Prefix, Env2, PrefixDef),
        (   PrefixDef = def(_, Known, _, _)
        ->  Def = partial(Why, Known)
        ;   Def = bad(Why)
        )
    ;   su_layout(Kind, Fields, Env2, Def)
    ),
    Env2 = e(Ords, Tags2, Defs0, Next),
    put_assoc(Id, Defs0, Def, Defs1),
    put_assoc(qmembers(Id), Defs1, Reflected, Defs2),
    Env = e(Ords, Tags2, Defs2, Next).

% A later unsupported member (notably glibc FILE's _flags2 bitfield)
% does not change preceding offsets. Never infer offsets beyond it, or
% a size/alignment for the whole object; those uses must still reject.
known_field_prefix([], []).
known_field_prefix([bad(_)|_], []) :- !.
known_field_prefix([f(Name, Type)|Fields], [f(Name, Type)|Prefix]) :-
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
% f(Name, Type) the member declaration Decl declares ([] for a static
% assertion), or [bad(Why)]; Name is some(Field), or none for an
% anonymous member. Reflected are the q(Name, QType) of the same
% members, QType keeping the qualifiers that Type drops.
member_decl(static_assert(_, _, _), [], [], Env, Env).
member_decl(field(Specs, dcl(Name, SyntaxType, _), Width), Fields,
            Reflected, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    (   Width \== none
    ->  Fields = [bad('bitfields')], Reflected = [],
        Env = Env1
    ;   apply_declarator(SyntaxType, Base, Type, Env1, Env),
        (   bad_type(Type, Why) -> Fields = [bad(Why)], Reflected = []
        ;   Fields = [f(Name, Type)],
            reflect_type(type(Specs, SyntaxType), Type, Env, QType),
            Reflected = [q(Name, QType)]
        )
    ).

% su_layout(+Kind, +Fields, +Env, -Def), with the SysV rules: each member
% at the next multiple of its alignment; size rounded up to the
% alignment. A trailing flexible array member has size 0.
su_layout(Kind, Fields, Env, Def) :-
    catch(fields_layout(Kind, Fields, Env, Layout), bad(Why),
          Layout = bad(Why)),
    layout_def(Layout, Kind, Def).

% fields_layout(+Kind, +Fields, +Env, -Layout): Layout is
% placed(Members, End, Align) for Fields laid out in Env, or incomplete
% when a field has no size. Throws bad(Why) as type_size_align/4.
fields_layout(Kind, Fields, Env, Layout) :-
    (   foldl(field_member(Kind, Env), Fields, Members, 0-1, End-Align)
    ->  Layout = placed(Members, End, Align)
    ;   Layout = incomplete
    ).

% layout_def(+Layout, +Kind, -Def): Def is the definition of a struct or
% union of Kind with Layout, its size rounded up to its alignment.
layout_def(placed(Members, End, Align), Kind, def(Kind, Members, Size, Align)) :-
    Size is (End + Align - 1) // Align * Align.
layout_def(incomplete, _, bad('incomplete member')).
layout_def(bad(Why), _, bad(Why)).

% field_member(+Kind, +Env, +Field, -Member, +End0-Align0, -End-Align):
% Member is Field placed after members ending at End0 with alignment
% Align0; End and Align include it. Throws bad(Why) as type_size_align/4.
% Any type but a flexible array (array(_, none)) has its own size, so the
% if-then-else keeps that default case.
field_member(Kind, Env, f(Name, Type), m(Name, Type, Off), End0-Align0,
             End-Align) :-
    (   Type = array(ElemType, none)
    ->  type_size_align(ElemType, Env, _, FieldAlign),
        FieldSize = 0
    ;   type_size_align(Type, Env, FieldSize, FieldAlign)
    ),
    member_offset_end(Kind, End0, FieldSize, FieldAlign, Off, End),
    Align is max(Align0, FieldAlign).

% member_offset_end(+Kind, +End0, +Size, +Align, -Off, -End): a member of
% Size and Align after members ending at End0 is at Off and ends the
% struct or union so far at End.
member_offset_end(struct, End0, Size, Align, Off, End) :-
    Off is (End0 + Align - 1) // Align * Align,
    End is Off + Size.
member_offset_end(union, End0, Size, _, 0, End) :-
    End is max(End0, Size).

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

%! apply_declarator(+SyntaxType, +Base, -Type, +Env0, -Env) is det.
%
%  Type is the declarator type SyntaxType with the atom base replaced by
%  Base, array sizes evaluated and parameter types resolved. The parser
%  builds declarator types outermost first around base. An array size
%  that is not a non-negative constant gives bad(Reason). Env is Env0
%  with the definitions of any struct or union a parameter list
%  declares; their names are scoped to the list.
apply_declarator(base, Base, Base, Env, Env).
apply_declarator(ptr(Syntax, _), Base, ptr(Type), Env0, Env) :-
    apply_declarator(Syntax, Base, Type, Env0, Env).
apply_declarator(array(Syntax, SizeExpr), Base, Type, Env0, Env) :-
    apply_declarator(Syntax, Base, ElemType, Env0, Env),
    (   SizeExpr == none
    ->  Type = array(ElemType, none)
    ;   catch(const_value(SizeExpr, Env, N, _), not_constant, fail), N >= 0
    ->  Type = array(ElemType, N)
    ;   Type = bad('non-constant array size')
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

param_type(param(Specs, dcl(_, SyntaxType, _)), Type, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    apply_declarator(SyntaxType, Base, Type0, Env1, Env),
    type_adjusted(Type0, Type).

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
%  looking into anonymous members. Fails if it has none, or SU is not
%  defined.
member_type_offset(SU, Name, Env, Type, Off) :-
    SU =.. [_, Id],
    Env = e(_, _, Defs, _),
    get_assoc(Id, Defs, Def),
    known_members(Def, Members),
    (   member(m(some(Name), Type, Off), Members) -> true
    ;   member(m(none, AnonType, AnonOff), Members),
        member_type_offset(AnonType, Name, Env, Type, InnerOff)
    ->  Off is AnonOff + InnerOff
    ).

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
    "The floating types nanofil supports; long double is refused.",
    cites('C11 6.2.5p10'),
    fails(float_type(ldouble))
]).
float_type(float).
float_type(double).

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
    "a pointer, s and d for float and double. Deterministic when Type is",
    "bound.",
    example(type_class(ushort, K), K = w),
    example(type_class(ullong, K), K = l),
    example(type_class(ptr(void), K), K = p),
    example(type_class(float, K), K = s),
    fails(type_class(struct(0), _))
]).
type_class(T, K) :- integer_type(T, Size, _, _), ( Size =:= 8 -> K = l ; K = w ).
type_class(float, s).
type_class(double, d).
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
    ; memberchk(Suffix, [l, 'L'])
    -> sema_error(constant, 'long double is not supported', [])
    ; Type = double, Digits = Cs
    ),
    type_class(Type, K), ieee:ieee_parse(K, Digits, Bits).

% glibc's HUGE_VAL and INFINITY are builtin constant expressions, not
% libm calls. Keep the value bits exact, including in static storage.
float_builtin('__builtin_huge_val', double, 0x7ff0000000000000).
float_builtin('__builtin_inf', double, 0x7ff0000000000000).
float_builtin('__builtin_huge_valf', float, 0x7f800000).
float_builtin('__builtin_inff', float, 0x7f800000).

% C arithmetic conversion of a constant. An undefined float-to-int
% conversion propagates ub, just like integer division by zero.
const_convert(ub, _, _, ub) :- !.
const_convert(V, T, T, V) :- !.
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

% const_eval(+Expr, +Env, -V, -T): Expr has value V, an integer or ub,
% of type T in Env. Fails when Expr is not a constant expression.
const_eval(num(V0, Suffix), Env, V, T) :-
    num_type(V0, Suffix, T0),
    env_int_type(Env, T0, T),
    convert_int(V0, T, V).
const_eval(float(Cs), e(_, _, _, _), V, T) :- float_literal(Cs, V, T).
const_eval(call(id(Name), []), Env, V, T) :-
    float_builtin(Name, T, V), \+ lookup_ordinary(Env, Name, _).
const_eval(chr(V), Env, V, T) :- env_int_type(Env, int, T).
const_eval(id(Name), Env, V, T) :- lookup_ordinary(Env, Name, enumconst(V, T)).
const_eval(un(not, X), Env, V, T) :-
    const_eval(X, Env, V0, T0),
    env_int_type(Env, int, T),
    const_truth(V0, T0, B),
    defined([B], V, truth(B =:= 0, V)).
const_eval(un(Op, X), Env, V, T) :-
    const_eval(X, Env, V0, T0),
    integer_promotion(T0, T),
    defined([V0], V, constant_unary(T, Op, V0, V)).
const_eval(bin(Op, A, B), Env, V, T) :-
    binary_kind(Op, Kind),
    const_eval(A, Env, VA, TA),
    const_eval(B, Env, VB, TB),
    kind_binary(Kind, Op, Env, VA, TA, VB, TB, V, T).
const_eval(cond(C, A, B), Env, V, T) :-
    const_eval(C, Env, VC, TC),
    const_eval(A, Env, VA, TA),
    const_eval(B, Env, VB, TB),
    usual_arith_conversion(TA, TB, T),
    const_truth(VC, TC, Test),
    defined([Test], V,
            ( Test =\= 0 -> const_convert(VA, TA, T, V)
            ; const_convert(VB, TB, T, V) )).
const_eval(cast(TypeName, X), Env, V, T) :-
    type_name_type(TypeName, T, Env, _),
    arithmetic_type(T),
    const_eval(X, Env, V0, From),
    const_convert(V0, From, T, V).
const_eval(sizeof_type(TypeName), Env, V, ulong) :-
    type_name_type(TypeName, T, Env, _),
    catch(type_size_align(T, Env, V, _), bad(_), fail).
const_eval(sizeof_expr(Expr), Env, V, ulong) :-
    expression_type(Expr, Env, T),
    catch(type_size_align(T, Env, V, _), bad(_), fail).
const_eval(generic(Control, Associations), Env, V, T) :-
    expression_type(Control, Env, CT0),
    value_type(CT0, CT),
    generic_selection(CT, Associations, Env, constant, Selected),
    const_eval(Selected, Env, V, T).
const_eval(alignof(TypeName), Env, V, ulong) :-
    type_name_type(TypeName, T, Env, _),
    catch(type_size_align(T, Env, _, V), bad(_), fail).
const_eval(offsetof(TypeName, Path), Env, V, ulong) :-
    type_name_type(TypeName, T, Env, _),
    offset_path(Path, T, Env, 0, V).
const_eval(comma(_, B), Env, V, T) :- const_eval(B, Env, V, T).

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

% env_int_type(+Env, +T0, -T): an integer of type T0 has type T in Env:
% T0 itself, or in a #if expression intmax_t or uintmax_t.
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

% kind_binary(+Kind, +Op, +Env, +VA, +TA, +VB, +TB, -V, -T): V of type T
% is the value of Op, of Kind, on VA of type TA and VB of type TB.
% Arithmetic and comparison use the usual arithmetic conversions; a
% shift has its promoted left operand's type.
kind_binary(arith, Op, _, VA, TA, VB, TB, V, T) :-
    usual_arith_conversion(TA, TB, T),
    defined([VA, VB], V,
            (   const_convert(VA, TA, T, A),
                const_convert(VB, TB, T, B),
                ( float_type(T)
                -> type_class(T, K), memberchk(Op, [add, sub, mul, div]),
                   ieee:ieee_binary(K, Op, A, B, V)
                ; const_arith(Op, A, B, R), int_value(R, T, V)
                )
            )).
kind_binary(shift, Op, _, VA, TA, VB, _, V, T) :-
    integer_promotion(TA, T),
    defined([VA, VB], V,
            (   convert_int(VA, T, A),
                const_shift(Op, A, VB, R),
                convert_int(R, T, V)
            )).
kind_binary(compare, Op, Env, VA, TA, VB, TB, V, T) :-
    usual_arith_conversion(TA, TB, CT),
    env_int_type(Env, int, T),
    defined([VA, VB], V,
            (   const_convert(VA, TA, CT, A),
                const_convert(VB, TB, CT, B),
                ( float_type(CT)
                -> type_class(CT, K), ieee:ieee_compare(K, Op, A, B, V)
                ; truth(const_compare(Op, A, B), V)
                )
            )).
kind_binary(logical, Op, Env, VA, TA, VB, TB, V, T) :-
    env_int_type(Env, int, T),
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
    "it, a function's parameters where either has a prototype. Fails when",
    "T and U are not compatible.",
    cites('C11 6.2.7p3'),
    example(composite_type(ptr(array(int, none)), ptr(array(int, 3)), C),
            C = ptr(array(int, 3))),
    example(composite_type(func(int, unspecified, fixed),
                           func(int, [ptr(char)], fixed), C),
            C = func(int, [ptr(char)], fixed)),
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
composite_size(N, N, N).

% composite_params(+Ps, +Qs, -Cs): parameter lists Ps and Qs, each
% unspecified without a prototype, agree on Cs.
composite_params(unspecified, Qs, Qs) :- !.
composite_params(Ps, unspecified, Ps) :- !.
composite_params(Ps, Qs, Cs) :- maplist(composite_type, Ps, Qs, Cs).

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
    association's. A child that is not elaborated yet is src(E), the
    source expression itself. */

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
    example(( empty_env(E), elaborate(str([104, 105]), E, X) ),
            X = obj(array(char, 3), str([104, 105]))),
    fails(( empty_env(E), elaborate(un(deref, chr(1)), E, _) ))
]).
elaborate(E, Env, X) :- elab(E, Env, X0), !, X = X0.

elab(id(Name), Env, X) :-
    lookup_ordinary(Env, Name, Binding), !,
    identifier_type(Binding, Name, Env, T),
    binding_node(Binding, T, Name, X).
elab(id(Name), _, obj(array(char, none), predefined(Name))) :-   % 6.4.2.2
    memberchk(Name, ['__func__', '__FUNCTION__', '__PRETTY_FUNCTION__']).
elab(num(V0, S), _, val(T, int(V))) :- num_type(V0, S, T), convert_int(V0, T, V).
elab(chr(V), _, val(int, int(V))).
elab(float(Cs), _, val(T, float(Cs))) :-
    last(Cs, Suffix),
    ( memberchk(Suffix, [f, 'F']) -> T = float
    ; memberchk(Suffix, [l, 'L']) -> T = ldouble
    ; T = double
    ).
elab(str(Bytes), _, obj(array(char, N), str(Bytes))) :-
    length(Bytes, M), N is M + 1.
elab(wstr(T, Values), _, obj(array(T, N), wstr(T, Values))) :-
    length(Values, M), N is M + 1.
elab(cast(TN, E), Env, val(T, cast(XV))) :-
    type_name_type(TN, T0, Env, _),
    operand(E, Env, XV, F0), unqualified(F0, F),
    castable(F, T0),
    reflect_type(TN, T0, Env, T).
elab(complit(TN, Init), Env, obj(T, complit(Init))) :-
    type_name_type(TN, T0, Env, _), reflect_type(TN, T0, Env, T).
elab(un(addr, E), Env, val(ptr(T), addr(X))) :-
    elaborate(E, Env, X), tree_type(X, T).
elab(un(deref, E), Env, X) :-
    operand(E, Env, XV, ptr(T)),
    designator(T, deref(XV), X).
elab(un(Op, E), Env, val(T, incdec(Op, X))) :-
    memberchk(Op, [preinc, predec, postinc, postdec]),
    elaborate(E, Env, X), tree_type(X, T0), value_type(T0, T).
elab(un(Op, E), Env, val(T, un(Op, XV))) :-
    memberchk(Op, [plus, neg, bnot, not]),
    operand(E, Env, XV, T1),
    unary_operand(Op, T1, T).
elab(index(A, I), Env, X) :-                                % 6.5.2.1p2
    elab(un(deref, bin(add, A, I)), Env, X).
elab(member(E, F), Env, X) :-
    elaborate(E, Env, XS), tree_type(XS, SU), member_type(SU, F, Env, T),
    member_node(XS, F, T, X).
elab(arrow(E, F), Env, X) :-                                % 6.5.2.3p4
    elab(member(un(deref, E), F), Env, X).
elab(call(id(Name), Args), Env, val(T, builtin(Name, Args))) :-
    \+ lookup_ordinary(Env, Name, _),
    (   Args == [], float_builtin(Name, T, _) -> true
    ;   builtin_type(Name, T)
    ).
elab(call(E, Args), Env, val(T, call(XV, src(Args)))) :-
    operand(E, Env, XV, ptr(func(T, _, _))).
elab(assign(Op, A, B), Env, val(T, assign(Op, X, src(B)))) :-
    elaborate(A, Env, X), tree_type(X, T).
elab(comma(A, B), Env, val(T, comma(src(A), XV))) :-
    operand(B, Env, XV, T).
elab(sizeof_expr(E), _, val(ulong, sizeof(src(E)))).
elab(sizeof_type(TN), _, val(ulong, sizeof(TN))).
elab(alignof(TN), _, val(ulong, alignof(TN))).
elab(offsetof(TN, Path), _, val(ulong, offsetof(TN, Path))).
elab(bin(Op, A, B), Env, val(T, bin(Op, XA, XB))) :-
    operand(A, Env, XA, TA), operand(B, Env, XB, TB),
    expression_binary_type(Op, TA, TB, T).
elab(cond(C, A, B), Env, val(T, cond(src(C), XA, XB))) :-
    arms(A, B, Env, XA, XB, T).
elab(gcond(C, B), Env, val(T, gcond(XC, XB))) :-
    arms(C, B, Env, XC, XB, T).
elab(va_arg(A, TN), Env, val(T, va_arg(src(A)))) :-
    type_name_type(TN, T0, Env, _), reflect_type(TN, T0, Env, T).
elab(stmtexpr(at(Loc, block(Items))), Env, val(T, stmtexpr(at(Loc, block(Items))))) :-
    block_value_type(Items, Env, T).
elab(generic(C, As), Env, X) :-                             % 6.5.1.1
    operand(C, Env, _, CT),
    generic_selection(CT, As, Env, constant, E),
    elaborate(E, Env, X).

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

% builtin_type(?Name, ?Type): a call of builtin Name, when Name is not
% declared, has Type.
builtin_type('__builtin_va_start', void).
builtin_type('__builtin_va_copy', void).
builtin_type('__builtin_va_end', void).
builtin_type('__builtin_unreachable', void).
builtin_type('__builtin_alloca', ptr(void)).
builtin_type('__builtin_expect', long).
builtin_type('__builtin_constant_p', int).
builtin_type(Name, bool) :- overflow_builtin(Name, _, _).

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
value(obj(T, F), val(V, decay(obj(T, F)))) :- array_type(T), !, value_type(T, V).
value(obj(T, F), val(V, load(obj(T, F)))) :- value_type(T, V).
value(fun(T, F), val(ptr(T), decay(fun(T, F)))).
value(val(T, F), val(V, F)) :- value_type(T, V).

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
modifiable_lvalue(E, Env) :-
    elaborate(E, Env, obj(T, _)),
    modifiable_type(T, Env).

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
expression_binary_type(Op, _, _, int) :- memberchk(Op, [land, lor]), !.
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
    arm(A, Env, XA, TA, NA), arm(B, Env, XB, TB, NB),
    arms_type(TA, NA, TB, NB, T).

arm(E, Env, XV, T, N) :-
    operand(E, Env, XV, T),
    nullness(E, Env, T, N).

% nullness(+E, +Env, +T, -N): E, of value type T, is a null pointer
% constant (null) or not (value).
nullness(E, Env, T, N) :- null_pointer_constant(E, Env, T), !, N = null.
nullness(_, _, _, value).

doc(null_pointer_constant(+E, +Env, +T), semidet, [
    E: "a C expression",
    Env: "the scope it is read in",
    T: "its value type",
    "E is an integer constant expression of value 0, or one cast to",
    "void * (unqualified void).",
    cites('C11 6.3.2.3p3'),
    example(( empty_env(E), null_pointer_constant(bin(sub, chr(7), chr(7)), E, int) )),
    fails(( empty_env(E), null_pointer_constant(chr(1), E, int) )),
    fails(( empty_env(E0), bind_ordinary(x, var(none, int), E0, E),
            null_pointer_constant(bin(mul, id(x), chr(0)), E, int) ))
]).
null_pointer_constant(E, Env, T) :-
    int_type(T), catch(const_value(E, Env, 0, _), not_constant, fail).
null_pointer_constant(cast(_, X), Env, ptr(void)) :-
    operand(X, Env, _, TX),
    null_pointer_constant(X, Env, TX).

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

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
      Defs  assoc, Id -> incomplete(Name) | def(Kind, Members, Size, Align)
            | bad(Reason); the lowering keeps entries of its own here too
            Members: [m(Name, Type, Offset)], Name none for an
            anonymous struct or union member
      Next  the next struct id
    Block scopes save Ords and Tags and restore them on exit; Defs and
    Next only grow.
*/
:- module(c_types, [empty_env/1, specs_type/4, apply_dcl/5, size_align/4,
                    complete/2, int_type/1, int_info/3, promote/2, usual/3,
                    wrap/3, const_value/4, num_type/3, scalar/1, class_of/2,
                    find_member/5, type_name_type/4, ord/3, put_ord/4,
                    env_scope/3, env_restore/3, sema_error/3,
                    enum_underlying/2, decl_types/5]).

:- use_module(library(lists)).
:- use_module(library(assoc)).

%% Environment

empty_env(e(Ords, Tags, Defs, 0)) :-
    empty_assoc(Ords),
    empty_assoc(Tags),
    empty_assoc(Defs).

% ord(+Env, +Name, -Value): the ordinary identifier Name.
ord(e(Ords, _, _, _), Name, Value) :- get_assoc(Name, Ords, Value).

put_ord(Name, Value, e(Ords0, Tags, Defs, Next), e(Ords, Tags, Defs, Next)) :-
    put_assoc(Name, Ords0, Value, Ords).

% env_scope(+Env, -Scope, _) saves the scoped part of Env;
% env_restore(+Scope, +Env0, -Env) puts it back.
env_scope(e(Ords, Tags, _, _), s(Ords, Tags), _).
env_restore(s(Ords, Tags), e(_, _, Defs, Next), e(Ords, Tags, Defs, Next)).

sema_error(Loc, Fmt, Args) :-
    format(atom(Msg0), Fmt, Args),
    format(atom(Msg), '~w: ~w', [Loc, Msg0]),
    throw(nanofil_error(Msg)).

%% Declarations

% decl_types(+Specs, +Inits, -Declared, +Env0, -Env): resolve a
% declaration. Typedefs are entered into Env; every other declarator is
% returned as d(Name, Type, Storage, Asm, Init), Storage one of none,
% static, extern, typedef excluded.
decl_types(Specs, Inits, Decls, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    (   memberchk(storage(Storage0), Specs) -> Storage = Storage0
    ;   Storage = none
    ),
    foldl(declarator_type(Base, Storage), Inits, Decls0, Env1, Env),
    exclude(==(none), Decls0, Decls).

declarator_type(Base, Storage, init(dcl(Name, SyntaxType, Asm), Init), Decl,
                Env0, Env) :-
    apply_dcl(SyntaxType, Base, Type, Env0, Env1),
    (   Storage == typedef
    ->  put_ord(Name, typedef(Type), Env1, Env),
        Decl = none
    ;   Env = Env1,
        Decl = d(Name, Type, Storage, Asm, Init)
    ).

%% Specifiers

% specs_type(+Specs, -Type, +Env0, -Env): the type the specifiers name.
% Struct, union and enum definitions in Specs are entered into Env.
specs_type(Specs, Type, Env0, Env) :-
    base_type(Specs, Type0, Env0, Env),
    (   member(Spec, Specs), layout_attr(Spec)
    ->  Type = bad('alignment attributes')
    ;   Type = Type0
    ).

% An attribute that changes layout, which the frontend does not model.
layout_attr(alignas(_)).
layout_attr(attr(Tokens)) :-
    is_list(Tokens),
    attr_word(Tokens, Word),
    memberchk(Word, [aligned, '__aligned__', packed, '__packed__']), !.

% attr_word(+Tokens, -Word): an identifier anywhere in an attribute's
% tokens, looking into groups.
attr_word(Tokens, Word) :-
    member(Token, Tokens),
    (   Token = id(Word)
    ;   Token = group(Group),
        attr_word(Group, Word)
    ).

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

named_type(tname(Name), Type, Env, Env) :-
    (   ord(Env, Name, typedef(Type0)) -> Type = Type0
    ;   Name == '__builtin_va_list' -> Type = bad('va_list')
    ;   Type = bad('unknown typedef')
    ).
named_type(typeof(_), bad('typeof'), Env, Env).
named_type(su(Kind, Tag, Members, Attrs), Type, Env0, Env) :-
    su_type(Kind, Tag, Members, Attrs, Type, Env0, Env).
named_type(enum(Tag, Enumerators), Type, Env0, Env) :-
    enum_type(Tag, Enumerators, Type, Env0, Env).

keyword_type([], int) :- !.   % implicit int, as in old headers' K&R style
keyword_type(Keywords, Type) :-
    msort(Keywords, Sorted),
    (   keyword_combo(Sorted, Type0) -> Type = Type0
    ;   Type = bad('invalid type specifiers')
    ).

% keyword_combo(+SortedKeywords, -Type)
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

% su_type(+Kind, +Tag, +Members, +Attrs, -Type, +Env0, -Env): Members is
% none for a reference to the tag, which declares it if it is not yet
% visible.
su_type(Kind, Tag, none, _, Type, Env0, Env) :- !,
    (   Tag \== none,
        Env0 = e(_, Tags, _, _),
        get_assoc(Tag, Tags, tag(Kind, Id))
    ->  Env = Env0
    ;   new_tag(Kind, Tag, Id, Env0, Env)
    ),
    Type =.. [Kind, Id].
su_type(Kind, Tag, Members, Attrs, Type, Env0, Env) :-
    (   Tag \== none,
        Env0 = e(_, Tags, Defs, _),
        get_assoc(Tag, Tags, tag(Kind, Id)),
        get_assoc(Id, Defs, incomplete(_))
    ->  Env1 = Env0       % completes a forward declaration in this scope
    ;   new_tag(Kind, Tag, Id, Env0, Env1)
    ),
    Type =.. [Kind, Id],
    foldl(member_decl, Members, Fieldss, Env1, Env2),
    append(Fieldss, Fields),
    (   memberchk(bad(Why), Fields) -> Def = bad(Why)
    ;   member(Attr, Attrs), layout_attr(attr(Attr))
    ->  Def = bad('alignment attributes')
    ;   su_layout(Kind, Fields, Env2, Def)
    ),
    Env2 = e(Ords, Tags2, Defs0, Next),
    put_assoc(Id, Defs0, Def, Defs1),
    Env = e(Ords, Tags2, Defs1, Next).

new_tag(Kind, Tag, Id, e(Ords, Tags0, Defs0, Id), e(Ords, Tags, Defs, Next)) :-
    Next is Id + 1,
    (   Tag == none -> Tags = Tags0
    ;   put_assoc(Tag, Tags0, tag(Kind, Id), Tags)
    ),
    put_assoc(Id, Defs0, incomplete(Tag), Defs).

% A member declaration gives fields f(Name, Type) or bad(Why).
member_decl(static_assert(_, _, _), [], Env, Env) :- !.
member_decl(field(Specs, dcl(Name, SyntaxType, _), Width), Fields,
            Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    (   Width \== none
    ->  Fields = [bad('bitfields')],
        Env = Env1
    ;   apply_dcl(SyntaxType, Base, Type, Env1, Env),
        (   bad_type(Type, Why) -> Fields = [bad(Why)]
        ;   Fields = [f(Name, Type)]
        )
    ).

% su_layout(+Kind, +Fields, +Env, -Def), with the SysV rules: each member
% at the next multiple of its alignment; size rounded up to the
% alignment. A trailing flexible array member has size 0.
su_layout(Kind, Fields, Env, Def) :-
    (   catch(foldl(place_member(Kind, Env), Fields, Members, 0-1, End-Align),
              bad(Why),
              (Def = bad(Why), true))
    ->  (   nonvar(Def) -> true
        ;   Size is (End + Align - 1) // Align * Align,
            Def = def(Kind, Members, Size, Align)
        )
    ;   Def = bad('incomplete member')
    ).

% place_member(+Kind, +Env, +Field, -Member, +End0-Align0, -End-Align)
place_member(Kind, Env, f(Name, Type), m(Name, Type, Off), End0-Align0,
             End-Align) :-
    (   Type = array(ElemType, none)
    ->  size_align(ElemType, Env, _, FieldAlign),
        FieldSize = 0
    ;   size_align(Type, Env, FieldSize, FieldAlign)
    ),
    (   Kind == struct
    ->  Off is (End0 + FieldAlign - 1) // FieldAlign * FieldAlign,
        End is Off + FieldSize
    ;   Off = 0,
        End is max(End0, FieldSize)
    ),
    Align is max(Align0, FieldAlign).

%% Enums

enum_type(Tag, none, Type, Env, Env) :- !,
    (   Tag \== none,
        Env = e(_, Tags, _, _),
        get_assoc(Tag, Tags, enum(Type0))
    ->  Type = Type0
    ;   Type = uint
    ).
enum_type(Tag, Enumerators, Type, Env0, Env) :-
    foldl(enumerator, Enumerators, Values, Env0-0, Env1-_),
    enum_underlying(Values, Type),
    (   Tag == none -> Env = Env1
    ;   Env1 = e(Ords, Tags0, Defs, Next),
        put_assoc(Tag, Tags0, enum(Type), Tags),
        Env = e(Ords, Tags, Defs, Next)
    ).

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
    put_ord(Name, enumconst(V, ConstType), Env0, Env).

enum_underlying(Values, Type) :-
    (   Values == [] -> Type = uint
    ;   min_list(Values, Lo),
        max_list(Values, Hi),
        (   Lo >= 0, Hi =< 4294967295 -> Type = uint
        ;   Lo >= -2147483648, Hi =< 2147483647 -> Type = int
        ;   Lo >= 0 -> Type = ulong
        ;   Type = long
        )
    ).

%% Declarators

% apply_dcl(+SyntaxType, +Base, -Type, +Env0, -Env): the parser builds
% declarator types outermost first around the atom base, so this replaces
% base with Base and resolves array sizes and parameter types.
apply_dcl(base, Base, Base, Env, Env).
apply_dcl(ptr(Syntax, _), Base, ptr(Type), Env0, Env) :-
    apply_dcl(Syntax, Base, Type, Env0, Env).
apply_dcl(array(Syntax, SizeExpr), Base, Type, Env0, Env) :-
    apply_dcl(Syntax, Base, ElemType, Env0, Env),
    (   SizeExpr == none
    ->  Type = array(ElemType, none)
    ;   catch(const_value(SizeExpr, Env, N, _), not_constant, fail), N >= 0
    ->  Type = array(ElemType, N)
    ;   Type = bad('non-constant array size')
    ).
apply_dcl(func(Syntax, Params), Base, func(Ret, ParamTypes, Variadic),
          Env0, Env) :-
    apply_dcl(Syntax, Base, Ret, Env0, Env1),
    param_types(Params, ParamTypes, Variadic, Env1, Env).

% Parameter declarations are scoped to the parameter list.
param_types(unspecified, unspecified, fixed, Env, Env).
param_types(params(Params, Variadic), Types, Variadic, Env0, Env) :-
    env_scope(Env0, Scope, _),
    foldl(param_type, Params, Types, Env0, Env1),
    env_restore(Scope, Env1, Env).

param_type(param(Specs, dcl(_, SyntaxType, _)), Type, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    apply_dcl(SyntaxType, Base, Type0, Env1, Env),
    adjust_param(Type0, Type).

adjust_param(array(T, _), ptr(T)) :- !.
adjust_param(func(R, P, V), ptr(func(R, P, V))) :- !.
adjust_param(T, T).

type_name_type(type(Specs, SyntaxType), Type, Env0, Env) :-
    specs_type(Specs, Base, Env0, Env1),
    apply_dcl(SyntaxType, Base, Type, Env1, Env).

% The first bad type inside T, if any (not through pointers, which may
% point at anything).
bad_type(bad(Why), Why) :- !.
bad_type(array(T, _), Why) :- bad_type(T, Why).
bad_type(func(Ret, Params, _), Why) :-
    (   bad_type(Ret, Why) -> true
    ;   is_list(Params),
        member(Param, Params),
        bad_type(Param, Why)
    ).

%% Sizes

% size_align(+Type, +Env, -Size, -Align). Throws bad(Why) for a bad or
% incomplete type.
size_align(Type, Env, Size, Align) :-
    (   size_align_(Type, Env, Size0, Align0) -> Size = Size0, Align = Align0
    ;   throw(bad(incomplete))
    ).

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
    size_align(T, Env, ElemSize, Align),
    Size is ElemSize * N.
size_align_(struct(Id), Env, Size, Align) :- su_size(Id, Env, Size, Align).
size_align_(union(Id), Env, Size, Align) :- su_size(Id, Env, Size, Align).
size_align_(bad(Why), _, _, _) :- throw(bad(Why)).

su_size(Id, e(_, _, Defs, _), Size, Align) :-
    get_assoc(Id, Defs, Def),
    (   Def = def(_, _, Size, Align) -> true
    ;   Def = bad(Why) -> throw(bad(Why))
    ;   fail
    ).

complete(Type, Env) :- catch(size_align(Type, Env, _, _), bad(_), fail).

% find_member(+SU, +Name, +Env, -Type, -Offset), looking into anonymous
% members.
find_member(SU, Name, Env, Type, Off) :-
    SU =.. [_, Id],
    Env = e(_, _, Defs, _),
    get_assoc(Id, Defs, def(_, Members, _, _)),
    (   member(m(Name, Type, Off), Members) -> true
    ;   member(m(none, AnonType, AnonOff), Members),
        find_member(AnonType, Name, Env, Type, InnerOff)
    ->  Off is AnonOff + InnerOff
    ).

%% Integers

int_type(T) :- int_info(T, _, _).

% int_info(?Type, ?Size, ?Signedness)
int_info(bool, 1, unsigned).
int_info(char, 1, signed).
int_info(schar, 1, signed).
int_info(uchar, 1, unsigned).
int_info(short, 2, signed).
int_info(ushort, 2, unsigned).
int_info(int, 4, signed).
int_info(uint, 4, unsigned).
int_info(long, 8, signed).
int_info(ulong, 8, unsigned).
int_info(llong, 8, signed).
int_info(ullong, 8, unsigned).

scalar(T) :- int_type(T), !.
scalar(ptr(_)).

% The integer conversion rank.
rank(bool, 0).
rank(char, 1).  rank(schar, 1).  rank(uchar, 1).
rank(short, 2). rank(ushort, 2).
rank(int, 3).   rank(uint, 3).
rank(long, 4).  rank(ulong, 4).
rank(llong, 5). rank(ullong, 5).

promote(T, P) :- rank(T, R), R < 3, !, P = int.
promote(T, T).

unsigned_of(int, uint).
unsigned_of(long, ulong).
unsigned_of(llong, ullong).

% The usual arithmetic conversions, on promoted integer types.
usual(TypeA0, TypeB0, Type) :-
    promote(TypeA0, A),
    promote(TypeB0, B),
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

% wrap(+V, +T, -W): V converted to integer type T.
wrap(V, bool, W) :- !, ( V =:= 0 -> W = 0 ; W = 1 ).
wrap(V, Type, W) :-
    int_info(Type, Size, Sign),
    M is 1 << (8 * Size),
    U is V mod M,
    (   Sign == signed, U >= M >> 1 -> W is U - M ; W = U ).

% class_of(+Type, -Class): the IR class of a scalar value.
class_of(T, w) :- int_info(T, Size, _), Size =< 4, !.
class_of(T, l) :- int_type(T), !.
class_of(ptr(_), p).

%% Integer constant expressions

% const_value(+Expr, +Env, -Value, -Type). Throws not_constant when Expr
% is not an integer constant expression.
const_value(Expr, Env, V, T) :-
    (   const_eval(Expr, Env, V0, T0) -> V = V0, T = T0
    ;   throw(not_constant)
    ).

const_eval(num(V0, Suffix), _, V, T) :-
    num_type(V0, Suffix, T),
    wrap(V0, T, V).
const_eval(chr(V), _, V, int).
const_eval(id(Name), Env, V, T) :- ord(Env, Name, enumconst(V, T)).
const_eval(un(neg, X), Env, V, T) :-
    const_eval(X, Env, V0, T0),
    promote(T0, T),
    wrap(-V0, T, V).
const_eval(un(plus, X), Env, V, T) :-
    const_eval(X, Env, V, T0),
    promote(T0, T).
const_eval(un(bnot, X), Env, V, T) :-
    const_eval(X, Env, V0, T0),
    promote(T0, T),
    wrap(\(V0), T, V).
const_eval(un(not, X), Env, V, int) :-
    const_eval(X, Env, V0, _),
    (   V0 =:= 0 -> V = 1 ; V = 0 ).
const_eval(bin(Op, A, B), Env, V, T) :-
    const_eval(A, Env, VA, TA),
    const_eval(B, Env, VB, TB),
    const_binary(Op, VA, TA, VB, TB, V, T).
const_eval(cond(C, A, B), Env, V, T) :-
    const_eval(C, Env, VC, _),
    const_eval(A, Env, VA, TA),
    const_eval(B, Env, VB, TB),
    usual(TA, TB, T),
    (   VC =\= 0 -> wrap(VA, T, V) ; wrap(VB, T, V) ).
const_eval(cast(TypeName, X), Env, V, T) :-
    type_name_type(TypeName, T, Env, _),
    int_type(T),
    const_eval(X, Env, V0, _),
    wrap(V0, T, V).
const_eval(sizeof_type(TypeName), Env, V, ulong) :-
    type_name_type(TypeName, T, Env, _),
    catch(size_align(T, Env, V, _), bad(_), fail).
const_eval(alignof(TypeName), Env, V, ulong) :-
    type_name_type(TypeName, T, Env, _),
    catch(size_align(T, Env, _, V), bad(_), fail).
const_eval(offsetof(TypeName, Path), Env, V, ulong) :-
    type_name_type(TypeName, T, Env, _),
    offset_path(Path, T, Env, 0, V).
const_eval(comma(_, B), Env, V, T) :- const_eval(B, Env, V, T).

% offset_path(+Path, +Type, +Env, +Off0, -Off): offsetof's member path.
offset_path([], _, _, Off, Off).
offset_path([field(F)|Path], T, Env, Off0, Off) :-
    find_member(T, F, Env, FieldType, FieldOff),
    Off1 is Off0 + FieldOff,
    offset_path(Path, FieldType, Env, Off1, Off).
offset_path([index(X)|Path], array(ElemType, _), Env, Off0, Off) :-
    const_eval(X, Env, I, _),
    size_align(ElemType, Env, ElemSize, _),
    Off1 is Off0 + I * ElemSize,
    offset_path(Path, ElemType, Env, Off1, Off).

const_binary(Op, VA, TA, VB, TB, V, T) :-
    memberchk(Op, [add, sub, mul, div, mod, and, or, xor]), !,
    usual(TA, TB, T),
    wrap(VA, T, A),
    wrap(VB, T, B),
    const_arith(Op, A, B, R),
    wrap(R, T, V).
const_binary(Op, VA, TA, VB, _, V, T) :-
    memberchk(Op, [shl, shr]), !,
    promote(TA, T),
    wrap(VA, T, A),
    (   Op == shl -> R is A << VB ; R is A >> VB ),
    wrap(R, T, V).
const_binary(Op, VA, TA, VB, TB, V, int) :-
    memberchk(Op, [eq, ne, lt, gt, le, ge]), !,
    usual(TA, TB, T),
    wrap(VA, T, A),
    wrap(VB, T, B),
    (   const_compare(Op, A, B) -> V = 1 ; V = 0 ).
const_binary(land, VA, _, VB, _, V, int) :-
    (   VA =\= 0, VB =\= 0 -> V = 1 ; V = 0 ).
const_binary(lor, VA, _, VB, _, V, int) :-
    (   ( VA =\= 0 ; VB =\= 0 ) -> V = 1 ; V = 0 ).

% Division by zero fails, so the expression is not constant.
const_arith(add, A, B, R) :- R is A + B.
const_arith(sub, A, B, R) :- R is A - B.
const_arith(mul, A, B, R) :- R is A * B.
const_arith(div, A, B, R) :- B =\= 0, R is A // B.
const_arith(mod, A, B, R) :- B =\= 0, R is A rem B.
const_arith(and, A, B, R) :- R is A /\ B.
const_arith(or, A, B, R) :- R is A \/ B.
const_arith(xor, A, B, R) :- R is xor(A, B).

const_compare(eq, A, B) :- A =:= B.
const_compare(ne, A, B) :- A =\= B.
const_compare(lt, A, B) :- A < B.
const_compare(gt, A, B) :- A > B.
const_compare(le, A, B) :- A =< B.
const_compare(ge, A, B) :- A >= B.

% The type of an integer constant: the first type in the C11 list for
% its suffix and radix that can represent it.
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

fits(V, Type) :-
    int_info(Type, Size, Sign),
    Bits is 8 * Size,
    (   Sign == signed -> V < 1 << (Bits - 1) ; V < 1 << Bits ).

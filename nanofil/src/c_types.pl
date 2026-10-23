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
            Members: [m(Name, Type, Offset)], Name none for an
            anonymous struct or union member
      Next  the next struct id
    Block scopes save Ords and Tags and restore them on exit; Defs and
    Next only grow.
*/
:- module(c_types, [empty_env/1, specs_type/4, apply_dcl/5, size_align/4, complete/2,
                    int_type/1, int_info/3, promote/2, usual/3, wrap/3, const_value/4, num_type/3,
                    scalar/1, class_of/2, find_member/5, type_name_type/4, ord/3,
                    put_ord/4, env_scope/3, env_restore/3, sema_error/3,
                    enum_underlying/2, decl_types/5]).

:- use_module(library(lists)).
:- use_module(library(assoc)).

empty_env(e(O, T, D, 0)) :- empty_assoc(O), empty_assoc(T), empty_assoc(D).

ord(e(O, _, _, _), N, V) :- get_assoc(N, O, V).
put_ord(N, V, e(O0, T, D, X), e(O, T, D, X)) :- put_assoc(N, O0, V, O).

env_scope(e(O, T, _, _), s(O, T), _).
env_restore(s(O, T), e(_, _, D, X), e(O, T, D, X)).

sema_error(Loc, Fmt, Args) :-
    format(atom(M0), Fmt, Args),
    format(atom(M), '~w: ~w', [Loc, M0]),
    throw(nanofil_error(M)).

%% Declarations

% decl_types(+Specs, +Inits, -Declared, +E0, -E): resolve a declaration.
% Typedefs are entered into E; every other declarator is returned as
% d(Name, Type, Storage, Asm, Init), Storage one of none, static,
% extern, typedef excluded.
decl_types(Ss, Is, Ds, E0, E) :-
    specs_type(Ss, B, E0, E1),
    (   memberchk(storage(St0), Ss) -> St = St0 ; St = none ),
    foldl(declarator_type(B, St), Is, Ds0, E1, E),
    exclude(==(none), Ds0, Ds).

declarator_type(B, St, init(dcl(N, ST, Asm), I), D, E0, E) :-
    apply_dcl(ST, B, T, E0, E1),
    (   St == typedef -> put_ord(N, typedef(T), E1, E), D = none
    ;   E = E1, D = d(N, T, St, Asm, I)
    ).

%% Specifiers

% specs_type(+Specs, -Type, +E0, -E): the type the specifiers name.
% Struct, union and enum definitions in Specs are entered into E.
specs_type(Ss, T, E0, E) :-
    specs_type_(Ss, T0, E0, E),
    (   member(S, Ss), layout_attr(S) -> T = bad('alignment attributes')
    ;   T = T0
    ).

layout_attr(alignas(_)).
layout_attr(attr(A)) :- is_list(A), attr_word(A, N),
    memberchk(N, [aligned, '__aligned__', packed, '__packed__']), !.

attr_word(Ts, N) :- member(T, Ts), ( T = id(N) ; T = group(G), attr_word(G, N) ).

specs_type_(Ss, T, E0, E) :-
    findall(K, member(tspec(K), Ss), Ks),
    findall(S, ( member(S, Ss), other_type_spec(S) ), Os),
    (   Os = [O], Ks == [] -> named_type(O, T, E0, E)
    ;   Os == [] -> keyword_type(Ks, T), E = E0
    ;   T = bad('conflicting type specifiers'), E = E0
    ).

other_type_spec(tname(_)).
other_type_spec(su(_, _, _, _)).
other_type_spec(enum(_, _)).
other_type_spec(typeof(_)).

named_type(tname(N), T, E, E) :-
    (   ord(E, N, typedef(T0)) -> T = T0
    ;   N == '__builtin_va_list' -> T = bad('va_list')
    ;   T = bad('unknown typedef')
    ).
named_type(typeof(_), bad('typeof'), E, E).
named_type(su(K, Tag, Ms, As), T, E0, E) :- su_type(K, Tag, Ms, As, T, E0, E).
named_type(enum(Tag, Es), T, E0, E) :- enum_type(Tag, Es, T, E0, E).

keyword_type([], int) :- !.   % implicit int, as in old headers' K&R style
keyword_type(Ks, T) :-
    msort(Ks, S),
    (   kw_combo(S, T0) -> T = T0 ; T = bad('invalid type specifiers') ).

kw_combo([void], void).
kw_combo([bool], bool).
kw_combo([char], char).
kw_combo([char, signed], schar).
kw_combo([char, unsigned], uchar).
kw_combo(S, short) :- member(S, [[short], [short, signed], [int, short], [int, short, signed]]).
kw_combo(S, ushort) :- member(S, [[short, unsigned], [int, short, unsigned]]).
kw_combo(S, int) :- member(S, [[int], [signed], [int, signed]]).
kw_combo(S, uint) :- member(S, [[unsigned], [int, unsigned]]).
kw_combo(S, long) :- member(S, [[long], [long, signed], [int, long], [int, long, signed]]).
kw_combo(S, ulong) :- member(S, [[long, unsigned], [int, long, unsigned]]).
kw_combo(S, llong) :- member(S, [[long, long], [long, long, signed], [int, long, long],
                                 [int, long, long, signed]]).
kw_combo(S, ullong) :- member(S, [[long, long, unsigned], [int, long, long, unsigned]]).
kw_combo([float], float).
kw_combo([double], double).
kw_combo([double, long], ldouble).
kw_combo(S, bad('_Complex')) :- memberchk(complex, S).
kw_combo(S, bad('__int128')) :- memberchk(int128, S).

%% Structs and unions

su_type(K, Tag, none, _, T, E0, E) :- !,
    (   Tag \== none, E0 = e(_, Tags, _, _), get_assoc(Tag, Tags, tag(K, Id))
    ->  E = E0
    ;   new_tag(K, Tag, Id, E0, E)
    ),
    T =.. [K, Id].
su_type(K, Tag, Ms, As, T, E0, E) :-
    (   Tag \== none, E0 = e(_, Tags, Defs, _), get_assoc(Tag, Tags, tag(K, Id)),
        get_assoc(Id, Defs, incomplete(_))
    ->  E1 = E0       % completes a forward declaration in this scope
    ;   new_tag(K, Tag, Id, E0, E1)
    ),
    T =.. [K, Id],
    foldl(member_decl, Ms, Fs0, E1, E2),
    append(Fs0, Fs),
    (   memberchk(bad(Why), Fs) -> Def = bad(Why)
    ;   member(A, As), layout_attr(attr(A)) -> Def = bad('alignment attributes')
    ;   layout(K, Fs, E2, Def)
    ),
    E2 = e(O, Tg, D0, X),
    put_assoc(Id, D0, Def, D),
    E = e(O, Tg, D, X).

new_tag(K, Tag, Id, e(O, Tags0, D0, Id), e(O, Tags, D, Next)) :-
    Next is Id + 1,
    (   Tag == none -> Tags = Tags0 ; put_assoc(Tag, Tags0, tag(K, Id), Tags) ),
    put_assoc(Id, D0, incomplete(Tag), D),
    _ = K.

% A member declaration gives fields f(Name, Type, Align) or bad(Why).
member_decl(static_assert(_, _, _), [], E, E) :- !.
member_decl(field(Ss, dcl(N, ST, _), W), Fs, E0, E) :-
    specs_type(Ss, Base, E0, E1),
    (   W \== none -> Fs = [bad('bitfields')], E = E1
    ;   apply_dcl(ST, Base, T, E1, E),
        (   bad_type(T, Why) -> Fs = [bad(Why)]
        ;   Fs = [f(N, T)]
        )
    ).

% layout(+Kind, +Fields, +E, -Def), with the SysV rules: each member at
% the next multiple of its alignment; size rounded up to the alignment.
% A trailing flexible array member has size 0.
layout(K, Fs, E, Def) :-
    (   catch(foldl(place(K, E), Fs, Ms, 0-1, End-Align), bad(Why), (Def = bad(Why), true))
    ->  (   nonvar(Def) -> true
        ;   Size is (End + Align - 1) // Align * Align,
            Def = def(K, Ms, Size, Align)
        )
    ;   Def = bad('incomplete member')
    ).

place(K, E, f(N, T), m(N, T, Off), End0-A0, End-A) :-
    (   T = array(ET, none) -> size_align(ET, E, _, FA), FS = 0
    ;   size_align(T, E, FS, FA)
    ),
    (   K == struct -> Off is (End0 + FA - 1) // FA * FA, End is Off + FS
    ;   Off = 0, End is max(End0, FS)
    ),
    A is max(A0, FA).

%% Enums

enum_type(Tag, none, T, E, E) :- !,
    (   Tag \== none, E = e(_, Tags, _, _), get_assoc(Tag, Tags, enum(T0)) -> T = T0
    ;   T = uint
    ).
enum_type(Tag, Es, T, E0, E) :-
    foldl(enumerator, Es, Vs, E0-0, E1-_),
    enum_underlying(Vs, T),
    (   Tag == none -> E = E1
    ;   E1 = e(O, Tags0, D, X), put_assoc(Tag, Tags0, enum(T), Tags), E = e(O, Tags, D, X)
    ).

% Each constant has type int when it fits, as C requires of constants
% whose values fit; the enum's own type follows clang.
enumerator(enumerator(N, V0), V, E0-Next, E-Next1) :-
    (   V0 == none -> V = Next
    ;   const_value(V0, E0, V, _)
    ),
    Next1 is V + 1,
    (   V >= -2147483648, V =< 2147483647 -> CT = int ; CT = long ),
    put_ord(N, enumconst(V, CT), E0, E).

enum_underlying(Vs, T) :-
    (   Vs == [] -> T = uint
    ;   min_list(Vs, Lo), max_list(Vs, Hi),
        (   Lo >= 0, Hi =< 4294967295 -> T = uint
        ;   Lo >= -2147483648, Hi =< 2147483647 -> T = int
        ;   Lo >= 0 -> T = ulong
        ;   T = long
        )
    ).

%% Declarators

% apply_dcl(+SyntaxType, +Base, -Type, +E0, -E): the parser builds
% declarator types outermost first around the atom base, so this replaces
% base with Base and resolves array sizes and parameter types.
apply_dcl(base, B, B, E, E).
apply_dcl(ptr(T0, _), B, ptr(T), E0, E) :- apply_dcl(T0, B, T, E0, E).
apply_dcl(array(T0, S), B, T, E0, E) :-
    apply_dcl(T0, B, ET, E0, E1),
    (   S == none -> T = array(ET, none), E = E1
    ;   catch(const_value(S, E1, N, _), not_constant, fail), N >= 0 -> T = array(ET, N), E = E1
    ;   T = bad('non-constant array size'), E = E1
    ).
apply_dcl(func(T0, Ps), B, func(R, PTs, V), E0, E) :-
    apply_dcl(T0, B, R, E0, E1),
    params_types(Ps, PTs, V, E1, E).

params_types(unspecified, unspecified, fixed, E, E).
params_types(params(Ps, V), Ts, V, E0, E) :-
    env_scope(E0, S, _),
    foldl(param_type, Ps, Ts, E0, E1),
    env_restore(S, E1, E).

param_type(param(Ss, dcl(_, ST, _)), T, E0, E) :-
    specs_type(Ss, B, E0, E1), apply_dcl(ST, B, T0, E1, E), adjust(T0, T).

adjust(array(T, _), ptr(T)) :- !.
adjust(func(R, P, V), ptr(func(R, P, V))) :- !.
adjust(T, T).

type_name_type(type(Ss, ST), T, E0, E) :- specs_type(Ss, B, E0, E1), apply_dcl(ST, B, T, E1, E).

% The first bad type inside T, if any (not through pointers, which may
% point at anything).
bad_type(bad(W), W) :- !.
bad_type(array(T, _), W) :- bad_type(T, W).
bad_type(func(R, Ps, _), W) :- ( bad_type(R, W) -> true ; is_list(Ps), member(P, Ps), bad_type(P, W) ).

%% Sizes

size_align(T, E, S, A) :-
    (   size_align_(T, E, S0, A0) -> S = S0, A = A0
    ;   throw(bad(incomplete))
    ).

size_align_(bool, _, 1, 1).
size_align_(char, _, 1, 1). size_align_(schar, _, 1, 1). size_align_(uchar, _, 1, 1).
size_align_(short, _, 2, 2). size_align_(ushort, _, 2, 2).
size_align_(int, _, 4, 4). size_align_(uint, _, 4, 4).
size_align_(long, _, 8, 8). size_align_(ulong, _, 8, 8).
size_align_(llong, _, 8, 8). size_align_(ullong, _, 8, 8).
size_align_(float, _, 4, 4). size_align_(double, _, 8, 8). size_align_(ldouble, _, 16, 16).
size_align_(ptr(_), _, 8, 8).
size_align_(array(T, N), E, S, A) :- integer(N), size_align(T, E, S0, A), S is S0 * N.
size_align_(struct(Id), E, S, A) :- su_size(Id, E, S, A).
size_align_(union(Id), E, S, A) :- su_size(Id, E, S, A).
size_align_(bad(W), _, _, _) :- throw(bad(W)).

su_size(Id, e(_, _, D, _), S, A) :-
    get_assoc(Id, D, Def),
    (   Def = def(_, _, S, A) -> true
    ;   Def = bad(W) -> throw(bad(W))
    ;   fail
    ).

complete(T, E) :- catch(size_align(T, E, _, _), bad(_), fail).

% find_member(+SU, +Name, +E, -Type, -Offset), looking into anonymous
% members.
find_member(SU, N, E, T, Off) :-
    SU =.. [_, Id], E = e(_, _, D, _),
    get_assoc(Id, D, def(_, Ms, _, _)),
    (   member(m(N, T, Off), Ms) -> true
    ;   member(m(none, AT, AOff), Ms), find_member(AT, N, E, T, O1) -> Off is AOff + O1
    ).

%% Integers

int_type(T) :- int_info(T, _, _).

int_info(bool, 1, unsigned).
int_info(char, 1, signed). int_info(schar, 1, signed). int_info(uchar, 1, unsigned).
int_info(short, 2, signed). int_info(ushort, 2, unsigned).
int_info(int, 4, signed). int_info(uint, 4, unsigned).
int_info(long, 8, signed). int_info(ulong, 8, unsigned).
int_info(llong, 8, signed). int_info(ullong, 8, unsigned).

scalar(T) :- int_type(T), !.
scalar(ptr(_)).

rank(bool, 0). rank(char, 1). rank(schar, 1). rank(uchar, 1).
rank(short, 2). rank(ushort, 2). rank(int, 3). rank(uint, 3).
rank(long, 4). rank(ulong, 4). rank(llong, 5). rank(ullong, 5).

promote(T, P) :- rank(T, R), R < 3, !, P = int.
promote(T, T).

unsigned_of(int, uint). unsigned_of(long, ulong). unsigned_of(llong, ullong).

% The usual arithmetic conversions, on promoted integer types.
usual(A0, B0, T) :-
    promote(A0, A), promote(B0, B),
    int_info(A, SA, GA), int_info(B, SB, GB), rank(A, RA), rank(B, RB),
    (   A == B -> T = A
    ;   GA == GB -> ( RA >= RB -> T = A ; T = B )
    ;   GA == unsigned, RA >= RB -> T = A
    ;   GB == unsigned, RB >= RA -> T = B
    ;   GA == signed, SA > SB -> T = A
    ;   GB == signed, SB > SA -> T = B
    ;   GA == signed -> unsigned_of(A, T)
    ;   unsigned_of(B, T)
    ).

% wrap(+V, +T, -W): V converted to integer type T.
wrap(V, bool, W) :- !, ( V =:= 0 -> W = 0 ; W = 1 ).
wrap(V, T, W) :-
    int_info(T, S, G),
    M is 1 << (8 * S),
    U is V mod M,
    (   G == signed, U >= M >> 1 -> W is U - M ; W = U ).

% class_of(+Type, -Class): the IR class of a scalar value.
class_of(T, w) :- int_info(T, S, _), S =< 4, !.
class_of(T, l) :- int_type(T), !.
class_of(ptr(_), p).

%% Integer constant expressions

% const_value(+Expr, +E, -Value, -Type)
const_value(X, E, V, T) :-
    (   cv(X, E, V0, T0) -> V = V0, T = T0
    ;   throw(not_constant)
    ).

cv(num(V0, S), _, V, T) :- num_type(V0, S, T), wrap(V0, T, V).
cv(chr(V), _, V, int).
cv(id(N), E, V, T) :- ord(E, N, enumconst(V, T)).
cv(un(neg, X), E, V, T) :- cv(X, E, V0, T0), promote(T0, T), wrap(-V0, T, V).
cv(un(plus, X), E, V, T) :- cv(X, E, V, T0), promote(T0, T).
cv(un(bnot, X), E, V, T) :- cv(X, E, V0, T0), promote(T0, T), wrap(\(V0), T, V).
cv(un(not, X), E, V, int) :- cv(X, E, V0, _), ( V0 =:= 0 -> V = 1 ; V = 0 ).
cv(bin(Op, A, B), E, V, T) :- cv(A, E, VA, TA), cv(B, E, VB, TB), cbin(Op, VA, TA, VB, TB, V, T).
cv(cond(C, A, B), E, V, T) :-
    cv(C, E, VC, _), cv(A, E, VA, TA), cv(B, E, VB, TB), usual(TA, TB, T),
    ( VC =\= 0 -> wrap(VA, T, V) ; wrap(VB, T, V) ).
cv(cast(TN, X), E, V, T) :- type_name_type(TN, T, E, _), int_type(T), cv(X, E, V0, _), wrap(V0, T, V).
cv(sizeof_type(TN), E, V, ulong) :- type_name_type(TN, T, E, _), catch(size_align(T, E, V, _), bad(_), fail).
cv(alignof(TN), E, V, ulong) :- type_name_type(TN, T, E, _), catch(size_align(T, E, _, V), bad(_), fail).
cv(offsetof(TN, Path), E, V, ulong) :- type_name_type(TN, T, E, _), offset_path(Path, T, E, 0, V).
cv(comma(_, B), E, V, T) :- cv(B, E, V, T).

offset_path([], _, _, V, V).
offset_path([field(F)|Ps], T, E, V0, V) :- find_member(T, F, E, FT, O), V1 is V0 + O, offset_path(Ps, FT, E, V1, V).
offset_path([index(X)|Ps], array(ET, _), E, V0, V) :-
    cv(X, E, I, _), size_align(ET, E, S, _), V1 is V0 + I * S, offset_path(Ps, ET, E, V1, V).

cbin(Op, VA, TA, VB, TB, V, T) :-
    memberchk(Op, [add, sub, mul, div, mod, and, or, xor]), !,
    usual(TA, TB, T),
    wrap(VA, T, A), wrap(VB, T, B),
    arith(Op, A, B, R), wrap(R, T, V).
cbin(Op, VA, TA, VB, _, V, T) :-
    memberchk(Op, [shl, shr]), !,
    promote(TA, T), wrap(VA, T, A),
    ( Op == shl -> R is A << VB ; R is A >> VB ),
    wrap(R, T, V).
cbin(Op, VA, TA, VB, TB, V, int) :-
    memberchk(Op, [eq, ne, lt, gt, le, ge]), !,
    usual(TA, TB, T), wrap(VA, T, A), wrap(VB, T, B),
    ( rel(Op, A, B) -> V = 1 ; V = 0 ).
cbin(land, VA, _, VB, _, V, int) :- ( VA =\= 0, VB =\= 0 -> V = 1 ; V = 0 ).
cbin(lor, VA, _, VB, _, V, int) :- ( ( VA =\= 0 ; VB =\= 0 ) -> V = 1 ; V = 0 ).

arith(add, A, B, R) :- R is A + B.
arith(sub, A, B, R) :- R is A - B.
arith(mul, A, B, R) :- R is A * B.
arith(div, A, B, R) :- B =\= 0, R is A // B.
arith(mod, A, B, R) :- B =\= 0, R is A rem B.
arith(and, A, B, R) :- R is A /\ B.
arith(or, A, B, R) :- R is A \/ B.
arith(xor, A, B, R) :- R is xor(A, B).

rel(eq, A, B) :- A =:= B.
rel(ne, A, B) :- A =\= B.
rel(lt, A, B) :- A < B.
rel(gt, A, B) :- A > B.
rel(le, A, B) :- A =< B.
rel(ge, A, B) :- A >= B.

% The type of an integer constant: the first type in the C11 list for
% its suffix and radix that can represent it.
num_type(V, S-R, T) :-
    (   const_list(R, S, Ts), member(T, Ts), fits(V, T) -> true
    ;   T = ullong
    ).

const_list(dec, none, [int, long, llong]).
const_list(dec, u, [uint, ulong, ullong]).
const_list(dec, l, [long, llong]).
const_list(dec, ul, [ulong, ullong]).
const_list(dec, ll, [llong]).
const_list(dec, ull, [ullong]).
const_list(other, none, [int, uint, long, ulong, llong, ullong]).
const_list(other, u, [uint, ulong, ullong]).
const_list(other, l, [long, ulong, llong, ullong]).
const_list(other, ul, [ulong, ullong]).
const_list(other, ll, [llong, ullong]).
const_list(other, ull, [ullong]).

fits(V, T) :- int_info(T, S, G), B is 8 * S,
    (   G == signed -> V < 1 << (B - 1) ; V < 1 << B ).

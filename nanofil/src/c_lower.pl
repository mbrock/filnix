/*  C to IR lowering (milestone 4b), in the style of cproc.

    Every local variable and parameter lives in an alloc'd object, the
    allocs hoisted into the entry block; M5's promote will turn them into
    temporaries. Pointers are class p, so the output is a Fil-C module.

    Values during lowering:
      v(Value, Type)   an rvalue: Value is an IR value, Type a C type
      lv(Addr, Type)   an lvalue: Addr is a p value
      fd(Symbol, Type) a function designator
    A narrow integer (char, short, bool) is always held sign- or
    zero-extended to 32 bits in a w, so conversions only extend when the
    source type has values the target cannot represent.

    The lowering threads a state through DCG notation (no terminals):
      st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)
      Cur     cur(Label, Phis), or none after a jump (dead code then
              opens an unreachable block)
      Insts, Blocks, Allocs  reversed
      Labels  assoc from C goto labels to IR labels
      Cases   the enclosing switch's case(Value, Label) and default(Label)
    The context argument X = x(Function, ReturnType, Break, Continue, Loc).
*/
:- module(c_lower, [c_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(dcgs)).
:- use_module(c_types).

% c_module(+Items, -Module): Items from c_parse.
c_module(Items, module(Fs)) :-
    empty_env(E0),
    foldl(top, Items, Fss, E0, _),
    append(Fss, Fs).

%% Top level

top(static_assert(L, X, _), [], E, E) :- !, static_assert(L, X, E).
top(decl(L, Ss, Is), [], E0, E) :- !,
    catch(decl_types(Ss, Is, Ds, E0, E1), not_constant, sema_error(L, 'array size is not a constant', [])),
    foldl(global_decl(L), Ds, E1, E).
top(fundef(L, Ss, dcl(Name, ST, Asm), Body), [F], E0, E) :-
    decl_types(Ss, [init(dcl(Name, ST, Asm), none)], [d(_, T, St, _, _)], E0, E1),
    global_decl(L, d(Name, T, St, Asm, none), E1, E),
    function(L, Name, T, ST, Body, E, F).

static_assert(L, X, E) :-
    (   catch(const_value(X, E, V, _), not_constant, fail) -> true
    ;   sema_error(L, 'static assertion is not a constant', [])
    ),
    (   V =\= 0 -> true ; sema_error(L, 'static assertion failed', []) ).

global_decl(L, d(N, T, St, Asm, I), E0, E) :-
    ( Asm = asm(Sym) -> true ; Sym = N ),
    (   T = func(_, _, _)
    ->  ( St == static -> Lk = local ; Lk = export ),
        (   I \== none -> sema_error(L, 'function ~w has an initializer', [N]) ; true ),
        put_ord(N, fn(T, Sym, Lk), E0, E)
    ;   put_ord(N, gvar(T, Sym, St, I), E0, E)
    ).

%% Functions

function(L, Name, func(RT, PTs, Var), ST, Body, E0, func(Sym, Lk, RK, Params, Blocks)) :-
    ord(E0, Name, fn(_, Sym, Lk)),
    (   Var == variadic -> sema_error(L, 'defining variadic function ~w is not supported', [Name]) ; true ),
    (   PTs == unspecified -> PTs1 = [] ; PTs1 = PTs ),
    ret_class(L, RT, RK),
    param_names(ST, Names),
    S0 = st(E0, cur(start, []), [], [], 0, Lt, [], []),
    empty_assoc(Lt),
    X = x(Name, RT, none, none, L),
    phrase(( params(Names, PTs1, X, Params),
             stmt(Body, X),
             fall_off(RT) ), S0, S),
    S = st(_, none, [], Bs, _, _, _, As),
    reverse(Bs, [blk(start, [], Is0, J0)|Rest]),
    reverse(As, AIs),
    append(AIs, Is0, Is),
    Blocks = [blk(start, [], Is, J0)|Rest].

ret_class(_, void, void) :- !.
ret_class(_, T, K) :- class_of(T, K), !.
ret_class(L, T, _) :- float_type(T), !, sema_error(L, 'floating point is not supported', []).
ret_class(L, T, _) :- sema_error(L, 'returning ~w is not supported yet', [T]).

float_type(T) :- memberchk(T, [float, double, ldouble]).

% The parameter names, from the function's own declarator.
param_names(func(base, unspecified), []) :- !.
param_names(func(base, params(Ps, _)), Ns) :- !,
    findall(N, member(param(_, dcl(N, _, _)), Ps), Ns).
param_names(func(T, _), Ns) :- !, param_names(T, Ns).
param_names(ptr(T, _), Ns) :- param_names(T, Ns).

params([], [], _, []) --> [].
params([N|Ns], [T|Ts], X, [par(K, P)|Ps]) -->
    { arg(5, X, L),
      (   class_of(T, K) -> true
      ;   float_type(T) -> sema_error(L, 'floating point is not supported', [])
      ;   sema_error(L, 'parameter of type ~w is not supported yet', [T])
      ) },
    fresh(P),
    (   { N == none } -> []
    ;   local_slot(T, A),
        store_typed(T, P, A),
        bind(N, var(A, T))
    ),
    params(Ns, Ts, X, Ps).

fall_off(RT) --> cur(C),
    (   { C == none } -> []
    ;   { RT == void } -> term(ret)
    ;   term(ret(c(0)))
    ).

%% State primitives

cur(C, S, S) :- S = st(_, C, _, _, _, _, _, _).

env(E, S, S) :- S = st(E, _, _, _, _, _, _, _).
set_env(E, st(_, C, I, B, N, L, Cs, A), st(E, C, I, B, N, L, Cs, A)).

bind(Name, V) --> env(E0), { put_ord(Name, V, E0, E) }, set_env(E).

fresh(t(T), st(E, C, I, B, N, L, Cs, A), st(E, C, I, B, N1, L, Cs, A)) :-
    N1 is N + 1, format(atom(T), 'v~w', [N]).
label(Lb, st(E, C, I, B, N, L, Cs, A), st(E, C, I, B, N1, L, Cs, A)) :-
    N1 is N + 1, format(atom(Lb), 'L~w', [N]).

live --> cur(C), ( { C == none } -> label(L), set_cur(cur(L, [])) ; [] ).
set_cur(C, st(E, _, I, B, N, L, Cs, A), st(E, C, I, B, N, L, Cs, A)).

emit(I) --> live, emit_(I).
emit_(I, st(E, C, Is, B, N, L, Cs, A), st(E, C, [I|Is], B, N, L, Cs, A)).

term(J) --> live, term_(J).
term_(J, st(E, cur(Lb, Ps), Is, Bs, N, L, Cs, A), st(E, none, [], [blk(Lb, Ps, RIs, J)|Bs], N, L, Cs, A)) :-
    reverse(Is, RIs).

% start(L): begin block L, falling through from a live current block.
start(L) --> cur(C), ( { C == none } -> [] ; term(jmp(L)) ), set_cur(cur(L, [])).
start_phi(L, Phis) --> set_cur(cur(L, Phis)).

here(L) --> live, cur(cur(L, _)).

add_alloc(I, st(E, C, Is, B, N, L, Cs, As), st(E, C, Is, B, N, L, Cs, [I|As])).

cases(Cs, S, S) :- S = st(_, _, _, _, _, _, Cs, _).
set_cases(Cs, st(E, C, I, B, N, L, _, A), st(E, C, I, B, N, L, Cs, A)).

goto_label(Name, Lb, st(E, C, I, B, N, L0, Cs, A), S) :-
    (   get_assoc(Name, L0, Lb) -> S = st(E, C, I, B, N, L0, Cs, A)
    ;   N1 is N + 1, format(atom(Lb), 'L~w', [N]), put_assoc(Name, L0, Lb, L),
        S = st(E, C, I, B, N1, L, Cs, A)
    ).

ins(K, Op, Args, D) --> fresh(D), emit(ins(D, K, Op, Args)).

% A local object: an alloc in the entry block.
local_slot(T, A) --> env(E),
    { catch(size_align(T, E, Size, Al), bad(W), throw(nanofil_error(W))),
      ( Al =< 4 -> AA = 4 ; AA = Al ), Sz is max(Size, 1) },
    fresh(A), add_alloc(ins(A, p, alloc(AA), [c(Sz)])).

%% Statements

stmt(at(L, S), X0) --> { setarg_loc(X0, L, X) }, stmt_(S, X).

setarg_loc(x(F, R, B, C, _), L, x(F, R, B, C, L)).

stmt_(block(Items), X) --> env(E), { env_scope(E, Sc, _) }, items(Items, X), env(E1), { env_restore(Sc, E1, E2) }, set_env(E2).
stmt_(null, _) --> [].
stmt_(expr(E), X) --> rval(E, X, _).
stmt_(if(C, T, E), X) -->
    label(LT), label(LE), label(LJ),
    cond_jump(C, X, LT, LE),
    start(LT), stmt(T, X), term(jmp(LJ)),
    start(LE), ( { E == none } -> [] ; stmt(E, X) ),
    start(LJ).
stmt_(while(C, S), X) -->
    label(LC), label(LB), label(LE),
    start(LC), cond_jump(C, X, LB, LE),
    start(LB), { loop_ctx(X, LE, LC, X1) }, stmt(S, X1), term(jmp(LC)),
    start(LE).
stmt_(do(S, C), X) -->
    label(LB), label(LC), label(LE),
    start(LB), { loop_ctx(X, LE, LC, X1) }, stmt(S, X1),
    start(LC), cond_jump(C, X, LB, LE),
    start(LE).
stmt_(for(I, C, St, S), X) -->
    env(E), { env_scope(E, Sc, _) },
    (   { I == none } -> []
    ;   { I = expr(IE) } -> rval(IE, X, _)
    ;   item(I, X)
    ),
    label(LC), label(LB), label(LS), label(LE),
    start(LC),
    ( { C == none } -> term(jmp(LB)) ; cond_jump(C, X, LB, LE) ),
    start(LB), { loop_ctx(X, LE, LS, X1) }, stmt(S, X1),
    start(LS), ( { St == none } -> [] ; rval(St, X, _) ), term(jmp(LC)),
    start(LE),
    env(E1), { env_restore(Sc, E1, E2) }, set_env(E2).
stmt_(switch(C, S), X) -->
    rval(C, X, V0), { V0 = v(_, T0), arg(5, X, L) },
    { int_type(T0) -> promote(T0, T) ; sema_error(L, 'switch on a non-integer', []) },
    convert(V0, T, v(V, _)),
    label(LD), label(LE),
    term(jmp(LD)),
    cases(Outer), set_cases([]),
    { X = x(F, R, _, Co, Lc), X1 = x(F, R, LE, Co, Lc) },
    stmt(S, X1),
    term(jmp(LE)),
    cases(Cs0), set_cases(Outer),
    { reverse(Cs0, Cs) },
    start(LD), dispatch(Cs, V, T, LE),
    start(LE).
stmt_(case(CE, S), X) -->
    env(E), { arg(5, X, L),
              ( catch(const_value(CE, E, CV, _), not_constant, fail) -> true
              ; sema_error(L, 'case label is not a constant', []) ) },
    label(Lb), start(Lb),
    cases(Cs), set_cases([case(CV, Lb)|Cs]),
    stmt(S, X).
stmt_(default(S), X) --> label(Lb), start(Lb), cases(Cs), set_cases([default(Lb)|Cs]), stmt(S, X).
stmt_(break, X) --> { arg(3, X, B), arg(5, X, L), ( B == none -> sema_error(L, 'break outside a loop or switch', []) ; true ) }, term(jmp(B)).
stmt_(continue, X) --> { arg(4, X, C), arg(5, X, L), ( C == none -> sema_error(L, 'continue outside a loop', []) ; true ) }, term(jmp(C)).
stmt_(return(none), X) --> { arg(2, X, RT) },
    ( { RT == void } -> term(ret) ; term(ret(c(0))) ).
stmt_(return(E), X) --> { E \== none, arg(2, X, RT), arg(5, X, L) },
    rval(E, X, V0),
    (   { RT == void } -> term(ret)
    ;   assign_convert(V0, RT, L, v(V, _)), term(ret(V))
    ).
stmt_(goto(N), _) --> goto_label(N, Lb), term(jmp(Lb)).
stmt_(label(N, S), X) --> goto_label(N, Lb), start(Lb), stmt(S, X).
stmt_(decl(L, Ss, Is), X) --> item(decl(L, Ss, Is), X).

loop_ctx(x(F, R, _, _, L), B, C, x(F, R, B, C, L)).

items([], _) --> [].
items([I|Is], X) --> item(I, X), items(Is, X).

item(at(L, S), X) --> !, stmt(at(L, S), X).
item(static_assert(L, E, _), _) --> !, env(Env), { static_assert(L, E, Env) }.
item(decl(L, Ss, Is), X) -->
    env(E0),
    { catch(decl_types(Ss, Is, Ds, E0, E1), not_constant,
            sema_error(L, 'array size is not a constant', [])) },
    set_env(E1),
    { setarg_loc(X, L, X1) },
    local_decls(Ds, X1).

local_decls([], _) --> [].
local_decls([d(N, T, St, Asm, I)|Ds], X) --> { arg(5, X, L) },
    (   { T = func(_, _, _) ; St == extern }
    ->  env(E0), { global_decl(L, d(N, T, St, Asm, I), E0, E) }, set_env(E)
    ;   { St == static } -> { sema_error(L, 'static local ~w is not supported yet', [N]) }
    ;   { complete_array(T, I, T1, L) },
        env(E), { bad_check(T1, E, L, N) },
        local_slot(T1, A),
        bind(N, var(A, T1)),
        (   { I == none } -> [] ; init(A, T1, I, X) )
    ),
    local_decls(Ds, X).

bad_check(T, E, L, N) :-
    catch(( size_align(T, E, _, _) -> true ; true ), bad(W),
          sema_error(L, '~w has a type nanofil does not support (~w)', [N, W])).

% An array of unknown size takes its size from the initializer.
complete_array(array(ET, none), I, array(ET, N), L) :- !,
    (   I = str(Bs), length(Bs, N0) -> N is N0 + 1
    ;   I = list(Es) -> list_extent(Es, 0, 0, N)
    ;   sema_error(L, 'array of unknown size', [])
    ).
complete_array(T, _, T, _).

list_extent([], _, M, M).
list_extent([entry(Ds, _)|Es], I0, M0, M) :-
    ( Ds = [index(num(V, _))|_] -> I = V ; I = I0 ),
    I1 is I + 1, M1 is max(M0, I1),
    list_extent(Es, I1, M1, M).

% The switch dispatch: one comparison per case, then the default.
dispatch([], _, _, LE) --> term(jmp(LE)).
dispatch(Cs, V, T, LE) -->
    { findall(CV-Lb, member(case(CV, Lb), Cs), Pairs),
      ( memberchk(default(LD), Cs) -> true ; LD = LE ),
      class_of(T, K) },
    dispatch_(Pairs, V, T, K, LD).

dispatch_([], _, _, _, LD) --> term(jmp(LD)).
dispatch_([CV-Lb|Ps], V, T, K, LD) -->
    { wrap(CV, T, W) },
    ins(w, cmp(eq, K), [V, c(W)], C),
    label(Next),
    term(jnz(C, Lb, Next)),
    start(Next),
    dispatch_(Ps, V, T, K, LD).

% cond_jump(E, X, LT, LF): branch on the truth of a scalar.
cond_jump(E, X, LT, LF) --> rval(E, X, V), truth(V, X, C), term(jnz(C, LT, LF)).

% truth(V, X, W): a w value that is nonzero exactly when V is.
truth(v(V, T), X, W) -->
    (   { class_of(T, w) } -> { W = V }
    ;   { class_of(T, l) } -> ins(w, cmp(ne, l), [V, c(0)], W)
    ;   { T = ptr(_) } -> ins(l, ptoi, [V], I), ins(w, cmp(ne, l), [I, c(0)], W)
    ;   { arg(5, X, L), sema_error(L, 'a ~w value is not a scalar', [T]) }
    ).

%% Initializers

init(A, T, I, X) --> { arg(5, X, L) },
    (   { I = list(Es) } -> zero_object(A, T), init_list(A, T, Es, X)
    ;   { T = array(ET, N), I = str(Bs), char_type_(ET) } -> zero_object(A, T), init_string(A, N, Bs, L)
    ;   { T = array(_, _) } -> { sema_error(L, 'array initializer must be a list', []) }
    ;   rval(I, X, V0), assign_convert(V0, T, L, v(V, _)), store_typed(T, V, A)
    ).

char_type_(T) :- memberchk(T, [char, schar, uchar]).

init_string(A, N, Bs, L) -->
    { length(Bs, NB), ( NB > N -> sema_error(L, 'string initializer is too long', []) ; true ),
      findall(I-B, nth0(I, Bs, B), Pairs) },
    store_bytes(Pairs, A).

store_bytes([], _) --> [].
store_bytes([I-B|Ps], A) --> offset(A, I, P), emit(store(b, c(B), P)), store_bytes(Ps, A).

% zero_object(A, T): clear the whole object, since allocs are hoisted
% and a local inside a loop must be reinitialized on every pass.
zero_object(A, T) --> env(E), { size_align(T, E, S, Al) }, zero_bytes(A, 0, S, Al).

zero_bytes(_, O, S, _) --> { O >= S }, !.
zero_bytes(A, O, S, Al) -->
    { R is S - O, member(W-N, [l-8, w-4, h-2, b-1]), N =< R, N =< Al, O mod N =:= 0 }, !,
    offset(A, O, P), emit(store(W, c(0), P)),
    { O1 is O + N }, zero_bytes(A, O1, S, Al).

% init_list(A, T, Entries, X): a braced list for an array or struct, with
% designators and brace elision.
init_list(A, T, Es, X) --> init_agg(A, T, Es, Rest, X), { arg(5, X, L) },
    ( { Rest == [] } -> [] ; { sema_error(L, 'excess initializers', []) } ).

% init_agg(A, T, Es0, Es, X): initialize aggregate T at A from the front
% of Es0; Es is what is left.
init_agg(A, T, Es0, Es, X) --> env(E), { aggregate_slots(T, E, Slots) }, init_slots(Slots, 0, A, Es0, Es, X).
init_agg(A, T, [entry(_, I)|Es], Es, X) --> { \+ aggregate(T) }, init(A, T, I, X).

aggregate(array(_, _)).
aggregate(struct(_)).
aggregate(union(_)).

% Slots: the element positions of an aggregate, slot(Key, Offset, Type),
% with Key an index or a field name. A union initializes its first member.
aggregate_slots(array(ET, N), E, Slots) :- !,
    size_align(ET, E, S, _), N1 is N - 1,
    findall(slot(I, O, ET), ( between(0, N1, I), O is I * S ), Slots).
aggregate_slots(SU, E, Slots) :- ( SU = struct(_) ; SU = union(_) ), !,
    SU =.. [K, Id], E = e(_, _, D, _), get_assoc(Id, D, def(K, Ms, _, _)),
    findall(slot(N, O, T), member(m(N, T, O), Ms), Slots0),
    ( K == union, Slots0 = [S0|_] -> Slots = [S0] ; Slots = Slots0 ).

init_slots(_, _, _, [], [], _) --> !.
init_slots(Slots, I, A, [entry([D|Ds], V)|Es0], Es, X) --> !,
    env(E), { designated(D, Slots, I1, E, X) },
    { nth0(I1, Slots, slot(_, O, T)) },
    offset(A, O, P),
    (   { Ds == [] } -> init_one(P, T, V, Es0, Es1, X)
    ;   init_agg(P, T, [entry(Ds, V)], [], X), { Es1 = Es0 }
    ),
    { I2 is I1 + 1 },
    init_slots(Slots, I2, A, Es1, Es, X).
init_slots(Slots, I, A, Es0, Es, X) -->
    (   { nth0(I, Slots, slot(_, O, T)) }
    ->  { Es0 = [entry([], V)|Es1] },
        offset(A, O, P),
        init_one(P, T, V, Es1, Es2, X),
        { I1 is I + 1 },
        init_slots(Slots, I1, A, Es2, Es, X)
    ;   { Es = Es0 }
    ).

% One slot: a braced or scalar value, or brace elision for an aggregate
% slot given a scalar (the slot then takes as many entries as it needs).
init_one(P, T, V, Es0, Es, X) -->
    (   { V = list(_) ; \+ aggregate(T) ; T = array(ET, _), V = str(_), char_type_(ET) }
    ->  init(P, T, V, X), { Es = Es0 }
    ;   init_agg(P, T, [entry([], V)|Es0], Es, X)
    ).

designated(index(IE), Slots, I, E, X) :-
    arg(5, X, L),
    (   catch(const_value(IE, E, I, _), not_constant, fail), nth0(I, Slots, slot(I, _, _)) -> true
    ;   sema_error(L, 'bad array designator', [])
    ).
designated(field(F), Slots, I, _, X) :-
    arg(5, X, L),
    (   nth0(I, Slots, slot(F, _, _)) -> true ; sema_error(L, 'no member ~w', [F]) ).

%% Expressions

% obj(E, X, R): E as an lvalue, function designator or rvalue, without
% array decay or loading.
obj(id(N), X, R) --> !, env(E),
    (   { ord(E, N, var(A, T)) } -> { R = lv(A, T) }
    ;   { ord(E, N, fn(T, Sym, _)) } -> { R = fd(Sym, T) }
    ;   { ord(E, N, enumconst(V, T)) } -> { R = v(c(V), T) }
    ;   { ord(E, N, gvar(_, _, _, _)) } -> { arg(5, X, L), sema_error(L, 'global variable ~w is not supported yet', [N]) }
    ;   { arg(5, X, L), sema_error(L, 'undeclared identifier ~w', [N]) }
    ).
obj(un(deref, P), X, R) --> !, rval(P, X, v(V, T)),
    (   { T = ptr(func(_, _, _)) } -> { arg(5, X, L), sema_error(L, 'calls through function pointers are not supported yet', []) }
    ;   { T = ptr(OT) } -> { R = lv(V, OT) }
    ;   { arg(5, X, L), sema_error(L, 'dereferencing a non-pointer', []) }
    ).
obj(index(A, I), X, R) --> !, obj(un(deref, bin(add, A, I)), X, R).
obj(member(S, F), X, lv(P, T)) --> !, obj(S, X, R0),
    (   { R0 = lv(A, ST) } -> member_lv(A, ST, F, X, P, T)
    ;   { arg(5, X, L), sema_error(L, 'member access on a non-lvalue', []) }
    ).
obj(arrow(S, F), X, lv(P, T)) --> !, rval(S, X, v(A, PT)),
    (   { PT = ptr(ST) } -> member_lv(A, ST, F, X, P, T)
    ;   { arg(5, X, L), sema_error(L, '-> on a non-pointer', []) }
    ).
obj(str(_), X, _) --> !, { arg(5, X, L), sema_error(L, 'string literals are not supported yet', []) }.
obj(E, X, R) --> rvalue(E, X, R).

member_lv(A, ST, F, X, P, T) --> env(E), { arg(5, X, L) },
    (   { ( ST = struct(_) ; ST = union(_) ), find_member(ST, F, E, T, O) } -> offset(A, O, P)
    ;   { sema_error(L, 'no member named ~w', [F]) }
    ).

% rval(E, X, v(V, T)): the value of E, arrays decayed, lvalues loaded.
rval(E, X, R) --> obj(E, X, R0), decay(R0, X, R).

decay(v(V, T), _, v(V, T)) --> [].
decay(lv(A, array(T, _)), _, v(A, ptr(T))) --> !.
decay(lv(A, T), X, v(V, T)) --> load_typed(T, A, X, V).
decay(fd(_, _), X, _) --> { arg(5, X, L), sema_error(L, 'function pointers are not supported yet', []) }.

% The type of an expression, for sizeof: lower it, keep only the type.
type_of(E, X, T, S, S) :- phrase(obj(E, X, R), S, _), arg(2, R, T).

load_typed(T, A, X, V) -->
    (   { load_op(T, K, Op) } -> ins(K, load(Op), [A], V)
    ;   { arg(5, X, L), sema_error(L, 'loading a ~w value is not supported yet', [T]) }
    ).

load_op(bool, w, ub). load_op(char, w, sb). load_op(schar, w, sb). load_op(uchar, w, ub).
load_op(short, w, sh). load_op(ushort, w, uh). load_op(int, w, sw). load_op(uint, w, uw).
load_op(long, l, l). load_op(ulong, l, l). load_op(llong, l, l). load_op(ullong, l, l).
load_op(ptr(_), p, p).

store_typed(T, V, A) --> { store_width(T, W) }, emit(store(W, V, A)).

store_width(ptr(_), p) :- !.
store_width(T, W) :- int_info(T, S, _), memberchk(S-W, [1-b, 2-h, 4-w, 8-l]).

% offset(A, O, P): the pointer A + O.
offset(A, 0, A) --> !.
offset(A, O, P) --> ins(p, add, [A, c(O)], P).

rvalue(num(V0, S), _, v(c(V), T)) --> !, { num_type(V0, S, T), wrap(V0, T, V) }.
rvalue(chr(V), _, v(c(V), int)) --> !.
rvalue(float(_), X, _) --> !, { arg(5, X, L), sema_error(L, 'floating point is not supported', []) }.
rvalue(sizeof_type(TN), X, v(c(S), ulong)) --> !, env(E), { type_size(TN, E, X, S) }.
rvalue(alignof(TN), X, v(c(A), ulong)) --> !, env(E),
    { type_name_type(TN, T, E, _), arg(5, X, L),
      catch(size_align(T, E, _, A), bad(W), sema_error(L, 'alignof: ~w', [W])) }.
rvalue(sizeof_expr(SE), X, v(c(S), ulong)) --> !, type_of(SE, X, T), env(E),
    { arg(5, X, L), catch(size_align(T, E, S, _), bad(W), sema_error(L, 'sizeof: ~w', [W])) }.
rvalue(offsetof(TN, Path), X, v(c(V), ulong)) --> !, env(E),
    { arg(5, X, L), ( catch(const_value(offsetof(TN, Path), E, V, _), not_constant, fail) -> true
                     ; sema_error(L, 'bad offsetof', []) ) }.
rvalue(cast(TN, CE), X, R) --> !, env(E), { type_name_type(TN, T, E, _) },
    rval(CE, X, V0),
    (   { T == void } -> { R = v(c(0), void) }
    ;   convert_checked(V0, T, X, R)
    ).
rvalue(comma(A, B), X, R) --> !, rval(A, X, _), rval(B, X, R).
rvalue(un(addr, A), X, v(P, ptr(T))) --> !, obj(A, X, R0),
    (   { R0 = lv(P, T) } -> []
    ;   { arg(5, X, L), ( R0 = fd(_, _) -> sema_error(L, 'function pointers are not supported yet', [])
                         ; sema_error(L, '& of a non-lvalue', []) ) }
    ).
rvalue(un(Op, A), X, R) --> { memberchk(Op, [preinc, predec, postinc, postdec]) }, !, incdec(Op, A, X, R).
rvalue(un(Op, A), X, R) --> !, rval(A, X, V), unary(Op, V, X, R).
rvalue(bin(land, A, B), X, R) --> !, logical(land, A, B, X, R).
rvalue(bin(lor, A, B), X, R) --> !, logical(lor, A, B, X, R).
rvalue(bin(Op, A, B), X, R) --> !, rval(A, X, VA), rval(B, X, VB), binary(Op, VA, VB, X, R).
rvalue(assign(Op, A, B), X, R) --> !, assignment(Op, A, B, X, R).
rvalue(cond(C, A, B), X, R) --> !, conditional(C, A, B, X, R).
rvalue(call(F, As), X, R) --> !, fcall(F, As, X, R).
rvalue(complit(_, _), X, _) --> !, { arg(5, X, L), sema_error(L, 'compound literals are not supported yet', []) }.
rvalue(E, X, _) --> { arg(5, X, L), sema_error(L, 'cannot lower ~w', [E]) }.

type_size(TN, E, X, S) :-
    type_name_type(TN, T, E, _), arg(5, X, L),
    catch(size_align(T, E, S, _), bad(W), sema_error(L, 'sizeof: ~w', [W])).

%% Conversions

% convert(v(V, From), To, v(V1, To)), for scalar types.
convert(v(V, T), T, v(V, T)) --> !.
convert(v(V, _), void, v(V, void)) --> !.
convert(v(V, F), bool, v(B, bool)) --> !, { F \== void }, truth(v(V, F), x(_, _, _, _, unknown), W),
    (   { class_of(F, w), \+ F == bool } -> ins(w, cmp(ne, w), [W, c(0)], B)
    ;   { B = W }
    ).
convert(v(c(N), F), T, v(c(W), T)) --> { int_type(F), int_type(T) }, !, { wrap(N, T, W) }.
convert(v(V, F), T, v(V1, T)) --> { int_type(F), int_type(T) }, !, int_convert(F, T, V, V1).
convert(v(c(N), F), ptr(P), v(c(W), ptr(P))) --> { int_type(F) }, !, { wrap(N, ulong, W) }.
convert(v(V, F), ptr(P), v(V1, ptr(P))) --> { int_type(F) }, !, int_convert(F, ulong, V, V2), ins(p, itop, [V2], V1).
convert(v(V, ptr(_)), T, R) --> { int_type(T) }, !, ins(l, ptoi, [V], I), convert(v(I, ulong), T, R).
convert(v(V, ptr(_)), ptr(P), v(V, ptr(P))) --> !.

int_convert(F, T, V, V1) -->
    {   int_info(F, SF, GF), int_info(T, ST, GT) },
    (   { ST =:= 8, SF < 8 } -> { GF == signed -> Op = sw ; Op = uw }, ins(l, ext(Op), [V], V1)
    ;   { ST < 4, \+ representable(SF, GF, ST, GT) } -> { narrow_ext(ST, GT, Op) }, ins(w, ext(Op), [V], V1)
    ;   { V1 = V }
    ).

representable(SF, GF, ST, GT) :- ST > SF, ( GT == signed ; GF == unsigned ), !.
representable(S, G, S, G).

narrow_ext(1, signed, sb). narrow_ext(1, unsigned, ub).
narrow_ext(2, signed, sh). narrow_ext(2, unsigned, uh).

convert_checked(V0, T, X, R) -->
    { V0 = v(_, F), arg(5, X, L) },
    (   { scalar(F), scalar(T) } -> convert(V0, T, R)
    ;   { sema_error(L, 'cannot convert ~w to ~w', [F, T]) }
    ).

% Conversion as by assignment (also arguments and returns).
assign_convert(V0, T, L, R) -->
    { V0 = v(_, F) },
    (   { scalar(F), scalar(T) } -> convert(V0, T, R)
    ;   { sema_error(L, 'cannot assign ~w to ~w', [F, T]) }
    ).

%% Operators

unary(neg, V0, X, v(V, T)) --> arith1(V0, X, T, V1), { class_of(T, K) }, ins(K, neg, [V1], V).
unary(plus, V0, X, v(V, T)) --> arith1(V0, X, T, V).
unary(bnot, V0, X, v(V, T)) --> arith1(V0, X, T, V1), { class_of(T, K) }, ins(K, xor, [V1, c(-1)], V).
unary(not, V0, X, v(V, int)) --> truth(V0, X, W), ins(w, cmp(eq, w), [W, c(0)], V).

arith1(V0, X, T, V) --> { V0 = v(_, F), arg(5, X, L),
                          ( int_type(F) -> promote(F, T) ; sema_error(L, 'operand of type ~w is not an integer', [F]) ) },
    convert(V0, T, v(V, _)).

binary(Op, VA, VB, X, R) -->
    { VA = v(_, TA), VB = v(_, TB), arg(5, X, L) },
    (   { int_type(TA), int_type(TB) } -> int_binary(Op, VA, VB, R)
    ;   { TA = ptr(PA), int_type(TB), memberchk(Op, [add, sub]) } -> ptr_offset(Op, VA, PA, VB, X, R)
    ;   { int_type(TA), TB = ptr(PB), Op == add } -> ptr_offset(add, VB, PB, VA, X, R)
    ;   { TA = ptr(PA), TB = ptr(_), Op == sub } -> ptr_diff(VA, VB, PA, X, R)
    ;   { cmp_op(Op, _, _), ( TA = ptr(_) ; TB = ptr(_) ) } -> ptr_compare(Op, VA, VB, R)
    ;   { sema_error(L, 'invalid operands to ~w: ~w and ~w', [Op, TA, TB]) }
    ).

int_binary(Op, VA, VB, v(V, T)) --> { memberchk(Op, [shl, shr]) }, !,
    { VA = v(_, TA), promote(TA, T), class_of(T, K), int_info(T, _, G) },
    convert(VA, T, v(A, _)), { VB = v(_, TB0), promote(TB0, TB) }, convert(VB, TB, v(B, _)),
    { Op == shl -> IOp = shl ; G == signed -> IOp = sar ; IOp = shr },
    ins(K, IOp, [A, B], V).
int_binary(Op, VA, VB, v(V, int)) --> { cmp_op(Op, SC, UC) }, !,
    { VA = v(_, TA), VB = v(_, TB), usual(TA, TB, T), class_of(T, K), int_info(T, _, G) },
    convert(VA, T, v(A, _)), convert(VB, T, v(B, _)),
    { G == signed -> C = SC ; C = UC },
    ins(w, cmp(C, K), [A, B], V).
int_binary(Op, VA, VB, v(V, T)) -->
    { VA = v(_, TA), VB = v(_, TB), usual(TA, TB, T), class_of(T, K), int_info(T, _, G),
      arith_op(Op, G, IOp) },
    convert(VA, T, v(A, _)), convert(VB, T, v(B, _)),
    ins(K, IOp, [A, B], V).

cmp_op(eq, eq, eq). cmp_op(ne, ne, ne).
cmp_op(lt, slt, ult). cmp_op(gt, sgt, ugt). cmp_op(le, sle, ule). cmp_op(ge, sge, uge).

arith_op(add, _, add). arith_op(sub, _, sub). arith_op(mul, _, mul).
arith_op(div, signed, div). arith_op(div, unsigned, udiv).
arith_op(mod, signed, rem). arith_op(mod, unsigned, urem).
arith_op(and, _, and). arith_op(or, _, or). arith_op(xor, _, xor).

% P + I or P - I: I scaled by the element size.
ptr_offset(Op, v(P, PT), ET, VI, X, v(R, PT)) -->
    { PT = ptr(ET) }, env(E),
    { arg(5, X, L), catch(size_align(ET, E, S, _), bad(W), sema_error(L, 'pointer arithmetic on ~w (~w)', [ET, W])) },
    convert(VI, long, v(I, _)),
    (   { I = c(N) } -> { O is N * S, OV = c(O) }
    ;   { S =:= 1 } -> { OV = I }
    ;   ins(l, mul, [I, c(S)], OV)
    ),
    ins(p, Op, [P, OV], R).

ptr_diff(v(A, _), v(B, _), ET, X, v(V, long)) --> env(E),
    { arg(5, X, L), catch(size_align(ET, E, S, _), bad(W), sema_error(L, 'pointer subtraction on ~w (~w)', [ET, W])) },
    ins(l, ptoi, [A], IA), ins(l, ptoi, [B], IB), ins(l, sub, [IA, IB], D),
    ( { S =:= 1 } -> { V = D } ; ins(l, div, [D, c(S)], V) ).

ptr_compare(Op, VA, VB, v(V, int)) -->
    convert(VA, ulong, v(A, _)), convert(VB, ulong, v(B, _)),
    { cmp_op(Op, _, C) },
    ins(w, cmp(C, l), [A, B], V).

% && and ||: a phi of 0/1 over the short-circuit edges.
logical(Op, A, B, X, v(V, int)) -->
    rval(A, X, VA), truth(VA, X, WA), here(LA),
    label(LR), label(LJ),
    { Op == land -> J = jnz(WA, LR, LJ), Short = 0 ; J = jnz(WA, LJ, LR), Short = 1 },
    term(J),
    start(LR), rval(B, X, VB), truth(VB, X, WB),
    ins(w, cmp(ne, w), [WB, c(0)], NB),
    here(LB), term(jmp(LJ)),
    fresh(V),
    start_phi(LJ, [phi(V, w, [LA-c(Short), LB-NB])]).

conditional(C, A, B, X, R) -->
    rtype(A, X, VA0), rtype(B, X, VB0),
    { VA0 = v(_, TA), VB0 = v(_, TB), arg(5, X, L), cond_type(TA, VA0, TB, VB0, T, L) },
    label(LA), label(LB), label(LJ),
    cond_jump(C, X, LA, LB),
    start(LA), rval(A, X, VA), arm_convert(VA, T, X, VA1), here(LA1), term(jmp(LJ)),
    start(LB), rval(B, X, VB), arm_convert(VB, T, X, VB1), here(LB1), term(jmp(LJ)),
    (   { T == void } -> start(LJ), { R = v(c(0), void) }
    ;   { class_of(T, K) }, fresh(V),
        start_phi(LJ, [phi(V, K, [LA1-VA1, LB1-VB1])]),
        { R = v(V, T) }
    ).

arm_convert(V0, void, _, c(0)) --> !, { V0 = v(_, _) }.
arm_convert(V0, T, X, V) --> convert_checked(V0, T, X, v(V, _)).

% rtype(E, X, R): E's decayed value term from a throwaway lowering; only
% its type (and whether it is a constant) is used.
rtype(E, X, R, S, S) :- phrase(rval(E, X, R), S, _).

% The type of c ? a : b.
cond_type(TA, _, TB, _, T, _) :- int_type(TA), int_type(TB), !, usual(TA, TB, T).
cond_type(void, _, void, _, void, _) :- !.
cond_type(ptr(P), _, ptr(_), _, ptr(P), _) :- !.
cond_type(ptr(P), _, TB, v(c(0), _), ptr(P), _) :- int_type(TB), !.
cond_type(TA, v(c(0), _), ptr(P), _, ptr(P), _) :- int_type(TA), !.
cond_type(TA, _, TB, _, _, L) :- sema_error(L, 'incompatible ?: operands ~w and ~w', [TA, TB]).

%% Assignment

assignment(Op, A, B, X, R) --> { arg(5, X, L) },
    obj(A, X, LV),
    { LV = lv(P, T) -> true ; sema_error(L, 'assignment to a non-lvalue', []) },
    (   { Op == '=' } -> rval(B, X, V0)
    ;   { compound_op(Op, BOp) }, load_typed(T, P, X, Cur), rval(B, X, VB),
        binary(BOp, v(Cur, T), VB, X, V0)
    ),
    assign_convert(V0, T, L, R), { R = v(V, _) },
    store_typed(T, V, P).

compound_op('*=', mul). compound_op('/=', div). compound_op('%=', mod).
compound_op('+=', add). compound_op('-=', sub). compound_op('<<=', shl).
compound_op('>>=', shr). compound_op('&=', and). compound_op('^=', xor).
compound_op('|=', or).

incdec(Op, A, X, R) --> { arg(5, X, L) },
    obj(A, X, LV),
    { LV = lv(P, T), scalar(T) -> true ; sema_error(L, '~w of a non-scalar lvalue', [Op]) },
    load_typed(T, P, X, Cur),
    { memberchk(Op, [preinc, postinc]) -> BOp = add ; BOp = sub },
    binary(BOp, v(Cur, T), v(c(1), int), X, V0),
    convert(V0, T, v(New, _)),
    store_typed(T, New, P),
    { memberchk(Op, [preinc, predec]) -> R = v(New, T) ; R = v(Cur, T) }.

%% Calls

fcall(F, As, X, R) --> { arg(5, X, L) },
    obj(F, X, FD),
    (   { FD = fd(Sym, func(RT, PTs, _)) } -> []
    ;   { sema_error(L, 'calls through function pointers are not supported yet', []) }
    ),
    ( { PTs == unspecified } -> { Ps = [] } ; { Ps = PTs } ),
    { length(Ps, NP), length(As, NA),
      ( NA < NP -> sema_error(L, 'too few arguments to ~w', [Sym]) ; true ),
      ( NA > NP, PTs \== unspecified, FD = fd(_, func(_, _, fixed)) -> sema_error(L, 'too many arguments to ~w', [Sym]) ; true ) },
    call_args(As, Ps, X, Args),
    (   { RT == void } -> emit(call(void, glo(Sym), Args)), { R = v(c(0), void) }
    ;   { class_of(RT, K) } -> fresh(D), emit(call(to(D, K), glo(Sym), Args)),
        normalize(RT, D, V), { R = v(V, RT) }
    ;   { sema_error(L, 'calls returning ~w are not supported yet', [RT]) }
    ).

call_args([], _, _, []) --> [].
call_args([A|As], Ps0, X, [arg(K, V)|Args]) --> { arg(5, X, L) },
    rval(A, X, V0),
    (   { Ps0 = [PT|Ps] } -> assign_convert(V0, PT, L, v(V, T))
    ;   { Ps = [], V0 = v(_, T0) },
        (   { int_type(T0) } -> { promote(T0, T) }, convert(V0, T, v(V, _))
        ;   { T0 = ptr(_) } -> { V0 = v(V, T) }
        ;   { sema_error(L, 'passing ~w to a variadic or unprototyped function is not supported', [T0]) }
        )
    ),
    { class_of(T, K) },
    call_args(As, Ps, X, Args).

% A narrow result is re-extended: nothing guarantees the callee did.
normalize(T, V0, V) -->
    (   { int_info(T, S, G), S < 4 } -> { narrow_ext(S, G, Op) }, ins(w, ext(Op), [V0], V)
    ;   { T == bool } -> ins(w, ext(ub), [V0], V)
    ;   { V = V0 }
    ).

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
      Env     the c_types environment e(Ords, Tags, Defs, Next)
      Cur     cur(Label, Phis), or none after a jump (dead code then
              opens an unreachable block)
      Insts, Blocks, Allocs  reversed
      N       the counter for fresh temporaries and labels
      Labels  assoc from C goto labels to IR labels
      Cases   the enclosing switch's case(Value, Label) and default(Label)
    The context argument Ctx = ctx(Function, ReturnType, Break, Continue,
    Loc); Break and Continue are labels or none.

    Besides what c_types keeps there, the environment's Defs hold
    gdef(Symbol) global definitions, lit(Symbol) string literals and
    deferred(Symbol) static inline functions, and its Next numbers
    literals and compound literals as well as struct ids.
*/
:- module(c_lower, [c_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(dcgs)).
:- use_module(c_types).

% c_module(+Items, -Module): Items from c_parse.
c_module(Items, module(Funcs)) :-
    empty_env(Env0),
    foldl(top_item, Items, Funcss, Env0, Env),
    append(Funcss, Funcs0),
    with_used_inlines(Funcs0, Env, Funcs).

/* A static inline function is lowered only if something refers to it,
   as clang emits it only then; headers are full of ones nanofil cannot
   lower. Lowering one can refer to more, so this iterates. The result
   is the functions followed by the global data. */
with_used_inlines(Funcs0, Env0, Items) :-
    global_data(Env0, Data),
    append(Funcs0, Data, Items0),
    env_defs(Env0, Defs),
    findall(Sym,
            (   item_ref(Items0, Sym),
                get_assoc(deferred(Sym), Defs, _),
                \+ memberchk(func(Sym, _, _, _, _), Funcs0)
            ),
            Syms0),
    sort(Syms0, Syms),
    (   Syms == []
    ->  Items = Items0
    ;   foldl(lower_inline, Syms, New, Env0, Env1),
        append(Funcs0, New, Funcs1),
        with_used_inlines(Funcs1, Env1, Items)
    ).

% item_ref(+Items, -Sym): a symbol some function or data item refers to.
item_ref(Items, Sym) :-
    member(Item, Items),
    (   Item = func(_, _, _, _, Blocks),
        member(blk(_, _, Insts, _), Blocks),
        member(Inst, Insts),
        (   Inst = ins(_, _, _, Args), member(glo(Sym), Args)
        ;   Inst = call(_, glo(Sym), _)
        )
    ;   Item = data(_, _, _, DataItems),
        member(item(p, sym(Sym, _)), DataItems)
    ).

% Lower a deferred inline function in the scope it was defined in.
lower_inline(Sym, Func, Env0, Env) :-
    env_defs(Env0, Defs),
    get_assoc(deferred(Sym), Defs, df(Loc, Name, Type, DclType, Body, Scope)),
    env_restore(Scope, Env0, Env1),
    function(Loc, Name, Type, DclType, Body, Env1, Env2, Func),
    env_scope(Env0, Scope0, _),
    env_restore(Scope0, Env2, Env).

%% Environment

env_defs(e(_, _, Defs, _), Defs).

put_def(Key, Value, e(Ords, Tags, Defs0, Next), e(Ords, Tags, Defs, Next)) :-
    put_assoc(Key, Defs0, Value, Defs).

% next_id(-Id, +Env0, -Env): take the environment's next number.
next_id(Id, e(Ords, Tags, Defs, Id), e(Ords, Tags, Defs, Next)) :-
    Next is Id + 1.

%% Top level

top_item(static_assert(Loc, Expr, _), [], Env, Env) :- !,
    static_assert(Loc, Expr, Env).
top_item(decl(Loc, Specs, Inits), [], Env0, Env) :- !,
    catch(decl_types(Specs, Inits, Decls, Env0, Env1), not_constant,
          sema_error(Loc, 'array size is not a constant', [])),
    foldl(global_decl(Loc), Decls, Env1, Env).
top_item(fundef(Loc, Specs, dcl(Name, DclType, Asm), Body), Funcs, Env0, Env) :-
    decl_types(Specs, [init(dcl(Name, DclType, Asm), none)],
               [d(_, Type, Storage, _, _)], Env0, Env1),
    global_decl(Loc, d(Name, Type, Storage, Asm, none), Env1, Env2),
    (   memberchk(fspec(inline), Specs)
    ->  Funcs = [],
        (   Storage == static
        ->  lookup_ordinary(Env2, Name, fn(_, Sym, _)),
            env_scope(Env2, Scope, _),
            put_def(deferred(Sym), df(Loc, Name, Type, DclType, Body, Scope),
                    Env2, Env)
        ;   Env = Env2      % extern or C99 inline: the definition is elsewhere
        )
    ;   Funcs = [Func],
        function(Loc, Name, Type, DclType, Body, Env2, Env, Func)
    ).

static_assert(Loc, Expr, Env) :-
    (   catch(const_value(Expr, Env, Value, _), not_constant, fail)
    ->  true
    ;   sema_error(Loc, 'static assertion is not a constant', [])
    ),
    (   Value =\= 0
    ->  true
    ;   sema_error(Loc, 'static assertion failed', [])
    ).

global_decl(Loc, d(Name, Type0, Storage, Asm, Init), Env0, Env) :-
    ( Asm = asm(Sym) -> true ; Sym = Name ),
    (   Type0 = func(_, _, _)
    ->  ( Storage == static -> Linkage = local ; Linkage = export ),
        (   Init \== none
        ->  sema_error(Loc, 'function ~w has an initializer', [Name])
        ;   true
        ),
        bind_ordinary(Name, fn(Type0, Sym, Linkage), Env0, Env)
    ;   vm_check(Type0, Loc),
        complete_array(Type0, Init, Type, Loc, Env0, none),
        bind_ordinary(Name, gvar(Type, Sym, Storage, Init), Env0, Env1),
        (   Storage == extern, Init == none
        ->  Env = Env1
        ;   ( Storage == static -> Linkage = local ; Linkage = export ),
            define_global(Sym, Type, Linkage, Init, Loc, Env1, Env)
        )
    ).

/* Definitions of globals live in the environment's Defs under
   gdef(Symbol), string literals under lit(Symbol); both survive block
   scopes. A tentative definition (no initializer) does not replace one
   with an initializer. */
define_global(Sym, Type, Linkage, Init, Loc, Env0, Env) :-
    env_defs(Env0, Defs),
    (   get_assoc(gdef(Sym), Defs, g(_, _, Init0, _)), Init0 \== none
    ->  (   Init == none
        ->  Env = Env0
        ;   sema_error(Loc, '~w is initialized twice', [Sym])
        )
    ;   put_def(gdef(Sym), g(Type, Linkage, Init, Loc), Env0, Env)
    ).

% A literal is a list of bytes (a char array) or w(ElemType, Values).
new_literal(Lit, Sym, Env0, Env) :-
    next_id(N, Env0, Env1),
    format(atom(Sym), 'str.~w', [N]),
    put_def(lit(Sym), Lit, Env1, Env).

% A string literal term's elements: str(Bytes) for a char array, or a
% wide one for an integer array of its element's size.
str_elems(str(Bytes), ElemType, Bytes) :-
    is_char_type(ElemType).
str_elems(wstr(WideType, Values), ElemType, Values) :-
    int_type(ElemType),
    int_info(ElemType, Size, _),
    int_info(WideType, Size, _).

% A file-scope compound literal: an unnamed static object.
new_complit(Type0, Init, Loc, Sym, Env0, Env) :-
    next_id(N, Env0, Env1),
    format(atom(Sym), 'complit.~w', [N]),
    complete_array(Type0, Init, Type, Loc, Env0, none),
    define_global(Sym, Type, local, Init, Loc, Env1, Env).

% The data items for every global definition and string literal.
global_data(Env0, Data) :-
    global_items(Env0, [], GlobalData, Env),
    env_defs(Env, Defs),
    assoc_to_list(Defs, Pairs),
    findall(data(Sym, ro(local), Align, Items),
            (   member(lit(Sym)-Lit, Pairs),
                (   Lit = w(WideType, Values0)
                ->  int_info(WideType, Align, _),
                    memberchk(Align-Width, [2-h, 4-w])
                ;   Values0 = Lit, Align = 1, Width = b
                ),
                append(Values0, [0], Values),
                findall(item(Width, c(V)), member(V, Values), Items)
            ),
            LiteralData),
    append(GlobalData, LiteralData, Data).

% Initializers can define more globals (file-scope compound literals),
% so this repeats until there are no new ones. Done lists their symbols.
global_items(Env0, Done, Data, Env) :-
    env_defs(Env0, Defs),
    assoc_to_list(Defs, Pairs),
    findall(Sym-G,
            ( member(gdef(Sym)-G, Pairs), \+ memberchk(Sym, Done) ),
            New),
    (   New == []
    ->  Data = [], Env = Env0
    ;   foldl(global_item, New, Data0, Env0, Env1),
        findall(NewSym, member(NewSym-_, New), NewSyms),
        append(Done, NewSyms, Done1),
        global_items(Env1, Done1, Data1, Env),
        append(Data0, Data1, Data)
    ).

global_item(Sym-g(Type, Linkage, Init, Loc), data(Sym, Linkage, Align, Items),
            Env0, Env) :-
    catch(size_align(Type, Env0, _, Align0), bad(Why),
          sema_error(Loc, '~w has an unsupported type (~w)', [Sym, Why])),
    Align is min(Align0, 16),
    static_items(Type, Init, Loc, Env0, Env, Items).

%% Functions

function(Loc, Name, func(RetType, ParamTypes0, Variadic), DclType, Body,
         Env0, Env, func(Sym, Linkage, RetClass, Params, Blocks)) :-
    lookup_ordinary(Env0, Name, fn(_, Sym, Linkage)),
    (   Variadic == variadic
    ->  sema_error(Loc, 'defining variadic function ~w is not supported',
                   [Name])
    ;   true
    ),
    ( ParamTypes0 == unspecified -> ParamTypes = [] ; ParamTypes = ParamTypes0 ),
    ret_class(Loc, RetType, Env0, RetClass),
    param_names(DclType, Names),
    State0 = st(Env0, cur(start, []), [], [], 0, Labels, [], []),
    empty_assoc(Labels),
    Ctx = ctx(Name, RetType, none, none, Loc),
    % The DCGs thread a state term, not a list, so they are called
    % directly: SWI's phrase/3 insists on a list.
    sret_param(RetType, SretParams, State0, State1),
    params(Names, ParamTypes, Ctx, Params0, State1, State2),
    append(SretParams, Params0, Params),
    stmt(Body, Ctx, State2, State3),
    fall_off(RetType, State3, State),
    State = st(EnvEnd, none, [], RevBlocks, _, _, _, RevAllocs),
    env_scope(Env0, Scope, _),
    env_restore(Scope, EnvEnd, Env),
    reverse(RevBlocks, [blk(start, [], Insts0, Jump)|Rest]),
    reverse(RevAllocs, Allocs),
    append(Allocs, Insts0, Insts),
    Blocks = [blk(start, [], Insts, Jump)|Rest].

% ret_class(+Loc, +RetType, +Env, -Class): the IR return class.
ret_class(_, void, _, void) :- !.
ret_class(_, Type, _, Class) :-
    type_class(Type, Class), !.
ret_class(Loc, Type, Env, Class) :-
    su(Type), !,
    ret_shape(Type, Env, Loc, Shape),
    (   Shape = words([eb(_, _, K0)]) -> Class = K0
    ;   Shape = words([eb(_, _, K1), eb(_, _, K2)]) -> Class = tuple([K1, K2])
    ;   Class = void
    ).
ret_class(Loc, Type, _, _) :-
    float_type(Type), !,
    sema_error(Loc, 'floating point is not supported', []).
ret_class(Loc, Type, _, _) :-
    sema_error(Loc, 'returning ~w is not supported yet', [Type]).

% A struct over 16 bytes is returned through a pointer the caller passes
% first, as clang does; the function itself returns nothing.
sret_param(RetType, Params) -->
    env(Env),
    (   { su(RetType), ret_shape(RetType, Env, unknown, sret) }
    ->  fresh(P),
        bind('%sret', sret(P)),
        { Params = [par(p, P)] }
    ;   { Params = [] }
    ).

float_type(Type) :- memberchk(Type, [float, double, ldouble]).

% The parameter names, from the function's own declarator: the outermost
% func, since declarator types are built outermost first.
param_names(func(_, unspecified), []) :- !.
param_names(func(_, params(Params, _)), Names) :-
    findall(Name, member(param(_, dcl(Name, _, _)), Params), Names).

% params(+Names, +Types, +Ctx, -Params): the IR parameters, each named
% one stored into a local. A struct or union comes in one word per
% eightbyte.
params([], [], _, []) --> [].
params([Name|Names], [Type|Types], Ctx, Params) -->
    { su(Type) }, !,
    env(Env),
    { ctx_loc(Ctx, Loc), arg_words(Type, Env, Loc, Ebs) },
    fresh_params(Ebs, Params0, Values),
    (   { Name == none } -> []
    ;   local_slot(Type, Addr),
        store_words(Ebs, Values, Addr),
        bind(Name, var(Addr, Type))
    ),
    params(Names, Types, Ctx, Params1),
    { append(Params0, Params1, Params) }.
params([Name|Names], [Type|Types], Ctx, [par(Class, P)|Params]) -->
    { ctx_loc(Ctx, Loc),
      vm_check(Type, Loc),
      (   type_class(Type, Class) -> true
      ;   float_type(Type)
      ->  sema_error(Loc, 'floating point is not supported', [])
      ;   sema_error(Loc, 'parameter of type ~w is not supported yet', [Type])
      ) },
    fresh(P),
    (   { Name == none } -> []
    ;   local_slot(Type, Addr),
        store_typed(Type, P, Addr),
        bind(Name, var(Addr, Type))
    ),
    params(Names, Types, Ctx, Params).

fresh_params([], [], []) --> [].
fresh_params([eb(_, _, Class)|Ebs], [par(Class, P)|Params], [P|Values]) -->
    fresh(P),
    fresh_params(Ebs, Params, Values).

% Falling off the end of the body returns as a bare return would.
fall_off(RetType) -->
    cur(Cur),
    (   { Cur == none } -> []
    ;   zero_ret(RetType)
    ).

% Returning without a value from a function with a result.
zero_ret(RetType) -->
    env(Env),
    (   { RetType == void } -> term(ret)
    ;   { su(RetType), ret_shape(RetType, Env, unknown, Shape) }
    ->  (   { Shape = words([_, _]) } -> term(rets([c(0), c(0)]))
        ;   { Shape = words(_) } -> term(ret(c(0)))
        ;   term(ret)
        )
    ;   term(ret(c(0)))
    ).

%% State primitives

cur(Cur, State, State) :-
    State = st(_, Cur, _, _, _, _, _, _).

env(Env, State, State) :-
    State = st(Env, _, _, _, _, _, _, _).

set_env(Env, st(_, Cur, Insts, Blocks, N, Labels, Cases, Allocs),
             st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)).

bind(Name, Value) -->
    env(Env0),
    { bind_ordinary(Name, Value, Env0, Env) },
    set_env(Env).

fresh(t(Temp), st(Env, Cur, Insts, Blocks, N0, Labels, Cases, Allocs),
               st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)) :-
    N is N0 + 1,
    format(atom(Temp), 'v~w', [N0]).

label(Label, st(Env, Cur, Insts, Blocks, N0, Labels, Cases, Allocs),
             st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)) :-
    N is N0 + 1,
    format(atom(Label), 'L~w', [N0]).

% Make sure there is a current block, opening an unreachable one after a
% jump.
ensure_live -->
    cur(Cur),
    (   { Cur == none } -> label(Label), set_cur(cur(Label, []))
    ;   []
    ).

set_cur(Cur, st(Env, _, Insts, Blocks, N, Labels, Cases, Allocs),
             st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)).

emit(Inst) --> ensure_live, push_inst(Inst).

push_inst(Inst, st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs),
                st(Env, Cur, [Inst|Insts], Blocks, N, Labels, Cases, Allocs)).

% term(Jump): end the current block with Jump.
term(Jump) --> ensure_live, close_block(Jump).

close_block(Jump,
            st(Env, cur(Label, Phis), Insts, Blocks, N, Labels, Cases, Allocs),
            st(Env, none, [], [blk(Label, Phis, BlockInsts, Jump)|Blocks],
               N, Labels, Cases, Allocs)) :-
    reverse(Insts, BlockInsts).

% start(Label): begin block Label, falling through from a live current
% block.
start(Label) -->
    cur(Cur),
    (   { Cur == none } -> []
    ;   term(jmp(Label))
    ),
    set_cur(cur(Label, [])).

% start_phi(Label, Phis): begin block Label, reached only by jumps.
start_phi(Label, Phis) --> set_cur(cur(Label, Phis)).

% here(Label): the current block's label.
here(Label) --> ensure_live, cur(cur(Label, _)).

add_alloc(Inst, st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs),
                st(Env, Cur, Insts, Blocks, N, Labels, Cases, [Inst|Allocs])).

cases(Cases, State, State) :-
    State = st(_, _, _, _, _, _, Cases, _).

set_cases(Cases, st(Env, Cur, Insts, Blocks, N, Labels, _, Allocs),
                 st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)).

% goto_label(Name, Label): the IR label of C label Name, made on first use.
goto_label(Name, Label, State0, State) :-
    State0 = st(Env, Cur, Insts, Blocks, N0, Labels0, Cases, Allocs),
    (   get_assoc(Name, Labels0, Label)
    ->  State = State0
    ;   N is N0 + 1,
        format(atom(Label), 'L~w', [N0]),
        put_assoc(Name, Labels0, Label, Labels),
        State = st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)
    ).

% ins(Class, Op, Args, Dest): emit an instruction into a fresh temporary.
ins(Class, Op, Args, Dest) -->
    fresh(Dest),
    emit(ins(Dest, Class, Op, Args)).

% A local object: an alloc in the entry block.
local_slot(Type, Addr) -->
    env(Env),
    { catch(size_align(Type, Env, Size0, Align0), bad(Why),
            throw(nanofil_error(Why))),
      ( Align0 =< 4 -> Align = 4 ; Align = Align0 ),
      Size is max(Size0, 1) },
    fresh(Addr),
    add_alloc(ins(Addr, p, alloc(Align), [c(Size)])).

%% Context

ctx_loc(ctx(_, _, _, _, Loc), Loc).

ctx_at(ctx(Func, Ret, Break, Cont, _), Loc, ctx(Func, Ret, Break, Cont, Loc)).

loop_ctx(ctx(Func, Ret, _, _, Loc), Break, Cont,
         ctx(Func, Ret, Break, Cont, Loc)).

switch_ctx(ctx(Func, Ret, _, Cont, Loc), Break,
           ctx(Func, Ret, Break, Cont, Loc)).

%% Statements

stmt(at(Loc, Stmt), Ctx0) -->
    { ctx_at(Ctx0, Loc, Ctx) },
    stmt_(Stmt, Ctx).

stmt_(block(Items), Ctx) -->
    save_scope(Scope),
    items(Items, Ctx),
    restore_scope(Scope).
stmt_(null, _) --> [].
stmt_(expr(Expr), Ctx) --> rval(Expr, Ctx, _).
stmt_(if(Cond, Then, Else), Ctx) -->
    label(LThen), label(LElse), label(LJoin),
    cond_jump(Cond, Ctx, LThen, LElse),
    start(LThen), stmt(Then, Ctx), term(jmp(LJoin)),
    start(LElse), ( { Else == none } -> [] ; stmt(Else, Ctx) ),
    start(LJoin).
stmt_(while(Cond, Body), Ctx) -->
    label(LCond), label(LBody), label(LEnd),
    start(LCond), cond_jump(Cond, Ctx, LBody, LEnd),
    start(LBody),
    { loop_ctx(Ctx, LEnd, LCond, BodyCtx) },
    stmt(Body, BodyCtx),
    term(jmp(LCond)),
    start(LEnd).
stmt_(do(Body, Cond), Ctx) -->
    label(LBody), label(LCond), label(LEnd),
    start(LBody),
    { loop_ctx(Ctx, LEnd, LCond, BodyCtx) },
    stmt(Body, BodyCtx),
    start(LCond), cond_jump(Cond, Ctx, LBody, LEnd),
    start(LEnd).
stmt_(for(Init, Cond, Step, Body), Ctx) -->
    save_scope(Scope),
    (   { Init == none } -> []
    ;   { Init = expr(InitExpr) } -> rval(InitExpr, Ctx, _)
    ;   item(Init, Ctx)
    ),
    label(LCond), label(LBody), label(LStep), label(LEnd),
    start(LCond),
    (   { Cond == none } -> term(jmp(LBody))
    ;   cond_jump(Cond, Ctx, LBody, LEnd)
    ),
    start(LBody),
    { loop_ctx(Ctx, LEnd, LStep, BodyCtx) },
    stmt(Body, BodyCtx),
    start(LStep),
    ( { Step == none } -> [] ; rval(Step, Ctx, _) ),
    term(jmp(LCond)),
    start(LEnd),
    restore_scope(Scope).
stmt_(switch(Expr, Body), Ctx) -->
    rval(Expr, Ctx, Value0),
    { Value0 = v(_, Type0), ctx_loc(Ctx, Loc) },
    {   int_type(Type0) -> integer_promotion(Type0, Type)
    ;   sema_error(Loc, 'switch on a non-integer', [])
    },
    convert(Value0, Type, v(Value, _)),
    label(LDispatch), label(LEnd),
    term(jmp(LDispatch)),
    cases(Outer), set_cases([]),
    { switch_ctx(Ctx, LEnd, BodyCtx) },
    stmt(Body, BodyCtx),
    term(jmp(LEnd)),
    cases(Cases0), set_cases(Outer),
    { reverse(Cases0, Cases) },
    start(LDispatch), dispatch(Cases, Value, Type, LEnd),
    start(LEnd).
stmt_(case(Expr, Body), Ctx) -->
    env(Env),
    { ctx_loc(Ctx, Loc),
      (   catch(const_value(Expr, Env, Value, _), not_constant, fail) -> true
      ;   sema_error(Loc, 'case label is not a constant', [])
      ) },
    label(Label), start(Label),
    cases(Cases), set_cases([case(Value, Label)|Cases]),
    stmt(Body, Ctx).
stmt_(default(Body), Ctx) -->
    label(Label), start(Label),
    cases(Cases), set_cases([default(Label)|Cases]),
    stmt(Body, Ctx).
stmt_(break, Ctx) -->
    { Ctx = ctx(_, _, Break, _, Loc),
      (   Break == none
      ->  sema_error(Loc, 'break outside a loop or switch', [])
      ;   true
      ) },
    term(jmp(Break)).
stmt_(continue, Ctx) -->
    { Ctx = ctx(_, _, _, Cont, Loc),
      (   Cont == none
      ->  sema_error(Loc, 'continue outside a loop', [])
      ;   true
      ) },
    term(jmp(Cont)).
stmt_(return(none), Ctx) -->
    { Ctx = ctx(_, RetType, _, _, _) },
    zero_ret(RetType).
stmt_(return(Expr), Ctx) -->
    { Expr \== none, Ctx = ctx(_, RetType, _, _, Loc) },
    rval(Expr, Ctx, Value0),
    (   { RetType == void } -> term(ret)
    ;   { su(RetType) }
    ->  assign_convert(Value0, RetType, Loc, v(Addr, _)),
        return_struct(RetType, Addr, Loc)
    ;   assign_convert(Value0, RetType, Loc, v(Value, _)),
        term(ret(Value))
    ).
stmt_(goto(Name), _) -->
    goto_label(Name, Label),
    term(jmp(Label)).
stmt_(label(Name, Body), Ctx) -->
    goto_label(Name, Label),
    start(Label),
    stmt(Body, Ctx).
stmt_(decl(Loc, Specs, Inits), Ctx) -->
    item(decl(Loc, Specs, Inits), Ctx).

% A block scope: save_scope(Scope) on entry, restore_scope(Scope) on exit.
save_scope(Scope) -->
    env(Env),
    { env_scope(Env, Scope, _) }.

restore_scope(Scope) -->
    env(Env0),
    { env_restore(Scope, Env0, Env) },
    set_env(Env).

items([], _) --> [].
items([Item|Items], Ctx) --> item(Item, Ctx), items(Items, Ctx).

item(at(Loc, Stmt), Ctx) --> !, stmt(at(Loc, Stmt), Ctx).
item(static_assert(Loc, Expr, _), _) --> !,
    env(Env),
    { static_assert(Loc, Expr, Env) }.
item(decl(Loc, Specs, Inits), Ctx0) -->
    env(Env0),
    { catch(decl_types(Specs, Inits, Decls, Env0, Env), not_constant,
            sema_error(Loc, 'array size is not a constant', [])) },
    set_env(Env),
    { ctx_at(Ctx0, Loc, Ctx) },
    local_decls(Decls, Ctx).

% Block-scope declarations: functions and extern objects are global,
% a static object is a global with a function-qualified name, anything
% else is a local slot.
local_decls([], _) --> [].
local_decls([d(Name, Type0, Storage, Asm, Init)|Decls], Ctx) -->
    { ctx_loc(Ctx, Loc) },
    (   { Type0 = func(_, _, _) ; Storage == extern }
    ->  env(Env0),
        { global_decl(Loc, d(Name, Type0, Storage, Asm, Init), Env0, Env) },
        set_env(Env)
    ;   { Storage == static }
    ->  env(Env0),
        { Ctx = ctx(Func, _, _, _, _),
          next_id(K, Env0, Env1),
          format(atom(Sym), '~w.~w.~w', [Func, Name, K]),
          complete_array(Type0, Init, Type, Loc, Env0, none),
          bind_ordinary(Name, gvar(Type, Sym, static, Init), Env1, Env2),
          define_global(Sym, Type, local, Init, Loc, Env2, Env) },
        set_env(Env)
    ;   env(Env),
        whole_probe(Ctx, Whole),
        { complete_array(Type0, Init, Type, Loc, Env, Whole),
          check_local_type(Type, Env, Loc, Name) },
        local_slot(Type, Addr),
        bind(Name, var(Addr, Type)),
        (   { Init == none } -> []
        ;   init(Addr, Type, Init, Ctx)
        )
    ),
    local_decls(Decls, Ctx).

check_local_type(Type, Env, Loc, Name) :-
    vm_check(Type, Loc),
    catch(( size_align(Type, Env, _, _) -> true ; true ), bad(Why),
          sema_error(Loc, '~w has a type nanofil does not support (~w)',
                     [Name, Why])).

/* An array of unknown size takes its size from the initializer, counting
   the entries each element takes with brace elision: {1, 2, 3, 4} is two
   elements of a struct {int a, b}. Whole is whole(Ctx, State) when an
   entry may be a struct expression that initializes a struct element
   whole (locals), none otherwise. */
complete_array(array(ElemType, none), none, array(ElemType, none), _, _, _) :- !.
complete_array(array(ElemType, none), Init, array(ElemType, N), Loc, Env,
               Whole) :- !,
    (   str_elems(Init, ElemType, Bytes), length(Bytes, N0) -> N is N0 + 1
    ;   Init = list(Entries)
    ->  list_extent(Entries, ElemType, Env, Whole, 0, 0, N)
    ;   sema_error(Loc, 'array of unknown size', [])
    ).
complete_array(Type, _, Type, _, _, _).

% list_extent(+Entries, +ElemType, +Env, +Whole, +Index, +Max0, -Max):
% one more than the largest element index the entries reach.
list_extent([], _, _, _, _, Max, Max).
list_extent([entry(Desigs, V)|Entries0], ElemType, Env, Whole, Index0, Max0,
            Max) :-
    ( Desigs = [index(num(Index, _))|_] -> true ; Index = Index0 ),
    (   Desigs = [_, _|_] -> Entries = Entries0
    ;   consume(ElemType, Env, Whole, [entry([], V)|Entries0], Entries)
    ),
    Index1 is Index + 1,
    Max1 is max(Max0, Index1),
    list_extent(Entries, ElemType, Env, Whole, Index1, Max1, Max).

% consume(Type, Env, Whole, Entries0, Entries): the entries a slot of type
% Type takes, as init_one does: one if it initializes Type by itself,
% else one per slot of Type recursively, stopping at a designator or the
% end.
consume(Type, _, Whole, [entry(_, V)|Entries], Entries) :-
    elided_one(Type, V, Whole), !.
consume(Type, Env, Whole, Entries0, Entries) :-
    aggregate_slots(Type, Env, Slots),
    consume_slots(Slots, Env, Whole, Entries0, Entries).

consume_slots([], _, _, Entries, Entries).
consume_slots([slot(_, _, Type)|Slots], Env, Whole, Entries0, Entries) :-
    (   Entries0 = [entry([], _)|_]
    ->  consume(Type, Env, Whole, Entries0, Entries1),
        consume_slots(Slots, Env, Whole, Entries1, Entries)
    ;   Entries = Entries0
    ).

% An entry that initializes a slot of type Type by itself.
elided_one(Type, V, Whole) :-
    (   V = list(_)
    ;   \+ aggregate(Type)
    ;   Type = array(CharType, _), str_elems(V, CharType, _)
    ;   Whole = whole(Ctx, State), su(Type), struct_expr(V, Ctx, Type, State, _)
    ), !.

% whole_probe(Ctx, Whole): Whole lets complete_array test, in the current
% state, whether an entry is a struct expression.
whole_probe(Ctx, whole(Ctx, State), State, State).

% The switch dispatch: one comparison per case, then the default.
dispatch([], _, _, LEnd) --> term(jmp(LEnd)).
dispatch(Cases, Value, Type, LEnd) -->
    { findall(CaseValue-Label, member(case(CaseValue, Label), Cases), Pairs),
      ( memberchk(default(LDefault), Cases) -> true ; LDefault = LEnd ),
      type_class(Type, Class) },
    dispatch_cases(Pairs, Value, Type, Class, LDefault).

dispatch_cases([], _, _, _, LDefault) --> term(jmp(LDefault)).
dispatch_cases([CaseValue-Label|Pairs], Value, Type, Class, LDefault) -->
    { convert_int(CaseValue, Type, Wrapped) },
    ins(w, cmp(eq, Class), [Value, c(Wrapped)], Test),
    label(Next),
    term(jnz(Test, Label, Next)),
    start(Next),
    dispatch_cases(Pairs, Value, Type, Class, LDefault).

% cond_jump(Expr, Ctx, LTrue, LFalse): branch on the truth of a scalar.
cond_jump(Expr, Ctx, LTrue, LFalse) -->
    rval(Expr, Ctx, Value),
    truth(Value, Ctx, Test),
    term(jnz(Test, LTrue, LFalse)).

% truth(V, Ctx, W): a w value that is nonzero exactly when V is.
truth(v(V, Type), Ctx, W) -->
    (   { type_class(Type, w) } -> { W = V }
    ;   { type_class(Type, l) } -> ins(w, cmp(ne, l), [V, c(0)], W)
    ;   { Type = ptr(_) }
    ->  ins(l, ptoi, [V], Int),
        ins(w, cmp(ne, l), [Int, c(0)], W)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'a ~w value is not a scalar', [Type]) }
    ).

%% Initializers

% init(Addr, Type, Init, Ctx): initialize the local object at Addr.
init(Addr, Type, Init, Ctx) -->
    { ctx_loc(Ctx, Loc) },
    (   { Init = list(Entries) }
    ->  zero_object(Addr, Type),
        init_list(Addr, Type, Entries, Ctx)
    ;   { Type = array(ElemType, N), str_elems(Init, ElemType, Bytes) }
    ->  zero_object(Addr, Type),
        init_string(Addr, ElemType, N, Bytes, Loc)
    ;   { Type = array(_, _) }
    ->  { sema_error(Loc, 'array initializer must be a list', []) }
    ;   rval(Init, Ctx, Value0),
        assign_convert(Value0, Type, Loc, v(Value, _)),
        store_typed(Type, Value, Addr)
    ).

is_char_type(Type) :- memberchk(Type, [char, schar, uchar]).

init_string(Addr, ElemType, N, Bytes, Loc) -->
    { length(Bytes, NBytes),
      (   NBytes > N
      ->  sema_error(Loc, 'string initializer is too long', [])
      ;   true
      ),
      store_width(ElemType, Width),
      width_bytes(Width, Size),
      findall(Off-Byte, ( nth0(I, Bytes, Byte), Off is I * Size ), Pairs) },
    store_elems(Pairs, Width, Addr).

store_elems([], _, _) --> [].
store_elems([Off-Value|Pairs], Width, Addr) -->
    offset(Addr, Off, P),
    emit(store(Width, c(Value), P)),
    store_elems(Pairs, Width, Addr).

% zero_object(Addr, Type): clear the whole object, since allocs are
% hoisted and a local inside a loop must be reinitialized on every pass.
zero_object(Addr, Type) -->
    env(Env),
    { size_align(Type, Env, Size, Align) },
    zero_bytes(Addr, 0, Size, Align).

% zero_bytes(Addr, Off, Size, Align): zero Off..Size with the widest
% stores the alignment allows.
zero_bytes(_, Off, Size, _) --> { Off >= Size }, !.
zero_bytes(Addr, Off, Size, Align) -->
    { Left is Size - Off,
      member(Width-N, [l-8, w-4, h-2, b-1]),
      N =< Left, N =< Align, Off mod N =:= 0 }, !,
    offset(Addr, Off, P),
    emit(store(Width, c(0), P)),
    { Off1 is Off + N },
    zero_bytes(Addr, Off1, Size, Align).

% init_list(Addr, Type, Entries, Ctx): a braced list for an array or
% struct, with designators and brace elision.
init_list(Addr, Type, Entries, Ctx) -->
    init_agg(Addr, Type, Entries, Rest, Ctx),
    { ctx_loc(Ctx, Loc) },
    (   { Rest == [] } -> []
    ;   { sema_error(Loc, 'excess initializers', []) }
    ).

% init_agg(Addr, Type, Entries0, Entries, Ctx): initialize aggregate Type
% at Addr from the front of Entries0; Entries is what is left.
init_agg(Addr, Type, Entries0, Entries, Ctx) -->
    env(Env),
    { aggregate_slots(Type, Env, Slots) },
    init_slots(Slots, 0, Addr, Entries0, Entries, Ctx).
init_agg(Addr, Type, [entry(_, Init)|Entries], Entries, Ctx) -->
    { \+ aggregate(Type) },
    init(Addr, Type, Init, Ctx).

aggregate(array(_, _)).
aggregate(struct(_)).
aggregate(union(_)).

% Slots: the element positions of an aggregate, slot(Key, Offset, Type),
% with Key an index or a field name. A union initializes its first member.
aggregate_slots(array(ElemType, N), Env, Slots) :- !,
    size_align(ElemType, Env, Size, _),
    Last is N - 1,
    findall(slot(I, Off, ElemType),
            ( between(0, Last, I), Off is I * Size ),
            Slots).
aggregate_slots(SU, Env, Slots) :-
    ( SU = struct(_) ; SU = union(_) ), !,
    SU =.. [Kind, Id],
    env_defs(Env, Defs),
    get_assoc(Id, Defs, def(Kind, Members, _, _)),
    findall(slot(Name, Off, Type), member(m(Name, Type, Off), Members), Slots0),
    (   Kind == union, Slots0 = [First|_] -> Slots = [First]
    ;   Slots = Slots0
    ).

% init_slots(Slots, Index, Addr, Entries0, Entries, Ctx): initialize the
% slots from Index on; a designated entry moves to its slot.
init_slots(_, _, _, [], [], _) --> !.
init_slots(Slots, _, Addr, [entry([Desig|Desigs], V)|Entries0], Entries,
           Ctx) --> !,
    env(Env),
    { designated(Desig, Slots, Index, Env, Ctx) },
    { nth0(Index, Slots, slot(_, Off, Type)) },
    offset(Addr, Off, P),
    (   { Desigs == [] }
    ->  init_one(P, Type, V, Entries0, Entries1, Ctx)
    ;   init_agg(P, Type, [entry(Desigs, V)], [], Ctx),
        { Entries1 = Entries0 }
    ),
    { Index1 is Index + 1 },
    init_slots(Slots, Index1, Addr, Entries1, Entries, Ctx).
init_slots(Slots, Index, Addr, Entries0, Entries, Ctx) -->
    (   { nth0(Index, Slots, slot(_, Off, Type)) }
    ->  { Entries0 = [entry([], V)|Entries1] },
        offset(Addr, Off, P),
        init_one(P, Type, V, Entries1, Entries2, Ctx),
        { Index1 is Index + 1 },
        init_slots(Slots, Index1, Addr, Entries2, Entries, Ctx)
    ;   { Entries = Entries0 }
    ).

% One slot: a braced or scalar value, or brace elision for an aggregate
% slot given a scalar (the slot then takes as many entries as it needs).
init_one(P, Type, V, Entries0, Entries, Ctx) -->
    (   { V = list(_)
        ; \+ aggregate(Type)
        ; Type = array(ElemType, _), str_elems(V, ElemType, _)
        }
    ->  init(P, Type, V, Ctx),
        { Entries = Entries0 }
    ;   { su(Type) }, struct_expr(V, Ctx, Type)
    ->  init(P, Type, V, Ctx),
        { Entries = Entries0 }
    ;   { undesignated(Entries0, Pre, Post) },
        init_agg(P, Type, [entry([], V)|Pre], Rest, Ctx),
        { append(Rest, Post, Entries) }
    ).

% An elided aggregate takes entries only up to the next designator, which
% belongs to the enclosing list.
undesignated(Entries, Pre, Post) :-
    append(Pre, Post, Entries),
    \+ member(entry([_|_], _), Pre),
    ( Post = [] ; Post = [entry([_|_], _)|_] ), !.

% designated(Desig, Slots, Index, Env, Ctx): the slot a designator names.
designated(index(Expr), Slots, Index, Env, Ctx) :-
    ctx_loc(Ctx, Loc),
    (   catch(const_value(Expr, Env, Index, _), not_constant, fail),
        nth0(Index, Slots, slot(Index, _, _))
    ->  true
    ;   sema_error(Loc, 'bad array designator', [])
    ).
designated(field(Field), Slots, Index, _, Ctx) :-
    ctx_loc(Ctx, Loc),
    (   nth0(Index, Slots, slot(Field, _, _)) -> true
    ;   sema_error(Loc, 'no member ~w', [Field])
    ).

%% Expressions

% obj(Expr, Ctx, R): Expr as an lvalue, function designator or rvalue,
% without array decay or loading.
obj(id(Name), Ctx, R) --> !,
    env(Env),
    (   { lookup_ordinary(Env, Name, var(Addr, Type)) } -> { R = lv(Addr, Type) }
    ;   { lookup_ordinary(Env, Name, fn(Type, Sym, _)) } -> { R = fd(glo(Sym), Type) }
    ;   { lookup_ordinary(Env, Name, enumconst(V, Type)) } -> { R = v(c(V), Type) }
    ;   { lookup_ordinary(Env, Name, gvar(Type, Sym, _, _)) }
    ->  ins(p, copy, [glo(Sym)], Addr),
        { R = lv(Addr, Type) }
    ;   { memberchk(Name, ['__func__', '__FUNCTION__', '__PRETTY_FUNCTION__']) }
    ->  { Ctx = ctx(Func, _, _, _, _), atom_codes(Func, Bytes) },
        obj(str(Bytes), Ctx, R)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'undeclared identifier ~w', [Name]) }
    ).
obj(un(deref, Ptr), Ctx, R) --> !,
    rval(Ptr, Ctx, v(V, Type)),
    (   { Type = ptr(FuncType), FuncType = func(_, _, _) }
    ->  callee_temp(V, Callee),
        { R = fd(Callee, FuncType) }
    ;   { Type = ptr(ObjType) } -> { R = lv(V, ObjType) }
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'dereferencing a non-pointer', []) }
    ).
obj(index(Array, Index), Ctx, R) --> !,
    obj(un(deref, bin(add, Array, Index)), Ctx, R).
obj(member(SU, Field), Ctx, lv(P, Type)) --> !,
    obj(SU, Ctx, R0),
    (   { R0 = lv(Addr, SUType) }
    ->  member_lv(Addr, SUType, Field, Ctx, P, Type)
    ;   { R0 = v(Addr, SUType), su(SUType) }
    ->  member_lv(Addr, SUType, Field, Ctx, P, Type)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'member access on a non-lvalue', []) }
    ).
obj(arrow(Ptr, Field), Ctx, lv(P, Type)) --> !,
    rval(Ptr, Ctx, v(Addr, PtrType)),
    (   { PtrType = ptr(SUType) }
    ->  member_lv(Addr, SUType, Field, Ctx, P, Type)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, '-> on a non-pointer', []) }
    ).
obj(str(Bytes), _, lv(Addr, array(char, N))) --> !,
    env(Env0),
    { new_literal(Bytes, Sym, Env0, Env),
      length(Bytes, N0),
      N is N0 + 1 },
    set_env(Env),
    ins(p, copy, [glo(Sym)], Addr).
obj(wstr(WideType, Values), _, lv(Addr, array(WideType, N))) --> !,
    env(Env0),
    { new_literal(w(WideType, Values), Sym, Env0, Env),
      length(Values, N0),
      N is N0 + 1 },
    set_env(Env),
    ins(p, copy, [glo(Sym)], Addr).
% A compound literal is an unnamed local, initialized where it appears.
obj(complit(TypeName, Init), Ctx, lv(Addr, Type)) --> !,
    env(Env),
    whole_probe(Ctx, Whole),
    { ctx_loc(Ctx, Loc),
      type_name(TypeName, Type0, Env, Loc),
      complete_array(Type0, Init, Type, Loc, Env, Whole),
      check_local_type(Type, Env, Loc, 'compound literal') },
    local_slot(Type, Addr),
    init(Addr, Type, Init, Ctx).
obj(Expr, Ctx, R) --> rvalue(Expr, Ctx, R).

% A callee must be a temporary.
callee_temp(t(T), t(T)) --> !.
callee_temp(V, Callee) --> ins(p, copy, [V], Callee).

member_lv(Addr, SUType, Field, Ctx, P, Type) -->
    env(Env),
    { ctx_loc(Ctx, Loc) },
    (   { ( SUType = struct(_) ; SUType = union(_) ),
          find_member(SUType, Field, Env, Type, Off) }
    ->  offset(Addr, Off, P)
    ;   { sema_error(Loc, 'no member named ~w', [Field]) }
    ).

% rval(Expr, Ctx, v(V, Type)): the value of Expr, arrays decayed, lvalues
% loaded.
rval(Expr, Ctx, R) --> obj(Expr, Ctx, R0), decay(R0, Ctx, R).

decay(v(V, Type), _, v(V, Type)) --> [].
decay(lv(Addr, array(Type, _)), _, v(Addr, ptr(Type))) --> !.
decay(lv(Addr, Type), _, v(Addr, Type)) --> { su(Type) }, !.
decay(lv(Addr, Type), Ctx, v(V, Type)) --> load_typed(Type, Addr, Ctx, V).
decay(fd(glo(Sym), Type), _, v(Addr, ptr(Type))) --> !,
    ins(p, copy, [glo(Sym)], Addr).
decay(fd(Callee, Type), _, v(Callee, ptr(Type))) --> [].

% The type of an expression, for sizeof: lower it, keep only the type.
type_of(Expr, Ctx, Type, State, State) :-
    obj(Expr, Ctx, R, State, _),
    arg(2, R, Type).

load_typed(Type, Addr, Ctx, V) -->
    (   { load_op(Type, Class, Op) } -> ins(Class, load(Op), [Addr], V)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'loading a ~w value is not supported yet', [Type]) }
    ).

% load_op(Type, Class, Op): the class and load of a scalar.
load_op(bool, w, ub).
load_op(char, w, sb).
load_op(schar, w, sb).
load_op(uchar, w, ub).
load_op(short, w, sh).
load_op(ushort, w, uh).
load_op(int, w, sw).
load_op(uint, w, uw).
load_op(long, l, l).
load_op(ulong, l, l).
load_op(llong, l, l).
load_op(ullong, l, l).
load_op(ptr(_), p, p).

store_typed(Type, V, Addr) --> { su(Type) }, !, copy_object(Type, V, Addr).
store_typed(Type, V, Addr) -->
    { store_width(Type, Width) },
    emit(store(Width, V, Addr)).

store_width(ptr(_), p) :- !.
store_width(Type, Width) :-
    int_info(Type, Size, _),
    memberchk(Size-Width, [1-b, 2-h, 4-w, 8-l]).

% offset(Addr, Off, P): the pointer Addr + Off.
offset(Addr, 0, Addr) --> !.
offset(Addr, Off, P) --> ins(p, add, [Addr, c(Off)], P).

% rvalue(Expr, Ctx, R): the expressions that are only rvalues.
rvalue(num(V0, Suffix), _, v(c(V), Type)) --> !,
    { num_type(V0, Suffix, Type), convert_int(V0, Type, V) }.
rvalue(chr(V), _, v(c(V), int)) --> !.
rvalue(float(_), Ctx, _) --> !,
    { ctx_loc(Ctx, Loc),
      sema_error(Loc, 'floating point is not supported', []) }.
rvalue(sizeof_type(TypeName), Ctx, v(c(Size), ulong)) --> !,
    env(Env),
    { type_size(TypeName, Env, Ctx, Size) }.
rvalue(alignof(TypeName), Ctx, v(c(Align), ulong)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc),
      type_name(TypeName, Type, Env, Loc),
      catch(size_align(Type, Env, _, Align), bad(Why),
            sema_error(Loc, 'alignof: ~w', [Why])) }.
rvalue(sizeof_expr(Expr), Ctx, v(c(Size), ulong)) --> !,
    type_of(Expr, Ctx, Type),
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(size_align(Type, Env, Size, _), bad(Why),
            sema_error(Loc, 'sizeof: ~w', [Why])) }.
rvalue(offsetof(TypeName, Path), Ctx, v(c(V), ulong)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc),
      (   catch(const_value(offsetof(TypeName, Path), Env, V, _),
                not_constant, fail)
      ->  true
      ;   sema_error(Loc, 'bad offsetof', [])
      ) }.
rvalue(cast(TypeName, Expr), Ctx, R) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc), type_name(TypeName, Type, Env, Loc) },
    rval(Expr, Ctx, Value0),
    (   { Type == void } -> { R = v(c(0), void) }
    ;   convert_checked(Value0, Type, Ctx, R)
    ).
rvalue(comma(A, B), Ctx, R) --> !,
    rval(A, Ctx, _),
    rval(B, Ctx, R).
rvalue(un(addr, Expr), Ctx, v(P, ptr(Type))) --> !,
    obj(Expr, Ctx, R0),
    (   { R0 = lv(P, Type) } -> []
    ;   { R0 = fd(_, _) } -> decay(R0, Ctx, v(P, ptr(Type)))
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, '& of a non-lvalue', []) }
    ).
rvalue(un(Op, Expr), Ctx, R) -->
    { memberchk(Op, [preinc, predec, postinc, postdec]) }, !,
    incdec(Op, Expr, Ctx, R).
rvalue(un(Op, Expr), Ctx, R) --> !,
    rval(Expr, Ctx, V),
    unary(Op, V, Ctx, R).
rvalue(bin(land, A, B), Ctx, R) --> !, logical(land, A, B, Ctx, R).
rvalue(bin(lor, A, B), Ctx, R) --> !, logical(lor, A, B, Ctx, R).
rvalue(bin(Op, A, B), Ctx, R) --> !,
    rval(A, Ctx, VA),
    rval(B, Ctx, VB),
    binary(Op, VA, VB, Ctx, R).
rvalue(assign(Op, A, B), Ctx, R) --> !, assignment(Op, A, B, Ctx, R).
rvalue(cond(Cond, A, B), Ctx, R) --> !, conditional(Cond, A, B, Ctx, R).
rvalue(call(id('__builtin_expect'), [A, B]), Ctx, R) -->
    env(Env),
    { \+ lookup_ordinary(Env, '__builtin_expect', _) }, !,
    rval(A, Ctx, VA),
    rval(B, Ctx, _),
    { ctx_loc(Ctx, Loc) },
    assign_convert(VA, long, Loc, R).
rvalue(call(Func, Args), Ctx, R) --> !, lower_call(Func, Args, Ctx, R).
rvalue(gcond(Cond, B), Ctx, R) --> !, gnu_conditional(Cond, B, Ctx, R).
rvalue(Expr, Ctx, _) -->
    { ctx_loc(Ctx, Loc),
      sema_error(Loc, 'cannot lower ~w', [Expr]) }.

type_size(TypeName, Env, Ctx, Size) :-
    ctx_loc(Ctx, Loc),
    type_name(TypeName, Type, Env, Loc),
    catch(size_align(Type, Env, Size, _), bad(Why),
          sema_error(Loc, 'sizeof: ~w', [Why])).

% A type name as lowering uses it: a variably modified one (an array of
% non-constant size anywhere inside) is rejected, since its size
% expressions would have to be evaluated, side effects and all.
type_name(TypeName, Type, Env, Loc) :-
    type_name_type(TypeName, Type, Env, _),
    vm_check(Type, Loc).

vm_check(Type, Loc) :-
    (   vm_type(Type)
    ->  sema_error(Loc,
                   'variably modified types (non-constant array size) are not supported',
                   [])
    ;   true
    ).

% vm_type(Type): Type is variably modified.
vm_type(bad('non-constant array size')).
vm_type(ptr(Type)) :- vm_type(Type).
vm_type(array(Type, _)) :- vm_type(Type).
vm_type(func(Ret, Params, _)) :-
    (   vm_type(Ret)
    ;   is_list(Params), member(Param, Params), vm_type(Param)
    ), !.

%% Conversions

% convert(v(V, From), To, v(V1, To)), for scalar types.
convert(v(V, Type), Type, v(V, Type)) --> !.
convert(v(V, _), void, v(V, void)) --> !.
convert(v(V, From), bool, v(B, bool)) --> !,
    { From \== void },
    truth(v(V, From), ctx(_, _, _, _, unknown), W),
    (   { type_class(From, w), \+ From == bool }
    ->  ins(w, cmp(ne, w), [W, c(0)], B)
    ;   { B = W }
    ).
convert(v(c(N), From), To, v(c(W), To)) -->
    { int_type(From), int_type(To) }, !,
    { convert_int(N, To, W) }.
convert(v(V, From), To, v(V1, To)) -->
    { int_type(From), int_type(To) }, !,
    int_convert(From, To, V, V1).
convert(v(c(N), From), ptr(P), v(c(W), ptr(P))) -->
    { int_type(From) }, !,
    { convert_int(N, ulong, W) }.
convert(v(V, From), ptr(P), v(V1, ptr(P))) -->
    { int_type(From) }, !,
    int_convert(From, ulong, V, V2),
    ins(p, itop, [V2], V1).
convert(v(V, ptr(_)), To, R) -->
    { int_type(To) }, !,
    ins(l, ptoi, [V], Int),
    convert(v(Int, ulong), To, R).
convert(v(V, ptr(_)), ptr(P), v(V, ptr(P))) --> !.

int_convert(From, To, V, V1) -->
    { int_info(From, SizeFrom, SignFrom), int_info(To, SizeTo, SignTo) },
    (   { SizeTo =:= 8, SizeFrom < 8 }
    ->  { SignFrom == signed -> Op = sw ; Op = uw },
        ins(l, ext(Op), [V], V1)
    ;   { SizeTo < 4, \+ representable(SizeFrom, SignFrom, SizeTo, SignTo) }
    ->  { narrow_ext(SizeTo, SignTo, Op) },
        ins(w, ext(Op), [V], V1)
    ;   { V1 = V }
    ).

% representable(SizeFrom, SignFrom, SizeTo, SignTo): every value of the
% source type is a value of the target type.
representable(SizeFrom, SignFrom, SizeTo, SignTo) :-
    SizeTo > SizeFrom,
    ( SignTo == signed ; SignFrom == unsigned ), !.
representable(Size, Sign, Size, Sign).

% narrow_ext(Size, Sign, Op): the extension that normalizes a narrow int.
narrow_ext(1, signed, sb).
narrow_ext(1, unsigned, ub).
narrow_ext(2, signed, sh).
narrow_ext(2, unsigned, uh).

% Conversion as by a cast.
convert_checked(Value0, To, Ctx, R) -->
    { Value0 = v(_, From), ctx_loc(Ctx, Loc) },
    (   { scalar_type(From), scalar_type(To) } -> convert(Value0, To, R)
    ;   { sema_error(Loc, 'cannot convert ~w to ~w', [From, To]) }
    ).

% Conversion as by assignment (also arguments and returns).
assign_convert(Value0, To, Loc, R) -->
    { Value0 = v(Addr, From) },
    (   { su(To) }
    ->  (   { From == To } -> { R = v(Addr, To) }
        ;   { sema_error(Loc, 'cannot assign ~w to ~w', [From, To]) }
        )
    ;   { scalar_type(From), scalar_type(To) } -> convert(Value0, To, R)
    ;   { sema_error(Loc, 'cannot assign ~w to ~w', [From, To]) }
    ).

%% Operators

unary(neg, Value0, Ctx, v(V, Type)) -->
    arith_operand(Value0, Ctx, Type, V1),
    { type_class(Type, Class) },
    ins(Class, neg, [V1], V).
unary(plus, Value0, Ctx, v(V, Type)) -->
    arith_operand(Value0, Ctx, Type, V).
unary(bnot, Value0, Ctx, v(V, Type)) -->
    arith_operand(Value0, Ctx, Type, V1),
    { type_class(Type, Class) },
    ins(Class, xor, [V1, c(-1)], V).
unary(not, Value0, Ctx, v(V, int)) -->
    truth(Value0, Ctx, W),
    ins(w, cmp(eq, w), [W, c(0)], V).

% arith_operand(Value0, Ctx, Type, V): an integer operand, promoted to
% Type.
arith_operand(Value0, Ctx, Type, V) -->
    { Value0 = v(_, From), ctx_loc(Ctx, Loc),
      (   int_type(From) -> integer_promotion(From, Type)
      ;   sema_error(Loc, 'operand of type ~w is not an integer', [From])
      ) },
    convert(Value0, Type, v(V, _)).

binary(Op, VA, VB, Ctx, R) -->
    { VA = v(_, TA), VB = v(_, TB), ctx_loc(Ctx, Loc) },
    (   { int_type(TA), int_type(TB) } -> int_binary(Op, VA, VB, R)
    ;   { TA = ptr(PA), int_type(TB), memberchk(Op, [add, sub]) }
    ->  ptr_offset(Op, VA, PA, VB, Ctx, R)
    ;   { int_type(TA), TB = ptr(PB), Op == add }
    ->  ptr_offset(add, VB, PB, VA, Ctx, R)
    ;   { TA = ptr(PA), TB = ptr(_), Op == sub }
    ->  ptr_diff(VA, VB, PA, Ctx, R)
    ;   { cmp_op(Op, _, _), ( TA = ptr(_) ; TB = ptr(_) ) }
    ->  ptr_compare(Op, VA, VB, R)
    ;   { sema_error(Loc, 'invalid operands to ~w: ~w and ~w', [Op, TA, TB]) }
    ).

% Shifts promote each operand on its own; comparisons and arithmetic
% convert both to their usual arithmetic type.
int_binary(Op, VA, VB, v(V, Type)) -->
    { memberchk(Op, [shl, shr]) }, !,
    { VA = v(_, TA), integer_promotion(TA, Type), type_class(Type, Class),
      int_info(Type, _, Sign) },
    convert(VA, Type, v(A, _)),
    { VB = v(_, TB0), integer_promotion(TB0, TB) },
    convert(VB, TB, v(B, _)),
    { Op == shl -> IOp = shl ; Sign == signed -> IOp = sar ; IOp = shr },
    ins(Class, IOp, [A, B], V).
int_binary(Op, VA, VB, v(V, int)) -->
    { cmp_op(Op, SignedCmp, UnsignedCmp) }, !,
    { VA = v(_, TA),
      VB = v(_, TB),
      usual_arith_conversion(TA, TB, Type),
      type_class(Type, Class),
      int_info(Type, _, Sign) },
    convert(VA, Type, v(A, _)),
    convert(VB, Type, v(B, _)),
    { Sign == signed -> Cmp = SignedCmp ; Cmp = UnsignedCmp },
    ins(w, cmp(Cmp, Class), [A, B], V).
int_binary(Op, VA, VB, v(V, Type)) -->
    { VA = v(_, TA),
      VB = v(_, TB),
      usual_arith_conversion(TA, TB, Type),
      type_class(Type, Class),
      int_info(Type, _, Sign),
      arith_op(Op, Sign, IOp) },
    convert(VA, Type, v(A, _)),
    convert(VB, Type, v(B, _)),
    ins(Class, IOp, [A, B], V).

% cmp_op(Op, SignedCmp, UnsignedCmp)
cmp_op(eq, eq, eq).
cmp_op(ne, ne, ne).
cmp_op(lt, slt, ult).
cmp_op(gt, sgt, ugt).
cmp_op(le, sle, ule).
cmp_op(ge, sge, uge).

% arith_op(Op, Sign, IROp)
arith_op(add, _, add).
arith_op(sub, _, sub).
arith_op(mul, _, mul).
arith_op(div, signed, div).
arith_op(div, unsigned, udiv).
arith_op(mod, signed, rem).
arith_op(mod, unsigned, urem).
arith_op(and, _, and).
arith_op(or, _, or).
arith_op(xor, _, xor).

% P + I or P - I: I scaled by the element size.
ptr_offset(Op, v(P, PtrType), ElemType, VI, Ctx, v(R, PtrType)) -->
    { PtrType = ptr(ElemType) },
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(size_align(ElemType, Env, Size, _), bad(Why),
            sema_error(Loc, 'pointer arithmetic on ~w (~w)', [ElemType, Why])) },
    convert(VI, long, v(I, _)),
    (   { I = c(N) } -> { Off is N * Size, OffV = c(Off) }
    ;   { Size =:= 1 } -> { OffV = I }
    ;   ins(l, mul, [I, c(Size)], OffV)
    ),
    ins(p, Op, [P, OffV], R).

ptr_diff(v(A, _), v(B, _), ElemType, Ctx, v(V, long)) -->
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(size_align(ElemType, Env, Size, _), bad(Why),
            sema_error(Loc, 'pointer subtraction on ~w (~w)', [ElemType, Why])) },
    ins(l, ptoi, [A], IA),
    ins(l, ptoi, [B], IB),
    ins(l, sub, [IA, IB], Diff),
    (   { Size =:= 1 } -> { V = Diff }
    ;   ins(l, div, [Diff, c(Size)], V)
    ).

ptr_compare(Op, VA, VB, v(V, int)) -->
    convert(VA, ulong, v(A, _)),
    convert(VB, ulong, v(B, _)),
    { cmp_op(Op, _, Cmp) },
    ins(w, cmp(Cmp, l), [A, B], V).

% && and ||: a phi of 0/1 over the short-circuit edges.
logical(Op, A, B, Ctx, v(V, int)) -->
    rval(A, Ctx, VA), truth(VA, Ctx, WA), here(LA),
    label(LRight), label(LJoin),
    {   Op == land -> Jump = jnz(WA, LRight, LJoin), Short = 0
    ;   Jump = jnz(WA, LJoin, LRight), Short = 1
    },
    term(Jump),
    start(LRight), rval(B, Ctx, VB), truth(VB, Ctx, WB),
    ins(w, cmp(ne, w), [WB, c(0)], NB),
    here(LB), term(jmp(LJoin)),
    fresh(V),
    start_phi(LJoin, [phi(V, w, [LA-c(Short), LB-NB])]).

% GNU c ?: b: c is evaluated once, and is the result if nonzero.
gnu_conditional(Cond, B, Ctx, R) -->
    rval(Cond, Ctx, VC), probe_rval(B, Ctx, VB0),
    { VC = v(_, TC), VB0 = v(_, TB), ctx_loc(Ctx, Loc),
      cond_type(TC, VC, TB, VB0, Type, Loc) },
    truth(VC, Ctx, W),
    label(LA), label(LB), label(LJoin),
    term(jnz(W, LA, LB)),
    start(LA), arm_convert(VC, Type, Ctx, VA1), here(LA1), term(jmp(LJoin)),
    start(LB), rval(B, Ctx, VB), arm_convert(VB, Type, Ctx, VB1), here(LB1),
    term(jmp(LJoin)),
    join_arms(Type, LJoin, LA1-VA1, LB1-VB1, R).

conditional(Cond, A, B, Ctx, R) -->
    probe_rval(A, Ctx, VA0), probe_rval(B, Ctx, VB0),
    { VA0 = v(_, TA), VB0 = v(_, TB), ctx_loc(Ctx, Loc),
      cond_type(TA, VA0, TB, VB0, Type, Loc) },
    label(LA), label(LB), label(LJoin),
    cond_jump(Cond, Ctx, LA, LB),
    start(LA), rval(A, Ctx, VA), arm_convert(VA, Type, Ctx, VA1), here(LA1),
    term(jmp(LJoin)),
    start(LB), rval(B, Ctx, VB), arm_convert(VB, Type, Ctx, VB1), here(LB1),
    term(jmp(LJoin)),
    join_arms(Type, LJoin, LA1-VA1, LB1-VB1, R).

% join_arms(Type, LJoin, LA-VA, LB-VB, R): the ?: result, a phi at LJoin.
join_arms(Type, LJoin, LA-VA, LB-VB, R) -->
    (   { Type == void } -> start(LJoin), { R = v(c(0), void) }
    ;   { su(Type) -> Class = p ; type_class(Type, Class) },
        fresh(V),
        start_phi(LJoin, [phi(V, Class, [LA-VA, LB-VB])]),
        { R = v(V, Type) }
    ).

arm_convert(Value0, void, _, c(0)) --> !, { Value0 = v(_, _) }.
arm_convert(v(Addr, Type), Type, _, Addr) --> { su(Type) }, !.
arm_convert(Value0, Type, Ctx, V) -->
    convert_checked(Value0, Type, Ctx, v(V, _)).

% probe_rval(Expr, Ctx, R): Expr's decayed value term from a throwaway
% lowering; only its type (and whether it is a constant) is used.
probe_rval(Expr, Ctx, R, State, State) :-
    rval(Expr, Ctx, R, State, _).

% struct_expr(Expr, Ctx, Type): Expr is an expression of struct or union
% type Type.
struct_expr(Expr, Ctx, Type, State, State) :-
    catch(rval(Expr, Ctx, v(_, Type1), State, _), nanofil_error(_), fail),
    Type1 == Type.

% The type of c ? a : b.
cond_type(TA, _, TB, _, Type, _) :-
    int_type(TA), int_type(TB), !,
    usual_arith_conversion(TA, TB, Type).
cond_type(void, _, void, _, void, _) :- !.
cond_type(Type, _, Type, _, Type, _) :- su(Type), !.
cond_type(ptr(P), _, ptr(_), _, ptr(P), _) :- !.
cond_type(ptr(P), _, TB, v(c(0), _), ptr(P), _) :- int_type(TB), !.
cond_type(TA, v(c(0), _), ptr(P), _, ptr(P), _) :- int_type(TA), !.
cond_type(TA, _, TB, _, _, Loc) :-
    sema_error(Loc, 'incompatible ?: operands ~w and ~w', [TA, TB]).

%% Assignment

assignment(Op, A, B, Ctx, R) -->
    { ctx_loc(Ctx, Loc) },
    obj(A, Ctx, LV),
    {   LV = lv(P, Type) -> true
    ;   sema_error(Loc, 'assignment to a non-lvalue', [])
    },
    (   { Op == '=' } -> rval(B, Ctx, Value0)
    ;   { compound_op(Op, BinOp) },
        load_typed(Type, P, Ctx, Cur),
        rval(B, Ctx, VB),
        binary(BinOp, v(Cur, Type), VB, Ctx, Value0)
    ),
    assign_convert(Value0, Type, Loc, R),
    { R = v(V, _) },
    store_typed(Type, V, P).

compound_op('*=', mul).
compound_op('/=', div).
compound_op('%=', mod).
compound_op('+=', add).
compound_op('-=', sub).
compound_op('<<=', shl).
compound_op('>>=', shr).
compound_op('&=', and).
compound_op('^=', xor).
compound_op('|=', or).

incdec(Op, A, Ctx, R) -->
    { ctx_loc(Ctx, Loc) },
    obj(A, Ctx, LV),
    {   LV = lv(P, Type), scalar_type(Type) -> true
    ;   sema_error(Loc, '~w of a non-scalar lvalue', [Op])
    },
    load_typed(Type, P, Ctx, Cur),
    { memberchk(Op, [preinc, postinc]) -> BinOp = add ; BinOp = sub },
    binary(BinOp, v(Cur, Type), v(c(1), int), Ctx, Value0),
    convert(Value0, Type, v(New, _)),
    store_typed(Type, New, P),
    { memberchk(Op, [preinc, predec]) -> R = v(New, Type) ; R = v(Cur, Type) }.

%% Calls

lower_call(Func, Args, Ctx, R) -->
    { ctx_loc(Ctx, Loc) },
    obj(Func, Ctx, FD0),
    (   { FD0 = fd(_, _) } -> { FD = FD0 }
    ;   decay(FD0, Ctx, v(FV, Type)),
        (   { Type = ptr(FuncType), FuncType = func(_, _, _) }
        ->  callee_temp(FV, Callee0),
            { FD = fd(Callee0, FuncType) }
        ;   { sema_error(Loc, 'called object is not a function', []) }
        )
    ),
    { FD = fd(Callee, func(RetType, ParamTypes0, _)),
      ( Callee = glo(Sym) -> true ; Sym = 'function pointer' ) },
    (   { ParamTypes0 == unspecified } -> { ParamTypes = [] }
    ;   { ParamTypes = ParamTypes0 }
    ),
    { length(ParamTypes, NParams),
      length(Args, NArgs),
      (   NArgs < NParams
      ->  sema_error(Loc, 'too few arguments to ~w', [Sym])
      ;   true
      ),
      (   NArgs > NParams, ParamTypes0 \== unspecified,
          FD = fd(_, func(_, _, fixed))
      ->  sema_error(Loc, 'too many arguments to ~w', [Sym])
      ;   true
      ) },
    call_args(Args, ParamTypes, Ctx, IRArgs),
    (   { su(RetType) } -> struct_call(RetType, Callee, IRArgs, Loc, R)
    ;   { RetType == void }
    ->  emit(call(void, Callee, IRArgs)),
        { R = v(c(0), void) }
    ;   { type_class(RetType, Class) }
    ->  fresh(D),
        emit(call(to(D, Class), Callee, IRArgs)),
        normalize(RetType, D, V),
        { R = v(V, RetType) }
    ;   { sema_error(Loc, 'calls returning ~w are not supported yet',
                     [RetType]) }
    ).

% call_args(Args, ParamTypes, Ctx, IRArgs): a struct argument goes as one
% word per eightbyte; arguments past the prototype get the default
% promotions.
call_args([], _, _, []) --> [].
call_args([Arg|Args], [ParamType|ParamTypes], Ctx, IRArgs) -->
    { su(ParamType) }, !,
    { ctx_loc(Ctx, Loc) },
    rval(Arg, Ctx, Value0),
    assign_convert(Value0, ParamType, Loc, v(Src, _)),
    env(Env),
    { arg_words(ParamType, Env, Loc, Ebs) },
    load_words(Ebs, Src, Words),
    { findall(arg(Class, W),
              ( nth0(I, Ebs, eb(_, _, Class)), nth0(I, Words, W) ),
              IRArgs0) },
    call_args(Args, ParamTypes, Ctx, IRArgs1),
    { append(IRArgs0, IRArgs1, IRArgs) }.
call_args([Arg|Args], ParamTypes0, Ctx, [arg(Class, V)|IRArgs]) -->
    { ctx_loc(Ctx, Loc) },
    rval(Arg, Ctx, Value0),
    (   { ParamTypes0 = [ParamType|ParamTypes] }
    ->  assign_convert(Value0, ParamType, Loc, v(V, Type))
    ;   { ParamTypes = [], Value0 = v(_, Type0) },
        (   { int_type(Type0) }
        ->  { integer_promotion(Type0, Type) },
            convert(Value0, Type, v(V, _))
        ;   { Type0 = ptr(_) } -> { Value0 = v(V, Type) }
        ;   { sema_error(Loc,
                'passing ~w to a variadic or unprototyped function is not supported',
                [Type0]) }
        )
    ),
    { type_class(Type, Class) },
    call_args(Args, ParamTypes, Ctx, IRArgs).

% A call returning a struct: its words land in a fresh local, or the
% callee writes the local through the sret pointer.
struct_call(RetType, Callee, Args, Loc, v(Tmp, RetType)) -->
    env(Env),
    { ret_shape(RetType, Env, Loc, Shape) },
    local_slot(RetType, Tmp),
    (   { Shape == sret }
    ->  emit(call(void, Callee, [arg(p, Tmp)|Args]))
    ;   { Shape = words([eb(_, _, Class)]) }
    ->  fresh(D),
        emit(call(to(D, Class), Callee, Args)),
        { Shape = words(Ebs) },
        store_words(Ebs, [D], Tmp)
    ;   { Shape = words(Ebs) },
        fresh(D1), fresh(D2),
        { Ebs = [eb(_, _, Class1), eb(_, _, Class2)] },
        emit(call(tuple([to(D1, Class1), to(D2, Class2)]), Callee, Args)),
        store_words(Ebs, [D1, D2], Tmp)
    ).

return_struct(RetType, Addr, Loc) -->
    env(Env),
    { ret_shape(RetType, Env, Loc, Shape) },
    (   { Shape == sret }
    ->  env(Env1),
        { lookup_ordinary(Env1, '%sret', sret(P)) },
        copy_object(RetType, Addr, P),
        term(ret)
    ;   { Shape = words(Ebs) },
        load_words(Ebs, Addr, Words),
        (   { Words = [W] } -> term(ret(W))
        ;   term(rets(Words))
        )
    ).

% A narrow result is re-extended: nothing guarantees the callee did.
normalize(Type, V0, V) -->
    (   { int_info(Type, Size, Sign), Size < 4 }
    ->  { narrow_ext(Size, Sign, Op) },
        ins(w, ext(Op), [V0], V)
    ;   { Type == bool } -> ins(w, ext(ub), [V0], V)
    ;   { V = V0 }
    ).

%% Struct values

/* A struct or union rvalue is v(Addr, T): Addr points at storage holding
   the value, a variable's or a temporary's. Copies, arguments and
   returns go an eightbyte at a time (eb(Offset, Bytes, Class)): class p
   if a pointer starts there, so its capability is copied with loadp and
   storep, else l, with a short last eightbyte moved in 4-, 2- and 1-byte
   pieces. A value of at most 16 bytes is passed as one word per
   eightbyte, as clang does; a larger return goes through an sret
   pointer. */
su(struct(_)).
su(union(_)).

eightbytes(Type, Env, Loc, Ebs) :-
    catch(size_align(Type, Env, Size, _), bad(Why),
          sema_error(Loc, '~w has an unsupported type (~w)', [Type, Why])),
    ptr_offsets(Type, Env, 0, PtrOffs0, []),
    sort(PtrOffs0, PtrOffs),
    Last is (Size + 7) // 8 - 1,
    findall(eb(Off, N, Class),
            (   between(0, Last, I),
                Off is 8 * I,
                N is min(8, Size - Off),
                ( memberchk(Off, PtrOffs) -> Class = p ; Class = l )
            ),
            Ebs).

% ptr_offsets(Type, Env, Base, Offs0, Offs): where Type holds pointers,
% as a difference list.
ptr_offsets(ptr(_), _, Base, [Base|Offs], Offs) :- !.
ptr_offsets(array(ElemType, N), Env, Base, Offs0, Offs) :-
    integer(N), !,
    ptr_offsets(ElemType, Env, 0, ElemOffs, []),
    (   ElemOffs == [] -> Offs0 = Offs
    ;   size_align(ElemType, Env, Size, _),
        Last is N - 1,
        findall(I, between(0, Last, I), Indices),
        foldl(elem_ptrs(ElemType, Env, Base, Size), Indices, Offs0, Offs)
    ).
ptr_offsets(SU, Env, Base, Offs0, Offs) :-
    su(SU), !,
    SU =.. [_, Id],
    env_defs(Env, Defs),
    get_assoc(Id, Defs, def(_, Members, _, _)),
    foldl(member_ptrs(Env, Base), Members, Offs0, Offs).
ptr_offsets(_, _, _, Offs, Offs).

elem_ptrs(ElemType, Env, Base, Size, I, Offs0, Offs) :-
    Base1 is Base + I * Size,
    ptr_offsets(ElemType, Env, Base1, Offs0, Offs).

member_ptrs(Env, Base, m(_, Type, Off), Offs0, Offs) :-
    Base1 is Base + Off,
    ptr_offsets(Type, Env, Base1, Offs0, Offs).

arg_words(Type, Env, Loc, Ebs) :-
    size_align(Type, Env, Size, _),
    (   Size > 16
    ->  sema_error(Loc, 'passing a ~w of ~w bytes by value is not supported yet',
                   [Type, Size])
    ;   eightbytes(Type, Env, Loc, Ebs)
    ).

% ret_shape(Type, Env, Loc, Shape): sret, or words(Eightbytes).
ret_shape(Type, Env, Loc, Shape) :-
    size_align(Type, Env, Size, _),
    (   Size > 16 -> Shape = sret
    ;   eightbytes(Type, Env, Loc, Ebs),
        Shape = words(Ebs)
    ).

copy_object(Type, Src, Dst) -->
    env(Env),
    { eightbytes(Type, Env, unknown, Ebs) },
    copy_ebs(Ebs, Src, Dst).

copy_ebs([], _, _) --> [].
copy_ebs([eb(Off, N, Class)|Ebs], Src, Dst) -->
    offset(Src, Off, S),
    offset(Dst, Off, D),
    (   { Class == p }
    ->  ins(p, load(p), [S], V),
        emit(store(p, V, D))
    ;   { pieces(N, 0, Pieces) },
        copy_pieces(Pieces, S, D)
    ),
    copy_ebs(Ebs, Src, Dst).

% pieces(N, Off, Pieces): N bytes from offset Off as
% p(Offset, Bytes, Load, Store).
pieces(0, _, []) :- !.
pieces(N, Off, [p(Off, Bytes, Load, Store)|Pieces]) :-
    member(Bytes-Load-Store, [8-l-l, 4-uw-w, 2-uh-h, 1-ub-b]),
    Bytes =< N, !,
    N1 is N - Bytes,
    Off1 is Off + Bytes,
    pieces(N1, Off1, Pieces).

copy_pieces([], _, _) --> [].
copy_pieces([p(Off, _, Load, Store)|Pieces], Src, Dst) -->
    offset(Src, Off, S),
    offset(Dst, Off, D),
    ins(l, load(Load), [S], V),
    emit(store(Store, V, D)),
    copy_pieces(Pieces, Src, Dst).

% The words of the value at Addr, one per eightbyte.
load_words([], _, []) --> [].
load_words([eb(Off, N, Class)|Ebs], Addr, [W|Words]) -->
    offset(Addr, Off, P),
    (   { Class == p } -> ins(p, load(p), [P], W)
    ;   { pieces(N, 0, Pieces) },
        load_pieces(Pieces, P, none, W)
    ),
    load_words(Ebs, Addr, Words).

% load_pieces(Pieces, P, Acc, W): or the shifted pieces together.
load_pieces([], _, W, W) --> [].
load_pieces([p(Off, _, Load, _)|Pieces], P, Acc0, W) -->
    offset(P, Off, P1),
    ins(l, load(Load), [P1], Piece0),
    (   { Off =:= 0 } -> { Piece = Piece0 }
    ;   { Shift is 8 * Off },
        ins(l, shl, [Piece0, c(Shift)], Piece)
    ),
    (   { Acc0 == none } -> { Acc = Piece }
    ;   ins(l, or, [Acc0, Piece], Acc)
    ),
    load_pieces(Pieces, P, Acc, W).

% Store words, one per eightbyte, into the object at Addr.
store_words([], [], _) --> [].
store_words([eb(Off, N, Class)|Ebs], [W|Words], Addr) -->
    offset(Addr, Off, P),
    (   { Class == p } -> emit(store(p, W, P))
    ;   { pieces(N, 0, Pieces) },
        store_pieces(Pieces, W, P)
    ),
    store_words(Ebs, Words, Addr).

store_pieces([], _, _) --> [].
store_pieces([p(Off, _, _, Store)|Pieces], W, P) -->
    offset(P, Off, P1),
    (   { Off =:= 0 } -> { Piece = W }
    ;   { Shift is 8 * Off },
        ins(l, shr, [W, c(Shift)], Piece)
    ),
    emit(store(Store, Piece, P1)),
    store_pieces(Pieces, W, P).

%% Static initializers

/* static_items(+Type, +Init, +Loc, +Env0, -Env, -Items): the data items
   of a global of type Type. Chunks chunk(Offset, Bytes, Item) are
   collected, a later one replacing an earlier one at the same offset,
   then the gaps are zero-filled. A pointer is item(p, sym(S, Off));
   string literals in initializers become data of their own. The static_*
   predicates thread Env-Chunks, the chunks reversed. */
static_items(Type, Init, Loc, Env0, Env, Items) :-
    size_align(Type, Env0, Size, _),
    (   Init == none -> Env = Env0, Chunks = []
    ;   static_init(0, Type, Init, Loc, Env0-[], Env-Chunks0),
        reverse(Chunks0, Chunks)
    ),
    empty_assoc(ByOffset0),
    foldl(put_chunk, Chunks, ByOffset0, ByOffset),
    assoc_to_values(ByOffset, Sorted),
    fill_items(Sorted, 0, Size, Loc, Items).

put_chunk(chunk(Off, N, Item), ByOffset0, ByOffset) :-
    put_assoc(Off, ByOffset0, chunk(Off, N, Item), ByOffset).

% fill_items(Chunks, Pos, Size, Loc, Items): the chunks with zero(N) gaps.
fill_items([], Pos, Size, _, Zeros) :-
    (   Pos < Size -> N is Size - Pos, Zeros = [zero(N)]
    ;   Zeros = []
    ).
fill_items([chunk(Off, N, Item)|Chunks], Pos, Size, Loc, Items) :-
    (   Off < Pos -> sema_error(Loc, 'overlapping initializers', [])
    ;   true
    ),
    (   Off > Pos -> Gap is Off - Pos, Items = [zero(Gap), Item|Items1]
    ;   Items = [Item|Items1]
    ),
    Pos1 is Off + N,
    fill_items(Chunks, Pos1, Size, Loc, Items1).

int_chunk(Off, Type, V, chunk(Off, N, item(Width, c(U)))) :-
    int_info(Type, N, _),
    memberchk(N-Width, [1-b, 2-h, 4-w, 8-l]),
    convert_int(V, Type, U).

% static_init(Off, Type, Init, Loc, S0, S): the chunks of Init for an
% object of type Type at offset Off.
static_init(Off, Type, list(Entries), Loc, S0, S) :- !,
    (   aggregate(Type)
    ->  static_agg(Off, Type, Entries, Rest, Loc, S0, S),
        (   Rest == [] -> true
        ;   sema_error(Loc, 'excess initializers', [])
        )
    ;   Entries = [entry([], V)|_] -> static_init(Off, Type, V, Loc, S0, S)
    ;   S = S0
    ).
static_init(Off, array(ElemType, N), Str, Loc, Env-Chunks0, Env-Chunks) :-
    str_elems(Str, ElemType, Bytes), !,
    length(Bytes, NBytes),
    (   NBytes > N -> sema_error(Loc, 'string initializer is too long', [])
    ;   true
    ),
    int_info(ElemType, Size, _),
    findall(Chunk,
            (   nth0(K, Bytes, Byte),
                ByteOff is Off + K * Size,
                int_chunk(ByteOff, ElemType, Byte, Chunk)
            ),
            New),
    reverse(New, RevNew),
    append(RevNew, Chunks0, Chunks).
static_init(Off, Type, Expr, Loc, Env-Chunks, Env-[Chunk|Chunks]) :-
    int_type(Type), !,
    (   catch(const_value(Expr, Env, V, _), not_constant, fail) -> true
    ;   sema_error(Loc, 'initializer is not a constant', [])
    ),
    int_chunk(Off, Type, V, Chunk).
static_init(Off, ptr(_), Expr, Loc, Env0-Chunks, Env-[Chunk|Chunks]) :- !,
    addr_const(Expr, Loc, Env0, Env, R),
    (   R = sym(Sym, SymOff, _)
    ->  Chunk = chunk(Off, 8, item(p, sym(Sym, SymOff)))
    ;   Chunk = chunk(Off, 8, item(l, c(0)))
    ).
static_init(_, Type, _, Loc, _, _) :-
    sema_error(Loc, 'cannot statically initialize a ~w', [Type]).

% static_agg, static_slots and static_one follow init_agg, init_slots
% and init_one.
static_agg(Off, Type, Entries0, Entries, Loc, Env0-Chunks0, S) :-
    aggregate_slots(Type, Env0, Slots),
    static_slots(Slots, 0, Off, Entries0, Entries, Loc, Env0-Chunks0, S).

static_slots(_, _, _, [], [], _, S, S) :- !.
static_slots(Slots, _, Off, [entry([Desig|Desigs], V)|Entries0], Entries, Loc,
             S0, S) :- !,
    S0 = Env0-_,
    designated(Desig, Slots, Index, Env0, ctx(_, _, _, _, Loc)),
    nth0(Index, Slots, slot(_, SlotOff, Type)),
    Off1 is Off + SlotOff,
    (   Desigs == []
    ->  static_one(Off1, Type, V, Entries0, Entries1, Loc, S0, S1)
    ;   static_agg(Off1, Type, [entry(Desigs, V)], [], Loc, S0, S1),
        Entries1 = Entries0
    ),
    Index1 is Index + 1,
    static_slots(Slots, Index1, Off, Entries1, Entries, Loc, S1, S).
static_slots(Slots, Index, Off, Entries0, Entries, Loc, S0, S) :-
    (   nth0(Index, Slots, slot(_, SlotOff, Type))
    ->  Entries0 = [entry([], V)|Entries1],
        Off1 is Off + SlotOff,
        static_one(Off1, Type, V, Entries1, Entries2, Loc, S0, S1),
        Index1 is Index + 1,
        static_slots(Slots, Index1, Off, Entries2, Entries, Loc, S1, S)
    ;   Entries = Entries0, S = S0
    ).

static_one(Off, Type, V, Entries0, Entries, Loc, S0, S) :-
    (   (   V = list(_)
        ;   \+ aggregate(Type)
        ;   Type = array(ElemType, _), str_elems(V, ElemType, _)
        )
    ->  static_init(Off, Type, V, Loc, S0, S),
        Entries = Entries0
    ;   undesignated(Entries0, Pre, Post),
        static_agg(Off, Type, [entry([], V)|Pre], Rest, Loc, S0, S),
        append(Rest, Post, Entries)
    ).

/* addr_const(+Expr, +Loc, +Env0, -Env, -R): an address constant,
   sym(Symbol, Offset, PointerType), or null. */
addr_const(str(Bytes), _, Env0, Env, sym(Sym, 0, ptr(char))) :- !,
    new_literal(Bytes, Sym, Env0, Env).
addr_const(wstr(WideType, Values), _, Env0, Env, sym(Sym, 0, ptr(WideType))) :- !,
    new_literal(w(WideType, Values), Sym, Env0, Env).
addr_const(complit(TypeName, Init), Loc, Env0, Env, sym(Sym, 0, ptr(ElemType))) :-
    type_name(TypeName, Type, Env0, Loc),
    Type = array(ElemType, _), !,
    new_complit(Type, Init, Loc, Sym, Env0, Env).
addr_const(id(Name), _, Env, Env, R) :-
    lookup_ordinary(Env, Name, gvar(array(ElemType, _), Sym, _, _)), !,
    R = sym(Sym, 0, ptr(ElemType)).
addr_const(id(Name), _, Env, Env, sym(Sym, 0, ptr(Type))) :-
    lookup_ordinary(Env, Name, fn(Type, Sym, _)), !.
addr_const(un(addr, Expr), Loc, Env0, Env, R) :- !,
    (   Expr = id(Name), lookup_ordinary(Env0, Name, fn(Type, Sym, _))
    ->  Env = Env0,
        R = sym(Sym, 0, ptr(Type))
    ;   lvalue_const(Expr, Loc, Env0, Env, sym(Sym, Off, Type)),
        R = sym(Sym, Off, ptr(Type))
    ).
addr_const(cast(TypeName, Expr), Loc, Env0, Env, R) :- !,
    type_name(TypeName, Type, Env0, Loc),
    (   Type = ptr(_)
    ->  addr_const(Expr, Loc, Env0, Env, R0),
        (   R0 = sym(Sym, Off, _) -> R = sym(Sym, Off, Type)
        ;   R = R0
        )
    ;   sema_error(Loc, 'initializer is not a constant', [])
    ).
addr_const(bin(Op, Ptr, Index), Loc, Env0, Env, R) :-
    memberchk(Op, [add, sub]),
    catch(const_value(Index, Env0, K, _), not_constant, fail), !,
    addr_const(Ptr, Loc, Env0, Env, R0),
    offset_const(Op, R0, K, Env, Loc, R).
addr_const(bin(add, Index, Ptr), Loc, Env0, Env, R) :-
    catch(const_value(Index, Env0, K, _), not_constant, fail), !,
    addr_const(Ptr, Loc, Env0, Env, R0),
    offset_const(add, R0, K, Env, Loc, R).
addr_const(Expr, Loc, Env, Env, null) :-
    (   catch(const_value(Expr, Env, 0, _), not_constant, fail) -> true
    ;   sema_error(Loc, 'initializer is not an address constant', [])
    ).

% offset_const(Op, R0, K, Env, Loc, R): R0 plus or minus K elements.
offset_const(Op, sym(Sym, Off0, ptr(ElemType)), K, Env, Loc,
             sym(Sym, Off, ptr(ElemType))) :- !,
    catch(size_align(ElemType, Env, Size, _), bad(Why),
          sema_error(Loc, 'pointer arithmetic on ~w (~w)', [ElemType, Why])),
    (   Op == add -> Off is Off0 + K * Size
    ;   Off is Off0 - K * Size
    ).
offset_const(_, _, _, _, Loc, _) :-
    sema_error(Loc, 'initializer is not an address constant', []).

% lvalue_const(+Expr, +Loc, +Env0, -Env, -R): the address of a static
% lvalue, sym(Symbol, Offset, ObjectType).
lvalue_const(id(Name), Loc, Env, Env, sym(Sym, 0, Type)) :- !,
    (   lookup_ordinary(Env, Name, gvar(Type, Sym, _, _)) -> true
    ;   sema_error(Loc, '~w is not a global', [Name])
    ).
lvalue_const(complit(TypeName, Init), Loc, Env0, Env, sym(Sym, 0, Type)) :- !,
    type_name(TypeName, Type0, Env0, Loc),
    new_complit(Type0, Init, Loc, Sym, Env0, Env),
    env_defs(Env, Defs),
    get_assoc(gdef(Sym), Defs, g(Type, _, _, _)).
lvalue_const(wstr(WideType, Values), _, Env0, Env,
             sym(Sym, 0, array(WideType, N))) :- !,
    new_literal(w(WideType, Values), Sym, Env0, Env),
    length(Values, N0),
    N is N0 + 1.
lvalue_const(str(Bytes), _, Env0, Env, sym(Sym, 0, array(char, N))) :- !,
    new_literal(Bytes, Sym, Env0, Env),
    length(Bytes, N0),
    N is N0 + 1.
lvalue_const(index(Array, Index), Loc, Env0, Env, R) :- !,
    lvalue_const(un(deref, bin(add, Array, Index)), Loc, Env0, Env, R).
lvalue_const(un(deref, Ptr), Loc, Env0, Env, sym(Sym, Off, Type)) :- !,
    addr_const(Ptr, Loc, Env0, Env, R0),
    (   R0 = sym(Sym, Off, ptr(Type)) -> true
    ;   sema_error(Loc, 'initializer is not an address constant', [])
    ).
lvalue_const(member(Expr, Field), Loc, Env0, Env, sym(Sym, Off, Type)) :- !,
    lvalue_const(Expr, Loc, Env0, Env, sym(Sym, Off0, SUType)),
    member_off(SUType, Field, Env, Loc, Type, MemberOff),
    Off is Off0 + MemberOff.
lvalue_const(arrow(Ptr, Field), Loc, Env0, Env, sym(Sym, Off, Type)) :- !,
    addr_const(Ptr, Loc, Env0, Env, R0),
    (   R0 = sym(Sym, Off0, ptr(SUType)) -> true
    ;   sema_error(Loc, 'initializer is not an address constant', [])
    ),
    member_off(SUType, Field, Env, Loc, Type, MemberOff),
    Off is Off0 + MemberOff.
lvalue_const(_, Loc, _, _, _) :-
    sema_error(Loc, 'initializer is not an address constant', []).

member_off(SUType, Field, Env, Loc, Type, Off) :-
    (   ( SUType = struct(_) ; SUType = union(_) ),
        find_member(SUType, Field, Env, Type, Off)
    ->  true
    ;   sema_error(Loc, 'no member named ~w', [Field])
    ).

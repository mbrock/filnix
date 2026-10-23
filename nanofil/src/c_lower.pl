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

    The lowering nonterminals describe a one-element list holding the
    state, accessed through the semicontext nonterminals state//1 and
    state//2 and called with phrase/3 at the entry points:
      st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)
      Env     the c_types environment e(Ords, Tags, Defs, Next)
      Cur     cur(Label, Phis), or none after a jump (dead code then
              opens an unreachable block)
      Insts, Blocks, Allocs  reversed
      N       the counter for fresh temporaries and labels
      Labels  assoc from C goto labels to IR labels
      Cases   the enclosing switch's case(Value, Label) and default(Label)
    The context argument Ctx = ctx(Function, ReturnType, Break, Continue,
    Loc); Break and Continue are some(Label), or none outside a loop or
    switch.

    Besides what c_types keeps there, the environment's Defs hold
    gdef(Symbol) global definitions, lit(Symbol) string literals and
    deferred(Symbol) static inline functions, and its Next numbers
    literals and compound literals as well as struct ids.

    Variable conventions: State0 and State are st/8 terms, Env0
    ... Env the environment; Ctx is the context and Loc a source
    location; R is a v/lv/fd value term, Value0 one before conversion,
    V an IR value; L-prefixed names are IR labels; Ebs are eightbytes
    eb(Offset, Bytes, Class); S0 ... S thread Env-Chunks pairs in the
    static initializer predicates.
*/
:- module(c_lower, [c_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(dcgs)).
:- use_module(c_types).
:- use_module(ir, [op_kind/2]).

%! c_module(+Items, -Module)
%
%  Module is the IR module of the top-level Items from c_parse:
%  module(Funcs) with the functions followed by the data of every
%  global and string literal. Throws a semantic error for C that
%  nanofil cannot lower.
c_module(Items, module(Funcs)) :-
    empty_env(Env0),
    findall(Name, external_inline_declaration(Items, Name), Names0),
    sort(Names0, ExternalNames),
    foldl(top_item(ExternalNames), Items, Funcss, Env0, Env),
    append(Funcss, Funcs0),
    with_used_inlines(Funcs0, Env, Funcs).

% C99 6.7.4: an inline body is an external definition unless ALL
% file-scope declarations are inline without extern. Inspect the whole
% translation unit: even a declaration after the body changes emission.
external_inline_declaration(Items, Name) :-
    member(Item, Items),
    (   Item = decl(_, Specs, Inits),
        member(init(dcl(some(Name), _, _), _), Inits)
    ;   Item = fundef(_, Specs, dcl(some(Name), _, _), _)
    ),
    \+ memberchk(storage(typedef), Specs),
    ( memberchk(storage(extern), Specs) ; \+ memberchk(fspec(inline), Specs) ).

% GNU inline reverses the C99 rule: an extern inline body is never the
% external definition, while a plain inline body is. The parser retains
% both spellings in the balanced tokens of specifier and suffix attrs.
external_inline_body(Specs, Storage, Name, ExternalNames) :-
    (   member(attr([group(Attrs)]), Specs),
        member(id(Attr), Attrs),
        memberchk(Attr, [gnu_inline, '__gnu_inline__'])
    ->  Storage \== extern
    ;   memberchk(Name, ExternalNames)
    ).

/* with_used_inlines(+Funcs0, +Env0, -Items): Items is Funcs0, then
   every deferred static inline function they refer to, directly or
   through one another, then the global data. A static inline function
   is lowered only if something refers to it, as clang emits it only
   then; headers are full of ones nanofil cannot lower. Lowering one can
   refer to more, so this iterates until no new symbol turns up. */
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

% item_ref(+Items, -Sym): some function or data item of Items refers to
% symbol Sym (nondet, with repeats).
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

% lower_inline(+Sym, -Func, +Env0, -Env): Func is the deferred inline
% function Sym, lowered in the scope it was defined in.
lower_inline(Sym, Func, Env0, Env) :-
    env_defs(Env0, Defs),
    get_assoc(deferred(Sym), Defs, df(Loc, Name, Type, DclType, Body, Scope)),
    env_restore(Scope, Env0, Env1),
    function(Loc, Name, Type, DclType, Body, Env1, Env2, Func),
    env_scope(Env0, Scope0, _),
    env_restore(Scope0, Env2, Env).

%% Environment

env_defs(e(_, _, Defs, _), Defs).

% put_def(+Key, +Value, +Env0, -Env): Env is Env0 with Key defined as
% Value.
put_def(Key, Value, e(Ords, Tags, Defs0, Next), e(Ords, Tags, Defs, Next)) :-
    put_assoc(Key, Defs0, Value, Defs).

% next_id(-Id, +Env0, -Env): Id is Env0's next number, which Env has
% moved past.
next_id(Id, e(Ords, Tags, Defs, Id), e(Ords, Tags, Defs, Next)) :-
    Next is Id + 1.

%% Top level

% top_item(+ExternalNames, +Item, -Funcs, +Env0, -Env): Funcs are the IR
% functions a top-level item defines now (a static inline is deferred).
top_item(_, static_assert(Loc, Expr, _), [], Env, Env) :- !,
    static_assert(Loc, Expr, Env).
top_item(_, decl(Loc, Specs, Inits), [], Env0, Env) :- !,
    catch(decl_types(Specs, Inits, Decls, Env0, Env1), not_constant,
          sema_error(Loc, 'array size is not a constant', [])),
    foldl(global_decl(Loc), Decls, Env1, Env).
top_item(ExternalNames, fundef(Loc, Specs, dcl(some(Name), DclType, Asm), Body), Funcs,
         Env0, Env) :-
    decl_types(Specs, [init(dcl(some(Name), DclType, Asm), none)],
               [d(_, Type, Storage, _, _)], Env0, Env1),
    global_decl(Loc, d(Name, Type, Storage, Asm, none), Env1, Env2),
    (   memberchk(fspec(inline), Specs),
        (   Storage == static
        ;   \+ external_inline_body(Specs, Storage, Name, ExternalNames)
        )
    ->  Funcs = [],
        (   Storage == static
        ->  lookup_ordinary(Env2, Name, fn(_, Sym, _)),
            env_scope(Env2, Scope, _),
            put_def(deferred(Sym), df(Loc, Name, Type, DclType, Body, Scope),
                    Env2, Env)
        ;   Env = Env2      % GNU extern inline or a C99 inline-only definition
        )
    ;   Funcs = [Func],
        function(Loc, Name, Type, DclType, Body, Env2, Env, Func)
    ).

% static_assert(+Loc, +Expr, +Env): throw a semantic error unless Expr
% is a nonzero constant.
static_assert(Loc, Expr, Env) :-
    (   catch(const_value(Expr, Env, Value, _), not_constant, fail)
    ->  true
    ;   sema_error(Loc, 'static assertion is not a constant', [])
    ),
    (   Value =\= 0
    ->  true
    ;   sema_error(Loc, 'static assertion failed', [])
    ).

% global_decl(+Loc, +Decl, +Env0, -Env): Env binds the d/5 declaration
% Decl of a function or of an object with static storage, and defines
% the object unless it is an extern without an initializer.
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

% new_literal(+Lit, -Sym, +Env0, -Env): Sym is a fresh symbol that Env
% defines as literal Lit, a list of bytes (a char array) or
% w(ElemType, Values).
new_literal(Lit, Sym, Env0, Env) :-
    next_id(N, Env0, Env1),
    format(atom(Sym), 'str.~w', [N]),
    put_def(lit(Sym), Lit, Env1, Env).

% str_elems(+Str, +ElemType, -Elems): string literal term Str can
% initialize an array of ElemType, and Elems are its elements. Str is
% str(Bytes) for a char array, or wstr(WideType, Values) for an
% integer array of its element's size.
str_elems(str(Bytes), ElemType, Bytes) :-
    is_char_type(ElemType).
str_elems(wstr(WideType, Values), ElemType, Values) :-
    int_type(ElemType),
    int_info(ElemType, Size, _),
    int_info(WideType, Size, _).
str_elems(list([entry([], Str)]), ElemType, Values) :-
    Str \= list(_), str_elems(Str, ElemType, Values).

% new_complit(+Type0, +Init, +Loc, -Sym, +Env0, -Env): Sym is a fresh
% symbol that Env defines as a file-scope compound literal, an unnamed
% static object.
new_complit(Type0, Init, Loc, Sym, Env0, Env) :-
    next_id(N, Env0, Env1),
    format(atom(Sym), 'complit.~w', [N]),
    complete_array(Type0, Init, Type, Loc, Env0, none),
    define_global(Sym, Type, local, Init, Loc, Env1, Env).

% global_data(+Env0, -Data): Data are the data items of every global
% definition and string literal.
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

% global_items(+Env0, +Done, -Data, -Env): Data are the data items of
% the global definitions whose symbols are not in Done. Initializers
% can define more globals (file-scope compound literals), so this
% repeats until there are no new ones; Done lists the symbols already
% emitted.
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

% global_item(+Sym-G, -Data, +Env0, -Env): Data is the data item of
% global definition G.
global_item(Sym-g(Type, Linkage, Init, Loc),
            data(Sym, Linkage, Align, Items), Env0, Env) :-
    catch(type_size_align(Type, Env0, _, Align0), bad(Why),
          sema_error(Loc, '~w has an unsupported type (~w)', [Sym, Why])),
    Align is min(Align0, 16),
    env_defs(Env0, Defs),
    ( get_assoc(initialized(Sym), Defs, Items)
    -> Env = Env0
    ; static_items(Type, Init, Loc, Env0, Env, Items)
    ).

%% Functions

% function(+Loc, +Name, +Type, +DclType, +Body, +Env0, -Env, -Func): Func
% is the IR function for the definition of Name with body Body.
function(Loc, Name, func(RetType, ParamTypes0, Variadic), DclType, Body,
         Env0, Env, func(Sym, Linkage, RetClass, Params, Blocks)) :-
    lookup_ordinary(Env0, Name, fn(_, Sym, Linkage)),
    (   ParamTypes0 == unspecified
    ->  ParamTypes = []
    ;   ParamTypes = ParamTypes0
    ),
    ret_class(Loc, RetType, Env0, RetClass),
    param_names(DclType, Names),
    statement_expression_jumps(Body, Loc),
    reflect_params(DclType, ParamTypes, Env0, ParamEnv),
    State0 = st(ParamEnv, cur(start, []), [], [], 0, Labels, [], []),
    empty_assoc(Labels),
    Ctx = ctx(Name, RetType, none, none, Loc),
    phrase(( sret_param(RetType, SretParams),
             params(Names, ParamTypes, Ctx, Params0),
             variadic_entry(Variadic, SretParams, Params0),
             stmt(Body, Ctx),
             fall_off(RetType)
           ),
           [State0], [State]),
    append(SretParams, Params0, Params),
    State = st(EnvEnd, none, [], RevBlocks, _, _, _, RevAllocs),
    env_scope(Env0, Scope, _),
    env_restore(Scope, EnvEnd, Env),
    reverse(RevBlocks, [blk(start, [], Insts0, Jump)|Rest]),
    reverse(RevAllocs, Allocs),
    append(Allocs, Insts0, Insts),
    Blocks = [blk(start, [], Insts, Jump)|Rest].

variadic_entry(fixed, _, _) --> [].
variadic_entry(variadic, Sret, Params) -->
    { append(Sret, Params, All), length(All, N), Off is 8 * N },
    bind(builtin(va_args), t(va_args)),
    emit(ins(t(va_args), p, va_args, [c(Off)])).

% ret_class(+Loc, +RetType, +Env, -Class): Class is the IR return class
% of a function returning RetType.
ret_class(_, void, _, void) :- !.
ret_class(_, Type, _, Class) :-
    type_class(Type, Class), !.
ret_class(Loc, Type, Env, Class) :-
    su(Type),
    !,
    ret_shape(Type, Env, Loc, Shape),
    (   Shape = words([eb(_, _, K0)]) -> Class = K0
    ;   Shape = words([eb(_, _, K1), eb(_, _, K2)]) -> Class = tuple([K1, K2])
    ;   Class = void
    ).
ret_class(Loc, Type, _, _) :-
    Type == ldouble,
    !,
    sema_error(Loc, 'long double is not supported', []).
ret_class(Loc, Type, _, _) :-
    sema_error(Loc, 'returning ~w is not supported yet', [Type]).

% sret_param(+RetType, -Params)//: Params are the hidden parameters of a
% function returning RetType. A struct over 16 bytes is returned through
% a pointer the caller passes first, as clang does; the function itself
% returns nothing.
sret_param(RetType, Params) -->
    env(Env),
    (   { su(RetType), ret_shape(RetType, Env, unknown, sret) }
    ->  fresh(P),
        bind('%sret', sret(P)),
        { Params = [par(p, P)] }
    ;   { Params = [] }
    ).

% param_names(+DclType, -Names): Names are the parameter names, each
% some(Name) or none, from the function's own declarator: the outermost func, since declarator types
% are built outermost first.
param_names(func(_, unspecified), []) :- !.
param_names(func(_, params(Params, _)), Names) :-
    findall(Name, member(param(_, dcl(Name, _, _)), Params), Names).

% params(+Names, +Types, +Ctx, -Params)//: Params are the IR parameters,
% and each named one is stored into a local. A struct or union comes in
% one word per eightbyte.
params([], [], _, []) --> [].
params([Name|Names], [Type|Types], Ctx, Params) -->
    { su(Type) },
    !,
    env(Env),
    { ctx_loc(Ctx, Loc), arg_words(Type, Env, Loc, Ebs) },
    fresh_params(Ebs, Params0, Values),
    su_param_local(Name, Type, Ebs, Values),
    params(Names, Types, Ctx, Params1),
    { append(Params0, Params1, Params) }.
params([Name|Names], [Type|Types], Ctx, [par(Class, P)|Params]) -->
    { ctx_loc(Ctx, Loc),
      vm_check(Type, Loc),
      (   type_class(Type, Class) -> true
      ;   sema_error(Loc, 'parameter of type ~w is not supported yet', [Type])
      ) },
    fresh(P),
    param_local(Name, Type, P),
    params(Names, Types, Ctx, Params).

% su_param_local(+Name, +Type, +Ebs, +Values)// and
% param_local(+Name, +Type, +P)//: a named parameter of Type, which came
% in as the words Values (eightbytes Ebs) or the temporary P, is stored
% into a local it is bound to; an unnamed one is dropped.
su_param_local(none, _, _, _) --> [].
su_param_local(some(Name), Type, Ebs, Values) -->
    local_slot(Type, Addr),
    store_words(Ebs, Values, Addr),
    bind(Name, var(Addr, Type)).

param_local(none, _, _) --> [].
param_local(some(Name), Type, P) -->
    local_slot(Type, Addr),
    store_typed(Type, P, Addr),
    bind(Name, var(Addr, Type)).

% fresh_params(+Ebs, -Params, -Values)//: one fresh parameter per
% eightbyte; Values are their temporaries.
fresh_params([], [], []) --> [].
fresh_params([eb(_, _, Class)|Ebs], [par(Class, P)|Params], [P|Values]) -->
    fresh(P),
    fresh_params(Ebs, Params, Values).

% fall_off(+RetType)//: end the body; falling off the end returns as a
% bare return would.
fall_off(RetType) -->
    cur(Cur),
    cur_fall_off(Cur, RetType).

% cur_fall_off(+Cur, +RetType)//: the end of the body when Cur is the
% current block: nothing after a jump, else a bare return.
cur_fall_off(none, _) --> [].
cur_fall_off(cur(_, _), RetType) --> zero_ret(RetType).

% zero_ret(+RetType)//: return without a value (zero, if the function
% has a result).
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

% state(-S)//: S is the state. state(-S0, +S)//: the state is S0 and
% becomes S. The semicontext of the one-element state list.
state(S), [S] --> [S].

state(S0, S), [S] --> [S0].

% Readers (cur//1, env//1, cases//1) leave the state as it is; set_*//1
% replace one field; fresh//1 and label//1 take the next number.

cur(Cur) --> state(st(_, Cur, _, _, _, _, _, _)).

env(Env) --> state(st(Env, _, _, _, _, _, _, _)).

set_env(Env) -->
    state(st(_, Cur, Insts, Blocks, N, Labels, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)).

bind(Name, Value) -->
    env(Env0),
    { bind_ordinary(Name, Value, Env0, Env) },
    set_env(Env).

fresh(t(Temp)) -->
    state(st(Env, Cur, Insts, Blocks, N0, Labels, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)),
    { N is N0 + 1,
      format(atom(Temp), 'v~w', [N0]) }.

label(Label) -->
    state(st(Env, Cur, Insts, Blocks, N0, Labels, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)),
    { N is N0 + 1,
      format(atom(Label), 'L~w', [N0]) }.

% ensure_live//: make sure there is a current block, opening an
% unreachable one after a jump.
ensure_live -->
    cur(Cur),
    cur_live(Cur).

% cur_live(+Cur)//: the current block is Cur, or a new one if Cur is
% none.
cur_live(none) --> label(Label), set_cur(cur(Label, [])).
cur_live(cur(_, _)) --> [].

set_cur(Cur) -->
    state(st(Env, _, Insts, Blocks, N, Labels, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)).

% emit(+Inst)//: append Inst to the current block.
emit(Inst) --> ensure_live, push_inst(Inst).

push_inst(Inst) -->
    state(st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs),
          st(Env, Cur, [Inst|Insts], Blocks, N, Labels, Cases, Allocs)).

% term(+Jump)//: end the current block with Jump.
term(Jump) --> ensure_live, close_block(Jump).

close_block(Jump) -->
    state(st(Env, cur(Label, Phis), Insts, Blocks, N, Labels, Cases, Allocs),
          st(Env, none, [], [blk(Label, Phis, BlockInsts, Jump)|Blocks],
             N, Labels, Cases, Allocs)),
    { reverse(Insts, BlockInsts) }.

% start(+Label)//: begin block Label, falling through from a live
% current block.
start(Label) -->
    cur(Cur),
    cur_fallthrough(Cur, Label),
    set_cur(cur(Label, [])).

% cur_fallthrough(+Cur, +Label)//: a live current block Cur ends with a
% jump to Label; after a jump (none) there is nothing to end.
cur_fallthrough(none, _) --> [].
cur_fallthrough(cur(_, _), Label) --> term(jmp(Label)).

% start_phi(+Label, +Phis)//: begin block Label, reached only by jumps.
start_phi(Label, Phis) --> set_cur(cur(Label, Phis)).

% here(-Label)//: Label is the current block's label.
here(Label) --> ensure_live, cur(cur(Label, _)).

add_alloc(Inst) -->
    state(st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, [Inst|Allocs])).

cases(Cases) --> state(st(_, _, _, _, _, _, Cases, _)).

set_cases(Cases) -->
    state(st(Env, Cur, Insts, Blocks, N, Labels, _, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)).

% goto_label(+Name, -Label)//: Label is the IR label of C label Name,
% made on first use.
goto_label(Name, Label) -->
    state(st(Env, Cur, Insts, Blocks, N0, Labels0, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)),
    {   get_assoc(Name, Labels0, Label)
    ->  N = N0, Labels = Labels0
    ;   N is N0 + 1,
        format(atom(Label), 'L~w', [N0]),
        put_assoc(Name, Labels0, Label, Labels)
    }.

% ins(+Class, +Op, +Args, -Dest)//: emit an instruction into Dest, a
% fresh temporary.
ins(Class, Op, Args, Dest) -->
    fresh(Dest),
    emit(ins(Dest, Class, Op, Args)).

% local_slot(+Type, -Addr)//: Addr points at a new local object of
% Type, an alloc in the entry block.
local_slot(Type, Addr) -->
    env(Env),
    { catch(type_size_align(Type, Env, Size0, Align0), bad(Why),
            throw(nanofil_error(Why))),
      ( Align0 =< 4 -> Align = 4 ; Align = Align0 ),
      Size is max(Size0, 1) },
    fresh(Addr),
    add_alloc(ins(Addr, p, alloc(Align), [c(Size)])).

%% Context

ctx_loc(ctx(_, _, _, _, Loc), Loc).

ctx_at(ctx(Func, Ret, Break, Cont, _), Loc, ctx(Func, Ret, Break, Cont, Loc)).

% loop_ctx(+Ctx0, +LBreak, +LCont, -Ctx), switch_ctx(+Ctx0, +LBreak,
% -Ctx): Ctx is Ctx0 inside a loop or switch whose break jumps to
% LBreak and continue to LCont.
loop_ctx(ctx(Func, Ret, _, _, Loc), LBreak, LCont,
         ctx(Func, Ret, some(LBreak), some(LCont), Loc)).

switch_ctx(ctx(Func, Ret, _, Cont, Loc), LBreak,
           ctx(Func, Ret, some(LBreak), Cont, Loc)).

%% Statements

% A lexical prepass gives each statement-expression boundary its AST path.
% Gotos may stay inside or leave boundaries, never enter one (including a
% sibling). Case dispatch must originate inside the same boundary. Keeping
% this separate from emission also checks forward gotos and unevaluated code.
statement_expression_jumps(Body, Loc) :-
    phrase(jump_regions(Body, [], [], [], Loc), Events),
    maplist(check_jump_region(Events), Events).

check_jump_region(Events, jump(Name, From, Loc)) :- !,
    (   member(label_region(Name, To), Events),
        \+ append(_, To, From)
    ->  sema_error(Loc, 'goto into a statement expression is not allowed', [])
    ;   true
    ).
check_jump_region(_, _).

% Visit leaves before matching compound shapes: on Trealla an atom built
% by atom_chars/2 (e.g. the field name "label") can unify with label/2.
% Recursing into its unbound "body" would then grow regions indefinitely.
jump_regions(Term, _, _, _, _) --> { atomic(Term) }, !.
jump_regions(at(Loc, Term), Path, Regions, Switch, _) --> !,
    jump_regions(Term, Path, Regions, Switch, Loc).
jump_regions(stmtexpr(Block), Path, Regions, Switch, Loc) --> !,
    jump_regions(Block, [0|Path], [Path|Regions], Switch, Loc).
jump_regions(label(Name, Body), Path, Regions, Switch, Loc) --> !,
    [label_region(Name, Regions)],
    jump_regions(Body, [0|Path], Regions, Switch, Loc).
jump_regions(goto(Name), _, Regions, _, Loc) --> !,
    [jump(Name, Regions, Loc)].
jump_regions(switch(Expr, Body), Path, Regions, Switch, Loc) --> !,
    jump_regions(Expr, [0|Path], Regions, Switch, Loc),
    jump_regions(Body, [1|Path], Regions, Regions, Loc).
jump_regions(case(Expr, Body), Path, Regions, Switch, Loc) --> !,
    { check_case_region(Regions, Switch, Loc) },
    jump_regions(Expr, [0|Path], Regions, Switch, Loc),
    jump_regions(Body, [1|Path], Regions, Switch, Loc).
jump_regions(default(Body), Path, Regions, Switch, Loc) --> !,
    { check_case_region(Regions, Switch, Loc) },
    jump_regions(Body, [0|Path], Regions, Switch, Loc).
jump_regions(Term, Path, Regions, Switch, Loc) -->
    (   { compound(Term), Term =.. [_|Args] }
    ->  jump_region_args(Args, 0, Path, Regions, Switch, Loc)
    ;   []
    ).

jump_region_args([], _, _, _, _, _) --> [].
jump_region_args([Arg|Args], I, Path, Regions, Switch, Loc) -->
    jump_regions(Arg, [I|Path], Regions, Switch, Loc),
    { J is I + 1 },
    jump_region_args(Args, J, Path, Regions, Switch, Loc).

check_case_region(Regions, Switch, Loc) :-
    (   Regions == Switch -> true
    ;   sema_error(Loc, 'switch dispatch into a statement expression is not allowed', [])
    ).

% stmt(+Stmt, +Ctx)//: lower statement Stmt, an at(Loc, S) term; stmt_//2
% lowers S itself.
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
stmt_(break, ctx(_, _, Break, _, Loc)) -->
    target_jump(Break, Loc, 'break outside a loop or switch').
stmt_(continue, ctx(_, _, _, Cont, Loc)) -->
    target_jump(Cont, Loc, 'continue outside a loop').
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

% target_jump(+Target, +Loc, +Error)//: a jump to the break or
% continue Target, some(Label); none is semantic error Error at Loc.
target_jump(some(Label), _, _) --> term(jmp(Label)).
target_jump(none, Loc, Error) --> { sema_error(Loc, Error, []) }.

% A block scope: save_scope(Scope) on entry, restore_scope(Scope) on exit.
save_scope(Scope) -->
    env(Env),
    { env_scope(Env, Scope, _) }.

restore_scope(Scope) -->
    env(Env0),
    { env_restore(Scope, Env0, Env) },
    set_env(Env).

% items(+Items, +Ctx)//, item(+Item, +Ctx)//: lower the items of a block,
% statements and declarations.
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

% local_decls(+Decls, +Ctx)//, local_decl(+Decl, +Ctx)//: lower
% block-scope declarations. Functions and extern objects are global, a
% static object is a global with a function-qualified name, anything
% else is a local slot.
local_decls([], _) --> [].
local_decls([Decl|Decls], Ctx) -->
    local_decl(Decl, Ctx),
    local_decls(Decls, Ctx).

local_decl(d(Name, Type0, Storage, Asm, Init), Ctx) -->
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
          define_global(Sym, Type, local, Init, Loc, Env2, Env3),
          % Resolve block-scope names before the scope is restored.
          static_items(Type, Init, Loc, Env3, Env4, Items),
          put_def(initialized(Sym), Items, Env4, Env) },
        set_env(Env)
    ;   env(Env),
        { complete_array(Type0, Init, Type, Loc, Env, whole),
          check_local_type(Type, Env, Loc, Name) },
        local_slot(Type, Addr),
        bind(Name, var(Addr, Type)),
        (   { Init == none } -> []
        ;   init(Addr, Type, Init, Ctx)
        )
    ).

% check_local_type(+Type, +Env, +Loc, +Name): throw a semantic error
% unless Type is a type a local object Name can have.
check_local_type(Type, Env, Loc, Name) :-
    vm_check(Type, Loc),
    catch(( type_size_align(Type, Env, _, _) -> true ; true ), bad(Why),
          sema_error(Loc, '~w has a type nanofil does not support (~w)',
                     [Name, Why])).

/* complete_array(+Type0, +Init, -Type, +Loc, +Env, +Whole): Type is
   Type0 with the size of an array of unknown size taken from its
   initializer Init, counting the entries each element takes with brace
   elision: {1, 2, 3, 4} is two elements of a struct {int a, b}. Whole
   is whole when an entry may be a struct expression that initializes a
   struct element whole (locals), none otherwise. */
complete_array(array(ElemType, none), none, array(ElemType, none),
               _, _, _) :- !.
complete_array(array(ElemType, none), Init, array(ElemType, N), Loc, Env,
               Whole) :- !,
    (   str_elems(Init, ElemType, Values)
    ->  length(Values, N0),
        N is N0 + 1
    ;   Init = list(Entries)
    ->  phrase(slots(array(ElemType, none), 0, 0, Entries, _, 0, N,
                     c(Env, Whole, Loc)),
               _)
    ;   sema_error(Loc, 'array of unknown size', [])
    ).
complete_array(Type, _, Type, _, _, _).

% single_value(+Type, +V, +Env, +Whole): entry value V initializes a
% slot of type Type by itself, so no braces were elided. The final cut
% makes this semidet: the alternatives can overlap.
single_value(Type, V, Env, Whole) :-
    (   V = list(_)
    ;   \+ aggregate(Type)
    ;   Type = array(CharType, _),
        str_elems(V, CharType, _)
    ;   Whole == whole,
        su(Type),
        catch(expression_type(V, Env, T0), nanofil_error(_), fail),
        value_type(T0, T1), unqualified(T1, Type1),
        Type1 == Type
    ),
    !.

% dispatch(+Cases, +Value, +Type, +LEnd)//: the switch dispatch, one
% comparison per case, then a jump to the default or LEnd.
dispatch([], _, _, LEnd) --> term(jmp(LEnd)).
dispatch(Cases, Value, Type, LEnd) -->
    { findall(CaseValue-Label, member(case(CaseValue, Label), Cases), Pairs),
      ( memberchk(default(LDefault), Cases) -> true ; LDefault = LEnd ),
      type_class(Type, Class) },
    dispatch_cases(Pairs, Value, Type, Class, LDefault).

% dispatch_cases(+Pairs, +Value, +Type, +Class, +LDefault)//: compare
% Value with each case value of Pairs in turn, then jump to LDefault.
dispatch_cases([], _, _, _, LDefault) --> term(jmp(LDefault)).
dispatch_cases([CaseValue-Label|Pairs], Value, Type, Class, LDefault) -->
    { convert_int(CaseValue, Type, Wrapped) },
    ins(w, cmp(eq, Class), [Value, c(Wrapped)], Test),
    label(Next),
    term(jnz(Test, Label, Next)),
    start(Next),
    dispatch_cases(Pairs, Value, Type, Class, LDefault).

% cond_jump(+Expr, +Ctx, +LTrue, +LFalse)//: branch on the truth of
% scalar Expr.
cond_jump(Expr, Ctx, LTrue, LFalse) -->
    rval(Expr, Ctx, Value),
    truth(Value, Ctx, Test),
    term(jnz(Test, LTrue, LFalse)).

% truth(+Value, +Ctx, -W)//: W is a w value that is nonzero exactly when
% scalar Value is.
truth(v(V, Type), Ctx, W) -->
    (   { type_class(Type, w) } -> { W = V }
    ;   { type_class(Type, l) } -> ins(w, cmp(ne, l), [V, c(0)], W)
    ;   { float_type(Type), type_class(Type, K) }
    ->  ins(w, cmp(ne, K), [V, c(0)], W)
    ;   { Type = ptr(_) }
    ->  ins(l, ptoi, [V], Int),
        ins(w, cmp(ne, l), [Int, c(0)], W)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'a ~w value is not a scalar', [Type]) }
    ).

%% Initializers

/* An initializer means its leaves: the assignments it makes to parts of
   an object, in the order C performs them, a later one overriding what
   an earlier one wrote.
     zero(Off, Type)        clear the object of Type at Off; a braced
                            list or a string literal first clears what
                            it initializes
     val(Off, Type, N)      the integer N, an element of a string literal
     expr(Off, Type, Expr)  the value of the expression Expr, converted
                            to Type: a scalar, or (locals) a whole struct
   Offsets are from the start of the object. A local object stores its
   leaves; a static one turns them into data chunks. The walk over the
   entries also gives an array of unknown size its length
   (complete_array/6). */

% init_leaves(+Type, +Init, +C, -Leaves): Leaves are what Init assigns
% to an object of Type. C = c(Env, Whole, Loc), with Whole as for
% complete_array/6.
init_leaves(Type, Init, C, Leaves) :-
    phrase(object_init(Type, 0, Init, C), Leaves).

% object_init(+Type, +Off, +Init, +C)//: the leaves of Init for the
% object of Type at Off. A scalar may be braced.
object_init(array(T, N), Off, list([entry([], Str)]), C) -->
    { str_elems(Str, T, _) }, !,
    object_init(array(T, N), Off, Str, C).
object_init(Type, Off, list(Entries), C) --> !,
    [zero(Off, Type)],
    (   { aggregate(Type) }
    ->  slots(Type, 0, Off, Entries, Rest, 0, _, C)
    ;   { Entries = [entry(_, V)|Rest] }
    ->  object_init(Type, Off, V, C)
    ;   { Rest = [] }
    ),
    { Rest == [] -> true ; init_error(C, 'excess initializers', []) }.
object_init(array(ElemType, N), Off, Init, C) -->
    { str_elems(Init, ElemType, Values) }, !,
    { length(Values, NValues),
      (   integer(N), NValues > N
      ->  init_error(C, 'string initializer is too long', [])
      ;   true
      ),
      C = c(Env, _, _),
      type_size_align(ElemType, Env, Size, _) },
    [zero(Off, array(ElemType, N))],
    elem_leaves(Values, ElemType, Off, Size).
object_init(array(_, _), _, _, C) --> !,
    { init_error(C, 'array initializer must be a list', []) }.
object_init(Type, Off, Expr, _) --> [expr(Off, Type, Expr)].

% elem_leaves(+Values, +Type, +Off, +Size)//: a val leaf for each of
% Values, consecutive elements of Type and Size from Off.
elem_leaves([], _, _, _) --> [].
elem_leaves([V|Vs], Type, Off, Size) -->
    [val(Off, Type, V)],
    { Off1 is Off + Size },
    elem_leaves(Vs, Type, Off1, Size).

/* slots(+Type, +I, +Off, +Entries0, -Entries, +Max0, -Max, +C)//: the
   leaves of aggregate Type at Off from Entries0, the next undesignated
   entry going to slot I; a designator moves to its slot. Entries is
   what is left when the slots run out. Max is the larger of Max0 and
   one past the last slot initialized. */
slots(_, _, _, [], [], Max, Max, _) --> !.
slots(Type, _, Off, [entry([D|Ds], V)|Entries0], Entries, Max0, Max, C) --> !,
    { designated_slot(D, Type, C, I, SlotOff, SlotType),
      Off1 is Off + SlotOff },
    (   { Ds == [] }
    ->  slot_init(SlotType, Off1, V, Entries0, Entries1, C)
    ;   slots(SlotType, 0, Off1, [entry(Ds, V)], _, 0, _, C),
        { Entries1 = Entries0 }
    ),
    { I1 is I + 1,
      Max1 is max(Max0, I1) },
    slots(Type, I1, Off, Entries1, Entries, Max1, Max, C).
slots(Type, I, Off, Entries0, Entries, Max0, Max, C) -->
    (   { slot(Type, C, I, SlotOff, SlotType) }
    ->  { Entries0 = [entry([], V)|Entries1],
          Off1 is Off + SlotOff },
        slot_init(SlotType, Off1, V, Entries1, Entries2, C),
        { I1 is I + 1,
          Max1 is max(Max0, I1) },
        slots(Type, I1, Off, Entries2, Entries, Max1, Max, C)
    ;   { Entries = Entries0,
          Max = Max0 }
    ).

% slot_init(+Type, +Off, +V, +Entries0, -Entries, +C)//: the leaves of
% entry value V for the slot of Type at Off. Either V initializes the
% slot by itself, or the slot's braces were elided and it takes the
% entries it needs from [V|Entries0], up to the next designator, which
% belongs to the enclosing list.
slot_init(Type, Off, V, Entries, Entries, C) -->
    { C = c(Env, Whole, _),
      single_value(Type, V, Env, Whole) },
    !,
    object_init(Type, Off, V, C).
slot_init(Type, Off, V, Entries0, Entries, C) -->
    { undesignated(Entries0, Pre, Post) },
    slots(Type, 0, Off, [entry([], V)|Pre], Rest, 0, _, C),
    { append(Rest, Post, Entries) }.

% slot(+Type, +C, +I, -Off, -SlotType): the undesignated entry for slot
% I of aggregate Type initializes the SlotType at Off. An array of
% unknown size has every slot; a union has only its first member.
slot(array(ElemType, N), c(Env, _, _), I, Off, ElemType) :-
    ( N == none -> true ; I < N ),
    type_size_align(ElemType, Env, Size, _),
    Off is I * Size.
slot(struct(Id), c(Env, _, _), I, Off, Type) :-
    su_members(struct(Id), Env, Members),
    nth0(I, Members, m(_, Type, Off)).
slot(union(Id), c(Env, _, _), 0, Off, Type) :-
    su_members(union(Id), Env, [m(_, Type, Off)|_]).

% designated_slot(+Desig, +Type, +C, -I, -Off, -SlotType): designator
% Desig of aggregate Type names its slot I, the SlotType at Off; any
% member of a union.
designated_slot(index(Expr), array(ElemType, N), C, I, Off, ElemType) :- !,
    C = c(Env, _, _),
    (   catch(const_value(Expr, Env, I, _), not_constant, fail),
        I >= 0,
        slot(array(ElemType, N), C, I, Off, _)
    ->  true
    ;   init_error(C, 'bad array designator', [])
    ).
designated_slot(field(Field), SU, C, I, Off, Type) :-
    su(SU),
    !,
    C = c(Env, _, _),
    (   su_members(SU, Env, Members),
        nth0(I, Members, m(some(Field), Type, Off))
    ->  true
    ;   init_error(C, 'no member ~w', [Field])
    ).
designated_slot(_, Type, C, _, _, _) :-
    init_error(C, 'bad designator for a ~w', [Type]).

% su_members(+SU, +Env, -Members): Members are the m(Name, Type, Offset)
% of the complete struct or union SU.
su_members(SU, Env, Members) :-
    SU =.. [Kind, Id],
    env_defs(Env, Defs),
    get_assoc(Id, Defs, def(Kind, Members, _, _)).

init_error(c(_, _, Loc), Format, Args) :-
    sema_error(Loc, Format, Args).

aggregate(array(_, _)).
aggregate(struct(_)).
aggregate(union(_)).

% undesignated(+Entries, -Pre, -Post): Pre is the longest prefix of
% Entries without a designator, Post the rest. The final cut commits to
% the first split found, which ends Pre just before the first designator
% (or at the end).
undesignated(Entries, Pre, Post) :-
    append(Pre, Post, Entries),
    \+ member(entry([_|_], _), Pre),
    ( Post = [] ; Post = [entry([_|_], _)|_] ),
    !.

is_char_type(Type) :- memberchk(Type, [char, schar, uchar]).

% init(+Addr, +Type, +Init, +Ctx)//: initialize the local object of
% Type at Addr from Init, storing its leaves.
init(Addr, Type, Init, Ctx) -->
    env(Env),
    { ctx_loc(Ctx, Loc),
      init_leaves(Type, Init, c(Env, whole, Loc), Leaves) },
    store_leaves(Leaves, Addr, Ctx).

store_leaves([], _, _) --> [].
store_leaves([Leaf|Leaves], Addr, Ctx) -->
    store_leaf(Leaf, Addr, Ctx),
    store_leaves(Leaves, Addr, Ctx).

store_leaf(zero(Off, Type), Addr, _) -->
    offset(Addr, Off, P),
    zero_object(P, Type).
store_leaf(val(Off, Type, N), Addr, _) -->
    offset(Addr, Off, P),
    { store_width(Type, Width) },
    emit(store(Width, c(N), P)).
store_leaf(expr(Off, Type, Expr), Addr, Ctx) -->
    offset(Addr, Off, P),
    rval(Expr, Ctx, Value0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(Value0, Type, Loc, v(Value, _)),
    store_typed(Type, Value, P).

% zero_object(+Addr, +Type)//: clear the whole object, since allocs are
% hoisted and a local inside a loop must be reinitialized on every pass.
zero_object(Addr, Type) -->
    env(Env),
    { type_size_align(Type, Env, Size, Align) },
    zero_bytes(Addr, 0, Size, Align).

% zero_bytes(+Addr, +Off, +Size, +Align)//: zero Off..Size with the
% widest stores the alignment allows; bytes below Off are done. The cut
% in the second clause commits to the widest store that fits.
zero_bytes(_, Off, Size, _) --> { Off >= Size }, !.
zero_bytes(Addr, Off, Size, Align) -->
    { Left is Size - Off,
      member(Width-N, [l-8, w-4, h-2, b-1]),
      N =< Left, N =< Align, Off mod N =:= 0 },
    !,
    offset(Addr, Off, P),
    emit(store(Width, c(0), P)),
    { Off1 is Off + N },
    zero_bytes(Addr, Off1, Size, Align).

%% Expressions

% GNU statement expressions load/decay their last expression before the
% block scope closes. A label on that statement does not hide its value.
statement_expression_items([], _, v(c(0), void)) --> [].
statement_expression_items([Item], Ctx, R) --> !,
    statement_expression_last(Item, Ctx, R).
statement_expression_items([Item|Items], Ctx, R) -->
    item(Item, Ctx), statement_expression_items(Items, Ctx, R).

statement_expression_last(at(Loc, expr(Expr)), Ctx0, R) --> !,
    { ctx_at(Ctx0, Loc, Ctx) }, rval(Expr, Ctx, R).
statement_expression_last(at(_, label(Name, Body)), Ctx, R) --> !,
    goto_label(Name, Label), start(Label),
    statement_expression_last(Body, Ctx, R).
statement_expression_last(Item, Ctx, v(c(0), void)) --> item(Item, Ctx).

% obj(+Expr, +Ctx, -R)//: R is Expr as an lvalue, function designator or
% rvalue, without array decay or loading.
obj(generic(Control, Associations), Ctx, R) --> !,
    expr_type(Control, Ctx, T0),
    env(Env),
    { value_type(T0, Type), ctx_loc(Ctx, Loc),
      generic_selection(Type, Associations, Env, Loc, Selected) },
    obj(Selected, Ctx, R).
obj(id(Name), Ctx, R) --> !,
    env(Env),
    (   { lookup_ordinary(Env, Name, Binding),
          object_binding(Binding) }
    ->  binding_obj(Binding, R)
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
    (   {   R0 = lv(Addr, SUType)
        ;   R0 = v(Addr, SUType),
            su(SUType)
        }
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
    { ctx_loc(Ctx, Loc),
      type_name(TypeName, Type0, Env, Loc),
      complete_array(Type0, Init, Type, Loc, Env, whole),
      check_local_type(Type, Env, Loc, 'compound literal') },
    local_slot(Type, Addr),
    init(Addr, Type, Init, Ctx).
obj(Expr, Ctx, R) --> rvalue(Expr, Ctx, R).

% object_binding(+Binding): Binding, an identifier's c_types binding,
% names an object, function or enumeration constant, not a typedef or
% the sret pointer.
object_binding(var(_, _)).
object_binding(fn(_, _, _)).
object_binding(enumconst(_, _)).
object_binding(gvar(_, _, _, _)).

% binding_obj(+Binding, -R)//: R is the identifier bound to Binding as
% obj//3 gives it. A global's address is copied into a temporary.
binding_obj(var(Addr, Type), lv(Addr, Type)) --> [].
binding_obj(fn(Type, Sym, _), fd(glo(Sym), Type)) --> [].
binding_obj(enumconst(V, Type), v(c(V), Type)) --> [].
binding_obj(gvar(Type, Sym, _, _), lv(Addr, Type)) -->
    ins(p, copy, [glo(Sym)], Addr).

% callee_temp(+V, -Callee)//: Callee is V in a temporary, as a callee
% must be.
callee_temp(t(T), t(T)) --> !.
callee_temp(V, Callee) --> ins(p, copy, [V], Callee).

% member_lv(+Addr, +SUType, +Field, +Ctx, -P, -Type)//: P points at
% member Field, of Type, of the struct or union at Addr.
member_lv(Addr, SUType, Field, Ctx, P, Type) -->
    env(Env),
    { ctx_loc(Ctx, Loc) },
    (   { ( SUType = struct(_) ; SUType = union(_) ),
          member_type_offset(SUType, Field, Env, Type, Off) }
    ->  offset(Addr, Off, P)
    ;   { sema_error(Loc, 'no member named ~w', [Field]) }
    ).

% rval(+Expr, +Ctx, -R)//: R is v(V, Type), the value of Expr, arrays
% decayed, lvalues loaded.
rval(Expr, Ctx, R) --> obj(Expr, Ctx, R0), decay(R0, Ctx, R).

% decay(+R0, +Ctx, -R)//: R is the rvalue of R0. An array or function
% decays to a pointer, a scalar lvalue is loaded, and a struct or union
% lvalue stands for its address.
decay(v(V, Type), _, v(V, Type)) --> [].
decay(lv(Addr, array(Type, _)), _, v(Addr, ptr(Type))) --> !.
decay(lv(Addr, Type), _, v(Addr, Type)) --> { su(Type) }, !.
decay(lv(Addr, Type), Ctx, v(V, Type)) --> load_typed(Type, Addr, Ctx, V).
decay(fd(glo(Sym), _), Ctx, _) -->
    { op_kind(setjmp(Sym), setjmp) }, !,
    { ctx_loc(Ctx, Loc),
      sema_error(Loc, 'setjmp requires a direct call, not a function pointer', []) }.
decay(fd(glo(Sym), Type), _, v(Addr, ptr(Type))) --> !,
    ins(p, copy, [glo(Sym)], Addr).
decay(fd(Callee, Type), _, v(Callee, ptr(Type))) --> [].

% expr_type(+Expr, +Ctx, -Type)//: Type is the (reflected) type of
% Expr, unevaluated, for sizeof and _Generic. If c_types cannot type
% Expr, lowering it reports why.
expr_type(Expr, Ctx, Type) -->
    env(Env),
    (   { expression_type(Expr, Env, Type) } -> []
    ;   obj(Expr, Ctx, _), { ctx_loc(Ctx, Loc),
        sema_error(Loc, 'cannot type ~w', [Expr]) }
    ).

% load_typed(+Type, +Addr, +Ctx, -V)//: V is the scalar of Type loaded
% from Addr.
load_typed(Type, Addr, Ctx, V) -->
    (   { load_op(Type, Class, Op) } -> ins(Class, load(Op), [Addr], V)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'loading a ~w value is not supported yet', [Type]) }
    ).

% load_op(+Type, -Class, -Op): Class and load Op hold a scalar of Type.
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
load_op(float, s, s).
load_op(double, d, d).
load_op(ptr(_), p, p).

% store_typed(+Type, +V, +Addr)//: store value V of Type at Addr; a
% struct or union V is the address of the value, copied.
store_typed(Type, V, Addr) --> { su(Type) }, !, copy_object(Type, V, Addr).
store_typed(Type, V, Addr) -->
    { store_width(Type, Width) },
    emit(store(Width, V, Addr)).

% store_width(+Type, -Width): Width is the store of a scalar of Type.
store_width(ptr(_), p) :- !.
store_width(float, s) :- !.
store_width(double, d) :- !.
store_width(Type, Width) :-
    int_info(Type, Size, _),
    memberchk(Size-Width, [1-b, 2-h, 4-w, 8-l]).

% offset(+Addr, +Off, -P)//: P is the pointer Addr + Off (Addr itself
% for 0, with no instruction).
offset(Addr, 0, Addr) --> !.
offset(Addr, Off, P) --> ins(p, add, [Addr, c(Off)], P).

% rvalue(+Expr, +Ctx, -R)//: R is the value of an expression that is
% only an rvalue.
rvalue(num(V0, Suffix), _, v(c(V), Type)) --> !,
    { num_type(V0, Suffix, Type), convert_int(V0, Type, V) }.
rvalue(chr(V), _, v(c(V), int)) --> !.
rvalue(float(Cs), _, v(c(V), Type)) --> !,
    { float_literal(Cs, V, Type) }.
rvalue(sizeof_type(TypeName), Ctx, v(c(Size), ulong)) --> !,
    env(Env),
    { type_size(TypeName, Env, Ctx, Size) }.
rvalue(alignof(TypeName), Ctx, v(c(Align), ulong)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc),
      type_name(TypeName, Type, Env, Loc),
      catch(type_size_align(Type, Env, _, Align), bad(Why),
            sema_error(Loc, 'alignof: ~w', [Why])) }.
rvalue(sizeof_expr(Expr), Ctx, v(c(Size), ulong)) --> !,
    expr_type(Expr, Ctx, Type),
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(type_size_align(Type, Env, Size, _), bad(Why),
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
    { memberchk(Op, [preinc, predec, postinc, postdec]) },
    !,
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
rvalue(va_arg(A, TypeName), Ctx, v(V, Type)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc), type_name(TypeName, Type, Env, Loc),
      ( type_class(Type, K), memberchk(Type, [int, uint, long, ulong, llong, ullong, double, ptr(_)])
      -> true
      ; sema_error(Loc, 'unsupported va_arg type ~w', [Type]) ) },
    rval(A, Ctx, v(P, _)),
    ins(K, va_arg, [P], V).
rvalue(call(id('__builtin_va_start'), [A, _]), Ctx, v(c(0), void)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc),
      ( lookup_ordinary(Env, builtin(va_args), Cursor) -> true
      ; sema_error(Loc, 'va_start outside a variadic function', []) ) },
    rval(A, Ctx, v(P, _)),
    emit(store(p, Cursor, P)).
rvalue(call(id('__builtin_va_copy'), [A, B]), Ctx, v(c(0), void)) --> !,
    rval(A, Ctx, v(P, _)), rval(B, Ctx, v(Q, _)),
    ins(p, load(p), [Q], V), emit(store(p, V, P)).
rvalue(call(id('__builtin_va_end'), [A]), Ctx, v(c(0), void)) --> !,
    rval(A, Ctx, _).
rvalue(call(id(Name), []), _, v(c(V), Type)) -->
    { float_builtin(Name, Type, V) },
    env(Env),
    { \+ lookup_ordinary(Env, Name, _) }, !.
rvalue(call(id('__builtin_constant_p'), [Expr]), _, v(c(V), int)) -->
    env(Env),
    { \+ lookup_ordinary(Env, '__builtin_constant_p', _) }, !,
    { ( catch(constant_value(Expr, Env, _, _), not_constant, fail)
      -> V = 1
      ; V = 0
      ) }.
rvalue(call(id('__builtin_unreachable'), []), _, v(c(0), void)) -->
    env(Env),
    { \+ lookup_ordinary(Env, '__builtin_unreachable', _) }, !,
    term(hlt).
rvalue(call(id('__builtin_alloca'), [Size]), Ctx, v(Addr, ptr(void))) -->
    env(Env),
    { \+ lookup_ordinary(Env, '__builtin_alloca', _) }, !,
    rval(Size, Ctx, V0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(V0, ulong, Loc, v(N, _)),
    ins(p, alloc(16), [N], Addr).
rvalue(call(id('__builtin_expect'), [A, B]), Ctx, R) -->
    env(Env),
    { \+ lookup_ordinary(Env, '__builtin_expect', _) },
    !,
    rval(A, Ctx, VA),
    rval(B, Ctx, _),
    { ctx_loc(Ctx, Loc) },
    assign_convert(VA, long, Loc, R).
rvalue(call(id(Name), Args), Ctx, R) -->
    { overflow_builtin(Name, Op, Fixed) },
    env(Env),
    { \+ lookup_ordinary(Env, Name, _) },
    !,
    checked_arithmetic(Args, Op, Fixed, Ctx, R).
rvalue(call(Func, Args), Ctx, R) --> !, lower_call(Func, Args, Ctx, R).
rvalue(gcond(Cond, B), Ctx, R) --> !, gnu_conditional(Cond, B, Ctx, R).
rvalue(stmtexpr(at(_, block(Items))), Ctx, R) --> !,
    save_scope(Scope),
    statement_expression_items(Items, Ctx, R),
    restore_scope(Scope).
rvalue(Expr, Ctx, _) -->
    { ctx_loc(Ctx, Loc),
      sema_error(Loc, 'cannot lower ~w', [Expr]) }.

% The generic builtins do NOT use the usual arithmetic conversions.
% Keep the exact result in two l limbs, then compare it with the stored
% value extended back to two limbs. 128 bits suffice for all supported
% integer operands (at most 64 bits), including unsigned 64-bit products.
checked_arithmetic(Args, Op, Fixed, Ctx, v(Flag, bool)) -->
    { ctx_loc(Ctx, Loc),
      ( Args = [A, B, P] -> true
      ; sema_error(Loc, 'checked arithmetic requires three arguments', []) ) },
    rval(A, Ctx, VA0), rval(B, Ctx, VB0), rval(P, Ctx, VP),
    { VA0 = v(_, TA), VB0 = v(_, TB),
      ( int_type(TA), int_type(TB), VP = v(Addr, ptr(Type)),
        int_type(Type), Type \== bool,
        ( Fixed == generic ; Fixed == Type )
      -> true
      ; sema_error(Loc, 'invalid checked arithmetic operand types', []) ) },
    overflow_operand(Fixed, VA0, VA), overflow_operand(Fixed, VB0, VB),
    overflow_widen(VA, X, XH), overflow_widen(VB, Y, YH),
    overflow_exact(Op, X, XH, Y, YH, Low, High),
    convert(v(Low, ulong), Type, v(Stored, Type)),
    store_typed(Type, Stored, Addr),
    overflow_widen(v(Stored, Type), Back, BackH),
    ins(w, cmp(ne, l), [Low, Back], BadLow),
    ins(w, cmp(ne, l), [High, BackH], BadHigh),
    ins(w, or, [BadLow, BadHigh], Flag).

overflow_operand(generic, V, V) --> !.
overflow_operand(Type, V, R) --> convert(V, Type, R).

% Extension to l must explicitly truncate a w value first: int_convert
% can reuse an l temp after a cast to int, as w consumers ignore its top.
overflow_widen(v(V, Type), Low, High) -->
    { int_info(Type, Size, Sign) },
    (   { Size < 8 }
    ->  { Sign == signed -> Ext = sw ; Ext = uw },
        ins(l, ext(Ext), [V], Low)
    ;   { Low = V }
    ),
    (   { Sign == signed }
    ->  ins(l, sar, [Low, c(63)], High)
    ;   { High = c(0) }
    ).

overflow_exact(add, X, XH, Y, YH, Low, High) -->
    ins(l, add, [X, Y], Low),
    ins(w, cmp(ult, l), [Low, X], Carry),
    ins(l, ext(uw), [Carry], C),
    ins(l, add, [XH, YH], H), ins(l, add, [H, C], High).
overflow_exact(sub, X, XH, Y, YH, Low, High) -->
    ins(l, sub, [X, Y], Low),
    ins(w, cmp(ult, l), [X, Y], Borrow),
    ins(l, ext(uw), [Borrow], C),
    ins(l, sub, [XH, YH], H), ins(l, sub, [H, C], High).
overflow_exact(mul, X, XH, Y, YH, Low, High) -->
    ins(l, mul, [X, Y], Low),
    ins(l, and, [X, c(4294967295)], XL),
    ins(l, shr, [X, c(32)], XU),
    ins(l, and, [Y, c(4294967295)], YL),
    ins(l, shr, [Y, c(32)], YU),
    ins(l, mul, [XL, YL], LL), ins(l, mul, [XU, YL], UL),
    ins(l, mul, [XL, YU], LU), ins(l, mul, [XU, YU], UU),
    ins(l, shr, [LL, c(32)], LLH),
    ins(l, and, [UL, c(4294967295)], ULL),
    ins(l, and, [LU, c(4294967295)], LUL),
    ins(l, add, [LLH, ULL], Mid0), ins(l, add, [Mid0, LUL], Mid),
    ins(l, shr, [Mid, c(32)], Carry),
    ins(l, shr, [UL, c(32)], ULH), ins(l, shr, [LU, c(32)], LUH),
    ins(l, add, [UU, ULH], H0), ins(l, add, [H0, LUH], H1),
    ins(l, add, [H1, Carry], H2),
    % Signed inputs contribute -Y or -X to the unsigned product's high limb.
    ins(l, and, [XH, Y], CX), ins(l, and, [YH, X], CY),
    ins(l, sub, [H2, CX], H3), ins(l, sub, [H3, CY], High).

% type_size(+TypeName, +Env, +Ctx, -Size): Size is sizeof(TypeName).
type_size(TypeName, Env, Ctx, Size) :-
    ctx_loc(Ctx, Loc),
    type_name(TypeName, Type, Env, Loc),
    catch(type_size_align(Type, Env, Size, _), bad(Why),
          sema_error(Loc, 'sizeof: ~w', [Why])).

% type_name(+TypeName, -Type, +Env, +Loc): Type is the type TypeName
% names, as lowering uses it: a variably modified one (an array of
% non-constant size anywhere inside) is rejected, since its size
% expressions would have to be evaluated, side effects and all.
type_name(TypeName, Type, Env, Loc) :-
    type_name_type(TypeName, Type, Env, _),
    vm_check(Type, Loc).

% vm_check(+Type, +Loc): throw a semantic error if Type is variably
% modified.
vm_check(Type, Loc) :-
    (   vm_type(Type)
    ->  sema_error(Loc,
                   'variably modified types (non-constant array size) are not supported',
                   [])
    ;   unsupported_value_type(Type, Why)
    ->  sema_error(Loc, '~w is not supported', [Why])
    ;   true
    ).

unsupported_value_type(ldouble, 'long double').
unsupported_value_type(bad(Why), Why).
unsupported_value_type(array(T, _), Why) :- unsupported_value_type(T, Why).

% vm_type(+Type): Type is variably modified. The cut ending the func
% clause succeeds once however many parts are variably modified.
vm_type(bad('non-constant array size')).
vm_type(ptr(Type)) :- vm_type(Type).
vm_type(array(Type, _)) :- vm_type(Type).
vm_type(func(Ret, Params, _)) :-
    (   vm_type(Ret)
    ;   is_list(Params),
        member(Param, Params),
        vm_type(Param)
    ),
    !.

%% Conversions

% convert(+Value0, +To, -R)//: R is v(V1, To), scalar Value0 =
% v(V, From) converted to scalar type To (or void). Callers check that
% the types are scalar first.
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
    { ( float_type(From) ; float_type(To) ),
      arithmetic_type(From), arithmetic_type(To),
      const_convert(N, From, To, W), integer(W) }, !.
convert(v(V, float), double, v(R, double)) --> !,
    ins(d, ext(s), [V], R).
convert(v(V, double), float, v(R, float)) --> !,
    ins(s, truncd, [V], R).
convert(v(V, From), To, v(R, To)) -->
    { int_type(From), float_type(To),
      type_class(From, IK), int_info(From, _, Sign),
      int_float_op(IK, Sign, Op), type_class(To, K) }, !,
    ins(K, Op, [V], R).
convert(v(V, From), To, v(R, To)) -->
    { float_type(From), int_type(To),
      type_class(From, K), int_info(To, _, Sign), type_class(To, IK),
      float_int_op(K, Sign, Op),
      conversion_int_type(IK, Sign, Base) }, !,
    ins(IK, Op, [V], I),
    int_convert(Base, To, I, R).
convert(v(c(N), From), To, v(c(W), To)) -->
    { int_type(From), int_type(To) },
    !,
    { convert_int(N, To, W) }.
convert(v(V, From), To, v(V1, To)) -->
    { int_type(From), int_type(To) },
    !,
    int_convert(From, To, V, V1).
convert(v(c(N), From), ptr(P), v(c(W), ptr(P))) -->
    { int_type(From) },
    !,
    { convert_int(N, ulong, W) }.
convert(v(V, From), ptr(P), v(V1, ptr(P))) -->
    { int_type(From) },
    !,
    int_convert(From, ulong, V, V2),
    ins(p, itop, [V2], V1).
convert(v(V, ptr(_)), To, R) -->
    { int_type(To) },
    !,
    ins(l, ptoi, [V], Int),
    convert(v(Int, ulong), To, R).
convert(v(V, ptr(_)), ptr(P), v(V, ptr(P))) --> [].

int_float_op(w, signed, swtof).
int_float_op(w, unsigned, uwtof).
int_float_op(l, signed, sltof).
int_float_op(l, unsigned, ultof).
float_int_op(s, signed, stosi).
float_int_op(s, unsigned, stoui).
float_int_op(d, signed, dtosi).
float_int_op(d, unsigned, dtoui).

% Float-to-integer instructions produce a full w/l; normalize narrow C
% destinations afterward, without ever routing an unsigned result via signed.
conversion_int_type(w, signed, int).
conversion_int_type(w, unsigned, uint).
conversion_int_type(l, signed, long).
conversion_int_type(l, unsigned, ulong).

% int_convert(+From, +To, +V, -V1)//: V1 is integer V of type From
% converted to type To, extended where the representation changes.
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

% representable(+SizeFrom, +SignFrom, +SizeTo, +SignTo): every value of
% the source type is a value of the target type.
representable(SizeFrom, SignFrom, SizeTo, SignTo) :-
    SizeTo > SizeFrom,
    ( SignTo == signed ; SignFrom == unsigned ),
    !.
representable(Size, Sign, Size, Sign).

% narrow_ext(+Size, +Sign, -Op): Op is the extension that normalizes a
% narrow int.
narrow_ext(1, signed, sb).
narrow_ext(1, unsigned, ub).
narrow_ext(2, signed, sh).
narrow_ext(2, unsigned, uh).

% convert_checked(+Value0, +To, +Ctx, -R)//: R is Value0 converted to
% To as by a cast.
convert_checked(Value0, To, Ctx, R) -->
    { Value0 = v(_, From), ctx_loc(Ctx, Loc) },
    (   { scalar_conversion(From, To) } -> convert(Value0, To, R)
    ;   { sema_error(Loc, 'cannot convert ~w to ~w', [From, To]) }
    ).

% assign_convert(+Value0, +To, +Loc, -R)//: R is Value0 converted to To
% as by assignment (also arguments and returns).
assign_convert(Value0, To, Loc, R) -->
    { Value0 = v(Addr, From) },
    (   { su(To) }
    ->  (   { From == To } -> { R = v(Addr, To) }
        ;   { sema_error(Loc, 'cannot assign ~w to ~w', [From, To]) }
        )
    ;   { scalar_conversion(From, To) } -> convert(Value0, To, R)
    ;   { sema_error(Loc, 'cannot assign ~w to ~w', [From, To]) }
    ).

% Floating values cannot be converted to/from pointers, even by a cast.
scalar_conversion(A, B) :- arithmetic_type(A), arithmetic_type(B).
scalar_conversion(ptr(_), ptr(_)).
scalar_conversion(ptr(_), B) :- int_type(B).
scalar_conversion(A, ptr(_)) :- int_type(A).

%% Operators

% unary(+Op, +Value0, +Ctx, -R)//: R is unary operator Op applied to
% Value0.
unary(neg, Value0, Ctx, v(V, Type)) -->
    arith_operand(Value0, Ctx, Type, V1),
    { type_class(Type, Class) },
    ins(Class, neg, [V1], V).
unary(plus, Value0, Ctx, v(V, Type)) -->
    arith_operand(Value0, Ctx, Type, V).
unary(bnot, Value0, Ctx, v(V, Type)) -->
    { Value0 = v(_, From), ctx_loc(Ctx, Loc),
      ( int_type(From) -> true
      ; sema_error(Loc, 'operand of ~~ is not an integer', []) ) },
    arith_operand(Value0, Ctx, Type, V1),
    { type_class(Type, Class) },
    ins(Class, xor, [V1, c(-1)], V).
unary(not, Value0, Ctx, v(V, int)) -->
    truth(Value0, Ctx, W),
    ins(w, cmp(eq, w), [W, c(0)], V).

% arith_operand(+Value0, +Ctx, -Type, -V)//: V is arithmetic operand
% Value0 promoted to Type.
arith_operand(Value0, Ctx, Type, V) -->
    { Value0 = v(_, From), ctx_loc(Ctx, Loc),
      (   arithmetic_type(From) -> integer_promotion(From, Type)
      ;   sema_error(Loc, 'operand of type ~w is not arithmetic', [From])
      ) },
    convert(Value0, Type, v(V, _)).

% binary(+Op, +VA, +VB, +Ctx, -R)//: R is binary operator Op applied to
% the values VA and VB, converted as binary_operands/6 says.
binary(Op, VA, VB, Ctx, R) -->
    { VA = v(_, TA), VB = v(_, TB), ctx_loc(Ctx, Loc),
      (   binary_operands(Op, TA, TB, CA, CB, T) -> true
      ;   sema_error(Loc, 'invalid operands to ~w: ~w and ~w', [Op, TA, TB])
      ) },
    binary_value(Op, CA, CB, T, VA, VB, Ctx, R).

% binary_value(+Op, +CA, +CB, +T, +VA, +VB, +Ctx, -R)//: R, of type T,
% is Op applied to VA converted to CA and VB converted to CB. Pointer
% arithmetic scales by the element size. Direct ordered comparisons are
% essential: !(a < b) is not a >= b when either operand is NaN.
binary_value(Op, ptr(E), long, _, VA, VB, Ctx, R) --> !,
    ptr_offset(Op, VA, E, VB, Ctx, R).
binary_value(add, long, ptr(E), _, VA, VB, Ctx, R) --> !,
    ptr_offset(add, VB, E, VA, Ctx, R).
binary_value(sub, ptr(E), ptr(_), _, VA, VB, Ctx, R) --> !,
    ptr_diff(VA, VB, E, Ctx, R).
binary_value(Op, CA, CB, T, VA, VB, _, v(V, T)) -->
    convert(VA, CA, v(A, _)),
    convert(VB, CB, v(B, _)),
    { type_class(CA, K),
      ( float_type(CA) -> Sign = signed ; int_info(CA, _, Sign) ),
      (   cmp_op(Op, SignedCmp, UnsignedCmp)
      ->  Class = w,
          (   float_type(CA) -> Cmp = Op
          ;   Sign == signed -> Cmp = SignedCmp
          ;   Cmp = UnsignedCmp
          ),
          IOp = cmp(Cmp, K)
      ;   Class = K, arith_op(Op, Sign, IOp)
      ) },
    ins(Class, IOp, [A, B], V).

% cmp_op(+Op, -SignedCmp, -UnsignedCmp): C comparison Op is IR
% comparison SignedCmp on signed and UnsignedCmp on unsigned operands.
cmp_op(eq, eq, eq).
cmp_op(ne, ne, ne).
cmp_op(lt, slt, ult).
cmp_op(gt, sgt, ugt).
cmp_op(le, sle, ule).
cmp_op(ge, sge, uge).

% arith_op(+Op, +Sign, -IROp): C arithmetic Op on operands of Sign is
% IR operation IROp.
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
arith_op(shl, _, shl).
arith_op(shr, signed, sar).
arith_op(shr, unsigned, shr).

% ptr_offset(+Op, +VP, +ElemType, +VI, +Ctx, -R)//: R is P + I or
% P - I, I scaled by the element size.
ptr_offset(Op, v(P, PtrType), ElemType, VI, Ctx, v(R, PtrType)) -->
    { PtrType = ptr(ElemType) },
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(type_size_align(ElemType, Env, Size, _), bad(Why),
            sema_error(Loc, 'pointer arithmetic on ~w (~w)',
                       [ElemType, Why])) },
    convert(VI, long, v(I, _)),
    (   { I = c(N) } -> { Off is N * Size, OffV = c(Off) }
    ;   { Size =:= 1 } -> { OffV = I }
    ;   ins(l, mul, [I, c(Size)], OffV)
    ),
    ins(p, Op, [P, OffV], R).

% ptr_diff(+VA, +VB, +ElemType, +Ctx, -R)//: R is A - B in elements.
ptr_diff(v(A, _), v(B, _), ElemType, Ctx, v(V, long)) -->
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(type_size_align(ElemType, Env, Size, _), bad(Why),
            sema_error(Loc, 'pointer subtraction on ~w (~w)',
                       [ElemType, Why])) },
    ins(l, ptoi, [A], IA),
    ins(l, ptoi, [B], IB),
    ins(l, sub, [IA, IB], Diff),
    (   { Size =:= 1 } -> { V = Diff }
    ;   ins(l, div, [Diff, c(Size)], V)
    ).

% logical(+Op, +A, +B, +Ctx, -R)//: R is A && B (land) or A || B (lor),
% a phi of 0/1 over the short-circuit edges.
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

% gnu_conditional(+Cond, +B, +Ctx, -R)//: R is GNU Cond ?: B. Cond is
% evaluated once, and is the result if nonzero.
gnu_conditional(Cond, B, Ctx, R) -->
    cond_type(Cond, B, Ctx, Type),
    rval(Cond, Ctx, VC),
    truth(VC, Ctx, W),
    label(LA), label(LB), label(LJoin),
    term(jnz(W, LA, LB)),
    start(LA), arm_convert(VC, Type, Ctx, VA1), here(LA1), term(jmp(LJoin)),
    start(LB), rval(B, Ctx, VB), arm_convert(VB, Type, Ctx, VB1), here(LB1),
    term(jmp(LJoin)),
    join_arms(Type, LJoin, LA1-VA1, LB1-VB1, R).

% conditional(+Cond, +A, +B, +Ctx, -R)//: R is Cond ? A : B. The arms are
% probed first for their types, then lowered in their own blocks.
conditional(Cond, A, B, Ctx, R) -->
    cond_type(A, B, Ctx, Type),
    label(LA), label(LB), label(LJoin),
    cond_jump(Cond, Ctx, LA, LB),
    start(LA), rval(A, Ctx, VA), arm_convert(VA, Type, Ctx, VA1), here(LA1),
    term(jmp(LJoin)),
    start(LB), rval(B, Ctx, VB), arm_convert(VB, Type, Ctx, VB1), here(LB1),
    term(jmp(LJoin)),
    join_arms(Type, LJoin, LA1-VA1, LB1-VB1, R).

% join_arms(+Type, +LJoin, +LA-VA, +LB-VB, -R)//: start block LJoin; R
% is the ?: result there, a phi of VA from LA and VB from LB.
join_arms(Type, LJoin, LA-VA, LB-VB, R) -->
    (   { Type == void } -> start(LJoin), { R = v(c(0), void) }
    ;   { su(Type) -> Class = p ; type_class(Type, Class) },
        fresh(V),
        start_phi(LJoin, [phi(V, Class, [LA-VA, LB-VB])]),
        { R = v(V, Type) }
    ).

% arm_convert(+Value0, +Type, +Ctx, -V)//: V is the IR value of ?: arm
% Value0 as the result Type: c(0) for void, the address for a struct.
arm_convert(Value0, void, _, c(0)) --> !, { Value0 = v(_, _) }.
arm_convert(v(Addr, Type), Type, _, Addr) --> { su(Type) }, !.
arm_convert(Value0, Type, Ctx, V) -->
    convert_checked(Value0, Type, Ctx, v(V, _)).

% cond_type(+A, +B, +Ctx, -Type)//: Type is the type of c ? A : B, as
% c_types judges it, unqualified. If an arm cannot be typed, lowering
% it reports why.
cond_type(A, B, Ctx, Type) -->
    env(Env),
    { ctx_loc(Ctx, Loc) },
    (   { conditional_type(A-B, Env, Type0) } -> { unqualified(Type0, Type) }
    ;   { maplist(arm_value_type(Env), [A, B], [TA, TB]) }
    ->  { sema_error(Loc, 'incompatible ?: operands ~w and ~w', [TA, TB]) }
    ;   rval(A, Ctx, _), rval(B, Ctx, _),
        { sema_error(Loc, 'cannot type ?: operands', []) }
    ).

arm_value_type(Env, E, T) :-
    expression_type(E, Env, T0), value_type(T0, T1), unqualified(T1, T).

%% Assignment

% assignment(+Op, +A, +B, +Ctx, -R)//: store B (or A Op B, for a compound
% Op) into lvalue A; R is the value stored.
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

% compound_op(+Op, -BinOp): compound assignment Op applies BinOp.
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

% incdec(+Op, +A, +Ctx, -R)//: increment or decrement scalar lvalue A;
% R is the new value (pre) or the old one (post).
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

% lower_call(+Func, +Args, +Ctx, -R)//: R is the result of calling Func
% with Args.
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
    (   { Callee = glo(Kind), op_kind(setjmp(Kind), setjmp) }
    ->  { ( RetType == int, setjmp_args(Kind, IRArgs, Operands) -> true
          ; sema_error(Loc, 'invalid ~w signature', [Kind]) ) },
        ins(w, setjmp(Kind), Operands, V),
        { R = v(V, int) }
    ;   { su(RetType) } -> struct_call(RetType, Callee, IRArgs, Loc, R)
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

setjmp_args(sigsetjmp, [arg(p, Buf), arg(w, Mask)], [Buf, Mask]).
setjmp_args(setjmp, [arg(p, Buf)], [Buf, c(0)]).
setjmp_args('_setjmp', [arg(p, Buf)], [Buf, c(0)]).

% call_args(Args, ParamTypes, Ctx, IRArgs): a struct argument goes as one
% word per eightbyte; arguments past the prototype get the default
% promotions.
call_args([], _, _, []) --> [].
call_args([Arg|Args], [ParamType|ParamTypes], Ctx, IRArgs) -->
    { su(ParamType) },
    !,
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
        (   { arithmetic_type(Type0) }
        ->  { default_promotion(Type0, Type) },
            convert(Value0, Type, v(V, _))
        ;   { Type0 = ptr(_) } -> { Value0 = v(V, Type) }
        ;   { sema_error(Loc,
                'passing ~w to a variadic or unprototyped function is not supported',
                [Type0]) }
        )
    ),
    { type_class(Type, Class) },
    call_args(Args, ParamTypes, Ctx, IRArgs).

% struct_call(+RetType, +Callee, +Args, +Loc, -R)//: R is the result of a
% call returning a struct: its words land in a fresh local, or the
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

% return_struct(+RetType, +Addr, +Loc)//: return the struct at Addr, in
% words or through the sret pointer.
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

% normalize(+Type, +V0, -V)//: V is call result V0 of Type, a narrow one
% re-extended: nothing guarantees the callee did.
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

% eightbytes(+Type, +Env, +Loc, -Ebs): Ebs are the eightbytes of Type.
eightbytes(Type, Env, Loc, Ebs) :-
    catch(type_size_align(Type, Env, Size, _), bad(Why),
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

% ptr_offsets(+Type, +Env, +Base, -Offs0, ?Offs): Offs0-Offs is the
% difference list of the offsets, from Base, where Type holds pointers.
ptr_offsets(ptr(_), _, Base, [Base|Offs], Offs) :- !.
ptr_offsets(array(ElemType, N), Env, Base, Offs0, Offs) :-
    integer(N),
    !,
    ptr_offsets(ElemType, Env, 0, ElemOffs, []),
    (   ElemOffs == [] -> Offs0 = Offs
    ;   type_size_align(ElemType, Env, Size, _),
        Last is N - 1,
        findall(I, between(0, Last, I), Indices),
        foldl(elem_ptrs(ElemType, Env, Base, Size), Indices, Offs0, Offs)
    ).
ptr_offsets(SU, Env, Base, Offs0, Offs) :-
    su(SU),
    !,
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

% arg_words(+Type, +Env, +Loc, -Ebs): Ebs are the eightbytes in which a
% struct or union argument of Type is passed.
arg_words(Type, Env, Loc, Ebs) :-
    by_value_check(Type, Env, Loc),
    type_size_align(Type, Env, Size, _),
    (   Size > 16
    ->  sema_error(Loc, 'passing a ~w of ~w bytes by value is not supported yet',
                   [Type, Size])
    ;   eightbytes(Type, Env, Loc, Ebs)
    ).

% ret_shape(+Type, +Env, +Loc, -Shape): Shape is how a struct or union
% of Type is returned: sret, or words(Eightbytes).
ret_shape(Type, Env, Loc, Shape) :-
    by_value_check(Type, Env, Loc),
    type_size_align(Type, Env, Size, _),
    (   Size > 16 -> Shape = sret
    ;   eightbytes(Type, Env, Loc, Ebs),
        Shape = words(Ebs)
    ).

by_value_check(Type, Env, Loc) :-
    ( contains_float(Type, Env)
    -> sema_error(Loc, 'float-containing struct or union by value is not supported', [])
    ; true
    ).

contains_float(Type, _) :- float_type(Type), !.
contains_float(ldouble, _).
contains_float(array(T, _), Env) :- contains_float(T, Env).
contains_float(Type, Env) :-
    su(Type), Type =.. [_, Id], env_defs(Env, Defs),
    get_assoc(Id, Defs, def(_, Members, _, _)),
    member(m(_, T, _), Members), contains_float(T, Env).

% copy_object(+Type, +Src, +Dst)//: copy the object of Type at Src to
% Dst, an eightbyte at a time.
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

% pieces(+N, +Off, -Pieces): Pieces are N bytes from offset Off as
% p(Offset, Bytes, Load, Store), widest first. The cut after the member
% commits to the widest piece that fits.
pieces(0, _, []) :- !.
pieces(N, Off, [p(Off, Bytes, Load, Store)|Pieces]) :-
    member(Bytes-Load-Store, [8-l-l, 4-uw-w, 2-uh-h, 1-ub-b]),
    Bytes =< N,
    !,
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

% load_words(+Ebs, +Addr, -Words)//: Words are the words of the value at
% Addr, one per eightbyte.
load_words([], _, []) --> [].
load_words([eb(Off, N, Class)|Ebs], Addr, [W|Words]) -->
    offset(Addr, Off, P),
    (   { Class == p } -> ins(p, load(p), [P], W)
    ;   { pieces(N, 0, Pieces) },
        load_pieces(Pieces, P, none, W)
    ),
    load_words(Ebs, Addr, Words).

% load_pieces(+Pieces, +P, +Acc0, -W)//: W is Acc0 (none at first) or'd
% with each of Pieces loaded from P and shifted into place.
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

% store_words(+Ebs, +Words, +Addr)//: store Words, one per eightbyte,
% into the object at Addr.
store_words([], [], _) --> [].
store_words([eb(Off, N, Class)|Ebs], [W|Words], Addr) -->
    offset(Addr, Off, P),
    (   { Class == p } -> emit(store(p, W, P))
    ;   { pieces(N, 0, Pieces) },
        store_pieces(Pieces, W, P)
    ),
    store_words(Ebs, Words, Addr).

% store_pieces(+Pieces, +W, +P)//: store each of Pieces of word W, shifted
% down, at P.
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
   of a global of type Type. Each leaf of Init becomes a chunk
   chunk(Offset, Bytes, Item), a later one replacing an earlier one at
   the same offset, then the gaps are zero-filled. A pointer is
   item(p, sym(S, Off)); string literals in initializers become data of
   their own. */
static_items(Type, Init, Loc, Env0, Env, Items) :-
    type_size_align(Type, Env0, Size, _),
    (   Init == none -> Leaves = []
    ;   init_leaves(Type, Init, c(Env0, none, Loc), Leaves)
    ),
    foldl(static_leaf(Loc), Leaves, s(Env0, [], 0), s(Env, Chunks0, _)),
    reverse(Chunks0, Chunks),
    empty_assoc(ByOffset0),
    foldl(put_chunk, Chunks, ByOffset0, ByOffset),
    assoc_to_values(ByOffset, Sorted),
    fill_items(Sorted, 0, Size, Loc, Items).

% put_chunk(+Chunk, +ByOffset0, -ByOffset): ByOffset maps Chunk's offset
% to Chunk, replacing any earlier one there.
put_chunk(chunk(Off, N, Item), ByOffset0, ByOffset) :-
    put_assoc(Off, ByOffset0, chunk(Off, N, Item), ByOffset).

% fill_items(+Chunks, +Pos, +Size, +Loc, -Items): Items are the items of
% Chunks, sorted by offset, with zero(N) filling the gaps from Pos to
% Size.
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

% int_chunk(+Off, +Type, +V, -Chunk): Chunk holds integer V of Type at
% Off.
int_chunk(Off, Type, V, chunk(Off, N, item(Width, c(U)))) :-
    int_info(Type, N, _),
    memberchk(N-Width, [1-b, 2-h, 4-w, 8-l]),
    convert_int(V, Type, U).

/* static_leaf(+Loc, +Leaf, +S0, -S): S = s(Env, Chunks, End) adds the
   chunk of Leaf to the reversed Chunks of S0; End is where the chunks
   end so far. A zero leaf drops the chunks it covers, which only a
   designator that goes back can have made. */
static_leaf(_, zero(Off, Type), s(Env, Chunks0, End), s(Env, Chunks, End)) :-
    (   Off >= End
    ->  Chunks = Chunks0
    ;   type_size_align(Type, Env, Size, _),
        Hi is Off + Size,
        exclude(chunk_within(Off, Hi), Chunks0, Chunks)
    ).
static_leaf(_, val(Off, Type, V), s(Env, Chunks, End0),
            s(Env, [Chunk|Chunks], End)) :-
    int_chunk(Off, Type, V, Chunk),
    chunk_end(Chunk, End0, End).
static_leaf(Loc, expr(Off, Type, Expr), s(Env0, Chunks, End0),
            s(Env, [Chunk|Chunks], End)) :-
    expr_chunk(Type, Off, Expr, Loc, Env0, Env, Chunk),
    chunk_end(Chunk, End0, End).

chunk_within(Lo, Hi, chunk(Off, _, _)) :- Off >= Lo, Off < Hi.

chunk_end(chunk(Off, N, _), End0, End) :- End is max(End0, Off + N).

% expr_chunk(+Type, +Off, +Expr, +Loc, +Env0, -Env, -Chunk): Chunk holds
% the constant value of Expr, of scalar Type, at Off.
expr_chunk(Type, Off, Expr, Loc, Env, Env, Chunk) :-
    arithmetic_type(Type),
    !,
    (   catch(constant_value(Expr, Env, V0, From), not_constant, fail),
        const_convert(V0, From, Type, V), integer(V)
    ->  true
    ;   sema_error(Loc, 'initializer is not a constant', [])
    ),
    ( float_type(Type)
    -> type_class(Type, K), type_size_align(Type, Env, N, _),
       Chunk = chunk(Off, N, item(K, c(V)))
    ; int_chunk(Off, Type, V, Chunk)
    ).
expr_chunk(ptr(_), Off, Expr, Loc, Env0, Env, Chunk) :- !,
    addr_const(Expr, Loc, Env0, Env, R),
    (   R = sym(Sym, SymOff, _)
    ->  Chunk = chunk(Off, 8, item(p, sym(Sym, SymOff)))
    ;   Chunk = chunk(Off, 8, item(l, c(0)))
    ).
expr_chunk(Type, _, _, Loc, _, _, _) :-
    sema_error(Loc, 'cannot statically initialize a ~w', [Type]).

/* addr_const(+Expr, +Loc, +Env0, -Env, -R): an address constant,
   sym(Symbol, Offset, PointerType), or null. */
addr_const(str(Bytes), _, Env0, Env, sym(Sym, 0, ptr(char))) :- !,
    new_literal(Bytes, Sym, Env0, Env).
addr_const(wstr(WideType, Values), _, Env0, Env,
           sym(Sym, 0, ptr(WideType))) :- !,
    new_literal(w(WideType, Values), Sym, Env0, Env).
addr_const(complit(TypeName, Init), Loc, Env0, Env,
           sym(Sym, 0, ptr(ElemType))) :-
    type_name(TypeName, Type, Env0, Loc),
    Type = array(ElemType, _),
    !,
    new_complit(Type, Init, Loc, Sym, Env0, Env).
addr_const(id(Name), _, Env, Env, R) :-
    lookup_ordinary(Env, Name, gvar(array(ElemType, _), Sym, _, _)),
    !,
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
    catch(const_value(Index, Env0, K, _), not_constant, fail),
    !,
    addr_const(Ptr, Loc, Env0, Env, R0),
    offset_const(Op, R0, K, Env, Loc, R).
addr_const(bin(add, Index, Ptr), Loc, Env0, Env, R) :-
    catch(const_value(Index, Env0, K, _), not_constant, fail),
    !,
    addr_const(Ptr, Loc, Env0, Env, R0),
    offset_const(add, R0, K, Env, Loc, R).
addr_const(Expr, Loc, Env, Env, null) :-
    (   catch(const_value(Expr, Env, 0, _), not_constant, fail) -> true
    ;   sema_error(Loc, 'initializer is not an address constant', [])
    ).

% offset_const(+Op, +R0, +K, +Env, +Loc, -R): R is address constant R0
% plus (add) or minus (sub) K elements.
offset_const(Op, sym(Sym, Off0, ptr(ElemType)), K, Env, Loc,
             sym(Sym, Off, ptr(ElemType))) :- !,
    catch(type_size_align(ElemType, Env, Size, _), bad(Why),
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
lvalue_const(complit(TypeName, Init), Loc, Env0, Env,
             sym(Sym, 0, Type)) :- !,
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

% member_off(+SUType, +Field, +Env, +Loc, -Type, -Off): member Field of
% struct or union SUType has Type and offset Off.
member_off(SUType, Field, Env, Loc, Type, Off) :-
    (   ( SUType = struct(_) ; SUType = union(_) ),
        member_type_offset(SUType, Field, Env, Type, Off)
    ->  true
    ;   sema_error(Loc, 'no member named ~w', [Field])
    ).

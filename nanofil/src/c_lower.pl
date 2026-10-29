/*  Lowering from C to IR (milestone 4b), in the style of cproc: it turns
    the parsed translation unit into an IR module for the Fil-C backend.

    Every local variable and parameter lives in an alloc'd object, and
    the allocs are hoisted into the entry block; with -O, promote turns
    them into temporaries. Pointers are class `p`, so the output is a
    Fil-C module.

    Expressions are lowered from c_types' typed trees (elaborate/3). The
    tree says what each expression is and what its operands are
    converted to, and the elaborator has checked C's constraints, so
    lowering only translates: lower//3 for values, place//3 for objects
    and functions.

    A narrow integer (char, short, bool) is always held sign- or
    zero-extended to 32 bits in a `w`, so conversions only extend when
    the source type has values the target cannot represent.

    ## Values

    | Value | Is |
    |---|---|
    | `v(Value, Type)` | an rvalue: Value is an IR value, Type a C type |
    | `lv(Addr, Type)` | an object at Addr, a `p` value: an lvalue, or a member of a struct rvalue |
    | `fd(Callee, Type)` | a function designator; Callee is an IR value, `global(Symbol)` for a named function |

    ## State

    The lowering nonterminals describe a one-element list holding the
    state, accessed through the semicontext nonterminals state//1 and
    state//2 and called with phrase/3 at the entry points. The state is
    `st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)`:

    | Field | Is |
    |---|---|
    | Env | the c_types environment `e(Ords, Tags, Defs, Next)` |
    | Cur | `cur(Label, Phis)`, the open block, or `none` after a jump; dead code then opens an unreachable block |
    | Insts, Blocks | reversed instructions and blocks, temporarily paired with origin IDs |
    | Allocs | `build(RevAllocs, ActiveOrigins, OriginCounter, RevRecords, index(Bindings, Hints, ActiveLoc))`; independent of executable names |
    | N | the counter for fresh temporaries and labels |
    | Labels | an assoc from C goto labels to IR labels |
    | Cases | the enclosing switch's `case(Value, Label)` and `default(Label)` |

    The context argument Ctx is
    `ctx(Function, ReturnType, Break, Continue, Loc)`, where Break and
    Continue are `some(Label)`, or `none` outside a loop or switch.

    ## The environment

    Besides what c_types keeps there, the environment's Defs hold:

    - `gdef(Symbol)`: a global definition;
    - `lit(Symbol)`: a string literal;
    - `deferred(Symbol)`: a static inline function, lowered only if
      something refers to it.

    Next numbers string and compound literals as well as struct ids.

    ## Variable names

    | Name | Is |
    |---|---|
    | State0, State | `st/8` terms |
    | Env0 ... Env | the environment |
    | Ctx | the context |
    | Loc | a source location |
    | R | a `v`, `lv` or `fd` value term; Value0 is one before conversion |
    | V | an IR value |
    | L-prefixed names | IR labels |
    | Ebs | eightbytes, `eb(Offset, Bytes, Class)` |
    | S0 ... S | `s(Env, Chunks, End)` in the static initializer predicates |
*/
:- module(c_lower, [c_module/2, c_toplevel_asm/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(library(dcgs)).
:- use_module(c_types).
:- use_module(ir, [op_kind/2, narrow_type/3, width_bytes/2]).
:- use_module(c_parse, [compound_assignment/2]).
:- use_module(cfg, [inst_def/2]).

%! c_module(+Items, -Module)
%
%  Module is the IR module of the top-level Items from c_parse:
%  module(Funcs) with the functions followed by the data of every
%  global and string literal. Throws a semantic error for C that
%  nanofil cannot lower.
c_module(Items00, module(Funcs)) :-
    empty_env(Env0),
    builtin_declarations(Builtins),
    append(Builtins, Items00, ItemsB),
    maplist(weakref_item(ItemsB), ItemsB, Items0),
    weak_aliases(Items0, Items, Aliases),
    findall(Name, external_inline_declaration(Items, Name), Names0),
    sort(Names0, ExternalNames),
    foldl(top_item(ExternalNames), Items, Funcss, Env0, Env1),
    foldl(weak_alias_def(ExternalNames), Aliases, AliasFuncss, Env1, Env),
    append(Funcss, Funcs0a), append(AliasFuncss, Funcs0b), append(Funcs0a, Funcs0b, Funcs0),
    with_used_inlines(Funcs0, Env, Funcs1),
    weak_symbols(Items0, Env, Weak),
    weak_linkage(Weak, Funcs1, Funcs).

%! c_toplevel_asm(+Items, -Lines)
%
%  Lines are the assembly lines for the top-level asm among Items, as
%  clang's Fil-C compiles module asm (FilPizlonator.cpp,
%  compileModuleAsm): blank lines vanish, and `.symver L, V` becomes
%  `.symver pizlonated_L, pizlonated_V`, versioning the symbol of L's
%  getter, as filcc's objects do (docs/abi-findings.md, *Top-level
%  asm*). filcc also takes its own .filc_* directives and crashes on any
%  other text; nanofil refuses everything but .symver, the one directive
%  the survey's packages use (xz's and libapparmor's compatibility
%  versions; libressl's empty asm("")).
c_toplevel_asm(Items, Lines) :-
    findall(Loc-L,
            ( member(toplevel_asm(Loc, Template), Items),
              split_at(Template, [0'\n], Ls),
              member(L, Ls) ),
            Pairs),
    maplist(module_asm_line, Pairs, Liness),
    append(Liness, Lines).

module_asm_line(Loc-L, Lines) :-
    atom_codes(A, L), atom_chars(A, Cs),
    (   phrase((ma_blank, ma_end), Cs) -> Lines = []
    ;   phrase((ma_blank, ".symver", ma_white, ma_blank, ma_id(Local), ma_blank, ",",
                ma_blank, ma_id(Versioned), ma_blank, ma_end), Cs)
    ->  atom_chars(LA, Local), atom_chars(VA, Versioned),
        format(atom(Line), '.symver pizlonated_~w, pizlonated_~w', [LA, VA]),
        Lines = [Line]
    ;   sema_error(Loc, 'top-level asm "~w" is not supported; only .symver is', [A])
    ).

% MATokenizer's whitespace (but newline) and identifiers: a letter or _
% and then letters, digits, _, $, @ and dots.
ma_blank --> [C], { C \== '\n', char_type(C, space) }, !, ma_blank.
ma_blank --> [].
ma_white --> [C], { C \== '\n', char_type(C, space) }.
ma_id([C|Cs]) --> [C], { char_code(C, N), N < 128, char_type(C, csymf) }, !, ma_id_rest(Cs).
ma_id_rest([C|Cs]) --> [C], { char_code(C, N), N < 128, ( char_type(C, csym) ; memberchk(C, ['$', '@', '.']) ) }, !, ma_id_rest(Cs).
ma_id_rest([]) --> [].
ma_end([], []).

/* Weak symbols (GCC's weak attribute and #pragma weak; C11 J.5.11 lists
   such extensions as common, not standard). A name declared weak in any
   declaration of the translation unit, before or after its definition,
   is a weak symbol: its definition has linkage weak (ir.pl), which a
   strong definition elsewhere replaces, and if the unit only declares
   it, its uses refer to it through data of linkage extern(weak), so
   that it is null when no object of the program defines it, as clang's
   are (docs/abi-findings.md, *Weak symbols*). A weak alias,
   `__attribute__((weak, alias("t")))` or `#pragma weak n = t`, is a weak
   definition of its own name that calls t. Weak static and thread-local
   names are refused. */
weak_attr(Specs) :-
    member(attr([group(Tokens)]), Specs),
    member(id(W), Tokens), memberchk(W, [weak, '__weak__']), !.

% weak_aliases(+Items0, -Items, -Aliases): Items is Items0 with each weak
% alias declaration an ordinary declaration of its name, and Aliases its
% alias(Loc, Specs, Dcl, Target) terms, defined after the last item.
weak_aliases(Items0, Items, Aliases) :- weak_aliases(Items0, Items0, Items, Aliases).
weak_aliases(_, [], [], []).
weak_aliases(All, [decl(Loc, Specs, Inits)|Is0], [decl(Loc, Specs1, Inits)|Is],
             [alias(Loc, Specs1, Inits, Target)|As]) :-
    weak_attr(Specs), alias_target(Specs, Target), !,
    exclude(alias_attr, Specs, Specs1),
    weak_aliases(All, Is0, Is, As).
weak_aliases(All, [pragma_weak(Loc, Name, Target)|Is0], Is, [Alias|As]) :-
    Target \== none, !,
    (   member(decl(_, Specs0, Inits), All),
        Inits = [init(dcl(some(Name), _, _), none)]
    ->  exclude(alias_attr, Specs0, Specs),
        Alias = alias(Loc, Specs, Inits, Target)
    ;   sema_error(Loc, '#pragma weak ~w = ~w needs a declaration of ~w', [Name, Target, Name])
    ),
    weak_aliases(All, Is0, Is, As).
weak_aliases(All, [I|Is0], [I|Is], As) :- weak_aliases(All, Is0, Is, As).
alias_attr(attr([group(Tokens)])) :-
    member(id(Word), Tokens), memberchk(Word, [alias, '__alias__']), !.

% weak_alias_def(+ExternalNames, +Alias, -Funcs, +Env0, -Env): Funcs
% define the alias's own symbol, calling its target with its arguments.
weak_alias_def(ExternalNames, alias(Loc, Specs, Inits, Target), Funcs, Env0, Env) :-
    (   Inits = [init(dcl(some(Name), DclType, none), none)] -> true
    ;   sema_error(Loc, 'alias is supported only for one prototyped, non-variadic function', [])
    ),
    decl_types(Specs, Inits, [d(_, Type, _, _, _)], Env0, _),
    (   Type = func(Ret, _, fixed) -> true
    ;   sema_error(Loc, 'alias is supported only for functions, not ~w', [Name])
    ),
    alias_wrapper_syntax(Loc, Name, Specs0, DclType, Type, Specs, RetSyntax, Ps, Env0, Env1),
    findall(param(PSpecs, dcl(some(A), S, PAsm)) - id(A),
            ( nth0(I, Ps, param(PSpecs, dcl(_, S, PAsm))),
              format(atom(A), '__nanofil_alias_arg~w', [I]) ),
            Named),
    pairs_keys_values(Named, NamedPs, Args),
    atom_concat('__nanofil_alias_', Name, Self),
    Call = call(id(Target), Args),
    (   Ret == void -> Stmt = expr(Call) ; Stmt = return(Call) ),
    exclude(alias_spec, Specs0, DefSpecs),
    top_item(ExternalNames,
             fundef(Loc, DefSpecs,
                    dcl(some(Self), func(RetSyntax, params(NamedPs, fixed)), asm(Name)),
                    at(Loc, block([at(Loc, Stmt)]))),
             Funcs, Env1, Env).

% weak_symbols(+Items, +Env, -Weak): Weak is the ordset of the symbols
% of the names Items declare weak, each Sym-Kind, Kind fn or data.
weak_symbols(Items, Env, Weak) :-
    findall(Loc-Name, weak_name(Items, Loc, Name), LNs),
    foldl(weak_symbol(Env), LNs, Weak0, []),
    sort(Weak0, Weak).
weak_name(Items, Loc, Name) :-
    member(Item, Items),
    (   Item = pragma_weak(Loc, Name, _)
    ;   Item = decl(Loc, Specs, Inits), weak_attr(Specs),
        member(init(dcl(some(Name), _, _), _), Inits)
    ;   Item = fundef(Loc, Specs, dcl(some(Name), _, _), _), weak_attr(Specs)
    ).
weak_symbol(Env, Loc-Name) -->
    (   { lookup_ordinary(Env, Name, fn(_, Sym, Linkage)) }
    ->  { weak_public(Loc, Name, Linkage) }, [Sym-fn]
    ;   { lookup_ordinary(Env, Name, gvar(_, Sym, Storage, _)) }
    ->  {   Storage = thread_local(_)
        ->  sema_error(Loc, 'weak thread-local variable ~w is not supported', [Name])
        ;   Storage == static -> weak_public(Loc, Name, local)
        ;   true
        },
        [Sym-data]
    ;   []                  % #pragma weak of an undeclared name: unused
    ).
weak_public(Loc, Name, local) :- !,
    sema_error(Loc, 'weak declaration of ~w must have external linkage', [Name]).
weak_public(_, _, _).

% weak_linkage(+Weak, +Items0, -Items): Items is Items0 with the weak
% symbols' definitions weak, and an extern(weak) declaration of each
% one Items0 refers to without defining it.
weak_linkage([], Items, Items) :- !.
weak_linkage(Weak, Items0, Items) :-
    maplist(weak_item(Weak), Items0, Items1),
    findall(data(Sym, extern(weak), 1, []),
            ( member(Sym-_, Weak),
              \+ memberchk(func(Sym, _, _, _, _), Items0),
              \+ memberchk(data(Sym, _, _, _), Items0),
              once(item_ref(Items0, Sym)) ),
            Decls),
    append(Items1, Decls, Items).
weak_item(Weak, func(S, export, R, Ps, Bs), func(S, weak, R, Ps, Bs)) :-
    memberchk(S-_, Weak), !.
weak_item(Weak, data(S, export, A, Is), data(S, weak, A, Is)) :-
    memberchk(S-_, Weak), !.
weak_item(Weak, data(S, ro(export), A, Is), data(S, ro(weak), A, Is)) :-
    memberchk(S-_, Weak), !.
weak_item(_, Item, Item).

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
% GNU89 mode (NANOFIL_STD=gnu89: -std=c90, gnu90 or -fgnu89-inline,
% where clang predefines __GNUC_GNU_INLINE__) gives every inline body
% the GNU rule, as glibc's extern __inline atoi relies on.
external_inline_body(Specs, Storage, Name, ExternalNames) :-
    (   (   getenv('NANOFIL_STD', gnu89)
        ;   member(attr([group(Attrs)]), Specs),
            member(id(Attr), Attrs),
            memberchk(Attr, [gnu_inline, '__gnu_inline__'])
        )
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
    findall(Sym, func_symbol(Funcs0, Sym), Defined0),
    sort(Defined0, Defined),
    used_inlines(Funcs0, Defined, Env0, New, Env),
    global_data(Env, Data0),
    append(Funcs0, New, Funcs),
    % A constructor or destructor attribute on a function this unit only
    % declares registers nothing, as in clang, which registers one when
    % it emits the definition (libgpg-error's header declares
    % gpg_err_init so in every unit).
    exclude(undefined_init(Funcs), Data0, Data),
    append(Funcs, Data, Items).

undefined_init(Funcs, data(_, init(_, _), _, [item(p, sym(Sym, _))])) :-
    \+ memberchk(func(Sym, _, _, _, _), Funcs).

% used_inlines(+Scan, +Defined, +Env0, -New, -Env): New are the deferred
% inline functions that the functions Scan or the global data refer to
% and that are not in the ordset Defined, then those the new ones (or
% data they add) refer to, and so on. Each round scans only the
% functions the previous one lowered, and the sorted references are
% looked up once: rescanning every function per round, with a scan of
% the functions per reference, was quadratic for SQLite.
used_inlines(Scan, Defined, Env0, New, Env) :-
    env_defs(Env0, Defs),
    global_data(Env0, Data),
    findall(Sym, ( item_ref(Scan, Sym) ; item_ref(Data, Sym) ), Refs0),
    sort(Refs0, Refs1),
    ord_subtract(Refs1, Defined, Refs),
    include(deferred_def(Defs), Refs, Syms),
    (   Syms == []
    ->  New = [], Env = Env0
    ;   foldl(lower_inline, Syms, Newss, Env0, Env1),
        append(Newss, New0),
        findall(Sym, func_symbol(New0, Sym), Lowered0),
        sort(Lowered0, Lowered),
        ord_union(Defined, Lowered, Defined1),
        used_inlines(New0, Defined1, Env1, New1, Env),
        append(New0, New1, New)
    ).

func_symbol(Items, Sym) :- member(func(Sym, _, _, _, _), Items).
deferred_def(Defs, Sym) :- get_assoc(deferred(Sym), Defs, _).

% item_ref(+Items, -Sym): some function or data item of Items refers to
% symbol Sym (nondet, with repeats).
item_ref(Items, Sym) :-
    member(Item, Items),
    (   Item = func(_, _, _, _, Blocks),
        member(block(_, _, Insts, _), Blocks),
        member(Inst, Insts),
        (   Inst = let(_, _, _, Args), member(global(Sym), Args)
        ;   Inst = call(_, global(Sym), _)
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
top_item(_, pragma_weak(_, _, _), [], Env, Env) :- !.
top_item(_, toplevel_asm(_, _), [], Env, Env) :- !.
top_item(_, static_assert(Loc, Expr, _), [], Env, Env) :- !,
    static_assert(Loc, Expr, Env).
top_item(_, decl(_, Specs, [init(Dcl, none)]), [], Env, Env) :-
    overload(Specs, Dcl, Env), !.
top_item(ExternalNames, fundef(Loc, Specs, dcl(some(Name), func(Ret, knr(Names, Decls)), Asm),
                                at(BL, block(Items))), Funcs, Env0, Env) :- !,
    % A K&R definition is lowered as the prototyped one knr_definition/6
    % rewrites it to.
    (   lookup_ordinary(Env0, Name, fn(func(_, Ps, _), _, _)), Ps \== unspecified
    ->  Prototyped = true
    ;   Prototyped = false
    ),
    knr_definition(Loc, knr(Names, Decls), Prototyped, Env0, Params, Locals),
    append(Locals, Items, Items1),
    top_item(ExternalNames, fundef(Loc, Specs, dcl(some(Name), func(Ret, Params), Asm),
                                   at(BL, block(Items1))), Funcs, Env0, Env).
top_item(_, fundef(_, Specs, Dcl, _), [], Env, Env) :-
    overload(Specs, Dcl, Env), !.
top_item(ExternalNames, decl(Loc, Specs, Inits), Funcs, Env0, Env) :-
    alias_target(Specs, Target), !,
    alias_decl(ExternalNames, Loc, Specs, Inits, Target, Funcs, Env0, Env).
top_item(_, decl(Loc, Specs, Inits), [], Env0, Env) :- !,
    catch(decl_types(Specs, Inits, Decls, Env0, Env1), not_constant,
          sema_error(Loc, 'array size is not a constant', [])),
    foldl(global_decl(Loc), Decls, Env1, Env2),
    foldl(init_decl(Loc, Specs), Decls, Env2, Env).
top_item(ExternalNames, fundef(Loc, Specs, dcl(some(Name), DclType, Asm), Body), Funcs,
         Env0, Env) :-
    decl_types(Specs, [init(dcl(some(Name), DclType, Asm), none)],
               [d(_, Type, Storage0, _, _)], Env0, Env1),
    prior_storage(Name, Storage0, Env1, Storage),
    global_decl(Loc, d(Name, Type, Storage, Asm, none), Env1, Env1a),
    init_decl(Loc, Specs, d(Name, Type, Storage, Asm, none), Env1a, Env2),
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
    ;   Storage == static
    ->  % One nanofil cannot lower is deferred as a static inline is:
        % clang emits an unreferenced static function not at all, and
        % headers (amxcomplexintrin.h) define ones nanofil refuses. A
        % reference lowers it again, which raises the error then.
        catch(function(Loc, Name, Type, DclType, Body, Env2, Env3, Funcs0),
              Error, ( deferrable(Error) -> true ; throw(Error) )),
        (   var(Funcs0)
        ->  Funcs = [],
            lookup_ordinary(Env2, Name, fn(_, Sym, _)),
            env_scope(Env2, Scope, _),
            put_def(deferred(Sym), df(Loc, Name, Type, DclType, Body, Scope),
                    Env2, Env)
        ;   Funcs = Funcs0, Env = Env3
        )
    ;   function(Loc, Name, Type, DclType, Body, Env2, Env, Funcs)
    ).

/* GNU's constructor and destructor attributes, with an optional
   priority: the function runs before main (after exit), as clang emits
   it: an .init_array (.fini_array) entry, with the priority in the
   section's name, whose native forwarder hands the function object to
   the Fil-C runtime. nanofil records init(Kind, Sym) with the priority
   (none without one), and global_data/2 makes a data item of linkage
   init(Kind, Priority) holding the function (ir.pl). The item refers to
   the function, so a static one is lowered even if deferred. */
init_decl(Loc, Specs, d(Name, func(_, _, _), _, _, _), Env0, Env) :-
    findall(Kind-Prio, init_attr(Specs, Kind, Prio), Inits), Inits \== [], !,
    lookup_ordinary(Env0, Name, fn(_, Sym, _)),
    foldl(init_def(Loc, Sym), Inits, Env0, Env).
init_decl(_, _, _, Env, Env).

init_def(Loc, Sym, Kind-Prio, Env0, Env) :-
    (   Prio = bad
    ->  sema_error(Loc, 'the ~w priority of ~w is not an integer from 0 to 65535', [Kind, Sym])
    ;   put_def(init(Kind, Sym), Prio, Env0, Env)
    ).

% init_attr(+Specs, -Kind, -Priority) is nondet: Specs carry GNU's
% constructor (Kind ctor) or destructor (dtor) attribute, with
% Priority an integer, none without one, or bad.
init_attr(Specs, Kind, Prio) :-
    member(attr(Tokens), Specs), is_list(Tokens),
    member(group(Group), Tokens),
    append(_, [id(Word)|Rest], Group),
    init_word(Word, Kind),
    (   Rest = [group(Arg)|_]
    ->  ( Arg = [int(Prio, _)], integer(Prio), between(0, 65535, Prio) -> true ; Prio = bad )
    ;   Prio = none
    ).

init_word(constructor, ctor).
init_word('__constructor__', ctor).
init_word(destructor, dtor).
init_word('__destructor__', dtor).

% rvals_discarded(+Args, +Ctx)//: evaluate Args for their effects.
rvals_discarded([], _) --> [].
rvals_discarded([A|As], Ctx) --> rval(A, Ctx, _), rvals_discarded(As, Ctx).

% deferrable(+Error): Error is a diagnostic of C that nanofil does not
% lower, not an internal failure, so a static function raising it can
% wait for a reference.
deferrable(nanofil_error(_)).

/* GCC's alias attribute: `int bg(int, char **) __attribute__((alias("fg")))`
   (dash's bgcmd). The name is bound to the target's symbol, as if
   declared with asm("fg"), so the translation unit's calls and
   addresses are the target's, as clang's are. An alias with external
   linkage also needs its own symbol for other translation units: Fil-C
   gives it only a getter that returns the target's function object;
   nanofil defines a function of the alias's name that calls the target
   with its arguments. Its address, seen from another translation unit,
   is therefore not the target's. Variable aliases, variadic or
   unprototyped function aliases and several declarators are refused. */
/* GNU's weakref(T), or weakref with alias(T), on a static declaration
   of N: N refers to the symbol T (GCC, Common Function Attributes,
   weakref), so the declaration is an extern one of N with asm label T.
   clang's reference is weak, null if no object defines T, unless the
   unit uses T otherwise; nanofil makes it weak when the unit does not
   declare T, so where it differs a missing T fails to link instead of
   reading null. Ruby's anyargs.h declares typed weakrefs of
   rb_define_method this way. */
weakref_item(All, decl(Loc, Specs0, [init(dcl(some(N), Syn, none), none)]),
             decl(Loc, Specs, [init(dcl(some(N), Syn, asm(T)), none)])) :-
    weakref_target(Specs0, T), !,
    (   memberchk(storage(static), Specs0) -> true
    ;   sema_error(Loc, 'weakref declaration of ~w must have internal linkage', [N])
    ),
    exclude(weakref_spec, Specs0, Specs1),
    (   member(decl(_, _, Is), All), member(init(dcl(some(T), _, _), _), Is) -> Weak = []
    ;   member(fundef(_, _, dcl(some(T), _, _), _), All) -> Weak = []
    ;   Weak = [attr([group([id(weak)])])]
    ),
    append([[storage(extern)], Weak, Specs1], Specs).
weakref_item(_, Item, Item).

weakref_target(Specs, T) :-
    member(attr([group(Tokens)]), Specs),
    append(_, [id(W)|Rest], Tokens), memberchk(W, [weakref, '__weakref__']), !,
    (   Rest = [group([str(Bytes)])|_] -> atom_codes(T, Bytes)
    ;   alias_target(Specs, T)
    ).

weakref_spec(storage(static)).
weakref_spec(attr([group(Tokens)])) :-
    member(id(W), Tokens), memberchk(W, [weakref, '__weakref__', alias, '__alias__']), !.

alias_target(Specs, Target) :-
    member(attr([group(Tokens)]), Specs),
    append(_, [id(Word), group(Arg)|_], Tokens),
    memberchk(Word, [alias, '__alias__']), !,
    Arg = [str(Bytes)], atom_codes(Target, Bytes).

alias_decl(ExternalNames, Loc, Specs, Inits, Target, Funcs, Env0, Env) :-
    (   Inits = [init(dcl(some(Name), DclType, none), none)] -> true
    ;   sema_error(Loc, 'alias is supported only for one prototyped, non-variadic function', [])
    ),
    decl_types(Specs, [init(dcl(some(Name), DclType, asm(Target)), none)],
               [d(_, Type, Storage, Asm, Init)], Env0, Env1),
    (   Type = func(Ret, _, fixed) -> true
    ;   sema_error(Loc, 'alias is supported only for functions, not ~w', [Name])
    ),
    global_decl(Loc, d(Name, Type, Storage, Asm, Init), Env1, Env2),
    (   Storage == static
    ->  Funcs = [], Env = Env2
    ;   % The alias's own symbol: a function that calls the target.
        alias_wrapper_syntax(Loc, Name, Specs0, DclType, Type, Specs, RetSyntax, Ps, Env2, Env3),
        findall(param(PSpecs, dcl(some(A), S, PAsm)) - id(A),
                ( nth0(I, Ps, param(PSpecs, dcl(_, S, PAsm))),
                  format(atom(A), '__nanofil_alias_arg~w', [I]) ),
                Named),
        pairs_keys_values(Named, NamedPs, Args),
        atom_concat('__nanofil_alias_', Name, Self),
        Call = call(id(Name), Args),
        (   Ret == void -> Stmt = expr(Call) ; Stmt = return(Call) ),
        exclude(alias_spec, Specs0, DefSpecs),
        top_item(ExternalNames,
                 fundef(Loc, DefSpecs,
                        dcl(some(Self), func(RetSyntax, params(NamedPs, fixed)), asm(Name)),
                        at(Loc, block([at(Loc, Stmt)]))),
                 Funcs, Env3, Env)
    ).

% alias_wrapper_syntax(+Loc, +Name, -WSpecs, +DclType, +Type, +Specs,
% -RetSyntax, -Params, +Env0, -Env): the syntax of the function that
% defines an alias's own symbol. A prototype declarator gives it; an
% alias declared through typeof (libapparmor's `extern
% typeof((f)) g __attribute__((alias("f")))`) takes it from its type,
% Type, each type named by a reserved typedef bound in Env.
alias_wrapper_syntax(_, _, Specs, func(RetSyntax, params(Ps, fixed)), _, Specs,
                     RetSyntax, Ps, Env, Env) :- !.
alias_wrapper_syntax(_, Name, WSpecs, base, func(Ret, PTs, fixed), Specs,
                     base, Ps, Env0, Env) :- !,
    exclude(type_spec_syntax, Specs, Others),
    format(atom(RetTd), '__nanofil_alias_ret_~w', [Name]),
    bind_ordinary(RetTd, typedef(Ret), Env0, Env1),
    WSpecs = [tname(RetTd)|Others],
    foldl(alias_param_syntax(Name), PTs, Ps, 0-Env1, _-Env).
alias_wrapper_syntax(Loc, _, _, _, _, _, _, _, _, _) :-
    sema_error(Loc, 'alias is supported only for one prototyped, non-variadic function', []).
alias_param_syntax(Name, PT, param([tname(Td)], dcl(none, base, none)), I0-Env0, I-Env) :-
    format(atom(Td), '__nanofil_alias_p~w_~w', [I0, Name]),
    bind_ordinary(Td, typedef(PT), Env0, Env),
    I is I0 + 1.
type_spec_syntax(tspec(_)).
type_spec_syntax(qual(_)).
type_spec_syntax(tname(_)).
type_spec_syntax(su(_, _, _, _)).
type_spec_syntax(enum(_, _)).
type_spec_syntax(typeof(_)).
type_spec_syntax(atomic(_)).

/* clang's overloadable attribute: glibc's _FORTIFY_SOURCE headers add
   overloads of open, open64 and openat chosen by arity, which C cannot
   express. nanofil has no overloading: a declaration or definition
   marked overloadable whose type is not compatible with the visible
   declaration of its name is skipped, and calls reach that function
   (glibc's open). glibc's overloads only check the flags before calling
   it, so a valid program behaves alike. A compatible overloadable
   declaration (glibc's printf wrappers) is an ordinary redeclaration. */
overload(Specs, dcl(some(Name), DclType, Asm), Env) :-
    member(attr([group(Tokens)]), Specs),
    member(id(Word), Tokens), memberchk(Word, [overloadable, '__overloadable__']), !,
    lookup_ordinary(Env, Name, fn(Visible, _, _)),
    decl_types(Specs, [init(dcl(some(Name), DclType, Asm), none)],
               [d(_, Type, _, _, _)], Env, _),
    \+ compatible_type(Visible, Type).

alias_spec(attr([group(Tokens)])) :-
    member(id(Word), Tokens), memberchk(Word, [alias, '__alias__']), !.
alias_spec(storage(extern)).

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
% Decl of a function or of an object with static or thread storage, and
% defines the object unless it is an extern without an initializer. A
% thread-local definition is data of linkage tls(L) (ir.pl).
global_decl(Loc, d(Name, Type1, Storage0, Asm, Init), Env0, Env) :-
    ( Asm = asm(Sym) -> true ; Sym = Name ),
    redeclared(Loc, Name, Sym, Type1, Env0, Type0),
    (   Storage0 = thread_local(Storage) -> Thread = tls ; Storage = Storage0, Thread = none ),
    (   Type0 = func(_, _, _)
    ->  (   Thread == tls                                   % 6.7.1p4
        ->  sema_error(Loc, 'function ~w cannot be _Thread_local', [Name])
        ;   true
        ),
        prior_storage(Name, Storage, Env0, Storage1),
        ( Storage1 == static -> Linkage = local ; Linkage = export ),
        (   Init \== none
        ->  sema_error(Loc, 'function ~w has an initializer', [Name])
        ;   true
        ),
        bind_ordinary(Name, fn(Type0, Sym, Linkage), Env0, Env)
    ;   static_type(Name, Type0, Loc),
        complete_array(Type0, Init, Type, Loc, Env0, none),
        bind_ordinary(Name, gvar(Type, Sym, Storage0, Init), Env0, Env1),
        (   Storage == extern, Init == none
        ->  Env = Env1
        ;   ( Storage == static -> Linkage0 = local ; Linkage0 = export ),
            thread_linkage(Thread, Linkage0, Linkage),
            define_global(Sym, Type, Linkage, Init, Loc, Env1, Env2),
            data_alignment(Name, Sym, Env2, Env)
        )
    ).

% prior_storage(+Name, +Storage0, +Env, -Storage): a function declared
% with Storage0 has Storage: static when Storage0 is not, and a visible
% declaration gave it internal linkage. A function declared without a
% storage class, or extern, takes the prior declaration's linkage (C11
% 6.2.2p4-5): libevent declares min_heap_ctor_ static inline and defines
% it without static.
prior_storage(Name, Storage0, Env, Storage) :-
    (   Storage0 \== static, lookup_ordinary(Env, Name, fn(_, _, local))
    ->  Storage = static
    ;   Storage = Storage0
    ).

% redeclared(+Loc, +Name, +Sym, +Type0, +Env, -Type): Type is what a
% declaration of Name (symbol Sym) as Type0 declares, given Name's
% visible declaration of the same symbol: their composite (C11 6.2.7p3),
% or a semantic error, as clang's, if they are of different kinds or
% incompatible types (6.7p4, 6.2.7p2). A declaration without one, or
% of another symbol (a block-scope static, an asm label), is Type0.
redeclared(Loc, Name, Sym, Type0, Env, Type) :-
    (   lookup_ordinary(Env, Name, Prev),
        ( Prev = fn(PType, PSym, _) ; Prev = gvar(PType, PSym, _, _) ),
        PSym == Sym
    ->  ( PType = func(_, _, _) -> K0 = function ; K0 = object ),
        ( Type0 = func(_, _, _) -> K = function ; K = object ),
        (   K0 == K
        ->  true
        ;   sema_error(Loc, 'redefinition of \'~w\' as different kind of symbol', [Name])
        ),
        (   composite_type(PType, Type0, Type, Env)    % a transparent union
        ->  true                                       % meets its members
        ;   Type0 = func(_, _, _)
        ->  sema_error(Loc, 'conflicting types for \'~w\'', [Name])
        ;   sema_error(Loc, 'redeclaration of \'~w\' with a different type', [Name])
        )
    ;   Type = Type0
    ).

% thread_linkage(+Thread, +Linkage0, -Linkage): the data linkage of a
% definition of linkage Linkage0, thread-local if Thread is tls.
thread_linkage(none, Linkage, Linkage).
thread_linkage(tls, Linkage, tls(Linkage)).

% static_type(+Name, +Type, +Loc): an object Name at file scope or with
% linkage may have Type: nanofil supports it, and it is not variably
% modified (C11 6.7.6.2p2).
static_type(Name, Type, Loc) :-
    supported(Type, Loc),
    (   vm_type(Type)
    ->  sema_error(Loc, '~w has a variably modified type at file scope or with linkage', [Name])
    ;   true
    ).

/* Definitions of globals live in the environment's Defs under
   gdef(Symbol), string literals under lit(Symbol); both survive block
   scopes. A tentative definition (no initializer) does not replace one
   with an initializer. */
% data_alignment(+Name, +Sym, +Env0, -Env): the data Sym of object Name
% is aligned to Name's alignment request (c_types' object_alignment/5),
% if it has one, the strictest of its declarations'.
data_alignment(Name, Sym, Env0, Env) :-
    (   lookup_ordinary(Env0, qalign(Name), A), integer(A)
    ->  env_defs(Env0, Defs),
        ( get_assoc(galign(Sym), Defs, A0) -> A1 is max(A, A0) ; A1 = A ),
        put_def(galign(Sym), A1, Env0, Env)
    ;   Env = Env0
    ).

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
                findall(item(Width, const(V)), member(V, Values), Items)
            ),
            LiteralData),
    findall(data(Name, init(Kind, Prio), 8, [item(p, sym(Sym, 0))]),
            (   member(init(Kind, Sym)-Prio, Pairs),
                format(atom(Name), '__nanofil_~w_~w', [Kind, Sym])
            ),
            InitData),
    append([GlobalData, LiteralData, InitData], Data).

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
    env_defs(Env0, Defs),
    ( get_assoc(galign(Sym), Defs, Requested) -> true ; Requested = 1 ),
    Align is max(Align0, Requested),
    ( get_assoc(initialized(Sym), Defs, Items)
    -> Env = Env0
    ; static_items(Type, Init, Loc, Env0, Env, Items)
    ).

%% Functions

% function(+Loc, +Name, +Type, +DclType, +Body, +Env0, -Env, -Func): Func
% is the IR function for the definition of Name with body Body.
% Lowering is deterministic; once/1 keeps a function's choicepoints from
% holding its states alive while the rest of the file is lowered.
% A type nanofil refuses (bad/1, from c_types) is reported at the
% function, unless a caller defers it (deferrable/1).
function(Loc, Name, Type, DclType, Body, Env0, Env, Func) :-
    catch(once(function_(Loc, Name, Type, DclType, Body, Env0, Env, Func)), bad(Why),
          sema_error(Loc, '~w uses a type nanofil does not support (~w)', [Name, Why])).

function_(Loc, Name, func(RetType, ParamTypes0, Variadic), DclType, Body,
         Env0, Env, [func(Sym, Linkage, RetClass, Params, Blocks), context(Sym, Records)]) :-
    lookup_ordinary(Env0, Name, fn(_, Sym, Linkage)),
    (   ParamTypes0 == unspecified
    ->  ParamTypes = []
    ;   ParamTypes = ParamTypes0
    ),
    ret_class(Loc, RetType, Env0, RetClass),
    param_names(DclType, Names),
    param_mins(DclType, Env0, Mins),
    statement_expression_jumps(Body, Loc),
    reflect_params(DclType, ParamTypes, Env0, ParamEnv0),
    label_values(Body, ParamEnv0, ParamEnv),
    source_location(Loc, SourceLoc),
    empty_assoc(Empty),
    State0 = st(ParamEnv, cur(start, []), [], [], 0, Labels, [],
                build([], [0], 1, [origin(0, SourceLoc, statement(function), [])],
                      index(Empty, Empty, SourceLoc))),
    empty_assoc(Labels),
    Ctx = ctx(Name, RetType, none, none, Loc),
    phrase(( sret_param(RetType, SretParams),
             params(Names, Mins, ParamTypes, Ctx, Params00),
             { length(SretParams, NSret) },
             pad_params(Params00, NSret, Params0),
             variadic_entry(Variadic, RetType-ParamTypes, SretParams, Params0),
             vm_params(Names, ParamTypes, Ctx),
             stmt(Body, Ctx),
             fall_off(RetType),
             computed_dispatch,
             vm_jumps
           ),
           [State0], [State]),
    append(SretParams, Params0, Params),
    State = st(EnvEnd, none, [], RevBlocks, _, _, _, build(RevAllocs, _, _, RevRecords, _)),
    env_scope(Env0, Scope, _),
    env_restore(Scope, EnvEnd, Env),
    reverse(RevBlocks, [block(start, [], Insts0, Jump)|Rest]),
    reverse(RevAllocs, Allocs),
    append(Allocs, Insts0, Insts),
    maplist(context_block, [block(start, [], Insts, Jump)|Rest], Blocks, Sites0),
    append(Sites0, Sites), reverse(RevRecords, RawRecords),
    exclude(is_hint, RawRecords, Origins),
    findall(T-H, member(hint(T, H), RawRecords), HintPairs), list_to_assoc(HintPairs, Hints),
    findall(S-Os, member(site(S, Os), Sites), SitePairs), list_to_assoc(SitePairs, SiteMap),
    findall(value(T, Hint, Os),
            ( ( member(param(_, tmp(T)), Params), Os = [0]
              ; member(block(L, Phis, Is, _), Blocks),
                ( member(phi(tmp(T), _, _), Phis), get_assoc(phi(T), SiteMap, Os)
                ; nth0(I, Is, Inst), inst_def(Inst, T),
                  get_assoc(inst(L, I), SiteMap, Os) ) ),
              ( get_assoc(T, Hints, H) -> Hint = H ; Hint = none ) ), Values),
    append([Origins, Values, Sites], Records).

is_hint(hint(_, _)).

context_block(block(L, Ps0, Is0, from(Os, J)), block(L, Ps, Is, J), Rs) :-
    maplist(context_phi, Ps0, Ps, PRs),
    context_insts(Is0, L, 0, Is, IRs),
    append([PRs, IRs, [site(jump(L), Os)]], Rs).
context_phi(from(Os, P), P, site(phi(T), Os)) :- P = phi(tmp(T), _, _).
context_insts([], _, _, [], []).
context_insts([from(Os, I)|Is0], L, N, [I|Is], [site(inst(L, N), Os)|Rs]) :-
    N1 is N + 1, context_insts(Is0, L, N1, Is, Rs).

% variadic_entry(+Variadic, +Types, +Sret, +Params)//: a variadic
% function takes the entry snapshot, a cursor past its fixed words. So
% does a function with a byval parameter, one whose parameters or
% result clang passes outside the fast signature (generic_only_type/2),
% or one of more than 16 words, which has no fast signature, unbound: the snapshot makes it
% generic-only, as clang makes it, and the packet it promotes to the
% heap holds the byval words, each pointer word with its capability.
variadic_entry(variadic, _, Sret, Params) -->
    { append(Sret, Params, All), length(All, N), Off is 8 * N },
    bind(builtin(va_args), tmp(va_args)),
    emit(let(tmp(va_args), p, va_args, [const(Off)])).
variadic_entry(fixed, RetType-Types, Sret, Params) -->
    env(Env),
    (   { (   member(Type, Types), abi_memory(Type), generic_only_type(Type, Env)
          ;   su(RetType), float_pair_type(RetType, Env)
          ;   x87_type(RetType, Env)
          ;   append(Sret, Params, All), length(All, NW), NW > 16
          ) }
    ->  { append(Sret, Params, All), length(All, N), Off is 8 * N },
        emit(let(tmp(va_args), p, va_args, [const(Off)]))
    ;   []
    ).

% ret_class(+Loc, +RetType, +Env, -Class): Class is the IR return class
% of a function returning RetType.
ret_class(_, void, _, void) :- !.
ret_class(_, ldouble, _, tuple([l, l])) :- !.
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
        { Params = [param(p, P)] }
    ;   { Params = [] }
    ).

% param_names(+DclType, -Names): Names are the parameter names, each
% some(Name) or none, from the function's own declarator: the outermost func, since declarator types
% are built outermost first.
param_names(func(_, unspecified), []) :- !.
param_names(func(_, params(Params, _)), Names) :-
    findall(Name, member(param(_, dcl(Name, _, _)), Params), Names).

% param_mins(+DclType, +Env, -Mins): each parameter's minimum alignment,
% its typedef's (inherited_alignment/4) or 1, as clang lays it out.
param_mins(func(_, unspecified), _, []) :- !.
param_mins(func(_, params(Params, _)), Env, Mins) :-
    findall(Min,
            ( member(param(Specs, dcl(_, Syntax, _)), Params),
              ( Syntax == base, inherited_alignment(Specs, base, Env, [align(Min)])
              -> true ; Min = 1 ) ),
            Mins).

% params(+Names, +Mins, +Types, +Ctx, -Params)//: Params are the IR parameters,
% and each named one is stored into a local. A struct or union comes in
% one word per eightbyte.
params([], _, [], _, []) --> [].
params([Name|Names], [Min|Mins], [Type|Types], Ctx, Params) -->
    { abi_memory(Type) },
    !,
    env(Env),
    { ctx_loc(Ctx, Loc), arg_words(Type, Env, Loc, Ebs) },
    fresh_params(Ebs, Params0, Values),
    su_param_local(Name, Type, Min, Ebs, Values),
    params(Names, Mins, Types, Ctx, Params1),
    { pad16_mark(Type, Env, Params0, Params2), append(Params2, Params1, Params) }.
params([Name|Names], [Min|Mins], [Type|Types], Ctx, [param(Class, P)|Params]) -->
    { ctx_loc(Ctx, Loc),
      supported(Type, Loc),
      (   type_class(Type, Class) -> true
      ;   sema_error(Loc, 'parameter of type ~w is not supported yet', [Type])
      ) },
    fresh(P),
    param_local(Name, Type, Min, P),
    params(Names, Mins, Types, Ctx, Params).

% su_param_local(+Name, +Type, +Min, +Ebs, +Values)// and
% param_local(+Name, +Type, +Min, +P)//: a named parameter of Type, which came
% in as the words Values (eightbytes Ebs) or the temporary P, is stored
% into a local it is bound to; an unnamed one is dropped.
su_param_local(none, _, _, _, _) --> [].
su_param_local(some(Name), Type, Min, Ebs, Values) -->
    local_slot(Type, Min, Addr),
    bind(Name, var(Addr, Type)),
    name_values(Values, Addr, piece),
    store_words(Ebs, Values, Addr).

param_local(none, _, _, _) --> [].
param_local(some(Name), Type, Min, P) -->
    local_slot(Type, Min, Addr),
    bind(Name, var(Addr, Type)),
    name_value(P, Addr, value),
    store_typed(Type, P, Addr).

% vm_params(+Names, +Types, +Ctx)//: on entry, the size expressions of
% each variably modified parameter are evaluated, in order, after every
% parameter is bound (C11 6.9.1p10); the parameter's binding then has
% the evaluated type.
vm_params([], [], _) --> [].
vm_params([Name|Names], [Type0|Types], Ctx) -->
    (   { Name = some(N), vm_type(Type0) }
    ->  env(Env),
        { lookup_ordinary(Env, N, var(Addr, _)) },
        realized(Type0, Type, Ctx),
        env(Env1), { bind_ordinary(N, var(Addr, Type), Env1, Env2) }, set_env(Env2)
    ;   []
    ),
    vm_params(Names, Types, Ctx).

% fresh_params(+Ebs, -Params, -Values)//: one fresh parameter per
% eightbyte; Values are their temporaries.
fresh_params([], [], []) --> [].
fresh_params([eb(_, _, Class)|Ebs], [param(Class, P)|Params], [P|Values]) -->
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
    ;   { RetType == ldouble } -> term(rets([const(0), const(0)]))
    ;   { su(RetType), ret_shape(RetType, Env, unknown, Shape) }
    ->  (   { Shape = words([_, _]) } -> term(rets([const(0), const(0)]))
        ;   { Shape = words(_) } -> term(ret(const(0)))
        ;   term(ret)
        )
    ;   term(ret(const(0)))
    ).

%% State primitives

% state(-S)//: S is the state. state(-S0, +S)//: the state is S0 and
% becomes S. The semicontext of the one-element state list.
state(S), [S] --> [S].

state(S0, S), [S] --> [S0].

% Metadata has its own counter; it never consumes a temporary or label.
build_state(B0, B) -->
    state(st(E, C, Is, Bs, N, Ls, Cs, B0), st(E, C, Is, Bs, N, Ls, Cs, B)).
active_origins(Os) --> build_state(build(A, Os, N, R, X), build(A, Os, N, R, X)).
metadata(Index) --> build_state(build(A, Os, N, R, Index), build(A, Os, N, R, Index)).
record(R) -->
    build_state(build(A, Os, N, Rs, X0), build(A, Os, N, [R|Rs], X)),
    { indexed_record(R, X0, X) }.

indexed_record(binding(Id, Name, T, Loc), index(B0, H, O), index(B, H, O)) :- !,
    put_assoc(Id, B0, binding(Id, Name, T, Loc), B).
indexed_record(hint(T, Hint), index(B, H0, O), index(B, H, O)) :- !,
    put_assoc(T, H0, Hint, H).
indexed_record(origin(_, _, _, _), X, X).

% The index's third part is the location of the active origin, the only
% one a binding asks for; an assoc of every origin's (half a million in
% SQLite) was a sixth of lowering. enter_origin//3 gives the parent's
% origins and location, which restore_origin//1 makes active again.
enter_origin(Loc0, Description, saved(Parent, ParentLoc)) -->
    build_state(build(A, Parent, N, Rs, index(B, H, ParentLoc)),
                build(A, [N], Next, Rs, index(B, H, Loc))),
    { Next is N + 1, source_location(Loc0, Loc) },
    record(origin(N, Loc, Description, Parent)).
restore_origin(saved(Os, Loc)) -->
    build_state(build(A, _, N, Rs, index(B, H, _)), build(A, Os, N, Rs, index(B, H, Loc))).
source_location(F:L, at(F, L)) :- !.
source_location(_, none).

binding_context(Name, var(tmp(B), _)) --> !,
    env(Env), metadata(index(_, _, Loc)),
    { expression_type(id(Name), Env, T) },
    record(binding(B, Name, T, Loc)), name_value(tmp(B), tmp(B), address).
binding_context(Name, gvar(_, Sym, _, _)) --> !,
    env(Env), metadata(index(Bindings, _, _)),
    ( { get_assoc(global(Sym), Bindings, _) } -> []
    ; { expression_type(id(Name), Env, T) },
      record(binding(global(Sym), Name, T, none)) ).
binding_context(_, _) --> [].

name_values([], _, _) --> [].
name_values([V|Vs], B, Role) --> name_value(V, B, Role), name_values(Vs, B, Role).
name_value(tmp(T), tmp(B), Role) --> !,
    metadata(index(Bindings, Hints, _)),
    ( { address_binding(B, Bindings, Hints, Id), \+ get_assoc(T, Hints, _) }
    -> record(hint(T, named(Id, Role)))
    ; [] ).
name_value(_, _, _) --> [].

address_binding(B, Bindings, Hints, Id) :-
    ( get_assoc(B, Bindings, _) -> Id = B ; get_assoc(B, Hints, named(Id, address)) ).

stored_name(store(W, V, Addr)) --> !, access_name(store(W), V, Addr).
stored_name(let(V, K, load(Op), [Addr])) --> !, access_name(load(K, Op), V, Addr).
stored_name(_) --> [].

% A zero-offset field or partial access is not the whole C object.
access_name(Access, V, tmp(A)) --> !,
    metadata(index(Bs, Hs, _)),
    ( { address_binding(A, Bs, Hs, B), get_assoc(B, Bs, binding(_, _, T, _)),
        unqualified(T, U), scalar_access(Access, U) }
    -> name_value(V, tmp(A), value)
    ; [] ).
access_name(_, _, _) --> [].
scalar_access(store(W), T) :- store_width(T, W).
scalar_access(load(K, Op), T) :- load_op(T, K, Op).

typed_origin(X, Ctx, Parent) -->
    env(Env),
    { X =.. [Category, Type, Node], ctx_loc(Ctx, Loc),
      shallow_node(Node, Env, Form),
      ( ground(Type) -> Description = typed(Category, Type, Form)
      ; Description = generated(lower, Form) ) },
    enter_origin(Loc, Description, Parent).

% Keep the operation and resolved binding, not recursive typed trees.
shallow_node(id(Name), Env, binding(B)) :-
    lookup_ordinary(Env, Name, var(tmp(B), _)), !.
shallow_node(id(Name), Env, binding(global(Sym))) :-
    lookup_ordinary(Env, Name, gvar(_, Sym, _, _)), !.
shallow_node(Node, _, Form) :-
    Node =.. [Op|Args], include(atomic, Args, Atoms), Form =.. [Op|Atoms].

result_name(val(_, load(obj(_, id(Name)))), v(V, _)) --> !,
    env(Env),
    ( { lookup_ordinary(Env, Name, var(Addr, _)) } -> name_value(V, Addr, value) ; [] ).
result_name(_, _) --> [].

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
    set_env(Env),
    binding_context(Name, Value).

fresh(tmp(Temp)) -->
    state(st(Env, Cur, Insts, Blocks, N0, Labels, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)),
    { N is N0 + 1,
      number_codes(N0, Cs), atom_codes(Temp, [0'v|Cs]) }.

label(Label) -->
    state(st(Env, Cur, Insts, Blocks, N0, Labels, Cases, Allocs),
          st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs)),
    { N is N0 + 1,
      number_codes(N0, Cs), atom_codes(Label, [0'L|Cs]) }.

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

% emit(+Inst)//: append Inst with its active typed origin. These private
% wrappers disappear before c_module/2 returns; they are never IR.
emit(Inst) --> ensure_live, stored_name(Inst), active_origins(Os), push_inst(from(Os, Inst)).

push_inst(Inst) -->
    state(st(Env, Cur, Insts, Blocks, N, Labels, Cases, Allocs),
          st(Env, Cur, [Inst|Insts], Blocks, N, Labels, Cases, Allocs)).

% term(+Jump)//: end the current block with Jump.
term(Jump) --> ensure_live, close_block(Jump).

close_block(Jump) -->
    active_origins(Os),
    state(st(Env, cur(Label, Phis), Insts, Blocks, N, Labels, Cases, Allocs),
          st(Env, none, [], [block(Label, Phis, BlockInsts, from(Os, Jump))|Blocks],
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
cur_fallthrough(cur(_, _), Label) --> term(goto(Label)).

% start_phi(+Label, +Phis)//: begin block Label, reached only by jumps.
start_phi(Label, Phis) -->
    active_origins(Os), { maplist(from_origins(Os), Phis, Located) },
    set_cur(cur(Label, Located)).

from_origins(Os, I, from(Os, I)).

% here(-Label)//: Label is the current block's label.
here(Label) --> ensure_live, cur(cur(Label, _)).

add_alloc(Inst) -->
    build_state(build(As, Os, N, Rs, X), build([from(Os, Inst)|As], Os, N, Rs, X)).

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

% let(+Class, +Op, +Args, -Dest)//: emit an instruction into Dest, a
% fresh temporary.
let(Class, Op, Args, Dest) -->
    fresh(Dest),
    emit(let(Dest, Class, Op, Args)).

% vla_slot(+Type, +Min, +Ctx, -Addr)//: Addr points at a new object of the
% variable length array Type, allocated where its declaration is
% reached, with its length as evaluated then (C11 6.2.4p7, 6.7.6.2p5),
% aligned to Min at least.
vla_slot(Type, Min, Ctx, Addr) -->
    extent(Type, Ctx, Size),
    env(Env),
    { element_type(Type, Elem),
      catch(type_size_align(Elem, Env, _, Align0), bad(Why), throw(nanofil_error(Why))),
      Align is max(4, max(Min, Align0)) },
    let(p, alloc(Align), [Size], Addr).

/* laundered(+XV, -XP, -Hole, -XV1): the integer value tree XV, cast to
   a pointer, takes the capability of the one pointer XP that a cast to
   an integer inside it converts, as Fil-C's pointer-as-int laundering
   does: XV1 is XV with that pointer replaced by val(T, lowered(Hole)),
   Hole the value XP lowers to. The pointer is the capability source
   through integer conversions, unary -, + and ~, and arithmetic and
   bitwise binary operators; a load, call, comparison, constant or
   anything else contributes none. The same pointer named more than
   once, without side effects (Fil-C sees one SSA value), is one source
   and is read once. Two different sources, or a pointer difference, or
   a source passed through ?:, a comma, an assignment or a statement
   expression, make it fail (Fil-C's TOP), as does none. XP is
   evaluated first: the operands of those operators are unsequenced, so
   that is an order C allows. Fil-C infers on SSA, after the optimizer
   has made locals values, so a source flowing through a local variable
   is not found here. */
laundered(XV, XP, Hole, XV1) :-
    launder_source(XV, XV1, [XP-Hole|Sources]),
    XP \== top,
    (   Sources == [] -> true
    ;   pure_tree(XP),
        maplist(same_source(XP, Hole), Sources)
    ).

same_source(XP, Hole, S-Hole) :- S == XP.

% launder_source(+XV, -XV1, -Sources): Sources are the XP-Hole pairs of
% the capability sources in integer tree XV, each replaced in XV1, with
% top-_ for a source Fil-C would merge into TOP.
launder_source(val(T, cast(TN, X)), val(T, cast(TN, XH)), Sources) :-
    \+ unqualified(T, bool), !,
    (   lowered(X, ptr(_))
    ->  tree_type(X, PT), XH = val(PT, lowered(Hole)), Sources = [X-Hole]
    ;   lowered(X, IT), int_type(IT)
    ->  launder_source(X, XH, Sources)
    ;   XH = X, Sources = []
    ).
launder_source(val(T, bin(Op, A, B)), val(T, bin(Op, A1, B1)), Sources) :-
    memberchk(Op, [add, sub, mul, div, mod, and, or, xor, shl, shr]),
    lowered(A, TA), int_type(TA), lowered(B, TB), int_type(TB), !,
    launder_source(A, A1, SA),
    launder_source(B, B1, SB),
    append(SA, SB, Sources).
launder_source(val(T, un(Op, A)), val(T, un(Op, A1)), Sources) :-
    memberchk(Op, [neg, plus, bnot]), !,
    launder_source(A, A1, Sources).
launder_source(X, X, Sources) :-
    (   passes_pointer_int(X) -> Sources = [top-_] ; Sources = [] ).

% passes_pointer_int(+X): X is a pointer difference, or passes on a
% value (?:, comma, assignment, statement expression) whose tree holds
% a pointer converted to an integer or a pointer difference.
passes_pointer_int(val(_, bin(sub, A, B))) :-
    lowered(A, ptr(_)), lowered(B, ptr(_)), !.
passes_pointer_int(val(_, Node)) :-
    functor(Node, F, _),
    memberchk(F, [cond, gcond, comma, assign, stmtexpr]),
    pointer_int_within(Node), !.

pointer_int_within(val(T, cast(_, X))) :-
    unqualified(T, IT), int_type(IT), lowered(X, ptr(_)), !.
pointer_int_within(X) :- passes_pointer_int(X), !.
pointer_int_within(X) :-
    compound(X), X =.. [_|Args], member(A, Args), pointer_int_within(A), !.

% pure_tree(+X): reading X twice is reading it once: X has no side
% effects and reads no volatile or _Atomic object.
pure_tree(val(_, int(_))).
pure_tree(val(_, load(X))) :-
    tree_type(X, T), \+ qualified_with(T, volatile), \+ atomic_qualified(T),
    pure_place(X).
pure_tree(val(_, decay(X))) :- pure_place(X).
pure_tree(val(_, addr(X))) :- pure_place(X).
pure_tree(val(_, cast(_, X))) :- pure_tree(X).
pure_tree(val(_, un(Op, X))) :- memberchk(Op, [neg, plus, bnot, not]), pure_tree(X).
pure_tree(val(_, bin(Op, A, B))) :-
    \+ memberchk(Op, [div, mod]), pure_tree(A), pure_tree(B).
pure_tree(val(_, member(XS, _))) :- pure_tree(XS).

pure_place(obj(_, id(_))).
pure_place(obj(_, member(X, _))) :- pure_place(X).
pure_place(obj(_, deref(XV))) :- pure_tree(XV).

qualified_with(qualified(Qs, _), Q) :- memberchk(Q, Qs).

% element_type(+Type, -Elem): Elem is the innermost element type of
% array Type, or Type itself.
element_type(array(T, _), E) :- !, element_type(T, E).
element_type(T, T).

% local_slot(+Type, -Addr)//: Addr points at a new local object of
% Type, an alloc in the entry block; local_slot(+Type, +Min, -Addr)//
% aligns it to Min at least.
local_slot(Type, Addr) --> local_slot(Type, 1, Addr).
local_slot(Type, Min, Addr) -->
    env(Env),
    { catch(type_size_align(Type, Env, Size0, Align0), bad(Why),
            throw(nanofil_error(Why))),
      Align is max(4, max(Align0, Min)),
      Size is max(Size0, 1) },
    fresh(Addr),
    add_alloc(let(Addr, p, alloc(Align), [const(Size)])).

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
% Lowering a statement is deterministic: committing to it keeps the
% choicepoints of a large function (sqlite3WhereCodeOneLoopStart) from
% holding every earlier state alive.
stmt(Stmt, Ctx, S0, S) :- once(stmt_at(Stmt, Ctx, S0, S)).

stmt_at(at(Loc, Stmt), Ctx0) -->
    { ctx_at(Ctx0, Loc, Ctx), functor(Stmt, Kind, _) },
    enter_origin(Loc, statement(Kind), Parent),
    stmt_(Stmt, Ctx), restore_origin(Parent).

% Declaration and loop helpers update the enclosing source context.
located(Kind, Loc) --> enter_origin(Loc, statement(Kind), _).

% loop_located(+Ctx)//: a loop's condition or step, in a block of its
% own after the body, is at the loop statement's location.
loop_located(Ctx) --> { ctx_loc(Ctx, Loc) }, located(loop, Loc).

stmt_(block(Items), Ctx) -->
    save_scope(Scope), env(Env), { cleanup_keys(Env, Outer) },
    items(Items, Ctx),
    scope_cleanups(Outer),
    restore_scope(Scope).
stmt_(null, _) --> [].
/* An asm whose template is blank, as filcc's handleInlineAsm counts it,
   emits no instruction. filcc passes it through when no operand is a
   pointer, so its operands are values the asm reads or writes in
   registers: "+r" or "+g" reads the lvalue and writes the same value
   back, "=r" writes an unspecified value, which leaving the object
   unchanged is, and "r", "g", "i" or "n" inputs are evaluated. These
   are libgcrypt's and xxhash's optimization barriers. A "memory" or
   "cc" clobber needs nothing: no pass of nanofil keeps a value of
   escaped memory across an instruction (promote takes only locals
   whose address does not escape, copy and the backend's caches only
   temporaries), so every access stays in program order as across a
   call. A pointer operand, another constraint or clobber, and asm goto
   are refused. */
stmt_(asm_empty(Outs, Ins, Clobbers, Goto), Ctx) --> !,
    { ctx_loc(Ctx, Loc),
      (   Goto == goto
      ->  sema_error(Loc, 'asm goto is not supported', [])
      ;   true
      ),
      forall(member(C, Clobbers),
             (   memberchk(C, [memory, cc]) -> true
             ;   sema_error(Loc, 'an asm clobber other than "memory" or "cc" is not supported (~w)', [C])
             )) },
    asm_outputs(Outs, Ctx),
    asm_inputs(Ins, Ctx).

/* Any other asm runs instructions nanofil cannot check. filcc's
   handleInlineAsm compiles some of them to a run-time error and passes
   the rest through after validateSafeInlineAsm; nanofil passes none
   through. Where filcc certainly refuses, nanofil calls zsafety_error
   with filcc's message up to its colon (filcc follows it with the
   call's LLVM IR, whose attribute and metadata numbers nanofil has no
   counterpart for; it uses the template), so a program that never runs
   the asm, such as GLib's G_BREAKPOINT behind a debug flag, behaves as
   under filcc. Everywhere else, cpuid among them, which filcc may
   accept, nanofil refuses the asm at compile time
   (asm_runtime_reason/6). */
stmt_(asm(Template, Outs, Ins, Clobbers, Goto), Ctx) --> !,
    env(Env0),
    { ctx_loc(Ctx, Loc),
      maplist(asm_operand(out, Env0, Loc), Outs, OutKs),
      maplist(asm_operand(in, Env0, Loc), Ins, InKs),
      atom_codes(T, Template),
      (   asm_runtime_reason(Goto, OutKs, InKs, Clobbers, Template, Reason) -> true
      ;   sema_error(Loc, 'inline asm "~w" is not supported: nanofil cannot check its instructions', [T])
      ),
      format(codes(Msg), 'cannot handle inline asm (~w): ~w', [Reason, T]),
      new_literal(Msg, Sym, Env0, Env) },
    set_env(Env),
    let(p, copy, [global(Sym)], Addr),
    emit(call(void, global(zsafety_error), [arg(p, Addr)])).

% An asm with a memory operand passes a pointer to code that nothing
% checks. clang's Fil-C compiles it to a run-time error, which a program
% reaches only if it runs the asm (gnulib's x87 control-word accesses in
% fpucw.h, under long double printf); nanofil calls zsafety_error alike
% (docs/abi-findings.md, *Inline asm*). Any other asm is refused.
stmt_(unsupported_asm(memory(Template)), _) --> !,
    { atom_codes(T, Template),
      format(codes(Msg), 'cannot handle inline asm (inline assembly with pointer argument is not supported): ~w', [T]) },
    env(Env0),
    { new_literal(Msg, Sym, Env0, Env) },
    set_env(Env),
    let(p, copy, [global(Sym)], Addr),
    emit(call(void, global(zsafety_error), [arg(p, Addr)])).
stmt_(unsupported_asm(_), Ctx) -->
    { ctx_loc(Ctx, Loc),
      sema_error(Loc, 'inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")', []) }.
stmt_(expr(Expr), Ctx) --> judged_rval(Expr, Ctx, _).
stmt_(if(Cond, Then, Else), Ctx) -->
    judged(Cond, Ctx),
    label(LThen), label(LElse), label(LJoin),
    cond_jump(Cond, Ctx, LThen, LElse),
    start(LThen), stmt(Then, Ctx), term(goto(LJoin)),
    start(LElse), ( { Else == none } -> [] ; stmt(Else, Ctx) ),
    start(LJoin).
stmt_(while(Cond, Body), Ctx) -->
    label(LCond), label(LBody), label(LEnd), cleanup_targets([LEnd, LCond]),
    start(LCond), loop_located(Ctx), judged(Cond, Ctx),
    cond_jump(Cond, Ctx, LBody, LEnd),
    start(LBody),
    { loop_ctx(Ctx, LEnd, LCond, BodyCtx) },
    stmt(Body, BodyCtx),
    term(goto(LCond)),
    start(LEnd).
stmt_(do(Body, Cond), Ctx) -->
    label(LBody), label(LCond), label(LEnd), cleanup_targets([LEnd, LCond]),
    start(LBody),
    { loop_ctx(Ctx, LEnd, LCond, BodyCtx) },
    stmt(Body, BodyCtx),
    start(LCond), loop_located(Ctx), judged(Cond, Ctx),
    cond_jump(Cond, Ctx, LBody, LEnd),
    start(LEnd).
stmt_(for(Init, Cond, Step, Body), Ctx) -->
    save_scope(Scope), env(Env0), { cleanup_keys(Env0, Outer) },
    (   { Init == none } -> []
    ;   { Init = expr(InitExpr) } -> judged_rval(InitExpr, Ctx, _)
    ;   item(Init, Ctx)
    ),
    label(LCond), label(LBody), label(LStep), label(LEnd),
    cleanup_targets([LEnd, LStep]),
    start(LCond), loop_located(Ctx),
    (   { Cond == none } -> term(goto(LBody))
    ;   judged(Cond, Ctx), cond_jump(Cond, Ctx, LBody, LEnd)
    ),
    start(LBody),
    { loop_ctx(Ctx, LEnd, LStep, BodyCtx) },
    stmt(Body, BodyCtx),
    start(LStep), loop_located(Ctx),
    ( { Step == none } -> [] ; judged_rval(Step, Ctx, _) ),
    term(goto(LCond)),
    start(LEnd),
    scope_cleanups(Outer),
    restore_scope(Scope).
stmt_(switch(Expr, Body), Ctx) -->
    judged_rval(Expr, Ctx, Value0),
    { Value0 = v(_, Type0), ctx_loc(Ctx, Loc) },
    {   int_type(Type0) -> integer_promotion(Type0, Type)
    ;   sema_error(Loc, 'switch on a non-integer', [])
    },
    convert(Value0, Type, v(Value, _)),
    label(LDispatch), label(LEnd), cleanup_targets([LEnd]),
    term(goto(LDispatch)),
    cases(Outer), set_cases([]),
    { switch_ctx(Ctx, LEnd, BodyCtx) },
    env(Env0),
    { vm_scopes(Env0, Scopes),
      ( lookup_ordinary(Env0, 'vm.switch', OuterScopes) -> true ; OuterScopes = [] ),
      bind_ordinary('vm.switch', Scopes, Env0, Env1) },
    set_env(Env1),
    stmt(Body, BodyCtx),
    env(Env2), { bind_ordinary('vm.switch', OuterScopes, Env2, Env3) }, set_env(Env3),
    term(goto(LEnd)),
    cases(Cases0), set_cases(Outer),
    { reverse(Cases0, Cases), distinct_cases(Cases, Type, Loc) },
    start(LDispatch), dispatch(Cases, Value, Type, LEnd),
    start(LEnd).
stmt_(case(Expr, Body), Ctx) -->
    env(Env),
    { ctx_loc(Ctx, Loc), case_values(Expr, Env, Loc, Values) },
    vm_case(Ctx),
    label(Label), start(Label),
    cases(Cases0),
    { findall(case(V, Label), member(V, Values), New0), reverse(New0, New),
      append(New, Cases0, Cases) },
    set_cases(Cases),
    stmt(Body, Ctx).
stmt_(default(Body), Ctx) -->
    vm_case(Ctx),
    label(Label), start(Label),
    cases(Cases), set_cases([default(Label)|Cases]),
    stmt(Body, Ctx).
stmt_(break, ctx(_, _, Break, _, Loc)) -->
    jump_cleanups(Break),
    target_jump(Break, Loc, 'break outside a loop or switch').
stmt_(continue, ctx(_, _, _, Cont, Loc)) -->
    jump_cleanups(Cont),
    target_jump(Cont, Loc, 'continue outside a loop').
stmt_(return(none), Ctx) -->
    { Ctx = ctx(_, RetType, _, _, _) },
    env(Env), { cleanup_keys(Env, Ks) }, run_cleanups(Ks),
    zero_ret(RetType).
stmt_(return(Expr), Ctx) -->
    { Expr \== none, Ctx = ctx(_, RetType, _, _, Loc) },
    judged_rval(Expr, Ctx, Value0),
    env(Env), { cleanup_keys(Env, Ks) },
    (   { RetType == void } -> run_cleanups(Ks), term(ret)
    ;   { abi_memory(RetType) }
    ->  assign_convert(Expr, Value0, RetType, Loc, v(V, _)),
        abi_source(RetType, V, Addr0),
        return_cleanups(RetType, Addr0, Addr),
        return_struct(RetType, Addr, Loc)
    ;   assign_convert(Expr, Value0, RetType, Loc, v(Value, _)),
        run_cleanups(Ks),
        term(ret(Value))
    ).
stmt_(goto(Name), Ctx) -->
    { ctx_loc(Ctx, Loc) },
    vm_goto(Name, Loc),
    goto_label(Name, Label),
    goto_cleanups(Name, Label, Target),
    term(goto(Target)).
% GNU goto *E: E is one of the function's label values (c_types'
% label_value/3), the label's number. Every goto * of the function
% stores it in one local and jumps to the function's single dispatch
% block (computed_dispatch//0), so an interpreter's many gotos share
% one search.
stmt_(computed_goto(E), Ctx) -->
    rval(E, Ctx, V0),
    { ctx_loc(Ctx, Loc) },
    (   { V0 = v(_, ptr(_)) } -> []
    ;   { sema_error(Loc, 'goto * of a non-pointer', []) }
    ),
    convert(V0, ulong, v(X, _)),
    env(Env), { cleanup_keys(Env, Ks) },
    (   { Ks == [] } -> []
    ;   { sema_error(Loc, 'goto * in the scope of a variable with a cleanup attribute is not supported', []) }
    ),
    state(st(_, _, _, _, _, Labels0, _, _)),
    (   { get_assoc(computed(goto), Labels0, dispatch(LDispatch, Slot, _)) } -> []
    ;   label(LDispatch), local_slot(ulong, Slot),
        state(st(E1, C1, I1, B1, N1, Labels1, Cs1, A1),
              st(E1, C1, I1, B1, N1, Labels2, Cs1, A1)),
        { put_assoc(computed(goto), Labels1, dispatch(LDispatch, Slot, Loc), Labels2) }
    ),
    store_typed(ulong, X, Slot),
    term(goto(LDispatch)).
stmt_(label(Name, Body), Ctx) -->
    vm_label(label(Name)),
    goto_label(Name, Label),
    label_cleanups(Name, Label),
    start(Label),
    stmt(Body, Ctx).
stmt_(decl(Loc, Specs, Inits), Ctx) -->
    item(decl(Loc, Specs, Inits), Ctx).

% asm_outputs(+Ops, +Ctx)//, asm_inputs(+Ops, +Ctx)//: a blank asm's
% operands (stmt_//2's asm_empty).
asm_outputs([], _) --> [].
asm_outputs([op(C, E)|Os], Ctx) -->
    { ctx_loc(Ctx, Loc),
      (   memberchk(C, ['+r', '+g', '=r']) -> true
      ;   sema_error(Loc, 'the asm output constraint "~w" is not supported', [C])
      ) },
    env(Env),
    { elaborate(E, Env, Loc, X) },
    place(X, Ctx, P),
    { (   P = lv(Addr, T0), unqualified(T0, T), asm_value_type(T) -> true
      ;   sema_error(Loc, 'an asm operand must have integer or floating type', [])
      ) },
    (   { C == '=r' } -> []
    ;   load_typed(T, Addr, Ctx, V), store_typed(T, V, Addr)
    ),
    asm_outputs(Os, Ctx).

asm_inputs([], _) --> [].
asm_inputs([op(C, E)|Os], Ctx) -->
    { ctx_loc(Ctx, Loc),
      (   memberchk(C, [r, g, i, n]) -> true
      ;   sema_error(Loc, 'the asm input constraint "~w" is not supported', [C])
      ) },
    env(Env),
    { (   memberchk(C, [i, n])
      ->  (   catch(const_value(E, Env, _, _), not_constant, fail) -> true
          ;   sema_error(Loc, 'the asm "~w" operand is not an integer constant', [C])
          )
      ;   true
      ) },
    judged_rval(E, Ctx, v(_, T0)),
    { unqualified(T0, T),
      (   asm_value_type(T) -> true
      ;   sema_error(Loc, 'an asm operand must have integer or floating type', [])
      ) },
    asm_inputs(Os, Ctx).

asm_value_type(T) :- arithmetic_type(T), T \== ldouble.

% asm_operand(+Dir, +Env, +Loc, +Op, -Kind): Kind is K-C for an operand
% with constraint C: K is mem if clang passes its address (an output
% constraint with m or g, an input "m"), else ptr, value or other by
% its type after decay.
asm_operand(Dir, Env, Loc, op(C, E), K-C) :-
    elaborate(E, Env, Loc, X), tree_type(X, T0), unqualified(T0, T),
    atom_chars(C, Cs),
    (   Dir == out, ( memberchk(m, Cs) ; memberchk(g, Cs) ) -> K = mem
    ;   Dir == in, C == m -> K = mem
    ;   memberchk(T, [ptr(_), array(_, _), func(_, _, _)]) -> K = ptr
    ;   asm_value_type(T) -> K = value
    ;   K = other
    ).

% asm_runtime_reason(+Goto, +OutKs, +InKs, +Clobbers, +Template, -Reason):
% filcc certainly compiles the asm to the run-time error "cannot handle
% inline asm (Reason)". handleInlineAsm refuses asm goto, then a
% pointer result, then a pointer argument (an address for a memory
% operand among them); validateSafeInlineAsm then checks constraints
% and clobbers, and refuses the first line, split at newlines and
% semicolons, whose mnemonic it does not know. The cases are probed
% against the pinned filcc at -O0 and -O2 (tests/c/prog/asm-refused.c);
% nanofil claims a mnemonic refusal only for operands and clobbers the
% probe saw pass validation and the first nonblank line's mnemonic
% (c_types filcc_refused_mnemonic/1). asm goto with a pointer operand
% crashes clang's Fil-C, so it is not claimed.
asm_runtime_reason(goto, OutKs, InKs, _, _, 'asm goto is not supported') :- !,
    append(OutKs, InKs, Ks),
    \+ ( member(K-_, Ks), memberchk(K, [mem, ptr, other]) ).
asm_runtime_reason(_, OutKs, _, _, _, 'inline assembly with pointer return type is not supported') :-
    memberchk(ptr-_, OutKs), !,
    \+ memberchk(mem-_, OutKs).
asm_runtime_reason(_, OutKs, InKs, _, _, 'inline assembly with pointer argument is not supported') :-
    ( memberchk(mem-_, OutKs) ; memberchk(mem-_, InKs) ; memberchk(ptr-_, InKs) ), !,
    \+ memberchk(other-_, OutKs), \+ memberchk(other-_, InKs).
asm_runtime_reason(_, OutKs, InKs, _, _, Reason) :-
    forall(member(K-_, OutKs), K == value),
    forall(member(K-_, InKs), K == value),
    append(OutKs, InKs, Ks),
    forall(member(_-C, Ks), asm_known_constraint(C)),
    member(_-C, Ks), asm_ir_constraint(C, IR), \+ asm_validated_constraint(IR), !,
    format(atom(Reason), 'unsupported constraint for safe inline asm: ~w', [IR]).
asm_runtime_reason(_, OutKs, InKs, Clobbers, Template, Reason) :-
    forall(member(K-C, OutKs), ( K == value, memberchk(C, ['=r', '+r', '=a']) )),
    forall(member(K-C, InKs), ( K == value, asm_validated_input(C) )),
    forall(member(C, Clobbers), memberchk(C, [memory, cc])),
    split_asm_lines(Template, Lines),
    member(Line, Lines),
    atom_codes(L, Line), normalize_space(atom(A), L), A \== '', !,
    atomic_list_concat([W|_], ' ', A), downcase_atom(W, M),
    filcc_refused_mnemonic(M),
    format(atom(Reason), 'unsupported mnemonic for safe inline asm: ~w', [M]).

% asm_ir_constraint(+C, -IR): the constraint clang writes in the IR for
% a value operand's GCC constraint C: + becomes = (its tied input is a
% digit), a fixed register letter its {reg}, g is imr, the rest as
% written (lib/CodeGen/CGStmt.cpp, X86's convertConstraint). An operand
% whose constraint allows memory and is passed by address is a pointer
% argument, which asm_operand/5 classifies as mem.
asm_ir_constraint(C, IR) :-
    atom_chars(C, Cs),
    asm_constraint_prefix(Cs, Ps0, Body),
    maplist(asm_ir_prefix, Ps0, Ps),
    (   Body = [L], asm_fixed_register(L, Reg) -> atom_chars(Reg, BCs)
    ;   Body == [g] -> BCs = [i, m, r]
    ;   BCs = Body
    ),
    append(Ps, BCs, IRCs), atom_chars(IR, IRCs).

asm_constraint_prefix([P|Cs], [P|Ps], Body) :-
    memberchk(P, ['=', '+', '&', '%']), !, asm_constraint_prefix(Cs, Ps, Body).
asm_constraint_prefix(Body, [], Body).

asm_ir_prefix('+', '=') :- !.
asm_ir_prefix(P, P).

asm_fixed_register(a, '{ax}').
asm_fixed_register(b, '{bx}').
asm_fixed_register(c, '{cx}').
asm_fixed_register(d, '{dx}').
asm_fixed_register('S', '{si}').
asm_fixed_register('D', '{di}').

% asm_known_constraint(+C): C's letters are ones whose lowering by clang
% asm_ir_constraint/2 knows: register classes, fixed registers, r, m, g,
% i, n and e, digits.
asm_known_constraint(C) :-
    atom_chars(C, Cs), asm_constraint_prefix(Cs, _, Body), Body = [_|_],
    forall(member(L, Body),
           ( memberchk(L, [r, m, g, i, n, e, q, 'Q', x, y, v, a, b, c, d, 'S', 'D']) ; char_code_digit(L) )).

% asm_validated_constraint(+IR): validateSafeInlineAsm accepts an
% operand constraint IR in its first loop (FilPizlonator.cpp): after
% the prefixes =, +, & and %, a register class r, q, Q, x, y, v or Yk, a
% fixed register of a general-purpose family, or a matching digit
% string. Every other operand constraint is refused there, first in the
% IR's order, outputs then inputs, with "unsupported constraint for safe
% inline asm: IR".
asm_validated_constraint(IR) :-
    atom_chars(IR, Cs), asm_constraint_prefix(Cs, _, Rest), atom_chars(R, Rest),
    (   memberchk(R, [r, q, 'Q', x, y, v, 'Yk']) -> true
    ;   memberchk(R, ['{ax}', '{bx}', '{cx}', '{dx}', '{si}', '{di}']) -> true
    ;   Rest = [_|_], forall(member(D, Rest), char_code_digit(D))
    ).

char_code_digit(D) :- char_code(D, N), N >= 0'0, N =< 0'9.

asm_validated_input(r).
asm_validated_input(a).
asm_validated_input(C) :- atom_length(C, 1), char_type(C, digit(_)).

split_asm_lines(Template, Lines) :-
    split_at(Template, [0'\n, 0';], Lines).
split_at(Cs, Seps, [L|Ls]) :-
    (   append(L, [Sep|Rest], Cs), memberchk(Sep, Seps)
    ->  split_at(Rest, Seps, Ls)
    ;   L = Cs, Ls = []
    ).

% case_values(+Expr, +Env, +Loc, -Values): the values a case label
% matches: its constant, or each of a GNU range Lo ... Hi, none when Lo
% exceeds Hi (GCC, Case Ranges). The range is expanded, so its values
% meet the other cases' in distinct_cases/3; one of more than 4096
% values is refused.
case_values(range(Lo, Hi), Env, Loc, Values) :- !,
    case_constant(Lo, Env, Loc, L), case_constant(Hi, Env, Loc, H),
    (   H - L >= 4096
    ->  sema_error(Loc, 'a case range of more than 4096 values is not supported', [])
    ;   H < L -> Values = []
    ;   numlist(L, H, Values)
    ).
case_values(Expr, Env, Loc, [Value]) :- case_constant(Expr, Env, Loc, Value).

case_constant(Expr, Env, Loc, Value) :-
    (   catch(const_value(Expr, Env, Value, _), not_constant, fail) -> true
    ;   sema_error(Loc, 'case label is not a constant', [])
    ).

% computed_dispatch//: the dispatch block of the function's goto *, if
% any: among its address-taken labels by number, any other value
% reaching unreachable, a Fil-C panic. Each such label is a goto
% target, so none may be in a variably modified scope the jump is not.
computed_dispatch -->
    state(st(Env, _, _, _, _, Labels, _, _)),
    (   { get_assoc(computed(goto), Labels, dispatch(LDispatch, Slot, Loc)) }
    ->  start(LDispatch),
        let(l, load(l), [Slot], X),
        { lookup_ordinary(Env, 'labels.taken', Names) },
        label_cases(Names, 1, Loc, Cases),
        label(LTrap),
        dispatch(Cases, X, ulong, LTrap),
        start(LTrap), term(unreachable)
    ;   []
    ).

label_cases([], _, _, []) --> [].
label_cases([Name|Names], N, Loc, [case(N, Label)|Cases]) -->
    vm_goto(Name, Loc), goto_label(Name, Label),
    { N1 is N + 1 },
    label_cases(Names, N1, Loc, Cases).

% label_values(+Body, +Env0, -Env): Env is Env0 with each label whose
% address Body takes (&&L, label_addr(L)) bound to its number, 1, 2, ...
% in order of first use, and 'labels.taken' to their list.
label_values(Body, Env0, Env) :-
    phrase(label_addrs(Body), Names0),
    list_to_ord_set(Names0, Set),
    first_uses(Names0, Set, Names),
    foldl(label_number, Names, 1-Env0, _-Env1),
    bind_ordinary('labels.taken', Names, Env1, Env).

label_addrs(label_addr(Name)) --> !, [Name].
label_addrs(T) --> { compound(T), !, T =.. [_|Args] }, label_addrs_list(Args).
label_addrs(_) --> [].
label_addrs_list([]) --> [].
label_addrs_list([A|As]) --> label_addrs(A), label_addrs_list(As).

first_uses([], _, []).
first_uses([N|Ns], Left0, Firsts) :-
    (   ord_memberchk(N, Left0)
    ->  ord_del_element(Left0, N, Left), Firsts = [N|Firsts1]
    ;   Left = Left0, Firsts = Firsts1
    ),
    first_uses(Ns, Left, Firsts1).

label_number(Name, N-Env0, N1-Env) :-
    bind_ordinary(label_addr(Name), N, Env0, Env), N1 is N + 1.

% target_jump(+Target, +Loc, +Error)//: a jump to the break or
% continue Target, some(Label); none is semantic error Error at Loc.
target_jump(some(Label), _, _) --> term(goto(Label)).
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
    enter_origin(Loc, statement(decl), Parent),
    vm_typedefs(Specs, Inits, Ctx),
    (   { \+ memberchk(storage(typedef), Specs), cleanup_attr(Specs, Fn) }
    ->  cleanup_decls(Decls, Loc, Fn, Ctx)
    ;   local_decls(Decls, Ctx)
    ),
    restore_origin(Parent).

% local_decls(+Decls, +Ctx)//, local_decl(+Decl, +Ctx)//: lower
% block-scope declarations. Functions and extern objects are global, a
% static object is a global with a function-qualified name, anything
% else is a local slot.
local_decls([], _) --> [].
local_decls([Decl|Decls], Ctx) -->
    local_decl(Decl, Ctx),
    local_decls(Decls, Ctx).

local_decl(d(Name, Type0, Storage0, Asm, Init), Ctx) -->
    { ctx_loc(Ctx, Loc),
      (   Storage0 = thread_local(Storage) -> Thread = tls
      ;   Storage = Storage0, Thread = none
      ) },
    (   { Type0 = func(_, _, _) ; Storage == extern }
    ->  env(Env0),
        { global_decl(Loc, d(Name, Type0, Storage0, Asm, Init), Env0, Env) },
        set_env(Env)
    ;   { Thread == tls, Storage \== static }              % 6.7.1p3
    ->  { sema_error(Loc, '_Thread_local ~w at block scope must also be static or extern', [Name]) }
    ;   { Storage == static }
    ->  { supported(Type0, Loc),
          (   vla_type(Type0)                               % 6.7.6.2p2
          ->  sema_error(Loc, '~w is a variable length array with static storage', [Name])
          ;   true
          ) },
        realized(Type0, Type1, Ctx),      % a pointer to one is allowed
        env(Env0),
        { Ctx = ctx(Func, _, _, _, _),
          next_id(K, Env0, Env1),
          format(atom(Sym), '~w.~w.~w', [Func, Name, K]),
          complete_array(Type1, Init, Type, Loc, Env0, none),
          bind_ordinary(Name, gvar(Type, Sym, Storage0, Init), Env1, Env2),
          thread_linkage(Thread, local, Linkage),
          define_global(Sym, Type, Linkage, Init, Loc, Env2, Env2a),
          data_alignment(Name, Sym, Env2a, Env3),
          % Resolve block-scope names before the scope is restored.
          static_items(Type, Init, Loc, Env3, Env4, Items),
          put_def(initialized(Sym), Items, Env4, Env) },
        set_env(Env),
        vm_scope(Type)
    ;   realized(Type0, Type1, Ctx),
        env(Env),
        { complete_array(Type1, Init, Type, Loc, Env, whole),
          check_local_type(Type, Env, Loc, Name) },
        { lookup_ordinary(Env, qalign(Name), A), integer(A) -> true ; A = 1 },
        (   { vla_type(Type) }
        ->  { Init == none -> true                          % 6.7.9p3
            ; sema_error(Loc, 'a variable length array cannot be initialized', []) },
            vla_slot(Type, A, Ctx, Addr)
        ;   local_slot(Type, A, Addr)
        ),
        bind(Name, var(Addr, Type)),
        vm_scope(Type),
        (   { Init == none } -> []
        ;   init(Addr, Type, Init, Ctx)
        )
    ).

% check_local_type(+Type, +Env, +Loc, +Name): throw a semantic error
% unless Type is a type a local object Name can have.
check_local_type(Type, Env, Loc, Name) :-
    supported(Type, Loc),
    (   vla_type(Type) -> element_type(Type, Elem) ; Elem = Type ),
    catch(( type_size_align(Elem, Env, _, _) -> true ; true ), bad(Why),
          sema_error(Loc, '~w has a type nanofil does not support (~w)',
                     [Name, Why])).

% vm_typedefs(+Specs, +Inits, +Ctx)//: a block-scope typedef of a
% variably modified type evaluates its size expressions where it is
% declared, once (C11 6.7.8p3); the name then has the evaluated type.
vm_typedefs(Specs, Inits, Ctx) -->
    (   { memberchk(storage(typedef), Specs) } -> vm_typedef_names(Inits, Ctx)
    ;   []
    ).

vm_typedef_names([], _) --> [].
vm_typedef_names([init(dcl(some(Name), _, _), _)|Inits], Ctx) -->
    env(Env0),
    (   { lookup_ordinary(Env0, Name, typedef(Type0)), vm_type(Type0) }
    ->  realized(Type0, Type, Ctx),
        env(Env1), { bind_ordinary(Name, typedef(Type), Env1, Env) }, set_env(Env),
        vm_scope(Type)
    ;   []
    ),
    vm_typedef_names(Inits, Ctx).

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

% static_complit(+V, +Type, +C): V is a compound literal of Type in a
% static initializer, which GNU C accepts as its initializer list.
static_complit(complit(TN, _), Type, c(Env, none, _)) :-
    aggregate(Type),
    catch(type_name_type(TN, T, Env, _), _, fail),
    T == Type.

% single_value(+Type, +V, +Env, +Whole): entry value V initializes a
% slot of type Type by itself, so no braces were elided. The final cut
% makes this semidet: the alternatives can overlap.
single_value(Type, V, Env, Whole) :-
    (   V = list(_)
    ;   static_complit(V, Type, c(Env, Whole, unknown))
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

% dispatch(+Cases, +Value, +Type, +LEnd)//: the switch dispatch (C11
% 6.8.4.2p5): a jump to the case whose value, converted to the promoted
% type Type, equals Value, else to the default or LEnd. Up to four cases
% are compared for equality in source order. More are read with Type's
% signedness and sorted; a binary search compares Value with them in
% Type's order, down to a few cases compared one by one.
dispatch([], _, _, LEnd) --> term(goto(LEnd)).
dispatch(Cases, Value, Type, LEnd) -->
    { findall(Wrapped-Label,
              ( member(case(CaseValue, Label), Cases),
                convert_int(CaseValue, Type, Wrapped) ),
              Pairs0),
      ( memberchk(default(LDefault), Cases) -> true ; LDefault = LEnd ),
      type_class(Type, Class) },
    (   { length(Pairs0, N), N =< 4 }
    ->  dispatch_cases(Pairs0, Value, Class, LDefault)
    ;   { keysort(Pairs0, Pairs),
          int_info(Type, _, Sign) },
        dispatch_search(Pairs, Value, Sign, Class, LDefault)
    ).

% distinct_cases(+Cases, +Type, +Loc): no two case values of a switch
% are equal once converted to the promoted controlling type Type (C11
% 6.8.4.2p3).
distinct_cases(Cases, Type, Loc) :-
    findall(W, ( member(case(V, _), Cases), convert_int(V, Type, W) ), Ws),
    msort(Ws, Sorted),
    (   append(_, [W, W|_], Sorted)
    ->  sema_error(Loc, 'duplicate case value ~w', [W])
    ;   true
    ).

% dispatch_search(+Pairs, +Value, +Sign, +Class, +LDefault)//: Pairs are
% sorted by value. More than four: branch on Value < the middle value,
% to the search of the lower or the upper half. Otherwise compare Value
% with each in turn, then jump to LDefault.
dispatch_search(Pairs, Value, Sign, Class, LDefault) -->
    { length(Pairs, N), N > 4, !,
      Half is N // 2, length(Lower, Half), append(Lower, Upper, Pairs),
      Upper = [Pivot-_|_],
      less_than(Sign, Less) },
    let(w, cmp(Less, Class), [Value, const(Pivot)], Test),
    label(LLower), label(LUpper),
    term(branch(Test, LLower, LUpper)),
    start(LLower),
    dispatch_search(Lower, Value, Sign, Class, LDefault),
    start(LUpper),
    dispatch_search(Upper, Value, Sign, Class, LDefault).
dispatch_search(Pairs, Value, _, Class, LDefault) -->
    dispatch_cases(Pairs, Value, Class, LDefault).

less_than(signed, slt).
less_than(unsigned, ult).

% dispatch_cases(+Pairs, +Value, +Class, +LDefault)//: compare Value
% with each case value of Pairs in turn, then jump to LDefault.
dispatch_cases([], _, _, LDefault) --> term(goto(LDefault)).
dispatch_cases([Wrapped-Label|Pairs], Value, Class, LDefault) -->
    let(w, cmp(eq, Class), [Value, const(Wrapped)], Test),
    label(Next),
    term(branch(Test, Label, Next)),
    start(Next),
    dispatch_cases(Pairs, Value, Class, LDefault).

% judged(+Expr, +Ctx)//: full expression Expr is typed, or c_types says
% why not; where it cannot say, lowering reports the fault.
judged(Expr, Ctx) -->
    expression_scope(Expr),
    env(Env),
    { ctx_loc(Ctx, Loc), ( elaborate(Expr, Env, Loc, _) -> true ; true ) }.

% expression_scope(+Expr)//: the scope gets the structs and unions full
% expression Expr's type names define (c_types expression_tags/3).
expression_scope(Expr) -->
    env(Env0), { expression_tags(Expr, Env0, Env) }, set_env(Env).

% judged_rval(+Expr, +Ctx, -R)//: judged//2, then rval//3, from one
% elaboration of Expr: elaborating each full expression twice was a
% seventh of lowering.
judged_rval(Expr, Ctx, R) -->
    expression_scope(Expr),
    env(Env),
    (   { ctx_loc(Ctx, Loc), elaborate(Expr, Env, Loc, X) }
    ->  { value(X, XV) }, lower(XV, Ctx, R)
    ;   { ctx_loc(Ctx, Loc), sema_error(Loc, 'cannot type ~w', [Expr]) }
    ).

% cond_jump(+Expr, +Ctx, +LTrue, +LFalse)//: branch on the truth of
% scalar Expr.
cond_jump(Expr, Ctx, LTrue, LFalse) -->
    rval(Expr, Ctx, Value),
    truth(Value, Ctx, Test),
    term(branch(Test, LTrue, LFalse)).

% truth(+Value, +Ctx, -W)//: W is a w value that is nonzero exactly when
% scalar Value is.
truth(v(V, Type), Ctx, W) -->
    (   { type_class(Type, w) } -> { W = V }
    ;   { type_class(Type, l) } -> let(w, cmp(ne, l), [V, const(0)], W)
    ;   { float_type(Type), type_class(Type, K) }
    ->  let(w, cmp(ne, K), [V, const(0)], W)
    ;   { Type = ptr(_) }
    ->  let(l, ptoi, [V], Int),
        let(w, cmp(ne, l), [Int, const(0)], W)
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
     bytes(Off, Type, Ns)   the integers Ns, the elements of a string
                            literal of a one-byte Type, from Off: one leaf
                            for GLib's megabyte resource blobs
     expr(Off, Type, Expr)  the value of the expression Expr, converted
                            to Type: a scalar, or (locals) a whole struct
   Offsets are from the start of the object. A local object stores its
   leaves; a static one turns them into data chunks. The walk over the
   entries also gives an array of unknown size its length
   (complete_array/6). */

% init_leaves(+Type, +Init, +C, -Leaves): Leaves are what Init assigns
% to an object of Type. C = c(Env, Whole, Loc), with Whole as for
% complete_array/6. The walk is deterministic; once/1 drops the
% choicepoints its clauses leave per slot, which would keep every
% slot's frames alive while a large table's leaves are used.
init_leaves(Type, Init, C, Leaves) :-
    once(phrase(object_init(Type, 0, Init, C), Leaves)).

% object_init(+Type, +Off, +Init, +C)//: the leaves of Init for the
% object of Type at Off. A scalar may be braced.
object_init(Type, Off, complit(TN, Init), C) -->
    { static_complit(complit(TN, Init), Type, C) }, !,
    object_init(Type, Off, Init, C).
object_init(bits(T, Pos, W), Off, list([entry(_, V)|Rest]), C) --> !,
    { Rest == [] -> true ; init_error(C, 'excess initializers', []) },
    object_init(bits(T, Pos, W), Off, V, C).
object_init(bits(T, Pos, W), Off, Expr, _) --> !, [bits(Off, T, Pos, W, Expr)].
object_init(array(T, N), Off, list([entry([], Str)]), C) -->
    { str_elems(Str, T, _) }, !,
    object_init(array(T, N), Off, Str, C).
object_init(array(T, N), Off, list(Entries), _) -->
    { integer(N), is_char_type(T), byte_entries(Entries, T, Vs),
      length(Vs, K), K =< N }, !,
    % A braced list of integer constants, nothing else, for a byte
    % array: one leaf, as a string literal is (GLib's resource blobs
    % for a compiler it does not know by name, gtk3's 1.5 MB of them).
    [zero(Off, array(T, N)), bytes(Off, T, Vs)].
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
    (   { Size =:= 1 } -> [bytes(Off, ElemType, Values)]
    ;   elem_leaves(Values, ElemType, Off, Size)
    ).
object_init(array(_, _), _, _, C) --> !,
    { init_error(C, 'array initializer must be a list', []) }.
object_init(Type, Off, Expr, _) --> [expr(Off, Type, Expr)].

% byte_entries(+Entries, +Type, -Values): Entries are undesignated
% integer or character constants, whose values converted to Type are
% Values.
byte_entries([], _, []).
byte_entries([entry([], X)|Es], T, [V|Vs]) :-
    ( X = num(V0, _) ; X = chr(V0) ), integer(V0), !,
    convert_int(V0, T, V),
    byte_entries(Es, T, Vs).

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
slots(Type, _, Off, [entry([range(E1, E2)|Ds], V)|Entries0], Entries, Max0, Max, C) --> !,
    { range_indexes(E1, E2, V, C, Is),
      findall(entry([index(num(I, none-dec))|Ds], V), member(I, Is), Expanded),
      append(Expanded, Entries0, Entries1) },
    slots(Type, 0, Off, Entries1, Entries, Max0, Max, C).
slots(Type, I, Off, [entry([field(F)|Ds], V)|Entries0], Entries, Max0, Max, C) -->
    { anonymous_member(Type, F, C, K) }, !,           % C11 6.7.2.1p13
    slots(Type, I, Off, [entry([anon(K), field(F)|Ds], V)|Entries0], Entries, Max0, Max, C).
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
    nth0(I, Members, M),
    member_slot(M, _, Off, Type).
slot(union(Id), c(Env, _, _), 0, Off, Type) :-
    su_members(union(Id), Env, [M|_]),
    member_slot(M, _, Off, Type).

% member_slot(+M, -Name, -Off, -SlotType): member M, named Name, is the
% slot of SlotType at Off; a bit-field's is bits(Type, Pos, Width), of
% the Type at Off.
member_slot(m(Name, Type, Off), Name, Off, Type).
member_slot(m(Name, Type, Off, bits(Pos, W)), Name, Off, bits(Type, Pos, W)).

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
        nth0(I, Members, M), member_slot(M, some(Field), Off, Type)
    ->  true
    ;   init_error(C, 'no member ~w', [Field])
    ).
designated_slot(anon(I), SU, c(Env, _, _), I, Off, Type) :- !,
    su_members(SU, Env, Members),
    nth0(I, Members, M), member_slot(M, none, Off, Type).
designated_slot(_, Type, C, _, _, _) :-
    init_error(C, 'bad designator for a ~w', [Type]).

% anonymous_member(+SU, +F, +C, -I): F is not a member of struct or
% union SU itself but of its anonymous member I, so a designator .F
% designates that member's F.
anonymous_member(SU, F, c(Env, _, _), I) :-
    su(SU),
    su_members(SU, Env, Members),
    \+ ( member(M, Members), member_slot(M, some(F), _, _) ),
    nth0(I, Members, M),
    member_slot(M, none, _, AT),
    catch(member_layout(AT, F, Env, _, _, _), _, fail), !.

% range_indexes(+E1, +E2, +V, +C, -Is): the GNU range designator
% [E1 ... E2] designates the elements Is, each initialized by V as if it
% had a designator of its own. GCC evaluates V once; nanofil lowers it
% for each element, so V may not have side effects.
range_indexes(E1, E2, V, C, Is) :-
    C = c(Env, _, _),
    (   catch(( const_value(E1, Env, Lo, _), const_value(E2, Env, Hi, _) ),
              not_constant, fail),
        0 =< Lo, Lo =< Hi
    ->  numlist(Lo, Hi, Is)
    ;   init_error(C, 'bad range designator', [])
    ),
    (   Lo < Hi, effectful(V)
    ->  init_error(C, 'a range designator\'s initializer has side effects', [])
    ;   true
    ).

% effectful(+E): the expression or initializer E may have side effects:
% it contains an assignment, increment, call or statement expression.
effectful(E) :-
    compound(E),
    (   ( E = assign(_, _, _) ; E = call(_, _) ; E = stmtexpr(_)
        ; E = un(Op, _), memberchk(Op, [preinc, predec, postinc, postdec]) )
    ->  true
    ;   E =.. [_|Args], member(A, Args), effectful(A)
    ->  true
    ).

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
store_leaf(bytes(Off, Type, Ns), Addr, Ctx) -->
    { phrase(elem_leaves(Ns, Type, Off, 1), Leaves) },
    store_leaves(Leaves, Addr, Ctx).
store_leaf(val(Off, Type, N), Addr, _) -->
    offset(Addr, Off, P),
    { store_width(Type, Width) },
    emit(store(Width, const(N), P)).
store_leaf(expr(Off, Type, Expr), Addr, Ctx) -->
    offset(Addr, Off, P),
    judged_rval(Expr, Ctx, Value0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(Expr, Value0, Type, Loc, v(Value, _)),
    store_typed(Type, Value, P).
store_leaf(bits(Off, Type, Pos, W, Expr), Addr, Ctx) -->
    offset(Addr, Off, P),
    judged_rval(Expr, Ctx, Value0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(Expr, Value0, Type, Loc, Value),
    place_write(bits(P, Type, Pos, W), Value, Ctx, _).

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
    emit(store(Width, const(0), P)),
    { Off1 is Off + N },
    zero_bytes(Addr, Off1, Size, Align).

%% Expressions

% GNU statement expressions load/decay their last expression before the
% block scope closes. A label on that statement does not hide its value.
statement_expression_items([], _, v(const(0), void)) --> [].
statement_expression_items([Item], Ctx, R) --> !,
    statement_expression_last(Item, Ctx, R).
statement_expression_items([Item|Items], Ctx, R) -->
    item(Item, Ctx), statement_expression_items(Items, Ctx, R).

statement_expression_last(at(Loc, expr(Expr)), Ctx0, R) --> !,
    { ctx_at(Ctx0, Loc, Ctx) }, judged_rval(Expr, Ctx, R).
statement_expression_last(at(_, label(Name, Body)), Ctx, R) --> !,
    vm_label(label(Name)),
    goto_label(Name, Label),
    label_cleanups(Name, Label),
    start(Label),
    statement_expression_last(Body, Ctx, R).
statement_expression_last(Item, Ctx, v(const(0), void)) --> item(Item, Ctx).

% binding_obj(+Binding, -R)//: R is the object or function an
% identifier bound to Binding designates. A global's address is copied
% into a temporary.
binding_obj(var(Addr, Type), lv(Addr, Type)) --> [].
binding_obj(fn(Type, Sym, _), fd(global(Sym), Type)) --> [].
binding_obj(gvar(Type, Sym, _, _), lv(Addr, Type)) -->
    let(p, copy, [global(Sym)], Addr).

% callee_temp(+V, -Callee)//: Callee is V in a temporary, as a callee
% must be.
callee_temp(tmp(T), tmp(T)) --> !.
callee_temp(V, Callee) --> let(p, copy, [V], Callee).

% member_lv(+Addr, +SUType, +Field, +Ctx, -P, -Type)//: P points at
% member Field, of Type, of the struct or union at Addr.
member_lv(Addr, SUType, Field, Ctx, P, Type) -->
    env(Env),
    { ctx_loc(Ctx, Loc) },
    (   { ( SUType = struct(_) ; SUType = union(_) ),
          member_type_offset(SUType, Field, Env, Type, Off) }
    ->  offset(Addr, Off, P)
    ;   { SUType =.. [_, Id], env_defs(Env, Defs),
          get_assoc(Id, Defs, Def), ( Def = bad(Why) ; Def = partial(Why, _) ) }
    ->  { sema_error(Loc, 'member ~w of a type nanofil does not support (~w)', [Field, Why]) }
    ;   { sema_error(Loc, 'no member named ~w', [Field]) }
    ).

% rval(+Expr, +Ctx, -R)//: R is v(V, Type), the value of Expr, arrays
% decayed, lvalues loaded, lowered from its typed tree (c_types'
% elaborate/3). Full expressions are judged first (judged//2), which
% diagnoses one that cannot be typed.
rval(Expr, Ctx, R) -->
    env(Env),
    (   { elaborate(Expr, Env, X) } -> { value(X, XV) }, lower(XV, Ctx, R)
    ;   { ctx_loc(Ctx, Loc), sema_error(Loc, 'cannot type ~w', [Expr]) }
    ).

/* lower(+XV, +Ctx, -R)//: R is v(V, Type), the value whose typed tree
   is XV. Types are unqualified, as code generation has them; a type
   name the source writes (a cast's, va_arg's, sizeof's) is read again
   by type_name/4, which refuses one nanofil does not support. */
lower(X, Ctx, R) -->
    typed_origin(X, Ctx, Parent), lower_node(X, Ctx, R),
    result_name(X, R), restore_origin(Parent).

lower_node(val(T, int(V)), _, v(const(V), U)) --> !, { unqualified(T, U) }.
lower_node(val(_, float(Cs)), _, v(const(V), Type)) --> !,
    { float_literal(Cs, V, Type) }.
lower_node(val(T, load(X)), Ctx, R) --> !,                 % 6.3.2.1p2
    place(X, Ctx, P),
    { unqualified(T, U) },
    (   { tree_type(X, TX), atomic_qualified(TX), P = lv(Addr, ptr(_)) }
    ->  let(p, atomic_load(p), [Addr], D),                 % 6.2.6.1p9
        { R = v(D, U) }
    ;   place_loaded(P, U, Ctx, R)
    ).
lower_node(val(T0, decay(X)), Ctx, R) --> !,               % 6.3.2.1p3-4
    place(X, Ctx, P),
    { ( P = lv(_, array(E, _)) -> PT = ptr(E) ; PT = T0 ), vm_typed(T0, PT, T) },
    decayed(P, T, Ctx, R).
lower_node(val(T0, addr(X)), Ctx, R) --> !,                % 6.5.3.2p3
    place(X, Ctx, P),
    { ( P = lv(_, PT0) -> PT = ptr(PT0) ; PT = T0 ), vm_typed(T0, PT, T) },
    decayed(P, T, Ctx, R).
lower_node(val(_, member(XS, F)), Ctx, R) --> !,           % 6.5.2.3p3
    lower(XS, Ctx, v(Addr, SU)),
    member_lv(Addr, SU, F, Ctx, P, Type),
    (   { Type = array(E, _) } -> { R = v(P, ptr(E)) }
    ;   loaded(Type, P, Ctx, R)
    ).
lower_node(val(_, comma(XA, XB)), Ctx, R) --> !,           % 6.5.17
    lower(XA, Ctx, _),
    lower(XB, Ctx, R).
lower_node(val(_, un(Op, XV)), Ctx, R) --> !,
    lower(XV, Ctx, V),
    unary(Op, V, Ctx, R).
lower_node(val(_, bin(Op, XA, XB)), Ctx, R) -->            % 6.5.13-14
    { memberchk(Op, [land, lor]) }, !,
    logical(Op, XA, XB, Ctx, R).
lower_node(val(_, bin(Op, XA, XB)), Ctx, R) --> !,
    lower(XA, Ctx, VA),
    lower(XB, Ctx, VB),
    binary(Op, VA, VB, Ctx, R).
lower_node(val(T, cond(XC, XA, XB)), Ctx, R) --> !,        % 6.5.15
    { unqualified(T, U) },
    label(LA), label(LB), label(LJoin),
    lower(XC, Ctx, VC), truth(VC, Ctx, W), term(branch(W, LA, LB)),
    start(LA), lower(XA, Ctx, VA), converted(VA, U, v(VA0, _)),
    arm_value(U, VA0, VA1), here(LA1),
    term(goto(LJoin)),
    start(LB), lower(XB, Ctx, VB), converted(VB, U, v(VB0, _)),
    arm_value(U, VB0, VB1), here(LB1),
    term(goto(LJoin)),
    join_arms(U, LJoin, LA1-VA1, LB1-VB1, R).
lower_node(val(T, gcond(XC, XB)), Ctx, R) --> !,           % GNU c ?: b
    { unqualified(T, U) },
    lower(XC, Ctx, VC), truth(VC, Ctx, W),
    label(LA), label(LB), label(LJoin),
    term(branch(W, LA, LB)),
    start(LA), converted(VC, U, v(VA0, _)), arm_value(U, VA0, VA1), here(LA1),
    term(goto(LJoin)),
    start(LB), lower(XB, Ctx, VB), converted(VB, U, v(VB0, _)),
    arm_value(U, VB0, VB1), here(LB1),
    term(goto(LJoin)),
    join_arms(U, LJoin, LA1-VA1, LB1-VB1, R).
lower_node(val(_, assign(=, X, XB)), Ctx, R) -->           % 6.2.6.1p9
    { tree_type(X, TX), atomic_qualified(TX) }, !,
    place(X, Ctx, lv(Addr, U)),
    lower(XB, Ctx, Value0),
    converted(Value0, U, R),
    { R = v(V, _) },
    atomic_stored(U, V, Addr, 5).
% A compound assignment or increment of an _Atomic object is one atomic
% read-modify-write (6.5.16.2p3, 6.5.2.4p2): a cas loop, the operand
% evaluated once before it; a pointer keeps its capability.
lower_node(val(_, assign(Op, X, XB)), Ctx, R) -->
    { tree_type(X, TX), atomic_qualified(TX) }, !,
    rmw_aligned(X, Ctx),
    place(X, Ctx, lv(Addr, U0)),
    lower(XB, Ctx, VB),
    { unqualified(U0, U), compound_assignment(Op, BinOp) },
    rmw(U, Addr, BinOp, VB, Ctx, _, R).
lower_node(val(_, incdec(Op, X)), Ctx, R) -->
    { tree_type(X, TX), atomic_qualified(TX) }, !,
    rmw_aligned(X, Ctx),
    place(X, Ctx, lv(Addr, U0)),
    { unqualified(U0, U),
      ( memberchk(Op, [preinc, postinc]) -> BinOp = add ; BinOp = sub ) },
    rmw(U, Addr, BinOp, v(const(1), int), Ctx, Old, New),
    { memberchk(Op, [preinc, predec]) -> R = New ; R = Old }.
lower_node(val(_, assign(Op, X, XB)), Ctx, R) --> !,       % 6.5.16
    place(X, Ctx, P),
    (   { Op == (=) } -> lower(XB, Ctx, Value0)
    ;   { compound_assignment(Op, BinOp) },
        place_read(P, Ctx, Cur),
        lower(XB, Ctx, VB),
        binary(BinOp, Cur, VB, Ctx, Value0)
    ),
    place_write(P, Value0, Ctx, R).
lower_node(val(_, incdec(Op, X)), Ctx, R) --> !,           % 6.5.2.4, 6.5.3.1
    place(X, Ctx, P),
    place_read(P, Ctx, Cur),
    { memberchk(Op, [preinc, postinc]) -> BinOp = add ; BinOp = sub },
    binary(BinOp, Cur, v(const(1), int), Ctx, Value0),
    place_write(P, Value0, Ctx, New),
    { memberchk(Op, [preinc, predec]) -> R = New ; R = Cur }.
lower_node(val(_, call(XF, XArgs)), Ctx, R) --> !,         % 6.5.2.2
    callee(XF, Ctx, Callee, func(RetType, Ps, _)),
    { Ps == unspecified -> ParamTypes = [] ; ParamTypes = Ps },
    call_args(XArgs, ParamTypes, Ctx, IRArgs0),
    env(Env),
    { su(RetType), ret_shape(RetType, Env, unknown, sret) -> NSret = 1 ; NSret = 0 },
    pad_args(IRArgs0, NSret, IRArgs),
    call_result(Callee, RetType, IRArgs, Ctx, R).
lower_node(val(_, builtin(Name, Args)), Ctx, R) --> !,
    builtin(Name, Args, Ctx, R).
lower_node(val(T, bit_cast(XA)), Ctx, R) --> !,
    % The operand's bytes stored, then loaded as T (c_types bit_castable/3).
    lower(XA, Ctx, v(V, A)),
    local_slot(T, Tmp),
    store_typed(A, V, Tmp),
    loaded(T, Tmp, Ctx, R).
lower_node(val(T, cast(TN, XV)), Ctx, R) -->              % 6.5.4
    { unqualified(T, ptr(_)), lowered(XV, IT), int_type(IT),
      laundered(XV, XP, Hole, XV1) }, !,
    evaluated_type(TN, Ctx, Type),
    lower(XP, Ctx, VP),
    { Hole = VP, VP = v(P, _) },
    lower(XV1, Ctx, VI),
    convert(VI, ulong, v(I, _)),
    let(l, ptoi, [P], IP),
    let(l, sub, [I, IP], D),
    let(p, add, [P, D], Q),
    { R = v(Q, Type) }.
lower_node(val(_, cast(TN, XV)), Ctx, R) --> !,            % 6.5.4
    evaluated_type(TN, Ctx, Type),
    lower(XV, Ctx, Value0),
    converted(Value0, Type, R).
lower_node(val(_, lowered(V)), _, V) --> !.
lower_node(val(_, va_arg(TN, XA)), Ctx, v(Tmp, Type)) -->  % 7.16.1.1
    evaluated_type(TN, Ctx, Type),
    { su(Type) }, !,
    % A struct or union is in consecutive 8-byte cells of the packet,
    % as the caller passed it: one va_arg per eightbyte, a pointer one
    % with its capability.
    % A long double member is one 16-aligned x cell (va_cells/5).
    env(Env),
    { ctx_loc(Ctx, Loc), eightbytes(Type, Env, Loc, Ebs0),
      leaves(Type, Env, 0, Leaves, []),
      va_cells(Ebs0, Leaves, Type, Loc, Ebs) },
    lower(XA, Ctx, v(P, _)),
    va_words(Ebs, P, Words),
    local_slot(Type, Tmp),
    store_words(Ebs, Words, Tmp).
lower_node(val(_, va_arg(TN, XA)), Ctx, v(V, Type)) --> !, % 7.16.1.1
    evaluated_type(TN, Ctx, Type),
    { ctx_loc(Ctx, Loc),
      ( type_class(Type, K), memberchk(Type, [int, uint, long, ulong, llong, ullong, double, ldouble, ptr(_)])
      -> true
      ; sema_error(Loc, 'unsupported va_arg type ~w', [Type]) ) },
    lower(XA, Ctx, v(P, _)),
    let(K, va_arg, [P], V).
% The operand of sizeof is evaluated only when it has a variable length
% array type, whose size is then known only at run time (6.5.3.4p2).
lower_node(val(_, sizeof(TN)), Ctx, v(Size, ulong)) --> % 6.5.3.4
    { TN = type(_, _) }, !,
    env(Env),
    { ctx_loc(Ctx, Loc), type_name_type(TN, Type0, Env, _) },
    (   { vla_type(Type0) }
    ->  evaluated_type(TN, Ctx, Type),
        extent(Type, Ctx, Size)
    ;   { type_size(TN, Env, Loc, Size0), Size = const(Size0) }
    ).
% sizeof (T[]){...}: the compound literal's array type is completed by
% its initializer (6.5.2.5p3, 6.7.9p22); the operand is not evaluated.
lower_node(val(_, sizeof(obj(array(_, none), complit(TN, Init)))), Ctx,
           v(const(Size), ulong)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc), type_name_type(TN, T0, Env, Env1),
      complete_array(T0, Init, T, Loc, Env1, whole),
      type_size_align(T, Env1, Size, _) }.
lower_node(val(_, sizeof(X)), Ctx, v(Size, ulong)) --> !,
    (   { tree_type(X, T), vla_type(T) }
    ->  place(X, Ctx, lv(_, Type)),
        extent(Type, Ctx, Size)
    ;   env(Env),
        { tree_type(X, Type), ctx_loc(Ctx, Loc),
          catch(sizeof_size(Type, Env, Size0), bad(Why),
                sema_error(Loc, 'sizeof: ~w', [Why])),
          Size = const(Size0) }
    ).
lower_node(val(_, alignof(TN)), Ctx, v(const(Align), ulong)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc),
      type_name_type(TN, Type0, Env, Env1), supported(Type0, Loc),
      element_type(Type0, Type),
      catch(type_size_align(Type, Env1, _, Align0), bad(Why),
            sema_error(Loc, 'alignof: ~w', [Why])),
      (   TN = type(Specs, Syntax),
          inherited_alignment(Specs, Syntax, Env, [align(A)])
      ->  Align = A
      ;   Align = Align0
      ) }.
% offsetof with a variable array index (GCC and clang accept
% offsetof(struct seccomp_data, args[x])) is computed at run time.
lower_node(val(_, offsetof(TN, Path)), Ctx, v(V, ulong)) --> !,
    env(Env),
    (   { catch(const_value(offsetof(TN, Path), Env, V0, _), not_constant, fail) }
    ->  { V = const(V0) }
    ;   { ctx_loc(Ctx, Loc), type_name_type(TN, T, Env, Env1),
          ( memberchk(index(_), Path) -> true ; sema_error(Loc, 'bad offsetof', []) ) },
        runtime_offset(Path, T, Env1, Ctx, const(0), V)
    ).
lower_node(val(_, stmtexpr(at(_, block(Items)))), Ctx, R) --> % GNU ({ ... })
    save_scope(Scope), env(Env), { cleanup_keys(Env, Outer) },
    statement_expression_items(Items, Ctx, R0),
    leaving(Outer, Ks),
    (   { Ks \== [], R0 = v(A, T), su(T) }       % the value, before them
    ->  local_slot(T, A1), copy_object(T, A, A1), { R = v(A1, T) }
    ;   { R = R0 }
    ),
    run_cleanups(Ks),
    restore_scope(Scope).

% converted(+Value0, +Type, -R)//: R is Value0 converted to Type, as
% assignment and casts convert, the elaborator having judged that they
% may: to void it is nothing, a struct or union stays its address.
converted(_, void, v(const(0), void)) --> !.
converted(v(Addr, _), Type, v(Addr, Type)) --> { su(Type) }, !.
converted(Value0, Type, R) --> convert(Value0, Type, R).

% loaded(+U, +Addr, +Ctx, -R)//: R is the value of type U stored at
% Addr: a struct or union stands for its address.
loaded(U, Addr, _, v(Addr, U)) --> { su(U) }, !.
loaded(U, Addr, Ctx, v(V, U)) --> load_typed(U, Addr, Ctx, V).

% decayed(+P, +T, +Ctx, -R)//: R, of pointer type T, points at the
% object or function P. A function's address is copied into a temp;
% setjmp's has none, since it is an intrinsic.
decayed(lv(Addr, _), T, _, v(Addr, U)) --> { unqualified(T, U) }.
decayed(fd(global(Sym), _), _, Ctx, _) -->
    { op_kind(setjmp(Sym), setjmp) }, !,
    { ctx_loc(Ctx, Loc),
      sema_error(Loc, 'setjmp requires a direct call, not a function pointer', []) }.
decayed(fd(global(Sym), Type), _, _, v(Addr, ptr(Type))) --> !,
    let(p, copy, [global(Sym)], Addr).
decayed(fd(Callee, Type), _, _, v(Callee, ptr(Type))) --> [].

/* place(+X, +Ctx, -P)//: P is lv(Addr, Type), the object that typed
   tree X designates, or fd(Callee, Type) for a function. */
place(X, Ctx, P) -->
    typed_origin(X, Ctx, Parent), place_node(X, Ctx, P), restore_origin(Parent).

place_node(obj(_, id(Name)), _, P) --> !, env(Env),
    { lookup_ordinary(Env, Name, Binding) },
    binding_obj(Binding, P),
    ( { Binding = gvar(_, Sym, _, _), P = lv(tmp(T), _) }
    -> binding_context(Name, Binding), record(hint(T, named(global(Sym), address)))
    ; [] ).
place_node(fun(_, id(Name)), _, P) --> !, env(Env),
    { lookup_ordinary(Env, Name, Binding) },
    binding_obj(Binding, P).
place_node(obj(_, predefined(_)), Ctx, P) --> !,           % 6.4.2.2
    { Ctx = ctx(Func, _, _, _, _), atom_codes(Func, Bytes) },
    place(obj(_, str(Bytes)), Ctx, P).
place_node(obj(_, str(Bytes)), _, lv(Addr, array(char, N))) --> !,
    env(Env0),
    { new_literal(Bytes, Sym, Env0, Env),
      length(Bytes, N0),
      N is N0 + 1 },
    set_env(Env),
    let(p, copy, [global(Sym)], Addr).
place_node(obj(_, wstr(WideType, Values)), _, lv(Addr, array(WideType, N))) --> !,
    env(Env0),
    { new_literal(w(WideType, Values), Sym, Env0, Env),
      length(Values, N0),
      N is N0 + 1 },
    set_env(Env),
    let(p, copy, [global(Sym)], Addr).
% A compound literal is an unnamed local, initialized where it appears.
place_node(obj(_, complit(TN, Init)), Ctx, lv(Addr, Type)) --> !, % 6.5.2.5
    env(Env),
    { ctx_loc(Ctx, Loc),
      type_name_type(TN, Type00, Env, _),
      ( vla_type(Type00)                                    % 6.5.2.5p1
      -> sema_error(Loc, 'a compound literal cannot have a variable length array type', [])
      ; true ) },
    evaluated_type(TN, Ctx, Type0),
    { complete_array(Type0, Init, Type, Loc, Env, whole),
      check_local_type(Type, Env, Loc, 'compound literal') },
    local_slot(Type, Addr),
    init(Addr, Type, Init, Ctx).
place_node(obj(T, deref(XV)), Ctx, lv(V, U)) --> !,        % 6.5.3.2p4
    lower(XV, Ctx, v(V, PT)),
    { ( PT = ptr(L) -> true ; L = T ), vm_typed(T, L, U) }.
place_node(fun(T, deref(XV)), Ctx, fd(Callee, U)) --> !,
    lower(XV, Ctx, v(V, _)),
    callee_temp(V, Callee),
    { unqualified(T, U) }.
place_node(obj(T, member(XS, F)), Ctx, lv(P, U)) -->       % 6.5.2.3p3
    place(XS, Ctx, lv(Addr, SU)),
    member_lv(Addr, SU, F, Ctx, P, _),
    { unqualified(T, U) }.
place_node(obj(_, bitfield(member(XS, F), W)), Ctx, bits(P, T, Pos, W)) --> % 6.7.2.1p10
    place(XS, Ctx, lv(Addr, SU)),
    env(Env),
    { member_layout(SU, F, Env, T, Off, bits(Pos, W)) },
    offset(Addr, Off, P).

/* An object is read and written through its place: lv(Addr, Type), or
   bits(Addr, Type, Pos, W), a bit-field of W bits from bit Pos of the
   Type at Addr. A bit-field is read by shifting it to the bottom of its
   unit, extended by its type's sign, and written by merging it into the
   unit; its value has its promoted type (bitfield_promotion/3). */

% place_loaded(+P, +U, +Ctx, -R)//: R is the value, of type U, of the
% object at place P.
place_loaded(lv(Addr, _), U, Ctx, R) --> loaded(U, Addr, Ctx, R).
place_loaded(bits(Addr, T, Pos, W), _, Ctx, R) -->
    place_read(bits(Addr, T, Pos, W), Ctx, R).

% place_read(+P, +Ctx, -R)//: R is the scalar value at place P.
place_read(lv(P, U), Ctx, v(Cur, U)) --> load_typed(U, P, Ctx, Cur).
place_read(bits(Addr, T, Pos, W), Ctx, R) -->
    load_typed(T, Addr, Ctx, Unit),
    { type_class(T, K), class_bits(K, KB), Up is KB - Pos - W },
    shifted(K, shl, Unit, Up, V1),
    bits_extended(T, W, V1, R).

% place_write(+P, +Value0, +Ctx, -R)//: store Value0, converted, at place
% P; R is the value stored.
place_write(lv(P, U), Value0, _, R) -->
    converted(Value0, U, R),
    { R = v(V, _) },
    store_typed(U, V, P).
place_write(bits(Addr, T, Pos, W), Value0, Ctx, R) -->
    convert(Value0, T, v(V, _)),
    load_typed(T, Addr, Ctx, Unit),
    { type_class(T, K), class_bits(K, KB),
      Mask is ((1 << W) - 1) << Pos,
      Keep is \Mask /\ ((1 << KB) - 1) },
    let(K, and, [Unit, const(Keep)], Kept),
    shifted(K, shl, V, Pos, V1),
    let(K, and, [V1, const(Mask)], Field),
    let(K, or, [Kept, Field], New),
    store_typed(T, New, Addr),
    { Up is KB - W },
    shifted(K, shl, V, Up, V2),
    bits_extended(T, W, V2, R).

% bits_extended(+T, +W, +V, -R)//: R is the W-bit field at the top of V,
% of T's class, moved down and extended as T's sign says, of the
% bit-field's promoted type.
bits_extended(T, W, V, R) -->
    { type_class(T, K), class_bits(K, KB), Down is KB - W,
      int_info(T, _, Sign), ( Sign == signed -> Op = sar ; Op = shr ),
      bitfield_promotion(T, W, P) },
    shifted(K, Op, V, Down, V1),
    convert(v(V1, T), P, R).

% shifted(+K, +Op, +V, +N, -R)//: R is V shifted by N bits.
shifted(_, _, V, 0, V) --> !.
shifted(K, Op, V, N, R) --> let(K, Op, [V, const(N)], R).

class_bits(w, 32).
class_bits(l, 64).

% load_typed(+Type, +Addr, +Ctx, -V)//: V is the scalar of Type loaded
% from Addr.
load_typed(Type, Addr, Ctx, V) -->
    (   { load_op(Type, Class, Op) } -> let(Class, load(Op), [Addr], V)
    ;   { ctx_loc(Ctx, Loc),
          sema_error(Loc, 'loading a ~w value is not supported yet', [Type]) }
    ).

% load_op(+Type, -Class, -Op): Class and load Op hold a scalar of Type:
% an integer narrower than 8 bytes is loaded extended into a w.
load_op(Type, Class, Op) :-
    int_info(Type, Size, Sign), !,
    type_class(Type, Class),
    ( Size =:= 8 -> Op = l ; narrow_type(Op, Size, Sign) ).
load_op(Type, Class, Class) :- type_class(Type, Class).

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
store_width(ldouble, x) :- !.
store_width(Type, Width) :-
    int_info(Type, Size, _),
    width_bytes(Width, Size), memberchk(Width, [b, h, w, l]), !.

% offset(+Addr, +Off, -P)//: P is the pointer Addr + Off (Addr itself
% for 0, with no instruction).
offset(Addr, 0, Addr) --> !.
offset(Addr, Off, P) --> let(p, add, [Addr, const(Off)], P).

% builtin(+Name, +Args, +Ctx, -R)//: R is the value of a call of
% builtin Name, which no declaration shadows, on source arguments Args.
builtin('__builtin_va_start', [A, _], Ctx, v(const(0), void)) --> !,
    env(Env),
    { ctx_loc(Ctx, Loc),
      ( lookup_ordinary(Env, builtin(va_args), Cursor) -> true
      ; sema_error(Loc, 'va_start outside a variadic function', []) ) },
    rval(A, Ctx, v(P, _)),
    emit(store(p, Cursor, P)).
builtin('__builtin_va_copy', [A, B], Ctx, v(const(0), void)) --> !,
    rval(A, Ctx, v(P, _)), rval(B, Ctx, v(Q, _)),
    let(p, load(p), [Q], V), emit(store(p, V, P)).
builtin('__builtin_va_end', [A], Ctx, v(const(0), void)) --> !,
    rval(A, Ctx, _).
builtin(Name, [], _, v(const(V), Type)) -->
    { float_builtin(Name, Type, V) }, !.
builtin('__builtin_constant_p', [Expr], _, v(const(V), int)) --> !,
    env(Env),
    { ( catch(constant_value(Expr, Env, _, _), not_constant, fail)
      -> V = 1
      ; V = 0
      ) }.
builtin(Name, Args, _, v(const(V), ulong)) -->
    env(Env), { object_size(Name, Args, Env, V) }, !.
builtin('__builtin_unreachable', [], _, v(const(0), void)) --> !,
    term(unreachable).
builtin('__builtin_alloca', [Size], Ctx, v(Addr, ptr(void))) --> !,
    rval(Size, Ctx, V0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(Size, V0, ulong, Loc, v(N, _)),
    let(p, alloc(16), [N], Addr).
builtin(Name, [A], Ctx, v(D, double)) -->
    { libm_builtin(Name, F) }, !,
    rval(A, Ctx, V0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(A, V0, double, Loc, v(X, _)),
    fresh(D),
    emit(call(result(D, d), global(F), [arg(d, X)])).
% __builtin_isnan(x): x is unordered with itself. A float compares as
% itself; anything else (double, long double, an integer) as a double,
% which keeps a NaN a NaN and makes no other value one.
builtin('__builtin_isnan', [A], Ctx, v(N, int)) --> !,
    rval(A, Ctx, V0),
    (   { V0 = v(X, float) } -> { K = s }
    ;   { ctx_loc(Ctx, Loc) },
        assign_convert(A, V0, double, Loc, v(X, _)), { K = d }
    ),
    let(w, cmp(uo, K), [X, X], N).
% The classification builtins (c_types' classify_builtin/1) read the
% float's bits: Abs is them without the sign; Inf and MinNormal are
% the format's infinity and smallest normal magnitude.
builtin('__builtin_fpclassify', [Nan, Inf, Normal, Sub, Zero, A], Ctx, v(N, int)) --> !,
    float_bits(A, Ctx, f(K, _, Abs, InfBits, MinNormal)),
    let(w, cmp(ugt, K), [Abs, InfBits], IsNan),
    let(w, cmp(eq, K), [Abs, InfBits], IsInf),
    normal_flag(K, Abs, InfBits, MinNormal, IsNormal),
    let(w, cmp(eq, K), [Abs, const(0)], IsZero),
    let(w, cmp(ult, K), [Abs, MinNormal], Small),
    let(w, sub, [Small, IsZero], IsSub),
    class_sum([IsNan-Nan, IsInf-Inf, IsNormal-Normal, IsSub-Sub, IsZero-Zero],
              Ctx, const(0), N).
builtin('__builtin_signbitf', [A], Ctx, R) --> !,
    builtin('__builtin_signbit', [cast(type([tspec(float)], base), A)], Ctx, R).
% A long double's sign is the top bit of its 80, stored to memory: bit
% 15 of the 16-bit sign and exponent at byte 8.
builtin(Name, [A], Ctx, v(N, int)) -->
    { memberchk(Name, ['__builtin_signbit', '__builtin_signbitl']) },
    rval(A, Ctx, V0),
    { Name == '__builtin_signbitl' ; V0 = v(_, ldouble) }, !,
    { ctx_loc(Ctx, Loc) },
    assign_convert(A, V0, ldouble, Loc, v(X, _)),
    local_slot(ldouble, Slot),
    store_typed(ldouble, X, Slot),
    let(p, add, [Slot, const(8)], Top),
    load_typed(ushort, Top, Ctx, Exp),
    let(w, shr, [Exp, const(15)], N).
builtin(Name, [A], Ctx, v(N, int)) -->
    { classify_builtin(Name) }, !,
    float_bits(A, Ctx, f(K, Bits, Abs, InfBits, MinNormal)),
    classified(Name, K, Bits, Abs, InfBits, MinNormal, N).
% __builtin_flt_rounds(): libc's fegetround() reads the x87 control
% word, as clang's lowering does, and its FE_* value R (0, 0x400, 0x800,
% 0xc00) maps to FLT_ROUNDS by (0x2D >> (R >> 9)) & 3, clang's formula.
builtin('__builtin_flt_rounds', [], _, v(N, int)) --> !,
    fresh(R),
    emit(call(result(R, w), global(fegetround), [])),
    let(w, shr, [R, const(9)], S),
    let(w, shr, [const(0x2D), S], M),
    let(w, and, [M, const(3)], N).
% The atomics c_types leaves as builtins (atomic_builtin/4): pointer
% loads and stores at any order, which Fil-C's helpers make single-copy
% atomic, a sequentially consistent integer store, the store and a
% fence, any store to an _Atomic object, and __c11_atomic_init's plain
% store. The order is a constant without side effects.
builtin(Name, [P, _], Ctx, v(D, T)) -->
    { memberchk(Name, ['__atomic_load_n', '__c11_atomic_load']) }, !,
    rval(P, Ctx, v(Addr, ptr(T0))),
    { unqualified(T0, T) },
    let(p, atomic_load(p), [Addr], D).
builtin(Name, [P, V|O], Ctx, v(const(0), void)) -->
    { memberchk(Name-O, ['__atomic_store_n'-[_], '__c11_atomic_store'-[_],
                         '__c11_atomic_init'-[]]) }, !,
    rval(P, Ctx, v(Addr, ptr(T0))),
    rval(V, Ctx, V0),
    { unqualified(T0, T), ctx_loc(Ctx, Loc) },
    assign_convert(V, V0, T, Loc, v(X, _)),
    (   { O = [OE] } -> env(Env), { const_value(OE, Env, Order, _) },
        atomic_stored(T, X, Addr, Order)
    ;   store_typed(T, X, Addr)
    ).
% A seq_cst thread fence is mfence; x86-64 already orders loads and
% stores for the others, and a signal fence orders nothing a thread sees.
builtin(Name, [OE], _, v(const(0), void)) -->
    { memberchk(Name, ['__c11_atomic_thread_fence', '__c11_atomic_signal_fence',
                       '__atomic_thread_fence', '__atomic_signal_fence']) }, !,
    env(Env),
    (   { const_value(OE, Env, 5, _), atom_concat(_, '_thread_fence', Name) }
    ->  emit(fence)
    ;   []
    ).

% The read-modify-writes (c_types atomic_builtin/4): a cas loop, or one
% cas to compare and exchange. A __c11 fetch-and-op of a pointer returns
% the old address without a capability, as filcc's does.
builtin(Name, [P, V|_], Ctx, R) -->
    { rmw_builtin(Name, Family, Op, Which) }, !,
    rmw_arg_aligned(P, Ctx),
    rval(P, Ctx, v(Addr, ptr(T0))),
    rval(V, Ctx, V0),
    { unqualified(T0, T), ctx_loc(Ctx, Loc),
      ( T = ptr(_), Op \== xchg -> To = long ; To = T ) },
    assign_convert(V, V0, To, Loc, V1),
    rmw(T, Addr, Op, V1, Ctx, Old, New),
    { Which == old -> R0 = Old ; R0 = New },
    (   { Family == c11, T = ptr(_), Op \== xchg, R0 = v(A, _) }
    ->  let(l, ptoi, [A], I), let(p, itop, [I], D), { R = v(D, T) }
    ;   { R = R0 }
    ).
builtin(Name, [P, E, D|_], Ctx, v(Eq, bool)) -->
    { memberchk(Name, ['__c11_atomic_compare_exchange_strong',
                       '__c11_atomic_compare_exchange_weak',
                       '__atomic_compare_exchange_n']) }, !,
    rmw_arg_aligned(P, Ctx),
    rval(P, Ctx, v(Addr, ptr(T0))),
    rval(E, Ctx, v(EAddr, _)),
    rval(D, Ctx, D0),
    { unqualified(T0, T), ctx_loc(Ctx, Loc) },
    assign_convert(D, D0, T, Loc, v(New, _)),
    load_typed(T, EAddr, Ctx, Expected),
    cas_once(T, Addr, Expected, New, Got, Eq),
    % *Expected gets *P only on failure (7.17.7.4p2).
    label(LF), label(LJ),
    term(branch(Eq, LJ, LF)),
    start(LF), store_typed(T, Got, EAddr), term(goto(LJ)),
    start(LJ).
builtin(Name, [P, O, N|_], Ctx, R) -->
    { memberchk(Name-Which, ['__sync_val_compare_and_swap'-val,
                             '__sync_bool_compare_and_swap'-bool]) }, !,
    rmw_arg_aligned(P, Ctx),
    rval(P, Ctx, v(Addr, ptr(T0))),
    rval(O, Ctx, O0), rval(N, Ctx, N0),
    { unqualified(T0, T), ctx_loc(Ctx, Loc) },
    assign_convert(O, O0, T, Loc, v(Expected, _)),
    assign_convert(N, N0, T, Loc, v(New, _)),
    cas_once(T, Addr, Expected, New, Got, Eq),
    { Which == val -> R = v(Got, T) ; R = v(Eq, bool) }.
builtin('__sync_lock_release', [P|_], Ctx, v(const(0), void)) --> !,
    rval(P, Ctx, v(Addr, ptr(T0))),
    { unqualified(T0, T) },
    atomic_stored(T, const(0), Addr, 3).
builtin('__sync_synchronize', [], _, v(const(0), void)) --> !, emit(fence).
builtin('__atomic_test_and_set', [P, _], Ctx, v(Set, bool)) --> !,
    rval(P, Ctx, v(Addr, _)),
    rmw(uchar, Addr, xchg, v(const(1), uchar), Ctx, v(Old, _), _),
    let(w, cmp(ne, w), [Old, const(0)], Set).
builtin('__atomic_clear', [P, OE], Ctx, v(const(0), void)) --> !,
    rval(P, Ctx, v(Addr, _)),
    env(Env), { const_value(OE, Env, Order, _) },
    atomic_stored(uchar, const(0), Addr, Order).

builtin('__builtin_assume_aligned', [P|Rest], Ctx, R) --> !,
    rval(P, Ctx, VP),
    rvals_discarded(Rest, Ctx),
    { ctx_loc(Ctx, Loc) },
    assign_convert(P, VP, ptr(void), Loc, R).
builtin('__builtin_expect', [A, B], Ctx, R) --> !,
    rval(A, Ctx, VA),
    rval(B, Ctx, _),
    { ctx_loc(Ctx, Loc) },
    assign_convert(A, VA, long, Loc, R).
builtin(Name, Args, Ctx, R) -->
    { overflow_builtin(Name, Op, Fixed) }, !,
    checked_arithmetic(Args, Op, Fixed, Ctx, R).
builtin(Name, [A], Ctx, R) -->
    { bit_builtin(Name, Op, Type) }, !,
    rval(A, Ctx, V0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(A, V0, Type, Loc, V1),
    convert(V1, ulong, v(X, _)),
    { int_info(Type, Bytes, _), Bits is 8 * Bytes },
    bit_count(Op, Bits, X, N),
    convert(v(N, long), int, R).
builtin(Name, [A], Ctx, R) -->
    { builtin_type(Name, Type), atom_concat('__builtin_bswap', _, Name) }, !,
    rval(A, Ctx, V0),
    { ctx_loc(Ctx, Loc) },
    assign_convert(A, V0, Type, Loc, V1),
    convert(V1, ulong, v(X, _)),
    { int_info(Type, Bytes, _), Last is Bytes - 1,
      numlist(1, Last, Is) },
    swapped_bytes([0|Is], X, Last, none, Y),
    convert(v(Y, ulong), Type, R).

% A rotate by N of a W-bit X is (X << (N & W-1)) | (X >> (-N & W-1)),
% shifted the other way for a right rotate, so N = 0 shifts by nothing.
builtin(Name, [A, B], Ctx, R) -->
    { rotate_builtin(Name, Dir, Type) }, !,
    rval(A, Ctx, VA0), rval(B, Ctx, VB0),
    { ctx_loc(Ctx, Loc), int_info(Type, Bytes, _), Mask is 8 * Bytes - 1 },
    assign_convert(A, VA0, Type, Loc, VA), assign_convert(B, VB0, Type, Loc, VB),
    convert(VA, ulong, v(X, _)), convert(VB, ulong, v(N, _)),
    let(l, and, [N, const(Mask)], S),
    let(l, neg, [N], M), let(l, and, [M, const(Mask)], T),
    { Dir == left -> First = shl, Second = shr ; First = shr, Second = shl },
    let(l, First, [X, S], Y1), let(l, Second, [X, T], Y2),
    let(l, or, [Y1, Y2], Y),
    convert(v(Y, ulong), Type, R).
builtin(Name, _, Ctx, _) -->
    { ctx_loc(Ctx, Loc), sema_error(Loc, 'wrong arguments to ~w', [Name]) }.

% rmw(+U, +Addr, +Op, +V, +Ctx, -Old, -New)//: the atomic
% read-modify-write of the U at Addr, New being Old combined with the
% value V by Op (a binary operator, or xchg, nand, max or min): read the
% U, then repeat a cas of the read value for its combination until the
% cas finds it unchanged (ir.pl). The first read of a pointer is atomic,
% so the pair it combines is one; a float or double goes through its
% bits, compared as an integer. Old and New are those of the cas that
% succeeded.
rmw(U, Addr, Op, V, Ctx, v(Old, U), v(New, U)) -->
    { cas_repr(U, T, K, Bits), type_class(U, KU) },
    (   { T == p } -> let(p, atomic_load(p), [Addr], Old0)
    ;   let(K, load(T), [Addr], B0), from_bits(Bits, B0, Old0)
    ),
    here(LE), label(LL), label(LD), fresh(Old),
    term(goto(LL)),
    start_phi(LL, [phi(Old, KU, [LE-Old0, LB-Got])]),
    rmw_new(Op, v(Old, U), V, U, Ctx, v(New, _)),
    to_bits(Bits, Old, OB), to_bits(Bits, New, NB),
    let(K, cas(T), [OB, NB, Addr], GB),
    cas_equal(K, GB, OB, Eq),
    from_bits(Bits, GB, Got),
    here(LB), term(branch(Eq, LD, LL)),
    start(LD).

% rmw_aligned(+X, +Ctx)//: X, the object tree of an atomic
% read-modify-write, is not an underaligned member (c_types
% underaligned_member/4); rmw_arg_aligned(+P, +Ctx)// is that for the
% object a builtin's pointer argument P takes the address &X of.
rmw_arg_aligned(P, Ctx) -->
    env(Env),
    (   { elaborate(P, Env, val(_, addr(X))) } -> rmw_aligned(X, Ctx)
    ;   []
    ).
rmw_aligned(X, Ctx) -->
    env(Env),
    {   tree_type(X, T0), unqualified(T0, T),
        catch(type_size_align(T, Env, W, _), bad(_), fail),
        underaligned_member(X, Env, W, Name)
    ->  ctx_loc(Ctx, Loc),
        sema_error(Loc, 'an atomic read-modify-write of ~w, a member of a packed struct or union, may be misaligned; clang calls libatomic for it, which nanofil does not have', [Name])
    ;   true
    }.

% cas_once(+T, +Addr, +E, +N, -Got, -Eq)//: one cas of the T at Addr from
% E to N; Got is the old value and Eq whether it was E.
cas_once(T, Addr, E, N, Got, Eq) -->
    { cas_repr(T, CT, K, Bits) },
    to_bits(Bits, E, EB), to_bits(Bits, N, NB),
    let(K, cas(CT), [EB, NB, Addr], GB),
    cas_equal(K, GB, EB, Eq),
    from_bits(Bits, GB, Got).

% cas_repr(+U, -T, -K, -Bits): an atomic U is cas(T) of class K; a float
% or double is the cas of its bits (Bits s or d), else Bits is none.
cas_repr(float, uw, w, s) :- !.
cas_repr(double, l, l, d) :- !.
cas_repr(U, T, K, none) :- load_op(U, K, T).

cas_equal(p, A, B, Eq) --> !,
    let(l, ptoi, [A], IA), let(l, ptoi, [B], IB),
    let(w, cmp(eq, l), [IA, IB], Eq).
cas_equal(K, A, B, Eq) --> let(w, cmp(eq, K), [A, B], Eq).

to_bits(none, V, V) --> [].
to_bits(s, V, B) --> let(w, cast, [V], B).
to_bits(d, V, B) --> let(l, cast, [V], B).
from_bits(none, B, B) --> [].
from_bits(s, B, V) --> let(s, cast, [B], V).
from_bits(d, B, V) --> let(d, cast, [B], V).

% rmw_new(+Op, +Old, +V, +U, +Ctx, -New)//: New, of U, is Old combined
% with V by Op.
rmw_new(xchg, _, V, U, _, New) --> !, convert(V, U, New).
rmw_new(nand, Old, V, U, Ctx, New) --> !,
    binary(and, Old, V, Ctx, A), unary(bnot, A, Ctx, B), convert(B, U, New).
rmw_new(Op, Old, V, U, Ctx, New) -->
    { memberchk(Op-Cmp, [max-gt, min-lt]) }, !,
    % Old where Old Cmp V, else V: a mask, so the loop stays one block.
    binary(Cmp, Old, V, Ctx, C), convert(C, U, C1), unary(neg, C1, Ctx, M),
    convert(M, U, M1), binary(and, Old, M1, Ctx, A), unary(bnot, M1, Ctx, NM),
    binary(and, V, NM, Ctx, B), binary(or, A, B, Ctx, O), convert(O, U, New).
rmw_new(Op, Old, V, U, Ctx, New) -->
    binary(Op, Old, V, Ctx, B), convert(B, U, New).

% atomic_stored(+T, +X, +Addr, +Order)//: X, of T, stored atomically at
% Addr with memory order Order: a pointer through Fil-C's helper, which
% is seq_cst at every order, anything else by the store, then a fence
% when seq_cst.
atomic_stored(ptr(_), X, Addr, _) --> !, emit(atomic_store(p, X, Addr)).
atomic_stored(T, X, Addr, Order) -->
    store_typed(T, X, Addr),
    (   { Order =:= 5 } -> emit(fence) ; [] ).

classified('__builtin_isinf_sign', K, Bits, Abs, InfBits, _, N) -->
    let(w, cmp(eq, K), [Abs, InfBits], IsInf),
    let(w, cmp(slt, K), [Bits, const(0)], Neg),
    let(w, and, [IsInf, Neg], T), let(w, add, [T, T], T2),
    let(w, sub, [IsInf, T2], N).
classified('__builtin_isinf', K, _, Abs, InfBits, _, N) -->
    let(w, cmp(eq, K), [Abs, InfBits], N).
classified('__builtin_isfinite', K, _, Abs, InfBits, _, N) -->
    let(w, cmp(ult, K), [Abs, InfBits], N).
classified('__builtin_isnormal', K, _, Abs, InfBits, MinNormal, N) -->
    normal_flag(K, Abs, InfBits, MinNormal, N).
classified('__builtin_signbit', K, Bits, _, _, _, N) -->
    let(w, cmp(slt, K), [Bits, const(0)], N).

% A normal magnitude is in [MinNormal, Inf): one unsigned compare.
normal_flag(K, Abs, InfBits, MinNormal, N) -->
    let(K, sub, [Abs, MinNormal], D),
    { InfBits = const(I), MinNormal = const(M), R is I - M },
    let(w, cmp(ult, K), [D, const(R)], N).

% class_sum(+Flags, +Ctx, +Acc, -Sum)//: Sum is Acc plus each Flag-E
% pair's flag (0 or 1) times E, E converted to int.
class_sum([], _, Sum, Sum) --> [].
class_sum([Flag-E|Fs], Ctx, Acc, Sum) -->
    rval(E, Ctx, V0), { ctx_loc(Ctx, Loc) },
    assign_convert(E, V0, int, Loc, v(X, _)),
    let(w, mul, [Flag, X], T),
    let(w, add, [Acc, T], Acc1),
    class_sum(Fs, Ctx, Acc1, Sum).

% float_bits(+A, +Ctx, -F)//: F = f(K, Bits, Abs, Inf, MinNormal), the
% bits of A as an integer of class K: a float's at w, anything else's as
% a double at l.
float_bits(A, Ctx, f(K, Bits, Abs, const(Inf), const(MinNormal))) -->
    rval(A, Ctx, V0), { ctx_loc(Ctx, Loc) },
    (   { V0 = v(X, float) }
    ->  { K = w, Inf = 0x7f800000, MinNormal = 0x00800000, Mask = 0x7fffffff },
        let(w, cast, [X], Bits)
    ;   { V0 = v(_, ldouble) }
    ->  { sema_error(Loc, 'classifying a long double is not supported', []) }
    ;   assign_convert(A, V0, double, Loc, v(X, _)),
        { K = l, Inf = 0x7ff0000000000000, MinNormal = 0x0010000000000000,
          Mask = 0x7fffffffffffffff },
        let(l, cast, [X], Bits)
    ),
    let(K, and, [Bits, const(Mask)], Abs).

% bit_count(+Op, +Bits, +X, -N)//: N is the number of trailing zeros,
% leading zeros or ones of X, a Bits-wide unsigned value zero-extended
% to 64 bits; branch-free, so the operand 0 (undefined for ctz and clz)
% needs no block.
bit_count(popcount, _, X, N) --> popcount64(X, N).
bit_count(ctz, _, X, N) -->
    let(l, neg, [X], M), let(l, and, [X, M], Low),
    let(l, sub, [Low, const(1)], Below), popcount64(Below, N).
% ffs: popcount of the bits up to the lowest set one, times 1 if X is
% nonzero (the top bit of X | -X), so 0 for 0.
bit_count(ffs, _, X, N) -->
    let(l, neg, [X], M), let(l, and, [X, M], Low),
    let(l, add, [Low, Low], Low2), let(l, sub, [Low2, const(1)], Upto),
    popcount64(Upto, P),
    let(l, or, [X, M], Any), let(l, shr, [Any, const(63)], NZ),
    let(l, mul, [P, NZ], N).
bit_count(clz, Bits, X, N) -->
    smear([1, 2, 4, 8, 16, 32], X, S), popcount64(S, P),
    let(l, sub, [P, const(Bits)], NegN), let(l, neg, [NegN], N).

smear([], X, X) --> [].
smear([Sh|Shs], X, Y) -->
    let(l, shr, [X, const(Sh)], T), let(l, or, [X, T], X1), smear(Shs, X1, Y).

popcount64(X, N) -->
    let(l, shr, [X, const(1)], A1), let(l, and, [A1, const(0x5555555555555555)], A2),
    let(l, sub, [X, A2], B),
    let(l, and, [B, const(0x3333333333333333)], C1),
    let(l, shr, [B, const(2)], C2), let(l, and, [C2, const(0x3333333333333333)], C3),
    let(l, add, [C1, C3], C),
    let(l, shr, [C, const(4)], D1), let(l, add, [C, D1], D2),
    let(l, and, [D2, const(0x0f0f0f0f0f0f0f0f)], D),
    let(l, mul, [D, const(0x0101010101010101)], E),
    let(l, shr, [E, const(56)], N).

% swapped_bytes(+Is, +X, +Last, +Y0, -Y)//: Y is Y0 (none for nothing
% yet) with each byte I in Is of X moved to byte Last - I.
swapped_bytes([], _, _, Y, Y) --> [].
swapped_bytes([I|Is], X, Last, Y0, Y) -->
    { From is 8 * I, To is 8 * (Last - I) },
    let(l, shr, [X, const(From)], B0), let(l, and, [B0, const(255)], B),
    let(l, shl, [B, const(To)], Moved),
    (   { Y0 == none } -> { Y1 = Moved } ; let(l, or, [Y0, Moved], Y1) ),
    swapped_bytes(Is, X, Last, Y1, Y).
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
    let(w, cmp(ne, l), [Low, Back], BadLow),
    let(w, cmp(ne, l), [High, BackH], BadHigh),
    let(w, or, [BadLow, BadHigh], Flag).

overflow_operand(generic, V, V) --> !.
overflow_operand(Type, V, R) --> convert(V, Type, R).

% Extension to l must explicitly truncate a w value first: int_convert
% can reuse an l temp after a cast to int, as w consumers ignore its top.
overflow_widen(v(V, Type), Low, High) -->
    { int_info(Type, Size, Sign) },
    (   { Size < 8 }
    ->  { Sign == signed -> Ext = sw ; Ext = uw },
        let(l, ext(Ext), [V], Low)
    ;   { Low = V }
    ),
    (   { Sign == signed }
    ->  let(l, sar, [Low, const(63)], High)
    ;   { High = const(0) }
    ).

overflow_exact(add, X, XH, Y, YH, Low, High) -->
    let(l, add, [X, Y], Low),
    let(w, cmp(ult, l), [Low, X], Carry),
    let(l, ext(uw), [Carry], C),
    let(l, add, [XH, YH], H), let(l, add, [H, C], High).
overflow_exact(sub, X, XH, Y, YH, Low, High) -->
    let(l, sub, [X, Y], Low),
    let(w, cmp(ult, l), [X, Y], Borrow),
    let(l, ext(uw), [Borrow], C),
    let(l, sub, [XH, YH], H), let(l, sub, [H, C], High).
overflow_exact(mul, X, XH, Y, YH, Low, High) -->
    let(l, mul, [X, Y], Low),
    let(l, and, [X, const(4294967295)], XL),
    let(l, shr, [X, const(32)], XU),
    let(l, and, [Y, const(4294967295)], YL),
    let(l, shr, [Y, const(32)], YU),
    let(l, mul, [XL, YL], LL), let(l, mul, [XU, YL], UL),
    let(l, mul, [XL, YU], LU), let(l, mul, [XU, YU], UU),
    let(l, shr, [LL, const(32)], LLH),
    let(l, and, [UL, const(4294967295)], ULL),
    let(l, and, [LU, const(4294967295)], LUL),
    let(l, add, [LLH, ULL], Mid0), let(l, add, [Mid0, LUL], Mid),
    let(l, shr, [Mid, const(32)], Carry),
    let(l, shr, [UL, const(32)], ULH), let(l, shr, [LU, const(32)], LUH),
    let(l, add, [UU, ULH], H0), let(l, add, [H0, LUH], H1),
    let(l, add, [H1, Carry], H2),
    % Signed inputs contribute -Y or -X to the unsigned product's high limb.
    let(l, and, [XH, Y], CX), let(l, and, [YH, X], CY),
    let(l, sub, [H2, CX], H3), let(l, sub, [H3, CY], High).

% type_size(+TypeName, +Env, +Loc, -Size): Size is sizeof(TypeName), a
% type of constant size.
type_size(TypeName, Env0, Loc, Size) :-
    % A type name can define a tag (sizeof(union {...}), dash's
    % SHELL_SIZE), which its own size needs.
    type_name_type(TypeName, Type, Env0, Env),
    supported(Type, Loc),
    catch(sizeof_size(Type, Env, Size), bad(Why),
          sema_error(Loc, 'sizeof: ~w', [Why])).

% type_name(+TypeName, -Type, +Env, +Loc): Type is the type TypeName
% names in a constant initializer, where nothing is evaluated: a
% variably modified one is refused.
type_name(TypeName, Type, Env, Loc) :-
    type_name_type(TypeName, Type, Env, _),
    supported(Type, Loc),
    (   vm_type(Type)
    ->  sema_error(Loc, 'a variably modified type in a constant initializer', [])
    ;   true
    ).

% evaluated_type(+TypeName, +Ctx, -Type)//: Type is the type TypeName
% names where it is evaluated (a cast, va_arg, sizeof of a variable
% length array type, a compound literal), its size expressions evaluated
% there (6.8p4).
evaluated_type(TypeName, Ctx, Type) -->
    env(Env),
    { ctx_loc(Ctx, Loc), type_name_type(TypeName, Type0, Env, _),
      supported(Type0, Loc) },
    realized(Type0, Type, Ctx).

% supported(+Type, +Loc): throw a semantic error if nanofil does not
% support Type (c_types' unsupported_type/3).
supported(Type, Loc) :-
    (   unsupported_type(Type, F, As) -> sema_error(Loc, F, As) ; true ).

% vm_typed(+T, +L, -U): U is the type code generation gives a tree of
% type T, when lowering knows it as L. A variably modified T may still
% hold the size expressions of a type name that lowering has evaluated
% since, so L, which has the lengths, is used; otherwise T unqualified.
vm_typed(T, L, U) :- ( vm_type(T) -> U = L ; unqualified(T, U) ).

/* Variable length arrays (C11 6.7.6.2). The type of each has an
   unevaluated length vla(E), until lowering reaches the declaration or
   type name: realized//3 evaluates E there, once, and the type holds
   the value as dyn(V). extent//3 is the size of a type then: a product
   of those lengths and a constant. A goto or switch may not jump into
   the scope of an identifier of variably modified type (6.8.6.1p1,
   6.8.4.2p2); vm_scope//1 enters one, and labels, cases and gotos
   remember the scopes they are in. */

% realized(+Type0, -Type, +Ctx)//: Type is Type0 with the size
% expressions of its variable length arrays evaluated, outermost first,
% each converted to a length of type long. Pointers and a function's
% return type are evaluated through; its parameters are not, since only
% a function's definition evaluates them, on entry.
realized(T, T, _) --> { \+ vm_type(T) }, !.
realized(ptr(T0), ptr(T), Ctx) --> !, realized(T0, T, Ctx).
realized(array(_, vla(star)), _, Ctx) --> !,               % 6.7.6.2p4
    { ctx_loc(Ctx, Loc),
      sema_error(Loc, '[*] is allowed only in a function prototype', []) }.
realized(array(T0, vla(E)), array(T, dyn(V)), Ctx) --> !,
    judged_rval(E, Ctx, V0),
    { V0 = v(_, LT), ctx_loc(Ctx, Loc),
      ( int_type(LT) -> true
      ; sema_error(Loc, 'array size is not an integer', []) ) },
    convert(V0, long, v(V, _)),
    realized(T0, T, Ctx).
realized(array(T0, N), array(T, N), Ctx) --> !, realized(T0, T, Ctx).
realized(func(R0, Ps, A), func(R, Ps, A), Ctx) --> realized(R0, R, Ctx).

% extent(+Type, +Ctx, -Size)//: Size is the size in bytes of Type, an
% l value: a constant unless Type is a variable length array.
extent(Type, Ctx, Size) -->
    { vla_type(Type) }, !,
    { Type = array(T, N) },
    extent(T, Ctx, ElemSize),
    { array_length(N, Ctx, Length) },
    product(Length, ElemSize, Size).
extent(Type, Ctx, const(Size)) -->
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(type_size_align(Type, Env, Size, _), bad(Why),
            sema_error(Loc, 'size of ~w (~w)', [Type, Why])) }.

array_length(dyn(V), _, V).
array_length(N, _, const(N)) :- integer(N).
array_length(vla(_), Ctx, _) :-
    ctx_loc(Ctx, Loc),
    sema_error(Loc, 'the length of a variable length array is not known here', []).

product(const(A), const(B), const(C)) --> !, { C is A * B }.
product(A, const(1), A) --> !.
product(A, B, C) --> let(l, mul, [A, B], C).

% vm_scope(+Type)//: a new identifier of Type is in scope; if Type is
% variably modified, this is a scope no jump may enter.
vm_scope(Type) -->
    (   { vm_type(Type) }
    ->  env(Env0),
        { vm_scopes(Env0, Scopes), next_id(K, Env0, Env1),
          bind_ordinary('vm.scopes', [K|Scopes], Env1, Env) },
        set_env(Env)
    ;   []
    ).

% vm_scopes(+Env, -Scopes): Scopes are the variably modified scopes
% that are open, innermost first.
vm_scopes(Env, Scopes) :-
    ( lookup_ordinary(Env, 'vm.scopes', Scopes0) -> Scopes = Scopes0 ; Scopes = [] ).

% vm_label(+Key)//, vm_goto(+Name, +Loc)//: remember the open scopes of
% a label or case, and of a goto, in the function's label assoc.
vm_label(Key) -->
    env(Env), { vm_scopes(Env, Scopes) },
    state(st(E, C, I, B, N, Labels0, Cs, A), st(E, C, I, B, N, Labels, Cs, A)),
    { put_assoc(vm(Key), Labels0, Scopes, Labels) }.

vm_goto(Name, Loc) -->
    env(Env), { vm_scopes(Env, Scopes) },
    state(st(E, C, I, B, N, Labels0, Cs, A), st(E, C, I, B, N, Labels, Cs, A)),
    { ( get_assoc(vm_gotos, Labels0, Gs) -> true ; Gs = [] ),
      put_assoc(vm_gotos, Labels0, [goto(Name, Scopes, Loc)|Gs], Labels) }.

% vm_jumps//: no goto of the function enters a scope it is not in.
vm_jumps -->
    state(st(_, _, _, _, _, Labels, _, _)),
    { ( get_assoc(vm_gotos, Labels, Gs) -> true ; Gs = [] ),
      maplist(vm_goto_ok(Labels), Gs) }.

vm_goto_ok(Labels, goto(Name, From, Loc)) :-
    (   get_assoc(vm(label(Name)), Labels, To), \+ append(_, To, From)
    ->  (   entered_cleanup(To, From)
        ->  sema_error(Loc, 'cannot jump from this goto statement to its label: it bypasses the initialization of a variable with __attribute__((cleanup))', [])
        ;   sema_error(Loc, 'goto into the scope of a variably modified identifier', [])
        )
    ;   true
    ).

% entered_cleanup(+To, +From): a jump from scopes From to scopes To
% enters the scope of a cleanup variable (cleanup_var//4).
entered_cleanup(To, From) :- member(cleanup(K), To), \+ memberchk(cleanup(K), From), !.

% vm_case(+Ctx)//: a case or default label is in no variably modified
% scope its switch is not in.
vm_case(Ctx) -->
    env(Env),
    { vm_scopes(Env, Scopes),
      ( lookup_ordinary(Env, 'vm.switch', Outer) -> true ; Outer = [] ),
      ( Scopes == Outer -> true
      ; ctx_loc(Ctx, Loc), entered_cleanup(Scopes, Outer)
      -> sema_error(Loc, 'cannot jump from switch statement to this case label: it bypasses the initialization of a variable with __attribute__((cleanup))', [])
      ; ctx_loc(Ctx, Loc),
        sema_error(Loc, 'switch jumps into the scope of a variably modified identifier', []) ) }.

/* GNU's cleanup attribute (GCC, Common Variable Attributes): an
   automatic variable declared with cleanup(F) has F(&v) run when its
   scope ends, by falling off the end of its block, return (after the
   returned value is taken), break, continue or goto, in reverse order
   of declaration; longjmp runs none. Clang ignores it, with a warning,
   on a variable that is not automatic. Each such variable is a scope
   cleanup(K) in 'vm.scopes', so jumping into it is refused as clang
   refuses it, and K's call, F(&v) judged where v is declared, is kept
   in the label assoc with bindings of its own names, so a scope that
   shadows F or v cannot change it. A goto out of the scope runs the
   cleanups it leaves: a backward one before jumping, a forward one
   through a block emitted at its label. A function returning a struct
   copies the value before the cleanups run; clang, returning a named
   local in place (NRVO), lets the cleanup see the returned object. */
% cleanup_decls(+Decls, +Loc, +Fn, +Ctx)//: a cleanup attribute among a
% declaration's specifiers applies to each automatic variable it
% declares, as GCC's attributes in a specifier list apply to every
% declarator. Each variable's scope, and so its cleanup's, begins after
% its own declarator, so the cleanups of `T a = .., b = ..;` run b's
% first (C11 6.2.1p7; GLib's `g_autofree char *a = NULL, *b = NULL;`).
cleanup_decls([], _, _, _) --> [].
cleanup_decls([D|Ds], Loc, Fn, Ctx) -->
    local_decl(D, Ctx),
    (   { automatic(D), D = d(Name, _, _, _, _) } -> cleanup_var(Loc, Name, Fn, Ctx)
    ;   []
    ),
    cleanup_decls(Ds, Loc, Fn, Ctx).

cleanup_attr(Specs, Fn) :-
    member(attr([group(Tokens)]), Specs),
    append(_, [id(Word), group(Arg)|_], Tokens),
    memberchk(Word, [cleanup, '__cleanup__']), !,
    (   Arg = [id(Fn)] -> true
    ;   throw(nanofil_error('the cleanup attribute takes one function name'))
    ).

automatic(d(_, Type, Storage, _, _)) :-
    Type \= func(_, _, _),
    \+ memberchk(Storage, [static, extern]), Storage \= thread_local(_).

cleanup_var(Loc, Name, Fn, Ctx) -->
    env(Env0),
    { lookup_ordinary(Env0, Name, VarB),
      (   lookup_ordinary(Env0, Fn, FnB), FnB = fn(_, _, _) -> true
      ;   sema_error(Loc, '\'cleanup\' argument ~w is not a function', [Fn])
      ),
      cleanup_parameter(Loc, Fn, FnB, VarB),
      next_id(K, Env0, Env1),
      format(atom(V), 'cleanup.~w.var', [K]),
      format(atom(F), 'cleanup.~w.fn', [K]),
      Binds = [V-VarB, F-FnB],
      foldl(bind_pair, Binds, Env1, Env2),
      elaborate(call(id(F), [un(addr, id(V))]), Env2, Loc, X), value(X, XV),
      vm_scopes(Env2, Scopes),
      bind_ordinary('vm.scopes', [cleanup(K)|Scopes], Env2, Env) },
    set_env(Env),
    { ctx_at(Ctx, Loc, Ctx1) },
    state(st(E, C, I, B, N, Labels0, Cs, A), st(E, C, I, B, N, Labels, Cs, A)),
    { put_assoc(cleanup(K), Labels0, c(XV, Binds, Ctx1), Labels) }.

% cleanup_parameter(+Loc, +Fn, +FnBinding, +VarBinding): Fn takes one
% parameter, a pointer that &v converts to without a diagnostic: to
% void or to a type compatible with v's (clang's 'cleanup' checks; it
% calls Fn as if by assignment).
cleanup_parameter(Loc, Fn, fn(func(_, PTs, _), _, _), VarB) :-
    (   VarB = var(_, VT0) -> unqualified(VT0, VT)
    ;   sema_error(Loc, 'a cleanup attribute on this variable is not supported', [])
    ),
    (   PTs = [PT], unqualified(PT, ptr(Q0)), unqualified(Q0, Q),
        ( Q == void ; compatible_type(Q, VT) )
    ->  true
    ;   PTs = [PT]
    ->  sema_error(Loc, '\'cleanup\' function ~w parameter has type ~w which is incompatible with type ~w',
                   [Fn, PT, ptr(VT0)])
    ;   sema_error(Loc, '\'cleanup\' function ~w must take 1 parameter', [Fn])
    ).

bind_pair(Name-Binding, Env0, Env) :- bind_ordinary(Name, Binding, Env0, Env).

% cleanup_keys(+Env, -Ks): the cleanup variables in scope, innermost
% first.
cleanup_keys(Env, Ks) :-
    vm_scopes(Env, Scopes), findall(K, member(cleanup(K), Scopes), Ks).

% run_cleanups(+Ks)//: call the cleanups of Ks, in order; none where
% control cannot reach.
run_cleanups(Ks) --> cur(Cur), run_cleanups(Cur, Ks).

run_cleanups(none, _) --> !.
run_cleanups(_, []) --> !.
run_cleanups(_, [K|Ks]) -->
    state(st(_, _, _, _, _, Labels, _, _)),
    { get_assoc(cleanup(K), Labels, c(XV, Binds, Ctx)) },
    env(Env0), { foldl(bind_pair, Binds, Env0, Env) }, set_env(Env),
    lower(XV, Ctx, _),
    run_cleanups(Ks).

% leaving(+Outer, -Ks)//: Ks are the cleanups in scope that Outer, the
% cleanup keys of an enclosing point, does not have.
leaving(Outer, Ks) -->
    env(Env), { cleanup_keys(Env, Ks0), ( append(Ks, Outer, Ks0) -> true ; Ks = [] ) }.

% scope_cleanups(+Outer)//: at the end of a scope entered with cleanup
% keys Outer, run the scope's own.
scope_cleanups(Outer) --> leaving(Outer, Ks), run_cleanups(Ks).

% cleanup_targets(+Labels)//: break or continue to each of Labels runs
% the cleanups declared since.
cleanup_targets(Labels) -->
    env(Env0),
    { cleanup_keys(Env0, Ks),
      foldl(cleanup_target(Ks), Labels, Env0, Env) },
    set_env(Env).

cleanup_target(Ks, Label, Env0, Env) :- bind_ordinary(cleanup_at(Label), Ks, Env0, Env).

% jump_cleanups(+Target)//: before break or continue to Target.
jump_cleanups(none) --> [].
jump_cleanups(some(Label)) -->
    env(Env),
    { lookup_ordinary(Env, cleanup_at(Label), Outer) -> true ; Outer = [] },
    leaving(Outer, Ks), run_cleanups(Ks).

% return_cleanups(+RetType, +Addr0, -Addr)//: every cleanup in scope,
% before a return of the value at Addr0, copied first to Addr.
return_cleanups(RetType, Addr0, Addr) -->
    env(Env), { cleanup_keys(Env, Ks) },
    (   { Ks == [] } -> { Addr = Addr0 }
    ;   local_slot(RetType, Addr), copy_object(RetType, Addr0, Addr),
        run_cleanups(Ks)
    ).

% goto_cleanups(+Name, +Label, -Target)//: a goto to Name, whose block
% is Label, jumps to Target, having run the cleanups it leaves (a
% backward goto) or through Target, a block emitted at the label.
goto_cleanups(Name, Label, Target) -->
    env(Env), { cleanup_keys(Env, From) },
    state(st(_, _, _, _, _, Labels0, _, _)),
    (   { From == [] } -> { Target = Label }
    ;   { get_assoc(vm(label(Name)), Labels0, ToScopes) }
    ->  { Target = Label, findall(K, member(cleanup(K), ToScopes), To) },
        leaving(To, Ks), run_cleanups(Ks)
    ;   label(Target),
        state(st(E, C, I, B, N, Labels1, Cs, A), st(E, C, I, B, N, Labels, Cs, A)),
        { ( get_assoc(cleanup_gotos(Name), Labels1, Ps) -> true ; Ps = [] ),
          put_assoc(cleanup_gotos(Name), Labels1, [p(Target, From)|Ps], Labels) }
    ).

% label_cleanups(+Name, +Label)//: the blocks of the forward gotos to
% Name that leave cleanup scopes, each running those it leaves, before
% Label begins.
label_cleanups(Name, Label) -->
    state(st(_, _, _, _, _, Labels, _, _)),
    (   { get_assoc(cleanup_gotos(Name), Labels, Ps) }
    ->  term(goto(Label)),
        env(Env), { cleanup_keys(Env, To) },
        goto_blocks(Ps, To, Label)
    ;   []
    ).

goto_blocks([], _, _) --> [].
goto_blocks([p(T, From)|Ps], To, Label) -->
    start(T),
    { append(Ks, To, From) -> true ; Ks = [] },      % else vm_jumps refuses
    run_cleanups(Ks), term(goto(Label)),
    goto_blocks(Ps, To, Label).

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
    ->  let(w, cmp(ne, w), [W, const(0)], B)
    ;   { B = W }
    ).
convert(v(const(N), From), To, v(const(W), To)) -->
    { ( float_type(From) ; float_type(To) ),
      arithmetic_type(From), arithmetic_type(To),
      const_convert(N, From, To, W), integer(W) }, !.
convert(v(V, float), double, v(R, double)) --> !,
    let(d, ext(s), [V], R).
convert(v(V, double), float, v(R, float)) --> !,
    let(s, truncd, [V], R).
convert(v(V, float), ldouble, v(R, ldouble)) --> !,
    let(x, ext(s), [V], R).
convert(v(V, double), ldouble, v(R, ldouble)) --> !,
    let(x, ext(d), [V], R).
convert(v(V, ldouble), To, v(R, To)) -->
    { memberchk(To, [float, double]) }, !,
    { type_class(To, K) },
    let(K, truncx, [V], R).
convert(v(V, From), To, v(R, To)) -->
    { int_type(From), float_type(To),
      type_class(From, IK), int_info(From, _, Sign),
      int_float_op(IK, Sign, Op), type_class(To, K) }, !,
    let(K, Op, [V], R).
convert(v(V, From), To, v(R, To)) -->
    { float_type(From), int_type(To),
      type_class(From, K), int_info(To, _, Sign), type_class(To, IK),
      float_int_op(K, Sign, Op),
      conversion_int_type(IK, Sign, Base) }, !,
    let(IK, Op, [V], I),
    int_convert(Base, To, I, R).
convert(v(const(N), From), To, v(const(W), To)) -->
    { int_type(From), int_type(To) },
    !,
    { convert_int(N, To, W) }.
convert(v(V, From), To, v(V1, To)) -->
    { int_type(From), int_type(To) },
    !,
    int_convert(From, To, V, V1).
convert(v(const(N), From), ptr(P), v(const(W), ptr(P))) -->
    { int_type(From) },
    !,
    { convert_int(N, ulong, W) }.
convert(v(V, From), ptr(P), v(V1, ptr(P))) -->
    { int_type(From) },
    !,
    int_convert(From, ulong, V, V2),
    let(p, itop, [V2], V1).
convert(v(V, ptr(_)), To, R) -->
    { int_type(To) },
    !,
    let(l, ptoi, [V], Int),
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
float_int_op(x, signed, xtosi).
float_int_op(x, unsigned, xtoui).

% Float-to-integer instructions produce a full w/l; normalize narrow C
% destinations afterward, without ever routing an unsigned result via signed.
conversion_int_type(Class, Sign, Base) :-
    integer_type(Base, _, Sign, Rank), Rank >= 3, type_class(Base, Class), !.

% int_convert(+From, +To, +V, -V1)//: V1 is integer V of type From
% converted to type To, extended where the representation changes.
int_convert(From, To, V, V1) -->
    { int_info(From, SizeFrom, SignFrom), int_info(To, SizeTo, SignTo) },
    (   { SizeTo =:= 8, SizeFrom < 8 }
    ->  { narrow_type(Op, 4, SignFrom) },
        let(l, ext(Op), [V], V1)
    ;   { SizeTo < 4, \+ representable(SizeFrom, SignFrom, SizeTo, SignTo) }
    ->  { narrow_type(Op, SizeTo, SignTo) },
        let(w, ext(Op), [V], V1)
    ;   { V1 = V }
    ).

% representable(+SizeFrom, +SignFrom, +SizeTo, +SignTo): every value of
% the source type is a value of the target type.
representable(SizeFrom, SignFrom, SizeTo, SignTo) :-
    SizeTo > SizeFrom,
    ( SignTo == signed ; SignFrom == unsigned ),
    !.
representable(Size, Sign, Size, Sign).

% assign_convert(+Expr, +Value0, +To, +Loc, -R)//: R is Value0, the
% value of Expr, converted to To as by assignment: a return value, an
% initializer or a builtin's argument. c_types' assigned/4 judges that
% it may be.
assign_convert(Expr, Value0, To, Loc, R) -->
    env(Env),
    { assigned(Expr, Env, To, Loc) },
    converted(Value0, To, R).

%% Operators

% unary(+Op, +Value0, +Ctx, -R)//: R is unary operator Op applied to
% Value0, converted as unary_operand/3 says.
unary(Op, Value0, Ctx, R) -->
    { Value0 = v(_, From), ctx_loc(Ctx, Loc),
      (   unary_operand(Op, From, Type) -> true
      ;   sema_error(Loc, 'invalid operand to ~w: ~w', [Op, From])
      ) },
    unary_value(Op, Value0, Type, Ctx, R).

unary_value(not, Value0, _, Ctx, v(V, int)) --> !,
    truth(Value0, Ctx, W),
    let(w, cmp(eq, w), [W, const(0)], V).
unary_value(Op, Value0, Type, _, v(V, Type)) -->
    convert(Value0, Type, v(V1, _)),
    { type_class(Type, K) },
    unary_ins(Op, K, V1, V).

unary_ins(plus, _, V, V) --> [].
unary_ins(neg, K, V1, V) --> let(K, neg, [V1], V).
unary_ins(bnot, K, V1, V) --> let(K, xor, [V1, const(-1)], V).

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
    let(Class, IOp, [A, B], V).

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
    { vla_type(ElemType) }, !,
    extent(ElemType, Ctx, Size),
    convert(VI, long, v(I, _)),
    product(I, Size, OffV),
    let(p, Op, [P, OffV], R).
ptr_offset(Op, v(P, PtrType), ElemType, VI, Ctx, v(R, PtrType)) -->
    { PtrType = ptr(ElemType) },
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(arith_size(ElemType, Env, Size), bad(Why),
            sema_error(Loc, 'pointer arithmetic on ~w (~w)',
                       [ElemType, Why])) },
    convert(VI, long, v(I, _)),
    (   { I = const(N) } -> { Off is N * Size, OffV = const(Off) }
    ;   { Size =:= 1 } -> { OffV = I }
    ;   let(l, mul, [I, const(Size)], OffV)
    ),
    let(p, Op, [P, OffV], R).

% ptr_diff(+VA, +VB, +ElemType, +Ctx, -R)//: R is A - B in elements.
ptr_diff(v(A, _), v(B, _), ElemType, Ctx, v(V, long)) -->
    { vla_type(ElemType) }, !,
    extent(ElemType, Ctx, Size),
    let(l, ptoi, [A], IA),
    let(l, ptoi, [B], IB),
    let(l, sub, [IA, IB], Diff),
    let(l, div, [Diff, Size], V).
ptr_diff(v(A, _), v(B, _), ElemType, Ctx, v(V, long)) -->
    env(Env),
    { ctx_loc(Ctx, Loc),
      catch(arith_size(ElemType, Env, Size), bad(Why),
            sema_error(Loc, 'pointer subtraction on ~w (~w)',
                       [ElemType, Why])) },
    let(l, ptoi, [A], IA),
    let(l, ptoi, [B], IB),
    let(l, sub, [IA, IB], Diff),
    (   { Size =:= 1 } -> { V = Diff }
    ;   let(l, div, [Diff, const(Size)], V)
    ).

% logical(+Op, +XA, +XB, +Ctx, -R)//: R is XA && XB (land) or XA || XB
% (lor), a phi of 0/1 over the short-circuit edges.
logical(Op, XA, XB, Ctx, v(V, int)) -->
    lower(XA, Ctx, VA), truth(VA, Ctx, WA), here(LA),
    label(LRight), label(LJoin),
    {   Op == land -> Jump = branch(WA, LRight, LJoin), Short = 0
    ;   Jump = branch(WA, LJoin, LRight), Short = 1
    },
    term(Jump),
    start(LRight), lower(XB, Ctx, VB), truth(VB, Ctx, WB),
    let(w, cmp(ne, w), [WB, const(0)], NB),
    here(LB), term(goto(LJoin)),
    fresh(V),
    start_phi(LJoin, [phi(V, w, [LA-const(Short), LB-NB])]).

% join_arms(+Type, +LJoin, +LA-VA, +LB-VB, -R)//: start block LJoin; R
% is the ?: result there, a phi of VA from LA and VB from LB.
join_arms(Type, LJoin, LA-VA, LB-VB, R) -->
    (   { Type == void } -> start(LJoin), { R = v(const(0), void) }
    ;   { Type == ldouble }
    ->  fresh(A),
        start_phi(LJoin, [phi(A, p, [LA-VA, LB-VB])]),
        let(x, load(x), [A], V),
        { R = v(V, Type) }
    ;   { su(Type) -> Class = p ; type_class(Type, Class) },
        fresh(V),
        start_phi(LJoin, [phi(V, Class, [LA-VA, LB-VB])]),
        { R = v(V, Type) }
    ).

%% Calls

% A call (6.5.2.2) lowers from its tree, whose callee and arguments the
% elaborator has checked: the callee is a function, the arguments fit its
% arity and each converts to its parameter as by assignment.

% callee(+XF, +Ctx, -Callee, -FuncType)//: Callee is the IR callee of
% function pointer XF: the function itself when XF is a function
% designator decayed, else a temp holding the pointer.
callee(val(_, decay(X)), Ctx, Callee, FuncType) -->
    { X = fun(_, _) }, !,
    place(X, Ctx, fd(Callee, FuncType)).
callee(XF, Ctx, Callee, FuncType) -->
    lower(XF, Ctx, v(V, ptr(FuncType))),
    callee_temp(V, Callee).

% call_result(+Callee, +RetType, +IRArgs, +Ctx, -R)//: R is the result
% of calling Callee with IRArgs; setjmp and its kin are intrinsics.
call_result(global(Kind), RetType, IRArgs, Ctx, R) -->
    { op_kind(setjmp(Kind), setjmp) }, !,
    { ( RetType == int, setjmp_args(Kind, IRArgs, Operands) -> true
      ; ctx_loc(Ctx, Loc), sema_error(Loc, 'invalid ~w signature', [Kind]) ) },
    let(w, setjmp(Kind), Operands, V),
    { R = v(V, int) }.
call_result(Callee, RetType, IRArgs, Ctx, R) -->
    { ctx_loc(Ctx, Loc) },
    (   { su(RetType) } -> struct_call(RetType, Callee, IRArgs, Loc, R)
    ;   { RetType == ldouble }
    ->  struct_call(RetType, Callee, IRArgs, Loc, v(Tmp, _)),
        let(x, load(x), [Tmp], V),
        { R = v(V, RetType) }
    ;   { RetType == void }
    ->  emit(call(void, Callee, IRArgs)),
        { R = v(const(0), void) }
    ;   { type_class(RetType, Class) }
    ->  fresh(D),
        emit(call(result(D, Class), Callee, IRArgs)),
        normalize(RetType, D, V),
        { R = v(V, RetType) }
    ;   { sema_error(Loc, 'calls returning ~w are not supported yet',
                     [RetType]) }
    ).

setjmp_args(sigsetjmp, [arg(p, Buf), arg(w, Mask)], [Buf, Mask]).
setjmp_args(setjmp, [arg(p, Buf)], [Buf, const(0)]).
setjmp_args('_setjmp', [arg(p, Buf)], [Buf, const(0)]).

% call_args(+XArgs, +ParamTypes, +Ctx, -IRArgs)//: IRArgs pass the
% arguments whose trees are XArgs. A struct argument goes as
% one word per eightbyte; arguments past the prototype get the default
% promotions.
call_args([], _, _, []) --> [].
call_args([XA|XAs], [ParamType|ParamTypes], Ctx, IRArgs) -->
    { abi_memory(ParamType) }, !,
    lower(XA, Ctx, Value0),
    env(Env),
    % An argument for a transparent union initializes the member of its
    % own type in a temporary union, which is passed.
    (   { transparent_argument(ParamType, XA, Env, Member) }
    ->  local_slot(ParamType, V),
        converted(Value0, Member, v(MV, _)),
        store_typed(Member, MV, V)
    ;   converted(Value0, ParamType, v(V, _))
    ),
    abi_source(ParamType, V, Src),
    { ctx_loc(Ctx, Loc), arg_words(ParamType, Env, Loc, Ebs) },
    load_words(Ebs, Src, Words),
    { findall(arg(Class, W),
              ( nth0(I, Ebs, eb(_, _, Class)), nth0(I, Words, W) ),
              IRArgs00),
      pad16_mark(ParamType, Env, IRArgs00, IRArgs0) },
    call_args(XAs, ParamTypes, Ctx, IRArgs1),
    { append(IRArgs0, IRArgs1, IRArgs) }.
call_args([XA|XAs], ParamTypes0, Ctx, IRArgs) -->
    lower(XA, Ctx, Value0),
    (   { ParamTypes0 == [], Value0 = v(V0, Type0), abi_memory(Type0) }
    ->  env(Env),                       % 6.5.2.2p7: no conversion
        abi_source(Type0, V0, Src),
        { ctx_loc(Ctx, Loc), variadic_words(Type0, Env, Loc, Ebs) },
        load_words(Ebs, Src, Words),
        { findall(arg(Class, W),
                  ( nth0(I, Ebs, eb(_, _, Class)), nth0(I, Words, W) ),
                  IRArgs00),
          pad16_mark(Type0, Env, IRArgs00, IRArgs0),
          ParamTypes = [] }
    ;   (   { ParamTypes0 = [ParamType|ParamTypes] }
        ->  converted(Value0, ParamType, v(V, Type))
        ;   { ParamTypes = [], Value0 = v(_, Type0) },
            (   { arithmetic_type(Type0) }
            ->  { default_promotion(Type0, Type) },
                convert(Value0, Type, v(V, _))
            ;   { Type0 = ptr(_) } -> { Value0 = v(V, Type) }
            ;   { ctx_loc(Ctx, Loc),
                  sema_error(Loc,
                    'passing ~w to a variadic or unprototyped function is not supported',
                    [Type0]) }
            )
        ),
        { type_class(Type, Class), IRArgs0 = [arg(Class, V)] }
    ),
    call_args(XAs, ParamTypes, Ctx, IRArgs1),
    { append(IRArgs0, IRArgs1, IRArgs) }.

% va_cells(+Ebs0, +Leaves, +Type, +Loc, -Ebs): Ebs are the cells in
% which a variadic caller passed a struct or union of Type with
% eightbytes Ebs0 and scalars Leaves: a long double is one x cell,
% 16-aligned, covering its two eightbytes; a pointer eightbyte is p, any
% other l. The x cell aligns the cursor, so a 16-aligned Type must start
% with one.
va_cells(Ebs0, Leaves, Type, Loc, Ebs) :-
    (   memberchk(_-x87, Leaves), Ebs0 = [eb(O, _, _)|_], \+ memberchk(O-x87, Leaves)
    ->  sema_error(Loc, 'va_arg of ~w, which does not start with its long double, is not supported', [Type])
    ;   va_cells(Ebs0, Leaves, Ebs)
    ).
va_cells([], _, []).
va_cells([eb(O, _, _), _|Ebs0], Leaves, [eb(O, 10, x)|Ebs]) :-
    memberchk(O-x87, Leaves), !,
    va_cells(Ebs0, Leaves, Ebs).
va_cells([eb(O, N, K0)|Ebs0], Leaves, [eb(O, N, K)|Ebs]) :-
    ( K0 == p -> K = p ; K = l ),
    va_cells(Ebs0, Leaves, Ebs).

% va_words(+Ebs, +P, -Words)//: Words are read through the va_list at
% P, one per eightbyte at its class.
va_words([], _, []) --> [].
va_words([eb(_, _, K)|Ebs], P, [W|Ws]) -->
    let(K, va_arg, [P], W), va_words(Ebs, P, Ws).

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
        emit(call(result(D, Class), Callee, Args)),
        { Shape = words(Ebs) },
        store_words(Ebs, [D], Tmp)
    ;   { Shape = words(Ebs) },
        fresh(D1), fresh(D2),
        { Ebs = [eb(_, _, Class1), eb(_, _, Class2)] },
        emit(call(tuple([result(D1, Class1), result(D2, Class2)]), Callee, Args)),
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
    ->  { narrow_type(Op, Size, Sign) },
        let(w, ext(Op), [V0], V)
    ;   { Type == bool } -> let(w, ext(ub), [V0], V)
    ;   { V = V0 }
    ).

%% Struct values

/* A struct or union rvalue is v(Addr, T): Addr points at storage holding
   the value, a variable's or a temporary's. Copies, arguments and
   returns go an eightbyte at a time (eb(Offset, Bytes, Class)): class p
   if a pointer starts there, so its capability is copied with load(p) and
   store(p, ...), else l, with a short last eightbyte moved in 4-, 2- and 1-byte
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
member_ptrs(_, _, m(_, _, _, bits(_, _)), Offs, Offs).

% arg_words(+Type, +Env, +Loc, -Ebs): Ebs are the eightbytes in which a
% struct or union argument of Type is passed. A byval one (class MEMORY)
% goes only in the generic packet, where its words are its bytes, so a
% float member does not matter; its eightbytes start at an 8-aligned
% offset, as clang's do for alignments up to 8, the most nanofil's
% types have. Others are classified as SysV does (abi_eightbytes/4).
arg_words(ldouble, _, _, [eb(0, 8, l), eb(8, 8, l)]) :- !.
arg_words(Type, Env, Loc, Ebs) :-
    (   byval_type(Type, Env) -> eightbytes(Type, Env, Loc, Ebs)
    ;   abi_eightbytes(Type, Env, Loc, Ebs)
    ).

% abi_memory(+Type): an argument or result of Type crosses calls as the
% words of its bytes (arg_words/4): a struct or union, or a long double,
% whose 10 bytes and 6 zero bytes of padding go as two l words, as in
% clang's generic packet (docs/float.md).
abi_memory(Type) :- su(Type).
abi_memory(ldouble).

% abi_source(+Type, +V, -Addr)//: Addr holds the bytes of the value V of
% Type: V itself for a struct or union, whose value is its address; a
% fresh 16-byte local for a long double. Only store(x) ever writes the
% local, so its last 6 bytes stay zero.
abi_source(ldouble, V, Addr) --> !,
    local_slot(ldouble, Addr),
    emit(store(x, V, Addr)).
abi_source(_, Addr, Addr) --> [].

% arm_value(+Type, +V0, -V)//: V is the ?: arm value V0 as the join's
% phi carries it: a long double through memory, since no phi has class x.
arm_value(ldouble, V0, A) --> !, abi_source(ldouble, V0, A).
arm_value(_, V, V) --> [].

% x87_type(+Type, +Env): Type is or holds a long double. clang passes
% none of them in the fast convention's registers (a long double is
% digit 3, on the native stack), and nanofil makes a function taking or
% returning one generic-only (docs/float.md).
x87_type(ldouble, _) :- !.
x87_type(Type, Env) :-
    su(Type), leaves(Type, Env, 0, Leaves, []), memberchk(_-x87, Leaves).

% pad16_mark(+Type, +Env, +Args0, -Args): an argument of Type with
% alignment 16 that holds a long double starts at a 16-aligned packet
% offset, as clang lays out the generic packet: Args is Args0 after a
% pad16 marker, which pad_args//3 resolves once the word count before
% it is known.
pad16_mark(Type, Env, Args, [pad16|Args]) :-
    x87_type(Type, Env), !.
pad16_mark(_, _, Args, Args).

% pad_args(+Args0, +N0, -Args)// and pad_params(+Params0, +N0, -Params)//:
% each pad16 marker becomes a zero l word when N0 words, counting an
% sret pointer, precede it at an odd count, and is dropped otherwise.
pad_args([], _, []) --> [].
pad_args([pad16|As0], N0, As) --> !,
    (   { N0 mod 2 =:= 1 } -> { As = [arg(l, const(0))|As1], N = N0 + 1 }
    ;   { As = As1, N = N0 }
    ),
    { N1 is N }, pad_args(As0, N1, As1).
pad_args([A|As0], N0, [A|As]) --> { N is N0 + 1 }, pad_args(As0, N, As).

pad_params([], _, []) --> [].
pad_params([pad16|Ps0], N0, Ps) --> !,
    (   { N0 mod 2 =:= 1 } -> fresh(P), { Ps = [param(l, P)|Ps1], N is N0 + 1 }
    ;   { Ps = Ps1, N = N0 }
    ),
    pad_params(Ps0, N, Ps1).
pad_params([P|Ps0], N0, [P|Ps]) --> { N is N0 + 1 }, pad_params(Ps0, N, Ps).

% generic_only_type(+Type, +Env): clang gives a function taking a
% struct or union of Type no fast entry: it is byval, or (as for a
% result, float_pair_type/2) an eightbyte of it holds two floats, which clang passes as <2 x float>,
% a type outside the fast signature's digits. nanofil makes such a
% function generic-only too, so the signatures agree.
% A byval result is an sret pointer, which leaves the fast entry.
generic_only_type(Type, Env) :- x87_type(Type, Env), !.
generic_only_type(Type, Env) :- byval_type(Type, Env), !.
generic_only_type(Type, Env) :- float_pair_type(Type, Env).

float_pair_type(Type, Env) :-
    \+ byval_type(Type, Env),
    eightbytes(Type, Env, unknown, Ebs),
    leaves(Type, Env, 0, Leaves, []),
    member(eb(O, _, _), Ebs), End is O + 8,
    findall(T, ( member(Off-T, Leaves), Off >= O, Off < End ), [T1, T2|Ts]),
    forall(member(T, [T1, T2|Ts]), T == float), !.

% byval_type(+Type, +Env): a struct or union of Type has SysV class
% MEMORY, so clang passes it byval and returns it through sret: it is
% larger than 16 bytes, or packed with misaligned members.
byval_type(Type, Env) :-
    type_size_align(Type, Env, Size, _),
    ( Size > 16 -> true ; unaligned_type(Type, Env) ).

% ret_shape(+Type, +Env, +Loc, -Shape): Shape is how a struct or union
% of Type is returned: sret, or words(Eightbytes).
ret_shape(ldouble, _, _, words([eb(0, 8, l), eb(8, 8, l)])) :- !.
ret_shape(Type, Env, Loc, Shape) :-
    (   byval_type(Type, Env) -> Shape = sret
    ;   abi_eightbytes(Type, Env, Loc, Ebs),
        Shape = words(Ebs)
    ).

% abi_eightbytes(+Type, +Env, +Loc, -Ebs): the eightbytes of a struct
% or union of 16 bytes or less, classed as the SysV psABI (3.2.3) and
% clang do. An eightbyte is p where a pointer starts. One holding only
% floating members is SSE: d if a double is among them, s for a lone
% float at its start, else l, for clang's <2 x float>, whose bytes go
% in an integer word in nanofil and in the generic packet's cell in
% both (so the function is generic-only in clang, by signature). Any
% other eightbyte is INTEGER, l. One without a scalar in it (only
% padding, as after aligned(16) on a struct of one int, or only unnamed
% bit-fields) is NO_CLASS, and is not passed at all, as clang does: its
% coerced type covers only the other eightbyte.
abi_eightbytes(Type, Env, Loc, Ebs) :-
    classed_eightbytes(Type, Env, Loc, Leaves, Ebs0),
    include(holds_leaf(Leaves), Ebs0, Ebs).

% classed_eightbytes(+Type, +Env, +Loc, -Leaves, -Ebs): Ebs are all the
% eightbytes of Type, classed as abi_eightbytes/4 does; Leaves are its
% scalars (leaves/5).
classed_eightbytes(Type, Env, Loc, Leaves, Ebs) :-
    eightbytes(Type, Env, Loc, Ebs0),
    leaves(Type, Env, 0, Leaves, []),
    maplist(eightbyte_class(Leaves), Ebs0, Ebs).

% variadic_words(+Type, +Env, +Loc, -Ebs): the eightbytes in which a
% struct or union of Type is passed past a prototype. clang passes it
% byval there, every eightbyte in the packet, NO_CLASS ones included,
% which is where va_arg reads them.
variadic_words(Type, Env, Loc, Ebs) :-
    (   ( Type == ldouble ; byval_type(Type, Env) )
    ->  arg_words(Type, Env, Loc, Ebs)
    ;   classed_eightbytes(Type, Env, Loc, _, Ebs)
    ).

holds_leaf(Leaves, eb(O, _, _)) :-
    End is O + 8,
    member(Off-T, Leaves),
    ( T == x87 -> LeafEnd is Off + 16 ; LeafEnd is Off + 1 ),  % X87UP too
    Off < End, LeafEnd > O, !.

eightbyte_class(_, eb(O, N, p), eb(O, N, p)) :- !.
eightbyte_class(Leaves, eb(O, N, _), eb(O, N, K)) :-
    End is O + 8,
    findall(Off-T, ( member(Off-T, Leaves), Off >= O, Off < End ), In),
    (   In \== [], forall(member(_-T, In), memberchk(T, [float, double]))
    ->  (   memberchk(_-double, In) -> K = d
        ;   forall(member(Off-_, In), Off =:= O) -> K = s
        ;   K = l
        )
    ;   K = l
    ).

% leaves(+Type, +Env, +Base, -Leaves0, ?Leaves): Leaves0-Leaves are the
% scalars of Type as Offset-Kind, Offset from Base and Kind one of int,
% ptr, float, double or x87; a bit-field is an int at its unit.
leaves(float, _, B, [B-float|L], L) :- !.
leaves(double, _, B, [B-double|L], L) :- !.
leaves(ldouble, _, B, [B-x87|L], L) :- !.
leaves(ptr(_), _, B, [B-ptr|L], L) :- !.
leaves(array(T, N), Env, B, L0, L) :-
    integer(N), N > 0, !,
    type_size_align(T, Env, Size, _),
    Last is N - 1, numlist(0, Last, Is),
    foldl(elem_leaves(T, Env, B, Size), Is, L0, L).
leaves(SU, Env, B, L0, L) :-
    su(SU), !,
    SU =.. [_, Id], env_defs(Env, Defs),
    get_assoc(Id, Defs, def(_, Members, _, _)),
    foldl(member_leaves(Env, B), Members, L0, L).
leaves(array(_, _), _, _, L, L) :- !.
leaves(_, _, B, [B-int|L], L).

elem_leaves(T, Env, B, Size, I, L0, L) :-
    B1 is B + I * Size, leaves(T, Env, B1, L0, L).

member_leaves(Env, B, m(_, T, Off), L0, L) :-
    B1 is B + Off, leaves(T, Env, B1, L0, L).
member_leaves(_, B, m(_, _, Off, bits(_, _)), [B1-int|L], L) :- B1 is B + Off.

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
    ->  let(p, load(p), [S], V),
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
    let(l, load(Load), [S], V),
    emit(store(Store, V, D)),
    copy_pieces(Pieces, Src, Dst).

% load_words(+Ebs, +Addr, -Words)//: Words are the words of the value at
% Addr, one per eightbyte.
load_words([], _, []) --> [].
load_words([eb(Off, N, Class)|Ebs], Addr, [W|Words]) -->
    offset(Addr, Off, P),
    (   { memberchk(Class, [p, s, d, x]) } -> let(Class, load(Class), [P], W)
    ;   { pieces(N, 0, Pieces) },
        load_pieces(Pieces, P, none, W)
    ),
    load_words(Ebs, Addr, Words).

% load_pieces(+Pieces, +P, +Acc0, -W)//: W is Acc0 (none at first) or'd
% with each of Pieces loaded from P and shifted into place.
load_pieces([], _, W, W) --> [].
load_pieces([p(Off, _, Load, _)|Pieces], P, Acc0, W) -->
    offset(P, Off, P1),
    let(l, load(Load), [P1], Piece0),
    (   { Off =:= 0 } -> { Piece = Piece0 }
    ;   { Shift is 8 * Off },
        let(l, shl, [Piece0, const(Shift)], Piece)
    ),
    (   { Acc0 == none } -> { Acc = Piece }
    ;   let(l, or, [Acc0, Piece], Acc)
    ),
    load_pieces(Pieces, P, Acc, W).

% store_words(+Ebs, +Words, +Addr)//: store Words, one per eightbyte,
% into the object at Addr.
store_words([], [], _) --> [].
store_words([eb(Off, N, Class)|Ebs], [W|Words], Addr) -->
    offset(Addr, Off, P),
    (   { memberchk(Class, [p, s, d, x]) } -> emit(store(Class, W, P))
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
        let(l, shr, [W, const(Shift)], Piece)
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
    foldl(static_leaf_once(Loc), Leaves, s(Env0, [], 0)-no, s(Env, Chunks0, _)-_),
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
int_chunk(Off, Type, V, chunk(Off, N, item(Width, const(U)))) :-
    int_info(Type, N, _),
    memberchk(N-Width, [1-b, 2-h, 4-w, 8-l]),
    convert_int(V, Type, U).

% static_leaf_once(+Loc, +Leaf, +S0-Str0, -S-Str): static_leaf/4,
% committed: a choicepoint left per leaf would keep every leaf's state
% alive. Str is yes when the chunks may hold a string's bytes as one
% chunk; a leaf before the end so far (a designator that goes back)
% first splits those into a chunk per byte, so that it overrides only
% the bytes it covers.
static_leaf_once(Loc, Leaf, s(Env, Chunks0, End)-Str0, S-Str) :-
    arg(1, Leaf, Off),
    (   Str0 == yes, Off < End
    ->  split_strs(Chunks0, Chunks1), Str1 = no
    ;   Chunks1 = Chunks0, Str1 = Str0
    ),
    once(static_leaf(Loc, Leaf, s(Env, Chunks1, End), S)),
    ( functor(Leaf, bytes, 3) -> Str = yes ; Str = Str1 ).

split_strs([], []).
split_strs([chunk(Off, _, item(b, str(Cs)))|Chunks0], Chunks) :- !,
    str_byte_chunks(Cs, Off, Chunks, Chunks1),
    split_strs(Chunks0, Chunks1).
split_strs([Chunk|Chunks0], [Chunk|Chunks]) :- split_strs(Chunks0, Chunks).

str_byte_chunks([], _, Chunks, Chunks).
str_byte_chunks([C|Cs], Off, [chunk(Off, 1, item(b, const(N)))|Chunks], Chunks0) :-
    char_code(C, N), Off1 is Off + 1,
    str_byte_chunks(Cs, Off1, Chunks, Chunks0).

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
static_leaf(_, bytes(_, _, []), S, S) :- !.
static_leaf(_, bytes(Off, Type, Vs), s(Env, Chunks, End0),
            s(Env, [Chunk|Chunks], End)) :-
    maplist(byte_char(Type), Vs, Cs),
    length(Cs, N),
    Chunk = chunk(Off, N, item(b, str(Cs))),
    chunk_end(Chunk, End0, End).
static_leaf(_, val(Off, Type, V), s(Env, Chunks, End0),
            s(Env, [Chunk|Chunks], End)) :-
    int_chunk(Off, Type, V, Chunk),
    chunk_end(Chunk, End0, End).
static_leaf(Loc, expr(Off, Type, Expr), s(Env0, Chunks, End0),
            s(Env, [Chunk|Chunks], End)) :-
    expr_chunk(Type, Off, Expr, Loc, Env0, Env, Chunk),
    chunk_end(Chunk, End0, End).

static_leaf(Loc, bits(Off, Type, Pos, W, Expr), s(Env, Chunks0, End0),
            s(Env, Chunks, End)) :-
    (   catch(constant_value(Expr, Env, V0, From), not_constant, fail),
        const_convert(V0, From, Type, V), integer(V)
    ->  true
    ;   sema_error(Loc, 'initializer is not a constant', [])
    ),
    Start is 8 * Off + Pos,
    First is Start // 8, Last is (Start + W - 1) // 8,
    numlist(First, Last, Bytes),
    foldl(bitfield_byte(Start, W, V), Bytes, Chunks0, Chunks),
    End is max(End0, Last + 1).

% bitfield_byte(+Start, +W, +V, +Byte, +Chunks0, -Chunks): Chunks adds
% to Chunks0 the byte at offset Byte with its bits of the W-bit field V,
% starting at bit Start, merged into the bits an earlier bit-field put
% there.
bitfield_byte(Start, W, V, Byte, Chunks0, [chunk(Byte, 1, item(b, const(New)))|Chunks0]) :-
    (   member(chunk(Byte, N, Item), Chunks0)
    ->  ( N =:= 1, Item = item(b, const(Old)) -> true ; Old = 0 )
    ;   Old = 0
    ),
    Shift is Start - 8 * Byte,
    Mask is (((1 << W) - 1) << (Shift + 64)) >> 64 /\ 255,
    Bits is ((V /\ ((1 << W) - 1)) << (Shift + 64)) >> 64 /\ 255,
    New is (Old /\ \Mask /\ 255) \/ Bits.

byte_char(Type, V, C) :- convert_int(V, Type, U), N is U /\ 255, char_code(C, N).

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
    -> type_class(Type, K), width_bytes(K, N),
       Chunk = chunk(Off, N, item(K, const(V)))
    ; int_chunk(Off, Type, V, Chunk)
    ).
expr_chunk(ptr(_), Off, Expr, Loc, Env0, Env, Chunk) :- !,
    (   elaborate(Expr, Env0, Loc, X) -> value(X, XV)
    ;   sema_error(Loc, 'initializer is not an address constant', [])
    ),
    address_constant(XV, Loc, Env0, Env, R),
    (   R = sym(Sym, SymOff)
    ->  Chunk = chunk(Off, 8, item(p, sym(Sym, SymOff)))
    ;   R = int(N)
    ->  Chunk = chunk(Off, 8, item(l, const(N)))
    ;   Chunk = chunk(Off, 8, item(l, const(0)))
    ).
expr_chunk(Type, _, _, Loc, _, _, _) :-
    sema_error(Loc, 'cannot statically initialize a ~w', [Type]).

/* address_constant(+XV, +Loc, +Env0, -Env, -R): the value tree XV is an
   address constant (C11 6.6p9), R = sym(Symbol, Offset), or a null
   pointer, R = null, or an integer constant cast to a pointer, R =
   int(Address). It is the address of a static object or a
   function, perhaps cast, plus or minus an integer constant; string
   literals and compound literals become data of their own. */
address_constant(val(_, decay(X)), Loc, Env0, Env, R) :- !,
    place_constant(X, Loc, Env0, Env, R).
address_constant(val(_, addr(X)), Loc, Env0, Env, R) :- !,
    place_constant(X, Loc, Env0, Env, R).
address_constant(val(_, cast(TypeName, XV)), Loc, Env0, Env, R) :- !,
    type_name(TypeName, Type, Env0, Loc),
    (   Type = ptr(_), lowered(XV, T), int_type(T), folded(XV, Env0, N), integer(N)
    ->  % 6.6p9: an integer constant cast to a pointer type is an address
        % constant, here an address with no capability, as in clang.
        Env = Env0, U is N mod (1 << 64), ( U =:= 0 -> R = null ; R = int(U) )
    ;   Type = ptr(_) -> address_constant(XV, Loc, Env0, Env, R)
    ;   % A pointer cast to a 64-bit integer, inside a cast back to a
        % pointer (the clause above), is the same address constant with
        % its capability, as filcc keeps it.
        int_type(Type), type_size_align(Type, Env0, 8, _),
        lowered(XV, ptr(_))
    ->  address_constant(XV, Loc, Env0, Env, R)
    ;   sema_error(Loc, 'initializer is not a constant', [])
    ).
address_constant(val(ptr(_), bin(Op, XA, XB)), Loc, Env0, Env, R) :-
    memberchk(Op, [add, sub]),
    lowered(XA, TA), lowered(XB, TB),
    (   TA = ptr(Elem) -> XP = XA, XK = XB
    ;   TB = ptr(Elem), XP = XB, XK = XA
    ),
    folded(XK, Env0, K), integer(K),
    !,
    address_constant(XP, Loc, Env0, Env, R0),
    offset_const(Op, R0, Elem, K, Env, Loc, R).
address_constant(XV, Loc, Env, Env, null) :-
    (   lowered(XV, T), int_type(T), folded(XV, Env, 0) -> true
    ;   sema_error(Loc, 'initializer is not an address constant', [])
    ).

% offset_const(+Op, +R0, +Elem, +K, +Env, +Loc, -R): R is address
% constant R0 plus (add) or minus (sub) K elements of type Elem.
offset_const(Op, sym(Sym, Off0), Elem, K, Env, Loc, sym(Sym, Off)) :- !,
    catch(arith_size(Elem, Env, Size), bad(Why),
          sema_error(Loc, 'pointer arithmetic on ~w (~w)', [Elem, Why])),
    (   Op == add -> Off is Off0 + K * Size
    ;   Off is Off0 - K * Size
    ).
offset_const(_, _, _, _, _, Loc, _) :-
    sema_error(Loc, 'initializer is not an address constant', []).

% place_constant(+X, +Loc, +Env0, -Env, -R): typed tree X designates a
% static object or a function at R = sym(Symbol, Offset).
place_constant(obj(_, id(Name)), Loc, Env, Env, sym(Sym, 0)) :- !,
    (   lookup_ordinary(Env, Name, gvar(_, Sym, Storage, _))
    ->  (   Storage = thread_local(_)                       % 6.6p9
        ->  sema_error(Loc, 'the address of thread-local ~w is not a constant', [Name])
        ;   true
        )
    ;   sema_error(Loc, '~w is not a global', [Name])
    ).
place_constant(fun(_, id(Name)), _, Env, Env, sym(Sym, 0)) :-
    lookup_ordinary(Env, Name, fn(_, Sym, _)), !.
place_constant(obj(_, str(Bytes)), _, Env0, Env, sym(Sym, 0)) :- !,
    new_literal(Bytes, Sym, Env0, Env).
place_constant(obj(_, wstr(WideType, Values)), _, Env0, Env, sym(Sym, 0)) :- !,
    new_literal(w(WideType, Values), Sym, Env0, Env).
place_constant(obj(_, complit(TypeName, Init)), Loc, Env0, Env, sym(Sym, 0)) :- !,
    type_name(TypeName, Type0, Env0, Loc),
    new_complit(Type0, Init, Loc, Sym, Env0, Env).
place_constant(obj(_, deref(XV)), Loc, Env0, Env, R) :- !,
    address_constant(XV, Loc, Env0, Env, R0),
    (   R0 = sym(_, _) -> R = R0
    ;   sema_error(Loc, 'initializer is not an address constant', [])
    ).
place_constant(obj(_, member(obj(T, F), Field)), Loc, Env0, Env, sym(Sym, Off)) :- !,
    place_constant(obj(T, F), Loc, Env0, Env, sym(Sym, Off0)),
    unqualified(T, SUType),
    member_off(SUType, Field, Env, Loc, _, MemberOff),
    Off is Off0 + MemberOff.
place_constant(_, Loc, _, _, _) :-
    sema_error(Loc, 'initializer is not an address constant', []).

% member_off(+SUType, +Field, +Env, +Loc, -Type, -Off): member Field of
% struct or union SUType has Type and offset Off.
member_off(SUType, Field, Env, Loc, Type, Off) :-
    (   ( SUType = struct(_) ; SUType = union(_) ),
        member_type_offset(SUType, Field, Env, Type, Off)
    ->  true
    ;   sema_error(Loc, 'no member named ~w', [Field])
    ).

% runtime_offset(+Path, +Type, +Env, +Ctx, +V0, -V)//: V is V0 plus the
% offset of offsetof's member Path in Type, its indexes evaluated.
runtime_offset([], _, _, _, V, V) --> [].
runtime_offset([field(F)|Path], T, Env, Ctx, V0, V) -->
    { ctx_loc(Ctx, Loc),
      (   member_type_offset(T, F, Env, FT, Off) -> true
      ;   sema_error(Loc, 'bad offsetof', [])
      ) },
    let(l, add, [V0, const(Off)], V1),
    runtime_offset(Path, FT, Env, Ctx, V1, V).
runtime_offset([index(X)|Path], T, Env, Ctx, V0, V) -->
    { ctx_loc(Ctx, Loc),
      (   T = array(ET, _), catch(type_size_align(ET, Env, Size, _), bad(_), fail) -> true
      ;   sema_error(Loc, 'bad offsetof', [])
      ) },
    rval(X, Ctx, XV),
    assign_convert(X, XV, long, Loc, v(I, _)),
    let(l, mul, [I, const(Size)], D),
    let(l, add, [V0, D], V1),
    runtime_offset(Path, ET, Env, Ctx, V1, V).


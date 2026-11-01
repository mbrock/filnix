/*  Pointer-as-integer laundering: an integer converted back to a
    pointer (`itop`) keeps the capability of the one pointer it was
    computed from, by launder_module/2. Fil-C's FilPizlonator does this
    with `inferPointerAsIntLaunderingForFunction`; this pass states the
    same abstract interpretation on nanofil's IR, before any
    optimization, so that the result does not depend on `-O`.

    ## The analysis

    Every `w` or `l` value has one of three abstract values:

    | Value | Means |
    |---|---|
    | `bot` | no capability source: a constant, a parameter, a load from memory, a call, a comparison |
    | `def(Id)` | computed from the one capability Id |
    | `top` | computed from two different capabilities |

    | Definition | Abstract value |
    |---|---|
    | `let(D, l, ptoi, [P])` | `def(P)`; `bot` when P is a constant plus offsets (`&((struct s *)0)->f`), whose conversion clang folds |
    | `let(D, K, Op, Args)`, Op arithmetic, bitwise, a shift, `copy`, `ext(_)` or `cast` | the merge of Args' values: `bot` is neutral, equal `def`s stay, anything else is `top` |
    | `phi(D, K, Ins)` | `def(phi(D))` when some incoming value is not `bot`, else `bot` |
    | anything else | `bot` |

    Fil-C runs its analysis on LLVM's SSA after clang's optimizer, so
    what it finds depends on the optimization level: at `-O0` an
    integer stored in a local variable comes back from a load, which is
    `bot`. This pass evaluates the rules on the SSA form that promote.pl
    gives the function (promote_func/3, whatever the level): a load of
    a promotable local is the value last stored to it, a phi where
    stores merge. Ids are SSA values too, so a pointer variable read
    twice is one source; so is a member or element read twice, its
    address computed twice from the same values, with no write between
    the reads in one block (block_loads/3, an optimizer's value
    numbering). The rules are Fil-C's; only the program they
    read is fixed. Clang's idiom recognition, which turns some selects
    into `llvm.umin` calls (`bot` to Fil-C), plays no part.

    A local the frontend declares `volatile` is memory, as it is to
    Fil-C: its reads are `bot` (volatile_allocs/2).

    A capability chosen this way is always one the program held: the
    rewrite never creates authority, and every access through the result
    is checked against that capability's bounds as any other.

    ## The rewrite

    The function is rewritten as it came from the frontend, and each
    capability the analysis names is computed where it is needed:

    | Instruction | Becomes |
    |---|---|
    | `let(D, p, itop, [X])`, X `def` | `I = ptoi C`, `Off = X - I`, `D = C + Off`, C the capability of X |
    | the same, X `bot` or `top` | unchanged: no capability |
    | an alloc with integer slots that ever hold a non-`bot` value | also a pointer slot, the slot's shadow, per such slot |
    | a store to such a slot | also a store of the value's capability (or null) to the shadow |
    | a `def` load of such a slot | also a load of the shadow |
    | a `def` phi whose capability is needed | also a `p` phi of its incoming values' capabilities (null for `bot` and `top`) |

    The shadow holds what Fil-C's capability phi would select: the
    capability of the value last stored, null for a `top` or `bot` one.
    Under `-O`, promote turns each shadow into exactly that phi.
    Functions without `itop`, and functions that are not in strict SSA
    form, are unchanged.
*/
:- module(launder, [launder_module/2, launder_func/4]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(cfg, [func_cfg/2, cfg_idoms/2]).
:- use_module(promote, [promote_func/3, promotable/4, strict_ssa/3]).
:- use_module(provenance, [remap_sites/3, emission_sites/7]).

%! launder_module(+Items0, -Items) is det.
%
%  Items are the module items Items0 (functions, their context/2 items
%  and data) with each function laundered by launder_func/4.
launder_module(Items0, Items) :-
    findall(Name-Rs, member(context(Name, Rs), Items0), CPairs0),
    sort(1, @<, CPairs0, CPairs),
    list_to_assoc(CPairs, Contexts0),
    foldl(launder_item, Items0, Items1, Contexts0, Contexts),
    maplist(relabel_context(Contexts), Items1, Items).

launder_item(F0, F, Cs0, Cs) :-
    F0 = func(Name, _, _, _, _), !,
    ( get_assoc(Name, Cs0, Rs0) -> true ; Rs0 = [] ),
    launder_func(F0, Rs0, F, Rs),
    ( Rs0 == Rs -> Cs = Cs0 ; put_assoc(Name, Cs0, Rs, Cs) ).
launder_item(Item, Item, Cs, Cs).

relabel_context(Cs, context(Name, _), context(Name, Rs)) :- !, get_assoc(Name, Cs, Rs).
relabel_context(_, Item, Item).

%! launder_func(+F0, +Records0, -F, -Records) is det.
%
%  F is the function F0 with each `itop` of an integer computed from one
%  capability given that capability (this module's header), and Records
%  is its context Records0 with instruction sites moved accordingly.
launder_func(F0, Rs0, F, Rs) :-
    F0 = func(Name, Linkage, Ret, Params, Blocks0),
    (   member(block(_, _, Is, _), Blocks0), memberchk(let(_, p, itop, _), Is), !,
        func_cfg(Blocks0, Cfg), cfg_idoms(Cfg, Idom),
        strict_ssa(F0, Cfg, Idom)
    ->  promote_func(filc, F0, FP),
        analysis(F0, Rs0, FP, An),
        demands(F0, An, St),
        rewrite_blocks(Blocks0, An, St, Blocks, Map),
        F = func(Name, Linkage, Ret, Params, Blocks),
        remap_sites(Rs0, Map, Rs)
    ;   F = F0, Rs = Rs0
    ).

%% The analysis

% analysis(+F0, +Records, +FP, -An): An is an(Copies, States, Defs, Addrs, Shadows):
% FP's copies T-V, the abstract values of FP's temps (bot left out), F0's
% definitions T-Inst, F0's address temps X-(A-Off) and the shadow temp
% of each tracked slot A-Off.
analysis(F0, Rs, FP, an(Copies, States, Defs, Addrs, Shadows)) :-
    F0 = func(_, _, _, _, Blocks0),
    promotable(filc, F0, Roots0, an(_, Addrs0, _)),
    ( Addrs0 == none -> empty_assoc(Addrs) ; Addrs = Addrs0 ),
    volatile_allocs(Rs, Volatile),
    exclude(volatile_root(Volatile), Roots0, Roots),
    findall(T-true, ( member(block(_, _, Is, _), Blocks0),
                      member(let(tmp(T), _, load(_), [tmp(X)]), Is),
                      get_assoc(X, Addrs, A-_), ord_memberchk(A, Volatile) ), VPs),
    list_to_assoc(VPs, VolatileLoads),
    FP = func(_, _, _, _, BlocksP),
    findall(T-V, ( member(block(_, _, Is, _), BlocksP),
                   member(let(tmp(T), _, copy, [V]), Is),
                   \+ get_assoc(T, VolatileLoads, _) ), CPs),
    list_to_assoc(CPs, Copies0),
    foldl(block_loads, BlocksP, Copies0, Copies),
    findall(Eq, ( member(block(_, Phis, Is, _), BlocksP),
                  ( member(I, Phis) ; member(I, Is) ),
                  equation(I, Copies, Eq), Eq = D-_,
                  \+ get_assoc(D, VolatileLoads, _) ), Eqs),
    empty_assoc(S0),
    fixpoint(Eqs, Copies, S0, States),
    findall(T-I, ( member(block(_, Phis, Is, _), Blocks0),
                   ( member(I, Phis) ; member(I, Is) ),
                   defines(I, T) ), DPs),
    list_to_assoc(DPs, Defs),
    findall(A-Off, ( member(block(_, _, Is, _), Blocks0),
                     member(store(W, V, tmp(X)), Is), W \== p,
                     get_assoc(X, Addrs, A-Off),
                     member(A-Slots, Roots), memberchk(acc(Off, W), Slots),
                     value_state(Copies, States, V, Av), Av \== bot ), Tracked0),
    sort(Tracked0, Tracked),
    used_names(F0, Used0),
    shadow_names(Tracked, Used0, 0, Shadows0),
    list_to_assoc(Shadows0, Shadows).

% volatile_allocs(+Records, -Allocs): Allocs is the ordset of the alloc
% temps of locals the frontend's context declares volatile. promote.pl
% makes such a local a value, but its reads are memory reads to Fil-C,
% so they are bot and the local has no shadow. The IR does not mark
% volatility; context only ever takes a capability away here.
volatile_allocs(Rs, Allocs) :-
    findall(A, ( member(binding(B, _, qualified(Qs, _), _), Rs),
                 memberchk(volatile, Qs),
                 member(value(A, named(B, address), _), Rs) ), As),
    sort(As, Allocs).

volatile_root(Volatile, A-_) :- ord_memberchk(A, Volatile).

% block_loads(+Block, +Copies0, -Copies): Copies is Copies0 with each
% pure computation of Block that repeats an earlier one on the same
% values, and each pointer load that repeats an earlier one from the
% same address with no write between them, a copy of the earlier: one
% value, as an optimizer's value numbering makes it (`s->p` read twice
% computes its address twice).
block_loads(block(_, _, Is, _), Copies0, Copies) :-
    empty_assoc(Seen),
    foldl(repeated_load, Is, Copies0-Seen, Copies-_).

repeated_load(let(tmp(T), p, load(p), [A]), Cs0-Seen0, Cs-Seen) :- !,
    root(Cs0, A, R),
    (   get_assoc(R, Seen0, T0)
    ->  put_assoc(T, Cs0, tmp(T0), Cs), Seen = Seen0
    ;   Cs = Cs0, put_assoc(R, Seen0, T, Seen)
    ).
repeated_load(let(tmp(T), K, Op, Args), Cs0-Seen0, Cs-Seen) :-
    pure_value_op(K, Op), !,
    maplist(root(Cs0), Args, Rs),
    Key = op(K, Op, Rs),
    (   get_assoc(Key, Seen0, T0)
    ->  put_assoc(T, Cs0, tmp(T0), Cs1), Seen = Seen0
    ;   Cs1 = Cs0, put_assoc(Key, Seen0, T, Seen)
    ),
    (   K == p, Args = [B|_]
    ->  put_assoc(base(T), Cs1, B, Cs)
    ;   Cs = Cs1
    ).
repeated_load(let(_, _, Op, _), State, State) :- \+ writes_memory(Op), !.
repeated_load(_, Cs-_, Cs-Seen) :- empty_assoc(Seen).

% pure_value_op(+K, +Op): a let of class K and Op computes its value
% from its arguments alone, so two with equal arguments are one value.
pure_value_op(p, Op) :- !, memberchk(Op, [add, sub]).
pure_value_op(K, Op) :- int_class(K), merge_op(Op), Op \== copy.

writes_memory(Op) :- \+ atom(Op), \+ Op = load(_), \+ Op = ext(_), \+ Op = cmp(_, _),
    \+ Op = alloc(_), !.
writes_memory(Op) :- memberchk(Op, [va_arg]).

defines(phi(tmp(T), _, _), T).
defines(let(tmp(T), _, _, _), T).

% equation(+Inst, +Copies, -Eq): FP's Inst defines an integer by one of
% the header's rules.
equation(let(tmp(D), l, ptoi, [P]), Copies, D-ptoi(Id)) :-
    root(Copies, P, Id), \+ constant_base(Copies, Id), !.
equation(let(tmp(D), l, ptoi, _), _, D-merge([])) :- !.
equation(phi(tmp(D), K, Ins), _, D-phi(Vs)) :- !,
    int_class(K), findall(V, member(_-V, Ins), Vs).
equation(let(tmp(D), K, Op, Args), _, D-merge(Args)) :-
    int_class(K), merge_op(Op).

int_class(w).
int_class(l).

merge_op(Op) :-
    memberchk(Op, [add, sub, mul, div, udiv, rem, urem, and, or, xor,
                   sar, shr, shl, neg, copy, cast]), !.
merge_op(ext(_)).

fixpoint(Eqs, Copies, S0, S) :-
    foldl(apply_equation(Copies), Eqs, S0-false, S1-Changed),
    ( Changed == true -> fixpoint(Eqs, Copies, S1, S) ; S = S1 ).

apply_equation(Copies, D-Rule, S0-C0, S-C) :-
    rule_value(Rule, D, Copies, S0, New),
    ( get_assoc(D, S0, Old) -> true ; Old = bot ),
    (   New == Old -> S = S0, C = C0
    ;   New == bot -> S = S0, C = C0
    ;   put_assoc(D, S0, New, S), C = true
    ).

rule_value(ptoi(Id), _, _, _, def(Id)).
rule_value(merge(Args), _, Copies, S, Av) :-
    foldl(merge_arg(Copies, S), Args, bot, Av).
rule_value(phi(Vs), D, Copies, S, Av) :-
    (   member(V, Vs), value_state(Copies, S, V, VAv), VAv \== bot
    ->  Av = def(phi(D))
    ;   Av = bot
    ).

merge_arg(Copies, S, V, Av0, Av) :-
    value_state(Copies, S, V, VAv),
    merge(Av0, VAv, Av).

%! merge(+A, +B, -C) is det.
merge(bot, X, X) :- !.
merge(X, bot, X) :- !.
merge(def(A), def(B), def(A)) :- A == B, !.
merge(_, _, top).

% constant_base(+Copies, +P): the pointer P is a constant plus offsets,
% as a hand-written offsetof, `&((struct s *)0)->f`, is: clang folds its
% conversion to an integer, so it is no capability source. Copies holds
% each p add or sub as base(T)-Base.
constant_base(_, const(_)) :- !.
constant_base(Copies, tmp(T)) :-
    get_assoc(base(T), Copies, B), root(Copies, B, R), constant_base(Copies, R).

root(Copies, tmp(T), R) :- get_assoc(T, Copies, V), !, root(Copies, V, R).
root(_, V, V).

% value_state(+Copies, +States, +V, -Av): the abstract value of V, an
% operand of F0 or FP.
value_state(Copies, S, V, Av) :-
    root(Copies, V, R),
    ( R = tmp(T), get_assoc(T, S, Av0) -> Av = Av0 ; Av = bot ).

an_state(an(Copies, S, _, _, _), V, Av) :- value_state(Copies, S, V, Av).

used_names(func(_, _, _, Params, Blocks), Used) :-
    findall(T, ( member(param(_, tmp(T)), Params)
               ; member(block(_, Phis, Is, _), Blocks),
                 ( member(I, Phis) ; member(I, Is) ), defines(I, T) ), Ts),
    sort(Ts, Used).

shadow_names([], _, _, []).
shadow_names([Slot|Slots], Used, N0, [Slot-T|Ps]) :-
    fresh_name(ld, Used, N0, T, N),
    shadow_names(Slots, Used, N, Ps).

% fresh_name(+Prefix, +Used, +N0, -T, -N): T is Prefix.N, the first such
% name after N0 that is not in Used, the function's own names. Shadows
% are ld.N and capabilities lc.N, each from its own counter, so a fresh
% name never needs adding to Used.
fresh_name(Prefix, Used, N0, T, N) :-
    N1 is N0 + 1,
    format(atom(T0), '~w.~w', [Prefix, N1]),
    (   ord_memberchk(T0, Used)
    ->  fresh_name(Prefix, Used, N1, T, N)
    ;   T = T0, N = N1
    ).

%% Which capabilities are needed

% demands(+F0, +An, -St): St is st(N, Used, Reals, Loads, Phis, Itops)
% once every capability needed by an itop or a store to a tracked slot
% has a value: Reals maps a temp to its capability operand, Loads a
% load to its shadow load's temp, Phis a phi to C-Ins, its capability
% phi, Itops an itop to the two temps of its offset.
demands(F0, An, St) :-
    F0 = func(_, _, _, _, Blocks),
    used_names(F0, Used),
    empty_assoc(E),
    St0 = st(0, Used, E, E, E, E),
    findall(I, ( member(block(_, _, Is, _), Blocks), member(I, Is) ), Insts),
    foldl(demand(An), Insts, St0, St).

demand(An, let(tmp(D), p, itop, [X]), St0, St) :-
    an_state(An, X, def(_)), !,
    real(An, X, R, St0, St1),
    (   R = const(_)
    ->  St = St1
    ;   fresh(I1, St1, St2), fresh(I2, St2, St3),
        St3 = st(N, U, Re, Lo, Ph, It0),
        put_assoc(D, It0, I1-I2, It),
        St = st(N, U, Re, Lo, Ph, It)
    ).
demand(An, store(W, V, tmp(X)), St0, St) :-
    W \== p, tracked_shadow(An, X, _),
    an_state(An, V, def(_)), !,
    real(An, V, _, St0, St).
demand(_, _, St, St).

tracked_shadow(an(_, _, _, Addrs, Shadows), X, Sh) :-
    get_assoc(X, Addrs, Slot), get_assoc(Slot, Shadows, Sh).

fresh(T, st(N0, U, Re, Lo, Ph, It), st(N, U, Re, Lo, Ph, It)) :-
    fresh_name(lc, U, N0, T, N).

% real(+An, +V, -R, +St0, -St): R is the capability operand of V, whose
% abstract value is def(_).
real(_, tmp(T), R, St, St) :-
    St = st(_, _, Re, _, _, _), get_assoc(T, Re, R), !.
real(An, tmp(T), R, St0, St) :-
    An = an(_, _, Defs, _, _),
    get_assoc(T, Defs, Inst),
    real_def(Inst, An, T, R, St0, St).

real_def(let(_, l, ptoi, [P]), _, T, P, St0, St) :- !, put_real(T, P, St0, St).
real_def(let(_, _, copy, [V]), An, T, R, St0, St) :- !,
    real(An, V, R, St0, St1), put_real(T, R, St1, St).
real_def(let(_, _, load(_), [tmp(X)]), An, T, R, St0, St) :- !,
    (   tracked_shadow(An, X, _)
    ->  fresh(C, St0, St1), R = tmp(C),
        St1 = st(N, U, Re, Lo0, Ph, It),
        put_assoc(T, Lo0, C, Lo),
        put_real(T, R, st(N, U, Re, Lo, Ph, It), St)
    ;   % A punned read of a narrower part of a slot.
        R = const(0), put_real(T, R, St0, St)
    ).
real_def(phi(_, _, Ins), An, T, tmp(C), St0, St) :- !,
    fresh(C, St0, St1),
    put_real(T, tmp(C), St1, St2),
    foldl(real_incoming(An), Ins, CapIns, St2, St3),
    St3 = st(N, U, Re, Lo, Ph0, It),
    put_assoc(T, Ph0, C-CapIns, Ph),
    St = st(N, U, Re, Lo, Ph, It).
real_def(let(_, _, _, Args), An, T, R, St0, St) :-
    an_state(An, tmp(T), def(Id)),
    member(A, Args), an_state(An, A, def(Id1)), Id1 == Id, !,
    real(An, A, R, St0, St1), put_real(T, R, St1, St).

real_incoming(An, P-V, P-R, St0, St) :-
    (   an_state(An, V, def(_))
    ->  real(An, V, R, St0, St)
    ;   R = const(0), St = St0
    ).

put_real(T, R, st(N, U, Re0, Lo, Ph, It), st(N, U, Re, Lo, Ph, It)) :-
    put_assoc(T, Re0, R, Re).

%% The rewrite

rewrite_blocks([], _, _, [], []).
rewrite_blocks([block(L, Phis0, Is0, J)|Bs0], An, St, [block(L, Phis, Is, J)|Bs], Map) :-
    St = st(_, _, _, _, CapPhis, _),
    findall(phi(tmp(C), p, CapIns),
            ( member(phi(tmp(T), _, _), Phis0), get_assoc(T, CapPhis, C-CapIns) ), New),
    append(Phis0, New, Phis),
    rewrite_insts(Is0, An, St, L, 0, 0, Is, Map, Map1),
    rewrite_blocks(Bs0, An, St, Bs, Map1).

rewrite_insts([], _, _, _, _, _, [], Map, Map).
rewrite_insts([I0|Is0], An, St, L, Old, New, Is, Map, Rest) :-
    rewrite_inst(I0, An, St, Out),
    emission_sites(L, Old, New, Out, Map, Map1, Next),
    append(Out, Is1, Is),
    Old1 is Old + 1,
    rewrite_insts(Is0, An, St, L, Old1, Next, Is1, Map1, Rest).

rewrite_inst(let(tmp(D), p, itop, [X]), _, St, Out) :-
    St = st(_, _, Re, _, _, It),
    get_assoc(D, It, I1-I2), !,
    get_assoc_value(X, Re, C),
    Out = [let(tmp(I1), l, ptoi, [C]),
           let(tmp(I2), l, sub, [X, tmp(I1)]),
           let(tmp(D), p, add, [C, tmp(I2)])].
rewrite_inst(I, An, _, [I|Shadows]) :-
    I = let(tmp(A), p, alloc(_), _),
    An = an(_, _, _, _, Shadows0),
    findall(let(tmp(Sh), p, alloc(8), [const(8)]),
            ( gen_assoc(A-_, Shadows0, Sh) ), Shadows),
    Shadows \== [], !.
rewrite_inst(I, An, St, [I, store(p, Cap, tmp(Sh))]) :-
    I = store(W, V, tmp(X)), W \== p,
    tracked_shadow(An, X, Sh), !,
    St = st(_, _, Re, _, _, _),
    (   an_state(An, V, def(_)), V = tmp(T), get_assoc(T, Re, Cap0)
    ->  Cap = Cap0
    ;   Cap = const(0)
    ).
rewrite_inst(I, An, St, [I, let(tmp(C), p, load(p), [tmp(Sh)])]) :-
    I = let(tmp(T), _, load(_), [tmp(X)]),
    St = st(_, _, _, Lo, _, _), get_assoc(T, Lo, C), !,
    tracked_shadow(An, X, Sh).
rewrite_inst(I, _, _, [I]).

get_assoc_value(tmp(T), Re, C) :- get_assoc(T, Re, C).

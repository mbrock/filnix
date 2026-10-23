/*  nanofil IR terms.

    module(Items)
      Items: func/5 and data/4 terms, in source order.

    func(Name, Linkage, Ret, Params, Blocks)
      Name     atom, the symbol without '$'
      Linkage  export | local
      Ret      w | l | p | void
      Params   [par(K, t(N))]            K in w, l, p
      Blocks   [blk(Label, Phis, Insts, Jump)], entry block first

    phi(t(D), K, [Pred-Value])
    Insts:
      ins(t(D), K, Op, Args)              value-producing instruction
      store(Width, Value, Addr)           Width in b, h, w, l, p
      call(Res, glo(F), [arg(K, Value)])  Res = to(t(D), K) | void
    Jump: jmp(L) | jnz(V, L1, L2) | ret(V) | ret | hlt

    Op: add sub mul div udiv rem urem and or xor sar shr shl neg copy
        cmp(Cond, K)   Cond in eq ne sle slt sge sgt ule ult uge ugt
        ext(T)         T in sw uw sh uh sb ub
        load(T)        T in l sw uw sh uh sb ub p
        alloc(Align)   Align in 4, 8, 16
        ptoi itop

    Values: t(Name) | c(Integer) | glo(Name)

    data(Name, Linkage, Align, Items)
      Items: [item(W, c(N)) | item(b, str(Chars)) | item(l, sym(Name, Off))
              | zero(N)]

    Temps are ground names; logic variables never appear in IR terms.

    A module is in one of two modes (module_mode/2):

      plain  QBE's integer IL. Addresses are l values. This is the mode
             compared against real qbe.
      filc   any use of class p. Addresses are p values (flight pointers
             with a capability), alloc yields p, loads and stores take a p
             address, p arithmetic is add/sub of an l offset, and ptoi/itop
             convert. Data definitions are not supported yet, and calls may
             name functions outside the module. See docs/m3.md.
*/
:- module(ir, [class_bits/2, modulus/2, half/2, op_arity/2, valid_module/1,
               func_named/3, width_bytes/2, op_arg_classes/4, module_mode/2,
               addr_class/2]).

:- use_module(library(lists)).
:- use_module(library(clpz)).

class_bits(w, 32).
class_bits(l, 64).

modulus(w, 4294967296).
modulus(l, 18446744073709551616).
modulus(p, 18446744073709551616).
half(w, 2147483648).
half(l, 9223372036854775808).

width_bytes(b, 1).
width_bytes(h, 2).
width_bytes(w, 4).
width_bytes(l, 8).
width_bytes(p, 8).

addr_class(plain, l).
addr_class(filc, p).

op_arity(add, 2).  op_arity(sub, 2).  op_arity(mul, 2).
op_arity(div, 2).  op_arity(udiv, 2). op_arity(rem, 2).  op_arity(urem, 2).
op_arity(and, 2).  op_arity(or, 2).   op_arity(xor, 2).
op_arity(sar, 2).  op_arity(shr, 2).  op_arity(shl, 2).
op_arity(neg, 1).  op_arity(copy, 1).
op_arity(cmp(_, _), 2).
op_arity(ext(_), 1).
op_arity(load(_), 1).
op_arity(alloc(_), 1).
op_arity(ptoi, 1).
op_arity(itop, 1).

func_named(module(Items), Name, F) :-
    F = func(Name, _, _, _, _),
    memberchk(F, Items).

/* module_mode(+M, -Mode): filc when anything in M has class p or uses a
   pointer-only op, plain otherwise. */
module_mode(module(Items), Mode) :-
    (   member(func(_, _, Ret, Params, Blocks), Items),
        (   Ret == p
        ;   member(par(p, _), Params)
        ;   member(blk(_, Phis, Insts, _), Blocks),
            (   member(phi(_, p, _), Phis)
            ;   member(I, Insts), pointer_inst(I)
            )
        )
    ->  Mode = filc
    ;   Mode = plain
    ).

pointer_inst(ins(_, p, _, _)).
pointer_inst(ins(_, _, ptoi, _)).
pointer_inst(store(p, _, _)).
pointer_inst(call(to(_, p), _, _)).
pointer_inst(call(_, _, Args)) :- memberchk(arg(p, _), Args).

/* valid_module(+M): M is a well-formed module. Throws
   nanofil_error(Message) describing the first problem found, so callers
   get a diagnostic rather than a silent failure. */
valid_module(M) :-
    M = module(Items),
    module_mode(M, Mode),
    maplist(valid_item(M, Mode), Items).

valid_item(M, Mode, func(Name, _, Ret, Params, Blocks)) :-
    (   Blocks == [] -> err(Name, 'function has no blocks', []) ; true ),
    findall(L, member(blk(L, _, _, _), Blocks), Labels),
    (   msort(Labels, S), sort(Labels, S) -> true
    ;   err(Name, 'duplicate block label', [])
    ),
    defs(Params, Blocks, Defs0),
    sort(Defs0, Defs),
    temp_classes(Name, Defs),
    Ctx = ctx(M, Name, Ret, Labels, Defs, Blocks, Mode),
    maplist(valid_block(Ctx), Blocks),
    Blocks = [blk(Entry, _, _, _)|_],
    (   member(blk(_, _, _, J), Blocks), jump_target(J, Entry)
    ->  err(Name, 'jump to the entry block @~w', [Entry])
    ;   true
    ).
valid_item(_, plain, data(_, _, _, _)).
valid_item(_, filc, data(Name, _, _, _)) :-
    format(atom(Msg), 'data $~w: data definitions are not supported with class p yet', [Name]),
    throw(nanofil_error(Msg)).

defs(Params, Blocks, Defs) :-
    findall(N-K, member(par(K, t(N)), Params), D0),
    findall(N-K,
            ( member(blk(_, Phis, Insts, _), Blocks),
              (   member(phi(t(N), K, _), Phis)
              ;   member(ins(t(N), K, _, _), Insts)
              ;   member(call(to(t(N), K), _, _), Insts)
              ) ),
            D1),
    append(D0, D1, Defs).

temp_classes(Fn, Defs) :-
    (   append(_, [N-K1, N-K2|_], Defs), K1 \== K2
    ->  err(Fn, 'temporary %~w has classes ~w and ~w', [N, K1, K2])
    ;   true
    ).

valid_block(Ctx, blk(L, Phis, Insts, Jump)) :-
    Ctx = ctx(_, Fn, _, _, _, Blocks, _),
    findall(P, ( member(blk(P, _, _, J), Blocks), jump_target(J, L) ), Preds0),
    sort(Preds0, Preds),
    maplist(valid_phi(Ctx, L, Preds), Phis),
    maplist(valid_inst(Ctx), Insts),
    valid_jump(Ctx, Jump),
    (   Phis \== [], Preds == [] -> err(Fn, 'phi in @~w, which has no predecessors', [L])
    ;   true
    ).

jump_target(jmp(L), L).
jump_target(jnz(_, L, _), L).
jump_target(jnz(_, _, L), L).

valid_phi(Ctx, L, Preds, phi(_, K, Pairs)) :-
    Ctx = ctx(_, Fn, _, _, _, _, _),
    pairs_keys_values_(Pairs, Ls, Vs),
    sort(Ls, SLs),
    (   SLs == Preds -> true
    ;   err(Fn, 'phi in @~w covers ~w but predecessors are ~w', [L, SLs, Preds])
    ),
    maplist(use(Ctx, K), Vs).

pairs_keys_values_([], [], []).
pairs_keys_values_([K-V|Ps], [K|Ks], [V|Vs]) :- pairs_keys_values_(Ps, Ks, Vs).

valid_inst(Ctx, ins(_, K, Op, Args)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   op_arity(Op, N), length(Args, N) -> true
    ;   err(Fn, 'bad instruction ~w with ~w', [Op, Args])
    ),
    (   op_result_ok(Mode, Op, K) -> true
    ;   err(Fn, 'instruction ~w cannot have class ~w', [Op, K])
    ),
    op_arg_classes(Op, K, Mode, AKs),
    maplist(use(Ctx), AKs, Args).
valid_inst(Ctx, store(W, V, A)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   W == p, Mode == plain -> err(Fn, 'storep needs class p', []) ; true ),
    store_value_class(W, VK),
    use(Ctx, VK, V),
    addr_class(Mode, AK),
    use(Ctx, AK, A).
valid_inst(Ctx, call(Res, glo(F), Args)) :-
    Ctx = ctx(M, Fn, _, _, _, _, Mode),
    findall(K, member(arg(K, _), Args), AKs),
    (   func_named(M, F, func(_, _, CRet, Params, _))
    ->  findall(K, member(par(K, _), Params), PKs),
        (   PKs == AKs -> true
        ;   err(Fn, 'call to $~w passes ~w, expects ~w', [F, AKs, PKs])
        ),
        call_result_ok(Fn, F, Res, CRet)
    ;   Mode == filc -> true
    ;   err(Fn, 'call to unknown function $~w', [F])
    ),
    forall(member(arg(K, V), Args), use(Ctx, K, V)).

store_value_class(l, l) :- !.
store_value_class(p, p) :- !.
store_value_class(_, w).

call_result_ok(_, _, void, _).
call_result_ok(Fn, F, to(_, K), Ret) :-
    (   Ret == void -> err(Fn, 'uses the result of void $~w', [F])
    ;   K == l, Ret == w -> err(Fn, 'reads the w result of $~w as l', [F])
    ;   ( K == p, Ret \== p ; K \== p, Ret == p ) -> err(Fn, 'reads the ~w result of $~w as ~w', [Ret, F, K])
    ;   true
    ).

valid_jump(Ctx, jmp(L)) :- label_exists(Ctx, L).
valid_jump(Ctx, jnz(V, L1, L2)) :-
    use(Ctx, w, V), label_exists(Ctx, L1), label_exists(Ctx, L2).
valid_jump(Ctx, ret(V)) :-
    Ctx = ctx(_, Fn, Ret, _, _, _, _),
    (   Ret == void -> err(Fn, 'ret with a value in a void function', []) ; true ),
    use(Ctx, Ret, V).
valid_jump(Ctx, ret) :-
    Ctx = ctx(_, Fn, Ret, _, _, _, _),
    (   Ret == void -> true ; err(Fn, 'ret without a value', []) ).
valid_jump(_, hlt).

label_exists(ctx(_, Fn, _, Labels, _, _, _), L) :-
    (   memberchk(L, Labels) -> true ; err(Fn, 'undefined label @~w', [L]) ).

use(Ctx, K, V) :- use_(V, Ctx, K).

% A p temporary is used only at p and vice versa; ptoi and itop are the
% conversions. An integer constant at p is a pointer with no capability.
use_(t(N), ctx(_, Fn, _, _, Defs, _, _), K) :-
    (   memberchk(N-K0, Defs)
    ->  (   K == l, K0 == w
        ->  err(Fn, '%~w has class w but is used as l', [N])
        ;   K0 == p, K \== p
        ->  err(Fn, '%~w has class p but is used as ~w (use ptoi)', [N, K])
        ;   K == p, K0 \== p
        ->  err(Fn, '%~w has class ~w but is used as p (use itop)', [N, K0])
        ;   true
        )
    ;   err(Fn, 'undefined temporary %~w', [N])
    ).
use_(c(N), _, _) :- integer(N).
use_(glo(G), ctx(M, Fn, _, _, _, _, Mode), K) :-
    addr_class(Mode, AK),
    (   K == AK -> true ; err(Fn, '$~w used as ~w', [G, K]) ),
    M = module(Items),
    (   memberchk(data(G, _, _, _), Items) -> true
    ;   err(Fn, '$~w is not a data definition', [G])
    ).

% Result classes each op allows.
op_result_ok(_, ext(T), K) :- !, ( memberchk(T, [sw, uw]) -> K == l ; int_class(K) ).
op_result_ok(_, load(l), K) :- !, K == l.
op_result_ok(Mode, load(p), K) :- !, Mode == filc, K == p.
op_result_ok(_, load(_), K) :- !, int_class(K).
op_result_ok(Mode, alloc(_), K) :- !, addr_class(Mode, K).
op_result_ok(Mode, ptoi, K) :- !, Mode == filc, K == l.
op_result_ok(Mode, itop, K) :- !, Mode == filc, K == p.
op_result_ok(_, Op, p) :- !, memberchk(Op, [add, sub, copy]).
op_result_ok(_, _, K) :- int_class(K).

int_class(w).
int_class(l).

% Classes at which each argument is read.
op_arg_classes(cmp(_, CK), _, _, [CK, CK]) :- !.
op_arg_classes(ext(_), _, _, [w]) :- !.
op_arg_classes(load(_), _, Mode, [A]) :- !, addr_class(Mode, A).
op_arg_classes(alloc(_), _, _, [l]) :- !.
op_arg_classes(ptoi, _, _, [p]) :- !.
op_arg_classes(itop, _, _, [l]) :- !.
op_arg_classes(Op, p, _, [p, l]) :- memberchk(Op, [add, sub]), !.
op_arg_classes(Op, K, _, [K, w]) :- memberchk(Op, [sar, shr, shl]), !.
op_arg_classes(Op, K, _, Ks) :- op_arity(Op, N), length(Ks, N), maplist(=(K), Ks).

err(Fn, Fmt, Args) :-
    format(atom(Msg), Fmt, Args),
    format(atom(Full), 'in $~w: ~w', [Fn, Msg]),
    throw(nanofil_error(Full)).

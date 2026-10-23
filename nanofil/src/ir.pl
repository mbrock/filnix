/*  nanofil IR terms (phase one: QBE's integer subset).

    module(Items)
      Items: func/5 and data/4 terms, in source order.

    func(Name, Linkage, Ret, Params, Blocks)
      Name     atom, the symbol without '$'
      Linkage  export | local
      Ret      w | l | void
      Params   [par(K, t(N))]            K in w, l
      Blocks   [blk(Label, Phis, Insts, Jump)], entry block first

    phi(t(D), K, [Pred-Value])
    Insts:
      ins(t(D), K, Op, Args)              value-producing instruction
      store(Width, Value, Addr)           Width in b, h, w, l
      call(Res, glo(F), [arg(K, Value)])  Res = to(t(D), K) | void
    Jump: jmp(L) | jnz(V, L1, L2) | ret(V) | ret | hlt

    Op: add sub mul div udiv rem urem and or xor sar shr shl neg copy
        cmp(Cond, K)   Cond in eq ne sle slt sge sgt ule ult uge ugt
        ext(T)         T in sw uw sh uh sb ub
        load(T)        T in l sw uw sh uh sb ub
        alloc(Align)   Align in 4, 8, 16

    Values: t(Name) | c(Integer) | glo(Name)

    data(Name, Linkage, Align, Items)
      Items: [item(W, c(N)) | item(b, str(Chars)) | item(l, sym(Name, Off))
              | zero(N)]

    Temps are ground names; logic variables never appear in IR terms.
    A value is an integer in 0..2^bits(K)-1 for its class K.
*/
:- module(ir, [class_bits/2, modulus/2, half/2, op_arity/2, valid_module/1,
               func_named/3, width_bytes/2, op_arg_classes/3]).

:- use_module(library(lists)).
:- use_module(library(clpz)).

class_bits(w, 32).
class_bits(l, 64).

% Moduli are facts on purpose: Trealla (12f4cbd and ba473a6) corrupts a
% clause whose body has a CLP(Z) goal over a ground integer >= 2^63, e.g.
% `Z #= X mod 18446744073709551616`. Binding the constant at run time works.
modulus(w, 4294967296).
modulus(l, 18446744073709551616).
half(w, 2147483648).
half(l, 9223372036854775808).

width_bytes(b, 1).
width_bytes(h, 2).
width_bytes(w, 4).
width_bytes(l, 8).

op_arity(add, 2).  op_arity(sub, 2).  op_arity(mul, 2).
op_arity(div, 2).  op_arity(udiv, 2). op_arity(rem, 2).  op_arity(urem, 2).
op_arity(and, 2).  op_arity(or, 2).   op_arity(xor, 2).
op_arity(sar, 2).  op_arity(shr, 2).  op_arity(shl, 2).
op_arity(neg, 1).  op_arity(copy, 1).
op_arity(cmp(_, _), 2).
op_arity(ext(_), 1).
op_arity(load(_), 1).
op_arity(alloc(_), 1).

func_named(module(Items), Name, F) :-
    F = func(Name, _, _, _, _),
    memberchk(F, Items).

/* valid_module(+M): M is a well-formed phase-one module. Throws
   nanofil_error(Message) describing the first problem found, so callers
   get a diagnostic rather than a silent failure. */
valid_module(M) :-
    M = module(Items),
    maplist(valid_item(M), Items).

valid_item(M, func(Name, _, Ret, Params, Blocks)) :-
    (   Blocks == [] -> err(Name, 'function has no blocks', []) ; true ),
    findall(L, member(blk(L, _, _, _), Blocks), Labels),
    (   msort(Labels, S), sort(Labels, S) -> true
    ;   err(Name, 'duplicate block label', [])
    ),
    defs(Params, Blocks, Defs0),
    sort(Defs0, Defs),
    temp_classes(Name, Defs),
    Ctx = ctx(M, Name, Ret, Labels, Defs, Blocks),
    maplist(valid_block(Ctx), Blocks),
    Blocks = [blk(Entry, _, _, _)|_],
    (   member(blk(_, _, _, J), Blocks), jump_target(J, Entry)
    ->  err(Name, 'jump to the entry block @~w', [Entry])
    ;   true
    ).
valid_item(_, data(_, _, _, _)).

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
    Ctx = ctx(_, Fn, _, _, _, Blocks),
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
    Ctx = ctx(_, Fn, _, _, _, _),
    pairs_keys_values_(Pairs, Ls, Vs),
    sort(Ls, SLs),
    (   SLs == Preds -> true
    ;   err(Fn, 'phi in @~w covers ~w but predecessors are ~w', [L, SLs, Preds])
    ),
    maplist(use(Ctx, K), Vs).

pairs_keys_values_([], [], []).
pairs_keys_values_([K-V|Ps], [K|Ks], [V|Vs]) :- pairs_keys_values_(Ps, Ks, Vs).

valid_inst(Ctx, ins(_, K, Op, Args)) :-
    Ctx = ctx(_, Fn, _, _, _, _),
    (   op_arity(Op, N), length(Args, N) -> true
    ;   err(Fn, 'bad instruction ~w with ~w', [Op, Args])
    ),
    (   op_result_ok(Op, K) -> true
    ;   err(Fn, 'instruction ~w cannot have class ~w', [Op, K])
    ),
    op_arg_classes(Op, K, AKs),
    maplist(use(Ctx), AKs, Args).
valid_inst(Ctx, store(W, V, A)) :-
    (   W == l -> VK = l ; VK = w ),
    use(Ctx, VK, V),
    use(Ctx, l, A).
valid_inst(Ctx, call(Res, glo(F), Args)) :-
    Ctx = ctx(M, Fn, _, _, _, _),
    (   func_named(M, F, func(_, _, _, Params, _))
    ->  findall(K, member(par(K, _), Params), PKs),
        findall(K, member(arg(K, _), Args), AKs),
        (   PKs == AKs -> true
        ;   err(Fn, 'call to $~w passes ~w, expects ~w', [F, AKs, PKs])
        )
    ;   err(Fn, 'call to unknown function $~w', [F])
    ),
    func_named(M, F, func(_, _, CRet, _, _)),
    call_result_ok(Fn, F, Res, CRet),
    forall(member(arg(K, V), Args), use(Ctx, K, V)).

call_result_ok(_, _, void, _).
call_result_ok(Fn, F, to(_, K), Ret) :-
    (   Ret == void -> err(Fn, 'uses the result of void $~w', [F])
    ;   K == l, Ret == w -> err(Fn, 'reads the w result of $~w as l', [F])
    ;   true
    ).

valid_jump(Ctx, jmp(L)) :- label_exists(Ctx, L).
valid_jump(Ctx, jnz(V, L1, L2)) :-
    use(Ctx, w, V), label_exists(Ctx, L1), label_exists(Ctx, L2).
valid_jump(Ctx, ret(V)) :-
    Ctx = ctx(_, Fn, Ret, _, _, _),
    (   Ret == void -> err(Fn, 'ret with a value in a void function', []) ; true ),
    use(Ctx, Ret, V).
valid_jump(Ctx, ret) :-
    Ctx = ctx(_, Fn, Ret, _, _, _),
    (   Ret == void -> true ; err(Fn, 'ret without a value', []) ).
valid_jump(_, hlt).

label_exists(ctx(_, Fn, _, Labels, _, _), L) :-
    (   memberchk(L, Labels) -> true ; err(Fn, 'undefined label @~w', [L]) ).

use(Ctx, K, V) :- use_(V, Ctx, K).

use_(t(N), ctx(_, Fn, _, _, Defs, _), K) :-
    (   memberchk(N-K0, Defs)
    ->  (   K == l, K0 == w
        ->  err(Fn, '%~w has class w but is used as l', [N])
        ;   true
        )
    ;   err(Fn, 'undefined temporary %~w', [N])
    ).
use_(c(N), _, _) :- integer(N).
use_(glo(G), ctx(M, Fn, _, _, _, _), K) :-
    (   K == l -> true ; err(Fn, '$~w used as ~w', [G, K]) ),
    M = module(Items),
    (   memberchk(data(G, _, _, _), Items) -> true
    ;   err(Fn, '$~w is not a data definition', [G])
    ).

% Result classes each op allows.
op_result_ok(ext(sw), l) :- !.
op_result_ok(ext(uw), l) :- !.
op_result_ok(ext(sw), _) :- !, fail.
op_result_ok(ext(uw), _) :- !, fail.
op_result_ok(load(l), l) :- !.
op_result_ok(load(l), _) :- !, fail.
op_result_ok(alloc(_), l) :- !.
op_result_ok(alloc(_), _) :- !, fail.
op_result_ok(_, K) :- class_bits(K, _).

% Classes at which each argument is read.
op_arg_classes(cmp(_, CK), _, [CK, CK]) :- !.
op_arg_classes(ext(_), _, [w]) :- !.
op_arg_classes(load(_), _, [l]) :- !.
op_arg_classes(alloc(_), _, [l]) :- !.
op_arg_classes(Op, K, [K, w]) :- memberchk(Op, [sar, shr, shl]), !.
op_arg_classes(Op, K, Ks) :- op_arity(Op, N), length(Ks, N), maplist(=(K), Ks).

err(Fn, Fmt, Args) :-
    format(atom(Msg), Fmt, Args),
    format(atom(Full), 'in $~w: ~w', [Fn, Msg]),
    throw(nanofil_error(Full)).

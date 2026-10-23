/*  nanofil IR terms.

    module(Items)
      Items: func/5 and data/4 terms, in source order.

    func(Name, Linkage, Ret, Params, Blocks)
      Name     atom, the symbol without '$'
      Linkage  export | local
      Ret      w | l | p | void | tuple([K1, K2])
               tuple: a two-word return (a struct of 9 to 16 bytes),
               each Ki in l, p; filc only
      Params   [par(K, t(N))]            K in w, l, p
      Blocks   [blk(Label, Phis, Insts, Jump)], entry block first

    phi(t(D), K, [Pred-Value])
    Insts:
      ins(t(D), K, Op, Args)              value-producing instruction
      store(Width, Value, Addr)           Width in b, h, w, l, p
      call(Res, Callee, [arg(K, Value)])  Res = to(t(D), K) | void
                                          | tuple([to(t(D1), K1), to(t(D2), K2)]);
                                          Callee glo(F), or (filc) a p temp
    Jump: jmp(L) | jnz(V, L1, L2) | ret(V) | rets([V1, V2]) | ret | hlt
          rets returns a tuple

    Op: add sub mul div udiv rem urem and or xor sar shr shl neg copy
        cmp(Cond, K)   Cond in eq ne sle slt sge sgt ule ult uge ugt
        ext(T)         T in sw uw sh uh sb ub
        load(T)        T in l sw uw sh uh sb ub p
        alloc(Align)   Align in 4, 8, 16
        ptoi itop

    Values: t(Name) | c(Integer) | glo(Name)

    data(Name, Linkage, Align, Items)
      Linkage  export | local | ro(export) | ro(local), ro for read-only
               data (QBE text: section ".rodata")
      Items: [item(W, c(N)) | item(b, str(Chars)) | item(l, sym(Name, Off))
              | item(p, sym(Name, Off)) | zero(N)]
      item(p, ...) is a pointer with the capability of Name (filc only).

    Temps are ground names; logic variables never appear in IR terms.

    A module is in one of two modes (module_mode/2):

      plain  QBE's integer IL. Addresses are l values. This is the mode
             compared against real qbe.
      filc   any use of class p. Addresses are p values (flight pointers
             with a capability), alloc yields p, loads and stores take a p
             address, p arithmetic is add/sub of an l offset, and ptoi/itop
             convert. Calls may name functions outside the module, or go
             through a p value. A symbol is used only as %t =p copy $s,
             which yields a pointer to the data or function object; $s
             may be defined outside the module. See docs/m3.md, m4.md.
*/
:- module(ir, [class_bits/2, modulus/2, half_modulus/2, op_arity/2, valid_module/1,
               func_named/3, width_bytes/2, op_arg_classes/4, module_mode/2,
               addr_class/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).

class_bits(w, 32).
class_bits(l, 64).

modulus(w, 4294967296).
modulus(l, 18446744073709551616).
modulus(p, 18446744073709551616).
half_modulus(w, 2147483648).
half_modulus(l, 9223372036854775808).

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

func_named(module(Items), Name, Func) :-
    Func = func(Name, _, _, _, _),
    memberchk(Func, Items).

%% Module mode

/* module_mode(+M, -Mode): filc when anything in M has class p, uses a
   pointer-only op, or calls a function M does not define (which only the
   Fil-C ABI can reach); plain otherwise. */
module_mode(module(Items), Mode) :-
    (   member(Item, Items),
        pointer_item(Item)
    ->  Mode = filc
    ;   member(func(_, _, _, _, Blocks), Items),
        member(blk(_, _, Insts, _), Blocks),
        member(call(_, glo(Callee), _), Insts),
        \+ memberchk(func(Callee, _, _, _, _), Items)
    ->  Mode = filc
    ;   Mode = plain
    ).

pointer_item(func(_, _, Ret, Params, Blocks)) :-
    (   ( Ret == p ; Ret = tuple(_) )
    ;   member(par(p, _), Params)
    ;   member(blk(_, Phis, Insts, _), Blocks),
        (   member(phi(_, p, _), Phis)
        ;   member(Inst, Insts),
            pointer_inst(Inst)
        )
    ), !.
pointer_item(data(_, Linkage, _, Items)) :-
    (   Linkage = ro(_)
    ;   memberchk(item(p, _), Items)
    ), !.

pointer_inst(ins(_, p, _, _)).
pointer_inst(ins(_, _, ptoi, _)).
pointer_inst(store(p, _, _)).
pointer_inst(call(to(_, p), _, _)).
pointer_inst(call(tuple(_), _, _)).
pointer_inst(call(_, _, Args)) :- memberchk(arg(p, _), Args).
pointer_inst(call(_, t(_), _)).

%% Validation

/* valid_module(+M): M is a well-formed module. Throws
   nanofil_error(Message) describing the first problem found, so callers
   get a diagnostic rather than a silent failure.

   Functions are checked against a context
     ctx(Module, Fn, Ret, LabelSet, TempClasses, PredMap, Mode)
   whose three assocs map each label to t, each temporary to its class,
   and each label to its sorted predecessors. */
valid_module(M) :-
    M = module(Items),
    module_mode(M, Mode),
    maplist(valid_item(M, Mode), Items).

valid_item(M, Mode, func(Name, _, Ret, Params, Blocks)) :-
    (   Blocks == [] -> fn_error(Name, 'function has no blocks', []) ; true ),
    (   Ret = tuple(Ks),
        \+ ( Ks = [_, _], forall(member(K, Ks), memberchk(K, [l, p])) )
    ->  fn_error(Name,
                 'a tuple return is two words of class l or p, not ~w', [Ks])
    ;   true
    ),
    findall(Label, member(blk(Label, _, _, _), Blocks), Labels),
    (   msort(Labels, Sorted), sort(Labels, Sorted) -> true
    ;   fn_error(Name, 'duplicate block label', [])
    ),
    temp_defs(Params, Blocks, Defs0),
    sort(Defs0, Defs),
    check_temp_classes(Name, Defs),
    % Labels, definitions and predecessors are indexed once, so checking
    % a function stays near linear in its size.
    findall(Label-t, member(Label, Labels), LabelPairs),
    list_to_assoc(LabelPairs, LabelSet),
    list_to_assoc(Defs, TempClasses),
    predecessors(Blocks, PredMap),
    Ctx = ctx(M, Name, Ret, LabelSet, TempClasses, PredMap, Mode),
    maplist(valid_block(Ctx), Blocks),
    Blocks = [blk(Entry, _, _, _)|_],
    (   member(blk(_, _, _, Jump), Blocks),
        jump_target(Jump, Entry)
    ->  fn_error(Name, 'jump to the entry block @~w', [Entry])
    ;   true
    ).
valid_item(_, Mode, data(Name, _, Align, Items)) :-
    (   memberchk(Align, [1, 2, 4, 8, 16]) -> true
    ;   fn_error(Name, 'unsupported data alignment ~w', [Align])
    ),
    (   Mode == plain, memberchk(item(p, _), Items)
    ->  fn_error(Name, 'pointer data items need a Fil-C module', [])
    ;   Mode == filc, memberchk(item(l, sym(Sym, _)), Items)
    ->  fn_error(Name, 'use p $~w for a pointer in a Fil-C module', [Sym])
    ;   true
    ).

% temp_defs(+Params, +Blocks, -Defs): Name-Class for every definition of
% a temporary, in parameter and then block order.
temp_defs(Params, Blocks, Defs) :-
    findall(N-K, member(par(K, t(N)), Params), ParamDefs),
    findall(N-K,
            ( member(blk(_, Phis, Insts, _), Blocks),
              (   member(phi(t(N), K, _), Phis)
              ;   member(ins(t(N), K, _, _), Insts)
              ;   member(call(to(t(N), K), _, _), Insts)
              ;   member(call(tuple(Tos), _, _), Insts),
                  member(to(t(N), K), Tos)
              ) ),
            BlockDefs),
    append(ParamDefs, BlockDefs, Defs).

% Defs is sorted, so two classes for one temporary are adjacent.
check_temp_classes(Fn, Defs) :-
    (   append(_, [N-K1, N-K2|_], Defs), K1 \== K2
    ->  fn_error(Fn, 'temporary %~w has classes ~w and ~w', [N, K1, K2])
    ;   true
    ).

% predecessors(+Blocks, -PredMap): each label's sorted predecessors.
predecessors(Blocks, PredMap) :-
    findall(Target-Pred,
            ( member(blk(Pred, _, _, Jump), Blocks),
              jump_target(Jump, Target)
            ),
            Edges0),
    sort(Edges0, Edges),
    empty_assoc(PredMap0),
    foldl(add_predecessor, Edges, PredMap0, PredMap).

add_predecessor(Target-Pred, PredMap0, PredMap) :-
    (   get_assoc(Target, PredMap0, Preds0) -> true ; Preds0 = [] ),
    append(Preds0, [Pred], Preds),
    put_assoc(Target, PredMap0, Preds, PredMap).

valid_block(Ctx, blk(Label, Phis, Insts, Jump)) :-
    Ctx = ctx(_, Fn, _, _, _, PredMap, _),
    (   get_assoc(Label, PredMap, Preds) -> true ; Preds = [] ),
    maplist(valid_phi(Ctx, Label, Preds), Phis),
    maplist(valid_inst(Ctx), Insts),
    valid_jump(Ctx, Jump),
    (   Phis \== [], Preds == []
    ->  fn_error(Fn, 'phi in @~w, which has no predecessors', [Label])
    ;   true
    ).

jump_target(jmp(L), L).
jump_target(jnz(_, L, _), L).
jump_target(jnz(_, _, L), L).

valid_phi(Ctx, Label, Preds, phi(_, K, Pairs)) :-
    Ctx = ctx(_, Fn, _, _, _, _, _),
    split_pairs(Pairs, PhiPreds0, Values),
    sort(PhiPreds0, PhiPreds),
    (   PhiPreds == Preds -> true
    ;   fn_error(Fn, 'phi in @~w covers ~w but predecessors are ~w',
                 [Label, PhiPreds, Preds])
    ),
    maplist(valid_use(Ctx, K), Values).

% pairs_keys_values/3, without depending on library(pairs).
split_pairs([], [], []).
split_pairs([K-V|Ps], [K|Ks], [V|Vs]) :- split_pairs(Ps, Ks, Vs).

valid_inst(ctx(_, _, _, _, _, _, filc), ins(_, p, copy, [glo(_)])) :- !.
valid_inst(Ctx, ins(_, K, Op, Args)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   op_arity(Op, N), length(Args, N) -> true
    ;   fn_error(Fn, 'bad instruction ~w with ~w', [Op, Args])
    ),
    (   op_result_ok(Mode, Op, K) -> true
    ;   fn_error(Fn, 'instruction ~w cannot have class ~w', [Op, K])
    ),
    op_arg_classes(Op, K, Mode, ArgClasses),
    maplist(valid_use(Ctx), ArgClasses, Args).
valid_inst(Ctx, store(Width, Value, Addr)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   Width == p, Mode == plain
    ->  fn_error(Fn, 'storep needs class p', [])
    ;   true
    ),
    store_value_class(Width, ValueClass),
    valid_use(Ctx, ValueClass, Value),
    addr_class(Mode, AddrClass),
    valid_use(Ctx, AddrClass, Addr).
valid_inst(Ctx, call(Res, glo(Callee), Args)) :-
    Ctx = ctx(M, Fn, _, _, _, _, Mode),
    findall(K, member(arg(K, _), Args), ArgClasses),
    (   func_named(M, Callee, func(_, _, CalleeRet, Params, _))
    ->  findall(K, member(par(K, _), Params), ParamClasses),
        (   ParamClasses == ArgClasses -> true
        ;   fn_error(Fn, 'call to $~w passes ~w, expects ~w',
                     [Callee, ArgClasses, ParamClasses])
        ),
        call_result_ok(Fn, Callee, Res, CalleeRet)
    ;   Mode == filc -> true
    ;   fn_error(Fn, 'call to unknown function $~w', [Callee])
    ),
    forall(member(arg(K, V), Args), valid_use(Ctx, K, V)).
valid_inst(Ctx, call(_, Callee, Args)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   Mode == filc, Callee = t(_) -> valid_use(Ctx, p, Callee)
    ;   fn_error(Fn, 'bad callee ~w', [Callee])
    ),
    forall(member(arg(K, V), Args), valid_use(Ctx, K, V)).

store_value_class(l, l) :- !.
store_value_class(p, p) :- !.
store_value_class(_, w).

% call_result_ok(+Fn, +Callee, +Res, +CalleeRet): the call site reads the
% result the way the callee returns it.
call_result_ok(_, _, void, _).
call_result_ok(Fn, Callee, tuple(Tos), Ret) :- !,
    findall(K, member(to(_, K), Tos), Ks),
    (   Ret == tuple(Ks) -> true
    ;   fn_error(Fn, 'reads the ~w result of $~w as tuple(~w)',
                 [Ret, Callee, Ks])
    ).
call_result_ok(Fn, Callee, to(_, K), Ret) :-
    (   Ret == void
    ->  fn_error(Fn, 'uses the result of void $~w', [Callee])
    ;   Ret = tuple(_)
    ->  fn_error(Fn, 'reads the tuple result of $~w as ~w', [Callee, K])
    ;   K == l, Ret == w
    ->  fn_error(Fn, 'reads the w result of $~w as l', [Callee])
    ;   ( K == p, Ret \== p ; K \== p, Ret == p )
    ->  fn_error(Fn, 'reads the ~w result of $~w as ~w', [Ret, Callee, K])
    ;   true
    ).

valid_jump(Ctx, jmp(L)) :- label_exists(Ctx, L).
valid_jump(Ctx, jnz(V, L1, L2)) :-
    valid_use(Ctx, w, V),
    label_exists(Ctx, L1),
    label_exists(Ctx, L2).
valid_jump(Ctx, ret(V)) :-
    Ctx = ctx(_, Fn, Ret, _, _, _, _),
    (   Ret == void
    ->  fn_error(Fn, 'ret with a value in a void function', [])
    ;   Ret = tuple(_)
    ->  fn_error(Fn, 'ret of one value in a tuple function', [])
    ;   true
    ),
    valid_use(Ctx, Ret, V).
valid_jump(Ctx, rets(Vs)) :-
    Ctx = ctx(_, Fn, Ret, _, _, _, _),
    (   Ret = tuple(Ks), length(Ks, N), length(Vs, N)
    ->  maplist(valid_use(Ctx), Ks, Vs)
    ;   fn_error(Fn, 'ret of a tuple in a ~w function', [Ret])
    ).
valid_jump(Ctx, ret) :-
    Ctx = ctx(_, Fn, Ret, _, _, _, _),
    (   Ret == void -> true ; fn_error(Fn, 'ret without a value', []) ).
valid_jump(_, hlt).

label_exists(ctx(_, Fn, _, LabelSet, _, _, _), L) :-
    (   get_assoc(L, LabelSet, _) -> true
    ;   fn_error(Fn, 'undefined label @~w', [L])
    ).

% valid_use(+Ctx, +K, +V): V may be read at class K. Arguments are in the
% order maplist needs; valid_use_/3 indexes on the value.
valid_use(Ctx, K, V) :- valid_use_(V, Ctx, K).

% A p temporary is used only at p and vice versa; ptoi and itop are the
% conversions. An integer constant at p is a pointer with no capability.
valid_use_(t(N), ctx(_, Fn, _, _, TempClasses, _, _), K) :-
    (   get_assoc(N, TempClasses, K0)
    ->  (   K == l, K0 == w
        ->  fn_error(Fn, '%~w has class w but is used as l', [N])
        ;   K0 == p, K \== p
        ->  fn_error(Fn, '%~w has class p but is used as ~w (use ptoi)',
                     [N, K])
        ;   K == p, K0 \== p
        ->  fn_error(Fn, '%~w has class ~w but is used as p (use itop)',
                     [N, K0])
        ;   true
        )
    ;   fn_error(Fn, 'undefined temporary %~w', [N])
    ).
valid_use_(c(N), _, _) :- integer(N).
valid_use_(glo(G), ctx(_, Fn, _, _, _, _, filc), _) :- !,
    fn_error(Fn, '$~w used as an operand; use %t =p copy $~w', [G, G]).
valid_use_(glo(G), ctx(M, Fn, _, _, _, _, Mode), K) :-
    addr_class(Mode, AddrClass),
    (   K == AddrClass -> true
    ;   fn_error(Fn, '$~w used as ~w', [G, K])
    ),
    M = module(Items),
    (   memberchk(data(G, _, _, _), Items) -> true
    ;   fn_error(Fn, '$~w is not a data definition', [G])
    ).

%% Operand and result classes

% op_result_ok(+Mode, +Op, +K): Op may produce a result of class K.
op_result_ok(_, ext(T), K) :- !,
    (   memberchk(T, [sw, uw]) -> K == l ; int_class(K) ).
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

% op_arg_classes(+Op, +K, +Mode, -Classes): the class at which each
% argument of Op with result class K is read.
op_arg_classes(cmp(_, CK), _, _, [CK, CK]) :- !.
op_arg_classes(ext(_), _, _, [w]) :- !.
op_arg_classes(load(_), _, Mode, [A]) :- !, addr_class(Mode, A).
op_arg_classes(alloc(_), _, _, [l]) :- !.
op_arg_classes(ptoi, _, _, [p]) :- !.
op_arg_classes(itop, _, _, [l]) :- !.
op_arg_classes(Op, p, _, [p, l]) :- memberchk(Op, [add, sub]), !.
op_arg_classes(Op, K, _, [K, w]) :- memberchk(Op, [sar, shr, shl]), !.
op_arg_classes(Op, K, _, Ks) :-
    op_arity(Op, N),
    length(Ks, N),
    maplist(=(K), Ks).

fn_error(Fn, Fmt, Args) :-
    format(atom(Msg), Fmt, Args),
    format(atom(Full), 'in $~w: ~w', [Fn, Msg]),
    throw(nanofil_error(Full)).

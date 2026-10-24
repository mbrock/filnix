/*  nanofil IR terms.

    module(Items)
      Items: func/5 and data/4 terms, in source order.

    func(Name, Linkage, Ret, Params, Blocks)
      Name     atom, the symbol without '$'
      Linkage  export | local
      Ret      w | l | p | s | d | void | tuple([K1, K2])
               tuple: a two-word return (a struct of 9 to 16 bytes),
               each Ki in l, p; filc only
      Params   [par(K, t(N))]            K in w, l, p, s, d
      Blocks   [blk(Label, Phis, Insts, Jump)], entry block first

    phi(t(D), K, [Pred-Value])
    Insts:
      ins(t(D), K, Op, Args)              value-producing instruction
      store(Width, Value, Addr)           Width in b, h, w, l, p, s, d
      call(Res, Callee, [arg(K, Value)])  Res = to(t(D), K) | void
                                          | tuple([to(t(D1), K1), to(t(D2), K2)]);
                                          Callee glo(F), or (filc) a p temp
    Jump: jmp(L) | jnz(V, L1, L2) | ret(V) | rets([V1, V2]) | ret | hlt
          rets returns a tuple

    Op: add sub mul div udiv rem urem and or xor sar shr shl neg copy
        cmp(Cond, K)   K w|l: eq ne sle slt sge sgt ule ult uge ugt;
                       K s|d: eq ne le lt ge gt o uo, result w
        ext(T)         T in sw uw sh uh sb ub s (s -> d)
        truncd         d -> s
        stosi stoui dtosi dtoui     s/d -> w/l
        swtof uwtof sltof ultof     w/l -> s/d
        cast           w <-> s, l <-> d, bitwise
        load(T)        T in l sw uw sh uh sb ub p s d
        alloc(Align)   Align in 4, 8, 16
        (op_kind/2 and valid_op/1 state these sets once)
        ptoi itop
        va_args       filc only: p cursor into the entry argument snapshot;
                      operand c(N), non-negative fixed-prefix byte count
        va_arg        filc only: w/l/p load through a va_list address,
                      advancing its cursor (reads and writes memory)
        setjmp(Kind)  filc only: w result, [p Buf, w SaveMask]; Kind is
                      setjmp | '_setjmp' | sigsetjmp. SaveMask must be
                      c(0) except for sigsetjmp. Native returns-twice;
                      snapshot/restore contract in docs/setjmp.md.

    Values: t(Name) | c(Integer) | glo(Name)
      At s/d, c(Integer) is an unsigned IEEE bit pattern (docs/float.md).

    data(Name, Linkage, Align, Items)
      Linkage  export | local | ro(export) | ro(local), ro for read-only
               data (in .rodata)
      Items: [item(W, c(N)) | item(b, str(Chars)) | item(l, sym(Name, Off))
              | item(p, sym(Name, Off)) | zero(N)]
      item(p, ...) is a pointer with the capability of Name (filc only).

    Temps are ground names; logic variables never appear in IR terms.

    A module is in one of two modes (module_mode/2):

      plain  classes w, l, s and d only. Addresses are l values, and the
             plain backend (amd64.pl) compiles it to ordinary x86-64.
      filc   any use of class p. Addresses are p values (flight pointers
             with a capability), alloc yields p, loads and stores take a p
             address, p arithmetic is add/sub of an l offset, and ptoi/itop
             convert. Calls may name functions outside the module, or go
             through a p value. A symbol is used only as %t =p copy $s,
             which yields a pointer to the data or function object; $s
             may be defined outside the module. See docs/m3.md, m4.md.

    Variable names below: M a module, Fn a function name, K a class
    (w, l or p), V an IR value, L a label.
*/
:- module(ir, [class_bits/2, modulus/2, half_modulus/2, op_arity/2,
               op_kind/2, valid_op/1, valid_module/1, func_named/3, width_bytes/2,
               op_arg_classes/4, op_result_ok/3,
               module_mode/2, addr_class/2, variadic_func/1, setjmp_func/1,
               narrow_type/3]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(dcgs)).

%! class(?K, ?Kind, ?Bits) is nondet.
%
%  K is a value class of Kind (int, pointer or float), Bits wide. Every
%  other fact about classes below follows from this table.

class(w, int, 32).
class(l, int, 64).
class(p, pointer, 64).
class(s, float, 32).
class(d, float, 64).

any_class(K) :- class(K, _, _).
int_class(K) :- class(K, int, _).
float_class(K) :- class(K, float, _).
numeric_class(K) :- int_class(K).
numeric_class(K) :- float_class(K).

%! class_bits(+K, -Bits) is semidet.
%
%  Bits is the width in bits of the numeric class K (w, l, s or d).

class_bits(K, Bits) :-
    numeric_class(K),
    class(K, _, Bits).

%! modulus(+K, -Mod) is semidet.
%
%  Mod is 2^bits(K): values of class K are the integers 0..Mod-1. A p
%  value's address has the modulus of l.

modulus(K, Mod) :-
    class(K, _, Bits),
    Mod is 1 << Bits.

%! half_modulus(+K, -Half) is semidet.
%
%  Half is half the modulus of the integer class K: the values Half..Mod-1
%  are negative when read as signed.

half_modulus(K, Half) :-
    class(K, int, Bits),
    Half is 1 << (Bits - 1).

%! width_bytes(+Width, -Size) is semidet.
%
%  A store of Width (b, h, or a class) writes Size bytes.

width_bytes(b, 1).
width_bytes(h, 2).
width_bytes(K, Size) :-
    class(K, _, Bits),
    Size is Bits // 8.

%! addr_class(+Mode, ?K) is semidet.
%
%  K is the class of an address in a module of Mode (plain or filc).

addr_class(plain, l).
addr_class(filc, p).

%! op_arity(+Op, -N) is semidet.
%
%  Op takes N arguments; it fails for anything that is not an Op of the
%  grammar.

op_arity(Op, N) :-
    op_kind(Op, Kind),
    kind_arity(Kind, N).

kind_arity(additive, 2).
kind_arity(alu, 2).
kind_arity(shift, 2).
kind_arity(cmp, 2).
kind_arity(neg, 1).
kind_arity(copy, 1).
kind_arity(ptoi, 1).
kind_arity(itop, 1).
kind_arity(va_args, 1).
kind_arity(va_arg, 1).
kind_arity(setjmp, 2).
kind_arity(ext, 1).
kind_arity(load, 1).
kind_arity(alloc, 1).
kind_arity(float_convert, 1).
kind_arity(float_to_int, 1).
kind_arity(int_to_float, 1).
kind_arity(cast, 1).

%! valid_op(+Op) is semidet.
%
%  Op is an instruction of the IR: one of op_kind/2's, with operands
%  from the sets below where it has them.

valid_op(cmp(Cond, K)) :- !, comparison(Cond, K).
valid_op(load(T)) :- !, load_type(T).
valid_op(alloc(Align)) :- !, alloc_align(Align).
valid_op(Op) :- op_kind(Op, _).

cmp_cond(eq).  cmp_cond(ne).
cmp_cond(sle). cmp_cond(slt). cmp_cond(sge). cmp_cond(sgt).
cmp_cond(ule). cmp_cond(ult). cmp_cond(uge). cmp_cond(ugt).

comparison(Cond, K) :- int_class(K), cmp_cond(Cond).
comparison(Cond, K) :- float_class(K), float_cond(Cond).
float_cond(eq). float_cond(ne). float_cond(le). float_cond(lt).
float_cond(ge). float_cond(gt). float_cond(o). float_cond(uo).

%! narrow_type(?T, ?Bytes, ?Signedness) is nondet.
%
%  The extension (and load) type T takes the low Bytes bytes of an
%  integer and extends them as Signedness says.
narrow_type(sw, 4, signed).   narrow_type(uw, 4, unsigned).
narrow_type(sh, 2, signed).   narrow_type(uh, 2, unsigned).
narrow_type(sb, 1, signed).   narrow_type(ub, 1, unsigned).


load_type(l). load_type(p).
load_type(d).
load_type(s).
load_type(T) :- narrow_type(T, _, _).

alloc_align(4).
alloc_align(8).
alloc_align(16).

%! op_kind(?Op, ?Kind) is nondet.
%
%  Kind is the category of Op that its consumers dispatch on, so that
%  each can case-split on Kind in clause heads. Deterministic in mode
%  (+, -): one fact per op, indexed on the first argument.
%
%    additive  add sub: integer, or (filc) a p plus or minus an l offset
%    alu       mul div udiv rem urem and or xor: binary, integer only
%    shift     sar shr shl: the count is read at w
%    neg copy ptoi itop  each its own kind; copy may be of class p
%    cmp ext load alloc  the four compounds

op_kind(add, additive).
op_kind(sub, additive).
op_kind(mul, alu).
op_kind(div, alu).
op_kind(udiv, alu).
op_kind(rem, alu).
op_kind(urem, alu).
op_kind(and, alu).
op_kind(or, alu).
op_kind(xor, alu).
op_kind(sar, shift).
op_kind(shr, shift).
op_kind(shl, shift).
op_kind(neg, neg).
op_kind(copy, copy).
op_kind(ptoi, ptoi).
op_kind(itop, itop).
op_kind(va_args, va_args).
op_kind(va_arg, va_arg).
op_kind(setjmp(Kind), setjmp) :- member(Kind, [setjmp, '_setjmp', sigsetjmp]).
op_kind(ext(s), float_convert).
op_kind(truncd, float_convert).
op_kind(stosi, float_to_int).
op_kind(stoui, float_to_int).
op_kind(dtosi, float_to_int).
op_kind(dtoui, float_to_int).
op_kind(swtof, int_to_float).
op_kind(uwtof, int_to_float).
op_kind(sltof, int_to_float).
op_kind(ultof, int_to_float).
op_kind(cast, cast).
op_kind(cmp(_, _), cmp).
op_kind(ext(T), ext) :- narrow_type(T, _, _).
op_kind(load(_), load).
op_kind(alloc(_), alloc).

%! func_named(+M, +Name, -Func) is semidet.
%
%  Func is the func/5 term that defines Name in the module M.

func_named(module(Items), Name, Func) :-
    Func = func(Name, _, _, _, _),
    memberchk(Func, Items).

% Entry snapshot metadata is retained even if its cursor is unused.
variadic_func(func(_, _, _, _, Blocks)) :-
    member(blk(_, _, Insts, _), Blocks),
    member(ins(_, p, va_args, _), Insts), !.

% Nonlocal returns restore compiler slots, not mutable local memory.
% Transformations must retain this boundary even in unreachable blocks.
setjmp_func(func(_, _, _, _, Blocks)) :-
    member(blk(_, _, Insts, _), Blocks),
    member(ins(_, _, setjmp(_), _), Insts), !.

%% Module mode

%! module_mode(+M, -Mode) is det.
%
%  Mode is filc when anything in M has class p, uses a pointer-only op,
%  or calls a function M does not define (which only the Fil-C ABI can
%  reach), and plain otherwise.

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

% pointer_item(+Item): Item has class p somewhere, or is read-only data,
% which only filc mode models. The cuts commit to the first witness.
pointer_item(func(_, _, Ret, Params, Blocks)) :-
    (   ( Ret == p ; Ret = tuple(_) )
    ;   member(par(p, _), Params)
    ;   member(blk(_, Phis, Insts, _), Blocks),
        (   member(phi(_, p, _), Phis)
        ;   member(Inst, Insts),
            pointer_inst(Inst)
        )
    ),
    !.
pointer_item(data(_, Linkage, _, Items)) :-
    (   Linkage = ro(_)
    ;   memberchk(item(p, _), Items)
    ),
    !.

% pointer_inst(+Inst): Inst produces, stores, passes or calls through a p
% value, or converts one (ptoi). Several clauses may hold for one Inst.
pointer_inst(ins(_, p, _, _)).
pointer_inst(ins(_, _, ptoi, _)).
pointer_inst(ins(_, _, setjmp(_), _)).
pointer_inst(store(p, _, _)).
pointer_inst(call(to(_, p), _, _)).
pointer_inst(call(tuple(_), _, _)).
pointer_inst(call(_, _, Args)) :- memberchk(arg(p, _), Args).
pointer_inst(call(_, t(_), _)).

%% Validation

%! valid_module(+M) is semidet.
%
%  M is a well-formed module. When it is not, throws
%  nanofil_error(Message) describing the first problem found, so callers
%  get a diagnostic rather than a silent failure. A few terms outside
%  the grammar (an item, instruction or jump of no known shape) make it
%  fail instead.
%
%  Functions are checked against a context
%    ctx(Module, Fn, Ret, LabelSet, TempClasses, PredMap, Mode)
%  whose three assocs map each label to t, each temporary to its class,
%  and each label to its sorted predecessors.

valid_module(M) :-
    M = module(Items),
    module_mode(M, Mode),
    maplist(valid_item(M, Mode), Items).

% valid_item(+M, +Mode, +Item): Item, an item of M, is well formed.
valid_item(M, Mode, func(Name, _, Ret, Params, Blocks)) :-
    (   Blocks == [] -> fn_error(Name, 'function has no blocks', []) ; true ),
    ( (any_class(Ret) ; Ret == void ; Ret = tuple(_)) -> true
    ; fn_error(Name, 'invalid return class ~w', [Ret]) ),
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
    forall((member(item(K, V), Items), float_class(K)),
           ( V = c(N), integer(N), modulus(K, Mod), N >= 0, N < Mod
           -> true ; fn_error(Name, 'invalid float data ~w', [V]) )),
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
    forall(member(_-K, Defs),
           ( any_class(K) -> true ; fn_error(Fn, 'invalid class ~w', [K]) )),
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

% valid_block(+Ctx, +Block): Block's phis cover exactly its predecessors,
% and its instructions and jump are well formed.
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

% jump_target(+Jump, -L) is nondet: Jump can branch to L.
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

% valid_inst(+Ctx, +Inst): Inst is well formed and reads each operand at
% a class its definition allows. In filc mode a symbol is an operand only
% of copy, which yields its pointer; the cut commits to that case before
% the general clause for ins/4.
valid_inst(ctx(_, _, _, _, _, _, filc), ins(_, p, copy, [glo(_)])) :- !.
valid_inst(Ctx, ins(_, K, Op, Args)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   valid_op(Op) -> true
    ;   fn_error(Fn, 'unknown instruction ~w', [Op])
    ),
    (   op_arity(Op, N), length(Args, N) -> true
    ;   fn_error(Fn, 'bad instruction ~w with ~w', [Op, Args])
    ),
    (   op_result_ok(Mode, Op, K) -> true
    ;   fn_error(Fn, 'instruction ~w cannot have class ~w', [Op, K])
    ),
    (   Op == va_args,
        \+ (Args = [c(Off)], integer(Off), Off >= 0)
    ->  fn_error(Fn, 'va_args needs a non-negative constant', [])
    ;   true
    ),
    (   Op = setjmp(Kind), Kind \== sigsetjmp, Args \= [_, c(0)]
    ->  fn_error(Fn, 'setjmp and _setjmp need a zero SaveMask', [])
    ;   true
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
    (   func_named(M, Callee, CalleeFunc),
        CalleeFunc = func(_, _, CalleeRet, Params, _)
    ->  findall(K, member(par(K, _), Params), ParamClasses),
        (   ( ParamClasses == ArgClasses
            ; variadic_func(CalleeFunc), append(ParamClasses, _, ArgClasses)
            ) -> true
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

% store_value_class(?Width, ?K): a store of Width reads its value at K.
store_value_class(b, w).
store_value_class(h, w).
store_value_class(K, K) :- any_class(K).

% call_result_ok(+Fn, +Callee, +Res, +CalleeRet): the call site reads the
% result the way the callee returns it.
call_result_ok(_, _, void, _).
call_result_ok(Fn, Callee, tuple(Tos), Ret) :-
    findall(K, member(to(_, K), Tos), Ks),
    (   Ret == tuple(Ks) -> true
    ;   fn_error(Fn, 'reads the ~w result of $~w as tuple(~w)',
                 [Ret, Callee, Ks])
    ).
call_result_ok(Fn, Callee, to(_, K), Ret) :-
    to_result_ok(Ret, K, Fn, Callee).

% to_result_ok(+Ret, +K, +Fn, +Callee): a call site may read at class K
% the result of Callee, which returns Ret.
to_result_ok(void, _, Fn, Callee) :-
    fn_error(Fn, 'uses the result of void $~w', [Callee]).
to_result_ok(tuple(_), K, Fn, Callee) :-
    fn_error(Fn, 'reads the tuple result of $~w as ~w', [Callee, K]).
to_result_ok(Ret, K, Fn, Callee) :-
    any_class(Ret),
    class_result_ok(Ret, K, Fn, Callee).

% class_result_ok(+Ret, +K, +Fn, +Callee): as to_result_ok/4, for a
% result of class Ret. A long may be read as a word, nothing else
% changes class.
class_result_ok(Ret, K, Fn, Callee) :-
    (   (float_class(Ret) ; float_class(K)), Ret \== K
    ->  fn_error(Fn, 'reads the ~w result of $~w as ~w', [Ret, Callee, K])
    ;   K == l, Ret == w
    ->  fn_error(Fn, 'reads the w result of $~w as l', [Callee])
    ;   ( K == p, Ret \== p ; K \== p, Ret == p )
    ->  fn_error(Fn, 'reads the ~w result of $~w as ~w', [Ret, Callee, K])
    ;   true
    ).

% valid_jump(+Ctx, +Jump): Jump names existing labels and returns what
% the function's return class requires.
valid_jump(Ctx, jmp(L)) :- label_exists(Ctx, L).
valid_jump(Ctx, jnz(V, L1, L2)) :-
    valid_use(Ctx, w, V),
    label_exists(Ctx, L1),
    label_exists(Ctx, L2).
valid_jump(Ctx, ret(V)) :-
    Ctx = ctx(_, _, Ret, _, _, _, _),
    ret_value_ok(Ret, Ctx, V).
valid_jump(Ctx, rets(Vs)) :-
    Ctx = ctx(_, Fn, Ret, _, _, _, _),
    (   Ret = tuple(Ks), length(Ks, N), length(Vs, N)
    ->  maplist(valid_use(Ctx), Ks, Vs)
    ;   fn_error(Fn, 'ret of a tuple in a ~w function', [Ret])
    ).
valid_jump(Ctx, ret) :-
    Ctx = ctx(_, Fn, Ret, _, _, _, _),
    ret_void_ok(Ret, Fn).
valid_jump(_, hlt).

% ret_value_ok(+Ret, +Ctx, +V): a function that returns Ret may return
% the one value V.
ret_value_ok(void, ctx(_, Fn, _, _, _, _, _), _) :-
    fn_error(Fn, 'ret with a value in a void function', []).
ret_value_ok(tuple(_), ctx(_, Fn, _, _, _, _, _), _) :-
    fn_error(Fn, 'ret of one value in a tuple function', []).
ret_value_ok(Ret, Ctx, V) :-
    any_class(Ret),
    valid_use(Ctx, Ret, V).

% ret_void_ok(+Ret, +Fn): a function that returns Ret may return
% nothing.
ret_void_ok(void, _).
ret_void_ok(tuple(_), Fn) :- fn_error(Fn, 'ret without a value', []).
ret_void_ok(Ret, Fn) :-
    any_class(Ret),
    fn_error(Fn, 'ret without a value', []).

label_exists(ctx(_, Fn, _, LabelSet, _, _, _), L) :-
    (   get_assoc(L, LabelSet, _) -> true
    ;   fn_error(Fn, 'undefined label @~w', [L])
    ).

% valid_use(+Ctx, +K, +V): V may be read at class K. Arguments are in the
% order maplist needs; valid_use_/3 indexes on the value.
valid_use(Ctx, K, V) :-
    Ctx = ctx(_, Fn, _, _, _, _, _),
    ( any_class(K) -> true ; fn_error(Fn, 'invalid use class ~w', [K]) ),
    valid_use_(V, Ctx, K).

% A p temporary is used only at p and vice versa; ptoi and itop are the
% conversions. An integer constant at p is a pointer with no capability.
valid_use_(t(N), ctx(_, Fn, _, _, TempClasses, _, _), K) :-
    (   get_assoc(N, TempClasses, K0)
    ->  (   (float_class(K) ; float_class(K0)), K \== K0
        ->  fn_error(Fn, '%~w has class ~w but is used as ~w', [N, K0, K])
        ;   K == l, K0 == w
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
valid_use_(c(N), ctx(_, Fn, _, _, _, _, _), K) :-
    integer(N),
    ( float_class(K), modulus(K, M), (N < 0 ; N >= M)
    -> fn_error(Fn, 'float bits out of range: ~w', [N])
    ; true ).
valid_use_(glo(G), Ctx, K) :-
    Ctx = ctx(_, _, _, _, _, _, Mode),
    symbol_use_ok(Mode, G, Ctx, K).

% symbol_use_ok(+Mode, +G, +Ctx, +K): the symbol $G may be read at class
% K in a module of Mode: in plain mode as an address of data, in filc
% mode never (copy, which yields its pointer, is checked apart).
symbol_use_ok(filc, G, ctx(_, Fn, _, _, _, _, _), _) :-
    fn_error(Fn, '$~w used as an operand; use %t =p copy $~w', [G, G]).
symbol_use_ok(plain, G, ctx(M, Fn, _, _, _, _, _), K) :-
    addr_class(plain, AddrClass),
    (   K == AddrClass -> true
    ;   fn_error(Fn, '$~w used as ~w', [G, K])
    ),
    M = module(Items),
    (   memberchk(data(G, _, _, _), Items) -> true
    ;   fn_error(Fn, '$~w is not a data definition', [G])
    ).

%% Operand and result classes

%! op_result_ok(+Mode, ?Op, ?K) is nondet.
%
%  Op may produce a result of class K in a module of Mode. With Op
%  partial (cmp(_, _), ext(_), load(_)) it enumerates the operands.
op_result_ok(Mode, Op, K) :-
    op_kind(Op, Kind),
    kind_result_ok(Kind, Op, Mode, K).

% kind_result_ok(+Kind, +Op, +Mode, +K): as op_result_ok/3, for Op of
% Kind.
kind_result_ok(additive, _, _, K) :- any_class(K).
kind_result_ok(alu, Op, _, K) :-
    ( int_class(K) ; memberchk(Op, [mul, div]), float_class(K) ).
kind_result_ok(shift, _, _, K) :- int_class(K).
kind_result_ok(neg, _, _, K) :- numeric_class(K).
kind_result_ok(copy, _, _, K) :- any_class(K).
kind_result_ok(ptoi, _, filc, l).
kind_result_ok(itop, _, filc, p).
kind_result_ok(va_args, _, filc, p).
kind_result_ok(va_arg, _, filc, K) :- any_class(K).
kind_result_ok(setjmp, _, filc, w).
kind_result_ok(cmp, cmp(C, CK), _, K) :-
    comparison(C, CK), (float_class(CK) -> K = w ; int_class(K)).
kind_result_ok(float_convert, ext(s), _, d).
kind_result_ok(float_convert, truncd, _, s).
kind_result_ok(float_to_int, _, _, K) :- int_class(K).
kind_result_ok(int_to_float, _, _, K) :- float_class(K).
kind_result_ok(cast, _, _, K) :- numeric_class(K).
kind_result_ok(ext, ext(T), _, K) :- ext_result_ok(T, K).
kind_result_ok(load, load(T), Mode, K) :- load_result_ok(T, Mode, K).
kind_result_ok(alloc, _, Mode, K) :- addr_class(Mode, K).

% ext_result_ok(+T, +K): an extension of type T may have class K; one
% from a word is a long.
ext_result_ok(sw, l).
ext_result_ok(uw, l).
ext_result_ok(sh, K) :- int_class(K).
ext_result_ok(uh, K) :- int_class(K).
ext_result_ok(sb, K) :- int_class(K).
ext_result_ok(ub, K) :- int_class(K).

% load_result_ok(+T, +Mode, +K): a load of type T may have class K in a
% module of Mode.
load_result_ok(l, _, l).
load_result_ok(p, filc, p).
load_result_ok(s, _, s).
load_result_ok(d, _, d).
load_result_ok(sw, _, K) :- int_class(K).
load_result_ok(uw, _, K) :- int_class(K).
load_result_ok(sh, _, K) :- int_class(K).
load_result_ok(uh, _, K) :- int_class(K).
load_result_ok(sb, _, K) :- int_class(K).
load_result_ok(ub, _, K) :- int_class(K).

%! op_arg_classes(+Op, +K, +Mode, ?Classes) is semidet.
%
%  Classes is the list of classes at which the arguments of Op are read
%  when its result has class K in a module of Mode. Fails for an Op
%  outside the grammar.

op_arg_classes(Op, K, Mode, Classes) :-
    op_kind(Op, Kind),
    kind_arg_classes(Kind, Op, K, Mode, Classes).

% kind_arg_classes(+Kind, +Op, +K, +Mode, ?Classes): as op_arg_classes/4,
% for Op of Kind.
kind_arg_classes(additive, _, K, _, Classes) :-
    additive_arg_classes(K, Classes).
kind_arg_classes(alu, _, K, _, [K, K]).
kind_arg_classes(shift, _, K, _, [K, w]).
kind_arg_classes(neg, _, K, _, [K]).
kind_arg_classes(copy, _, K, _, [K]).
kind_arg_classes(ptoi, _, _, _, [p]).
kind_arg_classes(itop, _, _, _, [l]).
kind_arg_classes(va_args, _, p, filc, [l]).
kind_arg_classes(va_arg, _, _, filc, [p]).
kind_arg_classes(setjmp, _, w, filc, [p, w]).
kind_arg_classes(cmp, cmp(_, CK), _, _, [CK, CK]).
kind_arg_classes(float_convert, ext(s), _, _, [s]).
kind_arg_classes(float_convert, truncd, _, _, [d]).
kind_arg_classes(float_to_int, Op, _, _, [K]) :-
    ( memberchk(Op, [stosi, stoui]) -> K = s ; K = d ).
kind_arg_classes(int_to_float, Op, _, _, [K]) :-
    ( memberchk(Op, [swtof, uwtof]) -> K = w ; K = l ).
kind_arg_classes(cast, _, K, _, [From]) :- cast_classes(K, From).
kind_arg_classes(ext, _, _, _, [w]).
kind_arg_classes(load, _, _, Mode, [A]) :- addr_class(Mode, A).
kind_arg_classes(alloc, _, _, _, [l]).

% additive_arg_classes(+K, ?Classes): add and sub of class K read
% Classes; at p they offset a pointer by an l.
additive_arg_classes(w, [w, w]).
additive_arg_classes(l, [l, l]).
additive_arg_classes(p, [p, l]).
additive_arg_classes(s, [s, s]).
additive_arg_classes(d, [d, d]).

cast_classes(w, s).
cast_classes(s, w).
cast_classes(l, d).
cast_classes(d, l).

% fn_error(+Fn, +Fmt, +Args): throw nanofil_error with the message
% Fmt/Args, attributed to the function Fn.
fn_error(Fn, Fmt, Args) :-
    format(atom(Msg), Fmt, Args),
    format(atom(Full), 'in $~w: ~w', [Fn, Msg]),
    throw(nanofil_error(Full)).

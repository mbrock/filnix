/*  The nanofil IR: modules of functions and data as ground Prolog
    terms, the contract between the frontend, the middle end, the
    interpreter and the backends. This module states its grammar and
    checks that a module is well formed.

    A function is a list of blocks; a block is phis, then instructions,
    then one jump. Temps are ground names; logic variables never appear
    in IR terms.

    ```diagram
    func(Name, Linkage, Ret, Params, Blocks)
    ┌───────────────────────────────┐
    │ entry block: first, no phis   │
    └───────────────┬───────────────┘
                    ▼
    ┌───────────────────────────────┐
    │ phis    phi(tmp(D), K, Pairs) │
    │ insts   let, store, call, loc │
    │ jump    goto, branch, ret ... │
    └───────────────────────────────┘
    ```

    ## Classes

    Every value has a class, one letter:

    | Class | Value |
    |---|---|
    | `w` | 32-bit integer (a word) |
    | `l` | 64-bit integer (a long) |
    | `s` | 32-bit float (single) |
    | `d` | 64-bit float (double) |
    | `p` | pointer: an address with its Fil-C capability (filc mode only) |
    | `a` | proven address: a `p` that a check has cleared (checked stage only) |
    | `f` | proven function: a `p` that a function check has cleared (checked stage only) |

    A store's width may also be `b` (8 bits) or `h` (16 bits). A load
    and `ext` name the narrow types `sb` `ub` `sh` `uh` `sw` `uw`:
    signed or unsigned byte, halfword and word.

    ## Items

    | Term | Means |
    |---|---|
    | `module(Items)` | Items are `func/5` and `data/4` terms, in source order |
    | `func(Name, Linkage, Ret, Params, Blocks)` | a function, fields below |
    | `data(Name, Linkage, Align, Items)` | a data object, fields under Data |

    | Field of func | Is |
    |---|---|
    | Name | an atom, the symbol |
    | Linkage | `export` or `local` |
    | Ret | `w`, `l`, `p`, `s`, `d`, `void`, or `tuple([K1, K2])` |
    | Params | a list of `param(K, tmp(N))`, K one of `w` `l` `p` `s` `d` |
    | Blocks | a list of `block(Label, Phis, Insts, Jump)`, the entry block first |

    A `tuple([K1, K2])` return is two words, each Ki `l` or `p`: a
    struct of 9 to 16 bytes (filc mode only).

    ## Phis and instructions

    | Term | Means |
    |---|---|
    | `phi(tmp(D), K, [Pred-Value])` | D is Value when control came from block Pred |
    | `let(tmp(D), K, Op, Args)` | D, of class K, is Op of Args (Ops below) |
    | `store(Width, Value, Addr)` | store Value at Addr; Width one of `b` `h` `w` `l` `p` `s` `d` |
    | `call(Res, Callee, [arg(K, Value)])` | call Callee: `global(F)`, or (filc mode) a `p` temp |
    | `loc(File, Line)` | does nothing: the instructions after it, up to the next loc, come from line Line of File |
    | `raw_store(Width, Off, Value, Addr)` | checked stage: a store at Addr+Off that does not check (Stages, below) |
    | `raw_call(Res, Callee, Args)` | checked stage: call the proven function Callee (class `f`); argument, result and exception handling are as for `call` |
    | `flight(tmp(D), Op, Args, Lower)` | checked stage: construct a `p` from a 64-bit address calculation and an independently selected capability |

    A call's Res is one of `result(tmp(D), K)`, `void`, or
    `tuple([result(tmp(D1), K1), result(tmp(D2), K2)])`.

    `flight` computes its address with `copy`, `add` or `sub`, using
    unsigned 64-bit arithmetic. Each argument is an `l` value or
    `address(P)`, the address bits of a `p` value. Lower is `none` or
    `lower(P)`, exactly P's capability identity, not an integer bound.
    The donors may differ: constructing a pair proves nothing about
    access. No getter, check, memory access or safepoint occurs inside
    flight; both components become one rooted `p` result. Projections
    occur only here and cannot read globals or proof classes.

    ## Jumps

    | Jump | Means |
    |---|---|
    | `goto(L)` | go to L |
    | `branch(V, L1, L2)` | go to L1 if V is nonzero, else to L2 |
    | `ret(V)` | return V |
    | `rets([V1, V2])` | return a tuple |
    | `ret` | return from a `void` function |
    | `unreachable` | stop the program (a trap instruction) |

    A jump's target may be `poll(L)`: a pollcheck on the edge, after the
    phis' copies, then L. A pollcheck is a safepoint: the thread may run
    signal handlers and answer the collector.

    ## Ops

    The Op of a `let(tmp(D), K, Op, Args)`; op_kind/2 and valid_op/1
    state these sets once, op_result_ok/3 and op_arg_classes/4 the
    classes.

    | Op | Result K | Args | Means |
    |---|---|---|---|
    | `add` `sub` | any | `[K, K]`; at `p`, a `p` and an `l` offset | |
    | `mul` `div` | `w` `l` `s` `d` | `[K, K]` | |
    | `udiv` `rem` `urem` `and` `or` `xor` | `w` `l` | `[K, K]` | |
    | `sar` `shr` `shl` | `w` `l` | `[K, w]` | the count is read at `w` |
    | `neg` | `w` `l` `s` `d` | `[K]` | |
    | `copy` | any | `[K]` | |
    | `cmp(Cond, K1)` | `w` `l`; `w` when K1 is a float | `[K1, K1]` | Cond for K1 `w` or `l`: `eq` `ne` `sle` `slt` `sge` `sgt` `ule` `ult` `uge` `ugt`; for `s` or `d`: `eq` `ne` `le` `lt` `ge` `gt` `o` `uo` |
    | `ext(T)` | `l` for `sw` `uw`; `w` or `l` for `sh` `uh` `sb` `ub` | `[w]` | extend the low bytes |
    | `ext(s)` | `d` | `[s]` | single to double |
    | `truncd` | `s` | `[d]` | double to single |
    | `stosi` `stoui` / `dtosi` `dtoui` | `w` `l` | `[s]` / `[d]` | float to signed or unsigned integer |
    | `swtof` `uwtof` / `sltof` `ultof` | `s` `d` | `[w]` / `[l]` | signed or unsigned integer to float |
    | `cast` | `w` `s` `l` `d` | `[s]` `[w]` `[d]` `[l]` | bitwise: `w` and `s`, `l` and `d` |
    | `load(T)` | as T: `l`, `p`, `s`, `d`; `w` or `l` for a narrow T | `[Addr]` | T one of `l` `sw` `uw` `sh` `uh` `sb` `ub` `p` `s` `d` |
    | `alloc(Align)` | the address class | `[l]`, the size | Align one of 4, 8, 16 |
    | `ptoi` | `l` | `[p]` | filc only |
    | `itop` | `p` | `[l]` | filc only |
    | `va_args` | `p` | `[const(N)]` | filc only: a cursor into the entry argument snapshot; N, non-negative, is the byte count of the fixed prefix |
    | `va_arg` | any | `[p]` | filc only: a load through a va_list address, advancing its cursor (reads and writes memory) |
    | `setjmp(Kind)` | `w` | `[p, w]`: Buf, SaveMask | filc only, below |
    | `check(Lo, Hi, Rights, Align)` | `a` | `[p]` | checked stage, below |
    | `raw_load(T, Off)` | as `load(T)` | `[a]` | checked stage: a load of type T at A+Off that does not check |
    | `check_function` | `f` | `[p]` | checked stage: trap unless the pointer designates a function object at its exact callable address |

    `setjmp(Kind)`: Kind is `setjmp`, `'_setjmp'` or `sigsetjmp`, and
    SaveMask must be `const(0)` except for `sigsetjmp`. It returns twice
    natively; the snapshot and restore contract is in docs/setjmp.md.

    `check(Lo, Hi, Rights, Align)` reads `[p P]`. It traps unless P's
    capability permits Rights (`read` or `write`) on [P+Lo, P+Hi) and
    P+Lo is Align-aligned (Align one of 1, 2, 4, 8, 16); otherwise its
    result is P, proven accessible.

    ## Values

    | Value | Means |
    |---|---|
    | `tmp(Name)` | a temporary, defined once (SSA) |
    | `const(Integer)` | a number; at `s` or `d` an unsigned IEEE bit pattern (docs/float.md) |
    | `global(Name)` | the address of a function or data object, by its symbol |

    ## Data

    In `data(Name, Linkage, Align, Items)`, Linkage is `export`,
    `local`, `ro(export)` or `ro(local)`, `ro` for read-only data (in
    .rodata), and Align is 1, 2, 4, 8 or 16. Items is a list of:

    | Item | Means |
    |---|---|
    | `item(W, const(N))` | N at width W |
    | `item(b, str(Chars))` | the bytes themselves, one character per byte (codes 0..255); a backend escapes them when it prints assembly |
    | `item(l, sym(Name, Off))` | the address of Name plus Off (plain mode) |
    | `item(p, sym(Name, Off))` | a pointer with the capability of Name (filc mode only) |
    | `zero(N)` | N zero bytes |

    ## Modes

    A module is in one of two modes, told apart by what it uses
    (module_mode/2):

    | Mode | Means |
    |---|---|
    | `plain` | classes `w`, `l`, `s` and `d` only. Addresses are `l` values, and the plain backend (amd64.pl) compiles it to ordinary x86-64. |
    | `filc` | anything of class `p`, a tuple return, read-only data, a pointer-only op, or a call to a function the module does not define. Addresses are `p` values (flight pointers with a capability), `alloc` yields `p`, loads and stores take a `p` address, `p` arithmetic is `add` or `sub` of an `l` offset, and `ptoi` and `itop` convert. |

    In filc mode calls may name functions outside the module, or go
    through a `p` value. A symbol `global(S)` is read only by
    `let(tmp(D), p, copy, [global(S)])`, which yields a pointer to the
    data or function object; S may be defined outside the module. See
    docs/m3.md and docs/m4.md.

    ## Stages

    A module is in one of two stages, told apart by its vocabulary:

    | Stage | Means |
    |---|---|
    | `unchecked` | as the frontend and the middle end write it. In filc mode, `load(T)` and `store` at a `p` address mean "Fil-C's access check, then the access". |
    | `checked` | after pizlonate.pl, what the Fil-C backend compiles: every check is explicit, and every cycle of the CFG has a poll edge. |

    In the checked stage a check yields a temporary of class `a`, a
    proven address, which only raw accesses read: `raw_load(T, Off)` and
    `raw_store(W, Off, V, A)`. The check that covers an access is its
    address operand's definition. A raw access its check does not cover
    is a bug of the pass, which the interpreter reports as the outcome
    `unchecked(Why)`.

    Pure pointer copies, add/sub and integer-to-pointer conversion use
    `flight` in checked IR; ordinary `p` copy remains only for getters.
    The middle end runs before pizlonation. Its entry point leaves a
    directly supplied checked module unchanged, even with `-O`.

    A `check_function` similarly yields class `f`, consumed only as
    the callee of the immediately following `raw_call`. It proves the
    target's identity, not a signature match: raw_call still selects
    fast or generic argument/result handling. A bad raw target reports
    `unchecked(not_a_function)`; traps from that handling or from the
    callee remain traps. Direct calls keep `call` and their ABI thunks.

    Neither proof class crosses a safepoint (a call, a pollcheck, `alloc`,
    `setjmp`, `va_arg`, a symbol's getter, or `raw_store(p, Off, V, A)`,
    whose ensure-aux may exit), since a free may make the proof stale.
    For now each check is followed immediately by its one use, so none
    can.

    ## Variable names

    In the predicates below: M a module, Fn a function name, K a class,
    V an IR value, L a label.
*/
:- module(ir, [class_bits/2, modulus/2, half_modulus/2, op_arity/2,
               op_kind/2, valid_op/1, valid_module/1, func_named/3, width_bytes/2,
               op_arg_classes/4, op_result_ok/3,
               module_mode/2, module_stage/2, addr_class/2, variadic_func/1, setjmp_func/1,
               narrow_type/3, without_locs/2, access_size_align/3,
               jump_target/2, polls_every_cycle/1, implicit_flight/1]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(dcgs)).
:- use_module(cfg).

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
kind_arity(check, 1).
kind_arity(check_function, 1).
kind_arity(ld, 1).

%! valid_op(+Op) is semidet.
%
%  Op is an instruction of the IR: one of op_kind/2's, with operands
%  from the sets below where it has them.

valid_op(cmp(Cond, K)) :- !, comparison(Cond, K).
valid_op(load(T)) :- !, load_type(T).
valid_op(alloc(Align)) :- !, alloc_align(Align).
valid_op(check(Lo, Hi, Rights, Align)) :- !,
    integer(Lo), integer(Hi), Lo < Hi,
    memberchk(Rights, [read, write]),
    memberchk(Align, [1, 2, 4, 8, 16]).
valid_op(raw_load(T, Off)) :- !, load_type(T), integer(Off).
valid_op(Op) :- op_kind(Op, _).

%! access_size_align(?X, ?Size, ?Align) is nondet.
%
%  A load of type X or a store of width X accesses Size bytes, and Fil-C
%  requires its address to be Align-aligned: 8 for a pointer, whose
%  capability lives in the aux word of its 8-byte slot, else 1.

access_size_align(p, 8, 8).
access_size_align(X, Size, 1) :-
    (   width_bytes(X, Size), X \== p
    ;   narrow_type(X, Size, _)
    ).

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
%    cmp ext load alloc  compounds
%    check ld   the checked stage: a check and a raw load

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
op_kind(check(_, _, _, _), check).
op_kind(check_function, check_function).
op_kind(raw_load(_, _), ld).

%! func_named(+M, +Name, -Func) is semidet.
%
%  Func is the func/5 term that defines Name in the module M.

func_named(module(Items), Name, Func) :-
    Func = func(Name, _, _, _, _),
    memberchk(Func, Items).

% Entry snapshot metadata is retained even if its cursor is unused.
variadic_func(func(_, _, _, _, Blocks)) :-
    member(block(_, _, Insts, _), Blocks),
    member(let(_, p, va_args, _), Insts), !.

% Nonlocal returns restore compiler slots, not mutable local memory.
% Transformations must retain this boundary even in unreachable blocks.
setjmp_func(func(_, _, _, _, Blocks)) :-
    member(block(_, _, Insts, _), Blocks),
    member(let(_, _, setjmp(_), _), Insts), !.

%% Module mode

%! module_mode(+M, -Mode) is det.
%
%  Mode is filc when anything in M has class p, uses a pointer-only op,
%  or calls a function M does not define (which only the Fil-C ABI can
%  reach), and plain otherwise.
%
%  The mode is inferred rather than stated: M uses a feature only filc
%  mode has, or it does not. Every rule above is such a feature, the
%  external call as much as class p. Stating the mode would mean a
%  module(Mode, Items) term or a Mode argument for valid_module/1,
%  run/5, promote and the backends, and a mode clause in each IR file,
%  for no case the inference gets wrong: a C module is filc unless it
%  uses none of these features (no memory, no pointers, no external
%  calls), and then validation, promotion and the interpreter treat it
%  alike in both modes; nanofil cc picks the Fil-C backend itself.

module_mode(module(Items), Mode) :-
    (   member(Item, Items),
        pointer_item(Item)
    ->  Mode = filc
    ;   member(func(_, _, _, _, Blocks), Items),
        member(block(_, _, Insts, _), Blocks),
        member(call(_, global(Callee), _), Insts),
        \+ memberchk(func(Callee, _, _, _, _), Items)
    ->  Mode = filc
    ;   Mode = plain
    ).

% pointer_item(+Item): Item has class p somewhere, or is read-only data,
% which only filc mode models. The cuts commit to the first witness.
pointer_item(func(_, _, Ret, Params, Blocks)) :-
    (   ( Ret == p ; Ret = tuple(_) )
    ;   member(param(p, _), Params)
    ;   member(block(_, Phis, Insts, _), Blocks),
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
pointer_inst(let(_, p, _, _)).
pointer_inst(let(_, _, ptoi, _)).
pointer_inst(let(_, _, setjmp(_), _)).
pointer_inst(store(p, _, _)).
pointer_inst(call(result(_, p), _, _)).
pointer_inst(call(tuple(_), _, _)).
pointer_inst(call(_, _, Args)) :- memberchk(arg(p, _), Args).
pointer_inst(call(_, tmp(_), _)).
pointer_inst(let(_, K, _, _)) :- proof_class(K).
pointer_inst(raw_store(_, _, _, _)).
pointer_inst(raw_call(_, _, _)).
pointer_inst(flight(_, _, _, _)).

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
    module_stage(M, Stage),
    maplist(valid_item(M, Mode, Stage), Items).

% module_stage(+M, -Stage): Stage is checked when M uses any word of the
% checked stage (a check, a raw access, flight or a poll edge), else unchecked.
module_stage(module(Items), Stage) :-
    (   member(func(_, _, _, _, Blocks), Items),
        member(block(_, _, Insts, Jump), Blocks),
        (   member(Inst, Insts), checked_inst(Inst)
        ;   checked_jump(Jump)
        )
    ->  Stage = checked
    ;   Stage = unchecked
    ).

checked_inst(let(_, _, check(_, _, _, _), _)).
checked_inst(let(_, _, check_function, _)).
checked_inst(let(_, _, raw_load(_, _), _)).
checked_inst(raw_store(_, _, _, _)).
checked_inst(raw_call(_, _, _)).
checked_inst(flight(_, _, _, _)).

checked_jump(goto(poll(_))).
checked_jump(branch(_, poll(_), _)).
checked_jump(branch(_, _, poll(_))).

% valid_item(+M, +Mode, +Stage, +Item): Item, an item of M, is well
% formed.
valid_item(M, Mode, Stage, func(Name, _, Ret, Params, Blocks)) :-
    (   Blocks == [] -> fn_error(Name, 'function has no blocks', []) ; true ),
    ( (any_class(Ret) ; Ret == void ; Ret = tuple(_)) -> true
    ; fn_error(Name, 'invalid return class ~w', [Ret]) ),
    (   Ret = tuple(Ks),
        \+ ( Ks = [_, _], forall(member(K, Ks), memberchk(K, [l, p])) )
    ->  fn_error(Name,
                 'a tuple return is two words of class l or p, not ~w', [Ks])
    ;   true
    ),
    findall(Label, member(block(Label, _, _, _), Blocks), Labels),
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
    Blocks = [block(Entry, _, _, _)|_],
    (   member(block(_, _, _, Jump), Blocks),
        jump_target(Jump, Entry)
    ->  fn_error(Name, 'jump to the entry block ~w', [Entry])
    ;   true
    ),
    proof_class_defs(Name, Params, Blocks),
    definitions_dominate(Name, Params, Blocks),
    stage_func(Stage, Name, Mode, Blocks).
valid_item(_, Mode, _, data(Name, _, Align, Items)) :-
    (   memberchk(Align, [1, 2, 4, 8, 16]) -> true
    ;   fn_error(Name, 'unsupported data alignment ~w', [Align])
    ),
    forall((member(item(K, V), Items), float_class(K)),
           ( V = const(N), integer(N), modulus(K, Mod), N >= 0, N < Mod
           -> true ; fn_error(Name, 'invalid float data ~w', [V]) )),
    (   Mode == plain, memberchk(item(p, _), Items)
    ->  fn_error(Name, 'pointer data items need a Fil-C module', [])
    ;   Mode == filc, memberchk(item(l, sym(Sym, _)), Items)
    ->  fn_error(Name, 'a pointer in a Fil-C module is item(p, sym(~w, _))',
                 [Sym])
    ;   true
    ),
    forall(member(item(_, str(Cs)), Items),
           ( maplist(byte_char, Cs) -> true
           ; fn_error(Name, 'str/1 holds characters of codes 0..255', []) )).

% byte_char(+C): C is a character that stands for one byte.
byte_char(C) :- atom(C), atom_length(C, 1), char_code(C, N), N =< 255.

% temp_defs(+Params, +Blocks, -Defs): Name-Class for every definition of
% a temporary, in parameter and then block order.
temp_defs(Params, Blocks, Defs) :-
    findall(N-K, member(param(K, tmp(N)), Params), ParamDefs),
    findall(N-K,
            ( member(block(_, Phis, Insts, _), Blocks),
              (   member(phi(tmp(N), K, _), Phis)
              ;   member(let(tmp(N), K, _, _), Insts)
              ;   member(flight(tmp(N), _, _, _), Insts), K = p
              ;   member(I, Insts), call_result_args(I, Res, _),
                  ( Res = result(tmp(N), K)
                  ; Res = tuple(Tos), member(result(tmp(N), K), Tos) )
              ) ),
            BlockDefs),
    append(ParamDefs, BlockDefs, Defs).

% Both call forms have the same result and argument vocabulary; only
% the callee's proof obligation differs.
call_result_args(call(Res, _, Args), Res, Args).
call_result_args(raw_call(Res, _, Args), Res, Args).

% Defs is sorted, so two classes for one temporary are adjacent.
check_temp_classes(Fn, Defs) :-
    forall(member(_-K, Defs),
           ( temp_class(K) -> true ; fn_error(Fn, 'invalid class ~w', [K]) )),
    (   append(_, [N-K1, N-K2|_], Defs), K1 \== K2
    ->  fn_error(Fn, 'tmp(~w) has classes ~w and ~w', [N, K1, K2])
    ;   true
    ).

% predecessors(+Blocks, -PredMap): each label's sorted predecessors.
predecessors(Blocks, PredMap) :-
    findall(Target-Pred,
            ( member(block(Pred, _, _, Jump), Blocks),
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
valid_block(Ctx, block(Label, Phis, Insts, Jump)) :-
    Ctx = ctx(_, Fn, _, _, _, PredMap, _),
    (   get_assoc(Label, PredMap, Preds) -> true ; Preds = [] ),
    maplist(valid_phi(Ctx, Label, Preds), Phis),
    maplist(valid_inst(Ctx), Insts),
    valid_jump(Ctx, Jump),
    (   Phis \== [], Preds == []
    ->  fn_error(Fn, 'phi in block ~w, which has no predecessors', [Label])
    ;   true
    ).

%! jump_target(+Jump, -L) is nondet.
%
%  Jump can branch to the label L, with or without a pollcheck.
jump_target(goto(T), L) :- edge_label(T, L).
jump_target(branch(_, T, _), L) :- edge_label(T, L).
jump_target(branch(_, _, T), L) :- edge_label(T, L).

% temp_class(?K): a temporary may have a value class or a proof class.
% Proofs live in no memory and are not values of C.
temp_class(K) :- any_class(K).
temp_class(K) :- proof_class(K).

proof_class(a).
proof_class(f).

% proof_class_defs(+Fn, +Params, +Blocks): only a check defines a
% proof temporary, and nothing passes one as a call argument. Phis,
% parameters and call results would carry a proof across an edge or a
% safepoint. (A check's own class is op_result_ok/3's.)
proof_class_defs(Fn, Params, Blocks) :-
    (   (   member(param(K, _), Params)
        ;   member(block(_, Phis, Insts, _), Blocks),
            (   member(phi(_, K, _), Phis)
            ;   member(I, Insts), call_result_args(I, Res, Args),
                (   Res = result(_, K)
                ;   Res = tuple(Tos), member(result(_, K), Tos)
                ;   member(arg(K, _), Args)
                )
            )
        ), proof_class(K)
    ->  fn_error(Fn, 'class ~w is only a check''s result', [K])
    ;   true
    ).

/* definitions_dominate(+Fn, +Params, +Blocks): in every reachable block,
   each use of a temporary is dominated by one of its definitions: a
   parameter, an earlier instruction or phi of the same block, or one in
   a block that strictly dominates it. A phi reads its value at the end
   of the predecessor, if that is reachable. A temporary may be defined
   more than once (tests/fixtures/memory.ir); one dominating definition
   is enough. Unreachable blocks are not checked. */
definitions_dominate(Fn, Params, Blocks) :-
    func_cfg(Blocks, Cfg),
    cfg_idoms(Cfg, Idom),
    dom_intervals(Cfg, Idom, Intervals),
    findall(N-param, member(param(_, tmp(N)), Params), ParamSites),
    block_sites(Blocks, Pairs0, []),
    append(ParamSites, Pairs0, Pairs),
    keysort(Pairs, Sorted),
    group_sites(Sorted, Grouped),
    list_to_assoc(Grouped, Sites),
    findall(L-End, ( member(block(L, _, Insts, _), Blocks), length(Insts, End) ),
            Ends0),
    list_to_assoc(Ends0, Ends),
    dominated_blocks(Blocks, dom(Fn, Sites, Intervals, Ends)).

% block_sites(+Blocks)//: N-at(L, I) for each definition of tmp(N), at
% index I of block L, a phi's at -1.
block_sites([]) --> [].
block_sites([block(L, Phis, Insts, _)|Bs]) -->
    phi_sites(Phis, L),
    inst_sites(Insts, L, 0),
    block_sites(Bs).

phi_sites([], _) --> [].
phi_sites([phi(tmp(N), _, _)|Phis], L) --> [N-at(L, -1)], phi_sites(Phis, L).

inst_sites([], _, _) --> [].
inst_sites([Inst|Insts], L, I) -->
    { findall(N-at(L, I), inst_def(Inst, N), Defs),
      I1 is I + 1 },
    seq(Defs),
    inst_sites(Insts, L, I1).

% group_sites(+Pairs, -Groups): Pairs N-Site, sorted by N, grouped as
% N-Sites.
group_sites([], []).
group_sites([N-S|Ps], [N-[S|Ss]|Gs]) :-
    same_key(N, Ps, Ss, Rest),
    group_sites(Rest, Gs).

same_key(N, [N1-S|Ps], [S|Ss], Rest) :- N1 == N, !, same_key(N, Ps, Ss, Rest).
same_key(_, Ps, [], Ps).

% dominated_blocks(+Blocks, +D): every use in the reachable blocks of
% Blocks (those with a dominator-tree interval) is dominated: an
% instruction's at its index, the jump's at the end of the block, and a
% phi's operand at the end of its predecessor, if that is reachable. D
% is dom(Fn, Sites, Intervals, Ends), Ends the number of instructions of
% each block. Plain recursion, not maplist/3 over closures, which
% Trealla copies with D at every call.
dominated_blocks([], _).
dominated_blocks([block(L, Phis, Insts, Jump)|Bs], D) :-
    D = dom(_, _, Intervals, _),
    (   get_assoc(L, Intervals, _)
    ->  dominated_insts(Insts, 0, End, L, D),
        jump_uses(Jump, Us),
        dominated_uses(Us, L, End, D),
        dominated_phis(Phis, D)
    ;   true
    ),
    dominated_blocks(Bs, D).

dominated_insts([], I, I, _, _).
dominated_insts([Inst|Insts], I, End, L, D) :-
    inst_uses(Inst, Us),
    dominated_uses(Us, L, I, D),
    I1 is I + 1,
    dominated_insts(Insts, I1, End, L, D).

dominated_uses([], _, _, _).
dominated_uses([N|Ns], L, I, D) :-
    dominated_use(D, L, I, N),
    dominated_uses(Ns, L, I, D).

dominated_phis([], _).
dominated_phis([phi(_, _, PVs)|Phis], D) :-
    dominated_phi_operands(PVs, D),
    dominated_phis(Phis, D).

dominated_phi_operands([], _).
dominated_phi_operands([P-V|PVs], D) :-
    D = dom(_, _, Intervals, Ends),
    (   V = tmp(N), get_assoc(P, Intervals, _)
    ->  get_assoc(P, Ends, End),
        dominated_use(D, P, End, N)
    ;   true
    ),
    dominated_phi_operands(PVs, D).

% dominated_use(+D, +L, +I, +N): some definition of tmp(N) dominates
% position I of block L.
dominated_use(dom(Fn, Sites, Intervals, _), L, I, N) :-
    (   get_assoc(N, Sites, Defs),
        member(Def, Defs),
        site_dominates(Def, L, I, Intervals)
    ->  true
    ;   fn_error(Fn, 'tmp(~w) is used in block ~w, which no definition dominates',
                 [N, L])
    ).

% site_dominates(+Def, +L, +I, +Intervals): the definition Def comes
% before position I of block L on every path from the entry.
site_dominates(param, _, _, _).
site_dominates(at(L, J), L, I, _) :- J < I.
site_dominates(at(D, _), L, _, Intervals) :-
    D \== L,
    dominates_by_interval(Intervals, D, L).

% stage_func(+Stage, +Fn, +Mode, +Blocks): Fn's blocks are well formed
% for the module's Stage. A checked function accesses memory only by raw
% accesses, each covered by the check right before it, and polls on
% every cycle.
stage_func(unchecked, _, _, _).
stage_func(checked, Fn, Mode, Blocks) :-
    forall(member(block(_, _, Insts, _), Blocks), checked_insts(Insts, Fn, Mode)),
    (   polls_every_cycle(Blocks) -> true
    ;   fn_error(Fn, 'a cycle without a poll edge in checked IR', [])
    ).

% checked_insts(+Insts, +Fn, +Mode): each check in Insts is followed by
% the one access it covers, which is its only use, so no safepoint can
% come between them; no other instruction accesses memory unchecked.
checked_insts([], _, _).
checked_insts([Inst|Insts], Fn, Mode) :-
    checked_inst_rest(Inst, Insts, Fn, Mode, Rest),
    checked_insts(Rest, Fn, Mode).

checked_inst_rest(let(tmp(Q), a, check(Lo, Hi, Rights, Align), _), Insts, Fn, _,
                  Rest) :- !,
    (   Insts = [Access|Rest],
        covered_access(Access, Q, Lo, Hi, Rights, Align)
    ->  true
    ;   fn_error(Fn, 'check tmp(~w) is not followed by an access it covers', [Q])
    ).
checked_inst_rest(let(tmp(Q), f, check_function, _), Insts, Fn, _, Rest) :- !,
    (   Insts = [raw_call(_, tmp(Q), _)|Rest] -> true
    ;   fn_error(Fn, 'function check tmp(~w) is not followed by its raw call', [Q])
    ).
checked_inst_rest(Inst, Insts, Fn, Mode, Insts) :-
    (   raw_access(Inst, _, _, _, _)
    ->  fn_error(Fn, 'a raw access whose address is not checked just before it', [])
    ;   Inst = raw_call(_, _, _)
    ->  fn_error(Fn, 'a raw call whose target is not checked just before it', [])
    ;   Mode == filc, unchecked_access(Inst, What)
    ->  fn_error(Fn, '~w in checked IR, where every access is checked', [What])
    ;   implicit_flight(Inst)
    ->  fn_error(Fn, 'implicit pointer operation in checked IR; use flight', [])
    ;   true
    ).

% implicit_flight(+Inst): a pure pointer operation whose address/lower
% policy must be made explicit before either validation or emission of
% checked IR. Getter copies are effects, not members of this set.
implicit_flight(let(_, p, Op, _)) :- memberchk(Op, [add, sub, itop]).
implicit_flight(let(_, p, copy, [tmp(_)])).
implicit_flight(let(_, p, copy, [const(_)])).

% raw_access(?Inst, ?Q, ?X, ?Off, ?Rights): Inst is a raw load of type X
% or store of width X at tmp(Q)+Off, needing Rights.
raw_access(let(_, _, raw_load(T, Off), [tmp(Q)]), Q, T, Off, read).
raw_access(raw_store(W, Off, _, tmp(Q)), Q, W, Off, write).

unchecked_access(let(_, _, load(T), _), load(T)).
unchecked_access(store(W, _, _), store(W)).
unchecked_access(call(_, tmp(_), _), 'indirect call').

% covered_access(+Access, +Q, +Lo, +Hi, +Rights, +Align): Access is a raw
% access at tmp(Q) within [Q+Lo, Q+Hi), as aligned as it must be, and
% Rights allow it (write allows reading too).
covered_access(Access, Q, Lo, Hi, Rights, Align) :-
    raw_access(Access, Q, X, Off, Need),
    access_size_align(X, Size, AccessAlign), !,
    Lo =< Off, Off + Size =< Hi,
    Align mod AccessAlign =:= 0,
    (Off - Lo) mod AccessAlign =:= 0,
    rights_allow(Rights, Need).

rights_allow(write, _).
rights_allow(read, read).

%! polls_every_cycle(+Blocks) is semidet.
%
%  Every cycle of the control-flow graph of Blocks, unreachable blocks
%  included, has a poll edge: without them the graph is acyclic. A call
%  does not count, since the callee need not poll. Depth-first search,
%  with each label gray while on the path and done after.
polls_every_cycle(Blocks) :-
    findall(L-Ss,
            ( member(block(L, _, _, Jump), Blocks),
              findall(S, unpolled_edge(Jump, S), Ss) ),
            Pairs),
    list_to_assoc(Pairs, Graph),
    empty_assoc(Color0),
    findall(L, member(L-_, Pairs), Labels),
    acyclic_from_all(Labels, Graph, Color0, _).

unpolled_edge(goto(T), T) :- T \= poll(_).
unpolled_edge(branch(_, T, _), T) :- T \= poll(_).
unpolled_edge(branch(_, _, T), T) :- T \= poll(_).

% acyclic_from_all(+Ls, +Graph, +Color0, -Color): no cycle of Graph is
% reachable from Ls; a gray successor closes one. Plain recursion, since
% Trealla copies a closure's arguments, Graph included, at every call.
acyclic_from_all([], _, Color, Color).
acyclic_from_all([L|Ls], Graph, Color0, Color) :-
    (   get_assoc(L, Color0, C)
    ->  C == done, Color1 = Color0
    ;   put_assoc(L, Color0, gray, ColorG),
        get_assoc(L, Graph, Ss),
        acyclic_from_all(Ss, Graph, ColorG, ColorS),
        put_assoc(L, ColorS, done, Color1)
    ),
    acyclic_from_all(Ls, Graph, Color1, Color).

valid_phi(Ctx, Label, Preds, phi(_, K, Pairs)) :-
    Ctx = ctx(_, Fn, _, _, _, _, _),
    split_pairs(Pairs, PhiPreds0, Values),
    sort(PhiPreds0, PhiPreds),
    (   PhiPreds == Preds -> true
    ;   fn_error(Fn, 'phi in block ~w covers ~w but predecessors are ~w',
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
valid_inst(ctx(_, Fn, _, _, _, _, _), loc(File, Line)) :- !,
    (   atom(File), integer(Line) -> true
    ;   fn_error(Fn, 'bad source location loc(~q, ~q)', [File, Line])
    ).
valid_inst(Ctx, flight(tmp(_), Op, Args, Lower)) :-
    Ctx = ctx(_, Fn, _, _, _, _, filc),
    (   memberchk(Op, [copy, add, sub]), op_arity(Op, N), length(Args, N)
    ->  true
    ;   fn_error(Fn, 'bad flight calculation ~w with ~w', [Op, Args])
    ),
    maplist(valid_flight_arg(Ctx), Args),
    valid_flight_lower(Lower, Ctx).
valid_inst(ctx(_, _, _, _, _, _, filc), let(_, p, copy, [global(_)])) :- !.
valid_inst(Ctx, let(_, K, Op, Args)) :-
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
        \+ (Args = [const(Off)], integer(Off), Off >= 0)
    ->  fn_error(Fn, 'va_args needs a non-negative constant', [])
    ;   true
    ),
    (   Op = setjmp(Kind), Kind \== sigsetjmp, Args \= [_, const(0)]
    ->  fn_error(Fn, 'setjmp and _setjmp need a zero SaveMask', [])
    ;   true
    ),
    op_arg_classes(Op, K, Mode, ArgClasses),
    maplist(valid_use(Ctx), ArgClasses, Args).
valid_inst(Ctx, store(Width, Value, Addr)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   Width == p, Mode == plain
    ->  fn_error(Fn, 'store(p, ...) needs a Fil-C module', [])
    ;   true
    ),
    store_value_class(Width, ValueClass),
    valid_use(Ctx, ValueClass, Value),
    addr_class(Mode, AddrClass),
    valid_use(Ctx, AddrClass, Addr).
valid_inst(Ctx, raw_store(Width, Off, Value, Addr)) :-
    Ctx = ctx(_, Fn, _, _, _, _, _),
    (   store_value_class(Width, ValueClass), integer(Off) -> true
    ;   fn_error(Fn, 'bad raw store raw_store(~w, ~w, ...)', [Width, Off])
    ),
    valid_use(Ctx, ValueClass, Value),
    valid_use(Ctx, a, Addr).
valid_inst(Ctx, call(Res, global(Callee), Args)) :-
    Ctx = ctx(M, Fn, _, _, _, _, Mode),
    findall(K, member(arg(K, _), Args), ArgClasses),
    (   func_named(M, Callee, CalleeFunc),
        CalleeFunc = func(_, _, CalleeRet, Params, _)
    ->  findall(K, member(param(K, _), Params), ParamClasses),
        (   ( ParamClasses == ArgClasses
            ; variadic_func(CalleeFunc), append(ParamClasses, _, ArgClasses)
            ) -> true
        ;   fn_error(Fn, 'call to global(~w) passes ~w, expects ~w',
                     [Callee, ArgClasses, ParamClasses])
        ),
        call_result_ok(Fn, Callee, Res, CalleeRet)
    ;   Mode == filc -> true
    ;   fn_error(Fn, 'call to undefined function global(~w)', [Callee])
    ),
    forall(member(arg(K, V), Args), valid_use(Ctx, K, V)).
valid_inst(Ctx, call(_, Callee, Args)) :-
    Ctx = ctx(_, Fn, _, _, _, _, Mode),
    (   Mode == filc, Callee = tmp(_) -> valid_use(Ctx, p, Callee)
    ;   fn_error(Fn, 'bad callee ~w', [Callee])
    ),
    forall(member(arg(K, V), Args), valid_use(Ctx, K, V)).
valid_inst(Ctx, raw_call(_, Callee, Args)) :-
    valid_use(Ctx, f, Callee),
    forall(member(arg(K, V), Args), valid_use(Ctx, K, V)).

% store_value_class(?Width, ?K): a store of Width reads its value at K.
store_value_class(b, w).
store_value_class(h, w).
store_value_class(K, K) :- any_class(K).

% call_result_ok(+Fn, +Callee, +Res, +CalleeRet): the call site reads the
% result the way the callee returns it.
call_result_ok(_, _, void, _).
call_result_ok(Fn, Callee, tuple(Tos), Ret) :-
    findall(K, member(result(_, K), Tos), Ks),
    (   Ret == tuple(Ks) -> true
    ;   fn_error(Fn, 'reads the ~w result of global(~w) as tuple(~w)',
                 [Ret, Callee, Ks])
    ).
call_result_ok(Fn, Callee, result(_, K), Ret) :-
    to_result_ok(Ret, K, Fn, Callee).

% to_result_ok(+Ret, +K, +Fn, +Callee): a call site may read at class K
% the result of Callee, which returns Ret.
to_result_ok(void, _, Fn, Callee) :-
    fn_error(Fn, 'uses the result of void global(~w)', [Callee]).
to_result_ok(tuple(_), K, Fn, Callee) :-
    fn_error(Fn, 'reads the tuple result of global(~w) as ~w', [Callee, K]).
to_result_ok(Ret, K, Fn, Callee) :-
    any_class(Ret),
    class_result_ok(Ret, K, Fn, Callee).

% class_result_ok(+Ret, +K, +Fn, +Callee): as to_result_ok/4, for a
% result of class Ret. A long may be read as a word, nothing else
% changes class.
class_result_ok(Ret, K, Fn, Callee) :-
    (   (float_class(Ret) ; float_class(K)), Ret \== K
    ->  fn_error(Fn, 'reads the ~w result of global(~w) as ~w', [Ret, Callee, K])
    ;   K == l, Ret == w
    ->  fn_error(Fn, 'reads the w result of global(~w) as l', [Callee])
    ;   ( K == p, Ret \== p ; K \== p, Ret == p )
    ->  fn_error(Fn, 'reads the ~w result of global(~w) as ~w', [Ret, Callee, K])
    ;   true
    ).

% valid_jump(+Ctx, +Jump): Jump names existing labels and returns what
% the function's return class requires.
valid_jump(Ctx, goto(T)) :- target_exists(Ctx, T).
valid_jump(Ctx, branch(V, T1, T2)) :-
    valid_use(Ctx, w, V),
    target_exists(Ctx, T1),
    target_exists(Ctx, T2).
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
valid_jump(_, unreachable).

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

% target_exists(+Ctx, +T): the jump target T, a label or poll(Label),
% names a block.
target_exists(Ctx, T) :-
    edge_label(T, L),
    label_exists(Ctx, L).

label_exists(ctx(_, Fn, _, LabelSet, _, _, _), L) :-
    (   get_assoc(L, LabelSet, _) -> true
    ;   fn_error(Fn, 'undefined block label ~w', [L])
    ).

% Projections are local to flight, not new ordinary operands. A lower
% is copied only from a p value; no integer can manufacture one.
valid_flight_arg(Ctx, address(P)) :- !, valid_use(Ctx, p, P).
valid_flight_arg(Ctx, V) :- valid_use(Ctx, l, V).

valid_flight_lower(none, _).
valid_flight_lower(lower(P), Ctx) :- valid_use(Ctx, p, P).

% valid_use(+Ctx, +K, +V): V may be read at class K. Arguments are in the
% order maplist needs; valid_use_/3 indexes on the value.
valid_use(Ctx, K, V) :-
    Ctx = ctx(_, Fn, _, _, _, _, _),
    ( temp_class(K) -> true ; fn_error(Fn, 'invalid use class ~w', [K]) ),
    valid_use_(V, Ctx, K).

% A p temporary is used only at p and vice versa; ptoi and itop are the
% conversions. An integer constant at p is a pointer with no capability.
% Only a check makes a proof (class a or f): no constant is one.
valid_use_(tmp(N), ctx(_, Fn, _, _, TempClasses, _, _), K) :-
    (   get_assoc(N, TempClasses, K0)
    ->  (   (proof_class(K) ; proof_class(K0)), K \== K0
        ->  fn_error(Fn, 'tmp(~w) has class ~w but is used as ~w', [N, K0, K])
        ;   (float_class(K) ; float_class(K0)), K \== K0
        ->  fn_error(Fn, 'tmp(~w) has class ~w but is used as ~w', [N, K0, K])
        ;   K == l, K0 == w
        ->  fn_error(Fn, 'tmp(~w) has class w but is used as l', [N])
        ;   K0 == p, K \== p
        ->  fn_error(Fn, 'tmp(~w) has class p but is used as ~w (use ptoi)',
                     [N, K])
        ;   K == p, K0 \== p
        ->  fn_error(Fn, 'tmp(~w) has class ~w but is used as p (use itop)',
                     [N, K0])
        ;   true
        )
    ;   fn_error(Fn, 'undefined temporary tmp(~w)', [N])
    ).
valid_use_(const(N), ctx(_, Fn, _, _, _, _, _), K) :-
    integer(N),
    ( float_class(K), modulus(K, M), (N < 0 ; N >= M)
    -> fn_error(Fn, 'float bits out of range: ~w', [N])
    ; proof_class(K)
    -> fn_error(Fn, 'const(~w) used as a proof (class ~w)', [N, K])
    ; true ).
valid_use_(global(G), Ctx, K) :-
    Ctx = ctx(_, _, _, _, _, _, Mode),
    symbol_use_ok(Mode, G, Ctx, K).

% symbol_use_ok(+Mode, +G, +Ctx, +K): the symbol global(G) may be read at
% class K in a module of Mode: in plain mode as an address of data, in
% filc mode never (copy, which yields its pointer, is checked apart).
symbol_use_ok(filc, G, ctx(_, Fn, _, _, _, _, _), _) :-
    fn_error(Fn, 'in a Fil-C module only copy at p reads global(~w)', [G]).
symbol_use_ok(plain, G, ctx(M, Fn, _, _, _, _, _), K) :-
    addr_class(plain, AddrClass),
    (   K == AddrClass -> true
    ;   fn_error(Fn, 'global(~w) used as ~w', [G, K])
    ),
    M = module(Items),
    (   memberchk(data(G, _, _, _), Items) -> true
    ;   fn_error(Fn, 'global(~w) is not a data definition', [G])
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
kind_result_ok(check, _, filc, a).
kind_result_ok(check_function, _, filc, f).
kind_result_ok(ld, raw_load(T, _), filc, K) :- load_result_ok(T, filc, K).

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
kind_arg_classes(check, _, _, filc, [p]).
kind_arg_classes(check_function, _, _, filc, [p]).
kind_arg_classes(ld, _, _, filc, [a]).

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
    format(atom(Full), 'in ~w: ~w', [Fn, Msg]),
    throw(nanofil_error(Full)).

%! without_locs(+Module0, -Module) is det.
%
%  Module is Module0 without its loc/2 source locations, which the
%  middle end and the backends do not read yet.
without_locs(module(Items0), module(Items)) :-
    maplist(item_without_locs, Items0, Items).

item_without_locs(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    maplist(block_without_locs, Bs0, Bs).
item_without_locs(Item, Item).

block_without_locs(block(L, Phis, Insts0, J), block(L, Phis, Insts, J)) :-
    exclude(is_loc, Insts0, Insts).

is_loc(loc(_, _)).

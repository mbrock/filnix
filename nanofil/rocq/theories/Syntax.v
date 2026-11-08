(** The [[core-subset|core subset]] of the [[stage|checked IR]],
    transcribed from ir.pl: its grammar as inductive types, one
    constructor per functor of the intermediate representation (IR),
    and the small tables of facts the semantics reads.

    The subset is formal.md's: [[mode|filc mode]], the checked stage,
    the integer and pointer [[class|classes]], [[check]] and its
    [[reuse]] vocabulary, the `raw_*` [[raw-access|accesses]],
    [[flight]], [[poll|poll edges]], `call`, `raw_call` and `free`, and
    named locals; and, for the Lua suite, the float classes with their
    conversions (Ieee.v) and variadic functions (`va_args`, `va_arg`).
    Vectors, [[cas]] and atomics, `setjmp`, [[asm_fixed]] and plain
    mode are deferred: a function that uses them is [IOutside], which
    has an address but no body (Transport.v decides).

    ## Items, blocks and instructions

    | Gallina | ir.pl |
    |---|---|
    | `IFunc f` | `func(Name, Linkage, Ret, Params, Blocks)` |
    | `IOutside n t` | a `func` named n outside the core subset, kept as its term t |
    | `IData n lk al items` | `data(Name, Linkage, Align, Items)` |
    | `IAlias n lk t` | `alias(Name, Linkage, Target)` |
    | `Phi d k pairs` | `phi(tmp(D), K, [Pred-Value])` |
    | `Let d k o args` | `let(tmp(D), K, Op, Args)` |
    | `Flight d o args lower` | `flight(tmp(D), Op, Args, Lower)` |
    | `RawStore w off v a` | `raw_store(Width, Off, Value, Addr)` |
    | `RawStorePointer off v a es` | `raw_store_pointer(Off, Value, Addr, Effects)` |
    | `Call r callee args` | `call(Res, Callee, [arg(K, Value)])` |
    | `RawCall r callee args` | `raw_call(Res, Callee, Args)` |
    | `LocalAlloc x size` | `local_alloc(Name, Size)` |
    | `Loc file line` | `loc(File, Line)` | *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term.
Import ListNotations.
Open Scope Z_scope.

(** ## Classes and widths *)

(** As `class(K, Kind, Bits)`: the [[class]] of a value, one letter in
    ir.pl. Besides the integer, pointer and float classes there are the
    two [[proof]] classes of the checked stage, whose values are
    pointers a check has cleared.

    | Class | ir.pl | Value |
    |---|---|---|
    | [W] | `w` | a 32-bit integer |
    | [L] | `l` | a 64-bit integer |
    | [P] | `p` | a pointer: an address with its [[capability]] |
    | [A] | `a` | a proven address, the result of a check |
    | [F] | `f` | a proven function, the result of `check_function` |
    | [Single] | `s` | an IEEE binary32 float, held as its 32-bit pattern |
    | [Double] | `d` | an IEEE binary64 float, held as its 64-bit pattern |
    | [Extended] | `x` | an x87 extended float, held as its 80-bit pattern |

    [Extended] is C's `long double`, never a parameter, result, call
    argument or [[phi]]. *)
Inductive class : Type := W | L | P | A | F | Single | Double | Extended.

(** Equality of classes. *)
Definition class_eqb (k k' : class) : bool :=
  match k, k' with
  | W, W | L, L | P, P | A, A | F, F
  | Single, Single | Double, Double | Extended, Extended => true
  | _, _ => false
  end.

(** As `float_class(K)`: whether the class k is a float class, `s`,
    `d` or `x`. *)
Definition float_class (k : class) : bool :=
  match k with Single | Double | Extended => true | _ => false end.

(** As `int_class(K)`: whether the class k is an integer class, `w` or
    `l`. *)
Definition int_class (k : class) : bool :=
  match k with W | L => true | _ => false end.

(** As `modulus(K, Mod)`: the values of class k are the integers from 0
    up to Mod - 1, a float's being its bit pattern; a [P] value's
    address has the modulus of [L]. The proof classes have none. *)
Definition modulus (k : class) : option Z :=
  match k with
  | W | Single => Some (2 ^ 32)
  | L | P | Double => Some (2 ^ 64)
  | Extended => Some (2 ^ 80)
  | A | F => None
  end.

(** As `class_bits(K, Bits)`: the width in bits of an integer class
    k. *)
Definition class_bits (k : class) : option Z :=
  match k with
  | W => Some 32
  | L => Some 64
  | _ => None
  end.

(** As `half_modulus(K, Half)`: half the [modulus] of an integer class
    k; the values from Half up to Mod - 1 are the negative ones when
    read as signed, in two's complement. *)
Definition half_modulus (k : class) : option Z :=
  match k with
  | W => Some (2 ^ 31)
  | L => Some (2 ^ 63)
  | _ => None
  end.

(** The width of a store or of a data item, what size of value it
    writes: [Wb] and [Wh] are ir.pl's `b` and `h`, a byte and a 16-bit
    halfword, and the others are the classes `w` `l` `p` `s` `d` `x`. *)
Inductive width : Type := Wb | Wh | Ww | Wl | Wp | Ws | Wd | Wx.

(** As `width_bytes(Width, Size)`: the bytes a width w writes; an x87
    extended float takes 10. *)
Definition width_bytes (w : width) : Z :=
  match w with
  | Wb => 1 | Wh => 2 | Ww => 4 | Wl => 8 | Wp => 8
  | Ws => 4 | Wd => 8 | Wx => 10
  end.

(** A narrow integer type, the T of a narrow load and of `ext(T)`:
    ir.pl's `sw` `uw` `sh` `uh` `sb` `ub`, a signed or unsigned word (4
    bytes), halfword (2) or byte (1). *)
Inductive narrow : Type := Sw | Uw | Sh | Uh | Sb | Ub.

(** Whether an integer is read as signed, in two's complement, or as
    unsigned. *)
Inductive signedness : Type := Signed | Unsigned.

(** As `narrow_type(T, Bytes, Signedness)`: the size in bytes and the
    signedness of the narrow type t. *)
Definition narrow_type (t : narrow) : Z * signedness :=
  match t with
  | Sw => (4, Signed) | Uw => (4, Unsigned)
  | Sh => (2, Signed) | Uh => (2, Unsigned)
  | Sb => (1, Signed) | Ub => (1, Unsigned)
  end.

(** The type of a [[raw-access|raw load]]: [LdL] for `l`, [LdS], [LdD]
    and [LdX] for the float classes `s` `d` `x`, or a narrow type. This
    is `load_type/1` without `p`, which [RawLoadPointer] reads
    instead. *)
Inductive load_type : Type := LdL | LdS | LdD | LdX | LdNarrow (t : narrow).

(** ## Ops *)

(** A comparison's Cond: `eq` and `ne` at any numeric class, the signed
    and unsigned orders at `w` and `l`, and `le` `lt` `ge` `gt` `o`
    (ordered) and `uo` (unordered) at a float class. *)
Inductive cond : Type :=
| Eq | Ne | Sle | Slt | Sge | Sgt | Ule | Ult | Uge | Ugt
| Le | Lt | Ge | Gt | Ord | Unord.

(** The [[rights]] an access asks for: to read, or to write, which a
    read-only object refuses. *)
Inductive rights : Type := Read | Write.

(** Equality of rights. *)
Definition rights_eqb (r r' : rights) : bool :=
  match r, r' with Read, Read | Write, Write => true | _, _ => false end.

(** Which end of an object's bounds a [[half_check|half check]] tests
    natively, ir.pl's `upper` or `lower`; an earlier check proves the
    other. *)
Inductive bound : Type := Upper | Lower.

(** One step of the protocol by which a pointer load or store moves an
    address and its capability, as `pointer_memory_effects/2` lists
    them:

    - a heap load reads the [[aux]] word ([AuxRead]), resolves the
      [[lower]] from it ([LowerResolve]), then reads the address
      ([AddressRead]);
    - a heap store makes sure the aux exists ([AuxEnsure]), applies the
      collector's barrier to the stored lower ([LowerBarrier]), reloads
      its destination from a [[root]] ([RootedReload]), then writes
      the lower ([LowerWrite]) before the address ([AddressWrite]);
    - [AtomicRead] and [AtomicWrite] are Fil-C's atomic pointer
      helpers, each a whole protocol. *)
Inductive effect : Type :=
| AuxRead | LowerResolve | AddressRead | AtomicRead
| AuxEnsure | LowerBarrier | RootedReload | LowerWrite | AddressWrite | AtomicWrite.

(** Equality of effects. *)
Definition effect_eqb (e e' : effect) : bool :=
  match e, e' with
  | AuxRead, AuxRead | LowerResolve, LowerResolve | AddressRead, AddressRead
  | AtomicRead, AtomicRead | AuxEnsure, AuxEnsure | LowerBarrier, LowerBarrier
  | RootedReload, RootedReload | LowerWrite, LowerWrite
  | AddressWrite, AddressWrite | AtomicWrite, AtomicWrite => true
  | _, _ => false
  end.

(** Equality of two effect lists, step by step. *)
Definition effects_eqb (es es' : list effect) : bool :=
  (length es =? length es')%nat && forallb (fun p => effect_eqb (fst p) (snd p)) (combine es es').

(** As `pointer_memory_effects(load, Effects)`: the protocol of a heap
    pointer load, one of the two that [evidence_preserving] accepts. *)
Definition load_effects : list effect := [AuxRead; LowerResolve; AddressRead].
(** As `pointer_memory_effects(local_load, Effects)`: the protocol of a
    pointer load from a named local, whose explicit stack aux has no
    atomic box, so there is no lower to resolve. *)
Definition local_load_effects : list effect := [AuxRead; AddressRead].

(** An operation, the Op of a `let` (ir.pl's Ops table): one
    constructor per functor in the core subset, with the functor's
    parameters as its arguments. The arithmetic and conversions come
    first, then the [[alloc]], the checks of the checked stage and
    their [[reuse]] forms, the [[raw-access|raw loads]] and the
    variadic ops. What each reads is [op_arg_classes]. *)
Inductive op : Type :=
| Add | Sub | Mul | Div | Udiv | Rem | Urem | And | Or | Xor
| Sar | Shr | Shl | Neg | Copy | Ptoi | Itop
| Cmp (c : cond) (k : class) (* 1 if two values of class k compare by c, else 0 *)
| Ext (t : narrow) (* the low bytes of a `w`, extended by t *)
(* The float conversions: `ext(s)` and `ext(d)` name their source
   class; `stosi` is `FloatToInt Single Signed`, `dtoui` is
   `FloatToInt Double Unsigned`; `swtof` is `IntToFloat W Signed`, `ultof`
   is `IntToFloat L Unsigned`. *)
| ExtF (k : class) (* widen a float of class k *)
| Truncd | Truncx
| FloatToInt (k : class) (sg : signedness) (* a float of class k to an integer, truncated *)
| IntToFloat (k : class) (sg : signedness) (* an integer of class k to the nearest float *)
| Cast (* the same bits at the other class: `w` and `s`, `l` and `d` *)
| Alloc (align : Z) (* a new zeroed heap object of the `l` size read *)
| Check (lo hi : Z) (r : rights) (align : Z) (* [[check]] of a pointer P: trap unless P may access from P+lo up to P+hi *)
| CheckAhead (lo hi : Z) (r : rights) (align ahi : Z) (* a check whose bytes from ahi up to hi are for a later access: [[check_ahead]] *)
| Renew (lo hi : Z) (r : rights) (align : Z) (* reuse a dominating check's bounds: [[renew]] *)
| RenewHull (lo hi : Z) (r : rights) (align : Z) (* a renew whose bounds two earlier proofs cover: [[renew_hull]] *)
| HalfCheck (b : bound) (lo hi : Z) (r : rights) (align : Z) (* a check that tests only the bound b: [[half_check]] *)
| SpanTest (lo hi : Z) (* 1 if the pointer's object holds the span, else 0: [[span_test]] *)
| RenewIf (lo hi : Z) (r : rights) (align : Z) (* a check whose bounds a passing span test proves: [[renew_if]] *)
| Limit (size : Z) (* an opaque snapshot of the pointer's bounds: [[limit]] *)
| CheckLimit (lo hi : Z) (r : rights) (align : Z) (* a check of the bounds against a limit: [[limit|check_limit]] *)
| CheckLocal (x : name) (off bytes : Z) (r : rights) (align : Z) (* prove an access to the named local x *)
| CheckFunction (* trap unless the pointer is a function's exact address *)
| RawLoad (t : load_type) (off : Z) (* a non-pointer load at the proven address plus off *)
| RawLoadPointer (off : Z) (es : list effect) (* a pointer load at the proven address plus off, by the protocol es *)
(* `va_args` takes a variadic function's entry argument snapshot at a
   byte offset; `va_arg` loads the next argument through a va_list. *)
| VaArgs
| VaArg.

(** ## Values, instructions and jumps *)

(** A value an instruction reads (ir.pl's Values table). *)
Inductive value : Type :=
| Tmp (n : name) (* `tmp(N)`, a [[temporary]], defined once *)
| Const (n : Z) (* `const(N)`, an integer; at a float class, its bit pattern *)
| Global (s : name). (* `global(S)`, the address of the function or data object s *)

(** An argument of a [[flight]]'s address computation: an `l` value, or
    `address(P)`, the address bits of the pointer P. *)
Inductive flight_arg : Type := FValue (v : value) | FAddress (p : value).

(** A flight's Lower, where its capability comes from: `none`, or
    `lower(P)`, exactly the capability of the pointer P. *)
Inductive flight_lower : Type := LowerNone | LowerOf (p : value).

(** A call's Res, where its results go. *)
Inductive call_result : Type :=
| CVoid (* `void`: none *)
| CResult (d : name) (k : class) (* `result(tmp(D), K)`: the temporary d, of class k *)
| CTuple (rs : list (name * class)). (* `tuple([result(tmp(D1), K1), ...])`: a pair of results *)

(** As `arg(K, Value)`: a call's argument, the value v passed at class
    k. *)
Inductive arg : Type := Arg (k : class) (v : value).

(** An instruction of a block, in the core subset; the table at the
    top of the page gives each one's ir.pl term. The raw forms do no
    checking of their own: they read a proof of class [A] or [F]. *)
Inductive inst : Type :=
| Let (d : name) (k : class) (o : op) (args : list value) (* d, of class k, is o of args *)
| Flight (d : name) (o : op) (args : list flight_arg) (lower : flight_lower) (* the pointer d: the address o computes, with the capability lower names *)
| RawStore (w : width) (off : Z) (v a : value) (* store v at the proven address a plus off *)
| RawStorePointer (off : Z) (v a : value) (es : list effect) (* store the pointer v there, by the protocol es *)
| Call (r : call_result) (callee : value) (args : list arg) (* call callee, a symbol or a pointer *)
| RawCall (r : call_result) (callee : value) (args : list arg) (* call the proven function callee, of class [F] *)
| LocalAlloc (x : name) (size : Z) (* declare the named local x, of size zeroed bytes *)
| Loc (file : term) (line : Z). (* a source position; does nothing *)

(** A jump's target: `L`, or `poll(L)`, a [[poll|pollcheck]] on the
    edge before going to L. *)
Inductive target : Type := To (l : name) | Poll (l : name).

(** As `edge_label(T, L)`: the label a target t goes to, polling or
    not. *)
Definition edge_label (t : target) : name := match t with To l | Poll l => l end.

(** The jump that ends a block (ir.pl's Jumps table). *)
Inductive jump : Type :=
| JGoto (t : target) (* `goto(L)` *)
| JBranch (v : value) (t1 t2 : target) (* to t1 if v is nonzero, else to t2 *)
| JRet (v : value) (* `ret(V)`: return v *)
| JRets (vs : list value) (* `rets([V1, V2])`: return a tuple *)
| JRetVoid (* `ret`, from a `void` function *)
| JUnreachable. (* stop the program, a trap instruction *)

(** As `phi(tmp(D), K, [Pred-Value])`: a [[phi]] at the head of a block,
    defining d, of class k, as the value paired with the block control
    came from. *)
Inductive phi : Type := Phi (d : name) (k : class) (pairs : list (name * value)).

(** As `block(Label, Phis, Insts, Jump)`: a [[block]], its phis, then
    its instructions, then the one jump that ends it. *)
Record block : Type := mkBlock {
  b_label : name;
  b_phis : list phi;
  b_insts : list inst;
  b_jump : jump
}.

(** A function's Ret: a class, `void`, or `tuple([K1, K2])`. *)
Inductive ret_type : Type :=
| RClass (k : class)
| RVoid
| RTuple (ks : list class). (* two words, a struct of 9 to 16 bytes *)

(** As `func(Name, Linkage, Ret, Params, Blocks)`: a function. *)
Record func : Type := mkFunc {
  fn_name : name;
  fn_linkage : term; (* `export`, `local` or `weak`, kept as its term *)
  fn_ret : ret_type;
  fn_params : list (class * name); (* each a class and a temporary *)
  fn_blocks : list block (* the entry block first *)
}.

(** As `variadic_func(Func)`: whether the function f takes the entry
    argument snapshot of a variadic function, which it does with a
    `va_args` anywhere in its blocks. *)
Definition variadic_func (f : func) : bool :=
  existsb (fun b => existsb (fun i => match i with
                                      | Let _ P VaArgs _ => true
                                      | _ => false
                                      end) (b_insts b)) (fn_blocks f).

(** ## Data *)

(** A data object's Linkage (ir.pl's Data section). [LExport],
    [LLocal] and [LWeak] are `export`, `local` and `weak`; [LRo] l is
    `ro(L)`, read-only data, and [LTls] l is `tls(L)`, an object each
    thread has its own instance of, both of the inner linkage l. *)
Inductive linkage : Type :=
| LExport | LLocal | LWeak
| LRo (l : term) | LTls (l : term)
| LInit (which prio : term) (* `init(ctor or dtor, Priority)`: a constructor or destructor table entry, not an object *)
| LExternWeak (* `extern(weak)`: a weak declaration of a symbol defined elsewhere, not an object *)
| LOther (t : term). (* any other Linkage term: `valid_module/1` rejects it, so only the validator meets it *)

(** A data Item, a piece of a data object's initial contents.
    `item(l, sym(Name, Off))` is plain mode's, outside the subset;
    `item(p, sym(Name, Off))` is [Sym]. *)
Inductive data_item : Type :=
| Item (w : width) (n : Z) (* `item(W, const(N))`: n at width w *)
| Str (codes : list Z) (* `item(b, str(Chars))`: the bytes themselves *)
| Sym (s : name) (off : Z) (* a pointer to s plus off, with the capability of s *)
| Zero (n : Z) (* `zero(N)`: n zero bytes *)
| ItemOther (t : term). (* any other term, kept as it is: `valid_module/1` rejects it (`data_item_shape/1`), so only the validator meets it *)

(** As `item_size(Item, Size0, Size)`: the bytes a data item takes. *)
Definition item_size (it : data_item) : Z :=
  match it with
  | Item w _ => width_bytes w
  | Str cs => Z.of_nat (length cs)
  | Sym _ _ => 8
  | Zero n => n
  | ItemOther _ => 0
  end.

(** The bytes a list of data items takes, the size of the object they
    make. *)
Definition items_size (its : list data_item) : Z :=
  fold_left (fun s it => s + item_size it) its 0.


(** ## Modules *)

(** An item of a module; the table at the top of the page gives each
    one's ir.pl term. *)
Inductive item : Type :=
| IFunc (f : func) (* a function of the core subset *)
| IOutside (n : name) (t : term) (* a function outside it: an address, no body *)
| IData (n : name) (lk : linkage) (align : Z) (items : list data_item) (* a data object *)
| IAlias (n : name) (lk : term) (target : name). (* a second symbol n for the function or data object target *)

(** A module, as `module(Items)`: its items in order. *)
Definition module := list item.

(** ## Facts about instructions *)

(** As `op_arg_classes(Op, K, filc, Classes)`: the classes at which
    the op o reads its arguments when its result has class k; none
    where o cannot have a result of class k. *)
Definition op_arg_classes (o : op) (k : class) : option (list class) :=
  match o with
  | Add | Sub =>
      (* additive_arg_classes/2 *)
      match k with
      | W => Some [W; W] | L => Some [L; L] | P => Some [P; L]
      | Single => Some [Single; Single] | Double => Some [Double; Double]
      | Extended => Some [Extended; Extended]
      | _ => None
      end
  | Mul | Div | Udiv | Rem | Urem | And | Or | Xor => Some [k; k]
  | Sar | Shr | Shl => Some [k; W]
  | Neg | Copy => Some [k]
  | Ptoi => Some [P]
  | Itop => Some [L]
  | Cmp _ ck => Some [ck; ck]
  | Ext _ => Some [W]
  | ExtF fk => Some [fk]
  | Truncd => Some [Double]
  | Truncx => Some [Extended]
  | FloatToInt fk _ => Some [fk]
  | IntToFloat ik _ => Some [ik]
  | Cast =>
      (* cast_classes/2 *)
      match k with
      | W => Some [Single] | Single => Some [W] | L => Some [Double] | Double => Some [L]
      | _ => None
      end
  | Alloc _ => Some [L]
  | Check _ _ _ _ | CheckAhead _ _ _ _ _ => Some [P]
  | Renew _ _ _ _ => Some [A; P]
  | RenewHull _ _ _ _ => Some [A; A; P]
  | HalfCheck _ _ _ _ _ => Some [A; P]
  | SpanTest _ _ => Some [P]
  | RenewIf _ _ _ _ => Some [P; W]
  | Limit _ => Some [P]
  | CheckLimit _ _ _ _ => Some [P; L]
  | CheckLocal _ _ _ _ _ => Some []
  | CheckFunction => Some [P]
  | RawLoad _ _ => Some [A]
  | RawLoadPointer _ _ => Some [A]
  | VaArgs => Some [L]
  | VaArg => Some [P]
  end.

(** Whether the value v is a symbol's address, a [Global]. *)
Definition is_global (v : value) : bool :=
  match v with Global _ => true | _ => false end.

(** As `evidence_preserving(Inst)`: the instruction i reaches no
    [[poll|safepoint]] and cannot free an object or change its bounds
    or rights, so the [[evidence]] of checks before it still holds
    after it. *)
Definition evidence_preserving (i : inst) : bool :=
  match i with
  | Loc _ _ => true
  | Flight _ _ _ _ => true
  | Let _ A (Check _ _ _ _) _ | Let _ A (CheckAhead _ _ _ _ _) _
  | Let _ A (Renew _ _ _ _) _ | Let _ A (RenewHull _ _ _ _) _
  | Let _ A (HalfCheck _ _ _ _ _) _ | Let _ W (SpanTest _ _) _
  | Let _ A (RenewIf _ _ _ _) _ | Let _ L (Limit _) _
  | Let _ A (CheckLimit _ _ _ _) _ => true
  | Let _ _ (RawLoad _ _) _ => true
  | Let _ P (RawLoadPointer _ es) _ =>
      effects_eqb es load_effects || effects_eqb es local_load_effects
  | RawStore w _ _ _ => match w with Wp => false | _ => true end
  | Let _ _ (Add | Sub | Mul | Div | Udiv | Rem | Urem | And | Or | Xor
             | Sar | Shr | Shl | Neg | Ptoi) _ => true
  | Let _ _ (Cmp _ _) _ => true
  | Let _ _ (Ext _) _ => true
  | Let _ _ (ExtF _ | Truncd | Truncx | FloatToInt _ _ | IntToFloat _ _ | Cast) _ => true
  | Let _ _ Copy args => negb (existsb is_global args)
  | _ => false
  end.

(** As `ahead_transparent(Inst)`: the instruction i may come between a
    [[check_ahead]] and the access whose [[need]] it checks early. It
    is [evidence_preserving], and not a division, whose fault would end
    the program otherwise than a Fil-C [[trap]]. *)
Definition ahead_transparent (i : inst) : bool :=
  evidence_preserving i &&
  match i with
  | Let _ _ (Div | Udiv | Rem | Urem) _ => false
  | _ => true
  end.

(** As `local_objects(Func, Objects)`: the named locals the function f
    declares, each with its size, in instruction order. *)
Definition local_objects (f : func) : list (name * Z) :=
  flat_map (fun b => flat_map (fun i => match i with
                                        | LocalAlloc x size => [(x, size)]
                                        | _ => []
                                        end) (b_insts b))
           (fn_blocks f).

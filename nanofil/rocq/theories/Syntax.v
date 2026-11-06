(** The checked IR's core subset, transcribed from ir.pl: its grammar
    as inductive types, one constructor per IR functor, and the small
    tables of facts the semantics reads.

    The subset is formal.md's: filc mode, the checked stage, the integer
    and pointer classes, `check` and its reuse vocabulary, the `raw_*`
    accesses, `flight`, poll edges, `call`, `raw_call` and `free`, and
    named locals. Floats, x87, vectors, `cas` and atomics, `setjmp`,
    `va_arg`, `asm_fixed` and plain mode are deferred: a function that
    uses them is `IOutside`, which has an address but no body
    (Transport.v decides).

    ## Classes

    | Class | Value |
    |---|---|
    | `W` | `w`, a 32-bit integer |
    | `L` | `l`, a 64-bit integer |
    | `P` | `p`, a pointer: an address with its capability |
    | `A` | `a`, a proven address, the result of a check |
    | `F` | `f`, a proven function, the result of `check_function` |

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
    | `Loc file line` | `loc(File, Line)` |

    A jump target `Poll l` is `poll(L)`: a pollcheck on the edge. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term.
Import ListNotations.
Open Scope Z_scope.

(** ## Classes and widths *)

(** `class(K, Kind, Bits)` for the integer and pointer classes, and the
    proof classes `a` and `f` of the checked stage. *)
Inductive class : Type := W | L | P | A | F.

Definition class_eqb (k k' : class) : bool :=
  match k, k' with
  | W, W | L, L | P, P | A, A | F, F => true
  | _, _ => false
  end.

(** `modulus(K, Mod)`: values of class K are 0..Mod-1; a p value's
    address has the modulus of l. The proof classes have none. *)
Definition modulus (k : class) : option Z :=
  match k with
  | W => Some (2 ^ 32)
  | L | P => Some (2 ^ 64)
  | A | F => None
  end.

(** `class_bits(K, Bits)` for the integer classes. *)
Definition class_bits (k : class) : option Z :=
  match k with
  | W => Some 32
  | L => Some 64
  | _ => None
  end.

(** `half_modulus(K, Half)`: Half..Mod-1 are negative read as signed. *)
Definition half_modulus (k : class) : option Z :=
  match k with
  | W => Some (2 ^ 31)
  | L => Some (2 ^ 63)
  | _ => None
  end.

(** A store's or data item's width: a class, or `b` and `h`. The float
    widths `s`, `d` and `x` occur only in data items here. *)
Inductive width : Type := Wb | Wh | Ww | Wl | Wp | Ws | Wd | Wx.

(** `width_bytes(Width, Size)`. *)
Definition width_bytes (w : width) : Z :=
  match w with
  | Wb => 1 | Wh => 2 | Ww => 4 | Wl => 8 | Wp => 8
  | Ws => 4 | Wd => 8 | Wx => 10
  end.

(** `narrow_type(T, Bytes, Signedness)`. *)
Inductive narrow : Type := Sw | Uw | Sh | Uh | Sb | Ub.

Inductive signedness : Type := Signed | Unsigned.

Definition narrow_type (t : narrow) : Z * signedness :=
  match t with
  | Sw => (4, Signed) | Uw => (4, Unsigned)
  | Sh => (2, Signed) | Uh => (2, Unsigned)
  | Sb => (1, Signed) | Ub => (1, Unsigned)
  end.

(** A raw load's type: `l` or a narrow type (`load_type/1` without `p`,
    which `raw_load_pointer` reads, and without the floats). *)
Inductive load_type : Type := LdL | LdNarrow (t : narrow).

(** ## Ops *)

Inductive cond : Type := Eq | Ne | Sle | Slt | Sge | Sgt | Ule | Ult | Uge | Ugt.

Inductive rights : Type := Read | Write.

Definition rights_eqb (r r' : rights) : bool :=
  match r, r' with Read, Read | Write, Write => true | _, _ => false end.

Inductive bound : Type := Upper | Lower.

(** The steps of a pointer access's protocol (`pointer_memory_effects/2`). *)
Inductive effect : Type :=
| AuxRead | LowerResolve | AddressRead | AtomicRead
| AuxEnsure | LowerBarrier | RootedReload | LowerWrite | AddressWrite | AtomicWrite.

Definition effect_eqb (e e' : effect) : bool :=
  match e, e' with
  | AuxRead, AuxRead | LowerResolve, LowerResolve | AddressRead, AddressRead
  | AtomicRead, AtomicRead | AuxEnsure, AuxEnsure | LowerBarrier, LowerBarrier
  | RootedReload, RootedReload | LowerWrite, LowerWrite
  | AddressWrite, AddressWrite | AtomicWrite, AtomicWrite => true
  | _, _ => false
  end.

Definition effects_eqb (es es' : list effect) : bool :=
  (length es =? length es')%nat && forallb (fun p => effect_eqb (fst p) (snd p)) (combine es es').

(** `pointer_memory_effects(load, _)` and `(local_load, _)`: the
    protocols of a pointer load that `evidence_preserving/1` accepts. *)
Definition load_effects : list effect := [AuxRead; LowerResolve; AddressRead].
Definition local_load_effects : list effect := [AuxRead; AddressRead].

(** The Op of a `let`: one constructor per functor of ir.pl's Ops
    table in the core subset. *)
Inductive op : Type :=
| Add | Sub | Mul | Div | Udiv | Rem | Urem | And | Or | Xor
| Sar | Shr | Shl | Neg | Copy | Ptoi | Itop
| Cmp (c : cond) (k : class)
| Ext (t : narrow)
| Alloc (align : Z)
| Check (lo hi : Z) (r : rights) (align : Z)
| CheckAhead (lo hi : Z) (r : rights) (align ahi : Z)
| Renew (lo hi : Z) (r : rights) (align : Z)
| RenewHull (lo hi : Z) (r : rights) (align : Z)
| HalfCheck (b : bound) (lo hi : Z) (r : rights) (align : Z)
| SpanTest (lo hi : Z)
| RenewIf (lo hi : Z) (r : rights) (align : Z)
| Limit (size : Z)
| CheckLimit (lo hi : Z) (r : rights) (align : Z)
| CheckLocal (x : name) (off bytes : Z) (r : rights) (align : Z)
| CheckFunction
| RawLoad (t : load_type) (off : Z)
| RawLoadPointer (off : Z) (es : list effect).

(** ## Values, instructions and jumps *)

(** An IR value (ir.pl's Values table). *)
Inductive value : Type :=
| Tmp (n : name)
| Const (n : Z)
| Global (s : name).

(** A flight argument: an `l` value or `address(P)`. *)
Inductive flight_arg : Type := FValue (v : value) | FAddress (p : value).

(** A flight's Lower: `none` or `lower(P)`. *)
Inductive flight_lower : Type := LowerNone | LowerOf (p : value).

(** A call's Res: `void`, `result(tmp(D), K)` or `tuple([...])`. *)
Inductive call_result : Type :=
| CVoid
| CResult (d : name) (k : class)
| CTuple (rs : list (name * class)).

(** `arg(K, Value)`. *)
Inductive arg : Type := Arg (k : class) (v : value).

Inductive inst : Type :=
| Let (d : name) (k : class) (o : op) (args : list value)
| Flight (d : name) (o : op) (args : list flight_arg) (lower : flight_lower)
| RawStore (w : width) (off : Z) (v a : value)
| RawStorePointer (off : Z) (v a : value) (es : list effect)
| Call (r : call_result) (callee : value) (args : list arg)
| RawCall (r : call_result) (callee : value) (args : list arg)
| LocalAlloc (x : name) (size : Z)
| Loc (file : term) (line : Z).

(** A jump's target: `L`, or `poll(L)`, a pollcheck on the edge. *)
Inductive target : Type := To (l : name) | Poll (l : name).

(** `edge_label(T, L)`. *)
Definition edge_label (t : target) : name := match t with To l | Poll l => l end.

Inductive jump : Type :=
| JGoto (t : target)
| JBranch (v : value) (t1 t2 : target)
| JRet (v : value)
| JRets (vs : list value)
| JRetVoid
| JUnreachable.

Inductive phi : Type := Phi (d : name) (k : class) (pairs : list (name * value)).

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
| RTuple (ks : list class).

Record func : Type := mkFunc {
  fn_name : name;
  fn_linkage : term;
  fn_ret : ret_type;
  fn_params : list (class * name);
  fn_blocks : list block
}.

(** ## Data *)

(** A data object's Linkage (ir.pl's Data section). *)
Inductive linkage : Type :=
| LExport | LLocal | LWeak
| LRo (l : term) | LTls (l : term)
| LInit (which prio : term)
| LExternWeak.

(** A data Item. `item(l, sym(Name, Off))` is plain mode's, outside the
    subset; `item(p, sym(Name, Off))` is `Sym`. *)
Inductive data_item : Type :=
| Item (w : width) (n : Z)
| Str (codes : list Z)
| Sym (s : name) (off : Z)
| Zero (n : Z).

(** ## Modules *)

Inductive item : Type :=
| IFunc (f : func)
| IOutside (n : name) (t : term)
| IData (n : name) (lk : linkage) (align : Z) (items : list data_item)
| IAlias (n : name) (lk : term) (target : name).

Definition module := list item.

(** ## Facts about instructions *)

(** `op_arg_classes(Op, K, filc, Classes)`: the classes at which Op's
    arguments are read when its result has class K. *)
Definition op_arg_classes (o : op) (k : class) : option (list class) :=
  match o with
  | Add | Sub =>
      (* additive_arg_classes/2 *)
      match k with
      | W => Some [W; W] | L => Some [L; L] | P => Some [P; L]
      | _ => None
      end
  | Mul | Div | Udiv | Rem | Urem | And | Or | Xor => Some [k; k]
  | Sar | Shr | Shl => Some [k; W]
  | Neg | Copy => Some [k]
  | Ptoi => Some [P]
  | Itop => Some [L]
  | Cmp _ ck => Some [ck; ck]
  | Ext _ => Some [W]
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
  end.

Definition is_global (v : value) : bool :=
  match v with Global _ => true | _ => false end.

(** `evidence_preserving(Inst)`: Inst reaches no safepoint and cannot
    free an object or change its bounds or rights. *)
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
  | Let _ _ Copy args => negb (existsb is_global args)
  | _ => false
  end.

(** `ahead_transparent(Inst)`: Inst may come between a `check_ahead`
    and the access whose need it checks early: evidence preserving, and
    not a division, whose fault would end the program otherwise than a
    Fil-C trap. *)
Definition ahead_transparent (i : inst) : bool :=
  evidence_preserving i &&
  match i with
  | Let _ _ (Div | Udiv | Rem | Urem) _ => false
  | _ => true
  end.

(** `local_objects(Func, Objects)`: the named locals a function
    declares, in instruction order. *)
Definition local_objects (f : func) : list (name * Z) :=
  flat_map (fun b => flat_map (fun i => match i with
                                        | LocalAlloc x size => [(x, size)]
                                        | _ => []
                                        end) (b_insts b))
           (fn_blocks f).

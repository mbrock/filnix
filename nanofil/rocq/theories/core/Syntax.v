(** After Nanofil lowers C source code into static single-assignment
    blocks, its safety passes insert explicit capability checks before
    every memory access and function call to produce the
    [[stage|checked IR]]. This module defines the abstract syntax of the
    [[core-subset|core subset]] of that checked IR as inductive types,
    together with the classification tables that the operational
    semantics and the translation [[validator]] share.

    In [[mode|filc mode]], the core subset covers 32-bit and 64-bit
    integers, pointers, IEEE floating-point numbers, capability
    [[check|checks]] and their [[reuse]] forms,
    [[raw-access|raw memory accesses]] including compare-and-exchange,
    [[flight]] instructions, [[poll|poll edges]], function calls, named
    stack locals, and variadic arguments. A compiled [module] is an
    ordered list of top-level functions, global data definitions, and
    symbol aliases, where each function body is a list of basic
    [[block|blocks]] made of entry [[phi]] nodes, sequential
    instructions, and a terminating control-flow jump. Functions that
    use features outside the core subset, such as vector operations or
    inline assembly, receive an address via [IOutside] without decoding
    their bodies. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term.
Import ListNotations.
Open Scope Z_scope.

(** ## Classes and widths

    Every temporary and instruction result in the IR carries a register
    [[class]] that determines its bit width and whether it holds an
    integer, a pointer, a floating-point bit pattern, or a checked
    [[proof]]. Memory instructions also specify a storage [width] or a
    [narrow] integer type when reading or writing fewer than eight
    bytes. *)

(** Every value in the checked IR has a register [class]. The classes
    [W] and [L] hold 32-bit and 64-bit integers, [P] holds a pointer
    with its [[capability]], [A] and [F] hold checked address and
    function [[proof|proofs]], and [Single], [Double], and [Extended]
    hold 32-bit, 64-bit, and 80-bit IEEE floating-point bit patterns.
    The 80-bit [Extended] class represents C's `c: long double` inside
    expressions, and never appears as a function parameter, return
    value, call argument, or [[phi]] node. *)
Inductive class : Type := W | L | P | A | F | Single | Double | Extended.

(** The function [class_eqb] tests whether two IR classes are identical. *)
Definition class_eqb (k k' : class) : bool :=
  match k, k' with
  | W, W | L, L | P, P | A, A | F, F
  | Single, Single | Double, Double | Extended, Extended => true
  | _, _ => false
  end.

(** The predicate [float_class] returns `true` when a class is one of
    the three floating-point classes [Single], [Double], or [Extended]. *)
Definition float_class (k : class) : bool :=
  match k with Single | Double | Extended => true | _ => false end.

(** The predicate [int_class] returns `true` when a class is one of the
    two integer classes [W] or [L]. *)
Definition int_class (k : class) : bool :=
  match k with W | L => true | _ => false end.

(** For any numeric or pointer class, [modulus] returns the power-of-two
    bound on its unsigned bit pattern, or `None` for the proof classes
    [A] and [F]. *)
Definition modulus (k : class) : option Z :=
  match k with
  | W | Single => Some (2 ^ 32)
  | L | P | Double => Some (2 ^ 64)
  | Extended => Some (2 ^ 80)
  | A | F => None
  end.

(** For an integer class, [class_bits] returns its bit width, which is
    32 for [W] and 64 for [L], or `None` for non-integer classes. *)
Definition class_bits (k : class) : option Z :=
  match k with
  | W => Some 32
  | L => Some 64
  | _ => None
  end.

(** For an integer class, [half_modulus] returns the sign-bit threshold
    at which unsigned values begin to represent negative numbers in
    two's complement. *)
Definition half_modulus (k : class) : option Z :=
  match k with
  | W => Some (2 ^ 31)
  | L => Some (2 ^ 63)
  | _ => None
  end.

(** A storage [width] specifies how many bytes a memory store or static
    data initializer writes, ranging from a single byte [Wb] or 16-bit
    halfword [Wh] up to a full integer, pointer, or floating-point
    value. *)
Inductive width : Type := Wb | Wh | Ww | Wl | Wp | Ws | Wd | Wx.

(** Given a storage [width], [width_bytes] returns the number of bytes
    written to memory, including 10 bytes for an x87 extended float
    [Wx]. *)
Definition width_bytes (w : width) : Z :=
  match w with
  | Wb => 1 | Wh => 2 | Ww => 4 | Wl => 8 | Wp => 8
  | Ws => 4 | Wd => 8 | Wx => 10
  end.

(** A [narrow] integer type specifies the byte width and signedness of a
    sub-word memory load or integer extension, covering signed and
    unsigned 4-byte words, 2-byte halfwords, and single bytes. *)
Inductive narrow : Type := Sw | Uw | Sh | Uh | Sb | Ub.

(** A [signedness] tag records whether an integer operation interprets
    bit patterns as two's-complement [Signed] numbers or [Unsigned]
    numbers. *)
Inductive signedness : Type := Signed | Unsigned.

(** Given a [narrow] integer type, [narrow_type] returns its size in
    bytes paired with its [signedness]. *)
Definition narrow_type (t : narrow) : Z * signedness :=
  match t with
  | Sw => (4, Signed) | Uw => (4, Unsigned)
  | Sh => (2, Signed) | Uh => (2, Unsigned)
  | Sb => (1, Signed) | Ub => (1, Unsigned)
  end.

(** A [load_type] describes the representation read by a non-pointer
    [[raw-access|raw load]], which may be a 64-bit integer, a
    floating-point value, or a narrow integer. Pointer loads use
    [RawLoadPointer] instead so they can specify their capability-reading
    protocol. *)
Inductive load_type : Type := LdL | LdS | LdD | LdX | LdNarrow (t : narrow).

(** A [cas_type] specifies the width and kind of value that a raw
    [[cas|compare-and-exchange]] compares and writes: a 64-bit integer
    [CasL], a pointer [CasP], or a narrow integer [CasNarrow]. *)
Inductive cas_type : Type := CasL | CasP | CasNarrow (t : narrow).

(** Given a [cas_type], [cas_bytes] returns the number of bytes that the
    compare-and-exchange accesses, which is also its required address
    alignment. *)
Definition cas_bytes (t : cas_type) : Z :=
  match t with
  | CasL | CasP => 8
  | CasNarrow n => fst (narrow_type n)
  end.

(** ## Ops

    An operation in a [Let] instruction computes an arithmetic result,
    allocates an object, performs or reuses a capability check, or
    executes a raw load or compare-and-exchange. This section defines
    the operation codes and the auxiliary types that describe comparison
    conditions, access rights, bounds, and pointer memory protocols. *)

(** A [cond] specifies the relational test performed by a comparison
    operation: equality and inequality on any numeric class, signed and
    unsigned orderings on integers, and ordered or unordered comparisons
    on floating-point numbers. *)
Inductive cond : Type :=
| Eq | Ne | Sle | Slt | Sge | Sgt | Ule | Ult | Uge | Ugt
| Le | Lt | Ge | Gt | Ord | Unord.

(** The [rights] type specifies whether a memory check requests [Read]
    access or [Write] access, which a read-only capability rejects. *)
Inductive rights : Type := Read | Write.

(** The function [rights_eqb] tests whether two access-rights tags are
    equal. *)
Definition rights_eqb (r r' : rights) : bool :=
  match r, r' with Read, Read | Write, Write => true | _, _ => false end.

(** A [bound] tag selects which end of an object's range a
    [[half_check|half check]] tests at run time—either the [Upper] bound
    or the [Lower] bound—when an earlier check already established the
    other end. *)
Inductive bound : Type := Upper | Lower.

(** In Fil-C, loading or storing a pointer in memory touches both the
    8-byte primary address and the capability slot in [[aux]]. An
    [effect] names one atomic step of that multi-step protocol: reading
    or ensuring the aux slot, resolving or writing the [[lower]] bound,
    applying the garbage collector's write barrier, reloading from a
    [[root]], reading or writing the primary address, or calling an
    atomic helper. *)
Inductive effect : Type :=
| AuxRead | LowerResolve | AddressRead | AtomicRead
| AuxEnsure | LowerBarrier | RootedReload | LowerWrite | AddressWrite | AtomicWrite.

(** The function [effect_eqb] tests whether two pointer-protocol steps
    are identical. *)
Definition effect_eqb (e e' : effect) : bool :=
  match e, e' with
  | AuxRead, AuxRead | LowerResolve, LowerResolve | AddressRead, AddressRead
  | AtomicRead, AtomicRead | AuxEnsure, AuxEnsure | LowerBarrier, LowerBarrier
  | RootedReload, RootedReload | LowerWrite, LowerWrite
  | AddressWrite, AddressWrite | AtomicWrite, AtomicWrite => true
  | _, _ => false
  end.

(** The function [effects_eqb] tests whether two pointer-protocol effect
    lists have the same length and matching steps at every position. *)
Definition effects_eqb (es es' : list effect) : bool :=
  (length es =? length es')%nat && forallb (fun p => effect_eqb (fst p) (snd p)) (combine es es').

(** A standard heap pointer load runs the three-step protocol
    [load_effects], which reads the [[aux]] slot, resolves the [[lower]]
    capability, and reads the 8-byte address. A pointer load from a
    named stack local runs the shorter protocol [local_load_effects],
    which reads the stack local's aux capability and 8-byte address
    directly. *)
Definition load_effects : list effect := [AuxRead; LowerResolve; AddressRead].
Definition local_load_effects : list effect := [AuxRead; AddressRead].

(** A [setjmp_kind] distinguishes the three C returns-twice functions
    `c: setjmp`, `c: _setjmp`, and `c: sigsetjmp`. *)
Inductive setjmp_kind : Type := SjSetjmp | SjUnderscore | SjSig.

(** An [op] is the operation performed by a [Let] instruction in the
    core subset. It includes integer and floating-point arithmetic and
    conversions, heap [[alloc|allocation]], capability [[check|checks]]
    and their [[reuse]] forms, [[raw-access|raw loads]] and raw [[cas]],
    variadic argument operations, and `c: setjmp`. The function
    [op_arg_classes] specifies the argument classes that each operation
    expects. *)
Inductive op : Type :=
| Add | Sub | Mul | Div | Udiv | Rem | Urem | And | Or | Xor
| Sar | Shr | Shl | Neg | Copy | Ptoi | Itop
| Select (* chooses the second argument when the first is nonzero, and the third when it is zero *)
| Cmp (c : cond) (k : class) (* returns 1 when two values of class k satisfy condition c, and 0 otherwise *)
| Ext (t : narrow) (* sign- or zero-extends the low bytes of a 32-bit word according to t *)
(* Floating-point conversions name their source or target format and
   signedness explicitly. *)
| ExtF (k : class) (* widens a floating-point value from class k to a wider format *)
| Truncd | Truncx
| FloatToInt (k : class) (sg : signedness) (* truncates a floating-point value of class k toward zero as a signed or unsigned integer *)
| IntToFloat (k : class) (sg : signedness) (* converts a signed or unsigned integer of class k to the nearest floating-point value *)
| Cast (* reinterprets the bit pattern between 32-bit int/float or 64-bit int/double *)
| Sqrt (* computes the IEEE square root of a floating-point value, rounded to nearest *)
| Alloc (align : Z) (* allocates a new zeroed heap object of the given alignment and size *)
| Check (lo hi : Z) (r : rights) (align : Z) (* [[check]] that a pointer can access offsets lo through hi with rights r and alignment align *)
| CheckAhead (lo hi : Z) (r : rights) (align ahi : Z) (* [[check_ahead]] that checks lo..ahi for the current access and ahi..hi for a later access *)
| Renew (lo hi : Z) (r : rights) (align : Z) (* [[renew]] that reuses a dominating check's bounds *)
| RenewHull (lo hi : Z) (r : rights) (align : Z) (* [[renew_hull]] whose span lies between two earlier checked spans *)
| HalfCheck (b : bound) (lo hi : Z) (r : rights) (align : Z) (* [[half_check]] that tests only bound b at run time *)
| SpanTest (lo hi : Z) (* [[span_test]] that returns 1 if the pointer's object covers lo..hi, and 0 otherwise *)
| RenewIf (lo hi : Z) (r : rights) (align : Z) (* [[renew_if]] guarded by a passing span test *)
| Limit (size : Z) (* [[limit]] that captures an opaque snapshot of a pointer's bounds for accesses of size bytes *)
| CheckLimit (lo hi : Z) (r : rights) (align : Z) (* [[limit|check_limit]] that checks an access against a captured limit *)
| CheckLocal (x : name) (off bytes : Z) (r : rights) (align : Z) (* proves an in-bounds access to the named stack local x *)
| CheckFunction (* traps unless the pointer is the exact entry address of a function *)
| RawLoad (t : load_type) (off : Z) (* loads a non-pointer value of type t from a proven address plus off *)
| RawLoadPointer (off : Z) (es : list effect) (* loads a pointer from a proven address plus off using protocol es *)
| RawCas (t : cas_type) (off : Z) (* executes a [[cas]] of type t at a proven address plus off *)
(* Variadic operations snapshot the entry arguments or read the next
   argument from a va_list cursor. *)
| VaArgs
| VaArg
(* A setjmp operation records the syntax of a returns-twice call so the
   validator can inspect functions that mention it. *)
| Setjmp (kind : setjmp_kind).

(** ## Values, instructions and jumps

    Inside a basic block, instructions read [value] operands, compute
    new temporaries or perform memory stores and calls as [inst] steps,
    and finish with a [jump] terminator that transfers control to the
    next block or returns from the function. This section defines those
    instruction-level syntax trees and the structure of blocks and
    functions. *)

(** An instruction operand [value] is a [[temporary]] name, an integer
    or floating-point bit-pattern constant, or the address of a module
    symbol. *)
Inductive value : Type :=
| Tmp (n : name) (* a [[temporary]] variable, which is assigned at most once in SSA form *)
| Const (n : Z) (* an integer constant, or the bit pattern of a floating-point constant *)
| Global (s : name). (* the pointer constant for a function or global data object *)

(** A [flight_arg] is an operand to the address calculation of a
    [[flight]] instruction: either a 64-bit integer [FValue] or the
    extracted address bits [FAddress] of a pointer. *)
Inductive flight_arg : Type := FValue (v : value) | FAddress (p : value).

(** A [flight_lower] specifies where a [[flight]] instruction obtains
    the [[capability]] for the pointer it builds: either [LowerNone] for
    a capability-free pointer, or [LowerOf] to copy the capability of an
    existing pointer operand. *)
Inductive flight_lower : Type := LowerNone | LowerOf (p : value).

(** A [call_result] specifies where a function call places its return
    value: nowhere for a void call [CVoid], into a single typed
    temporary [CResult], or into a list of temporaries [CTuple] for a
    multi-word return. *)
Inductive call_result : Type :=
| CVoid (* a call with no return value *)
| CResult (d : name) (k : class) (* a single return value written to temporary d at class k *)
| CTuple (rs : list (name * class)). (* a multi-word return value written to a list of typed temporaries *)

(** An [arg] pairs a call argument [value] with the register [class] at
    which the caller passes it. *)
Inductive arg : Type := Arg (k : class) (v : value).

(** An [inst] is a single non-terminating instruction inside a basic
    [[block]]. The raw memory and call forms [RawStore],
    [RawStorePointer], and [RawCall] perform no capability check of
    their own; instead, they consume a [[proof]] temporary of class [A]
    or [F] produced by an earlier check. *)
Inductive inst : Type :=
| Let (d : name) (k : class) (o : op) (args : list value) (* evaluates operation o on args and binds temporary d at class k *)
| Flight (d : name) (o : op) (args : list flight_arg) (lower : flight_lower) (* builds pointer d from the address computed by o and the capability selected by lower *)
| RawStore (w : width) (off : Z) (v a : value) (* stores non-pointer value v of width w at proven address a plus off *)
| RawStorePointer (off : Z) (v a : value) (es : list effect) (* stores pointer v at proven address a plus off using protocol es *)
| Call (r : call_result) (callee : value) (args : list arg) (* checks and calls callee with args, storing the result in r *)
| RawCall (r : call_result) (callee : value) (args : list arg) (* calls proven function callee of class F with args *)
| LocalAlloc (x : name) (size : Z) (* allocates a zeroed stack local x of size bytes for the current invocation *)
| Loc (file : term) (line : Z) (* records a source file and line number without changing execution state *)
| Touch (q : name). (* consumes the proof temporary q from a preceding vector check without accessing memory *)

(** A jump [target] names the destination block label of a control-flow
    edge, either as a direct jump [To] or with a garbage-collection
    [[poll|pollcheck]] on the edge via [Poll]. *)
Inductive target : Type := To (l : name) | Poll (l : name).

(** Given a jump [target], [edge_label] extracts the destination block
    label regardless of whether the edge performs a pollcheck. *)
Definition edge_label (t : target) : name := match t with To l | Poll l => l end.

(** A [jump] is the control-flow terminator that ends a basic [[block]]:
    an unconditional jump, a conditional branch, a function return, or
    an unreachable trap. *)
Inductive jump : Type :=
| JGoto (t : target) (* jumps unconditionally to target t *)
| JBranch (v : value) (t1 t2 : target) (* jumps to t1 when v is nonzero, and to t2 when v is zero *)
| JRet (v : value) (* returns a single value v from the current function *)
| JRets (vs : list value) (* returns a tuple of values vs from the current function *)
| JRetVoid (* returns from a void function *)
| JUnreachable. (* traps immediately if control reaches this point *)

(** A [phi] node sits at the entry of a basic [[block]] and binds a
    temporary of a given class to the operand paired with whichever
    predecessor block control arrived from. *)
Inductive phi : Type := Phi (d : name) (k : class) (pairs : list (name * value)).

(** A [block] is a labeled basic block consisting of its entry [[phi]]
    nodes, its sequential body instructions, and its terminating [jump]. *)
Record block : Type := mkBlock {
  b_label : name;
  b_phis : list phi;
  b_insts : list inst;
  b_jump : jump
}.

(** A [ret_type] specifies the return signature of a function: a single
    value class [RClass], no return value [RVoid], or a multi-word
    tuple of classes [RTuple]. *)
Inductive ret_type : Type :=
| RClass (k : class)
| RVoid
| RTuple (ks : list class). (* a two-word struct return of 9 to 16 bytes *)

(** A [func] record represents a compiled function in the core subset,
    giving its symbol name, linkage term, return signature, typed
    parameter list, and basic blocks with the entry block first. *)
Record func : Type := mkFunc {
  fn_name : name;
  fn_linkage : term; (* linkage atom such as export, local, or weak *)
  fn_ret : ret_type;
  fn_params : list (class * name); (* parameter classes paired with their temporary names *)
  fn_blocks : list block (* basic blocks of the function, starting with the entry block *)
}.

(** A function satisfies [variadic_func] when any block in its body
    contains a [VaArgs] instruction, which tells call setup to allocate
    a snapshot of the extra call arguments on entry. *)
Definition variadic_func (f : func) : bool :=
  existsb (fun b => existsb (fun i => match i with
                                      | Let _ P VaArgs _ => true
                                      | _ => false
                                      end) (b_insts b)) (fn_blocks f).

(** ## Data

    Besides functions, a compiled module can declare global and
    thread-local data objects initialized with constants, byte strings,
    symbol pointers, or zero padding. This section defines the linkage
    kinds and initializer items for static data, along with their byte
    size calculations. *)

(** A [linkage] tag describes the visibility and storage kind of a
    global data declaration. Exported, module-local, and weak writable
    objects use [LExport], [LLocal], and [LWeak]; read-only and
    thread-local objects wrap an inner linkage in [LRo] or [LTls];
    constructor/destructor entries and external weak declarations use
    [LInit] and [LExternWeak]; and unrecognized linkage terms use
    [LOther] so the validator can reject them. *)
Inductive linkage : Type :=
| LExport | LLocal | LWeak
| LRo (l : term) | LTls (l : term)
| LInit (which prio : term) (* a constructor or destructor table entry rather than a data object *)
| LExternWeak (* a weak declaration of a symbol defined elsewhere *)
| LOther (t : term). (* an unrecognized linkage term that module validation rejects *)

(** A [data_item] represents one piece of a global data object's static
    initializer: a fixed-width integer constant, a raw byte string, an
    8-byte symbol pointer with an offset, a run of zero bytes, or an
    unrecognized term that module validation rejects. *)
Inductive data_item : Type :=
| Item (w : width) (n : Z) (* an integer constant n written at storage width w *)
| Str (codes : list Z) (* a sequence of literal byte values *)
| Sym (s : name) (off : Z) (* a pointer to symbol s plus byte offset off, carrying the capability of s *)
| Zero (n : Z) (* a span of n zero bytes *)
| ItemOther (t : term). (* an unrecognized initializer term that module validation rejects *)

(** Given a single [data_item], [item_size] returns the number of bytes
    it occupies in a static data object, and [items_size] sums those
    byte counts across a list of initializer items. *)
Definition item_size (it : data_item) : Z :=
  match it with
  | Item w _ => width_bytes w
  | Str cs => Z.of_nat (length cs)
  | Sym _ _ => 8
  | Zero n => n
  | ItemOther _ => 0
  end.

Definition items_size (its : list data_item) : Z :=
  fold_left (fun s it => s + item_size it) its 0.


(** ## Modules

    A compiled translation unit is a sequence of top-level function,
    data, and alias declarations. This section packages those top-level
    declarations into the [item] and [module] types. *)

(** A top-level [item] in a module is a function in the core subset, a
    function outside the core subset kept as its raw term, a global data
    object, or a symbol alias. *)
Inductive item : Type :=
| IFunc (f : func) (* a function whose body is in the core subset *)
| IOutside (n : name) (t : term) (* a function outside the core subset, given an address but no decoded body *)
| IData (n : name) (lk : linkage) (align : Z) (items : list data_item) (* a global or thread-local data object *)
| IAlias (n : name) (lk : term) (target : name). (* an alias symbol n that resolves to the same pointer as target *)

(** A [module] is the ordered list of top-level items that make up a
    compiled translation unit. *)
Definition module := list item.

(** ## Facts about instructions

    Both the operational semantics and the translation [[validator]]
    need to know which operand classes an operation expects, which
    instructions preserve prior check [[evidence]], and which local
    stack objects a function allocates. This section defines those
    shared syntactic queries over instructions and functions. *)

(** Given an operation and its result class, [op_arg_classes] returns
    the list of register classes at which the operation reads its
    arguments in [[mode|filc mode]], or `None` when the operation cannot
    produce a result of that class. *)
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
  | Select => Some [W; k; k]
  | Ptoi => Some [P]
  | Itop => Some [L]
  | Cmp _ ck => Some [ck; ck]
  | Ext _ => Some [W]
  | ExtF fk => Some [fk]
  | Truncd => Some [Double]
  | Truncx => Some [Extended]
  | FloatToInt fk _ => Some [fk]
  | IntToFloat ik _ => Some [ik]
  | Sqrt => Some [k] (* kind_arg_classes(float_convert, sqrt, K, _, [K]) *)
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
  | RawCas _ _ => Some [A; k; k] (* kind_arg_classes(raw_cas, _, K, filc, [a, K, K]) *)
  | VaArgs => Some [L]
  | VaArg => Some [P]
  | Setjmp _ => match k with W => Some [P; W] | _ => None end (* kind_arg_classes(setjmp, _, w, filc, [p, w]) *)
  end.

(** The predicate [is_global] returns `true` when an operand [value] is
    a [Global] symbol reference. *)
Definition is_global (v : value) : bool :=
  match v with Global _ => true | _ => false end.

(** An instruction satisfies [evidence_preserving] when it cannot hit a
    garbage-collection [[poll|safepoint]] and cannot free any object or
    alter object bounds or access rights. Across any such instruction,
    the [[validator]] can safely keep all check [[evidence]] established
    earlier in the block. *)
Definition evidence_preserving (i : inst) : bool :=
  match i with
  | Loc _ _ => true
  | Touch _ => true
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
  | Let _ _ (ExtF _ | Truncd | Truncx | FloatToInt _ _ | IntToFloat _ _ | Cast | Sqrt) _ => true
  | Let _ _ Copy args => negb (existsb is_global args)
  | _ => false
  end.

(** An instruction satisfies [ahead_transparent] when it can safely
    appear between a [[check_ahead]] instruction and the later memory
    access whose [[need]] that check verified early. Every
    [[ahead_transparent|ahead-transparent]] instruction preserves check
    evidence and excludes integer divisions, which on hardware could
    fault before control reaches the checked access. *)
Definition ahead_transparent (i : inst) : bool :=
  evidence_preserving i &&
  match i with
  | Let _ _ (Div | Udiv | Rem | Urem) _ => false
  | _ => true
  end.

(** A function satisfies [setjmp_func] when any block in its body
    contains a [Setjmp] instruction. Because a second return from
    `c: setjmp` transfers control along an edge that is invisible in the
    block graph, the [[validator]] refuses optimizations that rely on
    ordinary dominance in such functions. *)
Definition setjmp_func (f : func) : bool :=
  existsb (fun b => existsb (fun i => match i with
                                      | Let _ _ (Setjmp _) _ => true
                                      | _ => false
                                      end) (b_insts b))
          (fn_blocks f).

(** Given a function, [local_objects] collects all named stack locals
    declared by [LocalAlloc] instructions across its blocks, paired with
    their byte sizes in instruction order. *)
Definition local_objects (f : func) : list (name * Z) :=
  flat_map (fun b => flat_map (fun i => match i with
                                        | LocalAlloc x size => [(x, size)]
                                        | _ => []
                                        end) (b_insts b))
           (fn_blocks f).

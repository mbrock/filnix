(** In the checked IR, every [Let] instruction and memory store
    evaluates an operation on run-time [word] values and the current
    memory state [mem]. This module defines integer and pointer
    arithmetic, capability [[check|checks]] and their [[reuse]] forms,
    [[raw-access|raw memory loads and stores]], compare-and-exchange
    ([[cas]]), variadic argument extraction, and IEEE floating-point
    operations.

    Integer values of class [W] or [L] are unsigned integers bounded by
    the modulus of their class, and signed operations interpret those
    bit patterns in two's complement. In Fil-C, integer division by zero
    returns 0 and dividing the most negative signed integer by -1 wraps
    back to the most negative integer, so integer arithmetic never
    causes a hardware fault or undefined behavior.

    The top-level function [op_res] evaluates any operation in the core
    subset. Most operations return an immediate partial result and an
    updated memory state, while [Alloc] returns an [OpAlloc] request
    because heap [[alloc|allocation]] depends on the [[fresh]] base
    address chosen by the runtime. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Ieee Syntax Values Memory.
Import ListNotations.
Open Scope Z_scope.

(** The notation `let* x := e in b` binds the value inside an `option`
    result and short-circuits to `None` when the step fails. *)
Notation "'let*' x ':=' e 'in' b" :=
  (match e with Some x => b | None => None end)
  (at level 200, x name, e at level 100, b at level 200).

(** ## Integers

    Integer temporaries hold unsigned bit patterns of 32 or 64 bits,
    while signed comparisons, shifts, extensions, and divisions
    interpret those bit patterns in two's complement. This section
    defines two's-complement conversion, integer comparisons, shift
    counts, total divisions, and the arithmetic evaluators [alu] and
    [additive_res]. *)

(** Given a power-of-two modulus and its half-modulus sign threshold,
    [sign_extension] converts an unsigned integer bit pattern into its
    signed two's-complement value. *)
Definition sign_extension (m h u : Z) : Z :=
  let l := u mod m in if h <=? l then l - m else l.

(** For an integer class, [signed] reads an unsigned bit pattern as a
    two's-complement signed integer, or returns `None` for non-integer
    classes. *)
Definition signed (k : class) (u : Z) : option Z :=
  let* m := modulus k in
  let* h := half_modulus k in
  Some (sign_extension m h u).

(** Given a [narrow] integer type and an integer word, [extension]
    extracts the low 1, 2, or 4 bytes and sign-extends or zero-extends
    them according to the narrow type. *)
Definition extension (t : narrow) (x : Z) : Z :=
  match t with
  | Sb => sign_extension 256 128 x
  | Ub => x mod 256
  | Sh => sign_extension 65536 32768 x
  | Uh => x mod 65536
  | Sw => sign_extension (2 ^ 32) (2 ^ 31) x
  | Uw => x mod 2 ^ 32
  end.

(** Given a comparison condition and an integer class, [cond_bit]
    compares two integer bit patterns and returns `Some 1` when the
    relation holds, `Some 0` when it fails, or `None` for
    floating-point conditions. *)
Definition cond_bit (c : cond) (k : class) (x y : Z) : option Z :=
  let bit (b : bool) := Some (if b then 1 else 0) in
  match c with
  | Eq => bit (x =? y)
  | Ne => bit (negb (x =? y))
  | Ult => bit (x <? y)
  | Ule => bit (x <=? y)
  | Ugt => bit (y <? x)
  | Uge => bit (y <=? x)
  | Slt => let* sx := signed k x in let* sy := signed k y in bit (sx <? sy)
  | Sle => let* sx := signed k x in let* sy := signed k y in bit (sx <=? sy)
  | Sgt => let* sx := signed k x in let* sy := signed k y in bit (sy <? sx)
  | Sge => let* sx := signed k x in let* sy := signed k y in bit (sy <=? sx)
  | Le | Lt | Ge | Gt | Ord | Unord => None
  end.

(** Given an integer class and a shift count, [shift_factor] reduces
    the shift count modulo the bit width of the class and returns the
    corresponding power of two. *)
Definition shift_factor (k : class) (y : Z) : option Z :=
  let* bits := class_bits k in
  Some (2 ^ (y mod bits)).

(** Given an unsigned division or remainder operator,
    [unsigned_division] returns 0 when the divisor is 0 and otherwise
    applies the operator to the dividend and divisor. *)
Definition unsigned_division (f : Z -> Z -> Z) (x y : Z) : Z :=
  if y =? 0 then 0 else f x y.

(** Given a signed quotient or remainder operator and an integer class,
    [signed_division] converts both operands to signed integers, returns
    0 when the divisor is 0, and reduces the result modulo the class
    modulus. Because signed division truncates toward zero and wraps
    modulo the class width, dividing the minimum signed integer by -1
    yields the minimum signed integer again. *)
Definition signed_division (f : Z -> Z -> Z) (k : class) (x y : Z) : option Z :=
  let* sx := signed k x in
  let* sy := signed k y in
  let* m := modulus k in
  Some (if sy =? 0 then 0 else f sx sy mod m).

(** Given an operation, a result class, and a list of operand words,
    [alu] evaluates integer arithmetic, bitwise logic, shifts, narrow
    extensions, integer comparisons, and integer-pointer casts. Integer
    results wrap modulo the class [modulus], while pointer addition and
    subtraction are handled by [additive_res]. *)
Definition alu (o : op) (k : class) (xs : list word) : option word :=
  match o, xs with
  | Ptoi, [WPtr p] => Some (WInt (ptr_addr p))
  | Itop, [WInt x] => Some (WPtr (mkPtr x CNone))
  | Add, [WInt x; WInt y] => let* m := modulus k in Some (WInt ((x + y) mod m))
  | Sub, [WInt x; WInt y] => let* m := modulus k in Some (WInt ((x - y) mod m))
  | Mul, [WInt x; WInt y] => let* m := modulus k in Some (WInt ((x * y) mod m))
  | Neg, [WInt x] => let* m := modulus k in Some (WInt ((- x) mod m))
  | Copy, [x] => Some x
  | Select, [WInt c; WInt x; WInt y] => Some (WInt (if c =? 0 then y else x))
  | And, [WInt x; WInt y] => Some (WInt (Z.land x y))
  | Or, [WInt x; WInt y] => Some (WInt (Z.lor x y))
  | Xor, [WInt x; WInt y] => Some (WInt (Z.lxor x y))
  | Udiv, [WInt x; WInt y] => Some (WInt (unsigned_division Z.div x y))
  | Urem, [WInt x; WInt y] => Some (WInt (unsigned_division Z.modulo x y))
  | Div, [WInt x; WInt y] => let* r := signed_division Z.quot k x y in Some (WInt r)
  | Rem, [WInt x; WInt y] => let* r := signed_division Z.rem k x y in Some (WInt r)
  | Shl, [WInt x; WInt y] =>
      let* p := shift_factor k y in let* m := modulus k in Some (WInt ((x * p) mod m))
  | Shr, [WInt x; WInt y] =>
      let* p := shift_factor k y in Some (WInt (x / p))
  | Sar, [WInt x; WInt y] =>
      let* p := shift_factor k y in let* sx := signed k x in
      let* m := modulus k in Some (WInt ((sx / p) mod m))
  | Ext t, [WInt x] => let* m := modulus k in Some (WInt (extension t x mod m))
  | Cmp c ck, [WInt x; WInt y] => let* b := cond_bit c ck x y in Some (WInt b)
  | _, _ => None
  end.

(** The function [additive_res] evaluates addition and subtraction at a
    given result class. At pointer class [P], adding or subtracting a
    64-bit integer offset wraps the pointer's address modulo `2 ^ 64`
    while keeping its [[capability]] intact; at integer classes [W] and
    [L], it delegates to [alu]. *)
Definition additive_res (k : class) (o : op) (xs : list word) : option word :=
  match k, o, xs with
  | P, Add, [WPtr p; WInt x] =>
      Some (WPtr (mkPtr ((ptr_addr p + x) mod 2 ^ 64) (ptr_cap p)))
  | P, Sub, [WPtr p; WInt x] =>
      Some (WPtr (mkPtr ((ptr_addr p - x) mod 2 ^ 64) (ptr_cap p)))
  | (W | L), _, _ => alu o k xs
  | _, _, _ => None
  end.

(** ## Checks

    Before a program reads or writes memory, it runs a capability
    [[check]] or one of its [[reuse]] forms to verify that the pointer's
    capability covers the accessed byte span. This section maps the
    outcome of the underlying access check to the result of a full
    check, a raw access, a renewed check, or a [[half_check|half check]]. *)

(** Given the result of an access check and the checked pointer word,
    [checked_res] returns the pointer word as a proven value when the
    check succeeds, and propagates any trap or unchecked fault. *)
Definition checked_res (r : res unit) (p : word) : res word :=
  match r with
  | RVal _ => RVal p
  | RTrap why => RTrap why
  | RUnchecked why => RUnchecked why
  end.

(** A [[raw-access|raw access]] assumes that an earlier check already
    verified its capability and bounds, so it performs no run-time trap
    check of its own. If the underlying access check would have trapped,
    [raw_res] turns that trap into an [[unchecked]] fault. *)
Definition raw_res {X : Type} (r : res X) : res X :=
  match r with
  | RTrap why => RUnchecked why
  | _ => r
  end.

(** When a [[renew]] operation reuses the bounds of a dominating check
    on a pointer, it still traps at run time if the target object has
    been freed or if a write targets a read-only object. Any other
    access-check failure means the dominating check's span did not
    actually cover the renewed access, so [renew_res] reports an
    [[unchecked]] [Span] fault. *)
Definition renew_res (r : res unit) (p : ptr) (m : mem) : option (res word) :=
  match r with
  | RVal _ => Some (RVal (WPtr p))
  | RTrap Readonly => Some (RTrap Readonly)
  | RTrap _ =>
      match ptr_cap p with
      | Obj base | Ro base =>
          let* reg := object_region base (m_regions m) in
          Some (match r_life reg with
                | Freed => RTrap OutOfBounds
                | Live => RUnchecked Span
                end)
      | _ => Some (RUnchecked Span)
      end
  | RUnchecked why => Some (RUnchecked why)
  end.

(** At run time, a [[half_check|half check]] tests only one end of an
    object's bounds because an earlier check already established the
    other end. Given the selected bound, the access span, and the
    object's region, [half_bound] tests `b + size <= end` for an [Upper]
    check, and tests that the object is [Live] with `base <= b` in
    signed 64-bit arithmetic for a [Lower] check. *)
Definition half_bound (bd : bound) (b size base end_ : Z) (l : life) : bool :=
  match bd with
  | Upper => b + size <=? end_
  | Lower =>
      match l with
      | Freed => false
      | Live => base <=? (if 2 ^ 63 <=? b then b - 2 ^ 64 else b)
      end
  end.

(** Given a bound selector, a memory state, an access span, a
    capability, requested rights, and an alignment, [half_passes]
    evaluates the complete run-time test of a [[half_check|half check]]:
    the chosen bound, write permission on a read-only object, and
    address alignment. If the capability does not name an object region,
    it returns `Some None` because a half check may only run on a
    capability whose object identity was already checked. *)
Definition half_passes (bd : bound) (m : mem) (b size : Z) (c : cap)
    (r : rights) (align : Z) : option (option bool) :=
  let test base ro :=
    let* reg := object_region base (m_regions m) in
    Some (Some (half_bound bd b size base (r_end reg) (r_life reg)
                && negb (rights_eqb r Write && ro)
                && (b mod align =? 0))) in
  match c with
  | Obj base => test base false
  | Ro base => test base true
  | _ => Some None
  end.

(** Given the full access check result and the boolean outcome of a half
    check's native test, [half_res] returns their shared outcome when
    both agree, and reports an [[unchecked]] [Half] fault if the
    unvalidated bound failed. *)
Definition half_res (r : res unit) (passes : bool) (p : word) : res word :=
  match r, passes with
  | RVal _, true => RVal p
  | RTrap why, false => RTrap why
  | _, _ => RUnchecked Half
  end.

(** ## Loads

    A non-pointer load reads a sequence of little-endian bytes from
    primary memory and extends narrow integer types to the target
    register class. A pointer load or store executes a multi-step
    protocol of [effect] operations that move both the 8-byte address in
    primary memory and the [[capability]] in the shadow [[aux]] slot. *)

(** Given a [narrow] integer type, a target register class, and a loaded
    unsigned integer, [extended] sign-extends or zero-extends the
    integer and wraps it to the modulus of the target class. *)
Definition extended (t : narrow) (k : class) (u : Z) : option word :=
  let* m := modulus k in Some (WInt (extension t u mod m)).

(** Given a non-pointer [load_type] and result class, [int_load_res]
    checks read permission for the required byte count at alignment 1,
    loads the little-endian bytes from memory, and applies [extended]
    when the load type is narrow. *)
Definition int_load_res (t : load_type) (k : class) (m : mem) (a : Z) (c : cap)
  : option (res word) :=
  let size := match t with
              | LdL | LdD => 8 | LdS => 4 | LdX => 10
              | LdNarrow n => fst (narrow_type n)
              end in
  let* chk := access_res m a c size Read 1 in
  match chk with
  | RVal _ =>
      let u := load_bytes m a size in
      match t with
      | LdNarrow n => let* x := extended n k u in Some (RVal x)
      | _ => Some (RVal (WInt u))
      end
  | RTrap why => Some (RTrap why)
  | RUnchecked why => Some (RUnchecked why)
  end.

(** Given a memory state, an address, the current accumulator of
    capability and pointer, and a single protocol [effect],
    [pointer_load_effect] executes one step of a pointer load. It reads
    the shadow capability on [AuxRead], resolves the capability on
    [LowerResolve], reads the 8-byte address on [AddressRead], or reads
    both together on [AtomicRead]. *)
Definition pointer_load_effect (m : mem) (a : Z) (st : cap * ptr) (e : effect)
  : option (cap * ptr) :=
  let (c, p) := st in
  match e with
  | AuxRead => let c' := aux_at m a in Some (c', mkPtr (ptr_addr p) c')
  | LowerResolve => Some (c, mkPtr (ptr_addr p) c)
  | AddressRead => Some (c, mkPtr (load_bytes m a 8) (ptr_cap p))
  | AtomicRead =>
      let c' := aux_at m a in Some (c', mkPtr (load_bytes m a 8) c')
  | _ => None
  end.

(** Given a memory state, an address, and a list of protocol steps,
    [pointer_load_effects] folds [pointer_load_effect] from an initial
    empty pointer state and returns the assembled pointer. *)
Definition pointer_load_effects (m : mem) (a : Z) (es : list effect) : option ptr :=
  let* st := fold_left (fun st e => let* s := st in pointer_load_effect m a s e)
                       es (Some (CNone, mkPtr 0 CNone)) in
  Some (snd st).

(** Given a target address, a pointer value, a memory state, and a
    single protocol [effect], [pointer_store_effect] executes one step
    of a pointer store. In the single-threaded model, [AuxEnsure],
    [LowerBarrier], and [RootedReload] leave memory unchanged, while
    [LowerWrite] writes the capability to [[aux]], [AddressWrite] writes
    the 8-byte address to primary memory, and [AtomicWrite] writes both. *)
Definition pointer_store_effect (a : Z) (x : ptr) (m : mem) (e : effect) : option mem :=
  match e with
  | AuxEnsure | LowerBarrier | RootedReload => Some m
  | LowerWrite => Some (store_aux m a (ptr_cap x))
  | AddressWrite => Some (store_bytes m a 8 (ptr_addr x))
  | AtomicWrite => Some (store_bytes (store_aux m a (ptr_cap x)) a 8 (ptr_addr x))
  | _ => None
  end.

(** Given a target address, a pointer value, a memory state, and a list
    of protocol steps, [pointer_store_effects] runs
    [pointer_store_effect] for each step in order. *)
Definition pointer_store_effects (a : Z) (x : ptr) (m : mem) (es : list effect)
  : option mem :=
  fold_left (fun m e => let* m' := m in pointer_store_effect a x m' e) es (Some m).

(** ## Stores

    A memory store checks write permission and alignment through the
    destination capability before modifying memory. This section defines
    [store_res], which writes either a pointer or a numeric value of a
    given storage [width]. *)

(** Given a storage [width], a memory state, a destination address and
    capability, and a value word, [store_res] checks write access and
    alignment, requiring 8-byte alignment for pointers and 80-bit floats
    and 1-byte alignment otherwise. When the check succeeds, it writes
    the value's little-endian bytes and, for a pointer store, writes the
    pointer's capability into the shadow [[aux]] slot; when the check
    traps, memory remains unchanged. *)
Definition store_res (w : width) (m : mem) (a : Z) (c : cap) (x : word)
  : option (res unit * mem) :=
  let size := width_bytes w in
  match w, x with
  | Wp, WPtr v =>
      let* chk := access_res m a c size Write 8 in
      Some (chk, match chk with
                 | RVal _ => store_aux (store_bytes m a size (ptr_addr v)) a (ptr_cap v)
                 | _ => m
                 end)
  | (Wb | Wh | Ww | Wl | Ws | Wd | Wx), WInt v =>
      let align := match w with Wx => 8 | _ => 1 end in
      let* chk := access_res m a c size Write align in
      Some (chk, match chk with RVal _ => store_bytes m a size v | _ => m end)
  | _, _ => None
  end.

(** ## Compare-exchange

    An atomic compare-and-exchange ([[cas]]) checks write permission and
    natural alignment for the accessed width, reads the current value at
    the address, compares it with the expected word, and writes the new
    word only when they match. This section defines [cas_res] for
    pointers, 64-bit integers, and narrow integers. *)

(** Given a [cas_type], result class, memory state, target address and
    capability, expected word, and new word, [cas_res] evaluates a
    compare-and-exchange. It first checks write access of [cas_bytes]
    bytes at natural alignment, leaving memory unchanged if the check
    traps. On a pointer [CasP], it compares only the 8-byte address in
    memory against the expected pointer's address, ignoring capabilities
    just as Fil-C's `c: filc_strong_cas_ptr` does, and writes the new
    pointer's capability and address when the addresses match. On an
    integer type, it compares the loaded bytes against the low bytes of
    the expected integer and writes the new integer's bytes on a match
    without touching [[aux]]. In both cases, it returns the old value
    read from memory. *)
Definition cas_res (t : cas_type) (k : class) (m : mem) (a : Z) (c : cap) (e n : word)
  : option (res word * mem) :=
  let size := cas_bytes t in
  let* chk := access_res m a c size Write size in
  match chk with
  | RTrap why => Some (RTrap why, m)
  | RUnchecked why => Some (RUnchecked why, m)
  | RVal _ =>
      let u := load_bytes m a size in
      match t, e with
      | CasP, WPtr ep =>
          let old := WPtr (mkPtr u (aux_at m a)) in
          if u =? ptr_addr ep then
            match n with
            | WPtr np => let* m' := pointer_store_effects a np m [LowerWrite; AddressWrite] in
                         Some (RVal old, m')
            | _ => None
            end
          else Some (RVal old, m)
      | CasL, WInt ev | CasNarrow _, WInt ev =>
          let* old := match t with CasNarrow nt => extended nt k u | _ => Some (WInt u) end in
          if u =? ev mod 2 ^ (8 * size) then
            match n with
            | WInt nv => Some (RVal old, store_bytes m a size nv)
            | _ => None
            end
          else Some (RVal old, m)
      | _, _ => None
      end
  end.

(** ## Variadic arguments

    In Fil-C, a variadic function receives its extra arguments in a
    read-only snapshot object, and a `c: va_list` holds a pointer cursor
    into that object. This section defines how `c: va_arg` aligns the
    cursor, checks the argument cell, advances the cursor, and loads the
    argument value. *)

(** For any value class other than a proof class, [class_width] returns
    the corresponding storage [width]. *)
Definition class_width (k : class) : option width :=
  match k with
  | W => Some Ww | L => Some Wl | P => Some Wp
  | Single => Some Ws | Double => Some Wd | Extended => Some Wx
  | _ => None
  end.

(** Given an argument [class], [va_cell] returns the byte step and
    required cursor alignment for a variadic argument of that class. An
    80-bit [Extended] float occupies a 16-byte cell aligned to 16 bytes
    from which 10 bytes are read, while all other classes step by their
    storage width at 8-byte alignment. *)
Definition va_cell (k : class) : option (Z * Z) :=
  match k with
  | Extended => Some (16, 16)
  | _ => let* w := class_width k in Some (width_bytes w, 8)
  end.

(** Given a target [class], a `c: va_list` pointer, and a memory state,
    [va_arg_res] reads the next variadic argument. It checks and loads
    the cursor pointer stored at the `c: va_list` address, aligns the
    cursor to the argument's [va_cell] alignment, checks that the cursor
    capability can read the cell, stores the advanced cursor address
    back into the `c: va_list`, and loads the argument word from the
    cell. *)
Definition va_arg_res (k : class) (p : ptr) (m : mem) : option (res word * mem) :=
  let* chk := access_res m (ptr_addr p) (ptr_cap p) 8 Read 8 in
  match chk with
  | RTrap why => Some (RTrap why, m)
  | RUnchecked _ => None
  | RVal _ =>
      let cursor := mkPtr (load_bytes m (ptr_addr p) 8) (aux_at m (ptr_addr p)) in
      let* cell := va_cell k in
      let (step, align) := cell in
      let* w := class_width k in
      let a := (ptr_addr cursor + align - 1) / align * align in
      let* chk' := access_res m a (ptr_cap cursor) step Read 8 in
      match chk' with
      | RTrap why => Some (RTrap why, m)
      | RUnchecked _ => None
      | RVal _ =>
          let* stored := store_res Wl m (ptr_addr p) (ptr_cap p) (WInt (a + step)) in
          let (r, m1) := stored in
          match r, k with
          | RTrap why, _ => Some (RTrap why, m1)
          | RUnchecked _, _ => None
          | RVal _, P => Some (RVal (WPtr (mkPtr (load_bytes m1 a 8) (aux_at m1 a))), m1)
          | RVal _, _ => Some (RVal (WInt (load_bytes m1 a (width_bytes w))), m1)
          end
      end
  end.

(** ## Ops

    Most operations in a [Let] instruction finish immediately with a
    partial result and a memory state, but heap allocation must ask the
    runtime allocator for a [[fresh]] base address. This section defines
    the operation outcome type [op_out] that unifies immediate results,
    undefined float-to-integer conversions, and allocation requests. *)

(** An [op_out] is the outcome of evaluating an operation: either a
    partial result paired with the resulting memory state [OpRes],
    undefined behavior from an out-of-range float-to-integer conversion
    [OpUB], or an allocation request [OpAlloc] paired with a
    continuation waiting for a [[fresh]] base address. *)
Inductive op_out : Type :=
| OpRes (r : res word) (m : mem)
| OpUB (why : term) (* `ub(Why)` *)
| OpAlloc (q : alloc_req) (k : Z -> word * mem). (* allocate q; k gives the result and the memory for its [[fresh]] base *)

(** ## Floats

    Floating-point temporaries hold IEEE 754 bit patterns as integer
    words, and floating-point operations delegate bit-exact arithmetic
    and conversions to [Ieee](Ieee.v). This section connects the
    floating-point operations in the IR to their IEEE implementations
    and then defines the complete operation evaluators [op_res_int] and
    [op_res]. *)

(** For a floating-point [class], [fmt_of] returns the corresponding
    IEEE format from [Ieee](Ieee.v), or `None` for non-float classes. *)
Definition fmt_of (k : class) : option fmt :=
  match k with
  | Single => Some FmtS | Double => Some FmtD | Extended => Some FmtX
  | _ => None
  end.

(** For a floating-point comparison condition, [fcond_of] returns the
    corresponding IEEE comparison code from [Ieee](Ieee.v), or `None`
    for signed and unsigned integer orderings. *)
Definition fcond_of (c : cond) : option fcond :=
  match c with
  | Eq => Some FEq | Ne => Some FNe | Le => Some FLe | Lt => Some FLt
  | Ge => Some FGe | Gt => Some FGt | Ord => Some FOrd | Unord => Some FUnord
  | _ => None
  end.

(** Given a comparison condition and an IEEE format, [float_compare]
    compares two floating-point bit patterns and returns 1 when the
    condition holds and 0 otherwise. *)
Definition float_compare (c : cond) (ck : fmt) (a b : Z) : Z :=
  match fcond_of c with Some fc => ieee_compare ck fc a b | None => 0 end.

(** Given an arithmetic operation, an IEEE format, and a list of operand
    words, [float_arithmetic] evaluates floating-point addition,
    subtraction, multiplication, division, negation, or copy on bit
    patterns. *)
Definition float_arithmetic (o : op) (k : fmt) (xs : list word) : option Z :=
  match o, xs with
  | Copy, [WInt x] => Some x
  | Neg, [WInt x] => Some (ieee_neg k x)
  | Add, [WInt x; WInt y] => Some (ieee_binary k FAdd x y)
  | Sub, [WInt x; WInt y] => Some (ieee_binary k FSub x y)
  | Mul, [WInt x; WInt y] => Some (ieee_binary k FMul x y)
  | Div, [WInt x; WInt y] => Some (ieee_binary k FDiv x y)
  | _, _ => None
  end.

(** Given a floating-point conversion or square-root operation, a target
    class, and an input bit pattern, [float_convert] widens, truncates,
    or takes the square root of the floating-point value using
    round-to-nearest-even. *)
Definition float_convert (o : op) (k : class) (x : Z) : option Z :=
  let* to := fmt_of k in
  match o, k with
  | ExtF Single, _ => Some (ieee_convert FmtS to x)
  | ExtF Double, Extended => Some (ieee_convert FmtD FmtX x)
  | Truncd, Single => Some (ieee_convert FmtD FmtS x)
  | Truncx, _ => Some (ieee_convert FmtX to x)
  | Sqrt, _ => Some (ieee_sqrt to x)
  | _, _ => None
  end.

(** Given a source IEEE format, target signedness, target integer class,
    and floating-point bit pattern, [float_integer] truncates the
    floating-point number toward zero. If the number is finite and fits
    within the signed or unsigned range of the target class, it returns
    the wrapped integer word; otherwise it reports `float_conversion`
    undefined behavior via [OpUB]. *)
Definition float_integer (from : fmt) (sg : signedness) (k : class) (x : Z) (m0 : mem)
  : option op_out :=
  let* m := modulus k in
  let '(lo, hi) := match sg with
                   | Signed => (- (m / 2), m / 2 - 1)
                   | Unsigned => (0, m - 1)
                   end in
  match ieee_to_int from x with
  | Some n => if (lo <=? n) && (n <=? hi) then Some (OpRes (RVal (WInt (n mod m))) m0)
              else Some (OpUB (TAtom "float_conversion"))
  | None => Some (OpUB (TAtom "float_conversion"))
  end.

(** Given an integer source class, signedness, and bit pattern,
    [integer_source] reads the integer as signed or unsigned before
    converting it to floating-point. *)
Definition integer_source (ik : class) (sg : signedness) (x : Z) : option Z :=
  match sg with Signed => signed ik x | Unsigned => Some x end.

(** The function [op_res_int] evaluates all non-floating-point
    operations in the core subset: heap [[alloc|allocation]], capability
    [[check|checks]] and their [[reuse]] forms, [[raw-access|raw loads]]
    and raw [[cas]], pointer addition and subtraction, and integer [alu]
    operations. It returns `None` when the operands have the wrong form
    or when an operation such as [Setjmp] is stuck in the semantics. *)
Definition op_res_int (o : op) (k : class) (xs : list word) (m : mem) : option op_out :=
  let pure (x : option word) := let* w := x in Some (OpRes (RVal w) m) in
  let with_mem (r : option (res word)) := let* r' := r in Some (OpRes r' m) in
  match o, k, xs with
  | Alloc align, _, [WInt size] =>
      if max_allocation_size <? size then Some (OpRes (RTrap TooBig) m)
      else
        let q := heap_req align size in
        Some (OpAlloc q (fun base => (WPtr (mkPtr base (Obj base)), allocated m q base)))
  | Check lo hi r al, A, [WPtr p] =>
      let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
      Some (OpRes (checked_res chk (WPtr p)) m)
  | CheckAhead lo hi r al ahi, A, [WPtr p] =>
      let b := raw_address (ptr_addr p) lo in
      let* need := access_res m b (ptr_cap p) (ahi - lo) r al in
      match need with
      | RTrap why => Some (OpRes (RTrap why) m)
      | _ =>
          let* whole := access_res m b (ptr_cap p) (hi - lo) r al in
          match whole with
          | RTrap why => Some (OpRes (RTrap (Early why)) m)
          | _ => Some (OpRes (RVal (WPtr p)) m)
          end
      end
  | Renew lo hi r al, A, [q1; x] =>
      match q1, x with
      | WPtr p1, WPtr p =>
          if cap_eqb (ptr_cap p1) (ptr_cap p) then
            let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
            with_mem (renew_res chk p m)
          else Some (OpRes (RUnchecked Alias) m)
      | _, _ => Some (OpRes (RUnchecked Alias) m)
      end
  | RenewHull lo hi r al, A, [ql; qh; x] =>
      match ql, qh, x with
      | WPtr pl, WPtr ph, WPtr p =>
          if cap_eqb (ptr_cap pl) (ptr_cap p) && cap_eqb (ptr_cap ph) (ptr_cap p) then
            let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
            with_mem (renew_res chk p m)
          else Some (OpRes (RUnchecked Alias) m)
      | _, _, _ => Some (OpRes (RUnchecked Alias) m)
      end
  | HalfCheck bd lo hi r al, A, [q1; x] =>
      match q1, x with
      | WPtr p1, WPtr p =>
          if cap_eqb (ptr_cap p1) (ptr_cap p) then
            let b := raw_address (ptr_addr p) lo in
            let* chk := access_res m b (ptr_cap p) (hi - lo) r al in
            let* passes := half_passes bd m b (hi - lo) (ptr_cap p) r al in
            match passes with
            | Some ok' => Some (OpRes (half_res chk ok' (WPtr p)) m)
            | None => Some (OpRes (RUnchecked Half) m)
            end
          else Some (OpRes (RUnchecked Alias) m)
      | _, _ => Some (OpRes (RUnchecked Alias) m)
      end
  | SpanTest lo hi, W, [WPtr p] =>
      let span base :=
        let* reg := object_region base (m_regions m) in
        let l := raw_address (ptr_addr p) lo in
        let h := raw_address (ptr_addr p) hi in
        Some (OpRes (RVal (WInt (if (base <=? l) && (l <? h) && (h <=? r_end reg)
                                 then 1 else 0))) m) in
      match ptr_cap p with
      | Obj base | Ro base => span base
      | _ => Some (OpRes (RVal (WInt 0)) m)
      end
  | RenewIf lo hi r al, A, [WPtr p; WInt g] =>
      let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
      if g =? 0 then Some (OpRes (checked_res chk (WPtr p)) m)
      else match chk with
           | RTrap Misaligned => Some (OpRes (RTrap Misaligned) m)
           | _ => with_mem (renew_res chk p m)
           end
  | Limit size, L, [WPtr p] => pure (Some (WLimit (ptr_cap p) size))
  | CheckLimit lo hi r al, A, [WPtr p; u] =>
      match u with
      | WLimit c size =>
          if cap_eqb c (ptr_cap p) && (size =? hi - lo) then
            let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
            Some (OpRes (checked_res chk (WPtr p)) m)
          else Some (OpRes (RUnchecked WhyLimit) m)
      | _ => Some (OpRes (RUnchecked WhyLimit) m)
      end
  | RawLoad t off, _, [WPtr p] =>
      let* r := int_load_res t k m (raw_address (ptr_addr p) off) (ptr_cap p) in
      Some (OpRes (raw_res r) m)
  | RawLoadPointer off es, P, [WPtr p] =>
      let b := raw_address (ptr_addr p) off in
      let* chk := access_res m b (ptr_cap p) 8 Read 8 in
      match chk with
      | RVal _ => let* x := pointer_load_effects m b es in Some (OpRes (RVal (WPtr x)) m)
      | RTrap why | RUnchecked why => Some (OpRes (RUnchecked why) m)
      end
  | RawCas t off, _, [WPtr p; e; n] =>
      let* rm := cas_res t k m (raw_address (ptr_addr p) off) (ptr_cap p) e n in
      Some (OpRes (raw_res (fst rm)) (snd rm))
  | (Add | Sub), _, _ => pure (additive_res k o xs)
  | (Mul | Div | Udiv | Rem | Urem | And | Or | Xor | Sar | Shr | Shl
     | Neg | Copy | Select | Ptoi | Itop | Cmp _ _ | Ext _), _, _ => pure (alu o k xs)
  | _, _, _ => None
  end.

(** The top-level function [op_res] evaluates any operation in the core
    subset on a list of argument words and a memory state. It dispatches
    floating-point comparisons, arithmetic, conversions, bit-casts, and
    [VaArg] first, and delegates all remaining integer, pointer, and
    check operations to [op_res_int]. *)
Definition op_res (o : op) (k : class) (xs : list word) (m : mem) : option op_out :=
  match o, fmt_of k, xs with
  | Cmp c ck, _, [WInt a; WInt b] =>
      match fmt_of ck with
      | Some f => Some (OpRes (RVal (WInt (float_compare c f a b))) m)
      | None => op_res_int o k xs m
      end
  | Cmp _ ck, _, _ => match fmt_of ck with Some _ => None | None => op_res_int o k xs m end
  | (Add | Sub | Mul | Div | Neg | Copy), Some f, _ =>
      let* r := float_arithmetic o f xs in Some (OpRes (RVal (WInt r)) m)
  | (ExtF _ | Truncd | Truncx | Sqrt), _, [WInt x] =>
      let* r := float_convert o k x in Some (OpRes (RVal (WInt r)) m)
  | FloatToInt fk sg, _, [WInt x] =>
      let* from := fmt_of fk in
      float_integer from sg k x m
  | IntToFloat ik sg, Some f, [WInt x] =>
      let* n := integer_source ik sg x in Some (OpRes (RVal (WInt (ieee_from_int f n))) m)
  | Cast, _, [WInt x] => Some (OpRes (RVal (WInt x)) m)
  | VaArg, _, [WPtr p] => let* rm := va_arg_res k p m in Some (OpRes (fst rm) (snd rm))
  | _, _, _ => op_res_int o k xs m
  end.

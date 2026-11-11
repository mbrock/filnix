(** In Fil-C, memory consists of three parts: the primary data bytes at
    every address, the list of allocated object [[region|regions]] that
    record each object's bounds and lifetime, and the shadow [[aux]] map
    that holds a pointer [[capability]] at every 8-byte-aligned address
    where a pointer was stored. This module defines that memory state
    [mem], the capability [[access]] check [access_res], little-endian
    byte loads and stores, deallocation via [free_res], and the
    [[fresh]] allocation predicate.

    A region's bounds run from its base address—which also serves as the
    object's [[identity]]—up to its end address. Only deallocation
    changes an existing region's bounds: freeing a heap object or ending
    a stack frame sets the region's end equal to its base and marks the
    region as [Freed], while leaving all data bytes and stored
    capabilities in place. Because every pointer capability names its
    target object by identity and looks up the region's current bounds
    on each access, every alias to a freed object sees empty bounds and
    traps immediately.

    Unlike the Prolog [[interpreter]], which threads a monotone
    next-allocation cursor inside the memory record, [mem] does not fix
    how the allocator chooses addresses. Instead, an allocation may use
    any base address that satisfies [fresh], and [Runtime](Runtime.v)
    axiomatizes the allocator, deallocator, and garbage-collection
    [[poll|safepoint]] behavior around [mem]. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values.
Import ListNotations.
Open Scope Z_scope.

(** ## Reasons and partial results

    When an instruction checks a pointer, accesses memory, or calls a
    function, it can either produce a value, stop the program with a
    Fil-C safety [[trap]], or—if a compiler pass emitted an invalid raw
    access or check reuse—fail as [[unchecked]]. This section defines
    the failure [reason] codes and the partial-result wrapper [res] that
    operations and memory checks return. *)

(** A [reason] explains why a safety check trapped or why an invalid raw
    access was flagged as [[unchecked]]. Memory access checks report
    [NullCapability], [OutOfBounds], [Misaligned], or [Readonly];
    function calls report [NotAFunction], [ArgumentSize], or
    [ReturnSize]; deallocation reports [InvalidFree] or [DoubleFree];
    and heap allocation reports [TooBig] or [OutOfMemory]. The [[reuse]]
    forms report [Alias], [Span], [Half], or [WhyLimit] when a broken
    pass reuses a check whose premises fail, while [Early] and [Ahead]
    distinguish a [[check_ahead]] that trapped early on bytes needed
    only by a later access. *)
Inductive reason : Type :=
| NullCapability | OutOfBounds | Misaligned | Readonly | NotAFunction
| ArgumentSize | ReturnSize | InvalidFree | DoubleFree
| TooBig | OutOfMemory
| Alias | Span | Half | WhyLimit
| Early (r : reason) (* a [[check_ahead]] trapped with r on bytes that only a later access needs *)
| Ahead (r : reason). (* a [[doomed]] run terminated before reaching the access that needed those bytes *)

(** A partial result [res] wraps the outcome of an operation or memory
    check: either a normal value [RVal], a safety trap [RTrap] with its
    [reason], or an [[unchecked]] fault [RUnchecked] when a
    [[raw-access|raw access]] or check reuse violates its capability. *)
Inductive res (X : Type) : Type :=
| RVal (x : X) (* a normal result value, or ok when X is unit *)
| RTrap (r : reason) (* a Fil-C safety check failed with reason r, causing a [[trap]] *)
| RUnchecked (r : reason). (* a [[raw-access|raw access]] or check reuse failed without trapping *)

Arguments RVal {X} x.
Arguments RTrap {X} r.
Arguments RUnchecked {X} r.

(** The notation [ok] abbreviates a successful [res] that carries the
    unit value. *)
Notation ok := (RVal tt).

(** ## Regions and memory

    Every allocated object in Fil-C has a [region] entry in memory that
    tracks where the object starts, where it ends, whether it lives on
    the stack, on the heap, or in global data, and whether it is still
    live. This section defines the [region] and [mem] records and the
    helper functions that look up or update an object's region by its
    base [[identity]]. *)

(** An object's storage [kind] records whether it lives on the [Stack]
    as a named local for the current invocation, on the [Heap], or in
    [GlobalData]. Only a [Heap] object can be deallocated by `c: free`. *)
Inductive kind : Type := Stack | Heap | GlobalData.

(** The function [kind_eqb] tests whether two storage kinds are equal. *)
Definition kind_eqb (k k' : kind) : bool :=
  match k, k' with
  | Stack, Stack | Heap, Heap | GlobalData, GlobalData => true
  | _, _ => false
  end.

(** A [life] tag records whether an allocated object is currently [Live]
    or has been [Freed]. *)
Inductive life : Type := Live | Freed.

(** A [region] describes one allocated object in memory, recording its
    base address, its current end address, its storage [kind], and its
    [life] state. *)
Record region : Type := mkRegion {
  r_base : Z; (* first byte address of the object, which also serves as its [[identity]] *)
  r_end : Z; (* address one past the last byte, or equal to r_base once freed *)
  r_kind : kind;
  r_life : life
}.

(** The [mem] record holds the complete memory state: the byte map
    [m_bytes], the list of object regions [m_regions], and the shadow
    capability map [m_aux]. *)
Record mem : Type := mkMem {
  m_bytes : Z -> Z; (* byte value at each address, defaulting to 0 in unwritten memory *)
  m_regions : list region; (* registered objects, with one region per object identity *)
  m_aux : Z -> cap (* capability stored at each 8-byte-aligned aux slot, or [CNone] elsewhere *)
}.

(** Given an object's base [[identity]] and a region list,
    [object_region] returns the first region with that base address, or
    `None` if no such object is registered. *)
Fixpoint object_region (base : Z) (rs : list region) : option region :=
  match rs with
  | [] => None
  | r :: rs' => if Z.eqb (r_base r) base then Some r else object_region base rs'
  end.

(** Given an object's base address and a region list, [remove_region]
    drops the first region with that base address and keeps all other
    regions in order. *)
Fixpoint remove_region (base : Z) (rs : list region) : list region :=
  match rs with
  | [] => []
  | r' :: rs' => if Z.eqb (r_base r') base then rs' else r' :: remove_region base rs'
  end.

(** When `c: free` or function return ends an object's lifetime,
    [replace_region] replaces the first region of that base address with
    an updated region at the front of the list, or returns `None` if the
    base address is not registered. *)
Definition replace_region (base : Z) (r : region) (rs : list region)
  : option (list region) :=
  match object_region base rs with
  | None => None
  | Some _ => Some (r :: remove_region base rs)
  end.

(** ## The access check

    Before any load or store runs, Fil-C checks the pointer's
    [[capability]] against the region table to verify that the pointer
    targets a live object, the accessed byte span lies within the
    object's bounds, the capability permits the requested [[rights]],
    and the address is properly aligned. This section defines that check
    in the exact order used by the Fil-C runtime. *)

(** Given a byte address and a required alignment, [aligned_res] returns
    [ok] when the address is a multiple of the alignment, and traps with
    [Misaligned] otherwise. *)
Definition aligned_res (a align : Z) : res unit :=
  if Z.eqb (a mod align) 0 then ok else RTrap Misaligned.

(** Once a pointer into a read-only object passes its bounds check,
    [readonly_access_res] traps with [Readonly] on a write and checks
    address alignment on a read. *)
Definition readonly_access_res (r : rights) (a align : Z) : res unit :=
  match r with
  | Read => aligned_res a align
  | Write => RTrap Readonly
  end.

(** Given a [[capability]], a region list, a byte span, requested
    [[rights]], and an alignment, [cap_access_res] runs Fil-C's
    capability [[access]] check. It checks trap conditions in the
    runtime's order: first a null capability, then the object's lower
    and upper bounds, then read-only permissions on a write, and finally
    address alignment. A function capability has zero byte extent so
    every memory access through it traps with [OutOfBounds], whereas an
    external symbol capability has no region in the module and returns
    `None`. *)
Definition cap_access_res (c : cap) (rs : list region) (a size : Z)
    (r : rights) (align : Z) : option (res unit) :=
  match c with
  | CNone => Some (RTrap NullCapability)
  | Fn _ => Some (RTrap OutOfBounds)
  | External _ => None
  | Obj base =>
      match object_region base rs with
      | None => None
      | Some reg =>
          Some (if (base <=? a) && (a + size <=? r_end reg)
                then aligned_res a align
                else RTrap OutOfBounds)
      end
  | Ro base =>
      match object_region base rs with
      | None => None
      | Some reg =>
          Some (if (base <=? a) && (a + size <=? r_end reg)
                then readonly_access_res r a align
                else RTrap OutOfBounds)
      end
  end.

(** The function [access_res] runs [cap_access_res] against the region
    list of a memory state [mem]. *)
Definition access_res (m : mem) (a : Z) (c : cap) (size : Z) (r : rights)
    (align : Z) : option (res unit) :=
  cap_access_res c (m_regions m) a size r align.

(** Given a base address and a signed byte offset, [raw_address]
    computes the effective 64-bit address modulo `2 ^ 64`. *)
Definition raw_address (a off : Z) : Z := (a + off) mod 2 ^ 64.

(** ## Bytes

    Multi-byte integers and pointer addresses are stored in primary
    memory in little-endian byte order, while pointer capabilities are
    stored alongside them in the shadow [[aux]] map. This section
    defines the functions that read and write little-endian byte
    sequences and shadow capability slots. *)

(** Given an integer and a zero-based byte index, [byte_of] extracts
    that byte in little-endian order. *)
Definition byte_of (x i : Z) : Z := (x / 2 ^ (8 * i)) mod 256.

(** Given a memory state, a starting address, and a byte count,
    [load_bytes] reads that many consecutive bytes and assembles them
    into an unsigned little-endian integer. *)
Definition load_bytes (m : mem) (a size : Z) : Z :=
  let fix go (n : nat) (acc : Z) :=
    match n with
    | O => acc
    | S n' => go n' (acc * 256 + m_bytes m (a + Z.of_nat n'))
    end in
  go (Z.to_nat size) 0.

(** Given a memory state, a starting address, a byte count, and an
    integer value, [store_bytes] writes the low bytes of the integer
    into primary memory in little-endian order and leaves regions and
    [[aux]] slots unchanged. *)
Definition store_bytes (m : mem) (a size x : Z) : mem :=
  let old := m_bytes m in
  mkMem (fun b => if (a <=? b) && (b <? a + size) then byte_of x (b - a) else old b)
        (m_regions m) (m_aux m).

(** Given a memory state, an address, and a [[capability]], [store_aux]
    updates the shadow [[aux]] slot at that address to hold the new
    capability. *)
Definition store_aux (m : mem) (a : Z) (c : cap) : mem :=
  let old := m_aux m in
  mkMem (m_bytes m) (m_regions m) (fun b => if Z.eqb b a then c else old b).

(** Given a memory state and an address, [aux_at] reads the
    [[capability]] stored in the shadow [[aux]] slot at that address,
    which is [CNone] if no pointer was stored there. *)
Definition aux_at (m : mem) (a : Z) : cap := m_aux m a.

(** ## Free

    In Fil-C, freeing a heap object does not reclaim its address or
    erase its data bytes; instead, it marks the object's [[region]] as
    [Freed] and collapses its upper bound to its base address so that
    any later access through any alias traps. This section defines the
    interpreter's deallocation functions for object capabilities,
    general capabilities, and run-time words. *)

(** Given an object's base [[identity]], a pointer address, and a memory
    state, [object_free_res] implements `c: free` for a pointer carrying
    an object capability. Passing address 0 is a no-op even when the
    pointer still carries an object's [[lower]] capability. For any
    nonzero address, it traps with [InvalidFree] unless the target is a
    [Heap] object and the address equals its base, traps with
    [DoubleFree] if the object is already [Freed], and otherwise
    replaces the object's region with an empty [Freed] region. *)
Definition object_free_res (base a : Z) (m : mem) : option (res unit * mem) :=
  if Z.eqb a 0 then Some (ok, m) else
  match object_region base (m_regions m) with
  | None => None
  | Some reg =>
      if negb (kind_eqb (r_kind reg) Heap) then Some (RTrap InvalidFree, m)
      else if negb (Z.eqb a base) then Some (RTrap InvalidFree, m)
      else match r_life reg with
           | Freed => Some (RTrap DoubleFree, m)
           | Live =>
               match replace_region base (mkRegion base base Heap Freed) (m_regions m) with
               | None => None
               | Some rs => Some (ok, mkMem (m_bytes m) rs (m_aux m))
               end
           end
  end.

(** Given any [[capability]] and address, [cap_free_res] dispatches
    `c: free` by capability kind: null and function capabilities succeed
    as a no-op at address 0 and trap with [InvalidFree] at any nonzero
    address, object capabilities run [object_free_res], and external
    capabilities return `None`. *)
Definition cap_free_res (c : cap) (a : Z) (m : mem) : option (res unit * mem) :=
  match c with
  | External _ => None
  | CNone | Fn _ => Some (if Z.eqb a 0 then ok else RTrap InvalidFree, m)
  | Obj base | Ro base => object_free_res base a m
  end.

(** Given a run-time [word] and a memory state, [free_res] runs
    `c: free` on a pointer word or treats a raw integer word as having
    [CNone] capability. In [Runtime](Runtime.v), the interpreter's
    runtime uses [free_res] and proves that it satisfies the
    deallocation axioms. *)
Definition free_res (x : word) (m : mem) : option (res unit * mem) :=
  match x with
  | WInt a => cap_free_res CNone a m
  | WPtr p => cap_free_res (ptr_cap p) (ptr_addr p) m
  | WLimit _ _ => None
  end.

(** ## Allocation

    When the program allocates a heap block or a named stack local, the
    allocator chooses a [[fresh]] base address that does not overlap any
    existing object and whose bytes and shadow capability slots are all
    zeroed. This section defines allocation requests, the [fresh]
    predicate, and the helper functions that add a newly allocated
    region to memory. *)

(** An [alloc_req] packages the three parameters of an
    [[alloc|allocation]]: the required byte alignment [req_align], the
    byte size [req_extent], and the storage kind [req_kind]. *)
Record alloc_req : Type := mkReq {
  req_align : Z;
  req_extent : Z;
  req_kind : kind
}.

(** A base address satisfies [fresh] for an allocation request in a
    memory state when it can serve as the address and [[identity]] of
    the new object. Specifically, the base must be positive, aligned to
    [req_align], unregistered in [m_regions], disjoint from the current
    bounds of every existing object, bounded by `2 ^ 64`, and backed by
    zero bytes and [CNone] capability slots across its entire extent. *)
Definition fresh (m : mem) (q : alloc_req) (base : Z) : Prop :=
  0 < base /\
  base mod req_align q = 0 /\
  base + req_extent q <= 2 ^ 64 /\
  object_region base (m_regions m) = None /\
  (forall b reg, object_region b (m_regions m) = Some reg ->
                 ~ (base < r_end reg /\ b < base + req_extent q)) /\
  (forall a, base <= a < base + req_extent q ->
             m_bytes m a = 0 /\ m_aux m a = CNone).

(** Given an address and a positive alignment, [align_up] rounds the
    address up to the next multiple of that alignment. *)
Definition align_up (a align : Z) : Z := (a + align - 1) / align * align.

(** Given a memory state, an allocation request, and a chosen base
    address, [allocated] prepends the new [Live] region to [m_regions]
    while keeping all bytes and shadow capabilities unchanged. *)
Definition allocated (m : mem) (q : alloc_req) (base : Z) : mem :=
  mkMem (m_bytes m)
        (mkRegion base (base + req_extent q) (req_kind q) Live :: m_regions m)
        (m_aux m).

(** The constant [max_allocation_size] is the maximum byte size
    `2 ^ 48 - 1` that Fil-C permits for a single heap allocation. *)
Definition max_allocation_size : Z := 2 ^ 48 - 1.

(** Given a requested alignment and byte size, [heap_req] constructs the
    [Heap] allocation request in [[mode|filc mode]], enforcing an
    alignment of at least 16 and rounding the byte extent up to a
    multiple of 16. *)
Definition heap_req (align size : Z) : alloc_req :=
  mkReq (Z.max align 16) ((size + 15) / 16 * 16) Heap.

(** Given a byte size, [local_req] constructs the [Stack] allocation
    request for a named local variable with 16-byte alignment and exact
    byte extent. *)
Definition local_req (size : Z) : alloc_req := mkReq 16 size Stack.

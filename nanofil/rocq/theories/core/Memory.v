(** Memory and Fil-C's access check, transcribed from interp.pl's
    Memory section.

    Memory is `mem(Bytes, Regions, Next, Aux)` in the interpreter. Here
    it is bytes, [[region|regions]] and [[aux]]; Next, the
    interpreter's next allocation address, is not part of the state. An
    allocation instead takes any base that is [[fresh]] for the memory
    (formal.md's decision): the interpreter's monotone Next is one such
    choice (the `alloc` of Runtime.v's [InterpRuntime]), and nothing
    may rely on it. Which bases a [[runtime]] may choose, and what it
    may do to memory at a [[poll|safepoint]], are Runtime.v's module
    type; this file states the interpreter's memory and its free.

    A region's bounds run from its base up to its end. Only free
    changes them, to empty: the end becomes the base and the region
    becomes freed. Bytes and aux stay as they were; every alias reads
    the region's current bounds. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values.
Import ListNotations.
Open Scope Z_scope.

(** ## Reasons and partial results *)

(** The reason of a `trap(Why)` or an `unchecked(Why)`, interp.pl's
    Why:

    - the access check's: [NullCapability], [OutOfBounds],
      [Misaligned], [Readonly];
    - a call's: [NotAFunction], [ArgumentSize] (fewer arguments than
      the callee's parameters), [ReturnSize] (the caller expects more
      result words than the callee returns);
    - free's: [InvalidFree], [DoubleFree];
    - an allocation's (`alloc_res/6`): [TooBig], [OutOfMemory];
    - the [[unchecked]] reasons of the [[reuse]] vocabulary, which only
      a broken pass produces: [Alias], a renew of another object;
      [Span], a renew whose source does not cover the access; [Half], a
      half check whose bound taken as known is false; [WhyLimit],
      interp.pl's `limit`, a [CheckLimit] whose limit does not match. *)
Inductive reason : Type :=
| NullCapability | OutOfBounds | Misaligned | Readonly | NotAFunction
| ArgumentSize | ReturnSize | InvalidFree | DoubleFree
| TooBig | OutOfMemory
| Alias | Span | Half | WhyLimit
| Early (r : reason) (* `early(Why)`: a [[check_ahead]] trapped with r for bytes a later access needs *)
| Ahead (r : reason). (* `ahead(Why)`: a [[doomed]] run did not reach that access *)

(** A partial result, interp.pl's Res. The interpreter's `ub(Why)`
    comes only from float conversions and plain mode, both outside the
    core subset. *)
Inductive res (X : Type) : Type :=
| RVal (x : X) (* `val(X)`, or `ok` when X is unit *)
| RTrap (r : reason) (* `trap(Why)`: a Fil-C check failed, a [[trap]] *)
| RUnchecked (r : reason). (* `unchecked(Why)`: a [[raw-access|raw access]] its capability does not allow *)

Arguments RVal {X} x.
Arguments RTrap {X} r.
Arguments RUnchecked {X} r.

(** Success with nothing to return, interp.pl's `ok`. *)
Notation ok := (RVal tt).

(** ## Regions and memory *)

(** Where an object lives: on the stack (a named local, gone when its
    invocation ends), on the heap, or in global data. Only a heap
    object may be passed to free. *)
Inductive kind : Type := Stack | Heap | GlobalData.

(** Equality of kinds. *)
Definition kind_eqb (k k' : kind) : bool :=
  match k, k' with
  | Stack, Stack | Heap, Heap | GlobalData, GlobalData => true
  | _, _ => false
  end.

(** Whether an object is live or has been freed. *)
Inductive life : Type := Live | Freed.

(** As `region(Base, End, Kind, Life)`: an object of memory, the
    [[region]] its capability names by its base. *)
Record region : Type := mkRegion {
  r_base : Z; (* the first address, also the object's [[identity]] *)
  r_end : Z; (* one past the last byte; the base again once freed *)
  r_kind : kind;
  r_life : life
}.

(** The memory, interp.pl's `mem(Bytes, Regions, Next, Aux)` without
    Next. *)
Record mem : Type := mkMem {
  m_bytes : Z -> Z; (* the byte at each address; 0 where nothing was written, since Fil-C zeroes allocations *)
  m_regions : list region; (* the objects, one region per identity *)
  m_aux : Z -> cap (* the capability a pointer store left at each 8-aligned slot, [CNone] elsewhere *)
}.

(** As `object_region(Base, Rs, Region)`: the first region of the list
    rs whose identity is base. Capabilities refer to registered
    identities; an unregistered base is outside the model. *)
Fixpoint object_region (base : Z) (rs : list region) : option region :=
  match rs with
  | [] => None
  | r :: rs' => if Z.eqb (r_base r) base then Some r else object_region base rs'
  end.

(** The regions rs without the first one of identity base. *)
Fixpoint remove_region (base : Z) (rs : list region) : list region :=
  match rs with
  | [] => []
  | r' :: rs' => if Z.eqb (r_base r') base then rs' else r' :: remove_region base rs'
  end.

(** As `select(Region, Rs0, Rest)` on the first region of identity
    base, with that region replaced by r at the front, as free and the
    end of an invocation do; none if no region has that identity. *)
Definition replace_region (base : Z) (r : region) (rs : list region)
  : option (list region) :=
  match object_region base rs with
  | None => None
  | Some _ => Some (r :: remove_region base rs)
  end.

(** ## The access check *)

(** As `aligned_res(A, Align, Res)`: [ok] if the address a is a
    multiple of align, else a [Misaligned] trap. *)
Definition aligned_res (a align : Z) : res unit :=
  if Z.eqb (a mod align) 0 then ok else RTrap Misaligned.

(** As `readonly_access_res(Kind, A, Align, Res)`: the last steps of
    the access check in bounds of a read-only object: a write traps
    [Readonly], and a read checks the alignment. *)
Definition readonly_access_res (r : rights) (a align : Z) : res unit :=
  match r with
  | Read => aligned_res a align
  | Write => RTrap Readonly
  end.

(** As `cap_access_res(Cap, Rs, A, Size, Kind, Align, Res)`: Fil-C's
    access check of size bytes at the address a, with the rights r and
    the alignment align, through the capability c among the regions
    rs. The trap reasons come in the backend's order: a null
    capability, then the bounds, then the read-only flag for a write,
    then the alignment. A function's capability has zero size, so every
    access through it is out of bounds. An external symbol's capability
    gives no answer: the interpreter cannot follow it, and neither does
    the model. *)
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

(** As `access_res(Mem, A, Cap, Size, Kind, Align, Res)`: the access
    check [cap_access_res] against the regions of the memory m. *)
Definition access_res (m : mem) (a : Z) (c : cap) (size : Z) (r : rights)
    (align : Z) : option (res unit) :=
  cap_access_res c (m_regions m) a size r align.

(** As `raw_address(A, Off, B)`: the address a plus the constant off,
    modulo 2^64. *)
Definition raw_address (a off : Z) : Z := (a + off) mod 2 ^ 64.

(** ## Bytes *)

(** As `le_bytes(N, X, Bytes)`, byte i of them: the i-th lowest byte of
    x, counting from 0, little-endian. *)
Definition byte_of (x i : Z) : Z := (x / 2 ^ (8 * i)) mod 256.

(** As `le_value(Bytes, U)` of the size bytes at the address a: their
    little-endian integer. *)
Definition load_bytes (m : mem) (a size : Z) : Z :=
  let fix go (n : nat) (acc : Z) :=
    match n with
    | O => acc
    | S n' => go n' (acc * 256 + m_bytes m (a + Z.of_nat n'))
    end in
  go (Z.to_nat size) 0.

(** As `written_bytes(Xs, A, Bytes0, Bytes)`: the memory m with the
    size low bytes of x written at the address a, little-endian. *)
Definition store_bytes (m : mem) (a size x : Z) : mem :=
  let old := m_bytes m in
  mkMem (fun b => if (a <=? b) && (b <? a + size) then byte_of x (b - a) else old b)
        (m_regions m) (m_aux m).

(** As `stored_aux(cap(C), A, Aux0, Aux)`: the memory m whose [[aux]]
    slot at the address a now holds the capability c. *)
Definition store_aux (m : mem) (a : Z) (c : cap) : mem :=
  let old := m_aux m in
  mkMem (m_bytes m) (m_regions m) (fun b => if Z.eqb b a then c else old b).

(** The capability a pointer store left at the address a, or [CNone]
    (`get_assoc(A, Aux, C) -> true ; C = none`). *)
Definition aux_at (m : mem) (a : Z) : cap := m_aux m a.

(** ## Free *)

(** As `object_free_res(Base, A, Mem0, Res, Mem)`: free of the address
    a through a capability of the object of identity base. Address 0
    is a no-op even with an object's [[lower]]. Otherwise it traps
    [InvalidFree] unless the object is on the heap and a is its base,
    and [DoubleFree] if it is freed already; else its region becomes
    empty and freed. Kind and address are validated before the free
    flag, as Fil-C's object_for_deallocate precedes free_impl. *)
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

(** As `cap_free_res(Cap, A, Mem0, Res, Mem)`: free of the address a
    through any capability c. One with no object, or a function's,
    frees only address 0, as a no-op, and traps [InvalidFree]
    otherwise; an external symbol's gives no answer. *)
Definition cap_free_res (c : cap) (a : Z) (m : mem) : option (res unit * mem) :=
  match c with
  | External _ => None
  | CNone | Fn _ => Some (if Z.eqb a 0 then ok else RTrap InvalidFree, m)
  | Obj base | Ro base => object_free_res base a m
  end.

(** As `free_res(P, Mem0, Res, Mem)`: the pinned runtime's free of the
    word x. An integer held at `p` has no capability. Runtime.v proves
    that it changes a region only as the lifetime axiom allows
    ([free_lifetime]). *)
Definition free_res (x : word) (m : mem) : option (res unit * mem) :=
  match x with
  | WInt a => cap_free_res CNone a m
  | WPtr p => cap_free_res (ptr_cap p) (ptr_addr p) m
  | WLimit _ _ => None
  end.

(** ## Allocation *)

(** What an [[alloc|allocation]] asks for: alignment, extent (the
    object's size in bytes) and kind, `alloc_base/6`'s Align, Extent
    and Kind. *)
Record alloc_req : Type := mkReq {
  req_align : Z;
  req_extent : Z;
  req_kind : kind
}.

(** The address base may be the identity and address of a new object
    of the request q in the memory m: a [[fresh|fresh base]]. It is a
    positive, aligned address; it is no object's identity, live or
    freed; the new bytes overlap no object's current bounds; they end
    at or below 2^64 (Runtime.v's [address_space] then bounds them by
    2^48, native's address space); and they read as zero with no
    stored capability, as Fil-C's allocations do. The interpreter
    never reuses an address; the model allows any choice that
    satisfies this. Runtime.v's [fresh_allocation] asks every
    runtime's choice to satisfy it.

    Objects are what [object_region] finds, as everywhere else: a
    region behind another of the same identity is no object. *)
Definition fresh (m : mem) (q : alloc_req) (base : Z) : Prop :=
  0 < base /\
  base mod req_align q = 0 /\
  base + req_extent q <= 2 ^ 64 /\
  object_region base (m_regions m) = None /\
  (forall b reg, object_region b (m_regions m) = Some reg ->
                 ~ (base < r_end reg /\ b < base + req_extent q)) /\
  (forall a, base <= a < base + req_extent q ->
             m_bytes m a = 0 /\ m_aux m a = CNone).

(** The address a rounded up to a multiple of align. *)
Definition align_up (a align : Z) : Z := (a + align - 1) / align * align.

(** The memory m after allocating the request q at base: the same bytes
    and aux, with the new object's region, live, in front. *)
Definition allocated (m : mem) (q : alloc_req) (base : Z) : mem :=
  mkMem (m_bytes m)
        (mkRegion base (base + req_extent q) (req_kind q) Live :: m_regions m)
        (m_aux m).

(** As `max_allocation_size/1`: Fil-C refuses a heap object of more
    bytes (FILC_MAX_ALLOCATION_SIZE, 2^48 - 1). *)
Definition max_allocation_size : Z := 2 ^ 48 - 1.

(** As `alloc_extent/4` and `alloc_align/3` in filc mode: the request
    of a heap object of size bytes at the alignment align. Its bounds
    are its size rounded up to 16, at an alignment of at least 16. *)
Definition heap_req (align size : Z) : alloc_req :=
  mkReq (Z.max align 16) ((size + 15) / 16 * 16) Heap.

(** The request of a named local of size bytes: exact size, 16-aligned,
    on the stack. *)
Definition local_req (size : Z) : alloc_req := mkReq 16 size Stack.

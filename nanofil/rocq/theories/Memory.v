(** Memory and Fil-C's access check, transcribed from interp.pl's
    Memory section.

    Memory is `mem(Bytes, Regions, Next, Aux)` in the interpreter. Here
    it is bytes, regions and aux; Next, the interpreter's next
    allocation address, is not part of the state. An allocation instead
    takes any base that is `fresh` for the memory (formal.md's
    decision): the interpreter's monotone Next is one such choice
    (Run.v's `interp_alloc`), and nothing may rely on it. Which bases
    a runtime may choose, and what it may do to memory at a safepoint,
    are Runtime.v's module type; this file states the interpreter's
    memory and its free.

    ## Parts

    | Part | Is |
    |---|---|
    | `m_bytes` | the byte at each address; 0 where nothing was written, since Fil-C zeroes allocations |
    | `m_regions` | `region(Base, End, Kind, Life)` objects, one per identity |
    | `m_aux` | the capability a pointer store left at each 8-aligned slot, `CNone` elsewhere |

    A region's bounds are [Base, End). Only free changes them, to
    empty: End becomes Base and Life becomes freed. Bytes and aux stay
    as they were; every alias reads the region's current bounds.

    ## The access check

    `cap_access_res` is Fil-C's access check, with the trap reasons in
    the backend's order: a null capability, then the bounds, then the
    read-only flag for a write, then the alignment. A function's
    capability has zero size, so every access is out of bounds. An
    external symbol's capability is stuck: the interpreter cannot
    follow it, and neither does the model. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values.
Import ListNotations.
Open Scope Z_scope.

(** ## Reasons and partial results *)

(** The reasons of `trap(Why)` and `unchecked(Why)`: the access check's,
    the call checks', free's, an allocation's (`alloc_res/6`), and those
    of the reuse vocabulary. *)
Inductive reason : Type :=
| NullCapability | OutOfBounds | Misaligned | Readonly | NotAFunction
| ArgumentSize | ReturnSize | InvalidFree | DoubleFree
| TooBig | OutOfMemory
| Alias | Span | Half | WhyLimit
| Early (r : reason)
| Ahead (r : reason).

(** A partial result, interp.pl's Res: `val(X)` (or `ok`, at unit),
    `trap(Why)` or `unchecked(Why)`. The interpreter's `ub(Why)` comes
    only from float conversions and plain mode, both outside the core
    subset. *)
Inductive res (X : Type) : Type :=
| RVal (x : X)
| RTrap (r : reason)
| RUnchecked (r : reason).

Arguments RVal {X} x.
Arguments RTrap {X} r.
Arguments RUnchecked {X} r.

Notation ok := (RVal tt).

(** ## Regions and memory *)

Inductive kind : Type := Stack | Heap | GlobalData.

Definition kind_eqb (k k' : kind) : bool :=
  match k, k' with
  | Stack, Stack | Heap, Heap | GlobalData, GlobalData => true
  | _, _ => false
  end.

Inductive life : Type := Live | Freed.

(** `region(Base, End, Kind, Life)`. *)
Record region : Type := mkRegion {
  r_base : Z;
  r_end : Z;
  r_kind : kind;
  r_life : life
}.

Record mem : Type := mkMem {
  m_bytes : Z -> Z;
  m_regions : list region;
  m_aux : Z -> cap
}.

(** `object_region(Base, Rs, Region)`: capabilities refer to registered
    identities; an unregistered base is outside the model. *)
Fixpoint object_region (base : Z) (rs : list region) : option region :=
  match rs with
  | [] => None
  | r :: rs' => if Z.eqb (r_base r) base then Some r else object_region base rs'
  end.

(** The regions without the first one of identity Base. *)
Fixpoint remove_region (base : Z) (rs : list region) : list region :=
  match rs with
  | [] => []
  | r' :: rs' => if Z.eqb (r_base r') base then rs' else r' :: remove_region base rs'
  end.

(** `select(Region, Rs0, Rest)` on the first region of identity Base,
    with Region replaced by R at the front, as free and the end of an
    invocation do. *)
Definition replace_region (base : Z) (r : region) (rs : list region)
  : option (list region) :=
  match object_region base rs with
  | None => None
  | Some _ => Some (r :: remove_region base rs)
  end.

(** ## The access check *)

(** `aligned_res(A, Align, Res)`. *)
Definition aligned_res (a align : Z) : res unit :=
  if Z.eqb (a mod align) 0 then ok else RTrap Misaligned.

(** `readonly_access_res(Kind, A, Align, Res)`. *)
Definition readonly_access_res (r : rights) (a align : Z) : res unit :=
  match r with
  | Read => aligned_res a align
  | Write => RTrap Readonly
  end.

(** `cap_access_res(Cap, Rs, A, Size, Kind, Align, Res)`: Fil-C's access
    check of Size bytes at A with Rights and Align. *)
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

(** `access_res(Mem, A, Cap, Size, Kind, Align, Res)`. *)
Definition access_res (m : mem) (a : Z) (c : cap) (size : Z) (r : rights)
    (align : Z) : option (res unit) :=
  cap_access_res c (m_regions m) a size r align.

(** `raw_address(A, Off, B)`: the address A plus the constant Off,
    modulo 2^64. *)
Definition raw_address (a off : Z) : Z := (a + off) mod 2 ^ 64.

(** ## Bytes *)

(** `le_bytes(N, X, Bytes)`, byte I of them: the I-th low byte of X. *)
Definition byte_of (x i : Z) : Z := (x / 2 ^ (8 * i)) mod 256.

(** `le_value(Bytes, U)` of the Size bytes at A. *)
Definition load_bytes (m : mem) (a size : Z) : Z :=
  let fix go (n : nat) (acc : Z) :=
    match n with
    | O => acc
    | S n' => go n' (acc * 256 + m_bytes m (a + Z.of_nat n'))
    end in
  go (Z.to_nat size) 0.

(** `written_bytes(Xs, A, Bytes0, Bytes)` for the Size low bytes of X. *)
Definition store_bytes (m : mem) (a size x : Z) : mem :=
  let old := m_bytes m in
  mkMem (fun b => if (a <=? b) && (b <? a + size) then byte_of x (b - a) else old b)
        (m_regions m) (m_aux m).

(** `stored_aux(cap(C), A, Aux0, Aux)`: the slot at A now holds C. *)
Definition store_aux (m : mem) (a : Z) (c : cap) : mem :=
  let old := m_aux m in
  mkMem (m_bytes m) (m_regions m) (fun b => if Z.eqb b a then c else old b).

(** The capability a pointer store left at A, or none
    (`get_assoc(A, Aux, C) -> true ; C = none`). *)
Definition aux_at (m : mem) (a : Z) : cap := m_aux m a.

(** ## Free *)

(** `object_free_res(Base, A, Mem0, Res, Mem)`: null is a no-op even
    with an object's lower; otherwise kind and address are validated
    before the free flag, as object_for_deallocate precedes free_impl. *)
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

(** `cap_free_res(Cap, A, Mem0, Res, Mem)`. *)
Definition cap_free_res (c : cap) (a : Z) (m : mem) : option (res unit * mem) :=
  match c with
  | External _ => None
  | CNone | Fn _ => Some (if Z.eqb a 0 then ok else RTrap InvalidFree, m)
  | Obj base | Ro base => object_free_res base a m
  end.

(** `free_res(P, Mem0, Res, Mem)`: the pinned runtime's free. An integer
    held at `p` has no capability. Runtime.v proves that it changes a
    region only as the lifetime axiom allows (`free_lifetime`). *)
Definition free_res (x : word) (m : mem) : option (res unit * mem) :=
  match x with
  | WInt a => cap_free_res CNone a m
  | WPtr p => cap_free_res (ptr_cap p) (ptr_addr p) m
  | WLimit _ _ => None
  end.

(** ## Allocation *)

(** What an allocation asks for: alignment, extent and kind
    (`alloc_base/6`'s Align, Extent and Kind). *)
Record alloc_req : Type := mkReq {
  req_align : Z;
  req_extent : Z;
  req_kind : kind
}.

(** `fresh m q base`: base may be the identity and address of a new
    object of q in m. It is a positive, aligned address; it is no
    object's identity, live or freed; the new bytes overlap no object's
    current bounds; they end at or below 2^64, so that no address
    inside the object wraps (`raw_address/3`); and they read as zero with
    no stored capability, as Fil-C's allocations do. The interpreter
    never reuses an address; the model allows any choice that satisfies
    this. Runtime.v's
    `fresh_allocation` asks every runtime's choice to satisfy it.

    Objects are what `object_region` finds, as everywhere else: a
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

(** a rounded up to a multiple of align. *)
Definition align_up (a align : Z) : Z := (a + align - 1) / align * align.

(** The memory after allocating q at base: its region, live. *)
Definition allocated (m : mem) (q : alloc_req) (base : Z) : mem :=
  mkMem (m_bytes m)
        (mkRegion base (base + req_extent q) (req_kind q) Live :: m_regions m)
        (m_aux m).

(** `max_allocation_size/1`: Fil-C refuses a heap object of more bytes
    (FILC_MAX_ALLOCATION_SIZE, 2^48 - 1). *)
Definition max_allocation_size : Z := 2 ^ 48 - 1.

(** `alloc_extent/4` and `alloc_align/3` in filc mode: a heap object's
    bounds are its size rounded up to 16, at an alignment of at least
    16. *)
Definition heap_req (align size : Z) : alloc_req :=
  mkReq (Z.max align 16) ((size + 15) / 16 * 16) Heap.

(** The same for a named local: exact size, 16-aligned, on the stack. *)
Definition local_req (size : Z) : alloc_req := mkReq 16 size Stack.

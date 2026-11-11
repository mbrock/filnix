(** In a C program proof, reasoning directly about the whole machine's
    memory as a single flat array is painful because of aliasing: every time
    a function writes through a pointer, you would have to prove that the
    store did not overwrite any other variable in the program.
    [[separation-logic|Separation logic]] avoids that work by splitting
    memory into independent pieces that different parts of a proof can own
    separately. This module defines the memory [piece] type used by the
    program logic in [Logic](Logic.v) and proves the whole-memory invariants
    that make owning pieces sound.

    ## Why pieces are keyed by object identity

    In Fil-C, every allocated object has a byte [[region]] in primary memory
    and a matching shadow [[aux]] region that holds pointer
    [[capability|capabilities]]. After a heap object is freed, a later
    [[fresh]] allocation can reuse its physical byte addresses for a new
    object with a new [[identity]]. If we keyed ownership by physical
    address, a freed object and a newly allocated object could share the
    same key. We therefore key memory pieces by object identity rather than
    physical address: [PLive] tracks whether an object is still live, while
    [PByte] and [PAux] name one data byte or one shadow capability slot at a
    byte offset inside that object. A fourth constructor, [PName], carries
    no memory at all and instead gives a [[ghost-state|ghost]] key for
    external library state, such as a locale name or stream handle.

    ## Whole-memory invariants and garbage collection

    Two properties of the whole Fil-C memory let proofs reason about
    separate objects and garbage collection independently. First, live
    objects never overlap in address space, so writing into one live object
    never alters any other live object's bytes or capabilities. Second, a
    garbage-collection [[poll|safepoint]] never moves or frees a live object
    and never alters data bytes. At a safepoint, the collector may only
    replace a shadow capability that pointed to a freed object with another
    capability that traps on access, so any capability to a live object
    remains intact. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls.
Import ListNotations.
Open Scope Z_scope.

(** ## Pieces

    To track ownership of individual fields and array elements inside an
    object, we break each object into a liveness token, individual data
    bytes, and individual shadow capability slots. This section defines the
    [piece] type, extracts the object [[identity]] that a memory piece
    belongs to, and defines the null pointer constant. *)

(** A [piece] names a single unit of state that an assertion in the program
    logic can own. The constructors [PLive], [PByte], and [PAux] name an
    object's liveness token, a data byte at an offset, and a shadow [[aux]]
    capability slot at an offset, while [PName] names a non-memory ghost
    entry for external world state. *)
Inductive piece : Type :=
| PLive (b : Z)
| PByte (b o : Z)
| PAux (b o : Z)
| PName (k : Z).

(** Every memory piece belongs to a specific allocated object. The function
    [piece_id] returns that object's [[identity]], or returns 0 for a
    [PName] ghost key that does not belong to any memory object. *)
Definition piece_id (p : piece) : Z :=
  match p with PLive b | PByte b _ | PAux b _ => b | PName _ => 0 end.

(** The predicate [mem_piece] holds when a piece represents actual object
    state in memory rather than a [PName] ghost key. *)
Definition mem_piece (p : piece) : Prop :=
  match p with PName _ => False | _ => True end.

(** In Fil-C, a null pointer has address 0 and carries no capability. The
    constant [null] packages that pointer value for use in C specifications. *)
Definition null : ptr := mkPtr 0 CNone.

(** ## The whole memory

    Owning pieces of an object by its identity only prevents aliasing if two
    different live objects can never occupy the same physical addresses.
    This section defines object liveness and address disjointness on
    physical memory, and characterizes how the garbage collector can rewrite
    capabilities to freed objects inside shadow [[aux]] slots. *)

(** An object identity satisfies [live_at] when it is registered in memory
    with the given [[region]] bounds and its lifetime state is currently
    live. *)
Definition live_at (m : mem) (b : Z) (reg : region) : Prop :=
  object_region b (m_regions m) = Some reg /\ r_life reg = Live.

(** A memory state satisfies [live_disjoint] when any two distinct live
    objects occupy non-overlapping byte address intervals. *)
Definition live_disjoint (m : mem) : Prop :=
  forall b1 r1 b2 r2, live_at m b1 r1 -> live_at m b2 r2 -> b1 <> b2 ->
    r_end r1 <= b2 \/ r_end r2 <= b1.

(** Two memory states satisfy [same_regions] when every object identity has
    the exact same region record in both memories. *)
Definition same_regions (m m' : mem) : Prop :=
  forall b, object_region b (m_regions m') = object_region b (m_regions m).

(** During a garbage-collection [[poll|safepoint]], the collector may sweep
    shadow [[aux]] slots that still point to freed objects and replace their
    capabilities with zeroed or trapping capabilities. The relation
    [aux_moves] states that each capability slot either keeps its exact
    capability or previously named a freed object and now holds a capability
    that still traps as freed. *)
Definition aux_moves (m m' : mem) : Prop :=
  forall a, m_aux m' a = m_aux m a \/
            (freed_in (m_regions m') (m_aux m a) /\ traps_as_freed (m_regions m') (m_aux m' a)).

(** Because a safepoint can rewrite dead capabilities in shadow memory at
    any time, our separation logic tracks capability slots up to collector
    sweeping. The predicate [aux_holds] holds when the shadow slot at an
    address either equals the recorded capability or both the recorded
    capability and the slot's current capability trap as freed. *)
Definition aux_holds (m : mem) (a : Z) (c : cap) : Prop :=
  m_aux m a = c \/ (freed_in (m_regions m) c /\ traps_as_freed (m_regions m) (m_aux m a)).

(** Whether a capability points to a freed object depends only on the
    memory's region table. If two memories have the same regions, any
    capability that was freed in the first memory remains freed in the
    second. *)
Lemma freed_in_same : forall m m' c,
  same_regions m m' -> freed_in (m_regions m) c -> freed_in (m_regions m') c.
Proof.
  intros m m' c Hr (b & reg & Hc & E & L). exists b, reg. rewrite Hr. auto.
Qed.

(** Similarly, whether dereferencing a capability traps like a freed object
    depends only on the memory's region table. Any capability that traps on
    access in one memory continues to trap in any memory with the same
    regions. *)
Lemma traps_as_freed_same : forall m m' c,
  same_regions m m' -> traps_as_freed (m_regions m) c -> traps_as_freed (m_regions m') c.
Proof.
  intros m m' c Hr H a size r align Hs. rewrite <- (H a size r align Hs).
  unfold cap_access_res. destruct c; try reflexivity; rewrite Hr; reflexivity.
Qed.

(** When the garbage collector sweeps shadow memory at a safepoint, it only
    rewrites capabilities that point to freed objects into other trapping
    capabilities. Consequently, any shadow capability slot that agreed with
    a recorded capability before the sweep still agrees with it afterward. *)
Lemma aux_holds_moves : forall m m' a c,
  same_regions m m' -> aux_moves m m' -> aux_holds m a c -> aux_holds m' a c.
Proof.
  intros m m' a c Hr Hm [E|(Hf & Ht)]; destruct (Hm a) as [E'|(Hf' & Ht')].
  - left. rewrite E'. exact E.
  - right. subst c. split; [exact Hf'|exact Ht'].
  - right. rewrite E'. split; [exact (freed_in_same _ _ _ Hr Hf)|exact (traps_as_freed_same _ _ _ Hr Ht)].
  - right. split; [exact (freed_in_same _ _ _ Hr Hf)|exact Ht'].
Qed.

(** The garbage collector only rewrites capabilities that point to freed
    objects. When a recorded capability is either empty or points to a live
    object, [aux_holds] guarantees that the shadow slot in memory holds that
    exact capability. *)
Lemma aux_holds_live : forall m a c,
  aux_holds m a c -> (c = CNone \/ exists b reg, c = Obj b /\ live_at m b reg) -> m_aux m a = c.
Proof.
  intros m a c [E|((b & reg & Hc & E & L) & _)] Hc'; [exact E|].
  destruct Hc' as [->|(b' & reg' & -> & E' & L')]; [destruct Hc as [?|?]; discriminate|].
  destruct Hc as [Hc|Hc]; [|discriminate]. injection Hc as <-. congruence.
Qed.

(** Because the garbage collector never rewrites a capability unless its
    target object has been freed, any non-freed capability recorded for a
    shadow slot is stored verbatim at that address in memory. *)
Lemma aux_holds_kept : forall m a c,
  aux_holds m a c -> ~ freed_in (m_regions m) c -> m_aux m a = c.
Proof. intros m a c [E | (Hf & _)] Hn; [exact E | contradiction]. Qed.

(** When a pointer to a constant object such as a string literal is stored
    in memory, its capability is read-only. As long as that object is live,
    the garbage collector leaves its capability untouched, so reading the
    slot back returns that exact read-only capability. *)
Lemma aux_holds_ro : forall m a b reg,
  aux_holds m a (Ro b) -> live_at m b reg -> m_aux m a = Ro b.
Proof.
  intros m a b reg [E | ((b' & reg' & Hc & Hr & Hf) & _)] [Hl HL]; [exact E|].
  destruct Hc as [Hc | Hc]; [discriminate|]. injection Hc as <-. congruence.
Qed.

(** ## Bytes

    When an instruction writes bytes or a capability into memory, we need to
    know that surrounding addresses and object regions remain unchanged.
    This section states the basic read-over-write and frame lemmas for byte
    and capability stores. *)

(** Storing a sequence of bytes at an address modifies only the bytes inside
    that range and leaves every byte outside the range unchanged. *)
Lemma store_bytes_other : forall m a size x a',
  ~ (a <= a' < a + size) -> m_bytes (store_bytes m a size x) a' = m_bytes m a'.
Proof.
  intros m a size x a' H. unfold store_bytes; cbn [m_bytes].
  destruct ((a <=? a') && (a' <? a + size)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(** Writing an unsigned 64-bit integer as 8 little-endian bytes and reading
    8 bytes back from the same address returns the original integer. *)
Lemma load_store_bytes : forall m a v, 0 <= v < 2 ^ 64 ->
  load_bytes (store_bytes m a 8 v) a 8 = v.
Proof.
  intros m a v Hv. rewrite stored_bytes_value by lia.
  change (256 ^ 8) with (2 ^ 64). apply Z.mod_small. exact Hv.
Qed.

(** Writing data bytes or a shadow capability into memory only updates the
    byte or capability map and leaves all object regions unchanged. *)
Lemma store_regions : forall m a size x c,
  m_regions (store_bytes m a size x) = m_regions m /\ m_regions (store_aux m a c) = m_regions m.
Proof. split; reflexivity. Qed.

(** ## Allocation

    When the program allocates a new object at a [[fresh]] base address, the
    memory gains a new live region without disturbing existing objects. This
    section shows how allocation updates the region table and preserves
    address disjointness among live objects. *)

(** After allocating a request at a base address, looking up that base
    identity returns the newly created live region, while looking up any
    other identity returns the region it had before. *)
Lemma object_region_allocated : forall m q base b,
  object_region b (m_regions (allocated m q base)) =
  if Z.eqb base b then Some (mkRegion base (base + req_extent q) (req_kind q) Live)
  else object_region b (m_regions m).
Proof. intros m q base b. reflexivity. Qed.

(** Because a [[fresh]] base address is chosen so that its byte range does
    not overlap any existing region, allocating a new object at a fresh base
    preserves [live_disjoint]. *)
Lemma live_disjoint_allocated : forall m q base,
  live_disjoint m -> fresh m q base -> 0 <= req_extent q -> live_disjoint (allocated m q base).
Proof.
  intros m q base Hd Hf Hq b1 r1 b2 r2 [E1 L1] [E2 L2] Hne.
  destruct Hf as (_ & _ & _ & _ & Hover & _).
  rewrite object_region_allocated in E1, E2.
  destruct (Z.eqb_spec base b1) as [<-|N1]; destruct (Z.eqb_spec base b2) as [<-|N2].
  - congruence.
  - injection E1 as <-. cbn [r_end].
    specialize (Hover b2 r2 E2). destruct (Z_le_gt_dec (base + req_extent q) b2); [left; lia|].
    destruct (Z_le_gt_dec (r_end r2) base); [right; lia|]. exfalso. apply Hover. lia.
  - injection E2 as <-. cbn [r_end].
    specialize (Hover b1 r1 E1). destruct (Z_le_gt_dec (r_end r1) base); [left; lia|].
    destruct (Z_le_gt_dec (base + req_extent q) b1); [right; lia|]. exfalso. apply Hover. lia.
  - exact (Hd b1 r1 b2 r2 (conj E1 L1) (conj E2 L2) Hne).
Qed.

(** ## Safepoints

    At a [[poll|safepoint]], the Fil-C garbage collector may inspect memory
    and sweep capabilities to already-freed objects, but it never moves or
    deallocates live objects. This section packages the runtime's safepoint
    guarantees into the exact memory-preservation facts needed by the
    program logic. *)

(** The functor [SafepointShape] derives the memory-preservation properties
    of garbage-collection safepoints for any implementation of the [Runtime]
    interface. *)
Module SafepointShape (R : Runtime).

(** By the runtime interface in [Runtime](../core/Runtime.v), a
    garbage-collection safepoint never alters the region table, so every
    live object before a safepoint remains live with the same region after
    the safepoint. *)
Lemma keeps_live : forall s m s' m' b reg, R.safepoint s m s' m' ->
  object_region b (m_regions m) = Some reg -> r_life reg = Live ->
  object_region b (m_regions m') = Some reg.
Proof. intros s m s' m' b reg Hsp E _. rewrite (R.collector_live _ _ _ _ Hsp). exact E. Qed.

(** Every safepoint preserves all object regions and all data bytes, and
    modifies shadow capability slots only by sweeping dead capabilities as
    permitted by [aux_moves]. *)
Lemma safepoint_shape : forall s m s' m',
  R.safepoint s m s' m' -> same_regions m m' /\ m_bytes m' = m_bytes m /\ aux_moves m m'.
Proof.
  intros s m s' m' Hsp. split; [|split].
  - intros b. rewrite (R.collector_live _ _ _ _ Hsp). reflexivity.
  - exact (R.non_moving _ _ _ _ Hsp).
  - exact (R.aux_round_trip _ _ _ _ Hsp).
Qed.

(** Because a safepoint leaves every object's region bounds unchanged, live
    objects that were disjoint before the safepoint remain disjoint after
    it. *)
Lemma live_disjoint_safepoint : forall s m s' m',
  R.safepoint s m s' m' -> live_disjoint m -> live_disjoint m'.
Proof.
  intros s m s' m' Hsp Hd b1 r1 b2 r2 [E1 L1] [E2 L2].
  destruct (safepoint_shape _ _ _ _ Hsp) as (Hr & _).
  rewrite Hr in E1, E2. exact (Hd b1 r1 b2 r2 (conj E1 L1) (conj E2 L2)).
Qed.

End SafepointShape.

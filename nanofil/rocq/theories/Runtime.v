(** The runtime as axioms: Campaign 2's `Module Type Runtime`, and the
    interpreter's instance of it (docs/formal.md, docs/runtime-axioms.md).

    The model of the checked IR is about one thread's program. What the
    Fil-C runtime does around that program, where it puts a new object,
    what free does to an object's header, what the collector and other
    threads may do while the program waits at a safepoint, is not the
    model's to decide. `Runtime` states those facts as one page of
    axioms, read against the staging Fil-C the toolchain pins (mbrock/fil-c
    at `18b6663a2785c8eba6cc2a544a7711e19fc448c7`, the `coreRev` of
    lib/filc-staging.json). Each axiom has a native test in
    tests/c/prog/axiom-*.c that fails if it is stated in the obvious
    stronger way that the runtime does not promise.

    ## The axioms

    | Fact | Statement | Native test |
    |---|---|---|
    | `fresh_allocation` | an allocation's base is `fresh`: a new identity, aligned, overlapping no object, ending at or below 2^64, reading as zero | axiom-fresh.c |
    | `address_space` | every object ends at or below 2^48, native Fil-C's address space; an allocation the runtime cannot hold is refused, a trap | axiom-address.c |
    | `non_moving` | at a safepoint no byte moves or changes: the collector writes no object's contents | axiom-nonmoving.c |
    | `free_lifetime`, `safepoint_lifetime` | bounds change only by free, which empties a live heap object's | axiom-lifetime.c |
    | `safepoints` | the runtime acts only at instructions that are not evidence preserving | axiom-safepoint.c |
    | `retention` | free leaves an object's bytes and stored capabilities where they were | axiom-retention.c |
    | `aux_round_trip` | a stored capability stays, or becomes one that traps as the freed object does | axiom-aux.c |
    | `rooting` | no identity the program can name is reclaimed | axiom-rooting.c |

    Two more obligations are about the runtime's own state, not about
    Fil-C, so they have no native test: `ready_kept`, the program's own
    writes inside objects and its emptying of bounds leave the runtime
    ready to allocate; and `safepoint_ready`, the runtime's actions at a
    safepoint do too. With `fresh_allocation` they make `ready` an
    invariant of every run (Machine.v).

    ## One thread's view

    The model has one thread and no collector. Another thread's free and
    the collector's rewriting of stored capabilities are what the
    program sees change at a safepoint, the `safepoint` relation, and
    nowhere else. Natively another thread may free an object between a
    check and its access; `retention` and `non_moving` are what make
    that the same as a free at the next safepoint: the object's bytes
    stay where they were, readable through the capability the check
    passed, until the program next looks at the header.

    A freed object's address can be a new object's natively, once
    nothing names the old one. The model's `fresh` never reuses an
    identity, because a capability never dies in the model: the two
    agree on every capability a program still holds.

    ## Instances

    `InterpRuntime` is the interpreter's: interp.pl's allocator
    (`alloc_base/6`), free as Memory.v states it, and no other thread.
    It proves every axiom, so the module type is consistent. Run.v's
    `Driver` takes any `Runtime`; the extracted model is
    `Driver InterpRuntime` (Transport.v). Semantics.v calls Memory.v's
    `free_res`, which is `InterpRuntime.free`; the step relation takes
    `fresh` bases, which every runtime's `alloc` gives.

    `fresh_allocation` holds of a runtime's state that is `ready` for
    the memory: for the interpreter, every object lies below Next and
    nothing above it has been written. Machine.v proves that every step
    keeps it. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory.
Import ListNotations.
Open Scope Z_scope.

(** ## What the axioms speak of *)

(** `lifetime_step m m'`: every identity of m' was one of m, unchanged,
    or a live heap object now freed, its bounds empty. *)
Definition lifetime_step (m m' : mem) : Prop :=
  forall b reg',
    object_region b (m_regions m') = Some reg' ->
    exists reg,
      object_region b (m_regions m) = Some reg /\
      (reg' = reg \/
       (r_kind reg = Heap /\ r_life reg = Live /\ reg' = mkRegion b b Heap Freed)).

(** `freed_in rs c`: c is the capability of an object freed in rs. *)
Definition freed_in (rs : list region) (c : cap) : Prop :=
  exists b reg,
    (c = Obj b \/ c = Ro b) /\ object_region b rs = Some reg /\ r_life reg = Freed.

(** `traps_as_freed rs c`: every access through c traps out of bounds,
    as every access to a freed object does. The collector's free
    singleton is such a capability. *)
Definition traps_as_freed (rs : list region) (c : cap) : Prop :=
  forall a size r align, 0 < size -> cap_access_res c rs a size r align = Some (RTrap OutOfBounds).

(** `objects_fit rs`: every object of rs ends at or below 2^48, native
    Fil-C's address space (`PAS_ADDRESS_BITS`). An address inside one
    never wraps (`raw_address/3`), and two addresses of one object are
    less than 2^63 apart, so a near offset between them does not wrap
    either (`hull_covered/7`). *)
Definition objects_fit (rs : list region) : Prop :=
  forall b reg, object_region b rs = Some reg -> r_end reg <= 2 ^ 48.

(** `in_object m a`: a is inside the current bounds of an object of m. *)
Definition in_object (m : mem) (a : Z) : Prop :=
  exists b reg, object_region b (m_regions m) = Some reg /\ b <= a < r_end reg.

(** `region_step m m'`: every identity of m' was one of m, unchanged,
    or live and now ended, its bounds empty: a free, or the end of an
    invocation's locals. *)
Definition region_step (m m' : mem) : Prop :=
  forall b reg',
    object_region b (m_regions m') = Some reg' ->
    exists reg,
      object_region b (m_regions m) = Some reg /\
      (reg' = reg \/ (r_life reg = Live /\ reg' = mkRegion b b (r_kind reg) Freed)).

(** `kept m m'`: what the program itself may do to memory between
    allocations: end objects, and write bytes and stored capabilities
    inside objects' bounds. *)
Definition kept (m m' : mem) : Prop :=
  region_step m m' /\
  forall a, ~ in_object m a -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a.

(** ## The module type *)

Module Type Runtime.

  (** The runtime's own state, which the program never reads: the
      interpreter's Next. *)
  Parameter state : Type.
  Parameter start : state.

  (** `ready s m`: s may allocate in m. *)
  Parameter ready : state -> mem -> Prop.

  (** The base of a new object of q, and the state after it; `None`
      when the runtime cannot hold the object, which ends the run with
      `trap(out_of_memory)`. *)
  Parameter alloc : state -> alloc_req -> option (Z * state).

  Axiom fresh_allocation : forall s m q base s',
    ready s m ->
    0 < req_align q ->
    0 <= req_extent q ->
    alloc s q = Some (base, s') ->
    fresh m q base /\ ready s' (allocated m q base).

  (** No object of a memory the runtime is ready in ends past 2^48. *)
  Axiom address_space : forall s m, ready s m -> objects_fit (m_regions m).

  (** The program's own changes keep the runtime ready. *)
  Axiom ready_kept : forall s m m', ready s m -> kept m m' -> ready s m'.

  (** Free of a pointer word: its result, and the memory after it. *)
  Parameter free : word -> mem -> option (res unit * mem).

  Axiom free_lifetime : forall x m r m',
    free x m = Some (r, m') -> lifetime_step m m'.

  Axiom retention : forall x m r m',
    free x m = Some (r, m') -> m_bytes m' = m_bytes m /\ m_aux m' = m_aux m.

  (** `at_safepoint i`: the runtime may act, and another thread's
      effects become visible, at i. *)
  Parameter at_safepoint : inst -> bool.

  Axiom safepoints : forall i,
    at_safepoint i = true -> evidence_preserving i = false.

  (** `safepoint s m s' m'`: what the program may find changed when it
      reaches a safepoint in s with memory m. *)
  Parameter safepoint : state -> mem -> state -> mem -> Prop.

  Axiom safepoint_lifetime : forall s m s' m',
    safepoint s m s' m' -> lifetime_step m m'.

  Axiom non_moving : forall s m s' m',
    safepoint s m s' m' -> m_bytes m' = m_bytes m.

  Axiom aux_round_trip : forall s m s' m',
    safepoint s m s' m' ->
    forall a, m_aux m' a = m_aux m a \/
              (freed_in (m_regions m') (m_aux m a) /\
               traps_as_freed (m_regions m') (m_aux m' a)).

  Axiom rooting : forall s m s' m',
    safepoint s m s' m' ->
    forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.

  (** The runtime's actions keep it ready. *)
  Axiom safepoint_ready : forall s m s' m', safepoint s m s' m' -> ready s m -> ready s' m'.

End Runtime.

(** ## Facts about Memory.v *)

Lemma object_region_remove : forall b base rs,
  b <> base -> object_region b (remove_region base rs) = object_region b rs.
Proof.
  intros b base rs Hne. induction rs as [|r rs IH]; simpl; auto.
  destruct (Z.eqb (r_base r) base) eqn:E.
  - apply Z.eqb_eq in E. destruct (Z.eqb (r_base r) b) eqn:E2; auto.
    apply Z.eqb_eq in E2. lia.
  - simpl. destruct (Z.eqb (r_base r) b); auto.
Qed.

Lemma object_region_replace : forall base r rs rs' b,
  replace_region base r rs = Some rs' -> r_base r = base ->
  object_region b rs' = if Z.eqb b base then Some r else object_region b rs.
Proof.
  unfold replace_region. intros base r rs rs' b H Hr.
  destruct (object_region base rs); inversion H; subst; clear H. simpl.
  destruct (Z.eqb b (r_base r)) eqn:E.
  - apply Z.eqb_eq in E. subst. rewrite Z.eqb_refl. reflexivity.
  - assert (b <> r_base r) by (apply Z.eqb_neq; auto).
    destruct (Z.eqb (r_base r) b) eqn:E2.
    + apply Z.eqb_eq in E2. lia.
    + apply object_region_remove; auto.
Qed.

(** What `free_res` may do: free one live heap object, nothing else. *)
Lemma free_res_frees : forall x m r m',
  free_res x m = Some (r, m') ->
  m' = m \/
  exists base reg,
    object_region base (m_regions m) = Some reg /\ r_kind reg = Heap /\ r_life reg = Live /\
    replace_region base (mkRegion base base Heap Freed) (m_regions m) = Some (m_regions m') /\
    m_bytes m' = m_bytes m /\ m_aux m' = m_aux m.
Proof.
  intros x m r m' H.
  destruct x as [a | p | c size]; simpl in H; try discriminate.
  - inversion H; auto.
  - unfold cap_free_res in H. destruct (ptr_cap p) as [ | base | base | f | n ];
      try (inversion H; auto; fail); try discriminate;
      unfold object_free_res in H;
      destruct (Z.eqb (ptr_addr p) 0); try (inversion H; auto; fail);
      destruct (object_region base (m_regions m)) as [reg|] eqn:Ereg; try discriminate;
      destruct (kind_eqb (r_kind reg) Heap) eqn:Ek; simpl in H; try (inversion H; auto; fail);
      destruct (Z.eqb (ptr_addr p) base); simpl in H; try (inversion H; auto; fail);
      destruct (r_life reg) eqn:El; try (inversion H; auto; fail);
      destruct (replace_region base (mkRegion base base Heap Freed) (m_regions m)) as [rs|] eqn:Er;
      try discriminate; inversion H; subst; right; exists base, reg;
      (split; [auto|]); (split; [destruct (r_kind reg); simpl in Ek; congruence|]);
      simpl; auto.
Qed.

Lemma free_res_lifetime : forall x m r m',
  free_res x m = Some (r, m') -> lifetime_step m m'.
Proof.
  intros x m r m' H. destruct (free_res_frees x m r m' H) as [-> | (base & reg & Hreg & Hk & Hl & Hr & _)].
  - intros b reg' Hb. exists reg'. auto.
  - intros b reg' Hb. rewrite (object_region_replace _ _ _ _ b Hr eq_refl) in Hb.
    destruct (Z.eqb b base) eqn:E.
    + apply Z.eqb_eq in E. subst. inversion Hb; subst. exists reg. auto.
    + exists reg'. auto.
Qed.

Lemma free_res_retention : forall x m r m',
  free_res x m = Some (r, m') -> m_bytes m' = m_bytes m /\ m_aux m' = m_aux m.
Proof.
  intros x m r m' H. destruct (free_res_frees x m r m' H) as [-> | (_ & _ & _ & _ & _ & _ & Hb & Ha)]; auto.
Qed.

(** ## The interpreter's runtime *)

(** a, rounded up to a multiple of a positive align, is at least a. *)
Lemma align_up_ge : forall a align, 0 < align -> a <= align_up a align.
Proof.
  intros a align H. unfold align_up.
  pose proof (Z.div_mod (a + align - 1) align ltac:(lia)).
  pose proof (Z.mod_pos_bound (a + align - 1) align H). nia.
Qed.

Lemma align_up_mod : forall a align, 0 < align -> align_up a align mod align = 0.
Proof. intros a align H. unfold align_up. apply Z.mod_mul. lia. Qed.

(** The interpreter's runtime is left unsealed, so that what it does
    at a safepoint (nothing) can be read off it (Persistence.v's
    `interp_spares`); Transport.v's `Driver InterpRuntime` and
    Persistence.v's `Persistence InterpRuntime` check it against
    `Runtime`. *)
Module InterpRuntime.

  (** interp.pl's Next. *)
  Definition state := Z.

  (** `stack_base/1`: allocations start at 2^32, above the data. *)
  Definition start : state := 2 ^ 32.

  (** `address_space/2`: Next stays at or below 2^48, libpas's address
      space (PAS_ADDRESS_BITS). *)
  Definition address_end : Z := 2 ^ 48.

  (** Every object lies below Next, Next within the address space, and
      nothing at or above Next has been written. *)
  Definition ready (next : state) (m : mem) : Prop :=
    0 < next <= address_end /\
    (forall b reg, object_region b (m_regions m) = Some reg -> b < next /\ r_end reg <= next) /\
    (forall a, next <= a -> m_bytes m a = 0 /\ m_aux m a = CNone).

  (** `alloc_base/6`: the request's alignment above Next; Next then
      moves past the object, rounded up to 16, and a 16-byte gap. Where
      that would pass the address space's end, the runtime is out of
      memory. *)
  Definition alloc (next : state) (q : alloc_req) : option (Z * state) :=
    let base := align_up next (req_align q) in
    let next' := base + align_up (req_extent q) 16 + 16 in
    if next' <=? address_end then Some (base, next') else None.

  Lemma fresh_allocation : forall s m q base s',
    ready s m ->
    0 < req_align q ->
    0 <= req_extent q ->
    alloc s q = Some (base, s') ->
    fresh m q base /\ ready s' (allocated m q base).
  Proof.
    intros next m q base s' (Hpos & Hobj & Hbytes) Ha He E. unfold alloc in E.
    destruct (_ <=? address_end) eqn:Hend in E; [|discriminate E].
    injection E as <- <-. apply Z.leb_le in Hend. unfold address_end in *.
    pose proof (align_up_ge next (req_align q) Ha) as Hb.
    pose proof (align_up_ge (req_extent q) 16 ltac:(lia)) as Hx.
    set (base := align_up next (req_align q)) in *.
    split.
    - unfold fresh. split; [lia|]. split; [apply align_up_mod; auto|]. split; [lia|]. split.
      { destruct (object_region base (m_regions m)) as [reg|] eqn:E; auto.
        destruct (Hobj _ _ E). lia. }
      split.
      { intros b reg E [H1 H2]. destruct (Hobj _ _ E). lia. }
      intros a Hr. apply Hbytes. lia.
    - unfold ready, allocated, address_end. simpl. split; [lia|]. split.
      + intros b reg E. destruct (Z.eqb base b) eqn:Eb.
        * injection E as <-. simpl. apply Z.eqb_eq in Eb. lia.
        * destruct (Hobj _ _ E). lia.
      + intros a Hr. apply Hbytes. lia.
  Qed.

  (** Objects end below Next, which is within 2^48. *)
  Lemma address_space : forall s m, ready s m -> objects_fit (m_regions m).
  Proof.
    intros next m (Hpos & Hobj & _) b reg E. destruct (Hobj _ _ E). unfold address_end in *. lia.
  Qed.

  (** Objects stay below Next as they end, and the program writes only
      inside them. *)
  Lemma ready_kept : forall s m m', ready s m -> kept m m' -> ready s m'.
  Proof.
    intros next m m' (Hpos & Hobj & Hbytes) (Hreg & Hout). split; [lia|]. split.
    - intros b reg' E. destruct (Hreg _ _ E) as (reg & E0 & Hr).
      destruct (Hobj _ _ E0). destruct Hr as [-> | (_ & ->)]; simpl; lia.
    - intros a Ha. assert (Hn : ~ in_object m a).
      { intros (b & reg & E & Hr). destruct (Hobj _ _ E). lia. }
      destruct (Hout a Hn) as [-> ->]. apply Hbytes. auto.
  Qed.

  (** Memory.v's free, the pinned runtime's as the interpreter has it. *)
  Definition free := free_res.

  Definition free_lifetime := free_res_lifetime.
  Definition retention := free_res_retention.

  (** The interpreter's runtime may act wherever the compiler does not
      promise that it cannot. *)
  Definition at_safepoint (i : inst) : bool := negb (evidence_preserving i).

  Lemma safepoints : forall i, at_safepoint i = true -> evidence_preserving i = false.
  Proof. unfold at_safepoint. intros i H. destruct (evidence_preserving i); auto. Qed.

  (** No other thread and no collector: nothing changes at a safepoint. *)
  Definition safepoint (s : state) (m : mem) (s' : state) (m' : mem) : Prop := s' = s /\ m' = m.

  Lemma safepoint_lifetime : forall s m s' m', safepoint s m s' m' -> lifetime_step m m'.
  Proof. intros s m s' m' [_ ->] b reg' H. exists reg'. auto. Qed.

  Lemma non_moving : forall s m s' m', safepoint s m s' m' -> m_bytes m' = m_bytes m.
  Proof. intros s m s' m' [_ ->]. reflexivity. Qed.

  Lemma aux_round_trip : forall s m s' m',
    safepoint s m s' m' ->
    forall a, m_aux m' a = m_aux m a \/
              (freed_in (m_regions m') (m_aux m a) /\
               traps_as_freed (m_regions m') (m_aux m' a)).
  Proof. intros s m s' m' [_ ->] a. auto. Qed.

  Lemma rooting : forall s m s' m',
    safepoint s m s' m' ->
    forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.
  Proof. intros s m s' m' [_ ->]. auto. Qed.

  Lemma safepoint_ready : forall s m s' m', safepoint s m s' m' -> ready s m -> ready s' m'.
  Proof. intros s m s' m' [-> ->]. auto. Qed.

End InterpRuntime.

(** A C program compiled by Nanofil runs alongside the Fil-C
    [[runtime]], which allocates new objects, deallocates heap objects
    when the program calls `c: free`, and runs the FUGC garbage
    collector at [[poll|safepoints]]. Rather than hard-coding a single
    allocator into the operational semantics, this module specifies what
    the formal model assumes of any Fil-C runtime as the module type
    [Runtime], and constructs the reference instance [InterpRuntime]
    used by the Prolog [[interpreter]].

    Each axiom in [Runtime] is checked against the pinned Fil-C runtime
    and paired with a native regression test under
    `tests/c/prog/axiom-*.c` that would fail if the axiom promised more
    than the real runtime guarantees.

    ## One thread's view

    The formal model describes the execution of a single program
    thread. When that thread reaches a garbage-collection
    [[poll|safepoint]], the collector may run; in the model, its visible
    effect is the [safepoint] relation, which can replace stored
    [[aux]] capabilities that point to already-freed objects with a
    capability that traps on every access, while leaving all object
    [[region|regions]] and data bytes unchanged.

    The Fil-C runtime never frees a live object on its own. An object's
    lifetime ends only when the program itself calls `c: free`, returns
    from a function with stack locals, or runs program-installed code
    such as a signal handler or another thread. Signal handlers run
    only at pollchecks, and concurrent threads are outside this
    single-threaded model; for multi-threaded programs, safety rests on
    Fil-C's hardware-level capability checks and memory [[retention]]
    of freed objects until collection. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory.
Import ListNotations.
Open Scope Z_scope.

(** ## What the axioms speak of

    Before stating the [Runtime] module type, we define the predicates
    on memory and regions that the axioms use to describe how
    deallocation, program stores, and garbage-collection safepoints may
    change memory. *)

(** A memory transition satisfies [lifetime_step] when every object
    registered in the new memory was already registered in the old
    memory with either the exact same region or, for a live heap
    object, an emptied [Freed] region. In particular, deallocation never
    creates a new object [[identity]]. *)
Definition lifetime_step (m m' : mem) : Prop :=
  forall b reg',
    object_region b (m_regions m') = Some reg' ->
    exists reg,
      object_region b (m_regions m) = Some reg /\
      (reg' = reg \/
       (r_kind reg = Heap /\ r_life reg = Live /\ reg' = mkRegion b b Heap Freed)).

(** A [[capability]] satisfies [freed_in] for a region list when it
    names an object region whose lifetime state is [Freed]. *)
Definition freed_in (rs : list region) (c : cap) : Prop :=
  exists b reg,
    (c = Obj b \/ c = Ro b) /\ object_region b rs = Some reg /\ r_life reg = Freed.

(** A [[capability]] satisfies [traps_as_freed] for a region list when
    every positive-size memory access through it traps with
    [OutOfBounds], just as any access to a freed object does. The
    garbage collector's free-singleton capability satisfies this
    predicate. *)
Definition traps_as_freed (rs : list region) (c : cap) : Prop :=
  forall a size r align, 0 < size -> cap_access_res c rs a size r align = Some (RTrap OutOfBounds).

(** A region list satisfies [objects_fit] when every registered object
    starts at a non-negative address and ends at or below `2 ^ 48`,
    which is the 48-bit address space of Fil-C's native allocator.
    Within that bound, addresses inside an object never wrap around
    `2 ^ 64`, and a wrapped negative address always fails the signed
    lower-bound test of a [[half_check|half check]]. *)
Definition objects_fit (rs : list region) : Prop :=
  forall b reg, object_region b rs = Some reg -> 0 <= b /\ r_end reg <= 2 ^ 48.

(** A region list satisfies [freed_empty] when every region marked
    [Freed] has its end address equal to its base address, giving it
    zero byte extent. *)
Definition freed_empty (rs : list region) : Prop :=
  forall b reg, object_region b rs = Some reg -> r_life reg = Freed -> r_end reg = b.

(** An address satisfies [in_object] when it falls within the current
    byte bounds of some registered object in memory. *)
Definition in_object (m : mem) (a : Z) : Prop :=
  exists b reg, object_region b (m_regions m) = Some reg /\ b <= a < r_end reg.

(** A memory transition satisfies [region_step] when every object in the
    new memory existed in the old memory either unchanged or with its
    formerly [Live] region emptied and marked [Freed]. Unlike
    [lifetime_step], [region_step] allows both heap objects and stack
    locals to end their lifetimes. *)
Definition region_step (m m' : mem) : Prop :=
  forall b reg',
    object_region b (m_regions m') = Some reg' ->
    exists reg,
      object_region b (m_regions m) = Some reg /\
      (reg' = reg \/ (r_life reg = Live /\ reg' = mkRegion b b (r_kind reg) Freed)).

(** When a program executes ordinary stores and returns between
    allocations, it writes only inside the bounds of existing objects
    and ends only existing object lifetimes. The predicate [kept]
    combines [region_step] with the requirement that bytes and shadow
    [[aux]] slots outside registered objects remain unchanged. *)
Definition kept (m m' : mem) : Prop :=
  region_step m m' /\
  forall a, ~ in_object m a -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a.

(** A deallocation function satisfies [frees_heap] when calling it on
    the null pointer succeeds without changing memory, and calling it on
    the base pointer of a non-null live [Heap] object empties and frees
    that object's region while leaving all other regions, bytes, and
    shadow capabilities unchanged. *)
Definition frees_heap (free : word -> mem -> option (res unit * mem)) : Prop :=
  (forall m, free (WPtr (mkPtr 0 CNone)) m = Some (ok, m)) /\
  forall m b reg, object_region b (m_regions m) = Some reg /\ r_life reg = Live ->
    r_kind reg = Heap -> b <> 0 ->
    exists rs, replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs /\
      free (WPtr (mkPtr b (Obj b))) m = Some (ok, mkMem (m_bytes m) rs (m_aux m)).

(** ## The module type

    The module type [Runtime] axiomatizes the three runtime services
    that interact with a running program: the object allocator, the
    `c: free` deallocator, and the garbage collector at
    [[poll|safepoints]]. Both the execution [Driver](Run.v) and the
    abstract [Machine](Machine.v) are parameterized over any
    implementation of [Runtime]. *)

(** Any module of type [Runtime] provides an allocator, a deallocator,
    and a safepoint relation that satisfy the memory-safety axioms
    below. *)
Module Type Runtime.

  (** The type [state] represents the runtime's private allocator and
      collector bookkeeping, which the program never reads directly. *)
  Parameter state : Type.

  (** The constant [start] is the initial runtime state at the
      beginning of a program run. *)
  Parameter start : state.

  (** The predicate [ready] states that the runtime's internal
      bookkeeping agrees with the current memory state, so the allocator
      can choose a [[fresh]] base address for the next allocation. *)
  Parameter ready : state -> mem -> Prop.

  (** Given the current runtime state and an allocation request, [alloc]
      either returns a new base address paired with the updated runtime
      state, or returns `None` when the allocator is out of memory. *)
  Parameter alloc : state -> alloc_req -> option (Z * state).

  (** Whenever the runtime is [ready] in memory and [alloc] grants an
      allocation request with positive alignment and non-negative
      extent, the returned base address satisfies [fresh] and the
      updated runtime state remains [ready] in the [allocated] memory.
      Although native Fil-C can reuse a physical address after the
      garbage collector proves no capability can reach the old object,
      the formal model keeps every capability alive forever and gives
      each allocation a distinct [[identity]]; native test
      `axiom-fresh.c` checks that a new allocation never aliases a
      reachable live object. *)
  Axiom fresh_allocation : forall s m q base s',
    ready s m ->
    0 < req_align q ->
    0 <= req_extent q ->
    alloc s q = Some (base, s') ->
    fresh m q base /\ ready s' (allocated m q base).

  (** Whenever the runtime is [ready] in a memory state, every
      registered object lies within the 48-bit native address space
      described by [objects_fit], as checked by native test
      `axiom-address.c`. *)
  Axiom address_space : forall s m, ready s m -> objects_fit (m_regions m).

  (** Whenever the runtime is [ready] in a memory state, every [Freed]
      object in that memory has empty bounds as required by
      [freed_empty]. *)
  Axiom freed_bounds : forall s m, ready s m -> freed_empty (m_regions m).

  (** When the runtime is [ready] in memory and the program modifies
      memory between allocations according to [kept], the runtime
      remains [ready] in the updated memory. *)
  Axiom ready_kept : forall s m m', ready s m -> kept m m' -> ready s m'.

  (** The function [free] executes a call to `c: free` on a pointer word
      and a memory state, returning a partial result and the updated
      memory state. *)
  Parameter free : word -> mem -> option (res unit * mem).

  (** Calling [free] changes object regions only as permitted by
      [lifetime_step]: it may empty and mark [Freed] a live heap object,
      and never registers a new object identity, as checked by
      `axiom-lifetime.c`. *)
  Axiom free_lifetime : forall x m r m',
    free x m = Some (r, m') -> lifetime_step m m'.

  (** Calling [free] leaves all data bytes and shadow [[aux]]
      capabilities unchanged, as checked by `axiom-retention.c`. Because
      freed memory is [[retention|retained]] while any capability can
      still name it, a raw access whose check passed before a concurrent
      free still reads valid bytes. *)
  Axiom retention : forall x m r m',
    free x m = Some (r, m') -> m_bytes m' = m_bytes m /\ m_aux m' = m_aux m.

  (** Calling [free] never removes an object [[identity]] from the
      region list; even the freed object's identity remains registered
      with empty bounds, as checked by `axiom-identity.c`. *)
  Axiom free_keeps_ids : forall x m r m',
    free x m = Some (r, m') ->
    forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.

  (** Calling [free] either succeeds or stops the program with a safety
      [[trap]], and never produces an [[unchecked]] fault, as checked by
      `axiom-free.c`. *)
  Axiom free_checked : forall x m w m', free x m <> Some (RUnchecked w, m').

  (** By [free_succeeds], calling [free] on a null pointer or on the
      base pointer of a live heap object always succeeds as specified by
      [frees_heap], as checked by `axiom-free-succeeds.c`. Calls to
      `c: free` on a global object, an interior pointer, or an
      already-freed object trap instead. *)
  Axiom free_succeeds : frees_heap free.

  (** The predicate [at_safepoint] tests whether the runtime may perform
      a garbage-collection handshake or pollcheck callback at a given
      instruction. *)
  Parameter at_safepoint : inst -> bool.

  (** In Fil-C, the garbage collector and signal handlers run only at
      explicit poll points such as function calls, allocations, pointer
      stores, and poll edges, as checked by `axiom-safepoint.c`. The
      axiom [safepoints] states that any instruction where the runtime
      may act has [evidence_preserving] equal to `false`, so the
      [[validator]] can safely keep check [[evidence]] across all other
      instructions. *)
  Axiom safepoints : forall i,
    at_safepoint i = true -> evidence_preserving i = false.

  (** The relation [safepoint] relates the runtime state and memory
      before a garbage-collection [[poll|safepoint]] to the runtime
      state and memory after the collector has acted. *)
  Parameter safepoint : state -> mem -> state -> mem -> Prop.

  (** At a safepoint, the garbage collector leaves the region list
      [m_regions] completely unchanged, as checked by
      `axiom-collector-live.c`. Any object that was live before a poll
      remains live with the exact same bounds after the poll. *)
  Axiom collector_live : forall s m s' m',
    safepoint s m s' m' -> m_regions m' = m_regions m.

  (** Because the garbage collector never alters any object's bounds or
      lifetime state at a safepoint, every safepoint transition also
      satisfies [lifetime_step]. *)
  Lemma safepoint_lifetime : forall s m s' m',
    safepoint s m s' m' -> lifetime_step m m'.
  Proof.
    intros s m s' m' H b reg' E. rewrite (collector_live s m s' m' H) in E. eauto.
  Qed.

  (** At a safepoint, the garbage collector neither moves objects nor
      modifies primary data bytes [m_bytes], as checked by
      `axiom-nonmoving.c`. *)
  Axiom non_moving : forall s m s' m',
    safepoint s m s' m' -> m_bytes m' = m_bytes m.

  (** At a safepoint, each stored [[capability]] in [m_aux] either
      remains unchanged or, if it pointed to an already-freed object, is
      replaced by the collector's free-singleton capability that
      satisfies [traps_as_freed], as checked by `axiom-aux.c`. *)
  Axiom aux_round_trip : forall s m s' m',
    safepoint s m s' m' ->
    forall a, m_aux m' a = m_aux m a \/
              (freed_in (m_regions m') (m_aux m a) /\
               traps_as_freed (m_regions m') (m_aux m' a)).

  (** Because [collector_live] preserves the region list across a
      safepoint, every object [[identity]] registered before the
      safepoint remains registered after it, matching
      `axiom-rooting.c`. *)
  Lemma rooting : forall s m s' m',
    safepoint s m s' m' ->
    forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.
  Proof. intros s m s' m' H b. rewrite (collector_live s m s' m' H). auto. Qed.

  (** Whenever the runtime is [ready] before a safepoint, its actions
      during the safepoint leave it [ready] in the resulting memory
      state. *)
  Axiom safepoint_ready : forall s m s' m', safepoint s m s' m' -> ready s m -> ready s' m'.

End Runtime.

(** ## Facts about Memory.v

    To show that the interpreter's deallocator [free_res] from
    [Memory](Memory.v) satisfies the deallocation axioms of [Runtime],
    we first prove how [remove_region] and [replace_region] affect
    region lookups, and then derive each deallocation property for
    [free_res]. *)

(** Removing the region for one base address from a region list leaves
    the lookup result of [object_region] unchanged for every other base
    address. *)
Lemma object_region_remove : forall b base rs,
  b <> base -> object_region b (remove_region base rs) = object_region b rs.
Proof.
  intros b base rs Hne. induction rs as [|r rs IH]; simpl; auto.
  destruct (Z.eqb (r_base r) base) eqn:E.
  - apply Z.eqb_eq in E. destruct (Z.eqb (r_base r) b) eqn:E2; auto.
    apply Z.eqb_eq in E2. lia.
  - simpl. destruct (Z.eqb (r_base r) b); auto.
Qed.

(** When [replace_region] replaces the region for a base address with a
    new region of that same base address, looking up that base returns
    the new region and looking up any other base returns its previous
    region. *)
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

(** Whenever [free_res] returns a result on a word and memory state, it
    either leaves memory completely unchanged or replaces a single live
    [Heap] region with an empty [Freed] region while keeping all bytes
    and shadow capabilities intact. *)
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

(** Deallocating a pointer with [free_res] only empties the bounds of a
    live heap object and never creates a new object, so the transition
    satisfies [lifetime_step]. *)
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

(** Deallocating a pointer with [free_res] never removes a registered
    object identity from the region list. *)
Lemma free_res_keeps_ids : forall x m r m',
  free_res x m = Some (r, m') ->
  forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.
Proof.
  intros x m r m' H b Hb. destruct (free_res_frees x m r m' H) as [-> | (base & reg & _ & _ & _ & Hr & _)]; [exact Hb|].
  rewrite (object_region_replace _ _ _ _ b Hr eq_refl). destruct (Z.eqb b base); [discriminate | exact Hb].
Qed.

(** Deallocating a pointer with [free_res] always returns either [ok] or
    a safety trap, and never returns an unchecked fault. *)
Lemma free_res_checked : forall x m w m', free_res x m <> Some (RUnchecked w, m').
Proof.
  intros x m w m' H. unfold free_res, cap_free_res, object_free_res in H.
  repeat match type of H with
         | context [match ?y with _ => _ end] => destruct y; try discriminate H
         end.
  all: injection H as H; discriminate H.
Qed.

(** Deallocating a pointer with [free_res] leaves all primary data bytes
    and shadow capability slots unchanged. *)
Lemma free_res_retention : forall x m r m',
  free_res x m = Some (r, m') -> m_bytes m' = m_bytes m /\ m_aux m' = m_aux m.
Proof.
  intros x m r m' H. destruct (free_res_frees x m r m' H) as [-> | (_ & _ & _ & _ & _ & _ & Hb & Ha)]; auto.
Qed.

(** Deallocating a null pointer or the base pointer of a live heap
    object with [free_res] always succeeds as described by
    [frees_heap]. *)
Lemma free_res_succeeds : frees_heap free_res.
Proof.
  split; [reflexivity|]. intros m b reg [Ereg Hlive] Hk Hb.
  unfold replace_region. rewrite Ereg. eexists. split; [reflexivity|].
  cbn. unfold object_free_res. rewrite (proj2 (Z.eqb_neq b 0) Hb). rewrite Ereg, Hk, Z.eqb_refl, Hlive. cbn.
  unfold replace_region. rewrite Ereg. reflexivity.
Qed.

(** ## The interpreter's runtime

    We now construct [InterpRuntime], the concrete instance of [Runtime]
    that implements the monotone bump allocator and single-threaded
    deallocator of the Prolog [[interpreter]]. Constructing
    [InterpRuntime] proves that the [Runtime] axioms are mutually
    consistent and provides the runtime used by the extracted reference
    runner. *)

(** Rounding an address up to a positive alignment with [align_up] never
    decreases the address, and always produces a multiple of that
    alignment. *)
Lemma align_up_ge : forall a align, 0 < align -> a <= align_up a align.
Proof.
  intros a align H. unfold align_up.
  pose proof (Z.div_mod (a + align - 1) align ltac:(lia)).
  pose proof (Z.mod_pos_bound (a + align - 1) align H). nia.
Qed.

Lemma align_up_mod : forall a align, 0 < align -> align_up a align mod align = 0.
Proof. intros a align H. unfold align_up. apply Z.mod_mul. lia. Qed.

(** The module [InterpRuntime] implements [Runtime] using the
    interpreter's monotone next-allocation cursor, the deallocator
    [free_res], and a no-op garbage collector at safepoints. *)
Module InterpRuntime.

  (** In [InterpRuntime], the private runtime [state] is the
      next-allocation address cursor, which begins at [start] above the
      static data segment and stays at or below the 48-bit limit
      [address_end]. *)
  Definition state := Z.
  Definition start : state := 2 ^ 32.
  Definition address_end : Z := 2 ^ 48.

  (** The interpreter's runtime cursor satisfies [ready] in memory when
      it lies between 0 and [address_end], every registered object lies
      below the cursor with empty bounds if freed, and all memory at or
      above the cursor holds zero bytes and [CNone] capabilities. *)
  Definition ready (next : state) (m : mem) : Prop :=
    0 < next <= address_end /\
    (forall b reg, object_region b (m_regions m) = Some reg ->
       0 <= b < next /\ r_end reg <= next /\ (r_life reg = Freed -> r_end reg = b)) /\
    (forall a, next <= a -> m_bytes m a = 0 /\ m_aux m a = CNone).

  (** Given the current cursor and an allocation request, [alloc] rounds
      the cursor up to the requested alignment for the new object's
      base, advances the cursor past the 16-byte-rounded object extent
      plus a 16-byte gap, and succeeds when the new cursor does not
      exceed [address_end]. *)
  Definition alloc (next : state) (q : alloc_req) : option (Z * state) :=
    let base := align_up next (req_align q) in
    let next' := base + align_up (req_extent q) 16 + 16 in
    if next' <=? address_end then Some (base, next') else None.

  (** Because all memory at or above the cursor is unwritten and owned
      by no existing object, placing a new allocation there produces a
      [fresh] base address and preserves [ready] for the advanced
      cursor. *)
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
        * injection E as <-. simpl. apply Z.eqb_eq in Eb. split; [lia|]. split; [lia | discriminate].
        * destruct (Hobj _ _ E) as (? & ? & Hf). split; [lia|]. split; [lia | exact Hf].
      + intros a Hr. apply Hbytes. lia.
  Qed.

  (** Because every registered object lies below the cursor and the
      cursor is at most `2 ^ 48`, all objects lie within the 48-bit
      address space and every freed object has empty bounds. *)
  Lemma address_space : forall s m, ready s m -> objects_fit (m_regions m).
  Proof.
    intros next m (Hpos & Hobj & _) b reg E. destruct (Hobj _ _ E) as (? & ? & _). unfold address_end in *. lia.
  Qed.

  Lemma freed_bounds : forall s m, ready s m -> freed_empty (m_regions m).
  Proof. intros next m (_ & Hobj & _) b reg E. exact (proj2 (proj2 (Hobj _ _ E))). Qed.

  (** When the program modifies memory within existing objects and ends
      object lifetimes according to [kept], all objects remain below the
      cursor and memory at or above the cursor stays unwritten,
      preserving [ready]. *)
  Lemma ready_kept : forall s m m', ready s m -> kept m m' -> ready s m'.
  Proof.
    intros next m m' (Hpos & Hobj & Hbytes) (Hreg & Hout). split; [lia|]. split.
    - intros b reg' E. destruct (Hreg _ _ E) as (reg & E0 & Hr).
      destruct (Hobj _ _ E0) as (? & ? & Hf). destruct Hr as [-> | (_ & ->)]; simpl.
      + split; [lia|]. split; [lia | exact Hf].
      + split; [lia|]. split; [lia | reflexivity].
    - intros a Ha. assert (Hn : ~ in_object m a).
      { intros (b & reg & E & Hr). destruct (Hobj _ _ E). lia. }
      destruct (Hout a Hn) as [-> ->]. apply Hbytes. auto.
  Qed.

  (** To deallocate a heap object, the interpreter calls [free_res],
      which satisfies all five deallocation properties proved above. *)
  Definition free := free_res.
  Definition free_lifetime := free_res_lifetime.
  Definition retention := free_res_retention.
  Definition free_keeps_ids := free_res_keeps_ids.
  Definition free_checked := free_res_checked.
  Definition free_succeeds := free_res_succeeds.

  (** In the single-threaded interpreter, potential safepoints are the
      instructions that do not preserve check evidence, and the garbage
      collector performs no memory changes at a safepoint. *)
  Definition at_safepoint (i : inst) : bool := negb (evidence_preserving i).

  Lemma safepoints : forall i, at_safepoint i = true -> evidence_preserving i = false.
  Proof. unfold at_safepoint. intros i H. destruct (evidence_preserving i); auto. Qed.

  Definition safepoint (s : state) (m : mem) (s' : state) (m' : mem) : Prop := s' = s /\ m' = m.

  Lemma collector_live : forall s m s' m', safepoint s m s' m' -> m_regions m' = m_regions m.
  Proof. intros s m s' m' [_ ->]. reflexivity. Qed.

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

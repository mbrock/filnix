(** The [[runtime|runtime as axioms]]: Campaign 2's module type
    [Runtime], and the [[interpreter]]'s instance of it
    ([formal.md](../../docs/formal.md),
    [runtime-axioms.md](../../docs/runtime-axioms.md), which gives each
    axiom's source in the runtime).

    The model of the [[stage|checked IR]] is about one thread's
    program. What the Fil-C runtime does around that program, where it
    puts a new object, what free does to an object's header, what the
    collector may do at a [[poll|safepoint]], is not the model's to
    decide. [Runtime] states those facts as one page of axioms, read against the staging Fil-C
    the toolchain pins (mbrock/fil-c at
    `18b6663a2785c8eba6cc2a544a7711e19fc448c7`, the `coreRev` of
    lib/filc-staging.json). Each axiom about Fil-C has a native test in
    tests/c/prog/axiom-*.c that fails if it is stated in the obvious
    stronger way that the runtime does not promise.

    ## One thread's view

    The model is one thread's. At a safepoint the collector acts, and
    what the program sees change there, the [safepoint] relation, is
    the collector's rewriting of stored capabilities to freed objects
    and nothing else: no region changes ([collector_live]). Fil-C's
    runtime never frees an object by itself. Only code the program
    brings in does: a signal handler it installed, which Fil-C runs
    only at pollchecks (tests/c/prog/axiom-safepoint.c), or a thread
    it started. Both are the program's code, not the runtime's, and a
    module that installs a handler or starts a thread calls an
    external with no contract, which ends its run in the model; a
    handler is to be verified as program code of its own. The model
    takes a run to be the program's whole execution after the trusted
    entry, with no handler installed and no other program thread when
    it starts: a constructor, a preloaded library or a native caller
    that installed one is outside it. A pointer store's aux exit is a
    native safepoint inside a check and its access, which the
    [[validator]] keeps facts across, so a handler a program installs
    could free a checked object there; a verified handler must not
    free an object whose check is in flight. Another
    thread is outside the model: its writes are ([non_moving] lets no
    byte change at a safepoint), and so are its frees, which natively
    show at any check, not only at a safepoint
    (tests/c/prog/axiom-threads.c). For a threaded program, native
    safety rests on Fil-C's own argument, not on the theorems proved
    over this module type: every check traps on a freed object, and an
    access whose check passed before the free reads retained memory
    ([retention]). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory.
Import ListNotations.
Open Scope Z_scope.

(** ## What the axioms speak of *)

(** How the [[runtime]]'s free may change objects, from memory m to m':
    every [[identity]] of m' was one of m, unchanged, or a live heap
    object now freed, its bounds empty. No identity appears. *)
Definition lifetime_step (m m' : mem) : Prop :=
  forall b reg',
    object_region b (m_regions m') = Some reg' ->
    exists reg,
      object_region b (m_regions m) = Some reg /\
      (reg' = reg \/
       (r_kind reg = Heap /\ r_life reg = Live /\ reg' = mkRegion b b Heap Freed)).

(** The [[capability]] c is that of an object freed in the
    [[region|regions]] rs. *)
Definition freed_in (rs : list region) (c : cap) : Prop :=
  exists b reg,
    (c = Obj b \/ c = Ro b) /\ object_region b rs = Some reg /\ r_life reg = Freed.

(** Every nonempty access through the capability c, in the regions rs,
    [[trap|traps]] out of bounds, as every access to a freed object
    does. The collector's free singleton is such a capability. *)
Definition traps_as_freed (rs : list region) (c : cap) : Prop :=
  forall a size r align, 0 < size -> cap_access_res c rs a size r align = Some (RTrap OutOfBounds).

(** Every object of the regions rs lies between 0 and 2^48, native
    Fil-C's address space (`PAS_ADDRESS_BITS`); a native address is
    unsigned, so no object starts below 0. An address inside one never
    wraps (`raw_address/3`), and two addresses of one object are less
    than 2^63 apart, so a near offset between them does not wrap either
    (`hull_covered/7`). A lower [[half check]] compares its address,
    read signed, with the object's base (`half_bound/6`), so an address
    that wrapped below 0 fails it. *)
Definition objects_fit (rs : list region) : Prop :=
  forall b reg, object_region b rs = Some reg -> 0 <= b /\ r_end reg <= 2 ^ 48.

(** Every freed object of the regions rs is empty. Free and the end of
    an invocation end an object's life and empty its bounds together
    ([lifetime_step], [region_step]). *)
Definition freed_empty (rs : list region) : Prop :=
  forall b reg, object_region b rs = Some reg -> r_life reg = Freed -> r_end reg = b.

(** The address a is inside the current bounds of an object of the
    memory m. *)
Definition in_object (m : mem) (a : Z) : Prop :=
  exists b reg, object_region b (m_regions m) = Some reg /\ b <= a < r_end reg.

(** How the program may change objects, from memory m to m': every
    [[identity]] of m' was one of m, unchanged, or live and now ended,
    its bounds empty: a free, or the end of an invocation's locals.
    Unlike [lifetime_step], an object of any kind may end. *)
Definition region_step (m m' : mem) : Prop :=
  forall b reg',
    object_region b (m_regions m') = Some reg' ->
    exists reg,
      object_region b (m_regions m) = Some reg /\
      (reg' = reg \/ (r_life reg = Live /\ reg' = mkRegion b b (r_kind reg) Freed)).

(** What the program itself may do to memory between allocations, from
    m to m': end objects ([region_step]), and write bytes and stored
    capabilities only inside objects' bounds. *)
Definition kept (m m' : mem) : Prop :=
  region_step m m' /\
  forall a, ~ in_object m a -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a.

(** ## The module type *)

(** What the model assumes of the Fil-C [[runtime]]: its allocator, its
    free, and what its collector may do at a [[poll|safepoint]]. A runtime is any module with these parts that
    proves these axioms; Run.v's [Driver] and Machine.v's [Machine] run
    over any of them. *)
Module Type Runtime.

  (** The runtime's own state, which the program never reads: the
      interpreter's Next. *)
  Parameter state : Type.

  (** The runtime's state when a run starts. *)
  Parameter start : state.

  (** The runtime in state s is [[ready]] to allocate in the memory m:
      its bookkeeping agrees with m, so a new object will be [fresh]
      there. For the interpreter, every object lies below Next and
      nothing above it has been written. *)
  Parameter ready : state -> mem -> Prop.

  (** The base of a new object for the request q, and the state after
      it; None when the runtime cannot hold the object, which ends the
      run with `trap(out_of_memory)`. *)
  Parameter alloc : state -> alloc_req -> option (Z * state).

  (** The allocator gives each new object an address no other object
      uses. Where the runtime in state s is ready in memory m, a
      request q with a positive alignment and an extent of at least 0
      that [alloc] grants gets a [fresh] base: a new [[identity]],
      aligned, overlapping no object, ending at or below 2^64, reading
      as zero with no stored capability; and the runtime is ready in
      the memory with the new object. The model needs it so that a new
      object cannot alias an old one, and so the step relation's
      choice of any fresh base covers every runtime.

      Natively a freed object's address can be a new object's once
      nothing names the old one; the model never reuses an identity,
      because a capability never dies in it. The two agree on whether
      each access through a capability the program still holds traps,
      not on its address bits after a collection. Native test:
      `axiom-fresh.c`. *)
  Axiom fresh_allocation : forall s m q base s',
    ready s m ->
    0 < req_align q ->
    0 <= req_extent q ->
    alloc s q = Some (base, s') ->
    fresh m q base /\ ready s' (allocated m q base).

  (** Every object lies in native Fil-C's address space: where the
      runtime in state s is ready in memory m, every object of m lies
      between 0 and 2^48 ([objects_fit]). The model needs it so that no
      address inside an object wraps and a wrapped address fails a
      lower [[half check]]; an allocation the runtime cannot hold is
      refused, a trap. Native test: `axiom-address.c`. *)
  Axiom address_space : forall s m, ready s m -> objects_fit (m_regions m).

  (** No freed object of a memory m the runtime is ready in has bounds
      ([freed_empty]). Every free and the end of every invocation empty
      them ([lifetime_step], [region_step]), so it constrains only the
      memory a run starts in. It is about the runtime's own
      bookkeeping, not Fil-C, so it has no native test. *)
  Axiom freed_bounds : forall s m, ready s m -> freed_empty (m_regions m).

  (** The program's own changes keep the runtime ready: if it is ready
      in m, and m' is m after the program wrote inside objects and
      ended some ([kept]), it is ready in m'. With
      [fresh_allocation] and [safepoint_ready] this makes [ready] hold
      in every state of a run (Machine.v). No native test: it is about
      the runtime's own bookkeeping. *)
  Axiom ready_kept : forall s m m', ready s m -> kept m m' -> ready s m'.

  (** Free of a pointer word: its result, and the memory after it. This
      is what a call of libc's `free` runs, the genv's [ge_free]. *)
  Parameter free : word -> mem -> option (res unit * mem).

  (** Free changes an object's bounds only by emptying a live heap
      object's, for every alias at once, and makes no new identity
      ([lifetime_step]). The model needs it so that a capability the
      program holds keeps its meaning across a free except for the
      freed object, whose every access then traps. Native test:
      `axiom-lifetime.c`. *)
  Axiom free_lifetime : forall x m r m',
    free x m = Some (r, m') -> lifetime_step m m'.

  (** Free changes no byte and no stored capability: a freed object's
      memory is retained while anything can name it. Machine.v uses it
      to show a free keeps the program's other memory; natively it is
      also what lets an access whose check passed before another
      thread's free read the same bytes. Native test: `axiom-retention.c`. *)
  Axiom retention : forall x m r m',
    free x m = Some (r, m') -> m_bytes m' = m_bytes m /\ m_aux m' = m_aux m.

  (** Free reclaims nothing: every [[identity]] before it is one after
      it, the freed object's too. Only the collector reclaims, at a
      safepoint ([rooting]), and natively only of objects nothing can
      name, whose regions the model keeps. With [fresh_allocation] this keeps a later
      allocation from taking a freed object's base. Native test:
      `axiom-identity.c`. *)
  Axiom free_keeps_ids : forall x m r m',
    free x m = Some (r, m') ->
    forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.

  (** Free frees or [[trap|traps]]; it never goes on having done
      something else, so it never answers [[unchecked]], which the
      model keeps for a broken pass. Native test: `axiom-free.c`. *)
  Axiom free_checked : forall x m w m', free x m <> Some (RUnchecked w, m').

  (** The runtime may act at the instruction i: the collector's
      handshake, a pollcheck callback, or a signal handler the program
      installed. Another thread's effects are outside the model (the
      header's One thread's view). *)
  Parameter at_safepoint : inst -> bool.

  (** The runtime acts only at instructions that are not
      `evidence_preserving/1`: calls, polls, alloc and the rest. The
      model needs it because the [[validator]] keeps [[evidence]]
      across every other instruction, which would be unsound if the
      runtime could free or rewrite memory there. Native test:
      `axiom-safepoint.c`. *)
  Axiom safepoints : forall i,
    at_safepoint i = true -> evidence_preserving i = false.

  (** What the program may find changed when it reaches a
      [[poll|safepoint]] with the runtime in state s and memory m: the
      runtime's state s' and memory m' after the collector acted. *)
  Parameter safepoint : state -> mem -> state -> mem -> Prop.

  (** At a safepoint no [[region]] changes: the collector frees no
      object, live or freed, and no identity appears. Natively the
      collector reclaims objects nothing can name; the model keeps
      their regions, as [fresh_allocation] explains. Only the program
      frees, by [free] or by code it brought in (a signal handler, a
      thread), and that is not the runtime's action. The model needs
      it so that an object live before a poll is live after it with
      the same bounds. Native test: `axiom-collector-live.c`. *)
  Axiom collector_live : forall s m s' m',
    safepoint s m s' m' -> m_regions m' = m_regions m.

  (** At a safepoint, as at a free, an object's bounds change only by
      a live heap object's being freed, and no identity appears
      ([lifetime_step]); at a safepoint none changes at all
      ([collector_live]). *)
  Lemma safepoint_lifetime : forall s m s' m',
    safepoint s m s' m' -> lifetime_step m m'.
  Proof.
    intros s m s' m' H b reg' E. rewrite (collector_live s m s' m' H) in E. eauto.
  Qed.

  (** At a safepoint no byte moves or changes: the collector writes no
      object's contents and no address word. The model needs it so that
      the bytes a check passed stay readable, unchanged, until the
      program next looks at the header. Native test:
      `axiom-nonmoving.c`. *)
  Axiom non_moving : forall s m s' m',
    safepoint s m s' m' -> m_bytes m' = m_bytes m.

  (** At a safepoint each stored [[capability]] (in the [[aux]]) stays,
      or, if its object was freed, becomes one that traps as a freed
      object does: the collector's free singleton. The model needs it
      so that a pointer loaded back after a collection behaves as the
      one stored, reading or trapping alike. Native test:
      `axiom-aux.c`. *)
  Axiom aux_round_trip : forall s m s' m',
    safepoint s m s' m' ->
    forall a, m_aux m' a = m_aux m a \/
              (freed_in (m_regions m') (m_aux m a) /\
               traps_as_freed (m_regions m') (m_aux m' a)).

  (** At a safepoint the collector reclaims no [[identity]] the program
      can name: every object of m is still one of m'. The model needs
      it because a capability never dies in the model, so the object it
      names must stay. It follows from [collector_live]. Native test:
      `axiom-rooting.c`. *)
  Lemma rooting : forall s m s' m',
    safepoint s m s' m' ->
    forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.
  Proof. intros s m s' m' H b. rewrite (collector_live s m s' m' H). auto. Qed.

  (** The runtime's actions at a safepoint keep it [[ready]]. With
      [fresh_allocation] and [ready_kept] this makes [ready] hold in
      every state of a run (Machine.v). No native test: it is about the
      runtime's own bookkeeping. *)
  Axiom safepoint_ready : forall s m s' m', safepoint s m s' m' -> ready s m -> ready s' m'.

End Runtime.

(** ## Facts about Memory.v *)

(** Removing the object at base from the regions rs leaves every other
    base b's object as it was. *)
Lemma object_region_remove : forall b base rs,
  b <> base -> object_region b (remove_region base rs) = object_region b rs.
Proof.
  intros b base rs Hne. induction rs as [|r rs IH]; simpl; auto.
  destruct (Z.eqb (r_base r) base) eqn:E.
  - apply Z.eqb_eq in E. destruct (Z.eqb (r_base r) b) eqn:E2; auto.
    apply Z.eqb_eq in E2. lia.
  - simpl. destruct (Z.eqb (r_base r) b); auto.
Qed.

(** If replacing the object at base by the region r, whose base is
    base, gives rs', then the object at base in rs' is r and every
    other object is as in rs. *)
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

(** What Memory.v's [free_res] (`free_res/4`) may do: change nothing,
    or free one live heap object, emptying its bounds, and change
    nothing else. *)
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

(** [free_res] changes objects only as [lifetime_step] allows: the
    interpreter's proof of [free_lifetime]. *)
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

(** Every [[identity]] before a [free_res] is one after it: the
    interpreter's proof of [free_keeps_ids]. *)
Lemma free_res_keeps_ids : forall x m r m',
  free_res x m = Some (r, m') ->
  forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.
Proof.
  intros x m r m' H b Hb. destruct (free_res_frees x m r m' H) as [-> | (base & reg & _ & _ & _ & Hr & _)]; [exact Hb|].
  rewrite (object_region_replace _ _ _ _ b Hr eq_refl). destruct (Z.eqb b base); [discriminate | exact Hb].
Qed.

(** [free_res] (`free_res/4`) answers ok or a [[trap]], never
    [[unchecked]]: the interpreter's proof of [free_checked]. *)
Lemma free_res_checked : forall x m w m', free_res x m <> Some (RUnchecked w, m').
Proof.
  intros x m w m' H. unfold free_res, cap_free_res, object_free_res in H.
  repeat match type of H with
         | context [match ?y with _ => _ end] => destruct y; try discriminate H
         end.
  all: injection H as H; discriminate H.
Qed.

(** [free_res] changes no byte and no stored capability: the
    interpreter's proof of [retention]. *)
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

(** a, rounded up to a multiple of a positive align, is a multiple of
    align. *)
Lemma align_up_mod : forall a align, 0 < align -> align_up a align mod align = 0.
Proof. intros a align H. unfold align_up. apply Z.mod_mul. lia. Qed.

(** The [[interpreter]]'s runtime: interp.pl's allocator
    (`alloc_base/6`), free as Memory.v states it ([free_res]), and no
    other thread or collector. It proves every axiom, so the module
    type is consistent; the extracted model is [Driver InterpRuntime]
    (Transport.v). It is left unsealed, so that what it does can be
    read off it; Transport.v's [Driver InterpRuntime] and
    Persistence.v's [Persistence InterpRuntime] check it against
    [Runtime]. *)
Module InterpRuntime.

  (** interp.pl's Next. *)
  Definition state := Z.

  (** As `stack_base/1`: allocations start at 2^32, above the data. *)
  Definition start : state := 2 ^ 32.

  (** As `address_space/2`: Next stays at or below 2^48, libpas's
      address space (`PAS_ADDRESS_BITS`). *)
  Definition address_end : Z := 2 ^ 48.

  (** The interpreter, its Next being next, is [[ready]] in m: every
      object lies between 0 and Next, empty if freed, Next is within the
      address space, and nothing at or above Next has been written. *)
  Definition ready (next : state) (m : mem) : Prop :=
    0 < next <= address_end /\
    (forall b reg, object_region b (m_regions m) = Some reg ->
       0 <= b < next /\ r_end reg <= next /\ (r_life reg = Freed -> r_end reg = b)) /\
    (forall a, next <= a -> m_bytes m a = 0 /\ m_aux m a = CNone).

  (** As `alloc_base/6`: the base is Next rounded up to the request's
      alignment; Next then moves past the object, rounded up to 16, and
      a 16-byte gap. Where that would pass the address space's end, the
      runtime is out of memory. *)
  Definition alloc (next : state) (q : alloc_req) : option (Z * state) :=
    let base := align_up next (req_align q) in
    let next' := base + align_up (req_extent q) 16 + 16 in
    if next' <=? address_end then Some (base, next') else None.

  (** The interpreter's allocator gives a [fresh] base and stays ready:
      everything at or above Next is unwritten and owned by no object,
      and the new object lies there. *)
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

  (** Objects lie between 0 and Next, which is within 2^48. *)
  Lemma address_space : forall s m, ready s m -> objects_fit (m_regions m).
  Proof.
    intros next m (Hpos & Hobj & _) b reg E. destruct (Hobj _ _ E) as (? & ? & _). unfold address_end in *. lia.
  Qed.

  (** A freed object of a memory the interpreter is ready in is empty,
      as [ready] says. *)
  Lemma freed_bounds : forall s m, ready s m -> freed_empty (m_regions m).
  Proof. intros next m (_ & Hobj & _) b reg E. exact (proj2 (proj2 (Hobj _ _ E))). Qed.

  (** Objects stay below Next as they end, and the program writes only
      inside them. *)
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

  (** Memory.v's free, the pinned runtime's as the interpreter has it. *)
  Definition free := free_res.

  (** Free empties only a live heap object's bounds:
      [free_res_lifetime]. *)
  Definition free_lifetime := free_res_lifetime.
  (** Free changes no byte and no stored capability:
      [free_res_retention]. *)
  Definition retention := free_res_retention.
  (** Free reclaims no identity: [free_res_keeps_ids]. *)
  Definition free_keeps_ids := free_res_keeps_ids.
  (** Free never answers unchecked: [free_res_checked]. *)
  Definition free_checked := free_res_checked.

  (** The interpreter's runtime may act wherever the compiler does not
      promise that it cannot. *)
  Definition at_safepoint (i : inst) : bool := negb (evidence_preserving i).

  (** A safepoint of the interpreter's runtime is not evidence
      preserving, by its definition. *)
  Lemma safepoints : forall i, at_safepoint i = true -> evidence_preserving i = false.
  Proof. unfold at_safepoint. intros i H. destruct (evidence_preserving i); auto. Qed.

  (** No other thread and no collector: nothing changes at a safepoint. *)
  Definition safepoint (s : state) (m : mem) (s' : state) (m' : mem) : Prop := s' = s /\ m' = m.

  (** Nothing changes at a safepoint, so no region does. *)
  Lemma collector_live : forall s m s' m', safepoint s m s' m' -> m_regions m' = m_regions m.
  Proof. intros s m s' m' [_ ->]. reflexivity. Qed.

  (** Nothing changes at a safepoint, so no object does. *)
  Lemma safepoint_lifetime : forall s m s' m', safepoint s m s' m' -> lifetime_step m m'.
  Proof. intros s m s' m' [_ ->] b reg' H. exists reg'. auto. Qed.

  (** Nothing changes at a safepoint, so no byte does. *)
  Lemma non_moving : forall s m s' m', safepoint s m s' m' -> m_bytes m' = m_bytes m.
  Proof. intros s m s' m' [_ ->]. reflexivity. Qed.

  (** Nothing changes at a safepoint, so every stored capability
      stays. *)
  Lemma aux_round_trip : forall s m s' m',
    safepoint s m s' m' ->
    forall a, m_aux m' a = m_aux m a \/
              (freed_in (m_regions m') (m_aux m a) /\
               traps_as_freed (m_regions m') (m_aux m' a)).
  Proof. intros s m s' m' [_ ->] a. auto. Qed.

  (** Nothing changes at a safepoint, so no identity is reclaimed. *)
  Lemma rooting : forall s m s' m',
    safepoint s m s' m' ->
    forall b, object_region b (m_regions m) <> None -> object_region b (m_regions m') <> None.
  Proof. intros s m s' m' [_ ->]. auto. Qed.

  (** Nothing changes at a safepoint, so the runtime stays ready. *)
  Lemma safepoint_ready : forall s m s' m', safepoint s m s' m' -> ready s m -> ready s' m'.
  Proof. intros s m s' m' [-> ->]. auto. Qed.

End InterpRuntime.

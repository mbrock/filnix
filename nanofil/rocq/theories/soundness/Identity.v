(** When a program reuses an earlier bounds check, it assumes the checked
    memory object still exists at the same base address. If `free` or the
    garbage collector reassigned that base to a new allocation, an old
    [[capability]] could access the new object instead of trapping.

    This file proves that every existing object keeps its [[identity]] along
    any [[run]] that starts [[ready]]. Because each object stays in memory
    unchanged or becomes freed in place, memory [persists] across steps and
    any reused bounds [[check]] either passes again or traps out of bounds.
    The main theorem [mreachable_persists] supports the soundness proof in
    [formal.md](../../../docs/formal.md#campaign-3-the-soundness-theorem)
    and [rocq.md](../../../docs/rocq.md#identities-persist).

    ## Decisions

    Three design choices shape this proof. First, freeing an object must
    leave its entry in the region table rather than deleting it. The
    runtime axiom [free_keeps_ids] provides that guarantee directly, whereas
    [free_lifetime] only checks that surviving regions existed earlier.

    Second, every [[fresh]] allocation must pick an unused base address so
    old capabilities never alias new objects. Third, persistence compares
    region lists directly rather than memory bytes, because [kept] already
    constrains where steps may write. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine.
Import ListNotations.
Open Scope Z_scope.

(** ## Identities persist

    To prove that reused checks stay sound across execution, we first define
    what it means for memory to keep every object's [[identity]] across a
    step. Each object in the old memory must remain in the new memory either
    unchanged or freed in place with empty bounds. *)

(** A memory transition satisfies [ids] when every base that names a
    [[region]] in m still names a region in m', even if its bounds or
    lifetime state changed. *)
Definition ids (m m' : Memory.mem) : Prop :=
  forall b reg, object_region b (m_regions m) = Some reg -> exists reg', object_region b (m_regions m') = Some reg'.

(** Freeing an object or ending its stack frame produces [freed_region],
    which keeps the same base and kind, sets the region's end to its base,
    and marks it [Freed] so any later access traps out of bounds. *)
Definition freed_region (reg : region) : region := mkRegion (r_base reg) (r_base reg) (r_kind reg) Freed.

(** An object's memory persists from m to m' when no base is ever lost or
    reassigned to another allocation. In [persists], every region in m
    appears in m' either identical or as its [freed_region], which allows
    [persists_access] to replay or trap earlier checks. *)
Definition persists (m m' : Memory.mem) : Prop :=
  forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg \/ object_region b (m_regions m') = Some (freed_region reg).

(** Looking up base b with [object_region] returns a region whose base
    field equals b. *)
Lemma object_region_base : forall b rs reg, object_region b rs = Some reg -> r_base reg = b.
Proof.
  intros b rs reg. induction rs as [|r rs IH]; simpl; [discriminate|].
  destruct (Z.eqb (r_base r) b) eqn:E; [intros H; injection H as <-; apply Z.eqb_eq; exact E | exact IH].
Qed.

(** Every memory persists from itself. *)
Lemma persists_refl : forall m, persists m m.
Proof. intros m b reg H. left. exact H. Qed.

(** Memory persistence is transitive: if m2 persists from m1 and m3 persists
    from m2, then m3 persists from m1. *)
Lemma persists_trans : forall m1 m2 m3, persists m1 m2 -> persists m2 m3 -> persists m1 m3.
Proof.
  intros m1 m2 m3 H12 H23 b reg H1. destruct (H12 _ _ H1) as [H2 | H2].
  - exact (H23 _ _ H2).
  - right. destruct (H23 _ _ H2) as [H3 | H3]; exact H3.
Qed.

(** Any memory m' with the same region list as m persists from m. *)
Lemma persists_same : forall m m', m_regions m' = m_regions m -> persists m m'.
Proof. intros m m' E b reg H. left. rewrite E. exact H. Qed.

(** When a transition only updates existing regions in place under
    [region_step] and keeps every base under [ids], the resulting memory
    [persists] from the original memory. *)
Lemma region_ids_persists : forall m m', region_step m m' -> ids m m' -> persists m m'.
Proof.
  intros m m' Hr Hi b reg H. destruct (Hi _ _ H) as [reg' H'].
  destruct (Hr _ _ H') as (reg0 & E0 & [-> | (_ & ->)]); rewrite H in E0; injection E0 as <-.
  - left. exact H'.
  - right. rewrite H'. unfold freed_region. rewrite (object_region_base _ _ _ H). reflexivity.
Qed.

(** A [lifetime_step] performed by `free` or a safepoint action preserves
    memory persistence whenever it keeps all object identities. *)
Lemma lifetime_ids_persists : forall m m', lifetime_step m m' -> ids m m' -> persists m m'.
Proof. intros m m' Hl Hi. exact (region_ids_persists _ _ (lifetime_region_step _ _ Hl) Hi). Qed.

(** Program steps between allocations satisfy [kept], so they preserve
    memory persistence whenever they keep all object identities. *)
Lemma kept_ids_persists : forall m m', kept m m' -> ids m m' -> persists m m'.
Proof. intros m m' [Hr _] Hi. exact (region_ids_persists _ _ Hr Hi). Qed.

(** Allocating a new object at a base unused in m leaves all prior objects
    untouched, so [allocated] persists from m. The [[runtime]]'s [[fresh]]
    allocator always selects such an unused base. *)
Lemma allocated_persists : forall m q base,
  object_region base (m_regions m) = None -> persists m (allocated m q base).
Proof.
  intros m q base Hn b reg H. left. simpl. destruct (Z.eqb base b) eqn:E; [|exact H].
  apply Z.eqb_eq in E. subst. rewrite Hn in H. discriminate H.
Qed.

(** ### Steps that write keep the regions *)

(** Writing bytes to memory with [store_res] updates contents only and
    leaves the region list unchanged. *)
Lemma store_res_regions : forall w m a c x r m', store_res w m a c x = Some (r, m') -> m_regions m' = m_regions m.
Proof. unfold store_res. intros w m a c x r m' H. destruct w, x; try discriminate; cases H; inversion H; reflexivity. Qed.

(** Folding a memory update over a list leaves the region list unchanged
    whenever each individual step preserves regions, which we use to
    reason about lists of store effects. *)
Lemma fold_regions : forall (A : Type) (f : Memory.mem -> A -> option Memory.mem) xs m0 m',
  (forall (m1 : Memory.mem) x m2, f m1 x = Some m2 -> m_regions m2 = m_regions m1) ->
  fold_left (fun acc x => let* m1 := acc in f m1 x) xs (Some m0) = Some m' -> m_regions m' = m_regions m0.
Proof.
  intros A f xs. induction xs as [|x xs IH]; simpl; intros m0 m' Hf H.
  - injection H as <-. reflexivity.
  - destruct (f m0 x) as [m1|] eqn:E.
    + rewrite (IH _ _ Hf H). exact (Hf _ _ _ E).
    + rewrite fold_left_none in H. discriminate H.
Qed.

(** Applying the byte and shadow effects of storing a pointer with
    [pointer_store_effects] leaves the region list unchanged. *)
Lemma pointer_store_effects_regions : forall a x m es m',
  pointer_store_effects a x m es = Some m' -> m_regions m' = m_regions m.
Proof.
  intros a x m es m' H. apply (fold_regions effect (pointer_store_effect a x) es m m'); [|exact H].
  intros m1 e m2 E. destruct e; simpl in E; try discriminate E; injection E as <-; reflexivity.
Qed.

(** Reading a variadic argument through [va_arg_res] may advance the
    argument cursor in memory, but it leaves the region list unchanged. *)
Lemma va_arg_res_regions : forall k p m r m', va_arg_res k p m = Some (r, m') -> m_regions m' = m_regions m.
Proof.
  unfold va_arg_res. intros k p m r m' H. cases H;
    match type of H with Some (_, ?x) = Some (_, ?y) => assert (x = y) as <- by congruence end;
    first [ reflexivity
          | match goal with E : store_res _ _ _ _ _ = Some _ |- _ => exact (store_res_regions _ _ _ _ _ _ _ E) end ].
Qed.

(** Evaluating any value-producing operation with [op_res] leaves the
    region list unchanged, because only allocation, `free`, and frame
    returns alter regions. *)
Lemma op_res_regions : forall o k xs m r m', op_res o k xs m = Some (OpRes r m') -> m_regions m' = m_regions m.
Proof.
  unfold op_res, float_integer. intros o k xs m r m' H.
  destruct o; cases H; inversion H; subst;
    first [ reflexivity
          | match goal with E : op_res_int _ _ _ _ = Some _ |- _ =>
              exact (proj2 (op_res_int_kept _ _ _ _ _ _ E)) end
          | match goal with E : va_arg_res _ _ _ = Some ?rm |- _ =>
              destruct rm; exact (va_arg_res_regions _ _ _ _ _ E) end ].
Qed.

(** Every memory keeps its own object identities. *)
Lemma ids_refl : forall m, ids m m.
Proof. intros m b reg H. eauto. Qed.

(** Identity preservation composes transitively across memories m1, m2, and
    m3. *)
Lemma ids_trans : forall m1 m2 m3, ids m1 m2 -> ids m2 m3 -> ids m1 m3.
Proof. intros m1 m2 m3 H12 H23 b reg H. destruct (H12 _ _ H) as [reg2 H2]. exact (H23 _ _ H2). Qed.

(** Any memory with the same region list as m keeps every object identity of
    m. *)
Lemma ids_same : forall m m', m_regions m' = m_regions m -> ids m m'.
Proof. intros m m' E b reg H. rewrite E. eauto. Qed.

(** When a function returns, [invalidate_locals] marks each stack-allocated
    local as freed in place without removing any region, so every
    [[identity]] is preserved. *)
Lemma invalidate_locals_ids : forall locals m m', invalidate_locals locals m = Some m' -> ids m m'.
Proof.
  unfold invalidate_locals. intros locals. induction locals as [|[x slot] ls IH]; simpl; intros m m' H.
  - injection H as <-. apply ids_refl.
  - destruct slot as [base|]; [|exact (IH _ _ H)].
    destruct (object_region base (m_regions m)) as [reg|] eqn:Er; simpl in H;
      [|rewrite fold_left_none in H; discriminate H].
    destruct (r_kind reg), (r_life reg); simpl in H; try (rewrite fold_left_none in H; discriminate H).
    destruct (replace_region base _ (m_regions m)) as [rs|] eqn:Ers; simpl in H;
      [|rewrite fold_left_none in H; discriminate H].
    eapply ids_trans; [|exact (IH _ _ H)]. intros b r0 Hb. simpl.
    rewrite (object_region_replace _ _ _ _ b Ers eq_refl). destruct (Z.eqb b base); eauto.
Qed.

(** ### A step keeps every identity *)

(** A `free` implementation satisfies [free_ids] when every freed object
    remains in the region list as a freed region rather than disappearing.
    The runtime axiom [free_keeps_ids] establishes this property for any
    runtime's `free` function in [R_free_ids]. *)
Definition free_ids (free : word -> Memory.mem -> option (res unit * Memory.mem)) : Prop :=
  forall x m r m', free x m = Some (r, m') -> ids m m'.

(** A normal instruction in [[frame]] fr that neither traps nor allocates
    keeps every object identity of memory m, provided the global
    environment's `free` function satisfies [free_ids]. *)
Lemma inst_step_ids : forall ge fr m i e l m',
  free_ids (ge_free ge) -> inst_step ge fr m i = Some (IContinue e l m') -> ids m m'.
Proof.
  intros ge fr m i e l m' Hfree H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst;
    first [ apply ids_refl
          | match goal with E : op_res _ _ _ _ = Some (OpRes _ _) |- _ =>
              exact (ids_same _ _ (op_res_regions _ _ _ _ _ _ E)) end
          | match goal with E : ge_free _ _ _ = Some (_, _) |- _ => exact (Hfree _ _ _ _ E) end
          | match goal with E : store_res _ _ _ _ _ = Some (_, _) |- _ =>
              exact (ids_same _ _ (store_res_regions _ _ _ _ _ _ _ E)) end
          | match goal with E : pointer_store_effects _ _ _ _ = Some _ |- _ =>
              exact (ids_same _ _ (pointer_store_effects_regions _ _ _ _ _ E)) end ].
Qed.

(** Returning from a call with [return_step] only frees the returning
    frame's locals in place, so it keeps every object identity. *)
Lemma return_step_ids : forall c o c', return_step c o = Next c' -> ids (c_mem c) (c_mem c').
Proof.
  unfold return_step. intros c o c' H. apply or_stuck_next in H.
  cases H; inversion H; subst; simpl.
  match goal with E : invalidate_locals _ _ = Some _ |- _ => exact (invalidate_locals_ids _ _ _ E) end.
Qed.

(** Executing a block jump with [jump_step] either branches without modifying
    memory or returns, so it keeps every object identity. *)
Lemma jump_step_ids : forall ge c l j c', jump_step ge c l j = Next c' -> ids (c_mem c) (c_mem c').
Proof.
  unfold jump_step, edge_step. intros ge c l j c' H.
  cases H; unstuck H.
  all: first
    [ match goal with E : return_step _ _ = Next _ |- _ => exact (return_step_ids _ _ _ E) end
    | inversion H; subst;
      first [ exact (ids_refl _)
            | match goal with E : return_step _ _ = Next _ |- _ => exact (return_step_ids _ _ _ E) end ] ].
Qed.

(** Any non-allocating configuration [[step]] preserves every object
    identity in memory whenever `ge`'s `free` function does. Allocation
    steps are proved separately in [step_fresh_regions]. *)
Lemma step_next_ids : forall ge c c',
  free_ids (ge_free ge) -> step ge c = Next c' -> ids (c_mem c) (c_mem c').
Proof.
  unfold step, inst_next. intros ge c c' Hfree H.
  cases H; unstuck H.
  all: first
    [ match goal with E : jump_step _ _ _ _ = Next _ |- _ => exact (jump_step_ids _ _ _ _ _ E) end
    | inversion H; subst; simpl; first
        [ exact (ids_refl _)
        | match goal with
          | E : doomed_result _ _ _ _ _ = Some ?od, Hc : fst ?od = IContinue _ _ _ |- _ =>
              destruct (doomed_result_out _ _ _ _ _ _ E) as [Ho | [(e' & l' & Ho) | (o' & Ho)]];
              rewrite Ho in Hc; try discriminate Hc;
              [ subst;
                match goal with E2 : inst_step _ _ _ _ = Some (IContinue _ _ _) |- _ =>
                  exact (inst_step_ids _ _ _ _ _ _ _ Hfree E2) end
              | inversion Hc; subst; apply ids_refl ]
          end ] ].
Qed.

(** When a variadic function enters, [snapshot_values] copies the incoming
    arguments into a new [[snapshot]] object without changing the region
    list. *)
Lemma snapshot_values_regions : forall xs a m, m_regions (snapshot_values xs a m) = m_regions m.
Proof.
  induction xs as [|x xs IH]; intros a m; simpl; [reflexivity|].
  destruct x; rewrite IH; reflexivity.
Qed.

(** Any allocating operation (`OpAlloc`) produces the exact memory
    [allocated] for the base chosen by the runtime, leaving every other
    region untouched. *)
Lemma op_res_alloc_exact : forall o k xs m q kont,
  op_res o k xs m = Some (OpAlloc q kont) -> forall base, snd (kont base) = allocated m q base.
Proof.
  unfold op_res, op_res_int, float_integer. intros o k xs m q kont H.
  destruct o; cases H; inversion H; subst. intros base. reflexivity.
Qed.

(** Executing an allocating instruction (`IFresh`) leaves the region list of
    [allocated] for whatever base the runtime picks, preserving all existing
    objects alongside the new one. *)
Lemma inst_step_fresh_regions : forall ge fr m i q k,
  inst_step ge fr m i = Some (IFresh q k) ->
  forall base, m_regions (snd (k base)) = m_regions (allocated m q base).
Proof.
  intros ge fr m i q k H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst; intros base.
  all: first
    [ reflexivity
    | match goal with E : op_res _ _ _ _ = Some (OpAlloc _ ?kont) |- _ =>
        pose proof (op_res_alloc_exact _ _ _ _ _ _ E base) as Ek;
        destruct (kont base) as [x m']; simpl in Ek |- *; rewrite Ek; reflexivity end ].
Qed.

(** Executing an allocating step (`Fresh`) adds one new object to the
    region list and drops none, matching [allocated] for whatever base the
    runtime picks. *)
Lemma step_fresh_regions : forall ge c q k,
  step ge c = Fresh q k -> forall base, m_regions (c_mem (k base)) = m_regions (allocated (c_mem c) q base).
Proof.
  unfold step, inst_next. intros ge c q k H.
  cases H; unstuck H;
    try (exfalso; exact (jump_step_not_fresh _ _ _ _ _ _ H)).
  all: injection H as Hq Hk; subst q k; intros base.
  - match goal with Hp : fr_at _ = Snapshot ?xs _ |- _ => exact (snapshot_values_regions xs base _) end.
  - match goal with
    | E : doomed_result _ _ _ _ _ = Some ?od, Hc : fst ?od = IFresh _ _ |- _ =>
        destruct (doomed_result_out _ _ _ _ _ _ E) as [Ho | [(e' & l' & Ho) | (o' & Ho)]];
        rewrite Ho in Hc; try discriminate Hc
    end.
    subst.
    match goal with E2 : inst_step _ _ _ _ = Some (IFresh _ ?k0) |- _ =>
      pose proof (inst_step_fresh_regions _ _ _ _ _ _ E2 base) as Hk end.
    simpl. match goal with Hk : m_regions (snd ?t) = _ |- _ => destruct t as [[e1 l1] m1] end. exact Hk.
Qed.

(** ## Replaying checks in persistent memory

    Once every object stays in memory either intact or freed in place, we
    can safely reuse earlier bounds checks. A nonempty check that passed
    against an object in an earlier memory cannot silently succeed against a
    different object later. *)

(** When a nonempty [[access]] check through [[capability]] c passed in
    memory m, [persists_access] proves that in any memory m' persisting from
    m, the same check either passes again or traps out of bounds because the
    object was freed. *)
Lemma persists_access : forall m m' a c size r al u,
  persists m m' -> 0 < size -> access_res m a c size r al = Some (RVal u) ->
  access_res m' a c size r al = Some (RVal u) \/ access_res m' a c size r al = Some (RTrap OutOfBounds).
Proof.
  unfold access_res, cap_access_res. intros m m' a c size r al u Hp Hs H.
  destruct c as [| base | base | f | n]; try discriminate H;
    destruct (object_region base (m_regions m)) as [reg|] eqn:E; try discriminate H;
    destruct (Hp _ _ E) as [E' | E']; rewrite E'; [left; exact H | right | left; exact H | right];
    pose proof (object_region_base _ _ _ E) as Hb; simpl; rewrite Hb;
    destruct ((base <=? a) && (a + size <=? base)) eqn:Eb; try reflexivity;
    apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia.
Qed.

(** ## Over runs *)

(** Lifting single-step persistence to whole executions connects the
    compiler's [[machine]] semantics to any [[runtime]] R. Starting from a
    [[ready]] state, every machine step and every reachable state along a
    run preserves object identities. *)
Module Identity (R : Runtime).

Module RM := Machine R.
Import RM.

(** By the runtime axiom [free_keeps_ids], `R.free` preserves every object
    identity because `free` only empties bounds and leaves reclamation to
    the collector at a safepoint. *)
Lemma R_free_ids : free_ids R.free.
Proof.
  intros x m r m' H b reg Hb. pose proof (R.free_keeps_ids _ _ _ _ H b) as Hk.
  destruct (object_region b (m_regions m')) as [reg'|]; [eauto|].
  exfalso. apply Hk; [rewrite Hb; discriminate | reflexivity].
Qed.

(** No single execution step can drop an object identity when the program
    uses the runtime's `free` function. In [mstep_persists], non-allocating
    steps free objects in place, allocations choose a [[fresh]] base, and
    safepoints preserve all identities by [rooting]. *)
Theorem mstep_persists : forall ge st st',
  ge_free ge = R.free -> ready_state st -> mstep ge st st' ->
  persists (c_mem (fst st)) (c_mem (fst st')).
Proof.
  unfold ready_state. intros ge st st' Hge Hr Hs.
  destruct Hs as [c c' s E | c q k s base s' E He Hal | c s s' m' _ Hsp]; simpl in *.
  - apply kept_ids_persists.
    + eapply step_next_kept; [rewrite Hge; exact free_kept | exact E].
    + eapply step_next_ids; [rewrite Hge; exact R_free_ids | exact E].
  - destruct (step_fresh_kept _ _ _ _ E) as [Ha _].
    destruct (R.fresh_allocation _ _ _ _ _ Hr Ha He Hal) as [(_ & _ & _ & Hnone & _) _].
    eapply persists_trans; [exact (allocated_persists _ q _ Hnone)|].
    apply persists_same. exact (step_fresh_regions _ _ _ _ E base).
  - apply lifetime_ids_persists; [exact (R.safepoint_lifetime _ _ _ _ Hsp)|].
    intros b reg H. pose proof (R.rooting _ _ _ _ Hsp b) as Hroot.
    destruct (object_region b (m_regions m')) as [reg'|] eqn:E'; [eauto|].
    exfalso. apply Hroot; [rewrite H; discriminate | reflexivity].
Qed.

(** Across any [[run]] of [Machine] R starting from a ready state,
    [mreachable_persists] proves that every reachable configuration's memory
    persists from the initial memory. *)
Theorem mreachable_persists : forall ge st st',
  ge_free ge = R.free -> mreachable ge st st' -> ready_state st ->
  persists (c_mem (fst st)) (c_mem (fst st')).
Proof.
  intros ge st st' Hge H. induction H as [st st' Hs | st | st1 st2 st3 H12 IH1 _ IH2]; intros Hr.
  - eapply mstep_persists; eauto.
  - apply persists_refl.
  - eapply persists_trans; [exact (IH1 Hr) | apply IH2; exact (mreachable_ready _ _ _ Hge H12 Hr)].
Qed.

End Identity.

(** Because the interpreter satisfies all runtime axioms directly, we can
    instantiate [Identity] with [InterpRuntime] to obtain persistence for
    interpreter runs. *)
Module InterpIdentity := Identity InterpRuntime.

(** Every ready run under the interpreter's runtime preserves memory
    persistence, requiring only that `ge` uses [InterpRuntime.free]. *)
Corollary interp_persists : forall ge st st',
  ge_free ge = InterpRuntime.free -> InterpIdentity.RM.mreachable ge st st' ->
  InterpIdentity.RM.ready_state st -> persists (c_mem (fst st)) (c_mem (fst st')).
Proof.
  intros ge st st' Hge H Hr. exact (InterpIdentity.mreachable_persists _ _ _ Hge H Hr).
Qed.

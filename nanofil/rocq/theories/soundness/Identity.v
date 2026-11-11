(** Objects last: what a run of [Machine] R, the [[machine]] over a
    [[runtime]] R, leaves of the objects it finds (docs/formal.md,
    Campaign 3; [docs/rocq.md, Identities persist](../../../docs/rocq.md#identities-persist)).

    The [[reuse]] forms trust a [[check]] that passed earlier, as long
    as the names it read are unchanged. That is sound only if the object
    it checked is still there when the reuse comes: as it was, so the
    check passes again, or freed, so it traps out of bounds. A run must
    never lose the object, or a new one could take its base and an old
    [[capability]] would name the new object. This file proves that
    memory [persists] over every run that starts [[ready]]
    ([mreachable_persists]): every object keeps its [[identity]].

    ## Decisions

    | Decision | Why |
    |---|---|
    | [free_ids] follows from an axiom | the module type's [free_lifetime] says each identity after a free was one before, not the reverse; [free_keeps_ids] (mbrock's decision, with axiom-identity.c) says the reverse, as [rooting] does at safepoints |
    | an allocation's base was no object's | [fresh] says so, which is what keeps an old capability from naming the new object |
    | the regions of a step are compared, not its bytes | [kept] already says where a step writes; identity is about the region list alone | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine.
Import ListNotations.
Open Scope Z_scope.

(** ## Identities persist *)

(** Every object of memory m is still an object of memory m': each base
    that names a [[region]] in m ([object_region]) names one in m',
    possibly changed. A step that satisfies this keeps every
    [[identity]]. *)
Definition ids (m m' : Memory.mem) : Prop :=
  forall b reg, object_region b (m_regions m) = Some reg -> exists reg', object_region b (m_regions m') = Some reg'.

(** The region reg as a free, or the end of its frame, leaves it: the
    same base and kind, its bounds emptied (its end at its base), and
    marked [Freed], so that every access to it traps out of bounds. *)
Definition freed_region (reg : region) : region := mkRegion (r_base reg) (r_base reg) (r_kind reg) Freed.

(** Each object of memory m is in memory m' as it was, or as its
    [freed_region]: nothing is lost, and no base is given to another
    object. This is how memory [[identity|persists]] along a run, and
    why a [[check]] that passed in m passes again in m' or traps
    ([persists_access]). *)
Definition persists (m m' : Memory.mem) : Prop :=
  forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg \/ object_region b (m_regions m') = Some (freed_region reg).

(** The region [object_region] finds for base b in a region list rs has
    base b. *)
Lemma object_region_base : forall b rs reg, object_region b rs = Some reg -> r_base reg = b.
Proof.
  intros b rs reg. induction rs as [|r rs IH]; simpl; [discriminate|].
  destruct (Z.eqb (r_base r) b) eqn:E; [intros H; injection H as <-; apply Z.eqb_eq; exact E | exact IH].
Qed.

(** A memory persists from itself. *)
Lemma persists_refl : forall m, persists m m.
Proof. intros m b reg H. left. exact H. Qed.

(** Persistence composes: if m2 persists from m1 and m3 from m2, then
    m3 persists from m1. *)
Lemma persists_trans : forall m1 m2 m3, persists m1 m2 -> persists m2 m3 -> persists m1 m3.
Proof.
  intros m1 m2 m3 H12 H23 b reg H1. destruct (H12 _ _ H1) as [H2 | H2].
  - exact (H23 _ _ H2).
  - right. destruct (H23 _ _ H2) as [H3 | H3]; exact H3.
Qed.

(** A memory m' with the same region list as m persists from m. *)
Lemma persists_same : forall m m', m_regions m' = m_regions m -> persists m m'.
Proof. intros m m' E b reg H. left. rewrite E. exact H. Qed.

(** A change of memory from m to m' persists where it is a
    [region_step] (each object of m' was one of m, unchanged or ended in
    place) and loses no identity ([ids]). These are what the program
    and the runtime may do to regions. *)
Lemma region_ids_persists : forall m m', region_step m m' -> ids m m' -> persists m m'.
Proof.
  intros m m' Hr Hi b reg H. destruct (Hi _ _ H) as [reg' H'].
  destruct (Hr _ _ H') as (reg0 & E0 & [-> | (_ & ->)]); rewrite H in E0; injection E0 as <-.
  - left. exact H'.
  - right. rewrite H'. unfold freed_region. rewrite (object_region_base _ _ _ H). reflexivity.
Qed.

(** The same for a [lifetime_step], what the [[runtime]]'s free and its
    safepoint action may do: with no identity lost, memory persists. *)
Lemma lifetime_ids_persists : forall m m', lifetime_step m m' -> ids m m' -> persists m m'.
Proof. intros m m' Hl Hi. exact (region_ids_persists _ _ (lifetime_region_step _ _ Hl) Hi). Qed.

(** The same for [kept], what the program's own steps between
    allocations may do to memory. *)
Lemma kept_ids_persists : forall m m', kept m m' -> ids m m' -> persists m m'.
Proof. intros m m' [Hr _] Hi. exact (region_ids_persists _ _ Hr Hi). Qed.

(** Adding a new object for the allocation request q at a base that no
    object of m has ([allocated] m q base) persists from m: no old object
    is touched. The runtime's [[fresh]] allocation gives such a base. *)
Lemma allocated_persists : forall m q base,
  object_region base (m_regions m) = None -> persists m (allocated m q base).
Proof.
  intros m q base Hn b reg H. left. simpl. destruct (Z.eqb base b) eqn:E; [|exact H].
  apply Z.eqb_eq in E. subst. rewrite Hn in H. discriminate H.
Qed.

(** ### Steps that write keep the regions *)

(** A store ([store_res], `store_res/7`) writes bytes but leaves the
    region list unchanged. *)
Lemma store_res_regions : forall w m a c x r m', store_res w m a c x = Some (r, m') -> m_regions m' = m_regions m.
Proof. unfold store_res. intros w m a c x r m' H. destruct w, x; try discriminate; cases H; inversion H; reflexivity. Qed.

(** Folding a memory update f over a list xs leaves the region list
    unchanged where each application of f does. A helper for lists of
    store effects. *)
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

(** The effects of storing the pointer x at address a
    ([pointer_store_effects], `pointer_store_effects//6`) leave the
    region list unchanged. *)
Lemma pointer_store_effects_regions : forall a x m es m',
  pointer_store_effects a x m es = Some m' -> m_regions m' = m_regions m.
Proof.
  intros a x m es m' H. apply (fold_regions effect (pointer_store_effect a x) es m m'); [|exact H].
  intros m1 e m2 E. destruct e; simpl in E; try discriminate E; injection E as <-; reflexivity.
Qed.

(** Reading a variadic argument through the argument pointer p
    ([va_arg_res]) leaves the region list unchanged, though it may write
    memory. *)
Lemma va_arg_res_regions : forall k p m r m', va_arg_res k p m = Some (r, m') -> m_regions m' = m_regions m.
Proof.
  unfold va_arg_res. intros k p m r m' H. cases H;
    match type of H with Some (_, ?x) = Some (_, ?y) => assert (x = y) as <- by congruence end;
    first [ reflexivity
          | match goal with E : store_res _ _ _ _ _ = Some _ |- _ => exact (store_res_regions _ _ _ _ _ _ _ E) end ].
Qed.

(** An op o that gives a result ([op_res] returning [OpRes]) leaves the
    region list unchanged: only allocation, free and the end of an
    invocation change regions. *)
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

(** A memory keeps its own identities. *)
Lemma ids_refl : forall m, ids m m.
Proof. intros m b reg H. eauto. Qed.

(** Keeping identities composes, from m1 to m2 to m3. *)
Lemma ids_trans : forall m1 m2 m3, ids m1 m2 -> ids m2 m3 -> ids m1 m3.
Proof. intros m1 m2 m3 H12 H23 b reg H. destruct (H12 _ _ H) as [reg2 H2]. exact (H23 _ _ H2). Qed.

(** A memory with the same region list as m keeps every identity of
    m. *)
Lemma ids_same : forall m m', m_regions m' = m_regions m -> ids m m'.
Proof. intros m m' E b reg H. rewrite E. eauto. Qed.

(** Ending an invocation's named locals as it returns, as
    `invalidate_locals/3` does, frees each in place and drops no object:
    every [[identity]] is kept. *)
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

(** A free function (from a pointer word and a memory to a result and a
    new memory) keeps every [[identity]]: what it frees stays an object,
    freed in place. The runtime axiom [free_keeps_ids] gives this of R's
    free ([R_free_ids]). *)
Definition free_ids (free : word -> Memory.mem -> option (res unit * Memory.mem)) : Prop :=
  forall x m r m', free x m = Some (r, m') -> ids m m'.

(** An instruction i of the [[frame]] fr that continues ([IContinue])
    with memory m' keeps every identity of m, where the free of the
    global environment ge ([ge_free]) does. *)
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

(** A return ([return_step]) from configuration c to c' keeps every
    identity: it only ends the returning frame's locals. *)
Lemma return_step_ids : forall c o c', return_step c o = Next c' -> ids (c_mem c) (c_mem c').
Proof.
  unfold return_step. intros c o c' H. apply or_stuck_next in H.
  cases H; inversion H; subst; simpl.
  match goal with E : invalidate_locals _ _ = Some _ |- _ => exact (invalidate_locals_ids _ _ _ E) end.
Qed.

(** A jump at the end of block l ([jump_step]) keeps every identity: it
    takes an edge, which leaves memory alone, or returns. *)
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

(** A [[step]] of configuration c that allocates nothing ([Next] c')
    keeps every identity of its memory, where ge's free does.
    Allocations are [step_fresh_regions]. *)
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

(** Storing the variadic arguments xs from address a
    ([snapshot_values], `snapshot_values/5`), as a variadic function's
    entry does into its new [[snapshot]] object, leaves the region list
    unchanged. *)
Lemma snapshot_values_regions : forall xs a m, m_regions (snapshot_values xs a m) = m_regions m.
Proof.
  induction xs as [|x xs IH]; intros a m; simpl; [reflexivity|].
  destruct x; rewrite IH; reflexivity.
Qed.

(** An op that allocates ([OpAlloc] with request q and continuation
    kont) leaves, for each base, exactly the memory [allocated] m q
    base: the new object, and no other change of memory. *)
Lemma op_res_alloc_exact : forall o k xs m q kont,
  op_res o k xs m = Some (OpAlloc q kont) -> forall base, snd (kont base) = allocated m q base.
Proof.
  unfold op_res, op_res_int, float_integer. intros o k xs m q kont H.
  destruct o; cases H; inversion H; subst. intros base. reflexivity.
Qed.

(** An instruction that allocates ([IFresh] q k) leaves, for whatever
    base the runtime picks, the region list of [allocated] m q base: the
    old objects and the new one. *)
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

(** A step that allocates ([Fresh] q k) does the same: whatever base the
    runtime gives, the next configuration's regions are the old ones
    with the new object added. An allocation adds one identity and
    drops none. *)
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

(** ## A check that passed passes again, or its object was freed *)

(** Where an [[access]] check of a nonempty range (size bytes at address
    a, through the [[capability]] c, with rights r and alignment al)
    passed in memory m, it passes the same way in any memory m' that
    persists from m, or traps out of bounds because the object was
    freed. This is what makes it sound to reuse a check. *)
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

(** Over the runs of [Machine] R, for any runtime R: each step from a
    [[ready]] state, and so each run that starts ready, persists
    memory. *)
Module Identity (R : Runtime).

Module RM := Machine R.
Import RM.

(** R's free keeps every identity, by the runtime axiom
    [free_keeps_ids]: free reclaims nothing; only the collector does, at
    a safepoint. *)
Lemma R_free_ids : free_ids R.free.
Proof.
  intros x m r m' H b reg Hb. pose proof (R.free_keeps_ids _ _ _ _ H b) as Hk.
  destruct (object_region b (m_regions m')) as [reg'|]; [eauto|].
  exfalso. apply Hk; [rewrite Hb; discriminate | reflexivity].
Qed.

(** Each [[machine]] step ([mstep]) from a state where R is ready
    ([ready_state]) persists memory, where the genv's free is R's: a
    step that allocates nothing ends objects in place, an allocation
    adds one at a [[fresh]] base, and R's safepoint action keeps every
    identity ([rooting]). *)
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

(** Over a [[run]] that starts ready, the memory of every later state
    ([mreachable]: any number of machine steps) persists from the
    first: each object is in every later state as it was, or freed. *)
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

(** The same for the interpreter's runtime [InterpRuntime], which proves
    every runtime axiom. *)
Module InterpIdentity := Identity InterpRuntime.

(** Under the interpreter's runtime, every run that starts ready
    persists memory, with no hypothesis but that the genv's free is the
    interpreter's. *)
Corollary interp_persists : forall ge st st',
  ge_free ge = InterpRuntime.free -> InterpIdentity.RM.mreachable ge st st' ->
  InterpIdentity.RM.ready_state st -> persists (c_mem (fst st)) (c_mem (fst st')).
Proof.
  intros ge st st' Hge H Hr. exact (InterpIdentity.mreachable_persists _ _ _ Hge H Hr).
Qed.

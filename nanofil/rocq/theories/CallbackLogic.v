(** Exact-state [[adequacy]] for retained void callbacks. The return
    postcondition observes the actual local teardown memory and CURRENT
    world, before [ReturnCallback] changes only the shutdown phase. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre adequacy.
From Stdlib Require Import ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Machine
  ExternalCalls ExternalMachine Shutdown Linked Pieces Heap Panics Language Logic.
Import ListNotations.
Open Scope Z_scope.

(** Callback proofs over any runtime, independently of libc's representation. *)
Module CallbackLogic (R : Runtime).
Module LG := Logic R.
Module L := LG.L.
Module LK := Linked R.
Import L LG L.RM.

(** Short local spelling of Linked's unchanged callback world type. *)
Local Notation cworld := LK.callback_world.

(** Linked and Language instantiate generative machine types separately;
    this changes only their constructor names, never their snapshots. *)
Definition logic_state {world : Type} (st : LK.M.state world) : M.state world :=
  match st with
  | LK.M.Running ms w => M.Running ms w
  | LK.M.Stopped why ms w => M.Stopped why ms w
  end.

(** Local transport for promotion: the two runtime instances admit the
    same external effects, with the same intermediate memories. *)
Lemma linked_effects sources roots releases requests s m born s' m' born' :
  LK.M.E.effects sources roots releases requests s m born s' m' born' ->
  M.E.effects sources roots releases requests s m born s' m' born'.
Proof.
  intros H. induction H.
  - constructor.
  - eapply M.E.effects_local; eauto.
  - eapply M.E.effects_alloc; eauto.
Qed.

(** Local transport for promotion: invocations keep their exact arguments,
    observations, runtime, memory and world across the module boundary. *)
Lemma linked_invoke {world : Type} (spec : contract world) r args xs s m w
    trace ending s' m' w' :
  LK.M.E.invoke spec r args xs s m w trace ending s' m' w' ->
  M.E.invoke spec r args xs s m w trace ending s' m' w'.
Proof.
  intros H. destruct H as
    [trace ending s' m' w' born Habi Hpre [He Hp] Hpost Hresource Hshape Hexit|
     why trace s' m' w' born Habi Hpre [He Hp] Hfailure Hresource].
  - eapply M.E.invoke_normal; eauto. split; [eapply linked_effects; exact He|exact Hp].
  - eapply M.E.invoke_resource; eauto.
    + split; [eapply linked_effects; exact He|exact Hp].
    + destruct Hfailure; [eapply M.E.failure_oom|eapply M.E.failure_big]; eauto.
Qed.

(** Local transport for promotion: a labelled step is unchanged except
    for the generative state constructors. *)
Lemma linked_step {world : Type} registry ge (st : LK.M.state world) trace st' :
  LK.M.step registry ge st trace st' ->
  M.step registry ge (logic_state st) trace (logic_state st').
Proof.
  intros H. destruct H; cbn [logic_state].
  - apply M.step_core. destruct H;
      [eapply M.P.I.RM.mstep_next|
       eapply M.P.I.RM.mstep_alloc|
       eapply M.P.I.RM.mstep_safepoint]; eauto.
  - eapply M.step_core_end; eauto.
  - eapply M.step_core_stuck; eauto.
  - eapply M.step_core_refusal; eauto.
  - eapply M.step_return; eauto using linked_invoke.
  - eapply M.step_exit; eauto using linked_invoke.
  - eapply M.step_resource; eauto using linked_invoke.
  - eapply M.step_rejected; eauto.
    destruct H0;
      [eapply M.reject_missing|eapply M.reject_arguments|
       eapply M.reject_abi|eapply M.reject_pre]; eauto.
  - eapply M.step_bad_return; eauto using linked_invoke.
Qed.

(** Local transport for promotion: every Linked run has the identical
    Language run, including its full trace and endpoint snapshots. *)
Lemma linked_run {world : Type} registry ge (st : LK.M.state world) trace st' :
  LK.M.run registry ge st trace st' ->
  M.run registry ge (logic_state st) trace (logic_state st').
Proof.
  intros H. induction H; [constructor|].
  econstructor; [eapply linked_step; eauto|exact IHrun].
Qed.

(** Local rule for promotion: unlike outcome-only [heap_labelled_safe],
    this keeps the final state interpretation together with the WP post.
    The existential heap in [heap_interp] is the one surviving execution. *)
Lemma heap_exact_adequacy Σ {HinvP : invGpreS Σ}
    {HheapP : gen_heapGpreS piece pval Σ}
    {world : Type} (registry : name -> option (contract world))
    (wi : mem -> world -> gmap piece pval -> Prop)
    ge fr m s (w : world) h0 fuel (Q : outcome -> lstate world -> Prop) :
  R.ready s m -> live_disjoint m -> agrees m h0 -> wi m w h0 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists Ψ : outcome -> iProp Σ,
      (([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
        let _ : irisGS_gen HasNoLc (nanofil_lang registry ge) Σ :=
          nanofil_irisGS registry wi ge in
        WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Ψ }}) /\
      (forall o σ, heap_interp wi σ ∗ Ψ o ⊢ ⌜Q o σ⌝)) ->
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr)
    (mkLstate m s fuel w) Q.
Proof.
  intros Hr Hd Ha Hw Hwp. apply adequate_alt.
  intros t2 σ2 Hsteps. apply erased_steps_nsteps in Hsteps.
  destruct Hsteps as [n [κs Hn]].
  eapply (wp_strong_adequacy_gen HasNoLc Σ _ NotStuck)
    with (num_laters_per_step := fun _ => 0%nat); [|exact Hn].
  intros HinvG.
  iMod (gen_heap_init h0) as (HheapG) "(Hh & Hpts & _)".
  destruct (Hwp HinvG HheapG) as (Ψ & Hbody & Hpost).
  iExists (fun σ _ _ _ => heap_interp wi σ), [Ψ], (fun _ => True%I), _.
  iSplitL "Hh".
  - iExists h0. iFrame "Hh". iPureIntro. exact (conj Ha (conj Hd (conj Hr Hw))).
  - iSplitL "Hpts".
    + cbn. iSplitL; [iApply Hbody; iExact "Hpts"|done].
    + iModIntro. iIntros (es' t2' -> Hlen Hsafe) "Hσ Hvals _".
      destruct es' as [|e es']; [discriminate Hlen|].
      destruct es'; [|discriminate Hlen].
      iApply fupd_mask_intro_discard; [set_solver|]. iSplit.
      * iIntros (v t He). injection He as He Ht. subst e.
        iEval (rewrite big_sepL2_cons to_of_val) in "Hvals".
        iDestruct "Hvals" as "[Hv _]".
        iApply (Hpost with "[$Hσ $Hv]").
      * iPureIntro. exact Hsafe.
Qed.

(** Local rule for promotion: any nonempty run has a final step and
    its actual prefix; this introduces no execution or termination premise. *)
Lemma run_last {world : Type} registry ge (start : M.state world) trace last :
  M.run registry ge start trace last ->
  start = last \/ exists prefix mid tail,
    M.run registry ge start prefix mid /\ M.step registry ge mid tail last.
Proof.
  intros Hrun. induction Hrun as [st|st tr mid tail last Hstep Hrun IH].
  - left. reflexivity.
  - right. destruct IH as [->|(prefix & before & ending & Hp & Hs)].
    + exists [], st, tr. split; [constructor|exact Hstep].
    + exists (tr ++ prefix), before, ending. split; [econstructor; eauto|exact Hs].
Qed.

(** Local rule for promotion: a stopped top-level void return reaches
    exactly the Iris state whose memory [invalidate_locals] produced. *)
Lemma callback_return_reachable {payload : Type} registry ge fr m s
    (w : cworld payload) fuel Q trace stopped entry ms' w' :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr)
    (mkLstate m s fuel w) Q ->
  LK.M.run registry ge (LK.M.Running (mkConfig fr [] m fuel, s) w) trace stopped ->
  LK.callback_return payload entry stopped ms' w' ->
  exists c sr wr m_return,
    stopped = LK.M.Stopped (CoreEnd RetVoid) (c, sr) wr /\
    c_callers c = [] /\
    invalidate_locals (fr_locals (c_frame c)) (c_mem c) = Some m_return /\
    ms' = (with_mem c m_return, sr) /\ fst w' = fst wr /\
    shutdown_step (snd wr) ReturnCallback (snd w') /\
    rtc (@erased_step (nanofil_lang registry ge))
      ([ERun fr], mkLstate m s fuel w)
      ([EEnd RetVoid], mkLstate m_return sr (c_fuel c) wr).
Proof.
  intros Had Hrun Hreturn.
  destruct (LK.callback_return_endpoint payload _ _ _ _ Hreturn)
    as (c & sr & wr & mr & -> & Hcs & Hi & Hms & Hw & Hshutdown).
  exists c, sr, wr, mr. repeat split; try assumption; try reflexivity.
  apply linked_run in Hrun. cbn [logic_state] in Hrun.
  destruct (run_last _ _ _ _ _ Hrun) as [Heq|(prefix & mid & tail & Hp & Hs)];
    [discriminate Heq|].
  inversion Hs; subst.
  match goal with E : Semantics.step ge c = Done RetVoid |- _ =>
    pose proof E as Hend end.
  destruct (adequate_labelled registry ge fr m s fuel w Q Had _ _ Hp) as [Hreach _].
  pose proof (Hreach c sr wr eq_refl) as Hiris.
  destruct c as [cf cs cm cfuel]. cbn in Hcs. subst cs.
  eapply rtc_r; [exact Hiris|].
  exact (head_erased registry ge [] _ _ _ _
    (hs_return registry ge cf cm sr cfuel wr RetVoid mr Hend I Hi)).
Qed.

(** Failure freedom is independent of a normal return: outcome-only
    [heap_labelled_safe] also covers callbacks that exit or never return. *)
Theorem callback_wp_safe Σ {HinvP : invGpreS Σ}
    {HheapP : gen_heapGpreS piece pval Σ}
    {payload : Type} (registry : name -> option (contract (cworld payload)))
    (wi : mem -> cworld payload -> gmap piece pval -> Prop)
    ge fr m s w h0 :
  R.ready s m -> live_disjoint m -> agrees m h0 -> wi m w h0 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    ([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
      let _ : irisGS_gen HasNoLc (nanofil_lang registry ge) Σ :=
        nanofil_irisGS registry wi ge in
      WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ _, True }}) ->
  forall fuel trace why ms' w',
    LK.M.run registry ge (LK.M.Running (mkConfig fr [] m fuel, s) w) trace
      (LK.M.Stopped why ms' w') -> ~ failure_ending why.
Proof.
  intros Hr Hd Ha Hw Hwp fuel trace why ms' w' Hrun.
  pose proof (heap_labelled_safe Σ registry wi ge fr m s w h0 (fun _ => True)
    Hr Hd Ha Hw Hwp fuel) as Hsafe.
  apply linked_run in Hrun. cbn [logic_state] in Hrun.
  exact (proj1 (Hsafe _ _ _ _ Hrun)).
Qed.

(** A handler's WP yields its pure postcondition at Linked's actual
    return memory and current world. No old payload, registry or status
    is restored, and no return is required of nonreturning executions. *)
Theorem callback_wp_return Σ {HinvP : invGpreS Σ}
    {HheapP : gen_heapGpreS piece pval Σ}
    {payload : Type} (registry : name -> option (contract (cworld payload)))
    (wi : mem -> cworld payload -> gmap piece pval -> Prop)
    ge fr m s w h0 (Q : mem -> cworld payload -> Prop) :
  R.ready s m -> live_disjoint m -> agrees m h0 -> wi m w h0 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists Ψ : outcome -> iProp Σ,
      (([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
        let _ : irisGS_gen HasNoLc (nanofil_lang registry ge) Σ :=
          nanofil_irisGS registry wi ge in
        WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Ψ }}) /\
      (forall σ, heap_interp wi σ ∗ Ψ RetVoid ⊢ ⌜Q (ls_mem σ) (ls_world σ)⌝)) ->
  forall fuel trace stopped entry ms' w',
    LK.M.run registry ge (LK.M.Running (mkConfig fr [] m fuel, s) w) trace stopped ->
    LK.callback_return payload entry stopped ms' w' ->
    exists c sr wr m_return,
      stopped = LK.M.Stopped (CoreEnd RetVoid) (c, sr) wr /\
      invalidate_locals (fr_locals (c_frame c)) (c_mem c) = Some m_return /\
      ms' = (with_mem c m_return, sr) /\ fst w' = fst wr /\
      shutdown_step (snd wr) ReturnCallback (snd w') /\ Q m_return wr.
Proof.
  intros Hr Hd Ha Hw Hwp fuel trace stopped entry ms' w' Hrun Hreturn.
  assert (Had : @adequate (nanofil_lang registry ge) NotStuck (ERun fr)
    (mkLstate m s fuel w)
    (fun o σ => o = RetVoid -> Q (ls_mem σ) (ls_world σ))).
  { eapply (heap_exact_adequacy Σ registry wi ge fr m s w h0 fuel);
      [exact Hr|exact Hd|exact Ha|exact Hw|].
    intros HinvG HheapG. destruct (Hwp HinvG HheapG) as (Ψ & Hbody & Hpost).
    exists Ψ. split; [exact Hbody|]. intros o σ.
    iIntros "H". iIntros (->). iApply Hpost. iExact "H". }
  destruct (callback_return_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ Had Hrun Hreturn)
    as (c & sr & wr & mr & Hst & Hcs & Hi & Hms & Hworld & Hshutdown & Hreach).
  exists c, sr, wr, mr. repeat split; try assumption.
  exact (adequate_result _ _ _ _ Had [] _ _ Hreach eq_refl).
Qed.

End CallbackLogic.

(** Spike: a ghost heap of pieces for the Iris instantiation of
    nanofil's machine (IrisLang.v), and the generic proof rules a program
    proof applies at each step. Nothing here is about one program.

    The ghost heap is Heap.v's (in theories/, taken from this file):
    Iris's [gen_heap] from Pieces.v's [piece] to a [pval], an object's
    life with its region, a byte, or a capability in an aux slot. The
    state interpretation [heap_interp] of a memory and a
    runtime state owns the authoritative heap h and says that h agrees
    with the memory ([agrees]: a life token names a live object; a byte
    or aux piece of a live object is inside its bounds and holds what
    the memory holds there, an aux slot up to the collector's rewriting
    of dead capabilities), that live objects do not overlap, and that
    the runtime is ready. Every piece of h names a registered object
    (part of [agree_piece]), so a fresh base has no pieces yet.

    The rules ([wpc_next], [wpc_done], [wpc_write], [wpc_alloc]) are all
    derived from one lifting lemma, [wpc_lift], which handles the
    safepoint: a safepoint step leaves the expression as it is and
    changes only memory, and no region of it (Runtime.v's
    [collector_live]), so it keeps [heap_interp] with the same ghost
    heap, and the lemma closes that case by Löb induction.
    [heap_never_panics] is IrisLang.v's adequacy with the ghost heap
    allocated: a program proof only proves [wpc] of its entry call. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls Ops Semantics Run
  Machine Panics Pieces Heap.
From Spike Require Import IrisLang.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The machine with a ghost heap *)

(** The ghost heap and the proof rules over any runtime R. *)
Module IrisHeap (R : Runtime).
Module IM := IrisMachine R.
Module SS := SafepointShape R.
Import IM.

(** A step that is not a safepoint: a machine step that allocates
    nothing, an allocation R grants, an allocation R refuses, or a
    non-failing ending. *)
Definition nosp_step (ge : genv) (c : config) (s : R.state) (e2 : expr) (σ2 : nstate) : Prop :=
  (exists c', Semantics.step ge c = Next c' /\ e2 = conf_expr c' /\ σ2 = (c_mem c', s)) \/
  (exists q k base s', Semantics.step ge c = Fresh q k /\ 0 <= req_extent q /\
     R.alloc s q = Some (base, s') /\ e2 = conf_expr (k base) /\ σ2 = (c_mem (k base), s')) \/
  (exists q k, Semantics.step ge c = Fresh q k /\ 0 <= req_extent q /\ R.alloc s q = None /\
     e2 = EEnd (Trap OutOfMemory) /\ σ2 = (c_mem c, s)) \/
  (exists o, Semantics.step ge c = Done o /\ ~ failure o /\ e2 = EEnd o /\ σ2 = (c_mem c, s)).

(** A primitive step of a configuration has no observation and no fork,
    and is a [nosp_step] or a safepoint, which keeps the expression. *)
Lemma prim_step_inv ge fr callers fuel m s κ e2 σ2 efs :
  prim_step ge (EConf fr callers fuel) (m, s) κ e2 σ2 efs ->
  κ = [] /\ efs = [] /\
  (nosp_step ge (mkConfig fr callers m fuel) s e2 σ2 \/
   exists s' m', R.safepoint s m s' m' /\ e2 = EConf fr callers fuel /\ σ2 = (m', s')).
Proof.
  intros H. inversion H; subst.
  - match goal with Hs : RM.mstep _ _ _ |- _ => inversion Hs; subst end.
    + split; [done|]. split; [done|]. left. left. eexists. split; [eassumption|]. split; reflexivity.
    + split; [done|]. split; [done|]. left. right. left. do 4 eexists.
      split; [eassumption|]. split; [assumption|]. split; [eassumption|]. split; reflexivity.
    + split; [done|]. split; [done|]. right. do 2 eexists. split; [eassumption|]. split; reflexivity.
  - split; [done|]. split; [done|]. left. right. right. left. do 2 eexists.
    split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; reflexivity.
  - split; [done|]. split; [done|]. left. right. right. right. eexists.
    split; [eassumption|]. split; [assumption|]. split; reflexivity.
Qed.

(** A configuration that does not [fails] is reducible. *)
Lemma not_fails_reducible ge fr callers m fuel s :
  ~ fails ge (mkConfig fr callers m fuel) -> @reducible (nanofil_lang ge) (EConf fr callers fuel) (m, s).
Proof.
  intros Hf. unfold reducible.
  destruct (Semantics.step ge (mkConfig fr callers m fuel)) as [c'|o|q k|why] eqn:E.
  - exists [], (conf_expr c'), (c_mem c', s), []. apply ps_machine; [exact Hf|]. apply RM.mstep_next, E.
  - assert (~ failure o) by (unfold fails in Hf; rewrite E in Hf; exact Hf).
    exists [], (EEnd o), (m, s), []. apply ps_done; assumption.
  - assert (0 <= req_extent q) by (unfold fails in Hf; rewrite E in Hf; lia).
    destruct (R.alloc s q) as [[base s']|] eqn:Ha.
    + exists [], (conf_expr (k base)), (c_mem (k base), s'), []. apply ps_machine; [exact Hf|].
      eapply RM.mstep_alloc; eauto.
    + exists [], (EEnd (Trap OutOfMemory)), (m, s), []. eapply ps_refused; eauto.
  - exfalso. apply Hf. unfold fails. rewrite E. exact I.
Qed.

(** The [nosp_step] of a configuration whose step is [Next] c'. *)
Lemma nosp_next ge c s e2 σ2 c' :
  Semantics.step ge c = Next c' -> nosp_step ge c s e2 σ2 -> e2 = conf_expr c' /\ σ2 = (c_mem c', s).
Proof.
  intros E [(c'' & E' & -> & ->) | [(q & k & b & s' & E' & _) | [(q & k & E' & _) | (o & E' & _)]]];
    rewrite E in E'; try discriminate E'.
  injection E' as <-. auto.
Qed.

(** The [nosp_step] of a configuration whose step is [Done] o. *)
Lemma nosp_done ge c s e2 σ2 o :
  Semantics.step ge c = Done o -> nosp_step ge c s e2 σ2 -> e2 = EEnd o /\ σ2 = (c_mem c, s).
Proof.
  intros E [(c'' & E' & _) | [(q & k & b & s' & E' & _) | [(q & k & E' & _) | (o' & E' & _ & -> & ->)]]];
    rewrite E in E'; try discriminate E'.
  injection E' as <-. auto.
Qed.

(** The [nosp_step] of a configuration whose step is [Fresh] q k: an
    allocation R grants, or its refusal. *)
Lemma nosp_fresh ge c s e2 σ2 q k :
  Semantics.step ge c = Fresh q k -> nosp_step ge c s e2 σ2 ->
  (exists base s', R.alloc s q = Some (base, s') /\ e2 = conf_expr (k base) /\ σ2 = (c_mem (k base), s')) \/
  (R.alloc s q = None /\ e2 = EEnd (Trap OutOfMemory) /\ σ2 = (c_mem c, s)).
Proof.
  intros E [(c'' & E' & _) | [(q' & k' & b & s' & E' & _ & Ha & -> & ->) | [(q' & k' & E' & _ & Ha & -> & ->) | (o & E' & _)]]];
    rewrite E in E'; try discriminate E'; injection E' as <- <-.
  - left. exists b, s'. auto.
  - right. auto.
Qed.

Section heap.
Context {hlc : has_lc} {Σ : gFunctors} {HinvG : invGS_gen hlc Σ} {HheapG : gen_heapGS piece pval Σ}.

(** The state interpretation of the memory and runtime state σ: the
    authoritative ghost heap, which agrees with the memory, live objects
    apart, and the runtime ready. *)
Definition heap_interp (σ : nstate) : iProp Σ :=
  ∃ h : gmap piece pval, gen_heap_interp h ∗ ⌜agrees σ.1 h /\ live_disjoint σ.1 /\ R.ready σ.2 σ.1⌝.

(** What owned pieces tell about the memory: [owned_facts]. *)
Lemma pts_facts m s ps : heap_interp (m, s) -∗ pts ps -∗ ⌜owned_facts ps m⌝.
Proof.
  iIntros "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr).
  iDestruct (pts_lookup with "Hh Hps") as %Hl. iPureIntro.
  split; [|split; [exact Hd | exact (R.address_space _ _ Hr)]].
  apply all_agree_intro. intros l v Hin. apply Ha, Hl, Hin.
Qed.

(** What R does at a safepoint keeps the state interpretation, with
    the same ghost heap. *)
Lemma heap_interp_safepoint m s m' s' :
  R.safepoint s m s' m' -> heap_interp (m, s) -∗ heap_interp (m', s').
Proof.
  intros Hsp. iIntros "Hσ". iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr).
  iExists h. iFrame "Hh". iPureIntro. cbn [fst snd] in *.
  destruct (SS.safepoint_shape _ _ _ _ Hsp) as (Hreg & Hb & Haux).
  split; [|split].
  - intros l v Hl. exact (agree_piece_safepoint _ _ _ _ Hreg Hb Haux (Ha l v Hl)).
  - exact (SS.live_disjoint_safepoint _ _ _ _ Hsp Hd).
  - exact (R.safepoint_ready _ _ _ _ Hsp Hr).
Qed.

Section wp.
Context (ge : genv).

(** The Iris instance of the genv ge: [heap_interp] as the state
    interpretation, no forks to speak of, one later per step. *)
Local Instance nanofil_irisGS : irisGS_gen hlc (nanofil_lang ge) Σ :=
  IrisG HinvG (fun σ _ _ _ => heap_interp σ) (fun _ => True%I) (fun _ => 0%nat)
        (fun _ _ _ _ => fupd_intro _ _).

(** The expression e never gets stuck: its weakest precondition with
    [NotStuck] and the postcondition True. *)
Definition wpc (e : expr) : iProp Σ :=
  (WP (e : language.expr (nanofil_lang ge)) @ NotStuck; ⊤ {{ _, True }})%I.

(** An ended run is safe. *)
Lemma wpc_end o : ⊢ wpc (EEnd o).
Proof. rewrite /wpc. iApply (wp_value' _ _ _ o). done. Qed.

(** The lifting lemma every rule is derived from. A configuration is
    safe, given Q, if Q and the state interpretation show it does not
    [fails], and if after any step that is not a safepoint they give
    the state interpretation and safety of what follows. A safepoint
    keeps the expression and Q, and changes only memory, which keeps
    the state interpretation: that case is closed by Löb induction. *)
Lemma wpc_lift (Q : iProp Σ) fr callers fuel :
  (forall m s, heap_interp (m, s) -∗ Q -∗ ⌜~ fails ge (mkConfig fr callers m fuel)⌝) ->
  (forall m s, heap_interp (m, s) -∗ Q -∗
     ▷ ∀ e2 σ2, ⌜nosp_step ge (mkConfig fr callers m fuel) s e2 σ2⌝ ==∗ heap_interp σ2 ∗ wpc e2) ->
  Q -∗ wpc (EConf fr callers fuel).
Proof.
  intros Hnf Hst. iLöb as "IH". iIntros "HQ". rewrite {2}/wpc.
  iApply wp_lift_step; [done|].
  iIntros ([m s] ns κ κs nt) "Hσ".
  iDestruct (Hnf with "Hσ HQ") as %Hnf'.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplitR; [iPureIntro; by apply not_fails_reducible|].
  iAssert ((▷ ∀ e2 σ2, ⌜nosp_step ge (mkConfig fr callers m fuel) s e2 σ2⌝ ==∗ heap_interp σ2 ∗ wpc e2)
           ∧ (heap_interp (m, s) ∗ Q))%I with "[Hσ HQ]" as "H".
  { iSplit; [iApply (Hst with "Hσ HQ") | iSplitL "Hσ"; [iExact "Hσ" | iExact "HQ"]]. }
  iNext. iIntros (e2 σ2 efs Hstep) "_". iMod "Hclose" as "_".
  destruct (prim_step_inv _ _ _ _ _ _ _ _ _ _ Hstep) as (-> & -> & [Hns | (s' & m' & Hsp & -> & ->)]).
  - iDestruct "H" as "[H _]". iMod ("H" with "[//]") as "[Hσ Hwp]". iModIntro.
    iSplitL "Hσ"; [iExact "Hσ"|]. iSplitL "Hwp"; [iExact "Hwp"|]. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro.
    iSplitL "Hσ"; [iApply (heap_interp_safepoint with "Hσ"); exact Hsp|].
    iSplitL; [iApply ("IH" with "HQ")|done].
Qed.

(** A step to the next configuration that leaves memory as it is, given
    what P shows the step to be: P is kept. *)
Lemma wpc_next (P : iProp Σ) fr callers fuel fr' callers' fuel' :
  (forall m s, heap_interp (m, s) -∗ P -∗
     ⌜Semantics.step ge (mkConfig fr callers m fuel) = Next (mkConfig fr' callers' m fuel')⌝) ->
  P -∗ ▷ (P -∗ wpc (EConf fr' callers' fuel')) -∗ wpc (EConf fr callers fuel).
Proof.
  intros Hs.
  assert (Hnf : forall m s, heap_interp (m, s) -∗ (P ∗ ▷ (P -∗ wpc (EConf fr' callers' fuel'))) -∗
                  ⌜~ fails ge (mkConfig fr callers m fuel)⌝).
  { iIntros (m s) "Hσ [HP _]". iDestruct (Hs with "Hσ HP") as %E. iPureIntro.
    unfold fails. rewrite E. auto. }
  assert (Hst : forall m s, heap_interp (m, s) -∗ (P ∗ ▷ (P -∗ wpc (EConf fr' callers' fuel'))) -∗
     ▷ ∀ e2 σ2, ⌜nosp_step ge (mkConfig fr callers m fuel) s e2 σ2⌝ ==∗ heap_interp σ2 ∗ wpc e2).
  { iIntros (m s) "Hσ [HP HK]". iDestruct (Hs with "Hσ HP") as %E. iNext. iIntros (e2 σ2 Hns).
    destruct (nosp_next _ _ _ _ _ _ E Hns) as [-> ->]. cbn [conf_expr c_frame c_callers c_fuel c_mem].
    iModIntro. iFrame "Hσ". iApply ("HK" with "HP"). }
  iIntros "HP HK". iApply (wpc_lift _ _ _ _ Hnf Hst with "[$HP $HK]").
Qed.

(** A step that ends the run with an outcome that is not a failure. *)
Lemma wpc_done (P : iProp Σ) fr callers fuel o :
  ~ failure o ->
  (forall m s, heap_interp (m, s) -∗ P -∗ ⌜Semantics.step ge (mkConfig fr callers m fuel) = Done o⌝) ->
  P -∗ wpc (EConf fr callers fuel).
Proof.
  intros Ho Hs.
  assert (Hnf : forall m s, heap_interp (m, s) -∗ P -∗ ⌜~ fails ge (mkConfig fr callers m fuel)⌝).
  { iIntros (m s) "Hσ HP". iDestruct (Hs with "Hσ HP") as %E. iPureIntro.
    unfold fails. rewrite E. exact Ho. }
  assert (Hst : forall m s, heap_interp (m, s) -∗ P -∗
     ▷ ∀ e2 σ2, ⌜nosp_step ge (mkConfig fr callers m fuel) s e2 σ2⌝ ==∗ heap_interp σ2 ∗ wpc e2).
  { iIntros (m s) "Hσ HP". iDestruct (Hs with "Hσ HP") as %E. iNext. iIntros (e2 σ2 Hns).
    destruct (nosp_done _ _ _ _ _ _ E Hns) as [-> ->]. cbn [c_mem].
    iModIntro. iFrame "Hσ". iApply wpc_end. }
  iIntros "HP". iApply (wpc_lift _ _ _ _ Hnf Hst with "HP").
Qed.

(** A step to the next configuration that writes memory: owning the
    pieces ps, where every memory those pieces agree with steps to
    [upd] m, which keeps regions, agrees with the new values ps' (same
    keys), and changes nothing outside them. Readiness follows from
    Machine.v's [mstep_ready]. *)
Lemma wpc_write ps ps' (upd : mem -> mem) fr callers fuel fr' callers' fuel' :
  ge_free ge = R.free -> ps'.*1 = ps.*1 ->
  (forall m, owned_facts ps m ->
     Semantics.step ge (mkConfig fr callers m fuel) = Next (mkConfig fr' callers' (upd m) fuel') /\
     m_regions (upd m) = m_regions m /\ all_agree (upd m) ps' /\ frame_ok ps'.*1 m (upd m)) ->
  pts ps -∗ ▷ (pts ps' -∗ wpc (EConf fr' callers' fuel')) -∗ wpc (EConf fr callers fuel).
Proof.
  intros Hge Hk Hs.
  assert (Hnf : forall m s, heap_interp (m, s) -∗ (pts ps ∗ ▷ (pts ps' -∗ wpc (EConf fr' callers' fuel'))) -∗
                  ⌜~ fails ge (mkConfig fr callers m fuel)⌝).
  { iIntros (m s) "Hσ [Hps _]". iDestruct (pts_facts with "Hσ Hps") as %Hf. iPureIntro.
    destruct (Hs m Hf) as (E & _). unfold fails. rewrite E. auto. }
  assert (Hst : forall m s, heap_interp (m, s) -∗ (pts ps ∗ ▷ (pts ps' -∗ wpc (EConf fr' callers' fuel'))) -∗
     ▷ ∀ e2 σ2, ⌜nosp_step ge (mkConfig fr callers m fuel) s e2 σ2⌝ ==∗ heap_interp σ2 ∗ wpc e2).
  { iIntros (m s) "Hσ [Hps HK]". iDestruct (pts_facts with "Hσ Hps") as %Hf.
    destruct (Hs m Hf) as (E & Hreg & Hag & Hfr). iNext. iIntros (e2 σ2 Hns).
    destruct (nosp_next _ _ _ _ _ _ E Hns) as [-> ->]. cbn [conf_expr c_frame c_callers c_fuel c_mem].
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr). cbn [fst snd] in Ha, Hd, Hr.
    iMod (pts_update with "Hh Hps") as "[Hh Hps]"; [exact Hk|].
    iModIntro. iSplitL "Hh".
    - iExists (overwrite ps' h). iFrame "Hh". iPureIntro. cbn [fst snd]. split; [|split].
      + intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [Hn Hh]].
        * exact (all_agree_elem _ _ _ _ Hag Hin).
        * exact (Hfr l v Hn (Ha l v Hh)).
      + exact (live_disjoint_regions _ _ Hreg Hd).
      + exact (RM.mstep_ready ge (mkConfig fr callers m fuel, s) (mkConfig fr' callers' (upd m) fuel', s)
                 Hge (RM.mstep_next ge _ _ s E) Hr).
    - iApply ("HK" with "Hps"). }
  iIntros "Hps HK". iApply (wpc_lift _ _ _ _ Hnf Hst with "[$Hps $HK]").
Qed.

(** An allocation of the request q: for every base R may grant, the new
    object's pieces are owned, and the base is positive, aligned, and
    the object ends within the address space. A refusal ends the run. *)
Lemma wpc_alloc q fr callers fuel (frk : Z -> frame) :
  0 < req_align q -> 0 <= req_extent q ->
  (forall m, Semantics.step ge (mkConfig fr callers m fuel) =
             Fresh q (fun base => mkConfig (frk base) callers (allocated m q base) fuel)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align q = 0 /\ base + req_extent q <= 2 ^ 48⌝ -∗
       pts (obj_ps base q) -∗ wpc (EConf (frk base) callers fuel)) -∗
  wpc (EConf fr callers fuel).
Proof.
  intros Hal Hex Hs.
  set (K := (∀ base, ⌜0 < base /\ base mod req_align q = 0 /\ base + req_extent q <= 2 ^ 48⌝ -∗
       pts (obj_ps base q) -∗ wpc (EConf (frk base) callers fuel))%I).
  assert (Hnf : forall m s, heap_interp (m, s) -∗ ▷ K -∗ ⌜~ fails ge (mkConfig fr callers m fuel)⌝).
  { iIntros (m s) "_ _". iPureIntro. unfold fails. rewrite Hs. lia. }
  assert (Hst : forall m s, heap_interp (m, s) -∗ ▷ K -∗
     ▷ ∀ e2 σ2, ⌜nosp_step ge (mkConfig fr callers m fuel) s e2 σ2⌝ ==∗ heap_interp σ2 ∗ wpc e2).
  { iIntros (m s) "Hσ HK". iNext. iIntros (e2 σ2 Hns).
    destruct (nosp_fresh _ _ _ _ _ _ _ (Hs m) Hns) as [(base & s' & Ha & -> & ->) | (Ha & -> & ->)].
    - cbn [conf_expr c_frame c_callers c_fuel c_mem].
      iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Hag & Hd & Hr). cbn [fst snd] in Hag, Hd, Hr.
      destruct (R.fresh_allocation _ _ _ _ _ Hr Hal Hex Ha) as [Hf Hr'].
      pose proof Hf as (Hpos & Hmod & _ & Hn & _).
      iMod (pts_alloc h (obj_ps base q) with "Hh") as "[Hh Hps]".
      { apply obj_ps_nodup. }
      { intros l v Hin. destruct (h !! l) as [v'|] eqn:E; [|reflexivity]. exfalso.
        pose proof (agree_piece_registered _ _ _ (obj_ps_mem _ _ _ _ Hin) (Hag l v' E)) as Hreg.
        rewrite (obj_ps_id _ _ _ _ Hin) in Hreg. exact (Hreg Hn). }
      iModIntro. iSplitL "Hh".
      + iExists _. iFrame "Hh". iPureIntro. cbn [fst snd]. split; [|split].
        * intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
          -- exact (obj_ps_agree _ _ _ _ _ Hf Hex Hin).
          -- exact (agree_piece_allocated _ _ _ _ _ Hn (Hag l v Hh)).
        * exact (live_disjoint_allocated _ _ _ Hd Hf Hex).
        * exact Hr'.
      + iApply ("HK" with "[%] Hps"). split; [exact Hpos|]. split; [exact Hmod|].
        destruct (R.address_space _ _ Hr' base (mkRegion base (base + req_extent q) (req_kind q) Live))
          as [_ Hend]; [rewrite object_region_allocated Z.eqb_refl; reflexivity|].
        cbn [r_end] in Hend. exact Hend.
    - cbn [c_mem]. iModIntro. iFrame "Hσ". iApply wpc_end. }
  iIntros "HK". iApply (wpc_lift _ _ _ _ Hnf Hst with "HK").
Qed.

End wp.
End heap.

(** Iris adequacy with the ghost heap: if, for every admissible input,
    the entry call is [wpc] safe under any invariant and ghost heap
    instance, with any fuel, the module never panics. The initial
    memory's live objects must not overlap (it holds none for a module
    with no data). *)
Theorem heap_never_panics Σ `{!invGpreS Σ, !gen_heapGpreS piece pval Σ}
    md entry (input : list word -> Prop) globals m f :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  live_disjoint m ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     forall fuel (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
       ⊢ wpc (P.program_genv md globals) (EConf fr [] fuel)) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hd Hwp. apply (IM.wp_never_panics HasNoLc Σ md entry input globals m f Hm Hf).
  intros xs Hxs. destruct (Hwp xs Hxs) as (fr & Hfr & Hw). exists fr. split; [exact Hfr|].
  intros Hready fuel Hinv.
  iMod (gen_heap_init (∅ : gmap piece pval)) as (HheapG) "(Hh & _ & _)".
  iModIntro. iExists (@heap_interp Σ HheapG).
  iSplitL "Hh".
  - iExists ∅. iFrame "Hh". iPureIntro. split; [|split; [exact Hd | exact Hready]].
    intros l v Hl. rewrite lookup_empty in Hl. discriminate.
  - iApply (Hw fuel Hinv HheapG).
Qed.

End IrisHeap.

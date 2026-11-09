(** Spike: nanofil's core machine as an Iris language, and Iris
    adequacy as a proof of [never_panics].

    An expression is a configuration less its memory ([EConf]: the
    running frame, the suspended callers and the fuel) or a finished run
    ([EEnd]: an outcome, which is also the value). The Iris state is the
    memory with the runtime's state. A primitive step is a step of
    Machine.v's [mstep] from a configuration that does not [fails], a
    refused allocation (which ends in a refusal trap), or an ending that
    is not a [failure]. A failing configuration is therefore never
    reducible, so a weakest precondition with [NotStuck] for the entry
    call rules out every failure; [wp_never_panics] proves that Panics.v's
    [never_panics] follows from such a weakest precondition, for every
    fuel. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre adequacy.
From Stdlib Require Import ZArith Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics.

Module IrisMachine (R : Runtime).
Module P := Panics R.
Module RM := P.RM.

(** An expression: a configuration without its memory (the frame, the
    callers and the fuel), or the outcome a run ended with. *)
Inductive expr : Type :=
| EConf (fr : frame) (callers : list (frame * pending)) (fuel : Z)
| EEnd (o : outcome).

(** The Iris state: the memory and the runtime's state. *)
Definition nstate : Type := (mem * R.state)%type.

(** A value is an outcome, written as the ended expression. *)
Definition of_val (o : outcome) : expr := EEnd o.

(** The outcome of an ended expression; None for a configuration. *)
Definition to_val (e : expr) : option outcome :=
  match e with EEnd o => Some o | EConf _ _ _ => None end.

(** The expression of the configuration c. *)
Definition conf_expr (c : config) : expr := EConf (c_frame c) (c_callers c) (c_fuel c).

(** A primitive step in the genv ge, with no observations and no forks:
    - [ps_machine]: a machine step of a configuration that does not
      [fails] (a failing configuration may have a safepoint due, and
      must still not count as reducible);
    - [ps_refused]: an allocation R refuses ends the run with the refusal
      trap [OutOfMemory];
    - [ps_done]: an ending that is not a failure. *)
Inductive prim_step (ge : genv) : expr -> nstate -> list unit -> expr -> nstate -> list expr -> Prop :=
| ps_machine fr callers fuel m s c' s' :
    ~ fails ge (mkConfig fr callers m fuel) ->
    RM.mstep ge (mkConfig fr callers m fuel, s) (c', s') ->
    prim_step ge (EConf fr callers fuel) (m, s) [] (conf_expr c') (c_mem c', s') []
| ps_refused fr callers fuel m s q k :
    Semantics.step ge (mkConfig fr callers m fuel) = Fresh q k ->
    (0 <= req_extent q)%Z ->
    R.alloc s q = None ->
    prim_step ge (EConf fr callers fuel) (m, s) [] (EEnd (Trap OutOfMemory)) (m, s) []
| ps_done fr callers fuel m s o :
    Semantics.step ge (mkConfig fr callers m fuel) = Done o ->
    ~ failure o ->
    prim_step ge (EConf fr callers fuel) (m, s) [] (EEnd o) (m, s) [].

(** The language laws: values round-trip, and a value takes no step. *)
Lemma nanofil_lang_mixin (ge : genv) : LanguageMixin of_val to_val (prim_step ge).
Proof.
  split.
  - reflexivity.
  - intros e o H. destruct e; inversion H; reflexivity.
  - intros e σ κ e' σ' efs H. destruct H; reflexivity.
Qed.

(** Nanofil's core machine in the genv ge as an Iris language. *)
Canonical Structure nanofil_lang (ge : genv) : language :=
  Language (nanofil_lang_mixin ge).

(** A configuration is its parts put back together. *)
Lemma config_eta (c : config) : mkConfig (c_frame c) (c_callers c) (c_mem c) (c_fuel c) = c.
Proof. destruct c; reflexivity. Qed.

(** A configuration that [fails] is not reducible: a failing ending,
    a stuck step and a negative extent each rule out all three kinds of
    primitive step. *)
Lemma fails_not_reducible (ge : genv) fr callers m fuel s :
  fails ge (mkConfig fr callers m fuel) ->
  ~ @reducible (nanofil_lang ge) (EConf fr callers fuel) (m, s).
Proof.
  intros Hf (κ & e' & σ' & efs & Hs). cbn in Hs.
  inversion Hs; subst.
  - contradiction.
  - unfold fails in Hf.
    match goal with E : Semantics.step _ _ = Fresh _ _ |- _ => rewrite E in Hf end. lia.
  - unfold fails in Hf.
    match goal with E : Semantics.step _ _ = Done _ |- _ => rewrite E in Hf end. contradiction.
Qed.

(** The Iris configuration of the machine state st: its expression as
    the only thread, with its memory and runtime state. *)
Definition cfg_of (ge : genv) (st : RM.mstate) : cfg (nanofil_lang ge) :=
  ([conf_expr (fst st)], (c_mem (fst st), snd st)).

(** A machine step from a configuration that does not [fails] is an
    Iris step between the corresponding Iris configurations. *)
Lemma mstep_erased_step (ge : genv) st st' :
  ~ fails ge (fst st) -> RM.mstep ge st st' -> erased_step (cfg_of ge st) (cfg_of ge st').
Proof.
  destruct st as [c s], st' as [c' s']. cbn [fst]. intros Hf Hs.
  exists []. apply step_atomic with (t1 := []) (t2 := []) (efs := [])
    (e1 := conf_expr c) (σ1 := (c_mem c, s)) (e2 := conf_expr c') (σ2 := (c_mem c', s'));
    [reflexivity | reflexivity |].
  rewrite <- (config_eta c) in Hf, Hs. unfold conf_expr at 1. cbn.
  exact (ps_machine ge _ _ _ _ _ _ _ Hf Hs).
Qed.

(** Where Iris adequacy holds for the configuration c's expression, every
    Iris configuration reached is not stuck, so no machine state reached
    [fails]; therefore every machine state the run reaches is
    Iris-reachable, and none [fails]. *)
Lemma adequate_no_fails (ge : genv) c0 s0 φ :
  @adequate (nanofil_lang ge) NotStuck (conf_expr c0) (c_mem c0, s0) φ ->
  forall st, RM.mreachable ge (c0, s0) st -> ~ fails ge (fst st).
Proof.
  intros Had.
  assert (Hok : forall st, rtc erased_step (cfg_of ge (c0, s0)) (cfg_of ge st) -> ~ fails ge (fst st)).
  { intros [c s] Hr Hf. cbn [fst] in Hf.
    destruct (adequate_not_stuck _ _ _ _ Had _ _ (conf_expr c) eq_refl Hr) as [[v Hv] | Hred].
    - set_solver.
    - discriminate Hv.
    - rewrite <- (config_eta c) in Hf. exact (fails_not_reducible ge _ _ _ _ s Hf Hred). }
  assert (Hgen : forall st1 st2, RM.mreachable ge st1 st2 ->
            rtc erased_step (cfg_of ge (c0, s0)) (cfg_of ge st1) ->
            rtc erased_step (cfg_of ge (c0, s0)) (cfg_of ge st2)).
  { intros st1 st2 H. induction H as [st1 st2 Hs | st1 | st1 st2 st3 _ IH1 _ IH2]; auto.
    intros Hr. eapply rtc_r; [exact Hr|]. apply mstep_erased_step; [apply Hok, Hr | exact Hs]. }
  intros st Hreach. apply Hok, (Hgen _ _ Hreach). reflexivity.
Qed.

(** Iris adequacy proves [never_panics]: where the module's initial
    memory and entry function exist, every admissible input makes the
    entry's frame, and (where R is ready at its start in that memory)
    for every fuel and every invariant instance a state interpretation
    stateI can be allocated that holds of the initial state and gives a
    [NotStuck] weakest precondition of the entry call, the module never
    panics. The later-credit flag hlc is left to the caller. *)
Theorem wp_never_panics (hlc : has_lc) Σ `{!invGpreS Σ} md entry (input : list word -> Prop) globals m f :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     (R.ready R.start m -> forall (fuel : Z) (Hinv : invGS_gen hlc Σ),
        ⊢ |={⊤}=> ∃ stateI : nstate -> iProp Σ,
            let _ : irisGS_gen hlc (nanofil_lang (P.program_genv md globals)) Σ :=
              IrisG Hinv (λ σ _ _ _, stateI σ) (λ _, True%I) (λ _, 0%nat)
                    (λ _ _ _ _, fupd_intro _ _) in
            stateI (m, R.start) ∗
            WP (EConf fr [] fuel : language.expr (nanofil_lang (P.program_genv md globals)))
              @ NotStuck; ⊤ {{ _, True }})) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hwp. exists globals, m, f. split; [exact Hm|]. split; [exact Hf|].
  intros xs Hxs. destruct (Hwp xs Hxs) as (fr & Hfr & Hw). exists fr. split; [exact Hfr|].
  intros Hready fuel st Hreach.
  set (ge := P.program_genv md globals) in *.
  assert (Had : @adequate (nanofil_lang ge) NotStuck (conf_expr (mkConfig fr [] m fuel))
                  (c_mem (mkConfig fr [] m fuel), R.start) (λ _ _, True)).
  { apply (wp_adequacy_gen hlc Σ (nanofil_lang ge) NotStuck _ _ (λ _, True)).
    intros Hinv κs. iMod (Hw Hready fuel Hinv) as (stateI) "[Hσ Hwp]". iModIntro.
    iExists (λ σ _, stateI σ), (λ _, True%I). cbn. iFrame "Hσ".
    iApply (wp_mono with "Hwp"). auto. }
  exact (adequate_no_fails ge _ _ _ Had st Hreach).
Qed.

End IrisMachine.

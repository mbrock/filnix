(** Spike: nanofil's core [[machine]] as an Iris language whose
    evaluation context is the stack of callers, and Iris [[adequacy]]
    as a proof of [never_panics].

    IrisLang.v made the whole configuration one expression, so a call
    was just another step and a function could have no specification of
    its own. Here the callers are Iris's evaluation context, so a call
    is [wp_bind] and a function's specification is an ordinary Hoare
    triple that hands resources back to its caller:
    - an expression is a running [[frame]] ([ERun]), the [[outcome]] an
      invocation returned ([EEnd], the value), or an expression running
      as the callee of a suspended caller frame ([EWait]); the one
      context item [KWait] is that caller;
    - the Iris state is the memory, the [[runtime]]'s state and the
      [[fuel]]: the machine has one fuel counter for the whole stack, so
      it belongs to the state, not to a frame;
    - a head step of [ERun fr] is the [[step]] of fr with no caller.
      [step_callers] shows that the callers are passive: they change
      only what a return does, which becomes [hs_return] (the value)
      and then [hs_resume] (the caller reads it);
    - an ending that is neither a failure nor a return (running out of
      fuel, a refusal trap) and an allocation the runtime refuses are
      stalls: [ERun fr] steps to itself. The machine has stopped without
      failing, and to Iris that is a run that never ends, which is safe.
      A failing frame has no head step at all, not even a safepoint.

    [run_reducible] and [head_step_run_inv] say a frame that does not
    fail is always head-reducible, and how; [wp_never_panics] proves
    Panics.v's [never_panics] from a [NotStuck] weakest precondition of
    the entry's [ERun], for every fuel. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language ectxi_language weakestpre adequacy.
From Stdlib Require Import ZArith Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics Steps.

(** Nanofil's core [[machine]] over the [[runtime]] R as an Iris
    language with evaluation contexts. *)
Module Language (R : Runtime).
Module P := Panics R.
Module RM := P.RM.

(** The [[outcome]] o returns to a caller: a return of one word, of
    several, or of none. *)
Definition returning (o : outcome) : Prop :=
  match o with Ret _ | Rets _ | RetVoid => True | _ => False end.

(** Whether an outcome returns is decided by its constructor. *)
Lemma returning_dec o : returning o \/ ~ returning o.
Proof. destruct o; cbn; tauto. Qed.

(** The configuration c' run as the callee of the callers cs: c''s own
    callers, then cs below them. *)
Definition lift_conf (cs : list (frame * pending)) (c' : config) : config :=
  mkConfig (c_frame c') (c_callers c' ++ cs) (c_mem c') (c_fuel c').

(** An instruction never stops with a returning outcome: only a jump
    returns, through [return_step]. *)
Lemma inst_step_stop ge fr m i o :
  inst_step ge fr m i = Some (IStop o) -> ~ returning o.
Proof.
  intros H. destruct i.
  1: destruct (special_let o0) eqn:Es;
       [destruct o0; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst;
    cbn; tauto.
Qed.

(** `doomed_result/5` makes no returning stop of its own: a returning
    stop after it is the instruction's. *)
Lemma doomed_result_stop ge fr m i out od o :
  doomed_result ge fr m i out = Some od -> fst od = IStop o -> returning o -> out = IStop o.
Proof.
  intros H Hf Hr. destruct (ahead_inst i) eqn:Ea.
  - destruct i as [d k op args | | | | | | |]; try discriminate Ea. destruct k; try discriminate Ea.
    destruct op; try discriminate Ea. destruct args as [|v [|v' args]]; try discriminate Ea.
    unfold doomed_result in H. cases H; inversion H; subst; cbn in Hf; try discriminate Hf;
      try (injection Hf as <-; cbn in Hr; tauto); auto.
  - rewrite (doomed_result_other _ _ _ _ _ Ea) in H.
    cases H; inversion H; subst; cbn in Hf; try discriminate Hf;
      try (injection Hf as <-; cbn in Hr; tauto); auto.
Qed.

(** A [[step]] that stops at an instruction, after [doomed_result],
    stops with an outcome that does not return. *)
Lemma stop_not_returning ge fr m i out od o :
  inst_step ge fr m i = Some out -> doomed_result ge fr m i out = Some od -> fst od = IStop o ->
  ~ returning o.
Proof.
  intros H1 H2 H3 Hr. pose proof (doomed_result_stop _ _ _ _ _ _ _ H2 H3 Hr) as ->.
  exact (inst_step_stop _ _ _ _ _ H1 Hr).
Qed.

(** A return with no caller ends the run with o once the locals end,
    and is stuck where they cannot. *)
Lemma return_nil fr m fuel o :
  return_step (mkConfig fr [] m fuel) o =
  match invalidate_locals (fr_locals fr) m with Some _ => Done o | None => Stuck "return" end.
Proof. unfold return_step. cbn. destruct (invalidate_locals _ _); reflexivity. Qed.

(** How the step r of a frame with the callers cs (the configuration c)
    follows from the step r0 of the same frame with none: the same next
    configuration or allocation with cs below its callers, the same
    ending where it does not return, the same [return_step] (now to a
    caller) where it returns and the locals can end, and stuck where
    r0 is stuck. *)
Definition lifted (cs : list (frame * pending)) (c : config) (r0 r : step_result) : Prop :=
  match r0 with
  | Next c' => r = Next (lift_conf cs c')
  | Fresh q k => exists k', r = Fresh q k' /\ forall base, k' base = lift_conf cs (k base)
  | Done o =>
      (~ returning o /\ r = Done o) \/
      (returning o /\ r = return_step c o /\
       exists m', invalidate_locals (fr_locals (c_frame c)) (c_mem c) = Some m')
  | Stuck _ => exists w, r = Stuck w
  end.

(** A tactic: succeed only if the term x contains no match. *)
Ltac no_match x := lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end.

(** The callers are passive: a [[step]] of the [[frame]] fr with the
    callers cs is the step of fr alone, related as [lifted] says. Only
    [return_step] reads the callers; every other part of [step] reads
    the frame, memory and [[fuel]] and passes the callers along. *)
Lemma step_callers ge fr cs m fuel :
  lifted cs (mkConfig fr cs m fuel)
    (Semantics.step ge (mkConfig fr [] m fuel)) (Semantics.step ge (mkConfig fr cs m fuel)).
Proof.
  unfold Semantics.step, jump_step, edge_step, inst_next, or_stuck, continue_at, with_point.
  cbn [c_frame c_callers c_mem c_fuel].
  repeat match goal with
  | |- context [return_step (mkConfig ?f [] ?mm ?fu) ?o] => rewrite (return_nil f mm fu o)
  | |- lifted _ _ ?r0 _ =>
      match r0 with
      | context [match ?x with _ => _ end] =>
          no_match x; destruct x eqn:?; cbn [fst snd c_frame c_callers c_mem c_fuel]
      end
  end.
  all: unfold lifted; cbn [lift_conf c_frame c_callers c_mem c_fuel app].
  all: first
    [ reflexivity
    | eexists; reflexivity
    | eexists; split; [reflexivity | intros ?; reflexivity]
    | left; split; [cbn; tauto | reflexivity]
    | right; split; [exact I | split; [reflexivity | eexists; eassumption]]
    | eexists; unfold return_step; cbn;
      match goal with E : invalidate_locals _ _ = None |- _ => rewrite E end; reflexivity
    | eexists; split; [reflexivity | intros base; cbv beta;
        match goal with kk : Z -> (env * _ * mem)%type |- _ => destruct (kk base) as [[? ?] ?] end;
        reflexivity]
    | left; split; [eapply stop_not_returning; eassumption | reflexivity] ].
Qed.

(** A next configuration of fr alone, with cs below its callers, is
    the next configuration of fr with the callers cs. *)
Lemma step_callers_next ge fr cs m fuel c' :
  Semantics.step ge (mkConfig fr [] m fuel) = Next c' ->
  Semantics.step ge (mkConfig fr cs m fuel) =
    Next (mkConfig (c_frame c') (c_callers c' ++ cs) (c_mem c') (c_fuel c')).
Proof. intros E. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H. exact H. Qed.

(** An allocation of fr alone is the same request with the callers
    cs, each base's configuration with cs below its callers. *)
Lemma step_callers_fresh ge fr cs m fuel q k :
  Semantics.step ge (mkConfig fr [] m fuel) = Fresh q k ->
  exists k', Semantics.step ge (mkConfig fr cs m fuel) = Fresh q k' /\
    forall base, k' base = mkConfig (c_frame (k base)) (c_callers (k base) ++ cs)
                                    (c_mem (k base)) (c_fuel (k base)).
Proof. intros E. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H. exact H. Qed.

(** An ending of fr alone that does not return is the same ending
    with any callers. *)
Lemma step_callers_stop ge fr cs m fuel o :
  Semantics.step ge (mkConfig fr [] m fuel) = Done o -> ~ returning o ->
  Semantics.step ge (mkConfig fr cs m fuel) = Done o.
Proof.
  intros E Hr. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H.
  destruct H as [[_ H] | [H _]]; [exact H | contradiction].
Qed.

(** A returning ending of fr alone is, with the callers cs, the
    return to them, and the locals of fr can end. *)
Lemma step_callers_return ge fr cs m fuel o :
  Semantics.step ge (mkConfig fr [] m fuel) = Done o -> returning o ->
  Semantics.step ge (mkConfig fr cs m fuel) = return_step (mkConfig fr cs m fuel) o /\
  exists m', invalidate_locals (fr_locals fr) m = Some m'.
Proof.
  intros E Hr. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H.
  destruct H as [[H _] | [_ H]]; [contradiction | exact H].
Qed.

(** A stuck step of fr alone is stuck with any callers. *)
Lemma step_callers_stuck ge fr cs m fuel w :
  Semantics.step ge (mkConfig fr [] m fuel) = Stuck w ->
  exists w', Semantics.step ge (mkConfig fr cs m fuel) = Stuck w'.
Proof. intros E. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H. exact H. Qed.

(** Whether a [[poll|safepoint]] is due reads only the running frame. *)
Lemma safepoint_due_callers ge fr cs m fuel :
  RM.safepoint_due ge (mkConfig fr cs m fuel) = RM.safepoint_due ge (mkConfig fr [] m fuel).
Proof. reflexivity. Qed.

(** The suspended caller frame cf, which reads its callee's result as
    pd says, resumed with the callee's returning outcome o: the tail of
    [return_step] (`call_outcome_result/5`), converting o by pd's
    convention and binding it in cf's environment. None where the
    result cannot be read so. *)
Definition resume (cf : frame) (pd : pending) (o : outcome) : option frame :=
  let* o' := match pd_conv pd with
             | None => Some o
             | Some (cw, kw) => converted_outcome cw kw o
             end in
  let* e := returned_env (pd_res pd) o' (fr_env cf) in
  Some (mkFrame (fr_fn cf) e (fr_locals cf) (fr_doomed cf) (fr_at cf)).

(** A return to the caller cf, where the locals of fr end in m', is the
    caller [resume]d, with the callers below it, or stuck where it
    cannot resume. *)
Lemma return_cons fr cf pd cs m m' fuel o :
  invalidate_locals (fr_locals fr) m = Some m' ->
  return_step (mkConfig fr ((cf, pd) :: cs) m fuel) o =
  match resume cf pd o with
  | Some cf' => Next (mkConfig cf' cs m' fuel)
  | None => Stuck "return"
  end.
Proof.
  intros E. unfold return_step, resume. cbn. rewrite E.
  destruct (match pd_conv pd with None => Some o | Some (cw, kw) => converted_outcome cw kw o end);
    [|reflexivity].
  destruct (returned_env _ _ _); reflexivity.
Qed.

(** A return with no caller, where the locals end, ends the run. *)
Lemma return_nil_done fr m m' fuel o :
  invalidate_locals (fr_locals fr) m = Some m' ->
  return_step (mkConfig fr [] m fuel) o = Done o.
Proof. intros E. rewrite return_nil E. reflexivity. Qed.

(** ## The language *)

(** An expression: a running invocation [ERun fr]; the outcome [EEnd o]
    an invocation returned, which is the value; or [EWait e cf pd], the
    expression e running as the callee of the suspended caller frame
    cf, which reads its result as pd says. *)
Inductive expr : Type :=
| ERun (fr : frame)
| EEnd (o : outcome)
| EWait (e : expr) (cf : frame) (pd : pending).

(** An evaluation context item: one suspended caller and how it reads
    its callee's result. *)
Inductive ectx_item : Type := KWait (cf : frame) (pd : pending).

(** The expression e as the callee of the context item Ki. *)
Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with KWait cf pd => EWait e cf pd end.

(** A value is an outcome, written as the ended expression. *)
Definition of_val (o : outcome) : expr := EEnd o.

(** The outcome of an ended expression; None otherwise. *)
Definition to_val (e : expr) : option outcome :=
  match e with EEnd o => Some o | _ => None end.

(** The Iris state: the memory, the runtime's state, and the [[fuel]]
    left, one counter for the whole stack. *)
Record lstate : Type := mkLstate { ls_mem : mem; ls_rt : R.state; ls_fuel : Z }.

(** The expression e under the callers cs, innermost first. *)
Fixpoint stack_expr (e : expr) (cs : list (frame * pending)) : expr :=
  match cs with
  | [] => e
  | (cf, pd) :: cs' => stack_expr (EWait e cf pd) cs'
  end.

(** The callers cs as an Iris evaluation context, innermost first. *)
Definition ctx_of (cs : list (frame * pending)) : list ectx_item :=
  map (fun '(cf, pd) => KWait cf pd) cs.

(** The expression of the configuration c: its running frame under its
    callers. *)
Definition conf_expr (c : config) : expr := stack_expr (ERun (c_frame c)) (c_callers c).

(** The Iris state of the configuration c with the runtime state s. *)
Definition conf_state (c : config) (s : R.state) : lstate :=
  {| ls_mem := c_mem c; ls_rt := s; ls_fuel := c_fuel c |}.

(** A head step in the genv ge, with no observations and no forks. The
    running frame fr steps as fr alone would ([mkConfig fr [] m fuel]):
    - [hs_next]: a step that allocates nothing; a call yields the callee
      with fr suspended as its one caller, an [EWait];
    - [hs_alloc]: an allocation R grants;
    - [hs_refused]: an allocation R refuses stalls: the run has stopped
      with a refusal, which is not a failure;
    - [hs_return]: a returning ending, once the locals end, is the value;
    - [hs_stop]: any other ending that is not a [failure] (running out
      of fuel, a refusal trap) stalls;
    - [hs_safepoint]: R's action at a due [[poll|safepoint]], only where
      fr does not [fails], so that a failing frame is never reducible;
    - [hs_resume]: a returned outcome resumes the caller waiting on it. *)
Inductive head_step (ge : genv) : expr -> lstate -> list unit -> expr -> lstate -> list expr -> Prop :=
| hs_next fr m s fuel c' :
    Semantics.step ge (mkConfig fr [] m fuel) = Next c' ->
    head_step ge (ERun fr) (mkLstate m s fuel) [] (conf_expr c') (conf_state c' s) []
| hs_alloc fr m s fuel q k base s' :
    Semantics.step ge (mkConfig fr [] m fuel) = Fresh q k ->
    (0 <= req_extent q)%Z ->
    R.alloc s q = Some (base, s') ->
    head_step ge (ERun fr) (mkLstate m s fuel) [] (conf_expr (k base)) (conf_state (k base) s') []
| hs_refused fr m s fuel q k :
    Semantics.step ge (mkConfig fr [] m fuel) = Fresh q k ->
    (0 <= req_extent q)%Z ->
    R.alloc s q = None ->
    head_step ge (ERun fr) (mkLstate m s fuel) [] (ERun fr) (mkLstate m s fuel) []
| hs_return fr m s fuel o m' :
    Semantics.step ge (mkConfig fr [] m fuel) = Done o ->
    returning o ->
    invalidate_locals (fr_locals fr) m = Some m' ->
    head_step ge (ERun fr) (mkLstate m s fuel) [] (EEnd o) (mkLstate m' s fuel) []
| hs_stop fr m s fuel o :
    Semantics.step ge (mkConfig fr [] m fuel) = Done o ->
    ~ failure o ->
    ~ returning o ->
    head_step ge (ERun fr) (mkLstate m s fuel) [] (ERun fr) (mkLstate m s fuel) []
| hs_safepoint fr m s fuel s' m' :
    ~ fails ge (mkConfig fr [] m fuel) ->
    RM.safepoint_due ge (mkConfig fr [] m fuel) = true ->
    R.safepoint s m s' m' ->
    head_step ge (ERun fr) (mkLstate m s fuel) [] (ERun fr) (mkLstate m' s' fuel) []
| hs_resume o cf pd cf' σ :
    resume cf pd o = Some cf' ->
    head_step ge (EWait (EEnd o) cf pd) σ [] (ERun cf') σ [].

(** The context-item language laws: values round-trip, a value takes
    no step, filling is injective and never makes a value, and a head
    step of a filled context is [hs_resume], whose callee is a value. *)
Lemma nanofil_mixin (ge : genv) : EctxiLanguageMixin of_val to_val fill_item (head_step ge).
Proof.
  split.
  - reflexivity.
  - intros e o H. destruct e; inversion H; reflexivity.
  - intros e1 σ1 κ e2 σ2 efs H. destruct H; reflexivity.
  - intros [cf pd] e [o H]. discriminate H.
  - intros [cf pd] e1 e2 H. injection H as H. exact H.
  - intros [cf1 pd1] [cf2 pd2] e1 e2 _ _ H. injection H as _ -> ->. reflexivity.
  - intros [cf pd] e σ1 κ e2 σ2 efs H. inversion H; subst. eexists. reflexivity.
Qed.

(** Nanofil's core machine in the genv ge as an Iris language with
    context items, contexts, and as a plain language. *)
Canonical Structure nanofil_ectxi_lang (ge : genv) : ectxiLanguage :=
  EctxiLanguage (nanofil_mixin ge).
Canonical Structure nanofil_ectx_lang (ge : genv) : ectxLanguage :=
  EctxLanguageOfEctxi (nanofil_ectxi_lang ge).
Canonical Structure nanofil_lang (ge : genv) : language :=
  LanguageOfEctx (nanofil_ectx_lang ge).

(** The expression e under the callers cs is Iris's [fill] of their
    context, [foldl (flip fill_item)], innermost first. *)
Lemma stack_expr_fill ge e cs :
  stack_expr e cs = @ectx_language.fill (nanofil_ectx_lang ge) (ctx_of cs) e.
Proof.
  revert e. induction cs as [|[cf pd] cs IH]; intros e; [reflexivity|].
  cbn [stack_expr]. rewrite IH. reflexivity.
Qed.

(** The expression under the callers cs1 then cs2 is under cs1, and
    that under cs2. *)
Lemma stack_expr_app e cs1 cs2 :
  stack_expr e (cs1 ++ cs2) = stack_expr (stack_expr e cs1) cs2.
Proof.
  revert e. induction cs1 as [|[cf pd] cs1 IH]; intros e; [reflexivity|]. cbn. apply IH.
Qed.

(** An expression that is not a value is not one under any callers. *)
Lemma to_val_stack e cs : to_val e = None -> to_val (stack_expr e cs) = None.
Proof.
  revert e. induction cs as [|[cf pd] cs IH]; intros e H; [exact H|]. cbn. apply IH. reflexivity.
Qed.

(** A head step under the callers cs is an Iris step of the thread
    pool of that one expression. *)
Lemma head_erased ge cs e1 σ1 e2 σ2 :
  head_step ge e1 σ1 [] e2 σ2 [] ->
  @erased_step (nanofil_lang ge) ([stack_expr e1 cs], σ1) ([stack_expr e2 cs], σ2).
Proof.
  intros H. exists []. apply (step_atomic (stack_expr e1 cs) σ1 (stack_expr e2 cs) σ2 [] [] []);
    [reflexivity | reflexivity |].
  rewrite !(stack_expr_fill ge). exact (Ectx_step' (Λ := nanofil_ectx_lang ge) _ _ _ _ _ _ _ H).
Qed.

(** Where e is not a value and has only values as sub-redexes, e under
    any callers is reducible only if e is head-reducible. *)
Lemma ctx_base_reducible ge cs e σ :
  to_val e = None ->
  (forall Ki e', e = fill_item Ki e' -> is_Some (to_val e')) ->
  @reducible (nanofil_lang ge) (stack_expr e cs) σ ->
  @base_reducible (nanofil_ectx_lang ge) e σ.
Proof.
  intros Hv Hsub (κ & e2 & σ2 & efs & Hs).
  rewrite (stack_expr_fill ge) in Hs.
  destruct Hs as [K e1' e2' HK _ Hb].
  destruct (step_by_val (Λ := nanofil_ectx_lang ge) (ctx_of cs) K e e1' _ _ _ _ _ HK Hv Hb)
    as [K'' ->].
  rewrite <- fill_comp in HK. apply (inj _) in HK.
  assert (Hs : @sub_redexes_are_values (nanofil_ectx_lang ge) e).
  { exact (ectxi_language_sub_redexes_are_values (Λ := nanofil_ectxi_lang ge) e Hsub). }
  pose proof (Hs K'' e1' HK (val_base_stuck _ _ _ _ _ _ Hb)) as ->.
  rewrite fill_empty in HK. subst e1'. do 4 eexists. exact Hb.
Qed.

(** The inversion of a head step from [ERun fr] in the state σ: no
    observations or forks, and one of the six cases of [head_step],
    each stated of fr alone. Weakest-precondition rules are stated per
    case. *)
Lemma head_step_run_inv ge fr σ κ e' σ' efs :
  head_step ge (ERun fr) σ κ e' σ' efs ->
  let c0 := mkConfig fr [] (ls_mem σ) (ls_fuel σ) in
  κ = [] /\ efs = [] /\
  ((exists c', Semantics.step ge c0 = Next c' /\ e' = conf_expr c' /\ σ' = conf_state c' (ls_rt σ)) \/
   (exists q k base s', Semantics.step ge c0 = Fresh q k /\ (0 <= req_extent q)%Z /\
      R.alloc (ls_rt σ) q = Some (base, s') /\ e' = conf_expr (k base) /\ σ' = conf_state (k base) s') \/
   (exists q k, Semantics.step ge c0 = Fresh q k /\ (0 <= req_extent q)%Z /\
      R.alloc (ls_rt σ) q = None /\ e' = ERun fr /\ σ' = σ) \/
   (exists o m', Semantics.step ge c0 = Done o /\ returning o /\
      invalidate_locals (fr_locals fr) (ls_mem σ) = Some m' /\
      e' = EEnd o /\ σ' = mkLstate m' (ls_rt σ) (ls_fuel σ)) \/
   (exists o, Semantics.step ge c0 = Done o /\ ~ failure o /\ ~ returning o /\ e' = ERun fr /\ σ' = σ) \/
   (exists s' m', ~ fails ge c0 /\ RM.safepoint_due ge c0 = true /\ R.safepoint (ls_rt σ) (ls_mem σ) s' m' /\
      e' = ERun fr /\ σ' = mkLstate m' s' (ls_fuel σ))).
Proof.
  intros H. inversion H; subst; cbn; (split; [reflexivity | split; [reflexivity |]]).
  - left. eauto.
  - right; left. eauto 10.
  - right; right; left. eauto 10.
  - right; right; right; left. eauto 10.
  - right; right; right; right; left. eauto 10.
  - right; right; right; right; right. eauto 10.
Qed.

(** A frame that takes a head step does not [fails], with no caller. *)
Lemma run_not_fails ge fr σ κ e' σ' efs :
  head_step ge (ERun fr) σ κ e' σ' efs -> ~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)).
Proof.
  intros H. destruct (head_step_run_inv _ _ _ _ _ _ _ H)
    as (_ & _ & [(c' & E & _) | [(q & k & b & s' & E & He & _) | [(q & k & E & He & _) |
        [(o & m' & E & Hr & _) | [(o & E & Hf & _) | (s' & m' & Hf & _)]]]]]);
    try exact Hf; unfold fails; rewrite E; try lia; auto.
  destruct o; cbn in *; tauto.
Qed.

(** The language never blocks a frame that does not fail: if fr alone
    does not [fails] in σ's memory and fuel, [ERun fr] is
    head-reducible in σ. *)
Lemma run_reducible ge fr σ :
  ~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) ->
  @base_reducible (nanofil_ectx_lang ge) (ERun fr) σ.
Proof.
  destruct σ as [m s fuel]. cbn. intros Hf. unfold fails in Hf.
  destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c' | o | q k | w] eqn:E.
  - do 4 eexists. exact (hs_next ge _ _ _ _ _ E).
  - destruct (returning_dec o) as [Hr | Hr].
    + destruct (step_callers_return ge fr [] m fuel o E Hr) as [_ [m' Hi]].
      do 4 eexists. exact (hs_return ge _ _ _ _ _ _ E Hr Hi).
    + do 4 eexists. exact (hs_stop ge _ _ _ _ _ E Hf Hr).
  - destruct (R.alloc s q) as [[base s'] |] eqn:Ea.
    + do 4 eexists. exact (hs_alloc ge _ _ _ _ _ _ _ _ E ltac:(lia) Ea).
    + do 4 eexists. exact (hs_refused ge _ _ _ _ _ _ E ltac:(lia) Ea).
  - contradiction.
Qed.

(** A returned outcome waiting on a caller is reducible, under any
    callers, only where the caller [resume]s. *)
Lemma wait_resumes ge cs o cf pd σ :
  @reducible (nanofil_lang ge) (stack_expr (EWait (EEnd o) cf pd) cs) σ ->
  exists cf', resume cf pd o = Some cf'.
Proof.
  intros H. apply ctx_base_reducible in H as (κ & e' & σ' & efs & Hs).
  - inversion Hs; subst. eauto.
  - reflexivity.
  - intros [cf' pd'] e' Heq. cbn in Heq. injection Heq as <- _ _. eexists. reflexivity.
Qed.

(** Where the expression of the configuration c is not stuck, its
    running frame alone does not [fails]. *)
Lemma conf_reducible ge c s :
  @not_stuck (nanofil_lang ge) (conf_expr c) (conf_state c s) ->
  ~ fails ge (mkConfig (c_frame c) [] (c_mem c) (c_fuel c)).
Proof.
  intros [[v Hv] | Hred].
  - change (to_val (conf_expr c) = Some v) in Hv.
    unfold conf_expr in Hv. rewrite to_val_stack in Hv; [discriminate Hv | reflexivity].
  - apply ctx_base_reducible in Hred as (κ & e' & σ' & efs & Hs).
    + exact (run_not_fails _ _ _ _ _ _ _ Hs).
    + reflexivity.
    + intros [cf pd] e' Heq. discriminate Heq.
Qed.

(** ## Adequacy *)

(** Adequacy for the run of the frame fr0 from the memory m0 and the
    fuel fuel0, at R's start. *)
Section adequacy.
Context (ge : genv) (fr0 : frame) (m0 : mem) (fuel0 : Z).

(** The configuration c with the runtime state s is Iris-reachable:
    its expression and state follow the initial ones by Iris steps. *)
Let iris_reach (c : config) (s : R.state) : Prop :=
  rtc (@erased_step (nanofil_lang ge))
    ([ERun fr0], mkLstate m0 R.start fuel0) ([conf_expr c], conf_state c s).

(** Where Iris adequacy holds, the running frame of every
    Iris-reachable configuration alone does not [fails]. *)
Lemma reach_ok φ c s :
  @adequate (nanofil_lang ge) NotStuck (ERun fr0) (mkLstate m0 R.start fuel0) φ ->
  iris_reach c s -> ~ fails ge (mkConfig (c_frame c) [] (c_mem c) (c_fuel c)).
Proof.
  intros Had Hr. apply (conf_reducible ge c s).
  apply (adequate_not_stuck _ _ _ _ Had _ _ (conf_expr c) eq_refl Hr). left.
Qed.

(** Every machine step from an Iris-reachable state reaches an
    Iris-reachable state: a step that allocates nothing, an allocation
    and a safepoint are one head step under the callers; a return to a
    caller is two, [hs_return] and then [hs_resume]. *)
Lemma reach_step φ c s c' s' :
  @adequate (nanofil_lang ge) NotStuck (ERun fr0) (mkLstate m0 R.start fuel0) φ ->
  iris_reach c s -> RM.mstep ge (c, s) (c', s') -> iris_reach c' s'.
Proof.
  intros Had Hr Hs. pose proof (reach_ok φ c s Had Hr) as Hnf.
  destruct c as [fr cs m fuel]. cbn in Hnf.
  pose proof (step_callers ge fr cs m fuel) as Hl.
  inversion Hs as [c1 c1' s1 E | c1 q k s1 base s1' E He Hal | c1 s1 s1' m' Hdue Hsp]; subst.
  - destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c0' | o | q k | w] eqn:E0;
      cbn [lifted] in Hl; rewrite E in Hl.
    + injection Hl as ->. eapply rtc_r; [exact Hr|].
      unfold conf_expr at 2. cbn [lift_conf c_frame c_callers].
      rewrite stack_expr_app.
      exact (head_erased ge cs _ _ _ _ (hs_next ge fr m s' fuel c0' E0)).
    + destruct Hl as [[_ Hl] | (Hrt & Hl & m' & Hi)]; [discriminate Hl|].
      destruct cs as [|[cf pd] cs].
      { rewrite (return_nil_done _ _ _ _ _ Hi) in Hl. discriminate Hl. }
      rewrite (return_cons _ _ _ _ _ _ _ _ Hi) in Hl.
      destruct (resume cf pd o) as [cf'|] eqn:Er; [|discriminate Hl]. injection Hl as ->.
      eapply rtc_r; [eapply rtc_r; [exact Hr|]|].
      * exact (head_erased ge ((cf, pd) :: cs) _ _ _ _ (hs_return ge fr m s' fuel o m' E0 Hrt Hi)).
      * exact (head_erased ge cs _ _ _ _ (hs_resume ge o cf pd cf' _ Er)).
    + destruct Hl as (k' & Hl & _). discriminate Hl.
    + destruct Hl as (w' & Hl). discriminate Hl.
  - destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c0' | o | q0 k0 | w] eqn:E0;
      cbn [lifted] in Hl; rewrite E in Hl.
    + discriminate Hl.
    + destruct Hl as [[_ Hl] | (Hrt & Hl & m' & Hi)]; [discriminate Hl|].
      exfalso. exact (return_step_not_fresh _ _ _ _ (eq_sym Hl)).
    + destruct Hl as (k' & Hl & Hk). injection Hl as -> ->. rewrite Hk.
      eapply rtc_r; [exact Hr|].
      unfold conf_expr at 2. cbn [lift_conf c_frame c_callers].
      rewrite stack_expr_app.
      exact (head_erased ge cs _ _ _ _ (hs_alloc ge fr m s fuel q0 k0 base s' E0 He Hal)).
    + destruct Hl as (w' & Hl). discriminate Hl.
  - eapply rtc_r; [exact Hr|].
    exact (head_erased ge cs _ _ _ _ (hs_safepoint ge fr m s fuel s' m' Hnf Hdue Hsp)).
Qed.

(** No Iris-reachable configuration [fails]: its frame alone does not,
    and where its return to a caller is stuck, the returned outcome
    waiting on that caller is Iris-reachable and stuck. *)
Lemma reach_not_fails φ c s :
  @adequate (nanofil_lang ge) NotStuck (ERun fr0) (mkLstate m0 R.start fuel0) φ ->
  iris_reach c s -> ~ fails ge c.
Proof.
  intros Had Hr. pose proof (reach_ok φ c s Had Hr) as Hnf.
  destruct c as [fr cs m fuel]. cbn in Hnf.
  pose proof (step_callers ge fr cs m fuel) as Hl.
  unfold fails in Hnf |- *.
  destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c0' | o | q k | w] eqn:E0;
    cbn [lifted] in Hl.
  - rewrite Hl. auto.
  - destruct Hl as [[Hrt Hl] | (Hrt & Hl & m' & Hi)]; rewrite Hl; [exact Hnf|].
    destruct cs as [|[cf pd] cs].
    { rewrite (return_nil_done _ _ _ _ _ Hi). destruct o; cbn in *; tauto. }
    rewrite (return_cons _ _ _ _ _ _ _ _ Hi).
    destruct (resume cf pd o) as [cf'|] eqn:Er; [auto|]. intros _.
    assert (Hr' : rtc (@erased_step (nanofil_lang ge)) ([ERun fr0], mkLstate m0 R.start fuel0)
                    ([stack_expr (EWait (EEnd o) cf pd) cs], mkLstate m' s fuel)).
    { eapply rtc_r; [exact Hr|].
      exact (head_erased ge ((cf, pd) :: cs) _ _ _ _ (hs_return ge fr m s fuel o m' E0 Hrt Hi)). }
    destruct (adequate_not_stuck _ _ _ _ Had _ _ _ eq_refl Hr' ltac:(left)) as [[v Hv] | Hred].
    + change (to_val (stack_expr (EWait (EEnd o) cf pd) cs) = Some v) in Hv.
      rewrite to_val_stack in Hv; [discriminate Hv | reflexivity].
    + destruct (wait_resumes ge cs o cf pd _ Hred) as [cf' Hcf']. congruence.
  - destruct Hl as (k' & -> & _). exact Hnf.
  - exfalso. exact (Hnf I).
Qed.

(** Where Iris adequacy holds for [ERun fr0], every machine state the
    run reaches is Iris-reachable, and none [fails]. *)
Lemma adequate_no_fails φ :
  @adequate (nanofil_lang ge) NotStuck (ERun fr0) (mkLstate m0 R.start fuel0) φ ->
  forall st, RM.mreachable ge (mkConfig fr0 [] m0 fuel0, R.start) st -> ~ fails ge (fst st).
Proof.
  intros Had.
  assert (Hgen : forall st1 st2, RM.mreachable ge st1 st2 ->
            iris_reach (fst st1) (snd st1) -> iris_reach (fst st2) (snd st2)).
  { intros st1 st2 H. induction H as [[c s] [c' s'] Hs | st1 | st1 st2 st3 _ IH1 _ IH2]; auto.
    cbn. intros Hr. exact (reach_step φ c s c' s' Had Hr Hs). }
  intros [c s] Hreach. apply (reach_not_fails φ c s Had).
  exact (Hgen _ _ Hreach (rtc_refl _ _)).
Qed.

End adequacy.

(** [[adequacy|Adequacy]]: Iris adequacy proves [never_panics]. Where
    the module's initial memory and entry function exist, every
    admissible input makes the entry's frame, and (where R is ready at
    its start in that memory) for every fuel and every invariant
    instance a state interpretation stateI can be allocated that holds
    of the initial state and gives a [NotStuck] weakest precondition of
    the entry's [ERun], the module never panics. The later-credit flag
    hlc is left to the caller. *)
Theorem wp_never_panics (hlc : has_lc) Σ `{!invGpreS Σ} md entry (input : list word -> Prop) globals m f :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     (R.ready R.start m -> forall (fuel : Z) (Hinv : invGS_gen hlc Σ),
        ⊢ |={⊤}=> ∃ stateI : lstate -> iProp Σ,
            let _ : irisGS_gen hlc (nanofil_lang (P.program_genv md globals)) Σ :=
              IrisG Hinv (λ σ _ _ _, stateI σ) (λ _, True%I) (λ _, 0%nat)
                    (λ _ _ _ _, fupd_intro _ _) in
            stateI (mkLstate m R.start fuel) ∗
            WP (ERun fr : language.expr (nanofil_lang (P.program_genv md globals)))
              @ NotStuck; ⊤ {{ _, True }})) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hwp. exists globals, m, f. split; [exact Hm|]. split; [exact Hf|].
  intros xs Hxs. destruct (Hwp xs Hxs) as (fr & Hfr & Hw). exists fr. split; [exact Hfr|].
  intros Hready fuel st Hreach.
  set (ge := P.program_genv md globals) in *.
  assert (Had : @adequate (nanofil_lang ge) NotStuck (ERun fr) (mkLstate m R.start fuel) (λ _ _, True)).
  { apply (wp_adequacy_gen hlc Σ (nanofil_lang ge) NotStuck _ _ (λ _, True)).
    intros Hinv κs. iMod (Hw Hready fuel Hinv) as (stateI) "[Hσ Hwp]". iModIntro.
    iExists (λ σ _, stateI σ), (λ _, True%I). cbn. iFrame "Hσ".
    iApply (wp_mono with "Hwp"). auto. }
  exact (adequate_no_fails ge fr m fuel _ Had st Hreach).
Qed.

End Language.

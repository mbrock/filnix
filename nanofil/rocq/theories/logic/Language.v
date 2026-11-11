(** Nanofil's [[machine]], with the [[external call|external calls]]
    of a contract registry, as an Iris language whose evaluation
    context is the stack of callers, and Iris [[adequacy]] as a proof
    of [never_panics] and of the labelled machine's safety.

    The first logic spike's IrisLang.v made the whole configuration one
    expression, so a call was just another step and a function could
    have no specification of its own. Here the callers are Iris's
    evaluation context, so a call is [wp_bind] and a function's
    specification is an ordinary Hoare triple that hands resources back
    to its caller:
    - an expression is a running [[frame]] ([ERun]), the [[outcome]] an
      invocation returned ([EEnd], the value), an expression running
      as the callee of a suspended caller frame ([EWait]), or the bad
      return of an external call ([EBad]); the one context item [KWait]
      is that caller;
    - the Iris state is the memory, the [[runtime]]'s state, the
      [[fuel]] and the world of libc state the contracts speak of: the
      machine has one fuel counter for the whole stack, so it belongs
      to the state, not to a frame;
    - a head step of [ERun fr] is the [[step]] of fr with no caller.
      [step_callers] shows that the callers are passive: they change
      only what a return does, which becomes [hs_return] (the value)
      and then [hs_resume] (the caller reads it);
    - an ending that is neither a failure nor a return (running out of
      fuel, a refusal trap) and an allocation the runtime refuses are
      stalls: [ERun fr] steps to itself. The machine has stopped without
      failing, and to Iris that is a run that never ends, which is safe.
      A failing frame has no head step at all, not even a safepoint.

    The language is over a world type and a contract registry, the
    labelled machine's (ExternalMachine.v). A call at an
    [external_site] is stuck to the core [step]; here it is:
    - admissible (a contract, arguments that evaluate, its ABI and its
      precondition): it may return ([hs_call_return], the frame resumed
      with the call's memory, runtime state and world), and it may also
      stall ([hs_call_wait]). The stall stands for everything the call
      does that is not a return: it may block, it may exit the process
      or end for lack of resources (the labelled machine stops there
      without failing), and the labelled machine makes no step where an
      admissible call has no completed invocation. None of these is a
      failure, and to Iris each is a run that never ends, so a stall is
      safe; and it makes an admissible call always reducible, whether or
      not the contract allows any return;
    - returning words the call site cannot take ([hs_call_bad]): the
      expression becomes [EBad], which is no value and has no step, so
      adequacy rules it out;
    - rejected: no head step, so adequacy rules it out too.
    With the empty registry ([no_contracts]) no call is admissible and
    the language is the core machine's.

    [run_reducible], [admissible_reducible] and [head_step_run_inv] say
    a frame that does not fail, or whose external call is admissible,
    is always head-reducible, and how. [wp_never_panics] proves
    Panics.v's [never_panics] from a [NotStuck] weakest precondition of
    the entry's [ERun] in the language with no contracts, for every
    fuel; [adequate_labelled] and [wp_labelled_safe] prove that no
    labelled [[run]] stops with a [failure_ending], and that a returned
    value satisfies the postcondition. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language ectxi_language weakestpre adequacy.
From Stdlib Require Import ZArith Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics Steps
  ExternalCalls ExternalMachine.

(** Nanofil's [[machine]] over the [[runtime]] R, with external calls,
    as an Iris language with evaluation contexts. *)
Module Language (R : Runtime).
Module P := Panics R.
Module RM := P.RM.
Module M := ExternalMachine R.

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
  - destruct i as [d k op args | | | | | | | | ]; try discriminate Ea. destruct k; try discriminate Ea.
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

(** ## External calls *)

(** Whether a configuration is at an [external_site] reads only its
    running frame: the frame alone is at the same site, in any memory
    and fuel. *)
Lemma external_site_frame ge c m fuel site :
  external_site ge c site -> external_site ge (mkConfig (c_frame c) [] m fuel) site.
Proof. intros H. exact H. Qed.

(** A frame is at most at one [external_site]: its next instruction
    fixes every part of the site. *)
Lemma external_site_unique ge c c' site site' :
  c_frame c = c_frame c' -> external_site ge c site -> external_site ge c' site' -> site = site'.
Proof.
  unfold external_site. cbv zeta. intros Hf (_ & Ha & _) (_ & Ha' & _).
  destruct site, site'. cbn in *.
  rewrite Hf Ha' in Ha. injection Ha. intros. subst. reflexivity.
Qed.

(** A completed call was admissible: its ABI and its precondition
    hold, whatever its ending. *)
Lemma invoke_admissible {world : Type} (spec : contract world) r args xs s m w trace ending s' m' w' :
  M.E.invoke spec r args xs s m w trace ending s' m' w' ->
  contract_abi spec r args /\ contract_pre spec xs m w.
Proof. intros H. destruct H; auto. Qed.

(** A call's resource ending is no [failure]: [resource_failure] is
    out of memory or too big, both refusals. *)
Lemma invoke_resource_refusal {world : Type} (spec : contract world) r args xs s m w trace why s' m' w' :
  M.E.invoke spec r args xs s m w trace (CallResource why) s' m' w' -> ~ failure (Trap why).
Proof.
  intros H. inversion H; subst.
  - match goal with Hn : forall why', CallResource ?x <> CallResource why' |- _ =>
      exfalso; exact (Hn _ eq_refl) end.
  - apply resource_not_failure.
    match goal with Hf : M.E.resource_failure _ _ _ |- _ => destruct Hf end;
      unfold resource_reason; auto.
Qed.

(** A core machine step of the labelled machine's copy of Machine.v is
    a step of this file's: the two functor instances share their
    definitions, and only the inductive relation is generative. *)
Lemma labelled_core_step ge ms ms' : M.P.I.RM.mstep ge ms ms' -> RM.mstep ge ms ms'.
Proof.
  intros H. destruct H; [eapply RM.mstep_next | eapply RM.mstep_alloc | eapply RM.mstep_safepoint];
    eassumption.
Qed.

(** ## The language *)

(** An expression: a running invocation [ERun fr]; the outcome [EEnd o]
    an invocation returned, which is the value; [EWait e cf pd], the
    expression e running as the callee of the suspended caller frame
    cf, which reads its result as pd says; or [EBad], an external call
    that returned words its call site cannot take, which is no value
    and takes no step. *)
Inductive expr : Type :=
| ERun (fr : frame)
| EEnd (o : outcome)
| EWait (e : expr) (cf : frame) (pd : pending)
| EBad.

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

(** The Iris state over the world type world: the memory, the
    runtime's state, the [[fuel]] left, one counter for the whole
    stack, and the world of libc state the contracts speak of. *)
Record lstate (world : Type) : Type :=
  mkLstate { ls_mem : mem; ls_rt : R.state; ls_fuel : Z; ls_world : world }.
Arguments mkLstate {world}.
Arguments ls_mem {world}.
Arguments ls_rt {world}.
Arguments ls_fuel {world}.
Arguments ls_world {world}.

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

(** The Iris state of the configuration c with the runtime state s and
    the world w. *)
Definition conf_state {world : Type} (c : config) (s : R.state) (w : world) : lstate world :=
  mkLstate (c_mem c) s (c_fuel c) w.

(** The frame fr after its external call at site returned, with the
    environment e: at the instruction after the call. *)
Definition resumed_frame (fr : frame) (site : call_site) (e : env) : frame :=
  mkFrame (fr_fn fr) e (fr_locals fr) None (Exec (site_label site) (site_rest site) (site_jump site)).

(** [resume_external] resumes the running frame as [resumed_frame]. *)
Lemma resume_external_frame c site e m :
  c_frame (resume_external c site e m) = resumed_frame (c_frame c) site e.
Proof. reflexivity. Qed.

(** What [ERun fr] becomes when its external call at site, of the
    contract spec, returns the words values: the [resumed_frame] where
    the site's result takes them ([external_env]), [EBad] where it
    cannot. *)
Definition returned_expr {world : Type} (fr : frame) (spec : contract world) (site : call_site)
    (values : list word) : expr :=
  match external_env spec site values (fr_env fr) with
  | Some e => ERun (resumed_frame fr site e)
  | None => EBad
  end.

(** The empty registry, over the world unit: no external function has
    a contract, so no external call is admissible. *)
Definition no_contracts : name -> option (contract unit) := fun _ => None.

(** The language over the registry, whose contracts share the world
    type world, in the genv ge. *)
Section language.
Context {world : Type} (registry : name -> option (contract world)) (ge : genv).

(** The frame fr, alone in the memory, fuel and world of σ, is at an
    [external_site] whose call is [M.admissible]: a contract is
    registered, the arguments evaluate, the ABI and the precondition
    hold. *)
Definition call_admissible (fr : frame) (σ : lstate world) : Prop :=
  exists site, external_site ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) site /\
    M.admissible registry ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) (ls_world σ) site.

(** The frame fr can go on in σ: alone it does not [fails], or it is at
    an external call that is admissible. [ERun fr] is head-reducible in
    σ exactly then ([run_proceeds], [proceeds_reducible]). *)
Definition proceeds (fr : frame) (σ : lstate world) : Prop :=
  ~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) \/ call_admissible fr σ.

(** A head step, with no observations and no forks. The running frame
    fr steps as fr alone would ([mkConfig fr [] m fuel]):
    - [hs_next]: a step that allocates nothing; a call yields the callee
      with fr suspended as its one caller, an [EWait];
    - [hs_alloc]: an allocation R grants;
    - [hs_refused]: an allocation R refuses stalls: the run has stopped
      with a refusal, which is not a failure;
    - [hs_return]: a returning ending, once the locals end, is the value;
    - [hs_stop]: any other ending that is not a [failure] (running out
      of fuel, a refusal trap) stalls;
    - [hs_safepoint]: R's action at a due [[poll|safepoint]], only where
      fr [proceeds], so that a failing frame or a rejected call is never
      reducible;
    - [hs_resume]: a returned outcome resumes the caller waiting on it;
    - [hs_call_return]: an external call whose contract's invocation
      returns words the call site takes resumes after the call, with
      the invocation's memory, runtime state and world;
    - [hs_call_bad]: one that returns words the site cannot take is
      [EBad];
    - [hs_call_wait]: an admissible call stalls: it may block, exit,
      end for lack of resources, or have no completed invocation. *)
Inductive head_step : expr -> lstate world -> list unit -> expr -> lstate world -> list expr -> Prop :=
| hs_next fr m s fuel w c' :
    Semantics.step ge (mkConfig fr [] m fuel) = Next c' ->
    head_step (ERun fr) (mkLstate m s fuel w) [] (conf_expr c') (conf_state c' s w) []
| hs_alloc fr m s fuel w q k base s' :
    Semantics.step ge (mkConfig fr [] m fuel) = Fresh q k ->
    (0 <= req_extent q)%Z ->
    R.alloc s q = Some (base, s') ->
    head_step (ERun fr) (mkLstate m s fuel w) [] (conf_expr (k base)) (conf_state (k base) s' w) []
| hs_refused fr m s fuel w q k :
    Semantics.step ge (mkConfig fr [] m fuel) = Fresh q k ->
    (0 <= req_extent q)%Z ->
    R.alloc s q = None ->
    head_step (ERun fr) (mkLstate m s fuel w) [] (ERun fr) (mkLstate m s fuel w) []
| hs_return fr m s fuel w o m' :
    Semantics.step ge (mkConfig fr [] m fuel) = Done o ->
    returning o ->
    invalidate_locals (fr_locals fr) m = Some m' ->
    head_step (ERun fr) (mkLstate m s fuel w) [] (EEnd o) (mkLstate m' s fuel w) []
| hs_stop fr m s fuel w o :
    Semantics.step ge (mkConfig fr [] m fuel) = Done o ->
    ~ failure o ->
    ~ returning o ->
    head_step (ERun fr) (mkLstate m s fuel w) [] (ERun fr) (mkLstate m s fuel w) []
| hs_safepoint fr m s fuel w s' m' :
    proceeds fr (mkLstate m s fuel w) ->
    RM.safepoint_due ge (mkConfig fr [] m fuel) = true ->
    R.safepoint s m s' m' ->
    head_step (ERun fr) (mkLstate m s fuel w) [] (ERun fr) (mkLstate m' s' fuel w) []
| hs_resume o cf pd cf' σ :
    resume cf pd o = Some cf' ->
    head_step (EWait (EEnd o) cf pd) σ [] (ERun cf') σ []
| hs_call_return fr m s fuel w site spec xs trace values s' m' w' e :
    external_site ge (mkConfig fr [] m fuel) site ->
    registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env fr)) (site_args site) = Some xs ->
    M.E.invoke spec (site_result site) (site_args site) xs s m w trace (CallReturn values) s' m' w' ->
    external_env spec site values (fr_env fr) = Some e ->
    head_step (ERun fr) (mkLstate m s fuel w) []
      (ERun (c_frame (resume_external (mkConfig fr [] m fuel) site e m'))) (mkLstate m' s' fuel w') []
| hs_call_bad fr m s fuel w site spec xs trace values s' m' w' :
    external_site ge (mkConfig fr [] m fuel) site ->
    registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env fr)) (site_args site) = Some xs ->
    M.E.invoke spec (site_result site) (site_args site) xs s m w trace (CallReturn values) s' m' w' ->
    external_env spec site values (fr_env fr) = None ->
    head_step (ERun fr) (mkLstate m s fuel w) [] EBad (mkLstate m' s' fuel w') []
| hs_call_wait fr m s fuel w site spec xs :
    external_site ge (mkConfig fr [] m fuel) site ->
    registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env fr)) (site_args site) = Some xs ->
    contract_abi spec (site_result site) (site_args site) ->
    contract_pre spec xs m w ->
    head_step (ERun fr) (mkLstate m s fuel w) [] (ERun fr) (mkLstate m s fuel w) [].

(** The context-item language laws: values round-trip, a value takes
    no step, filling is injective and never makes a value, and a head
    step of a filled context is [hs_resume], whose callee is a value. *)
Lemma nanofil_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
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

End language.

(** Nanofil's machine with the contracts of registry, in the genv ge,
    as an Iris language with context items, contexts, and as a plain
    language. *)
Canonical Structure nanofil_ectxi_lang {world : Type} (registry : name -> option (contract world))
    (ge : genv) : ectxiLanguage :=
  EctxiLanguage (nanofil_mixin registry ge).
(** The same language with evaluation contexts. *)
Canonical Structure nanofil_ectx_lang {world : Type} (registry : name -> option (contract world))
    (ge : genv) : ectxLanguage :=
  EctxLanguageOfEctxi (nanofil_ectxi_lang registry ge).
(** The same language, plain. *)
Canonical Structure nanofil_lang {world : Type} (registry : name -> option (contract world))
    (ge : genv) : language :=
  LanguageOfEctx (nanofil_ectx_lang registry ge).

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

(** Facts of the language with the contracts of registry, in the genv
    ge. *)
Section facts.
Context {world : Type} (registry : name -> option (contract world)) (ge : genv).

(** The expression e under the callers cs is Iris's [fill] of their
    context, [foldl (flip fill_item)], innermost first. *)
Lemma stack_expr_fill e cs :
  stack_expr e cs = @ectx_language.fill (nanofil_ectx_lang registry ge) (ctx_of cs) e.
Proof.
  revert e. induction cs as [|[cf pd] cs IH]; intros e; [reflexivity|].
  cbn [stack_expr]. rewrite IH. reflexivity.
Qed.

(** A head step under the callers cs is an Iris step of the thread
    pool of that one expression. *)
Lemma head_erased cs e1 σ1 e2 σ2 :
  head_step registry ge e1 σ1 [] e2 σ2 [] ->
  @erased_step (nanofil_lang registry ge) ([stack_expr e1 cs], σ1) ([stack_expr e2 cs], σ2).
Proof.
  intros H. exists []. apply (step_atomic (stack_expr e1 cs) σ1 (stack_expr e2 cs) σ2 [] [] []);
    [reflexivity | reflexivity |].
  rewrite !stack_expr_fill.
  exact (Ectx_step' (Λ := nanofil_ectx_lang registry ge) _ _ _ _ _ _ _ H).
Qed.

(** Where e is not a value and has only values as sub-redexes, e under
    any callers is reducible only if e is head-reducible. *)
Lemma ctx_base_reducible cs e σ :
  to_val e = None ->
  (forall Ki e', e = fill_item Ki e' -> is_Some (to_val e')) ->
  @reducible (nanofil_lang registry ge) (stack_expr e cs) σ ->
  @base_reducible (nanofil_ectx_lang registry ge) e σ.
Proof.
  intros Hv Hsub (κ & e2 & σ2 & efs & Hs).
  rewrite stack_expr_fill in Hs.
  destruct Hs as [K e1' e2' HK _ Hb].
  destruct (step_by_val (Λ := nanofil_ectx_lang registry ge) (ctx_of cs) K e e1' _ _ _ _ _ HK Hv Hb)
    as [K'' ->].
  rewrite <- fill_comp in HK. apply (inj _) in HK.
  assert (Hs : @sub_redexes_are_values (nanofil_ectx_lang registry ge) e).
  { exact (ectxi_language_sub_redexes_are_values (Λ := nanofil_ectxi_lang registry ge) e Hsub). }
  pose proof (Hs K'' e1' HK (val_base_stuck _ _ _ _ _ _ Hb)) as ->.
  rewrite fill_empty in HK. subst e1'. do 4 eexists. exact Hb.
Qed.

(** The inversion of a head step from [ERun fr] in the state σ: no
    observations or forks, and one of the cases of [head_step], each
    stated of fr alone; an external call's return is one case, the
    frame resumed or [EBad] ([returned_expr]). Weakest-precondition
    rules are stated per case. *)
Lemma head_step_run_inv fr σ κ e' σ' efs :
  head_step registry ge (ERun fr) σ κ e' σ' efs ->
  let c0 := mkConfig fr [] (ls_mem σ) (ls_fuel σ) in
  κ = [] /\ efs = [] /\
  ((exists c', Semantics.step ge c0 = Next c' /\ e' = conf_expr c' /\
      σ' = conf_state c' (ls_rt σ) (ls_world σ)) \/
   (exists q k base s', Semantics.step ge c0 = Fresh q k /\ (0 <= req_extent q)%Z /\
      R.alloc (ls_rt σ) q = Some (base, s') /\ e' = conf_expr (k base) /\
      σ' = conf_state (k base) s' (ls_world σ)) \/
   (exists q k, Semantics.step ge c0 = Fresh q k /\ (0 <= req_extent q)%Z /\
      R.alloc (ls_rt σ) q = None /\ e' = ERun fr /\ σ' = σ) \/
   (exists o m', Semantics.step ge c0 = Done o /\ returning o /\
      invalidate_locals (fr_locals fr) (ls_mem σ) = Some m' /\
      e' = EEnd o /\ σ' = mkLstate m' (ls_rt σ) (ls_fuel σ) (ls_world σ)) \/
   (exists o, Semantics.step ge c0 = Done o /\ ~ failure o /\ ~ returning o /\ e' = ERun fr /\ σ' = σ) \/
   (exists s' m', proceeds registry ge fr σ /\ RM.safepoint_due ge c0 = true /\
      R.safepoint (ls_rt σ) (ls_mem σ) s' m' /\
      e' = ERun fr /\ σ' = mkLstate m' s' (ls_fuel σ) (ls_world σ)) \/
   (exists site spec xs trace values s' m' w', external_site ge c0 site /\
      registry (site_name site) = Some spec /\
      map_option (arg_x ge (fr_env fr)) (site_args site) = Some xs /\
      M.E.invoke spec (site_result site) (site_args site) xs (ls_rt σ) (ls_mem σ) (ls_world σ)
        trace (CallReturn values) s' m' w' /\
      e' = returned_expr fr spec site values /\ σ' = mkLstate m' s' (ls_fuel σ) w') \/
   (call_admissible registry ge fr σ /\ e' = ERun fr /\ σ' = σ)).
Proof.
  intros H. inversion H; subst; cbn [ls_mem ls_rt ls_fuel ls_world];
    (split; [reflexivity | split; [reflexivity |]]).
  - left. eauto.
  - right; left. eauto 10.
  - do 2 right; left. eauto 10.
  - do 3 right; left. eauto 10.
  - do 4 right; left. eauto 10.
  - do 5 right; left. eauto 10.
  - do 6 right; left. do 8 eexists. repeat (split; [eassumption|]).
    split; [|reflexivity]. unfold returned_expr.
    match goal with He : external_env _ _ _ _ = Some _ |- _ => rewrite He end. reflexivity.
  - do 6 right; left. do 8 eexists. repeat (split; [eassumption|]).
    split; [|reflexivity]. unfold returned_expr.
    match goal with He : external_env _ _ _ _ = None |- _ => rewrite He end. reflexivity.
  - do 7 right. split; [|split; reflexivity]. eexists. split; [eassumption|].
    do 2 eexists. eauto.
Qed.

(** A frame that takes a head step [proceeds]: it does not [fails]
    alone, or its external call is admissible. *)
Lemma run_proceeds fr σ κ e' σ' efs :
  head_step registry ge (ERun fr) σ κ e' σ' efs -> proceeds registry ge fr σ.
Proof.
  intros H. destruct (head_step_run_inv _ _ _ _ _ _ H)
    as (_ & _ & [(c' & E & _) | [(q & k & b & s' & E & He & _) | [(q & k & E & He & _) |
        [(o & m' & E & Hr & _) | [(o & E & Hf & _) | [(s' & m' & Hp & _) |
        [(site & spec & xs & tr & vs & s' & m' & w' & Hs & Hreg & Hx & Hi & _) | (Ha & _)]]]]]]]).
  - left. unfold fails. rewrite E. auto.
  - left. unfold fails. rewrite E. lia.
  - left. unfold fails. rewrite E. lia.
  - left. unfold fails. rewrite E. destruct o; cbn in *; tauto.
  - left. unfold fails. rewrite E. exact Hf.
  - exact Hp.
  - right. destruct (invoke_admissible _ _ _ _ _ _ _ _ _ _ _ _ Hi) as [Habi Hpre].
    exists site. split; [exact Hs|]. exists spec, xs. auto.
  - right. exact Ha.
Qed.

(** The language never blocks a frame that does not fail: if fr alone
    does not [fails] in σ's memory and fuel, [ERun fr] is
    head-reducible in σ. *)
Lemma run_reducible fr σ :
  ~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) ->
  @base_reducible (nanofil_ectx_lang registry ge) (ERun fr) σ.
Proof.
  destruct σ as [m s fuel w]. cbn. intros Hf. unfold fails in Hf.
  destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c' | o | q k | w'] eqn:E.
  - do 4 eexists. eapply hs_next. exact E.
  - destruct (returning_dec o) as [Hr | Hr].
    + destruct (step_callers_return ge fr [] m fuel o E Hr) as [_ [m' Hi]].
      do 4 eexists. eapply hs_return; eassumption.
    + do 4 eexists. eapply hs_stop; eassumption.
  - destruct (R.alloc s q) as [[base s'] |] eqn:Ea.
    + do 4 eexists. eapply hs_alloc; [exact E | lia | exact Ea].
    + do 4 eexists. eapply hs_refused; [exact E | lia | exact Ea].
  - contradiction.
Qed.

(** Nor an admissible external call: [ERun fr] at one is
    head-reducible, by [hs_call_wait], whether or not the contract
    allows a return. *)
Lemma admissible_reducible fr σ :
  call_admissible registry ge fr σ -> @base_reducible (nanofil_ectx_lang registry ge) (ERun fr) σ.
Proof.
  destruct σ as [m s fuel w]. intros (site & Hs & spec & xs & Hr & Hx & Ha & Hp).
  do 4 eexists. eapply hs_call_wait; eassumption.
Qed.

(** A frame that [proceeds] is head-reducible. *)
Lemma proceeds_reducible fr σ :
  proceeds registry ge fr σ -> @base_reducible (nanofil_ectx_lang registry ge) (ERun fr) σ.
Proof. intros [H | H]; [exact (run_reducible _ _ H) | exact (admissible_reducible _ _ H)]. Qed.

(** A returned outcome waiting on a caller is reducible, under any
    callers, only where the caller [resume]s. *)
Lemma wait_resumes cs o cf pd σ :
  @reducible (nanofil_lang registry ge) (stack_expr (EWait (EEnd o) cf pd) cs) σ ->
  exists cf', resume cf pd o = Some cf'.
Proof.
  intros H. apply ctx_base_reducible in H as (κ & e' & σ' & efs & Hs).
  - inversion Hs; subst. eauto.
  - reflexivity.
  - intros [cf' pd'] e' Heq. cbn in Heq. injection Heq as <- _ _. eexists. reflexivity.
Qed.

(** A bad return is stuck under any callers. *)
Lemma bad_stuck cs σ : ~ @reducible (nanofil_lang registry ge) (stack_expr EBad cs) σ.
Proof.
  intros H. apply ctx_base_reducible in H as (κ & e' & σ' & efs & Hs).
  - inversion Hs.
  - reflexivity.
  - intros [cf pd] e' Heq. discriminate Heq.
Qed.

(** Where the expression of the configuration c is not stuck, its
    running frame [proceeds]. *)
Lemma conf_reducible c s w :
  @not_stuck (nanofil_lang registry ge) (conf_expr c) (conf_state c s w) ->
  proceeds registry ge (c_frame c) (conf_state c s w).
Proof.
  intros [[v Hv] | Hred].
  - change (to_val (conf_expr c) = Some v) in Hv.
    unfold conf_expr in Hv. rewrite to_val_stack in Hv; [discriminate Hv | reflexivity].
  - apply ctx_base_reducible in Hred as (κ & e' & σ' & efs & Hs).
    + exact (run_proceeds _ _ _ _ _ _ Hs).
    + reflexivity.
    + intros [cf pd] e' Heq. discriminate Heq.
Qed.

End facts.

(** ## Adequacy *)

(** Adequacy for the run of the frame fr0, with the contracts of
    registry in the genv ge, from the memory m0, the runtime state s0,
    the fuel fuel0 and the world w0. *)
Section adequacy.
Context {world : Type} (registry : name -> option (contract world)) (ge : genv)
  (fr0 : frame) (m0 : mem) (s0 : R.state) (fuel0 : Z) (w0 : world).

(** The configuration c with the runtime state s and the world w is
    Iris-reachable: its expression and state follow the initial ones by
    Iris steps. *)
Definition iris_reach (c : config) (s : R.state) (w : world) : Prop :=
  rtc (@erased_step (nanofil_lang registry ge))
    ([ERun fr0], mkLstate m0 s0 fuel0 w0) ([conf_expr c], conf_state c s w).

(** Where Iris adequacy holds, the running frame of every
    Iris-reachable configuration [proceeds]. *)
Lemma reach_proceeds φ c s w :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> proceeds registry ge (c_frame c) (conf_state c s w).
Proof.
  intros Had Hr. apply (conf_reducible registry ge c s w).
  apply (adequate_not_stuck _ _ _ _ Had _ _ (conf_expr c) eq_refl Hr). left.
Qed.

(** Every core machine step from an Iris-reachable state reaches an
    Iris-reachable state, in the same world: a step that allocates
    nothing, an allocation and a safepoint are one head step under the
    callers; a return to a caller is two, [hs_return] and then
    [hs_resume]. *)
Lemma reach_step φ c s w c' s' :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> RM.mstep ge (c, s) (c', s') -> iris_reach c' s' w.
Proof.
  intros Had Hr Hs. pose proof (reach_proceeds φ c s w Had Hr) as Hp.
  destruct c as [fr cs m fuel].
  pose proof (step_callers ge fr cs m fuel) as Hl.
  inversion Hs as [c1 c1' s1 E | c1 q k s1 base s1' E He Hal | c1 s1 s1' m' Hdue Hsp]; subst.
  - destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c0' | o | q k | w'] eqn:E0;
      cbn [lifted] in Hl; rewrite E in Hl.
    + injection Hl as ->. eapply rtc_r; [exact Hr|].
      unfold conf_expr at 2. cbn [lift_conf c_frame c_callers].
      rewrite stack_expr_app.
      exact (head_erased registry ge cs _ _ _ _ (hs_next registry ge fr m s' fuel w c0' E0)).
    + destruct Hl as [[_ Hl] | (Hrt & Hl & m' & Hi)]; [discriminate Hl|].
      destruct cs as [|[cf pd] cs].
      { rewrite (return_nil_done _ _ _ _ _ Hi) in Hl. discriminate Hl. }
      rewrite (return_cons _ _ _ _ _ _ _ _ Hi) in Hl.
      destruct (resume cf pd o) as [cf'|] eqn:Er; [|discriminate Hl]. injection Hl as ->.
      eapply rtc_r; [eapply rtc_r; [exact Hr|]|].
      * exact (head_erased registry ge ((cf, pd) :: cs) _ _ _ _
                 (hs_return registry ge fr m s' fuel w o m' E0 Hrt Hi)).
      * exact (head_erased registry ge cs _ _ _ _ (hs_resume registry ge o cf pd cf' _ Er)).
    + destruct Hl as (k' & Hl & _). discriminate Hl.
    + destruct Hl as (w'' & Hl). discriminate Hl.
  - destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c0' | o | q0 k0 | w'] eqn:E0;
      cbn [lifted] in Hl; rewrite E in Hl.
    + discriminate Hl.
    + destruct Hl as [[_ Hl] | (Hrt & Hl & m' & Hi)]; [discriminate Hl|].
      exfalso. exact (return_step_not_fresh _ _ _ _ (eq_sym Hl)).
    + destruct Hl as (k' & Hl & Hk). injection Hl as -> ->. rewrite Hk.
      eapply rtc_r; [exact Hr|].
      unfold conf_expr at 2. cbn [lift_conf c_frame c_callers].
      rewrite stack_expr_app.
      exact (head_erased registry ge cs _ _ _ _ (hs_alloc registry ge fr m s fuel w q0 k0 base s' E0 He Hal)).
    + destruct Hl as (w'' & Hl). discriminate Hl.
  - eapply rtc_r; [exact Hr|].
    exact (head_erased registry ge cs _ _ _ _ (hs_safepoint registry ge fr m s fuel w s' m' Hp Hdue Hsp)).
Qed.

(** An Iris-reachable configuration whose frame alone does not [fails]
    does not fail: where its return to a caller is stuck, the returned
    outcome waiting on that caller is Iris-reachable and stuck. *)
Lemma reach_not_fails φ c s w :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> ~ fails ge (mkConfig (c_frame c) [] (c_mem c) (c_fuel c)) -> ~ fails ge c.
Proof.
  intros Had Hr Hnf.
  destruct c as [fr cs m fuel]. cbn in Hnf.
  pose proof (step_callers ge fr cs m fuel) as Hl.
  unfold fails in Hnf |- *.
  destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c0' | o | q k | w'] eqn:E0;
    cbn [lifted] in Hl.
  - rewrite Hl. auto.
  - destruct Hl as [[Hrt Hl] | (Hrt & Hl & m' & Hi)]; rewrite Hl; [exact Hnf|].
    destruct cs as [|[cf pd] cs].
    { rewrite (return_nil_done _ _ _ _ _ Hi). destruct o; cbn in *; tauto. }
    rewrite (return_cons _ _ _ _ _ _ _ _ Hi).
    destruct (resume cf pd o) as [cf'|] eqn:Er; [auto|]. intros _.
    assert (Hr' : rtc (@erased_step (nanofil_lang registry ge)) ([ERun fr0], mkLstate m0 s0 fuel0 w0)
                    ([stack_expr (EWait (EEnd o) cf pd) cs], mkLstate m' s fuel w)).
    { eapply rtc_r; [exact Hr|].
      exact (head_erased registry ge ((cf, pd) :: cs) _ _ _ _
               (hs_return registry ge fr m s fuel w o m' E0 Hrt Hi)). }
    destruct (adequate_not_stuck _ _ _ _ Had _ _ _ eq_refl Hr' ltac:(left)) as [[v Hv] | Hred].
    + change (to_val (stack_expr (EWait (EEnd o) cf pd) cs) = Some v) in Hv.
      rewrite to_val_stack in Hv; [discriminate Hv | reflexivity].
    + destruct (wait_resumes registry ge cs o cf pd _ Hred) as [cf' Hcf']. congruence.
  - destruct Hl as (k' & -> & _). exact Hnf.
  - exfalso. exact (Hnf I).
Qed.

(** An Iris-reachable configuration at no external site does not
    [fails]. *)
Lemma reach_core φ c s w :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> (forall site, ~ external_site ge c site) -> ~ fails ge c.
Proof.
  intros Had Hr Hns. apply (reach_not_fails φ c s w Had Hr).
  destruct (reach_proceeds φ c s w Had Hr) as [Hnf | (site & Hs & _)]; [exact Hnf|].
  exfalso. exact (Hns site Hs).
Qed.

(** A core ending of an Iris-reachable configuration at no external
    site is no [failure]; a returning one is a top-level return, whose
    value satisfies φ in some Iris-reachable state. *)
Lemma reach_end φ c s w o :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> (forall site, ~ external_site ge c site) ->
  Semantics.step ge c = Done o -> ~ failure o /\ (returning o -> exists σ, φ o σ).
Proof.
  intros Had Hr Hns E. pose proof (reach_core φ c s w Had Hr Hns) as Hnf.
  unfold fails in Hnf. rewrite E in Hnf. split; [exact Hnf|]. intros Hret.
  destruct c as [fr cs m fuel].
  pose proof (step_callers ge fr cs m fuel) as Hl. rewrite E in Hl.
  destruct (Semantics.step ge (mkConfig fr [] m fuel)) as [c0' | o0 | q k | w'] eqn:E0;
    cbn [lifted] in Hl.
  - discriminate Hl.
  - destruct Hl as [[Hr0 Hl] | (Hr0 & Hl & m' & Hi)].
    + injection Hl as <-. contradiction.
    + destruct cs as [|[cf pd] cs].
      * rewrite (return_nil_done _ _ _ _ _ Hi) in Hl. injection Hl as <-.
        exists (mkLstate m' s fuel w). apply (adequate_result _ _ _ _ Had []).
        eapply rtc_r; [exact Hr|].
        exact (head_erased registry ge [] _ _ _ _ (hs_return registry ge fr m s fuel w o m' E0 Hr0 Hi)).
      * rewrite (return_cons _ _ _ _ _ _ _ _ Hi) in Hl. destruct (resume cf pd o0); discriminate Hl.
  - destruct Hl as (k' & Hl & _). discriminate Hl.
  - destruct Hl as (w'' & Hl). discriminate Hl.
Qed.

(** An Iris-reachable configuration at no external site is not stuck. *)
Lemma reach_stuck φ c s w why :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> (forall site, ~ external_site ge c site) ->
  Semantics.step ge c <> Stuck why.
Proof.
  intros Had Hr Hns E. apply (reach_core φ c s w Had Hr Hns). unfold fails. rewrite E. exact I.
Qed.

(** An external call's return to an Iris-reachable configuration
    reaches an Iris-reachable one: [hs_call_return] under the callers. *)
Lemma reach_return c s w site spec xs trace values s' m' w' e :
  iris_reach c s w -> external_site ge c site -> registry (site_name site) = Some spec ->
  map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
  M.E.invoke spec (site_result site) (site_args site) xs s (c_mem c) w trace (CallReturn values) s' m' w' ->
  external_env spec site values (fr_env (c_frame c)) = Some e ->
  iris_reach (resume_external c site e m') s' w'.
Proof.
  intros Hr Hs Hreg Hx Hi He. destruct c as [fr cs m fuel]. eapply rtc_r; [exact Hr|].
  exact (head_erased registry ge cs _ _ _ _
           (hs_call_return registry ge fr m s fuel w site spec xs trace values s' m' w' e Hs Hreg Hx Hi He)).
Qed.

(** An Iris-reachable configuration's external call never returns
    words its call site cannot take: that would reach [EBad]. *)
Lemma reach_bad φ c s w site spec xs trace values s' m' w' :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> external_site ge c site -> registry (site_name site) = Some spec ->
  map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
  M.E.invoke spec (site_result site) (site_args site) xs s (c_mem c) w trace (CallReturn values) s' m' w' ->
  external_env spec site values (fr_env (c_frame c)) = None -> False.
Proof.
  intros Had Hr Hs Hreg Hx Hi He. destruct c as [fr cs m fuel].
  assert (Hr' : rtc (@erased_step (nanofil_lang registry ge)) ([ERun fr0], mkLstate m0 s0 fuel0 w0)
                  ([stack_expr EBad cs], mkLstate m' s' fuel w')).
  { eapply rtc_r; [exact Hr|].
    exact (head_erased registry ge cs _ _ _ _
             (hs_call_bad registry ge fr m s fuel w site spec xs trace values s' m' w' Hs Hreg Hx Hi He)). }
  destruct (adequate_not_stuck _ _ _ _ Had _ _ _ eq_refl Hr' ltac:(left)) as [[v Hv] | Hred].
  - change (to_val (stack_expr EBad cs) = Some v) in Hv.
    rewrite to_val_stack in Hv; [discriminate Hv | reflexivity].
  - exact (bad_stuck registry ge cs _ Hred).
Qed.

(** No external call of an Iris-reachable configuration is
    [M.rejected]: its frame [proceeds], and it is at a failing step, so
    its call is admissible. *)
Lemma reach_rejected φ c s w site why :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> external_site ge c site -> M.rejected world registry ge c w site why -> False.
Proof.
  intros Had Hr Hs Hrej.
  destruct (reach_proceeds φ c s w Had Hr) as [Hnf | (site' & Hs' & Hadm)].
  - apply Hnf. unfold fails. cbn [conf_state ls_mem ls_fuel].
    rewrite (external_site_stuck _ _ _ (external_site_frame ge c (c_mem c) (c_fuel c) site Hs)).
    exact I.
  - assert (site' = site) as ->.
    { eapply (external_site_unique ge); [|exact Hs'|exact Hs]. reflexivity. }
    destruct c as [fr cs m fuel].
    exact (M.admissible_not_rejected world registry ge (mkConfig fr cs m fuel) w site why Hadm Hrej).
Qed.

(** What adequacy says of a labelled machine state: a running state is
    Iris-reachable; a stopped one stopped with no [failure_ending], and
    a returning core ending satisfies φ in some state. *)
Definition labelled_good (φ : outcome -> lstate world -> Prop) (st : M.state world) : Prop :=
  match st with
  | M.Running ms w => iris_reach (fst ms) (snd ms) w
  | M.Stopped why _ _ =>
      ~ failure_ending why /\ forall o, why = CoreEnd o -> returning o -> exists σ, φ o σ
  end.

(** Every labelled step from an Iris-reachable running state reaches a
    [labelled_good] state: a core step is [reach_step]; an external
    return is [reach_return]; a core ending is [reach_end]; an exit is
    no failure, nor a resource ending ([invoke_resource_refusal]), nor
    a refusal; and a stuck core step, a rejected call and a bad return
    cannot happen. *)
Lemma reach_labelled φ c s w trace st :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> M.step registry ge (M.Running (c, s) w) trace st -> labelled_good φ st.
Proof.
  intros Had Hr Hs. inversion Hs; subst; cbn [labelled_good fst snd].
  - match goal with H : M.P.I.RM.mstep _ _ ?ms' |- _ =>
      destruct ms' as [c' s']; exact (reach_step φ c s w c' s' Had Hr (labelled_core_step _ _ _ H)) end.
  - match goal with Hn : forall site, ~ external_site _ _ site, E : Semantics.step _ _ = Done ?o |- _ =>
      destruct (reach_end φ c s w o Had Hr Hn E) as [Hf Hφ] end.
    split; [exact Hf|]. intros o' Ho. injection Ho as <-. exact Hφ.
  - exfalso. match goal with Hn : forall site, ~ external_site _ _ site,
                             E : Semantics.step _ _ = Stuck _ |- _ =>
      exact (reach_stuck φ c s w _ Had Hr Hn E) end.
  - split.
    + cbn. unfold refusal. tauto.
    + intros o Ho. injection Ho as <-. cbn. tauto.
  - eapply reach_return; eassumption.
  - split; [cbn; tauto | discriminate].
  - split.
    + match goal with Hi : M.E.invoke _ _ _ _ _ _ _ _ (CallResource _) _ _ _ |- _ =>
        exact (invoke_resource_refusal _ _ _ _ _ _ _ _ _ _ _ _ Hi) end.
    + intros o Ho. injection Ho as <-. cbn. tauto.
  - exfalso. eapply reach_rejected; eassumption.
  - exfalso. eapply reach_bad; eassumption.
Qed.

(** Adequacy for the labelled machine (ExternalMachine.v): where Iris
    adequacy holds for [ERun fr0] from m0, s0, fuel0 and w0, every
    running state of a labelled [[run]] from there is Iris-reachable,
    and every stopped state stopped with no [failure_ending]; where it
    stopped with a returning core ending, a top-level return, its value
    satisfies φ in some state. *)
Theorem adequate_labelled φ :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  forall trace st, M.run registry ge (M.Running (mkConfig fr0 [] m0 fuel0, s0) w0) trace st ->
  (forall c s w, st = M.Running (c, s) w -> iris_reach c s w) /\
  (forall why ms w, st = M.Stopped why ms w ->
     ~ failure_ending why /\ forall o, why = CoreEnd o -> returning o -> exists σ, φ o σ).
Proof.
  intros Had.
  assert (Hgen : forall st1 trace st2, M.run registry ge st1 trace st2 ->
            labelled_good φ st1 -> labelled_good φ st2).
  { intros st1 trace st2 H. induction H as [st | st tr mid tail last Hs _ IH]; [auto|].
    intros Hg. apply IH. destruct st as [[c s] w | why ms w].
    - exact (reach_labelled φ c s w tr mid Had Hg Hs).
    - exfalso. eapply M.stopped_no_step. exact Hs. }
  intros trace st Hrun. pose proof (Hgen _ _ _ Hrun (rtc_refl _ _)) as Hg.
  split.
  - intros c s w ->. exact Hg.
  - intros why ms w ->. exact Hg.
Qed.

End adequacy.

(** With no contracts no call is admissible: a frame [proceeds] only
    where it does not fail. *)
Lemma proceeds_closed ge fr σ :
  proceeds no_contracts ge fr σ -> ~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)).
Proof. intros [H | (site & _ & spec & xs & Hr & _)]; [exact H | unfold no_contracts in Hr; discriminate Hr]. Qed.

(** Where Iris adequacy holds for [ERun fr0] with no contracts, every
    core machine state the run reaches is Iris-reachable, and none
    [fails]. *)
Lemma adequate_no_fails ge fr0 m0 fuel0 φ :
  @adequate (nanofil_lang no_contracts ge) NotStuck (ERun fr0) (mkLstate m0 R.start fuel0 tt) φ ->
  forall st, RM.mreachable ge (mkConfig fr0 [] m0 fuel0, R.start) st -> ~ fails ge (fst st).
Proof.
  intros Had.
  pose (reach := fun st : RM.mstate =>
                   iris_reach no_contracts ge fr0 m0 R.start fuel0 tt (fst st) (snd st) tt).
  assert (Hgen : forall st1 st2, RM.mreachable ge st1 st2 -> reach st1 -> reach st2).
  { intros st1 st2 H. induction H as [[c s] [c' s'] Hs | st1 | st1 st2 st3 _ IH1 _ IH2]; auto.
    unfold reach. cbn. intros Hr. exact (reach_step _ _ _ _ _ _ _ φ c s tt c' s' Had Hr Hs). }
  intros [c s] Hreach. pose proof (Hgen _ _ Hreach (rtc_refl _ _)) as Hr. unfold reach in Hr.
  cbn [fst snd] in Hr |- *.
  apply (reach_not_fails _ _ _ _ _ _ _ φ c s tt Had Hr).
  exact (proceeds_closed ge (c_frame c) _ (reach_proceeds _ _ _ _ _ _ _ φ c s tt Had Hr)).
Qed.

(** [[adequacy|Adequacy]]: Iris adequacy proves [never_panics]. Where
    the module's initial memory and entry function exist, every
    admissible input makes the entry's frame, and (where R is ready at
    its start in that memory) for every fuel and every invariant
    instance a state interpretation stateI can be allocated that holds
    of the initial state and gives a [NotStuck] weakest precondition of
    the entry's [ERun], with no contracts, the module never panics. The
    later-credit flag hlc is left to the caller. *)
Theorem wp_never_panics (hlc : has_lc) Σ `{!invGpreS Σ} md entry (input : list word -> Prop) globals m f :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\
     (R.ready R.start m -> forall (fuel : Z) (Hinv : invGS_gen hlc Σ),
        ⊢ |={⊤}=> ∃ stateI : lstate unit -> iProp Σ,
            let _ : irisGS_gen hlc (nanofil_lang no_contracts (P.program_genv md globals)) Σ :=
              IrisG Hinv (λ σ _ _ _, stateI σ) (λ _, True%I) (λ _, 0%nat)
                    (λ _ _ _ _, fupd_intro _ _) in
            stateI (mkLstate m R.start fuel tt) ∗
            WP (ERun fr : language.expr (nanofil_lang no_contracts (P.program_genv md globals)))
              @ NotStuck; ⊤ {{ _, True }})) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hwp. exists globals, m, f. split; [exact Hm|]. split; [exact Hf|].
  intros xs Hxs. destruct (Hwp xs Hxs) as (fr & Hfr & Hw). exists fr. split; [exact Hfr|].
  intros Hready fuel st Hreach.
  set (ge := P.program_genv md globals) in *.
  assert (Had : @adequate (nanofil_lang no_contracts ge) NotStuck (ERun fr) (mkLstate m R.start fuel tt)
                  (λ _ _, True)).
  { apply (wp_adequacy_gen hlc Σ (nanofil_lang no_contracts ge) NotStuck _ _ (λ _, True)).
    intros Hinv κs. iMod (Hw Hready fuel Hinv) as (stateI) "[Hσ Hwp]". iModIntro.
    iExists (λ σ _, stateI σ), (λ _, True%I). cbn. iFrame "Hσ".
    iApply (wp_mono with "Hwp"). auto. }
  exact (adequate_no_fails ge fr m fuel _ Had st Hreach).
Qed.

(** The labelled machine's safety for the frame fr, with the contracts
    of registry in the genv ge, from the memory m, the runtime state s,
    the world w and the fuel fuel: every labelled [[run]] from there
    that stops, stops with no [failure_ending], and where it stops with
    a returning core ending, a top-level return, its value satisfies
    φ. *)
Definition labelled_safe {world : Type} (registry : name -> option (contract world)) (ge : genv)
    (fr : frame) (m : mem) (s : R.state) (w : world) (fuel : Z) (φ : outcome -> Prop) : Prop :=
  forall trace why ms w',
    M.run registry ge (M.Running (mkConfig fr [] m fuel, s) w) trace (M.Stopped why ms w') ->
    ~ failure_ending why /\ forall o, why = CoreEnd o -> returning o -> φ o.

(** [[adequacy|Adequacy]] for the labelled machine: where, for every
    invariant instance, a state interpretation stateI can be allocated
    that holds of the initial state (the memory m, the runtime state s,
    the fuel, the world w) and gives a [NotStuck] weakest precondition
    of [ERun fr] with the postcondition φ, the run is [labelled_safe].
    Where R must be [[ready]] in s and m, as for a ghost heap, that is
    the caller's premise for allocating stateI ([heap_labelled_safe]). *)
Theorem wp_labelled_safe (hlc : has_lc) Σ `{!invGpreS Σ} {world : Type}
    (registry : name -> option (contract world)) ge fr m s (w : world) fuel (φ : outcome -> Prop) :
  (forall Hinv : invGS_gen hlc Σ,
     ⊢ |={⊤}=> ∃ stateI : lstate world -> iProp Σ,
         let _ : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
           IrisG Hinv (λ σ _ _ _, stateI σ) (λ _, True%I) (λ _, 0%nat)
                 (λ _ _ _ _, fupd_intro _ _) in
         stateI (mkLstate m s fuel w) ∗
         WP (ERun fr : language.expr (nanofil_lang registry ge)) @ NotStuck; ⊤ {{ o, ⌜φ o⌝ }}) ->
  labelled_safe registry ge fr m s w fuel φ.
Proof.
  intros Hw trace why ms w' Hrun.
  assert (Had : @adequate (nanofil_lang registry ge) NotStuck (ERun fr) (mkLstate m s fuel w)
                  (λ o _, φ o)).
  { apply (wp_adequacy_gen hlc Σ (nanofil_lang registry ge) NotStuck _ _ φ).
    intros Hinv κs. iMod (Hw Hinv) as (stateI) "[Hσ Hwp]". iModIntro.
    iExists (λ σ _, stateI σ), (λ _, True%I). cbn. iFrame "Hσ". iExact "Hwp". }
  destruct (adequate_labelled registry ge fr m s fuel w _ Had _ _ Hrun) as [_ H].
  destruct (H why ms w' eq_refl) as [Hf Hφ]. split; [exact Hf|].
  intros o Ho Hr. destruct (Hφ o Ho Hr) as [σ Hσ]. exact Hσ.
Qed.

End Language.

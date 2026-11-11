(** A C function should have a specification that its callers can use
    without repeating the proof of its body. This module presents
    nanofil's [[machine]] as an [[iris|Iris]] language, separating the
    running function from the callers waiting for its result.
    Each suspended caller becomes an evaluation [[context]], allowing
    a function's [[hoare-triple|Hoare triple]] to return resources to that caller.

    The running [[frame]] supplies the next [[step]], while suspended
    callers matter only when control returns to them.
    Memory, [[runtime]] state, and remaining [[fuel]] belong to the
    shared language state, together with the external library's world.
    One fuel counter serves the whole stack rather than each function
    receiving a new execution budget.

    The language distinguishes a safety failure from a permitted end
    that produces no return, such as resource exhaustion or process exit.
    It represents such endings by steps back to the same expression,
    which Iris treats as safe execution that never returns.
    This encoding does not prove termination or promise that a blocked
    call will eventually finish.

    An [[external-call|external call]] must have a registered contract,
    evaluable arguments, a matching calling convention, and a satisfied precondition.
    An admissible call may return or stall, even when its contract
    permits no completed invocation at all.
    A rejected call has no step, and an incompatible return reaches
    [EBad], which is neither a result nor an expression that can step.

    Finally, [[adequacy]] connects the Iris proof to actual machine
    runs: no reachable state stops with a safety failure.
    With no external contracts, [wp_never_panics] establishes the
    closed program's panic freedom for every execution budget.
    With contracts, [wp_labelled_safe] also establishes the promised
    postcondition whenever the program returns normally. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language ectxi_language weakestpre adequacy.
From Stdlib Require Import ZArith Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics Steps
  ExternalCalls ExternalMachine.

(** The module [Language] presents function calls and external contracts
    as an Iris language over the chosen runtime R. *)
Module Language (R : Runtime).
Module P := Panics R.
Module RM := P.RM.
Module M := ExternalMachine R.

(** A function can return one word, several words, or no words;
    [returning] recognizes exactly those three kinds of [[outcome]]. *)
Definition returning (o : outcome) : Prop :=
  match o with Ret _ | Rets _ | RetVoid => True | _ => False end.

(** Inspecting an outcome's constructor decides whether it represents a
    return, without inspecting memory or the suspended caller's state. *)
Lemma returning_dec o : returning o \/ ~ returning o.
Proof. destruct o; cbn; tauto. Qed.

(** Running a configuration beneath additional callers appends those
    callers below its existing stack, which [lift_conf] constructs without changing memory. *)
Definition lift_conf (cs : list (frame * pending)) (c' : config) : config :=
  mkConfig (c_frame c') (c_callers c' ++ cs) (c_mem c') (c_fuel c').

(** Ordinary instructions never produce function returns; only a block's
    terminating jump can return control through [return_step] to a caller. *)
Lemma inst_step_stop ge fr m i o :
  inst_step ge fr m i = Some (IStop o) -> ~ returning o.
Proof.
  intros H. destruct i.
  1: destruct (special_let o0) eqn:Es;
       [destruct o0; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst;
    cbn; tauto.
Qed.

(** Handling a doomed instruction cannot manufacture a returning outcome;
    any return after [doomed_result] must already have been the instruction's result. *)
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

(** A stop produced while executing an instruction is not a function
    return, even after the model handles a doomed result. *)
Lemma stop_not_returning ge fr m i out od o :
  inst_step ge fr m i = Some out -> doomed_result ge fr m i out = Some od -> fst od = IStop o ->
  ~ returning o.
Proof.
  intros H1 H2 H3 Hr. pose proof (doomed_result_stop _ _ _ _ _ _ _ H2 H3 Hr) as ->.
  exact (inst_step_stop _ _ _ _ _ H1 Hr).
Qed.

(** Returning from the outermost function ends execution after invalidating
    its stack locals; failure to invalidate them leaves the machine stuck. *)
Lemma return_nil fr m fuel o :
  return_step (mkConfig fr [] m fuel) o =
  match invalidate_locals (fr_locals fr) m with Some _ => Done o | None => Stuck "return" end.
Proof. unfold return_step. cbn. destruct (invalidate_locals _ _); reflexivity. Qed.

(** Adding suspended callers changes how a return resumes execution,
    but it leaves ordinary steps, allocation requests, and other endings unchanged.
    The predicate [lifted] describes that correspondence, carrying the
    extra callers beneath any new frames created by the step. *)
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

(** A proof may need to avoid expanding unresolved case distinctions;
    the tactic [no_match] succeeds only when its argument contains none. *)
Ltac no_match x := lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end.

(** Suspended callers do not affect a running frame's instructions,
    allocation requests, or failures; only returning control consults their saved state.
    The lemma [step_callers] establishes the correspondence needed to
    treat the caller stack as an evaluation context. *)
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

(** An ordinary next step under extra callers produces the same
    configuration, with those callers appended beneath its resulting stack. *)
Lemma step_callers_next ge fr cs m fuel c' :
  Semantics.step ge (mkConfig fr [] m fuel) = Next c' ->
  Semantics.step ge (mkConfig fr cs m fuel) =
    Next (mkConfig (c_frame c') (c_callers c' ++ cs) (c_mem c') (c_fuel c')).
Proof. intros E. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H. exact H. Qed.

(** Adding suspended callers leaves an allocation request unchanged and
    carries those callers into the continuation for every possible allocated base. *)
Lemma step_callers_fresh ge fr cs m fuel q k :
  Semantics.step ge (mkConfig fr [] m fuel) = Fresh q k ->
  exists k', Semantics.step ge (mkConfig fr cs m fuel) = Fresh q k' /\
    forall base, k' base = mkConfig (c_frame (k base)) (c_callers (k base) ++ cs)
                                    (c_mem (k base)) (c_fuel (k base)).
Proof. intros E. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H. exact H. Qed.

(** A nonreturning end stops execution with the same outcome regardless
    of how many callers were waiting for the function. *)
Lemma step_callers_stop ge fr cs m fuel o :
  Semantics.step ge (mkConfig fr [] m fuel) = Done o -> ~ returning o ->
  Semantics.step ge (mkConfig fr cs m fuel) = Done o.
Proof.
  intros E Hr. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H.
  destruct H as [[_ H] | [H _]]; [exact H | contradiction].
Qed.

(** A return from a standalone frame can invalidate its locals and
    becomes [return_step] when suspended callers are placed beneath it. *)
Lemma step_callers_return ge fr cs m fuel o :
  Semantics.step ge (mkConfig fr [] m fuel) = Done o -> returning o ->
  Semantics.step ge (mkConfig fr cs m fuel) = return_step (mkConfig fr cs m fuel) o /\
  exists m', invalidate_locals (fr_locals fr) m = Some m'.
Proof.
  intros E Hr. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H.
  destruct H as [[H _] | [_ H]]; [contradiction | exact H].
Qed.

(** Suspending additional callers cannot repair a stuck instruction;
    the running frame remains stuck with any caller stack beneath it. *)
Lemma step_callers_stuck ge fr cs m fuel w :
  Semantics.step ge (mkConfig fr [] m fuel) = Stuck w ->
  exists w', Semantics.step ge (mkConfig fr cs m fuel) = Stuck w'.
Proof. intros E. pose proof (step_callers ge fr cs m fuel) as H. rewrite E in H. exact H. Qed.

(** Whether a [[poll|safepoint]] is due depends only on the running
    frame, so adding suspended callers does not change that decision. *)
Lemma safepoint_due_callers ge fr cs m fuel :
  RM.safepoint_due ge (mkConfig fr cs m fuel) = RM.safepoint_due ge (mkConfig fr [] m fuel).
Proof. reflexivity. Qed.

(** A returning function must convert its result to the caller's
    convention and bind the returned words in the caller's environment.
    The function [resume] performs those operations on a saved frame,
    returning no frame when the result cannot be accepted. *)
Definition resume (cf : frame) (pd : pending) (o : outcome) : option frame :=
  let* o' := match pd_conv pd with
             | None => Some o
             | Some (cw, kw) => converted_outcome cw kw o
             end in
  let* e := returned_env (pd_res pd) o' (fr_env cf) in
  Some (mkFrame (fr_fn cf) e (fr_locals cf) (fr_doomed cf) (fr_at cf)).

(** After invalidating the callee's locals, a return resumes the nearest
    caller with its remaining stack, or becomes stuck if result conversion fails. *)
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

(** Once a function's locals have been invalidated, returning with no
    suspended caller ends execution with the function's returned outcome. *)
Lemma return_nil_done fr m m' fuel o :
  invalidate_locals (fr_locals fr) m = Some m' ->
  return_step (mkConfig fr [] m fuel) o = Done o.
Proof. intros E. rewrite return_nil E. reflexivity. Qed.

(** ## External calls

    Calling code outside the module requires a contract rather than
    another function body that the core machine can execute.
    The following facts identify such call sites and distinguish an
    allowed resource refusal from a violation of the caller's obligations. *)

(** The running frame alone determines whether execution has reached an
    external call site, independently of memory, fuel, or suspended callers. *)
Lemma external_site_frame ge c m fuel site :
  external_site ge c site -> external_site ge (mkConfig (c_frame c) [] m fuel) site.
Proof. intros H. exact H. Qed.

(** A frame's next instruction determines at most one external call
    site, including the symbol, arguments, result location, and continuation. *)
Lemma external_site_unique ge c c' site site' :
  c_frame c = c_frame c' -> external_site ge c site -> external_site ge c' site' -> site = site'.
Proof.
  unfold external_site. cbv zeta. intros Hf (_ & Ha & _) (_ & Ha' & _).
  destruct site, site'. cbn in *.
  rewrite Hf Ha' in Ha. injection Ha. intros. subst. reflexivity.
Qed.

(** Every completed contract invocation began with a matching calling
    convention and a satisfied precondition, regardless of how the call ended. *)
Lemma invoke_admissible {world : Type} (spec : contract world) r args xs s m w trace ending s' m' w' :
  M.E.invoke spec r args xs s m w trace ending s' m' w' ->
  contract_abi spec r args /\ contract_pre spec xs m w.
Proof. intros H. destruct H; auto. Qed.

(** A contract's resource ending reports exhausted memory or an oversized
    request, both permitted refusals rather than failures of program safety. *)
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

(** The labelled machine and this language instantiate the same core
    machine definitions, so [labelled_core_step] translates a step between their relation instances. *)
Lemma labelled_core_step ge ms ms' : M.P.I.RM.mstep ge ms ms' -> RM.mstep ge ms ms'.
Proof.
  intros H. destruct H; [eapply RM.mstep_next | eapply RM.mstep_alloc | eapply RM.mstep_safepoint];
    eassumption.
Qed.

(** ## The language

    Iris needs an expression for the running computation and a separate
    state for memory, runtime bookkeeping, fuel, and the external world.
    The expression records suspended callers around the current function,
    allowing one function's proof to be used inside another function's call. *)

(** An expression records a running frame, a completed outcome, a callee
    beneath a waiting caller, or an incompatible external return.
    The type [expr] represents these cases explicitly, keeping [EBad]
    separate from completed values so a safety proof must exclude it. *)
Inductive expr : Type :=
| ERun (fr : frame)
| EEnd (o : outcome)
| EWait (e : expr) (cf : frame) (pd : pending)
| EBad.

(** A suspended caller stores its saved frame and result convention;
    [ectx_item] packages those together as one evaluation-context item. *)
Inductive ectx_item : Type := KWait (cf : frame) (pd : pending).

(** Placing a callee beneath one suspended caller produces a waiting
    expression, which [fill_item] constructs without changing the shared machine state. *)
Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with KWait cf pd => EWait e cf pd end.

(** A completed function outcome becomes a language value through
    [of_val], which wraps it as an ended expression without further execution. *)
Definition of_val (o : outcome) : expr := EEnd o.

(** Only an ended expression supplies a value through [to_val]; running
    frames, waiting callers, and bad returns supply no value. *)
Definition to_val (e : expr) : option outcome :=
  match e with EEnd o => Some o | _ => None end.

(** All frames share memory, runtime bookkeeping, one fuel counter, and
    an external-library world, which [lstate] collects as the Iris language state. *)
Record lstate (world : Type) : Type :=
  mkLstate { ls_mem : mem; ls_rt : R.state; ls_fuel : Z; ls_world : world }.
Arguments mkLstate {world}.
Arguments ls_mem {world}.
Arguments ls_rt {world}.
Arguments ls_fuel {world}.
Arguments ls_world {world}.

(** The function [stack_expr] nests an expression beneath suspended
    callers in stack order, placing the nearest caller around it first. *)
Fixpoint stack_expr (e : expr) (cs : list (frame * pending)) : expr :=
  match cs with
  | [] => e
  | (cf, pd) :: cs' => stack_expr (EWait e cf pd) cs'
  end.

(** The function [ctx_of] turns each suspended caller into an Iris
    context item, preserving the stack's innermost-first order for later filling. *)
Definition ctx_of (cs : list (frame * pending)) : list ectx_item :=
  map (fun '(cf, pd) => KWait cf pd) cs.

(** A machine configuration becomes a language expression through
    [conf_expr], which places its running frame beneath the configuration's suspended callers. *)
Definition conf_expr (c : config) : expr := stack_expr (ERun (c_frame c)) (c_callers c).

(** A machine configuration supplies memory and fuel, while [conf_state]
    adds the runtime bookkeeping and external world needed by the language. *)
Definition conf_state {world : Type} (c : config) (s : R.state) (w : world) : lstate world :=
  mkLstate (c_mem c) s (c_fuel c) w.

(** After an external return, [resumed_frame] installs the updated
    environment and advances the frame to the instruction following the call. *)
Definition resumed_frame (fr : frame) (site : call_site) (e : env) : frame :=
  mkFrame (fr_fn fr) e (fr_locals fr) None (Exec (site_label site) (site_rest site) (site_jump site)).

(** Resuming an external call updates the running frame exactly as
    [resumed_frame] specifies, while the surrounding configuration retains its other execution data. *)
Lemma resume_external_frame c site e m :
  c_frame (resume_external c site e m) = resumed_frame (c_frame c) site e.
Proof. reflexivity. Qed.

(** Returned words either bind successfully and resume the caller, or
    produce a bad expression when the call site cannot accept them.
    The function [returned_expr] makes this distinction visible to Iris,
    so a safety proof must rule out incompatible results. *)
Definition returned_expr {world : Type} (fr : frame) (spec : contract world) (site : call_site)
    (values : list word) : expr :=
  match external_env spec site values (fr_env fr) with
  | Some e => ERun (resumed_frame fr site e)
  | None => EBad
  end.

(** An empty contract registry permits no external call, which
    [no_contracts] represents using a world with no external-library state. *)
Definition no_contracts : name -> option (contract unit) := fun _ => None.

(** The following language steps use a fixed global environment and
    registry, whose contracts all describe the same external-world type. *)
Section language.
Context {world : Type} (registry : name -> option (contract world)) (ge : genv).

(** An external call is admissible when its contract exists, its
    arguments evaluate, and its calling convention and precondition are satisfied.
    The predicate [call_admissible] checks these requirements for the
    current frame without consulting suspended callers. *)
Definition call_admissible (fr : frame) (σ : lstate world) : Prop :=
  exists site, external_site ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) site /\
    M.admissible registry ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) (ls_world σ) site.

(** A running frame can proceed when its core step does not fail or
    when its next external call satisfies its contract.
    The predicate [proceeds] captures exactly when the language can
    supply a step for that frame. *)
Definition proceeds (fr : frame) (σ : lstate world) : Prop :=
  ~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)) \/ call_admissible fr σ.

(** One language step executes the running frame or resumes a caller,
    without emitting observations or creating additional threads.
    The relation [head_step] follows ordinary machine steps, granted
    allocations, returns, due safepoints, and contracted external calls.

    Refused allocations and other permitted nonreturning endings step
    back to the same expression rather than becoming stuck.
    An admissible external call may likewise stall, representing a
    blocking call, process exit, resource refusal, or absence of a completed invocation.
    Safepoints require a frame that can otherwise proceed, so they
    cannot hide a failing instruction or rejected call.

    A compatible external return resumes execution with the invocation's
    updated memory, runtime state, and world; an incompatible return produces [EBad].
    Returning from an internal function first produces an ended value,
    then a separate step resumes its waiting caller. *)
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

(** The waiting-caller representation must obey Iris's language laws:
    values cannot step, and placing a caller around an expression cannot create a value.
    The lemma [nanofil_mixin] also shows that a waiting caller resumes
    only after its callee has become a value. *)
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

(** The structure [nanofil_ectxi_lang] packages the machine and contracts
    as an Iris language whose context items are individual suspended callers. *)
Canonical Structure nanofil_ectxi_lang {world : Type} (registry : name -> option (contract world))
    (ge : genv) : ectxiLanguage :=
  EctxiLanguage (nanofil_mixin registry ge).
(** The structure [nanofil_ectx_lang] presents the same execution rules
    with whole caller contexts rather than individual suspended caller items. *)
Canonical Structure nanofil_ectx_lang {world : Type} (registry : name -> option (contract world))
    (ge : genv) : ectxLanguage :=
  EctxLanguageOfEctxi (nanofil_ectxi_lang registry ge).
(** The structure [nanofil_lang] exposes the same expressions and steps
    through Iris's basic language interface, without requiring callers to mention contexts. *)
Canonical Structure nanofil_lang {world : Type} (registry : name -> option (contract world))
    (ge : genv) : language :=
  LanguageOfEctx (nanofil_ectx_lang registry ge).

(** Nesting an expression beneath two concatenated caller stacks equals
    nesting it beneath the first stack and then beneath the second. *)
Lemma stack_expr_app e cs1 cs2 :
  stack_expr e (cs1 ++ cs2) = stack_expr (stack_expr e cs1) cs2.
Proof.
  revert e. induction cs1 as [|[cf pd] cs1 IH]; intros e; [reflexivity|]. cbn. apply IH.
Qed.

(** A computation that has not returned cannot become a value merely
    because additional callers are placed around its expression. *)
Lemma to_val_stack e cs : to_val e = None -> to_val (stack_expr e cs) = None.
Proof.
  revert e. induction cs as [|[cf pd] cs IH]; intros e H; [exact H|]. cbn. apply IH. reflexivity.
Qed.

(** The following facts relate the machine's caller stack to Iris
    contexts for a fixed global environment and contract registry. *)
Section facts.
Context {world : Type} (registry : name -> option (contract world)) (ge : genv).

(** Saved callers must resume in the same order whether execution uses
    a machine stack or Iris's surrounding expression contexts.
    The lemma [stack_expr_fill] equates these two representations of the
    running computation, preserving the order of every saved caller. *)
Lemma stack_expr_fill e cs :
  stack_expr e cs = @ectx_language.fill (nanofil_ectx_lang registry ge) (ctx_of cs) e.
Proof.
  revert e. induction cs as [|[cf pd] cs IH]; intros e; [reflexivity|].
  cbn [stack_expr]. rewrite IH. reflexivity.
Qed.

(** Executing the current expression beneath any suspended callers gives
    an Iris execution step for the model's single-threaded pool. *)
Lemma head_erased cs e1 σ1 e2 σ2 :
  head_step registry ge e1 σ1 [] e2 σ2 [] ->
  @erased_step (nanofil_lang registry ge) ([stack_expr e1 cs], σ1) ([stack_expr e2 cs], σ2).
Proof.
  intros H. exists []. apply (step_atomic (stack_expr e1 cs) σ1 (stack_expr e2 cs) σ2 [] [] []);
    [reflexivity | reflexivity |].
  rewrite !stack_expr_fill.
  exact (Ectx_step' (Λ := nanofil_ectx_lang registry ge) _ _ _ _ _ _ _ H).
Qed.

(** Saved callers cannot execute until the current computation returns,
    so they cannot provide a missing step for that computation.
    The lemma [ctx_base_reducible] applies when the current expression
    has not returned and any child computation has already produced its value. *)
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

(** Every step of a running frame falls into an ordinary machine,
    allocation, return, stall, safepoint, or external-call case.
    The lemma [head_step_run_inv] exposes these alternatives without
    observations or new threads, allowing instruction proofs to handle each case. *)
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

(** A frame that takes a language step either avoids core failure or
    satisfies its external-call contract, as [run_proceeds] establishes. *)
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

(** Any frame whose standalone core step does not fail can take a
    language step, including a stall for permitted nonreturning endings. *)
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

(** An admissible external call can always stall, so it can step even
    when its contract allows no completed return. *)
Lemma admissible_reducible fr σ :
  call_admissible registry ge fr σ -> @base_reducible (nanofil_ectx_lang registry ge) (ERun fr) σ.
Proof.
  destruct σ as [m s fuel w]. intros (site & Hs & spec & xs & Hr & Hx & Ha & Hp).
  do 4 eexists. eapply hs_call_wait; eassumption.
Qed.

(** Execution can take another step when an instruction avoids failure
    or an external call meets its registered contract's precondition.
    The lemma [proceeds_reducible] supplies that step, including a
    permitted stall when no returning external invocation is available. *)
Lemma proceeds_reducible fr σ :
  proceeds registry ge fr σ -> @base_reducible (nanofil_ectx_lang registry ge) (ERun fr) σ.
Proof. intros [H | H]; [exact (run_reducible _ _ H) | exact (admissible_reducible _ _ H)]. Qed.

(** Once a callee has returned, further execution requires its waiting
    caller to accept the outcome, regardless of any outer callers. *)
Lemma wait_resumes cs o cf pd σ :
  @reducible (nanofil_lang registry ge) (stack_expr (EWait (EEnd o) cf pd) cs) σ ->
  exists cf', resume cf pd o = Some cf'.
Proof.
  intros H. apply ctx_base_reducible in H as (κ & e' & σ' & efs & Hs).
  - inversion Hs; subst. eauto.
  - reflexivity.
  - intros [cf' pd'] e' Heq. cbn in Heq. injection Heq as <- _ _. eexists. reflexivity.
Qed.

(** A caller cannot continue after receiving words it cannot accept
    from an external function, regardless of any other saved callers.
    The lemma [bad_stuck] shows that wrapping this rejected return in
    additional caller expressions cannot supply another execution step. *)
Lemma bad_stuck cs σ : ~ @reducible (nanofil_lang registry ge) (stack_expr EBad cs) σ.
Proof.
  intros H. apply ctx_base_reducible in H as (κ & e' & σ' & efs & Hs).
  - inversion Hs.
  - reflexivity.
  - intros [cf pd] e' Heq. discriminate Heq.
Qed.

(** If a configuration's expression is not stuck, its running frame
    must satisfy [proceeds], even when surrounded by suspended callers. *)
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

(** ## Adequacy

    A proof about Iris expressions is useful only if it also rules
    out safety failures in actual machine executions.
    The following simulation follows each machine step beneath its
    suspended callers, including external returns, and transfers Iris's safety guarantee to those runs. *)

(** The simulation fixes an initial frame, memory, runtime state, fuel,
    and external world, together with the program environment and contract registry. *)
Section adequacy.
Context {world : Type} (registry : name -> option (contract world)) (ge : genv)
  (fr0 : frame) (m0 : mem) (s0 : R.state) (fuel0 : Z) (w0 : world).

(** A configuration is reachable in Iris when its expression and shared
    state follow the initial expression by zero or more execution steps.
    The predicate [iris_reach] records this connection for the machine
    configuration, runtime bookkeeping, and external world. *)
Definition iris_reach (c : config) (s : R.state) (w : world) : Prop :=
  rtc (@erased_step (nanofil_lang registry ge))
    ([ERun fr0], mkLstate m0 s0 fuel0 w0) ([conf_expr c], conf_state c s w).

(** Iris's safety guarantee ensures that every reachable running frame
    can proceed, either through the core machine or an admissible external call. *)
Lemma reach_proceeds φ c s w :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> proceeds registry ge (c_frame c) (conf_state c s w).
Proof.
  intros Had Hr. apply (conf_reducible registry ge c s w).
  apply (adequate_not_stuck _ _ _ _ Had _ _ (conf_expr c) eq_refl Hr). left.
Qed.

(** Every core machine step from an Iris-reachable state reaches another
    such state without changing the external world.
    Ordinary execution, allocation, and safepoints use one language step;
    returning to a caller uses one step to return and another to resume. *)
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

(** A reachable configuration cannot fail when its standalone frame is
    safe, because an incompatible caller return would contradict Iris's safety guarantee. *)
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

(** Away from an external call site, every reachable configuration
    avoids core-machine failure, as [reach_core] derives from Iris's safety guarantee. *)
Lemma reach_core φ c s w :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> (forall site, ~ external_site ge c site) -> ~ fails ge c.
Proof.
  intros Had Hr Hns. apply (reach_not_fails φ c s w Had Hr).
  destruct (reach_proceeds φ c s w Had Hr) as [Hnf | (site & Hs & _)]; [exact Hnf|].
  exfalso. exact (Hns site Hs).
Qed.

(** A reachable core ending outside external calls cannot be a failure;
    a normal return also satisfies the promised postcondition in some language state. *)
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

(** A reachable configuration outside an external call site cannot
    produce a stuck core step, as [reach_stuck] derives from adequacy. *)
Lemma reach_stuck φ c s w why :
  @adequate (nanofil_lang registry ge) NotStuck (ERun fr0) (mkLstate m0 s0 fuel0 w0) φ ->
  iris_reach c s w -> (forall site, ~ external_site ge c site) ->
  Semantics.step ge c <> Stuck why.
Proof.
  intros Had Hr Hns E. apply (reach_core φ c s w Had Hr Hns). unfold fails. rewrite E. exact I.
Qed.

(** When a library returns acceptable words, the caller resumes with
    the memory and library state produced by that invocation.
    The lemma [reach_return] extends the corresponding Iris execution
    path to include this return and its updated runtime state. *)
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

(** A reachable external call cannot return incompatible words under
    Iris's safety guarantee, since such a return would reach the stuck expression [EBad]. *)
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

(** A reachable external call cannot be rejected: its frame must
    proceed, and only an admissible contract can permit that step. *)
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

(** A labelled state is good when execution remains Iris-reachable or
    has stopped safely, with any normal return satisfying the postcondition.
    The predicate [labelled_good] collects these cases for the simulation
    of whole machine runs. *)
Definition labelled_good (φ : outcome -> lstate world -> Prop) (st : M.state world) : Prop :=
  match st with
  | M.Running ms w => iris_reach (fst ms) (snd ms) w
  | M.Stopped why _ _ =>
      ~ failure_ending why /\ forall o, why = CoreEnd o -> returning o -> exists σ, φ o σ
  end.

(** Every labelled step preserves reachability or stops safely, including
    external returns, process exit, and permitted resource refusals.
    The lemma [reach_labelled] excludes stuck instructions, rejected
    calls, and incompatible results by the earlier simulation facts. *)
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

(** Iris's safety guarantee covers every labelled machine [[run]] from
    the initial state, not merely the execution chosen by a particular interpreter.
    The theorem [adequate_labelled] keeps running states reachable,
    excludes failure endings, and establishes the postcondition for normal top-level returns. *)
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

(** Without external contracts, no external call is admissible, so a
    frame that proceeds must avoid failure in the core machine itself. *)
Lemma proceeds_closed ge fr σ :
  proceeds no_contracts ge fr σ -> ~ fails ge (mkConfig fr [] (ls_mem σ) (ls_fuel σ)).
Proof. intros [H | (site & _ & spec & xs & Hr & _)]; [exact H | unfold no_contracts in Hr; discriminate Hr]. Qed.

(** With no external contracts, Iris adequacy rules out failure in
    every reachable core-machine state, as [adequate_no_fails] derives from the simulation. *)
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

(** A closed program never panics if its entry function has a safe Iris
    proof for every admitted input and execution budget.
    The theorem [wp_never_panics] requires valid initial memory, an
    entry frame for each input, and a runtime ready to begin execution.

    Memory ownership gives an instruction proof permission to read or
    write bytes, while the machine itself operates on concrete memory.
    A [[state-interpretation|state interpretation]] connects these two
    views, and the proof must establish that connection before execution begins.
    The entry proof then describes safe execution through a
    [[weakest-precondition|weakest precondition]], without assuming any particular allocation of Iris invariants.
    The theorem permits either setting of Iris's later-credit feature,
    which controls bookkeeping in the proof rather than the program's execution. *)
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

(** A contracted program is safe when every stopped run avoids a
    failure ending and every normal top-level return satisfies the promised postcondition.
    The predicate [labelled_safe] states that guarantee for a fixed
    initial frame, memory, runtime state, world, and execution budget. *)
Definition labelled_safe {world : Type} (registry : name -> option (contract world)) (ge : genv)
    (fr : frame) (m : mem) (s : R.state) (w : world) (fuel : Z) (φ : outcome -> Prop) : Prop :=
  forall trace why ms w',
    M.run registry ge (M.Running (mkConfig fr [] m fuel, s) w) trace (M.Stopped why ms w') ->
    ~ failure_ending why /\ forall o, why = CoreEnd o -> returning o -> φ o.

(** An entry proof establishes safe execution and a promised result
    property whenever the program returns normally at the top level.
    The theorem [wp_labelled_safe] transfers that proof to complete
    machine runs, provided ownership describes initial memory for every Iris invariant instance.
    If establishing this description needs a [[ready]] runtime, the
    caller must supply readiness among its own initial assumptions. *)
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

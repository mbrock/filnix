(** This module models whole-program execution across `c: main`, its coupled
    libc stdio state, and process shutdown. Every external call must satisfy
    its preconditions at the point where it is reached rather than assuming
    those preconditions from the existence of a return witness. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import LibcCallFixtures Term Syntax Values Memory Runtime Ops Semantics Identity
  ExternalCalls LibcCalls Startup Stdio Shutdown ExternalMachine Hi Composition Panics.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** This outer development leaves every core module and terminal unchanged. *)
Module Program (R : Runtime).
Module C := Composition R.
Module H := C.H.
Module M := C.M.

Section Body.
Variable rep : mem -> stdio_world -> Prop.
Variable requests : list word -> mem -> stdio_world -> Z -> Z -> Prop.

(** Garbage-collector pauses must keep the stream representation and stdio
    readiness valid across execution steps. *)
Hypothesis stdio_stable : forall s m s' m' w,
  R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
  rep m' w /\ stdio_ready m' w.

(** Only `c: puts` is linked through this coupled world registry. *)
Definition registry (symbol : name) : option (contract program_world) :=
  if name_eqb symbol (TAtom "puts") then Some (program_puts rep requests) else None.

(** Projecting a program state forgets the logical stdout buffer and
    callback list while leaving the underlying machine snapshot intact. *)
Definition project (st : M.state program_world) : M.state stdio_world :=
  match st with
  | M.Running ms w => M.Running ms (program_stdio w)
  | M.Stopped why ms w => M.Stopped why ms (program_stdio w)
  end.

(** The richer world stays attached to running and stopped states alike. *)
Definition world_of (st : M.state program_world) : program_world :=
  match st with M.Running _ w | M.Stopped _ _ w => w end.

(** The whole-program invariant combines `c: main`'s body invariant with
    well-formedness of the coupled world and a non-wide stdout stream. *)
Definition body_inv (st : M.state program_world) : Prop :=
  H.hi_body_state rep (project st) /\ program_world_wf (world_of st) /\
  orientation (program_stdout (world_of st)) <> WideOriented.

(** No rich-world precondition is hidden behind a successful invoke. *)
Theorem reached_admissible : forall c s w site,
  body_inv (M.Running (c, s) w) -> external_site H.hi_genv c site ->
  M.admissible registry H.hi_genv c w site.
Proof.
  intros c s w site [Hbody [Hwf Ho]] Hsite.
  destruct (H.hi_reached_call_admissible rep requests _ _ _ _ Hbody Hsite) as [Heq Hadmit].
  subst site. destruct Hadmit as (spec & xs & Hreg & Hargs & Habi & Hpre).
  change (Some (puts_contract rep requests) = Some spec) in Hreg. injection Hreg as <-.
  exists (program_puts rep requests), xs. split; [reflexivity|].
  split; [exact Hargs|]. split; [exact Habi|]. split; [exact Hpre|]. auto.
Qed.

(** Exact call syntax selects the coupled contract, not an arbitrary registry entry. *)
Lemma selected_call : forall c s w site spec xs,
  body_inv (M.Running (c, s) w) -> external_site H.hi_genv c site ->
  registry (site_name site) = Some spec ->
  map_option (arg_x H.hi_genv (fr_env (c_frame c))) (site_args site) = Some xs ->
  site = hi_site /\ spec = program_puts rep requests.
Proof.
  intros c s w site spec xs [Hbody _] Hsite Hreg Hargs.
  destruct (H.hi_reached_call_admissible rep requests _ _ _ _ Hbody Hsite) as [-> _].
  split; [reflexivity|]. change (Some (program_puts rep requests) = Some spec) in Hreg.
  congruence.
Qed.

(** Projection includes rejected-call cases: independently proved rich
    admissibility rules them out rather than silently deleting them. *)
Lemma step_projects : forall st trace st',
  M.step registry H.hi_genv st trace st' -> body_inv st ->
  M.step (H.hi_registry rep requests) H.hi_genv (project st) trace (project st').
Proof.
  intros st trace st' Hstep Hinv.
  destruct Hstep as
    [ms ms' w Hcore
    |c s w o Hnone Hdone
    |c s w why Hnone Hstuck
    |c s w q k Hnone Hfresh Hsize Hrefuse
    |c s w site spec xs trace values s' m' w' e Hsite Hreg Hargs Hcall Henv
    |c s w site spec xs trace status s' m' w' Hsite Hreg Hargs Hcall
    |c s w site spec xs trace why s' m' w' Hsite Hreg Hargs Hcall
    |c s w site why Hsite Hreject
    |c s w site spec xs trace values s' m' w' Hsite Hreg Hargs Hcall Henv]; simpl.
  - apply M.step_core. exact Hcore.
  - apply M.step_core_end; assumption.
  - apply M.step_core_stuck; assumption.
  - eapply M.step_core_refusal; eauto.
  - destruct (selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs) as [-> ->].
    eapply M.step_return; [exact Hsite|reflexivity|exact Hargs| |exact Henv].
    eapply C.program_invoke_projects; eauto.
  - destruct (selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs) as [-> ->].
    eapply M.step_exit; [exact Hsite|reflexivity|exact Hargs|].
    eapply C.program_invoke_projects; eauto.
  - destruct (selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs) as [-> ->].
    eapply M.step_resource; [exact Hsite|reflexivity|exact Hargs|].
    eapply C.program_invoke_projects; eauto.
  - exfalso. eapply M.admissible_not_rejected; [eapply reached_admissible; eauto|exact Hreject].
  - destruct (selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs) as [-> ->].
    eapply M.step_bad_return; [exact Hsite|reflexivity|exact Hargs| |exact Henv].
    eapply C.program_invoke_projects; eauto.
Qed.

(** Stream evolution also preserves the extra world obligations. *)
Lemma body_step : forall st trace st',
  M.step registry H.hi_genv st trace st' -> body_inv st -> body_inv st'.
Proof.
  intros st trace st' Hstep Hinv.
  pose proof (step_projects _ _ _ Hstep Hinv) as Hproject.
  destruct Hinv as [Hbody [Hwf Ho]]. split.
  - eapply H.hi_body_step; [exact stdio_stable|exact Hproject|exact Hbody].
  - destruct Hstep; simpl in *; try (split; assumption).
    all: assert (Hselected : spec = program_puts rep requests).
    all: try (destruct (H.hi_reached_call_admissible rep requests _ _ _ _ Hbody H) as [Heq _];
      rewrite Heq in H0; change (Some (program_puts rep requests) = Some spec) in H0; congruence).
    all: subst spec.
    all: destruct (C.program_invoke_continuity _ _ _ _ _ _ _ _ _ _ _ _ _ H2)
      as [_ [Hstream Hwf']].
    all: split; [exact Hwf'|].
    all: destruct Hstream as (p & bytes & actions & tail & _ & _ & Hrun & _).
    all: eapply stream_run_nonwide; eauto.
Qed.

(** Every finite richer run retains the old safety facts and the new
    obligations. This is not inferred from invoke projection alone. *)
Theorem body_run : forall st trace st',
  M.run registry H.hi_genv st trace st' -> body_inv st -> body_inv st'.
Proof.
  intros st trace st' H. induction H; [auto|]. intros Hinv.
  apply IHrun. eapply body_step; eauto.
Qed.

(** The application cannot replace the entry's callback inventory with a
    different list merely because the replacement has distinct tokens. *)
Lemma body_step_inventory : forall st trace st',
  M.step registry H.hi_genv st trace st' -> body_inv st ->
  program_pending (world_of st') = program_pending (world_of st).
Proof.
  intros st trace st' Hstep Hinv. destruct Hinv as [Hbody _].
  destruct Hstep; simpl in *; try reflexivity.
  all: assert (Hselected : spec = program_puts rep requests).
  all: try (destruct (H.hi_reached_call_admissible rep requests _ _ _ _ Hbody H) as [Heq _];
    rewrite Heq in H0; change (Some (program_puts rep requests) = Some spec) in H0; congruence).
  all: subst spec.
  all: exact (proj1 (C.program_invoke_continuity _ _ _ _ _ _ _ _ _ _ _ _ _ H2)).
Qed.

(** Every reached call keeps the actual initial registration list, not
    an arbitrary well-formed inventory admitted by the raw contract. *)
Theorem body_run_inventory : forall st trace st',
  M.run registry H.hi_genv st trace st' -> body_inv st ->
  program_pending (world_of st') = program_pending (world_of st).
Proof.
  intros st trace st' Hrun. induction Hrun; [reflexivity|]. intros Hinv.
  rewrite IHHrun by (eapply body_step; eauto). eapply body_step_inventory; eauto.
Qed.

(** Every reachable rich-world external call meets all additional premises. *)
Theorem all_calls_admissible : forall st trace c s w site,
  body_inv st -> M.run registry H.hi_genv st trace (M.Running (c, s) w) ->
  external_site H.hi_genv c site -> M.admissible registry H.hi_genv c w site.
Proof.
  intros st trace c s w site Hinv Hrun Hsite.
  eapply reached_admissible; [eapply body_run; eauto|exact Hsite].
Qed.

(** Additional contract premises do not introduce specification-violation
    terminals. Finite safety remains conditional, without native totality. *)
Theorem finite_safety : forall st trace why ms w,
  body_inv st -> M.run registry H.hi_genv st trace (M.Stopped why ms w) -> H.hi_ending why.
Proof.
  intros st trace why ms w Hinv Hrun.
  destruct (body_run _ _ _ Hrun Hinv) as [Hbody _]. inversion Hbody. assumption.
Qed.

(** Normal termination, out-of-fuel stops, and genuine resource refusals
    never count as capability panics under the shared failure predicate. *)
Lemma hi_ending_not_failure : forall why, H.hi_ending why -> ~ failure_ending why.
Proof.
  intros why [->|[->|(resource & -> & Hr)]]; simpl; tauto.
Qed.

(** Every stopped application run avoids capability panics and contract
    violations under the same failure predicate used by closed modules. *)
Theorem application_never_panics : forall st trace why ms w,
  body_inv st -> M.run registry H.hi_genv st trace (M.Stopped why ms w) ->
  ~ failure_ending why.
Proof. intros st trace why ms w Hinv Hrun. apply hi_ending_not_failure. eapply finite_safety; eauto. Qed.

(** Every application observation is exit-free, including resource leaves. *)
Lemma application_exit_free : forall st trace st' status,
  M.step registry H.hi_genv st trace st' -> body_inv st -> ~ In (ProcessExit status) trace.
Proof.
  intros st trace st' status Hstep Hinv. destruct Hstep; simpl; try tauto.
  all: destruct (selected_call _ _ _ _ _ _ Hinv H H0 H1) as [-> ->].
  all: destruct (C.program_invoke_continuity _ _ _ _ _ _ _ _ _ _ _ _ _ H2)
    as [_ [Hstream _]].
  all: eapply puts_stream_prefix_exit_free; eauto.
Qed.

End Body.

(** Pure control actions observe no new stdout acceptance; starting a
    callback is not an atomic execution of its entire printing body. *)
Definition action_events (action : shutdown_action) : list event :=
  match action with ShutdownOutput (Accept bytes) => [StreamBytes 1 bytes] | _ => [] end.

(** Only host completion may report process exit. *)
Lemma action_events_exit_free : forall action status,
  ~ In (ProcessExit status) (action_events action).
Proof. intros action status. destruct action; simpl; try tauto. destruct action; simpl; intuition discriminate. Qed.

(** A conservative partial segment stays in its selected output family
    and byte budget. Control actions, including callback entry, print
    nothing. This does not claim coverage of mixed native segments. *)
Definition partial_actions (action : shutdown_action) (actions : list stream_action) : Prop :=
  match action with
  | ShutdownOutput (Accept wanted) =>
      Forall (fun a => exists bytes, a = Accept bytes) actions /\
      exists tail, wanted = accepted actions ++ tail
  | ShutdownOutput (Deliver wanted) =>
      Forall (fun a => exists bytes, a = Deliver bytes) actions /\
      exists tail, wanted = resolved actions ++ tail
  | ShutdownOutput (Discard wanted) =>
      Forall (fun a => exists bytes, a = Discard bytes) actions /\
      exists tail, wanted = resolved actions ++ tail
  | ShutdownOutput OutputError => actions = [] \/ actions = [OutputError]
  | _ => actions = []
  end.

(** A partial output segment summarizes a single incomplete shutdown step
    rather than a resumable execution. Delivery and discard remain distinct in
    the action history, and only byte acceptance produces an output event. *)
Definition partial_output action q trace actions q' : Prop :=
  partial_actions action actions /\ stream_run q actions q' /\
  match action with
  | ShutdownOutput (Accept _) => prefix_observation trace actions
  | _ => trace = []
  end.

(** Partial actions cannot smuggle a process-exit event into a leaf. *)
Lemma partial_output_exit_free : forall action q trace actions q' status,
  partial_output action q trace actions q' -> ~ In (ProcessExit status) trace.
Proof.
  intros action q trace actions q' status (_ & _ & Hobs).
  destruct action; simpl in Hobs; try (subst trace; simpl; tauto).
  destruct action; simpl in Hobs; try (subst trace; simpl; tauto).
  destruct Hobs as [[-> _]| ->]; simpl; intuition discriminate.
Qed.

(** Even when a shutdown action fails to complete, its stream prefix still
    preserves FIFO byte accounting, stream well-formedness, and sticky
    errors. *)
Theorem partial_output_accounting : forall action q trace actions q',
  partial_output action q trace actions q' ->
  outstanding q ++ accepted actions = resolved actions ++ outstanding q' /\
  (stream_wf q -> stream_wf q') /\
  (stream_error q = true -> stream_error q' = true).
Proof.
  intros action q trace actions q' (_ & Hrun & _). split.
  - apply stream_accounting. exact Hrun.
  - split; [eapply stream_run_wf|eapply stream_error_sticky]; eauto.
Qed.

(** Trusted segment selection is independent of successful execution.
    ABI/arguments describe the selected segment boundary, not a proof
    of native callback calling conventions or retained-argument validity. *)
Record shutdown_boundary : Type := mkShutdownBoundary {
  shutdown_ready : R.state -> mem -> stdio_world -> shutdown_state -> Prop;
  action_contract : shutdown_state -> shutdown_action -> contract stdio_world;
  action_result : shutdown_state -> shutdown_action -> call_result;
  action_arguments : shutdown_state -> shutdown_action -> list arg;
  action_words : shutdown_state -> shutdown_action -> list word;
  action_post : shutdown_state -> shutdown_action -> R.state -> mem -> stdio_world ->
    list Z -> list event -> R.state -> mem -> stdio_world -> shutdown_state -> Prop
}.

(** Obligations can fail even when no effect or completion witness exists. *)
Definition shutdown_admissible (b : shutdown_boundary) (s : R.state) (m : mem)
    (w : stdio_world) (sh : shutdown_state) (action : shutdown_action) : Prop :=
  contract_abi (action_contract b sh action) (action_result b sh action) (action_arguments b sh action) /\
  contract_pre (action_contract b sh action) (action_words b sh action) m w.

(** An actual successful action segment must carry its memory effects,
    exact endpoints and compatible output; logical lifecycle edges alone
    neither grant memory authority nor prove readiness. *)
Inductive realizes (b : shutdown_boundary) :
    R.state -> mem -> stdio_world -> shutdown_state -> shutdown_action -> list event ->
    R.state -> mem -> stdio_world -> shutdown_state -> Prop :=
| realize_action : forall s m w sh action trace s' m' w' sh' born,
    shutdown_step sh action sh' -> shutdown_ready b s m w sh ->
    shutdown_admissible b s m w sh action ->
    M.E.prefix (action_contract b sh action) (action_words b sh action)
      s m w born trace s' m' w' ->
    action_post b sh action s m w born trace s' m' w' sh' ->
    trace = action_events action -> shutdown_ready b s' m' w' sh' ->
    realizes b s m w sh action trace s' m' w' sh'.

(** Every realized shutdown step preserves allocator readiness and existing
    objects through its memory-effect witness. *)
Theorem realizes_preserve : forall b s m w sh action trace s' m' w' sh',
  realizes b s m w sh action trace s' m' w' sh' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof.
  intros b s m w sh action trace s' m' w' sh' H Hr. destruct H.
  eapply M.E.prefix_preserve; eauto.
Qed.

(** Each realized segment obeys the same FIFO accounting as its selected
    lifecycle action, without equating delivery with error-discard. *)
Theorem realizes_accounting : forall b s m w sh action trace s' m' w' sh',
  realizes b s m w sh action trace s' m' w' sh' ->
  outstanding (shutdown_stdout sh) ++ accepted (shutdown_output action) =
  resolved (shutdown_output action) ++ outstanding (shutdown_stdout sh').
Proof.
  intros b s m w sh action trace s' m' w' sh' H. destruct H.
  destruct H; simpl; try apply app_nil_r.
  all: repeat rewrite app_nil_r.
  all: eapply stream_step_accounting; eassumption.
Qed.

(** The outer machine tracks whether execution is inside `c: main`, in
    shutdown, stopped at an unfinished call or resource leaf, or finished.
    Shutdown leaves keep their original snapshot for provenance rather than
    creating a resumable state. *)
Inductive state : Type :=
| Application (body : M.state program_world)
| ShuttingDown (runtime : R.state) (memory : mem) (stdio : stdio_world) (sh : shutdown_state)
| Unfinished (runtime : R.state) (memory : mem) (world : program_world)
| ShutdownUnfinished (runtime : R.state) (memory : mem) (stdio : stdio_world)
    (original : shutdown_state) (action : shutdown_action)
    (observed : list stream_action) (stdout : stream_state)
| ShutdownResource (why : reason) (runtime : R.state) (memory : mem) (stdio : stdio_world)
    (original : shutdown_state) (action : shutdown_action)
    (observed : list stream_action) (stdout : stream_state)
| Finished (runtime : R.state) (memory : mem) (stdio : stdio_world) (sh : shutdown_state).

(** Host completion is explicitly tied to the entire handoff snapshot. *)
Definition host_boundary : Type := R.state -> mem -> stdio_world -> shutdown_state -> Prop.

(** Each outer transition advances `c: main`, enters shutdown on return,
    records an unfinished or resource leaf, or finishes process exit once.
    Stopped states and unfinished prefixes never restart from their endpoints. *)
Inductive step (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
    (b : shutdown_boundary) (host : host_boundary) : state -> list event -> state -> Prop :=
| program_application : forall st trace st',
    M.step (registry rep requests) H.hi_genv st trace st' ->
    step rep requests b host (Application st) trace (Application st')
| program_main_return : forall c s w bits,
    main_return_site H.hi_genv c bits ->
    shutdown_ready b s (c_mem c) (program_stdio w)
      (mkShutdown Tls (main_status bits) (program_pending w) [] (program_stdout w)) ->
    step rep requests b host (Application (M.Running (c, s) w)) []
      (ShuttingDown s (c_mem c) (program_stdio w)
        (mkShutdown Tls (main_status bits) (program_pending w) [] (program_stdout w)))
| program_unfinished : forall c s w site born trace s' m' w',
    external_site H.hi_genv c site -> site = hi_site ->
    M.admissible (registry rep requests) H.hi_genv c w site ->
    map_option (arg_x H.hi_genv (fr_env (c_frame c))) (site_args site) = Some [WPtr hi_literal] ->
    M.E.prefix (program_puts rep requests) [WPtr hi_literal] s (c_mem c) w
      born trace s' m' w' ->
    step rep requests b host (Application (M.Running (c, s) w)) trace (Unfinished s' m' w')
| program_shutdown : forall s m w sh action trace s' m' w' sh',
    realizes b s m w sh action trace s' m' w' sh' ->
    step rep requests b host (ShuttingDown s m w sh) trace (ShuttingDown s' m' w' sh')
| program_shutdown_unfinished : forall s m w sh action full born trace s' m' w' actions q',
    shutdown_step sh action full -> shutdown_ready b s m w sh ->
    shutdown_admissible b s m w sh action ->
    M.E.prefix (action_contract b sh action) (action_words b sh action)
      s m w born trace s' m' w' ->
    partial_output action (shutdown_stdout sh) trace actions q' ->
    step rep requests b host (ShuttingDown s m w sh) trace
      (ShutdownUnfinished s' m' w' sh action actions q')
| program_shutdown_resource : forall s m w sh action full why trace s' m' w' actions q',
    shutdown_step sh action full -> shutdown_ready b s m w sh ->
    shutdown_admissible b s m w sh action ->
    M.E.invoke (action_contract b sh action) (action_result b sh action)
      (action_arguments b sh action) (action_words b sh action)
      s m w trace (CallResource why) s' m' w' ->
    partial_output action (shutdown_stdout sh) trace actions q' ->
    step rep requests b host (ShuttingDown s m w sh) trace
      (ShutdownResource why s' m' w' sh action actions q')
| program_complete : forall s m w kind status pending consumed q,
    host s m w (mkShutdown (HandedOff kind) status pending consumed q) ->
    step rep requests b host (ShuttingDown s m w (mkShutdown (HandedOff kind) status pending consumed q))
      [ProcessExit (process_status status)]
      (Finished s m w (mkShutdown (HandedOff kind) status pending consumed q)).

(** Finite outer runs chain zero or more steps together without assuming
    that every execution eventually terminates. *)
Inductive run rep requests b host : state -> list event -> state -> Prop :=
| program_refl : forall st, run rep requests b host st [] st
| program_next : forall st trace mid tail last,
    step rep requests b host st trace mid -> run rep requests b host mid tail last ->
    run rep requests b host st (trace ++ tail) last.

(** Two finite runs sharing an intermediate state compose into a single
    run over the concatenated event trace. *)
Lemma run_trans : forall rep requests b host st first mid last final,
  run rep requests b host st first mid -> run rep requests b host mid last final ->
  run rep requests b host st (first ++ last) final.
Proof.
  intros rep requests b host st first mid last final H. induction H; intros Htail; simpl; auto.
  rewrite <- app_assoc. eapply program_next; eauto.
Qed.

(** A consumed host completion cannot be reused by this outer machine. *)
Theorem finished_terminal : forall rep requests b host s m w sh trace st,
  ~ step rep requests b host (Finished s m w sh) trace st.
Proof. intros rep requests b host s m w sh trace st Hstep. inversion Hstep. Qed.

(** An unfinished observation does not assert that the call can resume. *)
Theorem unfinished_terminal : forall rep requests b host s m w trace st,
  ~ step rep requests b host (Unfinished s m w) trace st.
Proof. intros rep requests b host s m w trace st Hstep. inversion Hstep. Qed.

(** A partial shutdown snapshot is provenance, not a resumed lifecycle
    state. No host rule can complete either kind of terminal leaf. *)
Theorem shutdown_leaves_terminal : forall rep requests b host s m w sh action actions q trace st,
  ~ step rep requests b host (ShutdownUnfinished s m w sh action actions q) trace st /\
  forall why, ~ step rep requests b host (ShutdownResource why s m w sh action actions q) trace st.
Proof. intros. split; intros; intro Hstep; inversion Hstep. Qed.

(** Even when a shutdown action stops mid-stream without completing, its
    partial effects preserve allocator readiness and existing objects. *)
Theorem shutdown_unfinished_preserve : forall rep requests b host s m w sh trace s' m' w' action actions q,
  step rep requests b host (ShuttingDown s m w sh) trace
    (ShutdownUnfinished s' m' w' sh action actions q) -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof.
  intros rep requests b host s m w sh trace s' m' w' action actions q Hstep Hr.
  inversion Hstep; subst. eapply M.E.prefix_preserve; eauto.
Qed.

(** A resource endpoint carries the same preservation evidence as its
    actual invocation, not merely a resource label or logical edge. *)
Theorem shutdown_resource_preserve : forall rep requests b host s m w sh trace why s' m' w' action actions q,
  step rep requests b host (ShuttingDown s m w sh) trace
    (ShutdownResource why s' m' w' sh action actions q) -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof.
  intros rep requests b host s m w sh trace why s' m' w' action actions q Hstep Hr.
  inversion Hstep; subst. eapply M.E.invoke_preserve; eauto.
Qed.

(** A reached resource leaf carries a genuine requested refusal. The
    shared classification excludes it from capability panics. *)
Theorem shutdown_resource_nonfailure : forall rep requests b host st trace why s m w sh action actions q,
  step rep requests b host st trace (ShutdownResource why s m w sh action actions q) ->
  resource_reason why /\ ~ failure_ending (CoreEnd (Trap why)).
Proof.
  intros rep requests b host st trace why s m w sh action actions q Hstep.
  inversion Hstep; subst. match goal with Hcall : M.E.invoke _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    inversion Hcall; subst end.
  match goal with Hnormal : forall why, CallResource _ <> CallResource why |- _ =>
    exfalso; apply (Hnormal why); reflexivity end.
  assert (Hr : resource_reason why).
  { match goal with Hrefuse : M.E.resource_failure _ _ _ |- _ => inversion Hrefuse end;
      unfold resource_reason; auto. }
  split; [exact Hr|]. apply resource_not_failure. exact Hr.
Qed.

(** No continuation is added to the inner machine's stopped observations. *)
Theorem stopped_application_terminal : forall rep requests b host why ms w trace st,
  ~ step rep requests b host (Application (M.Stopped why ms w)) trace st.
Proof.
  intros rep requests b host why ms w trace st Hstep. inversion Hstep; subst.
  eapply M.stopped_no_step; eauto.
Qed.

(** Inner application runs lift unchanged, including their stopped outcomes. *)
Lemma application_run : forall rep requests b host st trace st',
  M.run (registry rep requests) H.hi_genv st trace st' ->
  run rep requests b host (Application st) trace (Application st').
Proof.
  intros rep requests b host st trace st' Hrun. induction Hrun.
  - constructor.
  - eapply program_next; [apply program_application; eassumption|exact IHHrun].
Qed.

(** A shutdown boundary satisfies [puts_shutdown_closed] when every
    returning `c: puts` call reached from the given entry state enters a
    ready shutdown state. *)
Definition puts_shutdown_closed rep requests (b : shutdown_boundary)
    (start : M.state program_world) : Prop :=
  forall first s m w fuel trace n s' m' w',
  M.run (registry rep requests) H.hi_genv start first
    (M.Running (hi_call m fuel, s) w) ->
  M.E.invoke (program_puts rep requests) (site_result hi_site) (site_args hi_site)
    [WPtr hi_literal] s m w trace (CallReturn [WInt n]) s' m' w' ->
  shutdown_ready b s' m' (program_stdio w')
    (mkShutdown Tls 0 (program_pending w') [] (program_stdout w')).

(** Under a closed shutdown boundary, any run reaching and returning from
    `c: puts` continues cleanly into shutdown with `c: main`'s zero return
    value. *)
Theorem returning_puts_shutdown : forall rep requests b host start first s m w fuel trace n s' m' w',
  puts_shutdown_closed rep requests b start ->
  M.run (registry rep requests) H.hi_genv start first
    (M.Running (hi_call m fuel, s) w) ->
  M.E.invoke (program_puts rep requests) (site_result hi_site) (site_args hi_site)
    [WPtr hi_literal] s m w trace (CallReturn [WInt n]) s' m' w' ->
  run rep requests b host (Application start) (first ++ trace)
    (ShuttingDown s' m' (program_stdio w')
      (mkShutdown Tls 0 (program_pending w') [] (program_stdout w'))).
Proof.
  intros rep requests b host start first s m w fuel trace n s' m' w' Hclosed Hreach Hcall.
  eapply run_trans; [apply application_run; exact Hreach|].
  rewrite <- (app_nil_r trace).
  eapply program_next with (trace := trace) (tail := [])
    (mid := Application (M.Running
      (resume_external (hi_call m fuel) hi_site
        [(TAtom "v1", WInt (n mod 2 ^ 32)); (TAtom "v0", WPtr hi_literal)] m', s') w')).
  - apply program_application. eapply M.step_return;
      [apply H.hi_external_site|reflexivity|reflexivity|exact Hcall|reflexivity].
  - eapply program_next with (trace := []) (tail := []).
    + apply program_main_return with (bits := 0).
      * apply H.hi_after_puts_return.
      * eapply Hclosed; eauto.
    + constructor.
Qed.

(** Logical readiness must independently justify the selected action's
    arguments and ABI even when that action has no successful realization. *)
Definition shutdown_ready_admits (b : shutdown_boundary) : Prop :=
  forall s m w sh action sh', shutdown_ready b s m w sh ->
    shutdown_step sh action sh' -> shutdown_admissible b s m w sh action.

(** Every outer machine state keeps allocator readiness, including
    unfinished calls and finished host snapshots. *)
Definition runtime_ready (st : state) : Prop :=
  match st with
  | Application body => M.state_ready program_world body
  | ShuttingDown s m _ _ | Unfinished s m _ | Finished s m _ _ => R.ready s m
  | ShutdownUnfinished s m _ _ _ _ _ | ShutdownResource _ s m _ _ _ _ _ => R.ready s m
  end.

(** No ready outer step can lose allocator readiness. *)
Theorem step_ready : forall rep requests b host st trace st',
  step rep requests b host st trace st' -> runtime_ready st -> runtime_ready st'.
Proof.
  intros rep requests b host st trace st' Hstep Hr. destruct Hstep; simpl in *; auto.
  - eapply M.step_ready; [|exact H|exact Hr]. reflexivity.
  - exact (proj1 (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ H3 Hr)).
  - exact (proj1 (realizes_preserve _ _ _ _ _ _ _ _ _ _ _ H Hr)).
  - exact (proj1 (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
  - exact (proj1 (M.E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
Qed.

(** Runtime readiness holds at every finite endpoint. *)
Theorem run_ready : forall rep requests b host st trace st',
  run rep requests b host st trace st' -> runtime_ready st -> runtime_ready st'.
Proof.
  intros rep requests b host st trace st' Hrun. induction Hrun; [auto|].
  intros Hr. apply IHHrun. eapply step_ready; eauto.
Qed.

(** Only application states need the body invariant for the exit-count theorem. *)
Definition application_safe rep (st : state) : Prop :=
  match st with Application body => body_inv rep body | _ => True end.

(** Outer phase changes cannot manufacture an unsafe application state. *)
Lemma step_application_safe : forall rep requests b host st trace st',
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
    rep m' w /\ stdio_ready m' w) ->
  step rep requests b host st trace st' -> application_safe rep st -> application_safe rep st'.
Proof.
  intros rep requests b host st trace st' Hstable Hstep Hsafe.
  destruct Hstep; simpl in *; auto. eapply body_step; eauto.
Qed.

(** Outer transitions cannot leave application execution and later
    re-enter it with facts that bypass the body invariant. *)
Lemma run_application_safe : forall rep requests b host st trace st',
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
    rep m' w /\ stdio_ready m' w) ->
  run rep requests b host st trace st' -> application_safe rep st -> application_safe rep st'.
Proof.
  intros rep requests b host st trace st' Hstable Hrun. induction Hrun; [auto|].
  intros Hsafe. apply IHHrun. eapply step_application_safe; eauto.
Qed.

(** Even when an outer run stops inside `c: main`, it cannot end in a
    capability panic or contract violation. *)
Theorem application_stopped_never_panics : forall rep requests b host st trace why ms w,
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
    rep m' w /\ stdio_ready m' w) ->
  application_safe rep st ->
  run rep requests b host st trace (Application (M.Stopped why ms w)) ->
  ~ failure_ending why.
Proof.
  intros rep requests b host st trace why ms w Hstable Hsafe Hrun.
  pose proof (run_application_safe _ _ _ _ _ _ _ Hstable Hrun Hsafe) as Hbody.
  destruct Hbody as [Hbody _]. apply hi_ending_not_failure. inversion Hbody. assumption.
Qed.

(** Counting process-exit events in an event trace keeps exit accounting
    separate from stdout acceptance summaries. *)
Fixpoint exit_count (trace : list event) : nat :=
  match trace with
  | [] => O
  | ProcessExit _ :: rest => S (exit_count rest)
  | _ :: rest => exit_count rest
  end.

(** Counts compose along actual runs, not by reusing cumulative puts summaries. *)
Lemma exit_count_app : forall first last,
  exit_count (first ++ last) = (exit_count first + exit_count last)%nat.
Proof. induction first as [|e rest IH]; intros last; [reflexivity|]. destruct e; simpl; rewrite IH; reflexivity. Qed.

(** Exit-free observations contribute no process-exit count. *)
Lemma exit_free_count : forall trace,
  (forall status, ~ In (ProcessExit status) trace) -> exit_count trace = O.
Proof.
  induction trace as [|e rest IH]; intros Hfree; [reflexivity|]. destruct e; simpl.
  - apply IH. intros status Hin. apply (Hfree status). right. exact Hin.
  - exfalso. apply (Hfree status). left. reflexivity.
Qed.

(** Any exit-bearing step is exactly a one-shot transition into Finished. *)
Lemma step_exit_shape : forall rep requests b host st trace st',
  step rep requests b host st trace st' -> application_safe rep st ->
  exit_count trace = O \/ exists s m w sh, st' = Finished s m w sh /\ exit_count trace = 1%nat.
Proof.
  intros rep requests b host st trace st' Hstep Hsafe. destruct Hstep; simpl in *.
  - left. apply exit_free_count. intros status. eapply application_exit_free; eauto.
  - left. reflexivity.
  - left. apply exit_free_count. intros status. eapply puts_stream_prefix_exit_free.
    exact (proj2 (proj2 (proj2 H3))).
  - left. destruct H. subst trace. apply exit_free_count. apply action_events_exit_free.
  - left. apply exit_free_count. intros status. eapply partial_output_exit_free; eauto.
  - left. apply exit_free_count. intros status. eapply partial_output_exit_free; eauto.
  - right. do 4 eexists. split; reflexivity.
Qed.

(** Finite runs from Finished are empty: the host witness cannot be replayed. *)
Lemma finished_run : forall rep requests b host s m w sh trace st,
  run rep requests b host (Finished s m w sh) trace st -> trace = [].
Proof.
  intros rep requests b host s m w sh trace st Hrun. inversion Hrun; subst; auto.
  exfalso. eapply finished_terminal; eauto.
Qed.

(** Every represented finite execution has at most one process-exit event.
    This is not a promise that a handoff or process exit is ever reached. *)
Theorem at_most_one_exit : forall rep requests b host st trace st',
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
    rep m' w /\ stdio_ready m' w) ->
  run rep requests b host st trace st' -> application_safe rep st ->
  (exit_count trace <= 1)%nat.
Proof.
  intros rep requests b host st trace st' Hstable Hrun. induction Hrun; [simpl; lia|].
  intros Hsafe. rewrite exit_count_app.
  destruct (step_exit_shape _ _ _ _ _ _ _ H Hsafe) as [Hz|(s & m & w & sh & -> & Hone)].
  - rewrite Hz. simpl. apply IHHrun. eapply step_application_safe; eauto.
  - rewrite Hone, (finished_run _ _ _ _ _ _ _ _ _ _ Hrun). simpl. lia.
Qed.

End Program.

(** ## Public conditional-composition checks

    To confirm that the outer machine's invariants and shutdown steps are
    consistent, we test them on concrete fixtures over the interpreter
    runtime. These checks use trivial memory segments rather than claiming
    that native libc implements them. *)
Module ProgramChecks.
Module P := Program InterpRuntime.

(** The fixture starts with an empty logical stdout buffer and no registered
    exit callbacks. *)
Definition initial_world : program_world := mkProgramWorld hello_world stdout_initial [].

(** Entering `c: main` in this fixture satisfies the whole-program
    invariant. *)
Lemma initial_body : P.body_inv fixture_rep
    (P.M.Running (hi_entry HiChecks.memory 10, InterpRuntime.start) initial_world).
Proof.
  split; [apply P.H.hi_body_entry; exact HiChecks.entry_pre|].
  split; [split; [exact stdout_initial_wf|constructor]|discriminate].
Qed.

(** Stronger preconditions remain independently admissible for every reached call. *)
Example all_rich_calls_admissible : forall trace c s w site,
  P.M.run (P.registry fixture_rep fixture_requests) P.H.hi_genv
    (P.M.Running (hi_entry HiChecks.memory 10, InterpRuntime.start) initial_world) trace
    (P.M.Running (c, s) w) -> external_site P.H.hi_genv c site ->
  P.M.admissible (P.registry fixture_rep fixture_requests) P.H.hi_genv c w site.
Proof.
  intros trace c s w site Hrun Hsite. eapply P.all_calls_admissible;
    [apply HiChecks.interpreter_stdio_stable|exact initial_body|exact Hrun|exact Hsite].
Qed.

(** Even a single distinct-token callback cannot appear at a reached
    call when this selected entry supplied no registrations. *)
Example changed_inventory_not_reached : forall trace m fuel s w entry,
  program_pending w = [entry] ->
  ~ P.M.run (P.registry fixture_rep fixture_requests) P.H.hi_genv
    (P.M.Running (hi_entry HiChecks.memory 10, InterpRuntime.start) initial_world) trace
    (P.M.Running (hi_call m fuel, s) w).
Proof.
  intros trace m fuel s w entry Hp Hrun.
  pose proof (P.body_run_inventory _ _ (HiChecks.interpreter_stdio_stable fixture_rep)
    _ _ _ Hrun initial_body) as Hsame.
  simpl in Hsame. rewrite Hp in Hsame. discriminate.
Qed.

(** Starting `c: main` with zero fuel stops immediately at entry without
    calling `c: puts` or entering shutdown. *)
Example zero_fuel_leaf : forall b host,
  P.step fixture_rep fixture_requests b host
    (P.Application (P.M.Running (hi_entry HiChecks.memory 0, InterpRuntime.start) initial_world)) []
    (P.Application (P.M.Stopped (CoreEnd OutOfFuel)
      (hi_entry HiChecks.memory 0, InterpRuntime.start) initial_world)).
Proof.
  intros b host. apply P.program_application. apply P.M.step_core_end; [|reflexivity].
  intros site Hsite. pose proof (external_site_stuck _ _ _ Hsite) as Hbad. discriminate.
Qed.

(** For any amount of fuel, every stopped application state reached from
    `c: main` avoids capability panics and contract violations. *)
Example all_outer_application_stops_safe : forall fuel b host trace why ms w,
  P.run fixture_rep fixture_requests b host
    (P.Application (P.M.Running (hi_entry HiChecks.memory fuel, InterpRuntime.start) initial_world))
    trace (P.Application (P.M.Stopped why ms w)) -> ~ failure_ending why.
Proof.
  intros fuel b host trace why ms w Hrun.
  eapply P.application_stopped_never_panics;
    [apply HiChecks.interpreter_stdio_stable| |exact Hrun].
  split; [apply P.H.hi_body_entry; exact HiChecks.entry_pre|].
  split; [split; [exact stdout_initial_wf|constructor]|discriminate].
Qed.

(** This dummy contract represents a shutdown segment with no memory writes
    so the fixture can step through shutdown without modelling native libc. *)
Definition segment : contract stdio_world :=
  mkContract stdio_world RVoid (fun _ _ => True) (fun _ _ _ => True)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ => True)
    (fun _ => False) (fun _ => False).

(** Fixture readiness does not assert the validity of any native callback. *)
Definition boundary : P.shutdown_boundary :=
  P.mkShutdownBoundary (fun _ _ _ _ => True) (fun _ _ => segment)
    (fun _ _ => CVoid) (fun _ _ => []) (fun _ _ => [])
    (fun _ _ _ _ _ _ _ _ _ _ _ => True).

(** The selected fixture segments are admissible independently of effects. *)
Example fixture_actions_admissible : P.shutdown_ready_admits boundary.
Proof. intros s m w sh action sh' Hr Hstep. split; exact I. Qed.

(** A lifecycle edge with no acceptance is realized with an actual empty
    effect path and the exact same runtime/memory/stdio snapshot. *)
Lemma silent_realization : forall s m w sh action sh',
  shutdown_step sh action sh' -> P.action_events action = [] ->
  P.realizes boundary s m w sh action [] s m w sh'.
Proof.
  intros s m w sh action sh' Hstep Htrace.
  eapply P.realize_action with (born := []);
    [exact Hstep|exact I|split; exact I| |exact I|symmetry; exact Htrace|exact I].
  split; [constructor|exact I].
Qed.

(** When no callbacks are registered, pending output bytes pass unchanged
    through TLS, handler, and cleanup steps to the soft handoff. *)
Lemma fixture_shutdown : forall s m w q host,
  P.run fixture_rep fixture_requests boundary host
    (P.ShuttingDown s m w (mkShutdown Tls 0 [] [] q)) []
    (P.ShuttingDown s m w (mkShutdown (HandedOff SoftExit) 0 [] [] q)).
Proof.
  intros s m w q host.
  eapply P.program_next with (trace := []) (tail := []);
    [apply P.program_shutdown with (action := EmptyTls); apply silent_realization; [constructor|reflexivity]|].
  eapply P.program_next with (trace := []) (tail := []);
    [apply P.program_shutdown with (action := StartCleanup); apply silent_realization; [constructor|reflexivity]|].
  eapply P.program_next with (trace := []) (tail := []);
    [apply P.program_shutdown with (action := Handoff SoftExit 0); apply silent_realization; [constructor|reflexivity]|].
  constructor.
Qed.

(** Returning main transfers the same stdout obligations, not a fresh stream. *)
Example main_to_exact_shutdown : forall s m q host,
  P.step fixture_rep fixture_requests boundary host
    (P.Application (P.M.Running (P.H.hi_return m 9 [], s) (mkProgramWorld hello_world q []))) []
    (P.ShuttingDown s m hello_world (mkShutdown Tls 0 [] [] q)).
Proof.
  intros s m q host. apply P.program_main_return with (bits := 0); [|exact I].
  exists (TAtom "start"), (Const 0). repeat split; reflexivity.
Qed.

(** Completing shutdown consumes the host witness once and leaves the outer
    machine in a terminal state that cannot step again. *)
Example complete_once : forall s m w q,
  P.step fixture_rep fixture_requests boundary (fun _ _ _ _ => True)
    (P.ShuttingDown s m w (mkShutdown (HandedOff SoftExit) 0 [] [] q)) [ProcessExit 0]
    (P.Finished s m w (mkShutdown (HandedOff SoftExit) 0 [] [] q)) /\
  (forall trace st, ~ P.step fixture_rep fixture_requests boundary (fun _ _ _ _ => True)
    (P.Finished s m w (mkShutdown (HandedOff SoftExit) 0 [] [] q)) trace st).
Proof. intros s m w q. split; [apply P.program_complete; exact I|apply P.finished_terminal]. Qed.

(** Accepting output in a callback cannot be realized by a silent trace. *)
Example hidden_callback_acceptance_rejected : forall s m w sh s' m' w' sh',
  ~ P.realizes boundary s m w sh (ShutdownOutput (Accept [65])) [] s' m' w' sh'.
Proof. intros s m w sh s' m' w' sh' H. inversion H. discriminate. Qed.

(** This fixture keeps accepted hello bytes outstanding; delivery is a
    separate obligation even if the host-completion predicate is granted. *)
Definition buffered : stream_state := mkStream ByteOriented (hello_bytes ++ [10]) false.

(** An inhabited returning puts with the exact logical endpoint used below. *)
Lemma buffered_puts :
  P.M.E.invoke (program_puts fixture_rep fixture_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start HiChecks.memory initial_world [StreamBytes 1 (hello_bytes ++ [10])]
    (CallReturn [WInt 6]) InterpRuntime.start HiChecks.memory
    (mkProgramWorld hello_world buffered []).
Proof.
  destruct HiChecks.entry_pre as [Hr [Hw Hl]].
  pose proof (P.H.hi_literal_checked HiChecks.memory Hl) as Hstr.
  assert (Hpost : puts_stream_post [WPtr hi_literal] HiChecks.memory stdout_initial
    [StreamBytes 1 (hello_bytes ++ [10])] (CallReturn [WInt 6]) buffered).
  { exists hi_literal, hello_bytes, ([Accept (hello_bytes ++ [10])]), 6.
    split; [reflexivity|]. split; [exact Hstr|]. split;
      [exact puts_buffered_acceptance|split; reflexivity]. }
  eapply P.M.E.invoke_normal with (born := []).
  - split; [right; exists (TAtom "v1"); reflexivity|]. exists (Tmp (TAtom "v0")). reflexivity.
  - split.
    + split; [exact Hr|]. split; [exact Hw|]. exists hi_literal, hello_bytes. auto.
    + split; [split; [exact stdout_initial_wf|constructor]|discriminate].
  - split; [constructor|]. split.
    + split; [exact Hr|]. split; [exact Hw|]. split.
      * apply stdio_delegates_refl; [reflexivity|exact (proj2 Hw)].
      * right. exists hi_literal, hello_bytes, (hello_bytes ++ [10]), ([] : list Z).
        split; [reflexivity|]. split; [exact Hstr|]. split; reflexivity.
    + split; [reflexivity|]. eapply P.C.program_post_prefix; exact Hpost.
  - split; [|exact Hpost].
    exact (protocol_puts_post hello_bytes stdout_initial [Accept (hello_bytes ++ [10])] 6 buffered
      HiChecks.memory hi_literal hello_world [] HiChecks.memory hello_world
      puts_buffered_acceptance Hstr Hw).
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt 6). split; reflexivity.
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** This example traces a complete finite run from `c: main` entry through
    `c: puts`, shutdown, and host completion without claiming native
    adequacy. *)
Example hi_entry_to_host :
  P.run fixture_rep fixture_requests boundary (fun _ _ _ _ => True)
    (P.Application (P.M.Running (hi_entry HiChecks.memory 10, InterpRuntime.start) initial_world))
    [StreamBytes 1 (hello_bytes ++ [10]); ProcessExit 0]
    (P.Finished InterpRuntime.start HiChecks.memory hello_world
      (mkShutdown (HandedOff SoftExit) 0 [] [] buffered)).
Proof.
  eapply P.run_trans with (first := [StreamBytes 1 (hello_bytes ++ [10])]) (last := [ProcessExit 0])
    (mid := P.ShuttingDown InterpRuntime.start HiChecks.memory hello_world
      (mkShutdown Tls 0 [] [] buffered)).
  - change (P.run fixture_rep fixture_requests boundary (fun _ _ _ _ => True)
      (P.Application (P.M.Running (hi_entry HiChecks.memory 10, InterpRuntime.start) initial_world))
      ([] ++ [StreamBytes 1 (hello_bytes ++ [10])])
      (P.ShuttingDown InterpRuntime.start HiChecks.memory hello_world
        (mkShutdown Tls 0 [] [] buffered))).
    eapply P.returning_puts_shutdown with (first := [])
      (w' := mkProgramWorld hello_world buffered []).
    + intros first s m w fuel trace n s' m' w' Hreach Hcall. exact I.
    + apply P.H.hi_reaches_call. lia.
    + exact buffered_puts.
  - eapply P.run_trans with (first := []) (last := [ProcessExit 0]).
    + apply fixture_shutdown.
    + eapply P.program_next with (trace := [ProcessExit 0]) (tail := []);
        [apply P.program_complete; exact I|constructor].
Qed.

(** Partial controls have no successful endpoint premise. This fixture
    deliberately makes Handlers unready and every action post false. *)
Definition prefix_boundary : P.shutdown_boundary :=
  P.mkShutdownBoundary (fun _ _ _ sh => shutdown_at sh = Tls) (fun _ _ => segment)
    (fun _ _ => CVoid) (fun _ _ => []) (fun _ _ => [])
    (fun _ _ _ _ _ _ _ _ _ _ _ => False).

(** An empty unfinished TLS segment exists although the complete target
    is unready and cannot satisfy the selected action's postcondition. *)
Example unfinished_without_completion : forall s m w q host,
  P.step fixture_rep fixture_requests prefix_boundary host
    (P.ShuttingDown s m w (mkShutdown Tls 0 [] [] q)) []
    (P.ShutdownUnfinished s m w (mkShutdown Tls 0 [] [] q) EmptyTls [] q) /\
  ~ P.shutdown_ready prefix_boundary s m w (mkShutdown Handlers 0 [] [] q).
Proof.
  intros s m w q host. split; [|discriminate].
  eapply P.program_shutdown_unfinished with (born := [])
    (full := mkShutdown Handlers 0 [] [] q).
  - constructor.
  - reflexivity.
  - split; exact I.
  - split; [constructor|exact I].
  - split; [reflexivity|]. split; [constructor|reflexivity].
Qed.

(** A partial delivery settles only the oldest selected bytes and
    preserves an existing error, without claiming the action completed. *)
Example partial_delivery_exact :
  P.partial_output (ShutdownOutput (Deliver [65; 66]))
    (mkStream ByteOriented [65; 66; 67] true) [] [Deliver [65]]
    (mkStream ByteOriented [66; 67] true).
Proof.
  split.
  - split; [constructor; [exists [65]; reflexivity|constructor]|exists [66]; reflexivity].
  - split; [|reflexivity]. eapply stream_next;
      [exact (stream_deliver [65] [66; 67] true ltac:(discriminate))|constructor].
Qed.

(** Control steps cannot emit output, and partial segments cannot accept
    extra bytes, deliver bytes out of order, or substitute discard for
    delivery. *)
Example incompatible_partial_output :
  (~ P.partial_output EmptyTls stdout_initial [StreamBytes 1 [65]] [Accept [65]]
    (mkStream ByteOriented [65] false)) /\
  (~ P.partial_output (ShutdownOutput (Accept [65; 66])) stdout_initial
    [StreamBytes 1 [65; 66; 67]] [Accept [65; 66; 67]]
    (mkStream ByteOriented [65; 66; 67] false)) /\
  (~ P.partial_output (ShutdownOutput (Deliver [66; 65]))
    (mkStream ByteOriented [65; 66] false) [] [Deliver [66]]
    (mkStream ByteOriented [65] false)) /\
  (~ P.partial_output (ShutdownOutput (Deliver [65; 66]))
    (mkStream ByteOriented [65; 66] false) [] [Discard [65]]
    (mkStream ByteOriented [66] true)) /\
  (~ P.partial_output (ShutdownOutput (Deliver [65]))
    (mkStream ByteOriented [65; 66] false) [] [Deliver [65; 66]]
    (mkStream ByteOriented [] false)) /\
  (~ P.partial_output (ShutdownOutput (Discard [65]))
    (mkStream ByteOriented [65; 66] false) [] [Discard [65; 66]]
    (mkStream ByteOriented [] true)) /\
  (~ P.partial_output (ShutdownOutput (Accept [65; 66])) stdout_initial
    [] [Accept [65]] (mkStream ByteOriented [65] false)).
Proof.
  repeat split.
  - intros [Hactions _]. discriminate.
  - intros [[_ [tail Hbad]] _]. discriminate.
  - intros [_ [Hrun _]]. inversion Hrun; subst.
    match goal with Hstep : stream_step _ _ _ |- _ => inversion Hstep; subst end. discriminate.
  - intros [[Hfamily _] _]. inversion Hfamily as [|a rest [bytes Hbad] Hrest]; subst.
    discriminate.
  - intros [[_ [tail Hbad]] _]. discriminate.
  - intros [[_ [tail Hbad]] _]. discriminate.
  - intros [_ [_ [[_ Hhidden]|Hhidden]]]; discriminate.
Qed.

(** A logical test contract can first allocate and accept a byte, then
    genuinely refuse an oversized request. It has no normal completion. *)
Definition resource_segment : contract stdio_world :=
  mkContract stdio_world RVoid (fun _ _ => True) (fun _ _ _ => True)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ align size => align = 16 /\ (size = 16 \/ size = 2 ^ 48))
    (fun _ _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ => False)
    resource_reason (fun _ => False).

(** This fixture grants source readiness but no successful action post. *)
Definition resource_boundary : P.shutdown_boundary :=
  P.mkShutdownBoundary (fun _ _ _ _ => True) (fun _ _ => resource_segment)
    (fun _ _ => CVoid) (fun _ _ => []) (fun _ _ => [])
    (fun _ _ _ _ _ _ _ _ _ _ _ => False).

(** The refusal leaf keeps nonempty memory and output progress, rather
    than rolling back to the selected action's original snapshot. *)
Example resource_after_progress : forall host entry,
  P.step fixture_rep fixture_requests resource_boundary host
    (P.ShuttingDown InterpRuntime.start HiChecks.memory hello_world
      (mkShutdown (InCallback entry) 0 [] [] stdout_initial))
    [StreamBytes 1 [65]]
    (P.ShutdownResource TooBig (InterpRuntime.start + 32)
      (allocated HiChecks.memory (heap_req 16 16) InterpRuntime.start) hello_world
      (mkShutdown (InCallback entry) 0 [] [] stdout_initial)
      (ShutdownOutput (Accept [65; 66])) [Accept [65]]
      (mkStream ByteOriented [65] false)).
Proof.
  intros host entry.
  eapply P.program_shutdown_resource with
    (full := mkShutdown (InCallback entry) 0 [] [] (mkStream ByteOriented [65; 66] false)).
  - apply shutdown_callback_output. apply stream_accept; [discriminate|repeat constructor; lia].
  - exact I.
  - split; exact I.
  - eapply P.M.E.invoke_resource with (born := [InterpRuntime.start]).
    + exact I.
    + exact I.
    + split; [|exact I]. eapply P.M.E.effects_alloc with
        (align := 16) (size := 16) (base := InterpRuntime.start)
        (s1 := InterpRuntime.start + 32).
      * split; [reflexivity|left; reflexivity].
      * unfold max_allocation_size. lia.
      * reflexivity.
      * constructor.
    + eapply P.M.E.failure_big with (align := 16) (size := 2 ^ 48).
      * split; [reflexivity|right; reflexivity].
      * unfold max_allocation_size. lia.
    + right. reflexivity.
  - split.
    + split; [constructor; [exists [65]; reflexivity|constructor]|exists [66]; reflexivity].
    + split.
      * eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|constructor].
      * right. reflexivity.
Qed.

(** Without a permitted request there is no resource endpoint, even
    when the logical action and its empty prefix are available. *)
Example unrequested_refusal_rejected : forall rep requests host s m w sh trace why s' m' w' action actions q,
  ~ P.step rep requests boundary host (P.ShuttingDown s m w sh) trace
    (P.ShutdownResource why s' m' w' sh action actions q).
Proof.
  intros rep requests host s m w sh trace why s' m' w' action actions q Hstep.
  inversion Hstep; subst.
  match goal with Hcall : P.M.E.invoke _ _ _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hcall; subst end.
  - match goal with Hnormal : forall why, CallResource _ <> CallResource why |- _ =>
      apply (Hnormal why); reflexivity end.
  - match goal with Hrefuse : P.M.E.resource_failure _ _ _ |- _ => inversion Hrefuse; subst end;
      contradiction.
Qed.

End ProgramChecks.

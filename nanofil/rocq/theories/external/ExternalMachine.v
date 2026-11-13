(** When a compiled C module calls a system-call wrapper or runtime helper
    that is not defined in the module itself, the core [[machine]] in
    [Machine](../soundness/Machine.v) halts on the unresolved symbol. This
    module extends that machine with a contract registry, such as the
    `zsys_*` table in `OsRegistry.v`, and labels each transition with the
    observable events from [ExternalCalls](ExternalCalls.v). Ordinary IR
    instructions, heap allocations, and garbage-collection
    [[poll|safepoints]] continue to run silently without emitting events.

    When an active [[frame]] that is not [[doomed]] reaches a direct call to
    an unresolved symbol ([external_site]), the machine looks up that
    symbol's [[external-call|contract]] in the registry and steps through
    [E.invoke]. A call that returns binds its result words in the caller's
    environment and resumes at the next instruction, whereas a call that
    exits the process or exhausts memory stops the machine in that final
    state. If a call site has no registered contract, passes ill-typed
    arguments, violates the contract's precondition, or receives an
    incompatible return value, the machine halts with a [ContractViolation]
    so that specification failures are never confused with Fil-C capability
    [[trap|traps]].

    Because an external call can overwrite memory, allocate new heap objects,
    and advance the [[runtime]] state before returning to compiled C code,
    external returns must preserve [[campaign|Campaign]] 3's [[validator]]
    invariants. The final section proves that returning from a valid external
    call keeps the runtime [[ready]], preserves object [[identity]], and
    maintains both the [[evidence]] invariant and the
    [[single-definition|single-definition]] invariant over every finite
    [run]. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine
  Validate Identity ExternalCalls Walk Steps Invariant Persistence Single.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Dispatch and the return channel

    Before coupling external calls to a runtime, we define when a frame is
    poised at an external call instruction and how the call's returned words
    flow back into the caller's environment. This section also defines the
    stopping conditions of the labelled machine and proves in
    [external_site_stuck] that ordinary IR execution never competes with
    external contract dispatch. *)

(** The record [call_site] packages the syntax of a direct call instruction
    together with its surrounding [[block]] label and the instructions and
    jump that follow the call when it returns. *)
Record call_site : Type := mkCallSite {
  site_label : name;
  site_result : call_result;
  site_name : name;
  site_args : list arg;
  site_rest : list inst;
  site_jump : jump
}.

(** A configuration c sits at an [external_site] when its active [[frame]] is
    not [[doomed]], its next instruction calls a global symbol directly, and
    that symbol is neither a function in the module, a global data object,
    nor a runtime deallocation (`c: free` or `c: zgc_free`). Requiring an
    undoomed frame prevents a doomed [[check_ahead]] path from escaping
    through an external contract, while excluding `c: free` keeps
    deallocation under the core runtime rules. *)
Definition external_site (ge : genv) (c : config) (site : call_site) : Prop :=
  let fr := c_frame c in
  fr_doomed fr = None /\
  fr_at fr = Exec (site_label site)
    (Call (site_result site) (Global (site_name site)) (site_args site) :: site_rest site) (site_jump site) /\
  find_fn ge (site_name site) = None /\ lookup (site_name site) (ge_globals ge) = None /\
  is_free_name (site_name site) = false.

(** When an external contract finishes, [external_outcome] packages its
    returned word list into a core [[outcome]] according to the contract's
    declared return type: [RetVoid] for a void return, [Ret] for a single
    scalar word, and [Rets] for a multi-word tuple. If a void or scalar
    contract produces the wrong number of words, [external_outcome] returns
    `None` so the machine can report a return-channel mismatch. *)
Definition external_outcome (ty : ret_type) (xs : list word) : option outcome :=
  match ty, xs with
  | RVoid, [] => Some RetVoid
  | RClass _, [x] => Some (Ret x)
  | RTuple _, _ => Some (Rets xs)
  | _, _ => None
  end.

(** Any word list that satisfies a contract's declared [return_shape]
    converts to a valid [[outcome]] under [external_outcome]. *)
Lemma external_outcome_total : forall ty xs,
  return_shape ty xs -> exists o, external_outcome ty xs = Some o.
Proof.
  intros ty xs H. destruct ty; simpl in H.
  - destruct H as (x & -> & _). eexists. reflexivity.
  - subst xs. eexists. reflexivity.
  - eexists. reflexivity.
Qed.

(** When an external call returns a list of words, [external_env] converts
    those words with [external_outcome] and binds them to the destination
    [[temporary]] names at the call site via [returned_env]. It returns
    `None` when the returned words do not match the call site's result
    binding. *)
Definition external_env {world : Type} (spec : contract world) (site : call_site)
    (xs : list word) (e : env) : option env :=
  let* o := external_outcome (contract_returns spec) xs in
  returned_env (site_result site) o e.

(** After an external call returns an updated environment e and memory m,
    [resume_external] advances the active frame past the call instruction
    while keeping the caller's function, stack locals, waiting callers, and
    remaining [[fuel]]. *)
Definition resume_external (c : config) (site : call_site) (e : env) (m : Memory.mem) : config :=
  let fr := c_frame c in
  mkConfig (mkFrame (fr_fn fr) e (fr_locals fr) None
    (Exec (site_label site) (site_rest site) (site_jump site))) (c_callers c) m (c_fuel c).

(** A [violation] classifies how a call site can fail its contract: the
    callee has no registered contract, an argument fails to evaluate, the
    call site violates the contract's ABI or precondition, or the returned
    words do not fit the caller's destination binding. These failures mark a
    broken specification rather than a runtime capability [[trap]]. *)
Inductive violation : Type := MissingContract | BadArguments | BadABI | BadPrecondition | BadReturn.

(** An [ending] records why the labelled machine stopped: a normal or
    trapping core [[outcome]], a stuck core instruction with its diagnostic
    message, a process exit triggered by an external call, or a
    [ContractViolation] at an external call site. *)
Inductive ending : Type :=
| CoreEnd (o : outcome)
| CoreStuck (diagnostic : string)
| ExternalExit (status : Z)
| ContractViolation (symbol : name) (why : violation).

(** When a configuration is poised at an [external_site], the core
    instruction step [Semantics.step] returns `Stuck "instruction"`, which
    ensures in [external_core_safepoint] that no core instruction or
    allocation step can fire in place of contract dispatch. *)
Lemma external_site_stuck : forall ge c site,
  external_site ge c site -> Semantics.step ge c = Stuck "instruction".
Proof.
  intros ge c site (Hd & Ha & Hfn & Hdata & Hfree).
  unfold Semantics.step. rewrite Ha, Hd. unfold inst_step.
  destruct (map_option (arg_x ge (fr_env (c_frame c))) (site_args site)); [|reflexivity].
  rewrite Hfn. unfold external_call. rewrite Hdata, Hfree. reflexivity.
Qed.

(** ## The labelled machine

    The functor [ExternalMachine] pairs the core machine over a [[runtime]] R
    with a logical world shared by all registered external contracts. This
    section defines when a call site is [admissible] or [rejected], gives the
    labelled [step] and multi-step [run] relations, and proves in
    [step_ready] and [step_persists] that every step preserves runtime
    readiness and existing object identities. *)

(** For any [[runtime]] implementation R, the module [ExternalMachine]
    combines the external-call semantics of [ExternalCalls] with the
    run-level validator invariants over R. *)
Module ExternalMachine (R : Runtime).

Module E := ExternalCalls R.
Module P := Persistence R.
Module S := Single R.
Import P.I P.I.RM.

(** Two modules that instantiate the core machine over the same runtime
    define the same step relation with separate constructors. This helper
    converts a core machine step from one module instance to the other. *)
Lemma single_core_step : forall ge ms ms', mstep ge ms ms' -> S.ID.RM.mstep ge ms ms'.
Proof. intros ge ms ms' H. destruct H; [eapply S.ID.RM.mstep_next | eapply S.ID.RM.mstep_alloc | eapply S.ID.RM.mstep_safepoint]; eauto. Qed.

(** By [external_site_stuck], the only core machine step that can fire at an
    [external_site] is a garbage-collection [[poll|safepoint]], which updates
    memory in place and leaves the configuration at the same call site. *)
Lemma external_core_safepoint : forall ge c s c' s' site,
  external_site ge c site -> mstep ge (c, s) (c', s') ->
  safepoint_due ge c = true /\ exists m', c' = with_mem c m' /\ R.safepoint s (c_mem c) s' m'.
Proof.
  intros ge c s c' s' site Hsite H.
  pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
  inversion H; subst; try congruence. eauto.
Qed.

(** Within this section, the type variable world represents the external
    library or operating-system state shared by all contracts in a registry. *)
Section World.
Variable world : Type.

(** A labelled machine [state] pairs the core machine state and the external
    world, and is either [Running] or [Stopped] with a terminal [ending]. *)
Inductive state : Type :=
| Running (machine : mstate) (w : world)
| Stopped (why : ending) (machine : mstate) (w : world).

(** The projection [machine_of] extracts the underlying core machine state
    from either a running or a stopped labelled state. *)
Definition machine_of (st : state) : mstate :=
  match st with Running ms _ | Stopped _ ms _ => ms end.

(** A labelled state satisfies [state_ready] when the [[runtime]] is [[ready]]
    in its underlying core machine state. *)
Definition state_ready (st : state) : Prop := ready_state (machine_of st).

(** An external call site is [admissible] when the registry provides a
    contract for the callee, the call arguments evaluate to words, and both
    the contract's ABI check and its precondition hold in the current memory
    and world. Admissibility is checked directly at the call site before any
    invocation runs, so failing a precondition is a contract violation rather
    than a runtime trap. *)
Definition admissible (registry : name -> option (contract world)) (ge : genv)
    (c : config) (w : world) (site : call_site) : Prop :=
  exists spec xs,
    registry (site_name site) = Some spec /\
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs /\
    contract_abi spec (site_result site) (site_args site) /\ contract_pre spec xs (c_mem c) w.

(** The inductive predicate [rejected] classifies why a call site fails
    [admissible], checking in order for a missing contract, unevaluable
    arguments, a broken ABI premise, or a violated precondition. Return-type
    mismatches after a call finishes are caught separately by
    [step_bad_return]. *)
Inductive rejected (registry : name -> option (contract world)) (ge : genv)
    (c : config) (w : world) (site : call_site) : violation -> Prop :=
| reject_missing : registry (site_name site) = None -> rejected registry ge c w site MissingContract
| reject_arguments : forall spec,
    registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = None ->
    rejected registry ge c w site BadArguments
| reject_abi : forall spec xs,
    registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
    ~ contract_abi spec (site_result site) (site_args site) -> rejected registry ge c w site BadABI
| reject_pre : forall spec xs,
    registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
    contract_abi spec (site_result site) (site_args site) ->
    ~ contract_pre spec xs (c_mem c) w -> rejected registry ge c w site BadPrecondition.

(** The relation [step] defines one transition of the labelled machine under
    a contract registry and records the observable events emitted during the
    step. Ordinary core machine steps, normal returns, core traps, stuck
    instructions, and allocation refusals run when no external call is due
    and emit an empty event trace.

    At an external call site, the machine invokes the callee's registered
    contract and records the events that the call emits. A returning call
    resumes at the next instruction in the updated memory and world, whereas
    a process exit, an allocation failure, or a broken contract stops the
    machine. *)
Inductive step (registry : name -> option (contract world)) (ge : genv)
    : state -> list event -> state -> Prop :=
| step_core : forall ms ms' w,
    mstep ge ms ms' -> step registry ge (Running ms w) [] (Running ms' w)
(** When a core execution finishes without an external call, the stopped
    state keeps the final configuration and runtime snapshot alongside the
    terminal outcome. *)
| step_core_end : forall c s w o,
    (forall site, ~ external_site ge c site) ->
    Semantics.step ge c = Done o ->
    step registry ge (Running (c, s) w) [] (Stopped (CoreEnd o) (c, s) w)
| step_core_stuck : forall c s w why,
    (forall site, ~ external_site ge c site) ->
    Semantics.step ge c = Stuck why ->
    step registry ge (Running (c, s) w) [] (Stopped (CoreStuck why) (c, s) w)
| step_core_refusal : forall c s w q k,
    (forall site, ~ external_site ge c site) ->
    Semantics.step ge c = Fresh q k -> 0 <= req_extent q -> R.alloc s q = None ->
    step registry ge (Running (c, s) w) [] (Stopped (CoreEnd (Trap OutOfMemory)) (c, s) w)
| step_return : forall c s w site spec xs trace values s' m' w' e,
    external_site ge c site -> registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
    E.invoke spec (site_result site) (site_args site) xs s (c_mem c) w
      trace (CallReturn values) s' m' w' ->
    external_env spec site values (fr_env (c_frame c)) = Some e ->
    step registry ge (Running (c, s) w) trace (Running (resume_external c site e m', s') w')
| step_exit : forall c s w site spec xs trace status s' m' w',
    external_site ge c site -> registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
    E.invoke spec (site_result site) (site_args site) xs s (c_mem c) w
      trace (CallExit status) s' m' w' ->
    step registry ge (Running (c, s) w) trace (Stopped (ExternalExit status) (with_mem c m', s') w')
| step_resource : forall c s w site spec xs trace why s' m' w',
    external_site ge c site -> registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
    E.invoke spec (site_result site) (site_args site) xs s (c_mem c) w
      trace (CallResource why) s' m' w' ->
    step registry ge (Running (c, s) w) trace (Stopped (CoreEnd (Trap why)) (with_mem c m', s') w')
| step_rejected : forall c s w site why,
    external_site ge c site -> rejected registry ge c w site why ->
    step registry ge (Running (c, s) w) []
      (Stopped (ContractViolation (site_name site) why) (c, s) w)
| step_bad_return : forall c s w site spec xs trace values s' m' w',
    external_site ge c site -> registry (site_name site) = Some spec ->
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
    E.invoke spec (site_result site) (site_args site) xs s (c_mem c) w
      trace (CallReturn values) s' m' w' ->
    external_env spec site values (fr_env (c_frame c)) = None ->
    step registry ge (Running (c, s) w) trace
      (Stopped (ContractViolation (site_name site) BadReturn) (with_mem c m', s') w').

(** The multi-step relation [run] chains a finite sequence of labelled [step]
    transitions and concatenates their event traces in order. Each completed
    external call appears as a single atomic step in this trace. *)
Inductive run (registry : name -> option (contract world)) (ge : genv)
    : state -> list event -> state -> Prop :=
| run_refl : forall st, run registry ge st [] st
| run_cons : forall st trace mid tail last,
    step registry ge st trace mid -> run registry ge mid tail last ->
    run registry ge st (trace ++ tail) last.

(** A starting state satisfies [no_violation] when no running state reachable
    from it via [run] can take a [step] to a [ContractViolation]. Every
    reachable state must avoid contract violations on every possible step,
    even if another branch such as a runtime safepoint could also fire at the
    same state. *)
Definition no_violation (registry : name -> option (contract world)) (ge : genv) (start : state) : Prop :=
  forall prefix ms w trace symbol why ms' w',
    run registry ge start prefix (Running ms w) ->
    ~ step registry ge (Running ms w) trace (Stopped (ContractViolation symbol why) ms' w').

(** If a starting state satisfies [no_violation], then no [external_site]
    reached during a [run] from that state can be [rejected]. *)
Lemma no_violation_rejected : forall registry ge start prefix c s w site why,
  no_violation registry ge start -> run registry ge start prefix (Running (c, s) w) ->
  external_site ge c site -> ~ rejected registry ge c w site why.
Proof.
  intros registry ge start prefix c s w site why Hsafe Hrun Hsite Hbad.
  exact (Hsafe _ _ _ _ _ _ _ _ Hrun (step_rejected _ _ _ _ _ _ _ Hsite Hbad)).
Qed.

(** Once the labelled machine reaches a [Stopped] state, it cannot take any
    further [step]. *)
Lemma stopped_no_step : forall registry ge why ms w trace st,
  ~ step registry ge (Stopped why ms w) trace st.
Proof. intros registry ge why ms w trace st H. inversion H. Qed.

(** Any labelled [step] from a configuration that is not at an
    [external_site] is a core transition and emits an empty event trace. *)
Lemma non_external_silent : forall registry ge c s w trace st,
  (forall site, ~ external_site ge c site) -> step registry ge (Running (c, s) w) trace st -> trace = [].
Proof. intros registry ge c s w trace st Hnone H. inversion H; subst; try reflexivity; exfalso; eapply Hnone; eauto. Qed.

(** A labelled [step] can stop with an [[unchecked]] outcome only when the
    underlying core semantics [Semantics.step] produces that outcome directly,
    because external contract invocations never manufacture unchecked
    outcomes. *)
Lemma unchecked_is_core : forall registry ge c s w trace ms' w' why,
  step registry ge (Running (c, s) w) trace (Stopped (CoreEnd (Unchecked why)) ms' w') ->
  Semantics.step ge c = Done (Unchecked why).
Proof. intros registry ge c s w trace ms' w' why H. inversion H; subst; assumption. Qed.

(** When an external call site satisfies [admissible], it cannot be
    [rejected] for any contract violation. *)
Lemma admissible_not_rejected : forall registry ge c w site why,
  admissible registry ge c w site -> ~ rejected registry ge c w site why.
Proof.
  intros registry ge c w site why (spec & xs & Hr & Hx & Ha & Hp) H.
  destruct H; try congruence.
Qed.

(** Every labelled [step] preserves [state_ready], because core machine steps
    and external contract invocations via [E.invoke_preserve] both keep the
    [[runtime]] [[ready]]. *)
Theorem step_ready : forall registry ge st trace st',
  ge_free ge = R.free -> step registry ge st trace st' -> state_ready st -> state_ready st'.
Proof.
  intros registry ge st trace st' Hfree H. destruct H; simpl; intros Hr;
    try exact Hr; try solve [eapply mstep_ready; eauto].
  all: exact (proj1 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
Qed.

(** Starting from a [state_ready] state, every object registered in memory
    before a labelled [step] [[identity|persists]] in memory after the step. *)
Theorem step_persists : forall registry ge st trace st',
  ge_free ge = R.free -> step registry ge st trace st' -> state_ready st ->
  persists (c_mem (fst (machine_of st))) (c_mem (fst (machine_of st'))).
Proof.
  intros registry ge st trace st' Hfree H. destruct H; simpl; intros Hr;
    try apply persists_refl.
  1: exact (S.ID.mstep_persists _ _ _ Hfree Hr (single_core_step _ _ _ H)).
  all: exact (proj2 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
Qed.

(** ## Continuations and Campaign 3

    When an external call returns to compiled IR code, the caller continues
    executing instructions that rely on Campaign 3's [[validator]] invariants.
    This section proves that resuming from an external call preserves both the
    [[evidence]] invariant [inv] and the [[single-definition|single-definition]]
    invariant [sinv], culminating in [run_preserve] for arbitrary multi-step
    runs. *)

(** A compiler cannot assume that capabilities checked before an external
    call remain valid after the call returns, so the validator clears all
    live capability facts at every call instruction. Because the caller frame
    carries no live facts across the call, resuming after the call returns
    preserves the [[evidence]] invariant [inv] in the new memory state. *)
Lemma resume_inv : forall ge md c s site e m' s',
  external_site ge c site -> inv ge md (c, s) -> inv ge md (resume_external c site e m', s').
Proof.
  intros ge md c s site e m' s' (Hd & Ha & _) [Hfr Hcs]. split; [|exact Hcs].
  exact (parked_resume ge md m'
    (mkFrame (fr_fn (c_frame c)) (fr_env (c_frame c)) (fr_locals (c_frame c)) None
      (Exec (site_label site) (site_rest site) (site_jump site))) e
    (call_parked _ _ _ _ _ _ _ _ _ _ Hfr Hd Ha)).
Qed.

(** Binding the return values of an external call with [external_env] updates
    only the destination [[temporary]] names listed in [result_names] and
    leaves every other temporary in the caller's environment unchanged. *)
Lemma external_env_other : forall (spec : contract world) site values old e a,
  external_env spec site values old = Some e -> ~ In a (result_names (site_result site)) ->
  lookup a e = lookup a old.
Proof.
  intros spec site values old e a H Ha. unfold external_env in H.
  destruct (external_outcome _ _) as [o|]; [|discriminate H].
  exact (returned_env_other _ _ _ _ _ H Ha).
Qed.

(** When an external call returns, it binds only the result temporaries of
    the call instruction and leaves every earlier temporary in the caller's
    frame untouched. As long as all objects that existed before the call
    [[identity|persist]] in the post-call memory, resuming after the call
    preserves the [[single-definition|single-definition]] invariant [sinv]. *)
Lemma resume_sinv : forall ge md c site (spec : contract world) values e m',
  checked_module md -> external_site ge c site ->
  external_env spec site values (fr_env (c_frame c)) = Some e ->
  persists (c_mem c) m' -> sinv ge md c -> sinv ge md (resume_external c site e m').
Proof.
  intros ge md c site spec values e m' Hmd (Hd & Ha & _) He Hp [[Hsh Hsc] Hcs].
  destruct Hsc as [Hdoom | Hsc]; [contradiction|].
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh.
  destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hsk & Hj).
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hsk)) as (Hki & Hrest & Hlen).
  assert (Hpt0 : point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (site_label site, Z.of_nat k))
    by (rewrite Ha, Hsk; exact (point_site_exec _ _ _ _ _ Hb Hk)).
  assert (Hpt1 : point_site (fr_fn (c_frame c)) (Exec (site_label site) (site_rest site) (site_jump site)) =
                  Some (site_label site, Z.of_nat (S k)))
    by (rewrite <- Hrest; exact (point_site_exec _ _ _ _ _ Hb Hlen)).
  split; [|exact (callers_mem _ _ _ _ _ Hcs Hp)]. split.
  - unfold shaped. cbv zeta. simpl. split; [exact Hin|]. split; [exact Hr|].
    exists b, (S k). split; [exact Hb|]. split; [exact Hlen|]. split; [symmetry; exact Hrest|exact Hj].
  - right. refine (scope_step _ _ (c_frame c) (c_frame (resume_external c site e m')) _ _ _ _ _
      (Call (site_result site) (Global (site_name site)) (site_args site))
      Hmd Hin eq_refl Hr Hb Hki Hpt0 Hpt1 _ Hp _ Hsc).
    + rewrite call_defs. exact (fun a Hn => external_env_other _ _ _ _ _ _ He Hn).
    + intros n Hrp. discriminate Hrp.
Qed.

(** A running machine must maintain the compiler's live capability facts in
    every active stack frame, whereas a stopped machine executes no further
    instructions. The predicate [evidence_inv] therefore requires [inv] on
    running states and holds trivially on stopped states. *)
Definition evidence_inv (ge : genv) (md : module) (st : state) : Prop :=
  match st with Running ms _ => inv ge md ms | Stopped _ _ _ => True end.

(** A running machine must also keep every single-definition temporary equal
    to the value computed at its definition site, whereas a stopped machine
    needs no frame invariant. The predicate [single_inv] therefore requires
    [sinv] on running states and holds trivially on stopped states. *)
Definition single_inv (ge : genv) (md : module) (st : state) : Prop :=
  match st with Running ms _ => sinv ge md (fst ms) | Stopped _ _ _ => True end.

(** Every step of the labelled machine from a ready state preserves the
    [[evidence]] invariant [evidence_inv], whether the machine runs a silent
    core instruction or returns from an external call. *)
Theorem step_inv : forall registry ge md st trace st',
  ge_module ge = md -> checked_module md ->
  step registry ge st trace st' -> state_ready st -> evidence_inv ge md st -> evidence_inv ge md st'.
Proof.
  intros registry ge md st trace st' Hge Hmd H. destruct H; simpl; intros Hr Hi; try exact I.
  - eapply P.mstep_inv; eauto.
  - eapply resume_inv; eauto.
Qed.

(** Every step of the labelled machine from a ready state preserves the
    [[single-definition|single-definition]] invariant [single_inv] across
    both core instructions and external calls. *)
Theorem step_sinv : forall registry ge md st trace st',
  ge_module ge = md -> checked_module md -> ge_free ge = R.free ->
  step registry ge st trace st' -> state_ready st -> single_inv ge md st -> single_inv ge md st'.
Proof.
  intros registry ge md st trace st' Hge Hmd Hfree H. destruct H; simpl; intros Hr Hi; try exact I.
  - exact (S.mstep_sinv _ _ _ _ Hge Hmd Hfree Hr (single_core_step _ _ _ H) Hi).
  - eapply resume_sinv; eauto. exact (proj2 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
Qed.

(** Over any finite [run] of a validated module from a ready starting state,
    the runtime remains [[ready]], every object allocated along the way keeps
    its [[identity]], and both the evidence invariant and the
    single-definition invariant continue to hold. *)
Theorem run_preserve : forall registry ge md st trace st',
  ge_module ge = md -> checked_module md -> ge_free ge = R.free ->
  run registry ge st trace st' -> state_ready st -> evidence_inv ge md st -> single_inv ge md st ->
  state_ready st' /\ persists (c_mem (fst (machine_of st))) (c_mem (fst (machine_of st'))) /\
  evidence_inv ge md st' /\ single_inv ge md st'.
Proof.
  intros registry ge md st trace st' Hge Hmd Hfree H.
  induction H; intros Hr Hi Hs.
  - split; [exact Hr|]. split; [apply persists_refl|auto].
  - pose proof (step_ready _ _ _ _ _ Hfree H Hr) as Hr1.
    pose proof (step_inv _ _ _ _ _ _ Hge Hmd H Hr Hi) as Hi1.
    pose proof (step_sinv _ _ _ _ _ _ Hge Hmd Hfree H Hr Hs) as Hs1.
    destruct (IHrun Hr1 Hi1 Hs1) as (Hr' & Hp & Hi' & Hs'). split; [exact Hr'|].
    split; [eapply persists_trans; [eapply step_persists; eauto | exact Hp] | auto].
Qed.

End World.

Arguments Running {world}.
Arguments Stopped {world}.
Arguments admissible {world}.
Arguments step {world}.
Arguments run {world}.
End ExternalMachine.

(** Client modules such as [Startup](Startup.v) parameterize over
    [ExternalMachineSig] so that they share the caller's exact
    [ExternalMachine] instance rather than generating a duplicate copy of its
    inductive [step] and [run] relations. *)
Module Type ExternalMachineSig (R : Runtime).
Include ExternalMachine R.
End ExternalMachineSig.

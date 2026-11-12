(** [[campaign|Campaign]] 4's guarded, labelled extension of Machine.v
    ([milestone 2](../../../docs/formal.md#campaign-4-milestone-2-guarded-machine-integration)):
    a [[machine]] whose steps carry the [[external call]] events of
    ExternalCalls.v.

    Existing machine steps are silent and unchanged. A direct call of
    an unresolved, non-data name other than free can invoke a registered
    contract, only in a frame that is not [[doomed]]. A completed call
    carries its observations and exact runtime/memory/world snapshot.

    Contract violations are specification failures, NOT native traps.
    Coverage and caller admissibility are checked independently of an
    invocation's existence. Admissible contracts may still have no
    completed invocation: native coverage, blocking/divergence and
    independent external prefixes remain obligations, not safety claims.
    This extension is relational; the extracted driver is unchanged. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine
  Validate Identity ExternalCalls Walk Steps Invariant Persistence Single.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Dispatch and the return channel *)

(** A direct call about to run: its [[block]] label, the call's result
    (where the returned words go), the called global's name, the
    argument syntax, and the instructions and jump that follow it in
    the block. *)
Record call_site : Type := mkCallSite {
  site_label : name;
  site_result : call_result;
  site_name : name;
  site_args : list arg;
  site_rest : list inst;
  site_jump : jump
}.

(** In the global environment ge, the configuration c is at the
    external call site: its [[frame]] is not [[doomed]], its next
    instruction is a direct call of site's global name, and that name is
    neither a function of the module (defined or outside the
    [[core subset]], [find_fn]), nor global data, nor a free the model
    runs ([is_free_name]: free or zgc_free). This preserves core
    dispatch precedence: both frees remain the runtime's operation, and
    no contract can be registered over either. In particular a doomed call cannot use this rule to
    escape [Ahead]. *)
Definition external_site (ge : genv) (c : config) (site : call_site) : Prop :=
  let fr := c_frame c in
  fr_doomed fr = None /\
  fr_at fr = Exec (site_label site)
    (Call (site_result site) (Global (site_name site)) (site_args site) :: site_rest site) (site_jump site) /\
  find_fn ge (site_name site) = None /\ lookup (site_name site) (ge_globals ge) = None /\
  is_free_name (site_name site) = false.

(** The [[outcome]] a call's returned words xs make under the declared
    return type ty: [RetVoid] for void, [Ret] for a scalar, [Rets] for
    any tuple; none when void or scalar gets the wrong number of words.
    The declared shape, not list length, selects the return channel. *)
Definition external_outcome (ty : ret_type) (xs : list word) : option outcome :=
  match ty, xs with
  | RVoid, [] => Some RetVoid
  | RClass _, [x] => Some (Ret x)
  | RTuple _, _ => Some (Rets xs)
  | _, _ => None
  end.

(** Words of the declared [return_shape] always make an outcome. *)
Lemma external_outcome_total : forall ty xs,
  return_shape ty xs -> exists o, external_outcome ty xs = Some o.
Proof.
  intros ty xs H. destruct ty; simpl in H.
  - destruct H as (x & -> & _). eexists. reflexivity.
  - subst xs. eexists. reflexivity.
  - eexists. reflexivity.
Qed.

(** The caller's environment e with the words xs a call of the contract
    spec returned bound as the site's result reads them
    ([returned_env], as `call_outcome_result/5`); none if the declared
    return channel and the site's result do not fit. *)
Definition external_env {world : Type} (spec : contract world) (site : call_site)
    (xs : list word) (e : env) : option env :=
  let* o := external_outcome (contract_returns spec) xs in
  returned_env (site_result site) o e.

(** The [[frame|configuration]] after an external call returns: the same
    function, locals, callers and [[fuel]], with environment e and
    memory m, at the instruction after the call. *)
Definition resume_external (c : config) (site : call_site) (e : env) (m : Memory.mem) : config :=
  let fr := c_frame c in
  mkConfig (mkFrame (fr_fn fr) e (fr_locals fr) None
    (Exec (site_label site) (site_rest site) (site_jump site))) (c_callers c) m (c_fuel c).

(** How a call site fails its contract: no contract is registered for
    the name, an argument does not evaluate, the ABI or the precondition
    does not hold, or the returned words do not fit the call's result.
    These are specification failures, not Fil-C [[trap|traps]]. *)
Inductive violation : Type := MissingContract | BadArguments | BadABI | BadPrecondition | BadReturn.

(** Why the labelled machine stopped: a core [[outcome]], a stuck core
    step with its diagnostic, a process exit with its status from an
    external call, or a contract violation at the call of symbol. *)
Inductive ending : Type :=
| CoreEnd (o : outcome)
| CoreStuck (diagnostic : string)
| ExternalExit (status : Z)
| ContractViolation (symbol : name) (why : violation).

(** At an [external_site], the core [Semantics.step] is stuck on the
    instruction, so no core continuation or allocation can compete with
    contract dispatch. Runtime safepoints ([[poll]]) remain. *)
Lemma external_site_stuck : forall ge c site,
  external_site ge c site -> Semantics.step ge c = Stuck "instruction".
Proof.
  intros ge c site (Hd & Ha & Hfn & Hdata & Hfree).
  unfold Semantics.step. rewrite Ha, Hd. unfold inst_step.
  destruct (map_option (arg_x ge (fr_env (c_frame c))) (site_args site)); [|reflexivity].
  rewrite Hfn. unfold external_call. rewrite Hdata, Hfree. reflexivity.
Qed.

(** ## The labelled machine *)

(** The labelled machine over any [[runtime]] R, with the call relations
    (E), the evidence invariant (P) and the [[single definition]]
    invariant (S) instantiated at R. *)
Module ExternalMachine (R : Runtime).

Module E := ExternalCalls R.
Module P := Persistence R.
Module S := Single R.
Import P.I P.I.RM.

(** A core machine step ([mstep]) is also a step of the copy of the
    machine inside the single-definition functor. The two invariant
    functors instantiate the same core machine, but its inductive
    relation is generative; copy only its constructors. *)
Lemma single_core_step : forall ge ms ms', mstep ge ms ms' -> S.ID.RM.mstep ge ms ms'.
Proof. intros ge ms ms' H. destruct H; [eapply S.ID.RM.mstep_next | eapply S.ID.RM.mstep_alloc | eapply S.ID.RM.mstep_safepoint]; eauto. Qed.

(** At an [external_site], the only core machine step is a safepoint
    ([[poll]]): it is due there, the runtime acts on memory, and the
    call point stays in place. A contract's precondition is then checked
    in the post-safepoint state. *)
Lemma external_core_safepoint : forall ge c s c' s' site,
  external_site ge c site -> mstep ge (c, s) (c', s') ->
  safepoint_due ge c = true /\ exists m', c' = with_mem c m' /\ R.safepoint s (c_mem c) s' m'.
Proof.
  intros ge c s c' s' site Hsite H.
  pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
  inversion H; subst; try congruence. eauto.
Qed.

(** Everything below is over one type world of logical libc state,
    shared by all registered contracts. *)
Section World.
Variable world : Type.

(** A labelled machine state: a core machine state (configuration and
    runtime state) and the world, either running or stopped with an
    [ending]. *)
Inductive state : Type :=
| Running (machine : mstate) (w : world)
| Stopped (why : ending) (machine : mstate) (w : world).

(** The core machine state inside st. *)
Definition machine_of (st : state) : mstate :=
  match st with Running ms _ | Stopped _ ms _ => ms end.

(** The [[runtime]] is [[ready]] in st's machine state. *)
Definition state_ready (st : state) : Prop := ready_state (machine_of st).

(** The call at site is admissible under the registry (each name's
    contract, if any) in configuration c and world w: a contract is
    registered, the arguments evaluate to words xs, and the ABI and the
    precondition hold. These obligations are at the call site, not
    conditional on there being an invoke derivation. Negating pre does
    not grant a libc trap. *)
Definition admissible (registry : name -> option (contract world)) (ge : genv)
    (c : config) (w : world) (site : call_site) : Prop :=
  exists spec xs,
    registry (site_name site) = Some spec /\
    map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs /\
    contract_abi spec (site_result site) (site_args site) /\ contract_pre spec xs (c_mem c) w.

(** Why the call at site is rejected, checked in order: no registered
    contract, an argument that does not evaluate, a false ABI premise,
    or a false precondition. Each is the [violation] of the same name;
    a bad return is caught after the call, by [step_bad_return]. *)
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

(** One labelled [[step]] under the registry, with its events:
    - a core machine step ([mstep]), silent;
    - a core terminal, stuck step or allocation refusal, where no
      external call is due, stopping with the configuration as it was;
    - a completed call at an [external_site]: a return resumes at the
      next instruction with the call's memory, runtime state and world
      ([resume_external]), an exit or resource ending stops with them;
    - a [rejected] call, or a return the site's result cannot take,
      stopping with a [ContractViolation]. *)
Inductive step (registry : name -> option (contract world)) (ge : genv)
    : state -> list event -> state -> Prop :=
| step_core : forall ms ms' w,
    mstep ge ms ms' -> step registry ge (Running ms w) [] (Running ms' w)
(** Core terminals retain an observation snapshot. Done contains no
    final memory: e.g. a top-level return discards its invalidated locals. *)
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

(** A finite labelled [[run]]: a sequence of steps whose events are
    concatenated in order. Completed calls are atomic here. [prefix]
    remains independent: this is not yet a native prefix or totality
    semantics. *)
Inductive run (registry : name -> option (contract world)) (ge : genv)
    : state -> list event -> state -> Prop :=
| run_refl : forall st, run registry ge st [] st
| run_cons : forall st trace mid tail last,
    step registry ge st trace mid -> run registry ge mid tail last ->
    run registry ge st (trace ++ tail) last.

(** No running state reached from start can step to a
    [ContractViolation]. Safety against specification failures is about
    EVERY reached state, not merely the ending a chosen path happens to
    take. A safepoint that later repairs pre cannot erase an earlier
    rejection. *)
Definition no_violation (registry : name -> option (contract world)) (ge : genv) (start : state) : Prop :=
  forall prefix ms w trace symbol why ms' w',
    run registry ge start prefix (Running ms w) ->
    ~ step registry ge (Running ms w) trace (Stopped (ContractViolation symbol why) ms' w').

(** Where there is [no_violation] from start, no external call reached
    from it is [rejected]. *)
Lemma no_violation_rejected : forall registry ge start prefix c s w site why,
  no_violation registry ge start -> run registry ge start prefix (Running (c, s) w) ->
  external_site ge c site -> ~ rejected registry ge c w site why.
Proof.
  intros registry ge start prefix c s w site why Hsafe Hrun Hsite Hbad.
  exact (Hsafe _ _ _ _ _ _ _ _ Hrun (step_rejected _ _ _ _ _ _ _ Hsite Hbad)).
Qed.

(** A stopped state does not step. *)
Lemma stopped_no_step : forall registry ge why ms w trace st,
  ~ step registry ge (Stopped why ms w) trace st.
Proof. intros registry ge why ms w trace st H. inversion H. Qed.

(** Where no external call is due, a step observes nothing. *)
Lemma non_external_silent : forall registry ge c s w trace st,
  (forall site, ~ external_site ge c site) -> step registry ge (Running (c, s) w) trace st -> trace = [].
Proof. intros registry ge c s w trace st Hnone H. inversion H; subst; try reflexivity; exfalso; eapply Hnone; eauto. Qed.

(** A step that stops with [[unchecked|Unchecked]] why is the old core's
    own ending: external calls never produce it. This does not prove
    arbitrary frees or [[doomed]] runs safe. *)
Lemma unchecked_is_core : forall registry ge c s w trace ms' w' why,
  step registry ge (Running (c, s) w) trace (Stopped (CoreEnd (Unchecked why)) ms' w') ->
  Semantics.step ge c = Done (Unchecked why).
Proof. intros registry ge c s w trace ms' w' why H. inversion H; subst; assumption. Qed.

(** An [admissible] call is not [rejected]. *)
Lemma admissible_not_rejected : forall registry ge c w site why,
  admissible registry ge c w site -> ~ rejected registry ge c w site why.
Proof.
  intros registry ge c w site why (spec & xs & Hr & Hx & Ha & Hp) H.
  destruct H; try congruence.
Qed.

(** A labelled step keeps the [[runtime]] [[ready]], where the global
    environment's free is the runtime's. *)
Theorem step_ready : forall registry ge st trace st',
  ge_free ge = R.free -> step registry ge st trace st' -> state_ready st -> state_ready st'.
Proof.
  intros registry ge st trace st' Hfree H. destruct H; simpl; intros Hr;
    try exact Hr; try solve [eapply mstep_ready; eauto].
  all: exact (proj1 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
Qed.

(** From a ready state, every object of the memory before a labelled
    step [[identity|persists]] into the memory after it. *)
Theorem step_persists : forall registry ge st trace st',
  ge_free ge = R.free -> step registry ge st trace st' -> state_ready st ->
  persists (c_mem (fst (machine_of st))) (c_mem (fst (machine_of st'))).
Proof.
  intros registry ge st trace st' Hfree H. destruct H; simpl; intros Hr;
    try apply persists_refl.
  1: exact (S.ID.mstep_persists _ _ _ Hfree Hr (single_core_step _ _ _ H)).
  all: exact (proj2 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
Qed.

(** ## Continuations and Campaign 3 *)

(** Resuming after an external call keeps the [[evidence]] invariant
    [inv] of a module md: the call kills the frame's live facts, so the
    frame is [parked] there ([call_parked]) and resumes with any result
    and memory ([parked_resume]). *)
Lemma resume_inv : forall ge md c s site e m' s',
  external_site ge c site -> inv ge md (c, s) -> inv ge md (resume_external c site e m', s').
Proof.
  intros ge md c s site e m' s' (Hd & Ha & _) [Hfr Hcs]. split; [|exact Hcs].
  exact (parked_resume ge md m'
    (mkFrame (fr_fn (c_frame c)) (fr_env (c_frame c)) (fr_locals (c_frame c)) None
      (Exec (site_label site) (site_rest site) (site_jump site))) e
    (call_parked _ _ _ _ _ _ _ _ _ _ Hfr Hd Ha)).
Qed.

(** Binding a call's returned values changes no [[temporary]] a but the
    names the site's result defines ([result_names]). *)
Lemma external_env_other : forall (spec : contract world) site values old e a,
  external_env spec site values old = Some e -> ~ In a (result_names (site_result site)) ->
  lookup a e = lookup a old.
Proof.
  intros spec site values old e a H Ha. unfold external_env in H.
  destruct (external_outcome _ _) as [o|]; [|discriminate H].
  exact (returned_env_other _ _ _ _ _ H Ha).
Qed.

(** Resuming after an external call keeps the [[single definition]]
    invariant [sinv] of a [checked_module] md, where the call's memory
    m' [[identity|persists]] from the old: the result names are its only
    new definitions, and waiting callers keep their scopes. *)
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

(** The [[evidence]] invariant [inv] of a running state; nothing of a
    stopped one. Terminal snapshots retain memory and readiness, not
    active-frame facts. Only a returned call has a caller continuation
    to re-establish. *)
Definition evidence_inv (ge : genv) (md : module) (st : state) : Prop :=
  match st with Running ms _ => inv ge md ms | Stopped _ _ _ => True end.

(** The [[single definition]] invariant [sinv] of a running state's
    configuration; nothing of a stopped one. *)
Definition single_inv (ge : genv) (md : module) (st : state) : Prop :=
  match st with Running ms _ => sinv ge md (fst ms) | Stopped _ _ _ => True end.

(** A labelled step from a ready state keeps [evidence_inv] of the
    environment's [checked_module] md. *)
Theorem step_inv : forall registry ge md st trace st',
  ge_module ge = md -> checked_module md ->
  step registry ge st trace st' -> state_ready st -> evidence_inv ge md st -> evidence_inv ge md st'.
Proof.
  intros registry ge md st trace st' Hge Hmd H. destruct H; simpl; intros Hr Hi; try exact I.
  - eapply P.mstep_inv; eauto.
  - eapply resume_inv; eauto.
Qed.

(** A labelled step from a ready state keeps [single_inv] of the
    environment's [checked_module] md, where its free is the runtime's. *)
Theorem step_sinv : forall registry ge md st trace st',
  ge_module ge = md -> checked_module md -> ge_free ge = R.free ->
  step registry ge st trace st' -> state_ready st -> single_inv ge md st -> single_inv ge md st'.
Proof.
  intros registry ge md st trace st' Hge Hmd Hfree H. destruct H; simpl; intros Hr Hi; try exact I.
  - exact (S.mstep_sinv _ _ _ _ Hge Hmd Hfree Hr (single_core_step _ _ _ H) Hi).
  - eapply resume_sinv; eauto. exact (proj2 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hr)).
Qed.

(** The four structural guarantees for every finite labelled [run] of
    a [checked_module] md, from a state that has them: the runtime stays
    [[ready]], objects [[identity|persist]], and [evidence_inv] and
    [single_inv] hold at the end. No completeness or absence of contract
    violations follows from them. *)
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

(** Accept an existing machine instance rather than instantiate a sibling
    functor. In particular its inductive [E.invoke], [E.effects], [step]
    and [run] types remain the caller's exact types. This signature adds
    no runtime assumptions and changes no transition or theorem. *)
Module Type ExternalMachineSig (R : Runtime).
Include ExternalMachine R.
End ExternalMachineSig.

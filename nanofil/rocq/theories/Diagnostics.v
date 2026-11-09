(** GNU error has two different continuations: status zero returns void;
    nonzero requests soft exit after the diagnostic. Formatting, program
    name/strerror decoration, stream effects and their authority are imported
    obligations, not invented bytes or an unmodelled stdout acceptance. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics
  Machine Identity ExternalCalls Startup Stdio Shutdown ExternalMachine Linked Ending.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** A formatter must interpret the fixed W,W,P arguments and exact promoted
    varargs. Its ABI supplies the allowed classes for the variadic suffix. *)
Definition error_abi (fmt_abi : call_result -> list arg -> Prop)
    (r : call_result) (args : list arg) : Prop :=
  r = CVoid /\ fmt_abi r args /\ exists status errnum format rest,
    args = Arg W status :: Arg W errnum :: Arg P format :: rest.

(** Status and errno are canonical C-int bits, not a low-byte wait status.
    String validity and actual varargs interpretation belong to the formatter. *)
Definition error_words (xs : list word) (status : Z) : Prop :=
  exists errnum format rest,
    xs = WInt status :: WInt errnum :: WPtr format :: rest /\
    0 <= status < 2 ^ 32 /\ 0 <= errnum < 2 ^ 32.

(** Only stderr acceptance is observable here. Stdout flushes may settle
    earlier output but cannot relabel diagnostic bytes as stdout acceptance. *)
Definition diagnostic_trace (trace : list event) : Prop :=
  Forall (fun observation => match observation with
    | StreamBytes stream _ => stream = 2 | ProcessExit _ => False end) trace.

(** No diagnostic prefix contains a host-termination observation. *)
Lemma diagnostic_trace_exit_free : forall trace,
  diagnostic_trace trace -> forall status, ~ In (ProcessExit status) trace.
Proof.
  intros trace H status Hin. unfold diagnostic_trace in H.
  rewrite Forall_forall in H. exact (H _ Hin).
Qed.

(** In particular stderr output never becomes stdout acceptance. *)
Lemma diagnostic_trace_not_stdout : forall trace bytes,
  diagnostic_trace trace -> ~ In (StreamBytes 1 bytes) trace.
Proof.
  intros trace bytes H Hin. unfold diagnostic_trace in H.
  rewrite Forall_forall in H. specialize (H _ Hin). discriminate H.
Qed.

(** This contract summarizes only the diagnostic stage, before the status
    branch. Its virtual void result is NOT a normal return from error when
    status is nonzero; do not register it as error's ordinary contract.
    Resource prefixes retain no normal-completion facts. All capability
    sources, writes, releases, allocations and panic policy come from fmt. *)
Definition diagnostic_contract {world : Type} (fmt : contract world) : contract world :=
  mkContract world RVoid (error_abi (contract_abi fmt))
    (fun xs m w => contract_pre fmt xs m w /\ exists status, error_words xs status)
    (contract_sources fmt) (contract_writes fmt) (contract_releases fmt) (contract_requests fmt)
    (fun xs m w born trace m' w' =>
      contract_prefix fmt xs m w born trace m' w' /\ diagnostic_trace trace)
    (fun xs m w born trace ending m' w' =>
      contract_post fmt xs m w born trace ending m' w' /\ ending = CallReturn [])
    (contract_resource fmt) (contract_panics fmt).

(** Only status-zero error may use ordinary ExternalMachine dispatch. The
    caller's frame/locals/continuation are preserved by resume_external;
    libc state, errno and stream settlement may change under fmt's effects. *)
Definition error_contract {world : Type} (fmt : contract world) : contract world :=
  let spec := diagnostic_contract fmt in
  mkContract world RVoid (contract_abi spec)
    (fun xs m w => contract_pre spec xs m w /\ error_words xs 0)
    (contract_sources spec) (contract_writes spec) (contract_releases spec) (contract_requests spec)
    (contract_prefix spec) (contract_post spec) (contract_resource spec) (contract_panics spec).

(** The normal-return shape is available without choosing a runtime instance. *)
Lemma error_post_void : forall world (fmt : contract world) xs m w born trace ending m' w',
  contract_post (error_contract fmt) xs m w born trace ending m' w' -> ending = CallReturn [].
Proof. intros world fmt xs m w born trace ending m' w' [_ H]. exact H. Qed.

(** Canonical argument lists determine status independently of behavior. *)
Lemma error_words_status : forall xs left right,
  error_words xs left -> error_words xs right -> left = right.
Proof.
  intros xs left right (e & p & rest & Hl & _) (e' & p' & rest' & Hr & _).
  rewrite Hl in Hr. injection Hr. auto.
Qed.

(** A nonzero diagnostic is never admitted as an ordinary returning error. *)
Lemma nonzero_error_not_returning : forall world (fmt : contract world) xs m w status,
  error_words xs status -> status <> 0 -> ~ contract_pre (error_contract fmt) xs m w.
Proof.
  intros world fmt xs m w status Hstatus Hnonzero [_ Hzero].
  apply Hnonzero. eapply error_words_status; eauto.
Qed.

(** Diagnostics reuse the exact runtime, effects and current Linked world. *)
Module Diagnostics (R : Runtime) (L : LinkedSig R).
Module N := Ending R L.
Module M := N.M.
Module E := N.E.
Module RM := N.RM.

Section World.
Variable payload : Type.
Variable fmt : contract (N.world payload).

(** The selected error call is independently admitted even if no diagnostic
    invocation completes. This premise does not promise termination. *)
Definition error_site ge c site xs : Prop :=
  external_site ge c site /\ site_name site = TAtom "error" /\
  map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs /\
  contract_abi (diagnostic_contract fmt) (site_result site) (site_args site).

(** Caller admission is independent of a completed formatting stage. *)
Definition error_admitted ge c w site : Prop :=
  exists xs, error_site ge c site xs /\ contract_pre (diagnostic_contract fmt) xs (c_mem c) w.

(** A nonzero completed diagnostic requests exit with its CURRENT world,
    including any stdout flush/error and stderr settlement. It never reuses
    registration-time state, resumes the caller or emits ProcessExit. *)
Inductive error_request ge : config -> R.state -> N.world payload -> list event ->
    RM.mstate -> N.world payload -> Prop :=
| error_requests_exit : forall c s w site xs status trace s' m' w' sh',
    error_site ge c site xs -> error_words xs status -> status <> 0 ->
    E.invoke (diagnostic_contract fmt) (site_result site) (site_args site) xs
      s (c_mem c) w trace (CallReturn []) s' m' w' ->
    shutdown_unique (snd w') -> exit_request SoftExit (main_status status) (snd w') sh' ->
    error_request ge c s w trace (RM.with_mem c m', s') (fst w', sh').

(** Extension rules are disjoint from Ending's ordinary error dispatch.
    Status-zero returns and resources remain ordinary external outcomes;
    nonzero diagnostics have an exit-request edge or a resource leaf. *)
Inductive step registry ge (b : N.boundary payload) admitted :
    N.state payload -> list event -> N.state payload -> Prop :=
| diagnostic_ending : forall st trace st',
    N.step payload registry ge (fun symbol => name_eqb symbol (TAtom "error")) b admitted
      st trace st' -> step registry ge b admitted st trace st'
| diagnostic_zero : forall c s w site xs trace result s' m' w' e,
    error_site ge c site xs ->
    E.invoke (error_contract fmt) (site_result site) (site_args site) xs
      s (c_mem c) w trace (CallReturn result) s' m' w' ->
    external_env (error_contract fmt) site result (fr_env (c_frame c)) = Some e ->
    step registry ge b admitted (N.Executing payload (M.Running (c, s) w)) trace
      (N.Executing payload (M.Running (resume_external c site e m', s') w'))
| diagnostic_request : forall c s w trace ms' w',
    error_request ge c s w trace ms' w' ->
    step registry ge b admitted (N.Executing payload (M.Running (c, s) w)) trace
      (N.Draining payload ms' w')
| diagnostic_resource : forall c s w site xs trace why s' m' w',
    error_site ge c site xs ->
    E.invoke (diagnostic_contract fmt) (site_result site) (site_args site) xs
      s (c_mem c) w trace (CallResource why) s' m' w' ->
    step registry ge b admitted (N.Executing payload (M.Running (c, s) w)) trace
      (N.Executing payload (M.Stopped (CoreEnd (Trap why)) (RM.with_mem c m', s') w'))
| diagnostic_prefix : forall c s w site xs born trace s' m' w',
    error_site ge c site xs -> contract_pre (diagnostic_contract fmt) xs (c_mem c) w ->
    E.prefix (diagnostic_contract fmt) xs s (c_mem c) w born trace s' m' w' ->
    step registry ge b admitted (N.Executing payload (M.Running (c, s) w)) trace
      (N.Partial payload (RM.with_mem c m', s') w')
| diagnostic_rejected : forall c s w site,
    external_site ge c site -> site_name site = TAtom "error" ->
    ~ error_admitted ge c w site ->
    step registry ge b admitted (N.Executing payload (M.Running (c, s) w)) []
      (N.Executing payload (M.Stopped (ContractViolation (TAtom "error") BadPrecondition) (c, s) w)).

(** A diagnostic request carries only diagnostic events, not host exit. *)
Theorem error_request_exit_free : forall ge c s w trace ms' w',
  error_request ge c s w trace ms' w' -> diagnostic_trace trace.
Proof.
  intros ge c s w trace ms' w' H. destruct H.
  destruct (E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ H2) as [born [_ [_ Htrace]]].
  exact Htrace.
Qed.

(** Every request keeps readiness and identities through the formatter's
    actual effect path; no final-return state is assumed for resources. *)
Theorem error_request_preserve : forall ge c s w trace ms' w',
  error_request ge c s w trace ms' w' -> R.ready s (c_mem c) ->
  RM.ready_state ms' /\ persists (c_mem c) (c_mem (fst ms')).
Proof.
  intros ge c s w trace ms' w' H Hr. destruct H. simpl.
  eapply E.invoke_preserve; eauto.
Qed.

(** Both diagnostic branches and their resource/unfinished leaves retain
    readiness and identities, using the imported formatter's exact effects. *)
Theorem step_preserve : forall registry ge b admitted st trace st',
  ge_free ge = R.free -> step registry ge b admitted st trace st' ->
  N.state_ready payload st -> N.state_ready payload st' /\
  persists (c_mem (fst (N.machine_of payload st)))
    (c_mem (fst (N.machine_of payload st'))).
Proof.
  intros registry ge b admitted st trace st' Hfree H. destruct H; intros Hr.
  - eapply N.step_preserve; eauto.
  - eapply E.invoke_preserve; eauto.
  - eapply error_request_preserve; eauto.
  - eapply E.invoke_preserve; eauto.
  - eapply E.prefix_preserve; eauto.
  - split; auto using persists_refl.
Qed.

End World.
End Diagnostics.

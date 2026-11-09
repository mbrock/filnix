(** Exit requests precede terminal external dispatch. This additive bridge
    shares Linked's current payload and authoritative shutdown inventory.
    Native registration, administrative effects and host completion remain
    explicit trusted obligations; no native coverage or termination follows. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics
  Machine Identity ExternalCalls Startup Stdio Shutdown ExitMemory ExternalMachine Linked.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Only these unresolved direct symbols are plain exit requests. An
    already stopped ExternalExit is never decoded as another request. *)
Definition exit_symbol (symbol : name) : option handoff_kind :=
  if name_eqb symbol (TAtom "exit") then Some SoftExit else
  if name_eqb symbol (TAtom "_exit") then Some HardExit else
  if name_eqb symbol (TAtom "_Exit") then Some HardExit else None.

(** A C int argument has W class and a nonreturning void call site. *)
Definition exit_abi (r : call_result) (args : list arg) : Prop :=
  r = CVoid /\ exists value, args = [Arg W value].

(** Initial and nested soft requests retain the CURRENT inventory and
    stdout. Initial application execution uses Tls as its dormant phase.
    No soft request reopens closed cleanup. Hard exit never flushes. *)
Inductive exit_request : handoff_kind -> Z -> shutdown_state -> shutdown_state -> Prop :=
| request_initial : forall status old pending consumed q,
    exit_request SoftExit status (mkShutdown Tls old pending consumed q)
      (mkShutdown Tls status pending consumed q)
| request_recursive : forall status old active pending consumed q,
    exit_request SoftExit status (mkShutdown (InCallback active) old pending consumed q)
      (mkShutdown Tls status pending consumed q)
| request_hard : forall status sh,
    (forall kind, shutdown_at sh <> HandedOff kind) ->
    exit_request HardExit status sh
      (mkShutdown (HandedOff HardExit) status (shutdown_pending sh)
        (shutdown_consumed sh) (shutdown_stdout sh)).

(** Requests preserve all registration instances and output obligations. *)
Lemma exit_request_inventory : forall kind status sh sh',
  exit_request kind status sh sh' ->
  shutdown_pending sh' = shutdown_pending sh /\
  shutdown_consumed sh' = shutdown_consumed sh /\
  shutdown_stdout sh' = shutdown_stdout sh /\ shutdown_status sh' = status.
Proof. intros kind status sh sh' H. destruct H; repeat split; reflexivity. Qed.

(** Uniqueness survives recursive and hard exit without a new inventory. *)
Lemma exit_request_unique : forall kind status sh sh',
  exit_request kind status sh sh' -> shutdown_unique sh -> shutdown_unique sh'.
Proof. intros kind status sh sh' H. destruct H; auto. Qed.

(** Successful registration is permitted before exit or inside a callback,
    never after cleanup. Tokens are fresh even for repeated function names. *)
Inductive registration_update (entry : registration) : shutdown_state -> shutdown_state -> Prop :=
| registration_before_exit : forall status pending consumed q,
    ~ In (registration_token entry) (consumed ++ map registration_token pending) ->
    registration_update entry (mkShutdown Tls status pending consumed q)
      (mkShutdown Tls status (entry :: pending) consumed q)
| registration_in_callback : forall status active pending consumed q,
    ~ In (registration_token entry) (consumed ++ map registration_token pending) ->
    registration_update entry (mkShutdown (InCallback active) status pending consumed q)
      (mkShutdown (InCallback active) status (entry :: pending) consumed q).

(** Registration does not alter the active status, consumed history or stdout. *)
Lemma registration_update_unique : forall entry sh sh',
  registration_update entry sh sh' -> shutdown_unique sh -> shutdown_unique sh'.
Proof.
  intros entry sh sh' H Hu. destruct H; unfold shutdown_unique in *; simpl in *;
    apply shutdown_unique_insert; assumption.
Qed.

(** This pin implements atexit with a cxa slot, null argument and null DSO.
    Physical representation and callback semantic admission are independent. *)
Definition atexit_installed m head blocks function entry : Prop :=
  exists token symbol,
    entry = mkRegistration token (CxaExit symbol (WPtr (mkPtr 0 CNone))) /\
    ptr_cap function = Fn symbol /\
    In (CxaSlot token symbol function (mkPtr 0 CNone) (mkPtr 0 CNone))
      (flat_map block_slots blocks) /\
    exit_registry_memory m head blocks.

(** Even resource/unfinished prefixes retain the current inventory or add
    exactly one freshly installed instance. Reserved physical slots do not
    yet add a logical callback. No completion result is asserted here. *)
Definition atexit_progress {payload : Type}
    (represented : mem -> payload -> ptr -> list exit_block -> Prop)
    xs (w : payload * shutdown_state) m' (w' : payload * shutdown_state) : Prop :=
  exists head blocks,
    represented m' (fst w') head blocks /\ exit_registry_memory m' head blocks /\
    exit_registry_pending blocks = shutdown_pending (snd w') /\
    (snd w' = snd w \/ exists function entry,
      xs = [WPtr function] /\ atexit_installed m' head blocks function entry /\
      registration_update entry (snd w) (snd w')).

(** The native contract supplies effects, allocation and private registry
    authority. This overlay supplies the exact public API and couples its
    successful result to physical installation and the single inventory.
    Callback admission must be supplied independently at entry. *)
Definition atexit_contract {payload : Type} (ge : genv)
    (native : contract (payload * shutdown_state))
    (represented : mem -> payload -> ptr -> list exit_block -> Prop)
    : contract (payload * shutdown_state) :=
  mkContract _ (RClass W)
    (fun r args => (r = CVoid \/ exists d, r = CResult d W) /\
      (exists value, args = [Arg P value]) /\ contract_abi native r args)
    (fun xs m w => contract_pre native xs m w /\ shutdown_unique (snd w) /\
      atexit_progress represented xs w m w /\
      exists function, xs = [WPtr function] /\ function_check_res ge function = Some ok)
    (contract_sources native) (contract_writes native) (contract_releases native)
    (contract_requests native)
    (fun xs m w born trace m' w' => contract_prefix native xs m w born trace m' w' /\
      trace = [] /\ atexit_progress represented xs w m' w')
    (fun xs m w born trace ending m' w' =>
      contract_post native xs m w born trace ending m' w' /\
      exists function result,
        xs = [WPtr function] /\ ending = CallReturn [WInt result] /\ trace = [] /\
        ((result = 0 /\ exists head blocks entry,
            represented m' (fst w') head blocks /\
            atexit_installed m' head blocks function entry /\
            exit_registry_pending blocks = shutdown_pending (snd w') /\
            registration_update entry (snd w) (snd w')) \/
         (result = 2 ^ 32 - 1 /\ snd w' = snd w)))
    (contract_resource native) (contract_panics native).

(** Only administrative actions may be delegated wholesale. Callback pop,
    execution and return use the separate, memory-backed rules below. *)
Definition administrative (action : shutdown_action) : Prop :=
  match action with
  | EmptyTls | StartCleanup | ShutdownOutput _ | Handoff _ _ => True
  | _ => False
  end.

(** Requests and callbacks extend the labelled machine, never Machine.v. *)
Module Ending (R : Runtime) (L : LinkedSig R).
Module M := L.M.
Module E := M.E.
Module RM := L.RM.
Module Pop := ExitPop R.
Module Unlink := ExitUnlink R.

Section World.
Variable payload : Type.
(** One payload and one authoritative lifecycle, as in Linked. *)
Definition world : Type := L.callback_world payload.

(** Running application/callback code, a suspended exit loop, and completed
    host termination retain exact machine snapshots. Stopped remains stopped. *)
Inductive state : Type :=
| Executing (st : M.state world)
| Draining (ms : RM.mstate) (w : world)
| Partial (ms : RM.mstate) (w : world)
| Finished (ms : RM.mstate) (w : world).

(** Every mode retains its exact machine snapshot, including partial leaves. *)
Definition machine_of (st : state) : RM.mstate :=
  match st with
  | Executing active => M.machine_of _ active
  | Draining ms _ | Partial ms _ | Finished ms _ => ms
  end.

(** Readiness does not assert contract admission, progress or native coverage. *)
Definition state_ready (st : state) : Prop := RM.ready_state (machine_of st).

(** Administrative libc effects use the existing capability/effects boundary.
    Readiness/representation at both endpoints is an explicit obligation,
    not a native satisfaction theorem. A synthetic CallReturn [] marks a
    completed internal cutpoint, not a native return from host handoff.
    registry_rep identifies the authoritative physical chain in the payload;
    use this same projection as atexit_contract's represented argument. *)
Record boundary : Type := mkBoundary {
  ending_rep : R.state -> mem -> world -> Prop;
  registry_rep : mem -> payload -> ptr -> list exit_block -> Prop;
  registry_owned : payload -> list Z;
  action_spec : shutdown_action -> contract world;
  action_args : shutdown_action -> list arg;
  action_values : shutdown_action -> list word;
  host_complete : R.state -> mem -> world -> Prop
}.

(** The selected request syntax, evaluated independently of any invocation. *)
Definition request_site ge c site kind bits : Prop :=
  external_site ge c site /\ exit_symbol (site_name site) = Some kind /\
  exit_abi (site_result site) (site_args site) /\
  map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some [WInt bits].

(** Admission is independent of successful execution. Reached-call proofs
    must establish it again after safepoints; its failure is visible below. *)
Definition request_admitted (b : boundary) ge c s w site kind : Prop :=
  ending_rep b s (c_mem c) w /\ shutdown_unique (snd w) /\
  exists bits sh', request_site ge c site kind bits /\
    exit_request kind (main_status bits) (snd w) sh'.

(** A single dispatcher: reserved names (e.g. error) are handled by a
    further explicit bridge, not ordinary terminal external dispatch.
    Safepoints at intercepted calls still run and recheck admission later. *)
Inductive step (registry : name -> option (contract world)) ge
    (reserved : name -> bool) (b : boundary)
    (admitted : registration -> R.state -> mem -> world -> Prop)
    : state -> list event -> state -> Prop :=
| ending_ordinary : forall st trace st',
    (forall c s w site, st = M.Running (c, s) w -> external_site ge c site ->
      exit_symbol (site_name site) = None /\ reserved (site_name site) = false) ->
    M.step registry ge st trace st' ->
    step registry ge reserved b admitted (Executing st) trace (Executing st')
| ending_poll : forall c s w s' m',
    RM.safepoint_due ge c = true -> R.safepoint s (c_mem c) s' m' ->
    step registry ge reserved b admitted (Executing (M.Running (c, s) w)) []
      (Executing (M.Running (RM.with_mem c m', s') w))
| ending_request : forall c s w site kind bits sh',
    request_site ge c site kind bits -> ending_rep b s (c_mem c) w ->
    shutdown_unique (snd w) ->
    exit_request kind (main_status bits) (snd w) sh' ->
    step registry ge reserved b admitted (Executing (M.Running (c, s) w)) []
      (Draining (c, s) (fst w, sh'))
| ending_rejected : forall c s w site kind,
    external_site ge c site -> exit_symbol (site_name site) = Some kind ->
    ~ request_admitted b ge c s w site kind ->
    step registry ge reserved b admitted (Executing (M.Running (c, s) w)) []
      (Executing (M.Stopped (ContractViolation (site_name site) BadPrecondition) (c, s) w))
| ending_action : forall c s w action trace s' m' w',
    administrative action -> shutdown_step (snd w) action (snd w') ->
    ending_rep b s (c_mem c) w ->
    contract_abi (action_spec b action) CVoid (action_args b action) ->
    contract_pre (action_spec b action) (action_values b action) (c_mem c) w ->
    E.invoke (action_spec b action) CVoid (action_args b action) (action_values b action)
      s (c_mem c) w trace (CallReturn []) s' m' w' ->
    trace = match action with ShutdownOutput (Accept bytes) => [StreamBytes 1 bytes] | _ => [] end ->
    ending_rep b s' m' w' ->
    step registry ge reserved b admitted (Draining (c, s) w) trace
      (Draining (RM.with_mem c m', s') w')
| ending_action_prefix : forall c s w action born trace s' m' w',
    administrative action -> ending_rep b s (c_mem c) w ->
    contract_abi (action_spec b action) CVoid (action_args b action) ->
    contract_pre (action_spec b action) (action_values b action) (c_mem c) w ->
    E.prefix (action_spec b action) (action_values b action)
      s (c_mem c) w born trace s' m' w' ->
    (forall status, ~ In (ProcessExit status) trace) ->
    step registry ge reserved b admitted (Draining (c, s) w) trace
      (Partial (RM.with_mem c m', s') w')
| ending_action_resource : forall c s w action trace why s' m' w',
    administrative action -> ending_rep b s (c_mem c) w ->
    E.invoke (action_spec b action) CVoid (action_args b action) (action_values b action)
      s (c_mem c) w trace (CallResource why) s' m' w' ->
    (forall status, ~ In (ProcessExit status) trace) ->
    step registry ge reserved b admitted (Draining (c, s) w) trace
      (Executing (M.Stopped (CoreEnd (Trap why)) (RM.with_mem c m', s') w'))
| ending_pop : forall c s data status consumed q head p older slot rest entry fuel callback,
    registry_rep b (c_mem c) data head (mkExitBlock p (older ++ [slot]) :: rest) ->
    exit_registry_memory (c_mem c) head (mkExitBlock p (older ++ [slot]) :: rest) ->
    exit_pop_separated head p rest -> exit_slot_pending slot = [entry] ->
    Forall (writable_span (c_mem c)) (exit_pop_writes p older slot) ->
    shutdown_unique (mkShutdown Handlers status
      (exit_registry_pending (mkExitBlock p (older ++ [slot]) :: rest)) consumed q) ->
    L.callback_entry payload admitted ge slot entry s (exit_pop_memory (c_mem c) p older slot)
      (data, mkShutdown (InCallback entry) status
        (exit_registry_pending (mkExitBlock p older :: rest))
        (consumed ++ [registration_token entry]) q) fuel callback ->
    fuel = c_fuel c ->
    registry_rep b (exit_pop_memory (c_mem c) p older slot) data head
      (mkExitBlock p older :: rest) ->
    step registry ge reserved b admitted
      (Draining (c, s) (data, mkShutdown Handlers status
        (exit_registry_pending (mkExitBlock p (older ++ [slot]) :: rest)) consumed q)) []
      (Executing (M.Running (callback, s)
        (data, mkShutdown (InCallback entry) status
          (exit_registry_pending (mkExitBlock p older :: rest))
          (consumed ++ [registration_token entry]) q)))
| ending_skip : forall c s data status consumed q head p older slot rest,
    registry_rep b (c_mem c) data head (mkExitBlock p (older ++ [slot]) :: rest) ->
    exit_registry_memory (c_mem c) head (mkExitBlock p (older ++ [slot]) :: rest) ->
    exit_pop_separated head p rest -> slot = FreeSlot \/ slot = ReservedSlot ->
    Forall (writable_span (c_mem c)) (exit_pop_writes p older slot) ->
    registry_rep b (exit_pop_memory (c_mem c) p older slot) data head
      (mkExitBlock p older :: rest) ->
    step registry ge reserved b admitted
      (Draining (c, s) (data, mkShutdown Handlers status
        (exit_registry_pending (mkExitBlock p (older ++ [slot]) :: rest)) consumed q)) []
      (Draining (RM.with_mem c (exit_pop_memory (c_mem c) p older slot), s)
        (data, mkShutdown Handlers status
          (exit_registry_pending (mkExitBlock p older :: rest)) consumed q))
| ending_unlink : forall c s data status consumed q head p rest,
    registry_rep b (c_mem c) data head (mkExitBlock p [] :: rest) ->
    exit_registry_memory (c_mem c) head (mkExitBlock p [] :: rest) ->
    exit_unlink_separated head (mkExitBlock p [] :: rest) ->
    writable_span (c_mem c) (mkSpan head 8) ->
    registry_rep b (exit_unlink_memory (c_mem c) head rest) data head rest ->
    step registry ge reserved b admitted
      (Draining (c, s) (data, mkShutdown Handlers status
        (exit_registry_pending (mkExitBlock p [] :: rest)) consumed q)) []
      (Draining (RM.with_mem c (exit_unlink_memory (c_mem c) head rest), s)
        (data, mkShutdown Handlers status (exit_registry_pending rest) consumed q))
| ending_retire : forall c s data sh head block rest m',
    shutdown_at sh = Handlers -> shutdown_pending sh = exit_registry_pending rest ->
    registry_rep b (c_mem c) data head rest ->
    exit_block_releasable (registry_owned b data) (c_mem c) head block rest ->
    R.free (WPtr (block_ptr block)) (c_mem c) = Some (ok, m') ->
    E.effects [] [] [ptr_addr (block_ptr block)] (fun _ _ => False)
      s (c_mem c) [] s m' [] ->
    registry_rep b m' data head rest ->
    step registry ge reserved b admitted (Draining (c, s) (data, sh)) []
      (Draining (RM.with_mem c m', s) (data, sh))
| ending_return : forall entry st ms' w',
    L.callback_return payload entry st ms' w' ->
    step registry ge reserved b admitted (Executing st) [] (Draining ms' w')
| ending_complete : forall c s data kind status pending consumed q,
    host_complete b s (c_mem c) (data, mkShutdown (HandedOff kind) status pending consumed q) ->
    step registry ge reserved b admitted
      (Draining (c, s) (data, mkShutdown (HandedOff kind) status pending consumed q))
      [ProcessExit (process_status status)]
      (Finished (c, s) (data, mkShutdown (HandedOff kind) status pending consumed q)).

(** Entry uses the actual post-pop memory, not a second chosen snapshot. *)
Lemma callback_entry_memory : forall admitted ge slot entry s m w fuel callback,
  L.callback_entry payload admitted ge slot entry s m w fuel callback -> c_mem callback = m.
Proof.
  intros admitted ge slot entry s m w fuel callback
    (_ & _ & _ & _ & _ & _ & fr & _ & ->). reflexivity.
Qed.

(** Every new edge preserves readiness and identities by its existing effect
    path or local teardown. This is structural preservation, not safety. *)
Theorem step_preserve : forall registry ge reserved b admitted st trace st',
  ge_free ge = R.free -> step registry ge reserved b admitted st trace st' ->
  state_ready st -> state_ready st' /\
  persists (c_mem (fst (machine_of st))) (c_mem (fst (machine_of st'))).
Proof.
  intros registry ge reserved b admitted st trace st' Hfree H.
  destruct H; unfold state_ready, machine_of, RM.ready_state; simpl; intros Hr.
  - split; [eapply M.step_ready|eapply M.step_persists]; eauto.
  - assert (Hs : M.step registry ge (M.Running (c, s) w) []
      (M.Running (RM.with_mem c m', s') w)).
    { apply M.step_core. eapply RM.mstep_safepoint; eauto. }
    split.
    + exact (M.step_ready world registry ge _ _ _ Hfree Hs Hr).
    + exact (M.step_persists world registry ge _ _ _ Hfree Hs Hr).
  - split; auto using persists_refl.
  - split; auto using persists_refl.
  - eapply E.invoke_preserve; eauto.
  - eapply E.prefix_preserve; eauto.
  - eapply E.invoke_preserve; eauto.
  - match goal with Hentry : L.callback_entry _ _ _ _ _ _ _ _ _ _ |- _ =>
      rewrite (callback_entry_memory _ _ _ _ _ _ _ _ _ Hentry) end.
    exact (proj2 (Pop.pop_preserves _ _ _ _ _ H3 Hr)).
  - exact (proj2 (Pop.pop_preserves _ _ _ _ _ H3 Hr)).
  - eapply Unlink.unlink_preserves; eauto.
    match goal with Hregistry : exit_registry_memory _ _ _ |- _ =>
      exact (proj1 (proj1 (proj2 (proj2 Hregistry)))) end.
  - eapply E.effects_preserve; eauto.
  - destruct (L.callback_return_preserve _ _ _ _ _ H Hr) as [Hr' [Hp _]]. auto.
  - split; auto using persists_refl.
Qed.

(** Finite prefixes need not finish a handler or reach host completion. *)
Inductive run registry ge reserved b admitted : state -> list event -> state -> Prop :=
| run_refl : forall st, run registry ge reserved b admitted st [] st
| run_cons : forall st trace mid tail st',
    step registry ge reserved b admitted st trace mid ->
    run registry ge reserved b admitted mid tail st' ->
    run registry ge reserved b admitted st (trace ++ tail) st'.

(** Finite execution retains readiness and every starting identity. *)
Theorem run_preserve : forall registry ge reserved b admitted st trace st',
  ge_free ge = R.free -> run registry ge reserved b admitted st trace st' ->
  state_ready st -> state_ready st' /\
  persists (c_mem (fst (machine_of st))) (c_mem (fst (machine_of st'))).
Proof.
  intros registry ge reserved b admitted st trace st' Hfree H. induction H; intros Hr.
  - split; auto using persists_refl.
  - destruct (step_preserve _ _ _ _ _ _ _ _ Hfree H Hr) as [Hr1 Hp1].
    destruct (IHrun Hr1) as [Hr' Hp2]. split; [exact Hr'|].
    eapply persists_trans; eauto.
Qed.

(** A request is silent and never takes the caller's ordinary continuation. *)
Lemma request_no_observation : forall registry ge reserved b admitted c s w site kind bits sh',
  request_site ge c site kind bits -> ending_rep b s (c_mem c) w ->
  shutdown_unique (snd w) -> exit_request kind (main_status bits) (snd w) sh' ->
  step registry ge reserved b admitted (Executing (M.Running (c, s) w)) []
    (Draining (c, s) (fst w, sh')).
Proof. intros. eapply ending_request; eauto. Qed.

(** Partial cutpoints cannot resume shutdown or inherit a completed action. *)
Lemma partial_terminal : forall registry ge reserved b admitted ms w trace st',
  ~ step registry ge reserved b admitted (Partial ms w) trace st'.
Proof. intros registry ge reserved b admitted ms w trace st' H. inversion H. Qed.

(** Completed external exits cannot resume a callback or request shutdown. *)
Lemma completed_exit_terminal : forall registry ge reserved b admitted status ms w trace st',
  ~ step registry ge reserved b admitted (Executing (M.Stopped (ExternalExit status) ms w)) trace st'.
Proof.
  intros registry ge reserved b admitted status ms w trace st' H. inversion H; subst.
  - eapply M.stopped_no_step; eauto.
  - match goal with Hreturn : L.callback_return _ _ _ _ _ |- _ =>
      apply L.callback_return_only_void in Hreturn; discriminate end.
Qed.

(** abort is deliberately not mapped to soft exit. A whole-program safety
    proof must exclude every reached abort call or provide another boundary. *)
Example abort_not_exit : exit_symbol (TAtom "abort") = None.
Proof. reflexivity. Qed.

End World.
End Ending.

(** Signed status replacement retains partially outstanding output. *)
Example request_nested_current : forall q,
  exit_request SoftExit (-257)
    (mkShutdown (InCallback exit_second) 31 [exit_added; exit_first] [2]%nat q)
    (mkShutdown Tls (-257) [exit_added; exit_first] [2]%nat q).
Proof. intros. constructor. Qed.

(** Neither cleanup nor an already completed handoff can restart soft exit. *)
Example request_closed : forall status old pending consumed q sh',
  ~ exit_request SoftExit status (mkShutdown Cleanup old pending consumed q) sh' /\
  ~ exit_request SoftExit status (mkShutdown (HandedOff SoftExit) old pending consumed q) sh'.
Proof. intros. split; intro H; inversion H. Qed.

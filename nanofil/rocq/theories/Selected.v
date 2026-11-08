(** Selected libc lifecycle segments, over the existing external-call
    effect discipline. Admission precedes behavior existence. Successful
    invocations supply their own logical endpoint and allocator readiness;
    neither is inferred from an unfinished prefix. Native satisfaction and
    coverage remain trusted obligations, not theorems of this adapter. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Identity
  ExternalCalls ExternalMachine Startup Stdio Shutdown Hi Composition HiArtifact Program Panics.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** No changes to the core machine, runtime axioms or shutdown leaves. *)
Module Selected (R : Runtime).
Module A := HiProgram R.
Module P := A.P.
Module E := P.M.E.

(** Logical libc validity is separate from allocator readiness. Each action
    selects its own capability sources, writable spans, owned releases and
    allocation requests; reachability alone grants none of those rights.
    Validity must retain pending/active callback code and arguments, not
    require already-consumed arguments to remain live forever. *)
Record segments : Type := mkSegments {
  libc_valid : mem -> stdio_world -> shutdown_state -> Prop;
  selected_action : mem -> stdio_world -> shutdown_state -> shutdown_action -> Prop;
  segment_sources : shutdown_state -> shutdown_action -> mem -> stdio_world -> list span;
  segment_writes : shutdown_state -> shutdown_action -> mem -> stdio_world -> list span;
  segment_releases : shutdown_state -> shutdown_action -> mem -> stdio_world -> list Z;
  segment_requests : shutdown_state -> shutdown_action -> mem -> stdio_world -> Z -> Z -> Prop;
  segment_prefix : shutdown_state -> shutdown_action -> mem -> stdio_world ->
    list Z -> list event -> mem -> stdio_world -> Prop;
  segment_panics : shutdown_state -> shutdown_action -> reason -> Prop
}.

(** Completion shares the very same logical target between the contract
    postcondition and the outer adapter. The lifecycle edge fixes phase,
    status, inventory and FIFO output transfer; validity supplies the native
    representation obligation. It says nothing about native totality. *)
Definition segment_finish (specs : segments) sh action trace m' w' sh' : Prop :=
  shutdown_step sh action sh' /\ trace = P.action_events action /\ libc_valid specs m' w' sh'.

(** Empty arguments/void return describe a logical segment marker, NOT a
    callback's C ABI or a native return from exit/_exit. Enabled selection
    and source validity are checked even when no invocation exists. *)
Definition selected_contract (specs : segments) sh action : contract stdio_world :=
  mkContract stdio_world RVoid
    (fun result args => result = CVoid /\ args = [])
    (fun xs m w => xs = [] /\ libc_valid specs m w sh /\
      selected_action specs m w sh action /\ exists full, shutdown_step sh action full)
    (fun _ m w => segment_sources specs sh action m w)
    (fun _ m w => segment_writes specs sh action m w)
    (fun _ m w => segment_releases specs sh action m w)
    (fun _ m w => segment_requests specs sh action m w)
    (fun _ m w => segment_prefix specs sh action m w)
    (fun _ _ _ _ trace ending m' w' => ending = CallReturn [] /\
      exists sh', segment_finish specs sh action trace m' w' sh')
    resource_reason (segment_panics specs sh action).

(** Runtime readiness is never hidden inside a memory-only precondition. *)
Definition selected_ready (specs : segments) s m w sh : Prop :=
  R.ready s m /\ libc_valid specs m w sh.

(** The adapter uses the contract's actual normal post, not a second
    independently supplied action-post or endpoint-readiness hypothesis. *)
Definition boundary (specs : segments) : P.shutdown_boundary :=
  P.mkShutdownBoundary (selected_ready specs) (selected_contract specs)
    (fun _ _ => CVoid) (fun _ _ => []) (fun _ _ => [])
    (fun sh action _ _ _ _ trace _ m' w' sh' => segment_finish specs sh action trace m' w' sh').

(** Admission is independent of invocation existence, but restricted to
    explicitly selected actions. InCallback's logical register rule alone
    cannot authorize an unknown callback. *)
Theorem selected_admits : forall specs s m w sh action full,
  selected_ready specs s m w sh -> selected_action specs m w sh action ->
  shutdown_step sh action full -> P.shutdown_admissible (boundary specs) s m w sh action.
Proof.
  intros specs s m w sh action full [_ Hvalid] Hselect Hstep.
  split; [split; reflexivity|]. split; [reflexivity|].
  split; [exact Hvalid|]. split; [exact Hselect|]. exists full. exact Hstep.
Qed.

(** The born list, prefix and normal post all come from the SAME invocation.
    Runtime readiness follows its effect path; logical validity follows its
    post. Resource endings and unfinished prefixes do not take this rule. *)
Theorem invocation_realizes : forall specs s m w sh action trace s' m' w',
  R.ready s m ->
  E.invoke (selected_contract specs sh action) CVoid [] [] s m w
    trace (CallReturn []) s' m' w' ->
  exists sh', P.realizes (boundary specs) s m w sh action trace s' m' w' sh'.
Proof.
  intros specs s m w sh action trace s' m' w' Hr Hcall.
  pose proof (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall Hr) as [Hr' _].
  inversion Hcall; subst.
  match goal with
  | Hpre : contract_pre _ _ _ _, Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
    destruct Hpre as [_ [Hvalid [Hselect Henabled]]];
    destruct Hpost as [_ [target [Hstep [Htrace Hvalid']]]];
    exists target; eapply P.realize_action; simpl;
      [exact Hstep | split; assumption |
       eapply selected_admits; [split; assumption | exact Hselect | exact Hstep] |
       eassumption | repeat split; assumption | exact Htrace | split; assumption]
  end.
Qed.

(** The body may carry a stronger opaque invariant for its ACTUAL entry
    inventory. This conservative form accepts every well-formed logical
    output queue; queues are obligations, not a claim about physical FILE
    buffers. Native puts preservation of this stronger invariant remains
    part of the trusted contract, not a new runtime axiom. *)
Definition entry_rep (specs : segments) (inventory : list registration)
    (m : mem) (w : stdio_world) : Prop :=
  forall q, stream_wf q -> libc_valid specs m w (mkShutdown Tls 0 inventory [] q).

(** Exact entry readiness survives a finite application run through the
    existing step theorem, without resetting to R.start after startup. *)
Lemma body_ready : forall specs inventory requests st trace st',
  P.M.run (P.registry (entry_rep specs inventory) requests) P.H.hi_genv st trace st' ->
  P.M.state_ready _ st -> P.M.state_ready _ st'.
Proof.
  intros specs inventory requests st trace st' Hrun. induction Hrun; [auto|].
  intros Hr. apply IHHrun. eapply P.M.step_ready; [|exact H|exact Hr]. reflexivity.
Qed.

(** Reached returning puts retains the selected entry's inventory AND its
    callback-validity representation. The former alone would be insufficient.
    This discharges the existing reached-call closure, not native coverage. *)
Theorem reached_puts_closed : forall specs inventory requests start,
  (forall s m s' m' w, R.safepoint s m s' m' -> entry_rep specs inventory m w ->
    stdio_ready m w -> entry_rep specs inventory m' w /\ stdio_ready m' w) ->
  P.body_inv (entry_rep specs inventory) start -> P.M.state_ready _ start ->
  program_pending (P.world_of start) = inventory ->
  P.puts_shutdown_closed (entry_rep specs inventory) requests (boundary specs) start.
Proof.
  intros specs inventory requests start Hstable Hinv Hr Hinitial.
  intros first s m w fuel trace n s' m' w' Hrun Hcall.
  pose proof (P.body_run_inventory _ _ Hstable _ _ _ Hrun Hinv) as Hpending.
  simpl in Hpending. rewrite Hinitial in Hpending.
  destruct (P.C.program_invoke_continuity _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as [Hpending' [_ [Hwf _]]].
  destruct (E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as [born [_ [[Hrep _] _]]].
  split.
  - exact (proj1 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall
      (body_ready _ _ _ _ _ _ Hrun Hr))).
  - rewrite Hpending', Hpending. apply Hrep. exact Hwf.
Qed.

(** A finite chain of actual normal invocations at exact shared snapshots.
    Logical edges name the targets; their validity and runtime readiness
    are extracted from those same calls, not supplied for each endpoint.
    This is not coverage of unfinished, refused or native executions. *)
Inductive normal_run (specs : segments) :
    R.state -> mem -> stdio_world -> shutdown_state -> list event ->
    R.state -> mem -> stdio_world -> shutdown_state -> Prop :=
| normal_refl : forall s m w sh, normal_run specs s m w sh [] s m w sh
| normal_next : forall s m w sh action trace s1 m1 w1 sh1 tail s' m' w' sh',
    shutdown_step sh action sh1 ->
    E.invoke (selected_contract specs sh action) CVoid [] []
      s m w trace (CallReturn []) s1 m1 w1 ->
    normal_run specs s1 m1 w1 sh1 tail s' m' w' sh' ->
    normal_run specs s m w sh (trace ++ tail) s' m' w' sh'.

(** Lift the invocation chain through the existing adapter. Logical target
    uniqueness identifies its extracted endpoint with the named cutpoint. *)
Theorem normal_run_lifts : forall specs s m w sh trace s' m' w' sh' rep requests host,
  normal_run specs s m w sh trace s' m' w' sh' -> R.ready s m ->
  P.run rep requests (boundary specs) host
    (P.ShuttingDown s m w sh) trace (P.ShuttingDown s' m' w' sh') /\
  (stream_wf (shutdown_stdout sh) -> stream_wf (shutdown_stdout sh')).
Proof.
  intros specs s m w sh trace s' m' w' sh' rep requests host Hrun.
  induction Hrun; intros Hr.
  - split; [constructor|auto].
  - destruct (invocation_realizes _ _ _ _ _ _ _ _ _ _ Hr H0) as [target Hreal].
    assert (Htarget : target = sh1).
    { inversion Hreal; subst. eapply shutdown_step_target; eauto. }
    subst target.
    destruct (IHHrun (proj1 (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H0 Hr)))
      as [Htail Hwf].
    split.
    + eapply P.program_next; [apply P.program_shutdown with (action := action); exact Hreal|exact Htail].
    + intros Hq. apply Hwf. destruct H; simpl in *; try exact Hq;
        eapply stream_step_wf; eauto.
Qed.

(** Conditional hi composition under the selected trusted libc contracts:
    exact successful entry, reached returning puts, normal shutdown calls,
    and an explicit completion witness at the resulting handoff. Nothing
    here claims that native execution supplies these witnesses or terminates. *)
Theorem trusted_hi_completion : forall specs inventory requests
    s0 m0 w0 argc argv envp args environment fuel
    first s m w callfuel calltrace n s1 m1 w1 tail s2 m2 w2
    kind status pending consumed q (completed : P.host_boundary),
  (forall s m s' m' w, R.safepoint s m s' m' -> entry_rep specs inventory m w ->
    stdio_ready m w -> entry_rep specs inventory m' w /\ stdio_ready m' w) ->
  A.trusted_entry_contract (entry_rep specs inventory) s0 m0 w0 argc argv envp args environment ->
  program_pending w0 = inventory ->
  P.M.run (P.registry (entry_rep specs inventory) requests) P.H.hi_genv
    (P.M.Running (hi_entry m0 fuel, s0) w0) first (P.M.Running (hi_call m callfuel, s) w) ->
  E.invoke (program_puts (entry_rep specs inventory) requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    s m w calltrace (CallReturn [WInt n]) s1 m1 w1 ->
  normal_run specs s1 m1 (program_stdio w1)
    (mkShutdown Tls 0 (program_pending w1) [] (program_stdout w1)) tail
    s2 m2 w2 (mkShutdown (HandedOff kind) status pending consumed q) ->
  completed s2 m2 w2 (mkShutdown (HandedOff kind) status pending consumed q) ->
  P.run (entry_rep specs inventory) requests (boundary specs) (A.trusted_host_contract completed)
    (P.Application (P.M.Running (hi_entry m0 fuel, s0) w0))
    (first ++ calltrace ++ tail ++ [ProcessExit (process_status status)])
    (P.Finished s2 m2 w2 (mkShutdown (HandedOff kind) status pending consumed q)).
Proof.
  intros specs inventory requests s0 m0 w0 argc argv envp args environment fuel
    first s m w callfuel calltrace n s1 m1 w1 tail s2 m2 w2 kind status pending consumed q completed
    Hstable Hentry Hinitial Hreach Hcall Hshutdown Hcomplete.
  pose proof (A.trusted_entry_body (entry_rep specs inventory) s0 m0 w0
    argc argv envp args environment fuel Hentry) as Hbody.
  destruct Hentry as (_ & Hr & _).
  assert (Hclosed := reached_puts_closed specs inventory requests _ Hstable Hbody Hr Hinitial).
  pose proof (P.returning_puts_shutdown (entry_rep specs inventory) requests (boundary specs)
    (A.trusted_host_contract completed) (P.M.Running (hi_entry m0 fuel, s0) w0)
    first s m w callfuel calltrace n s1 m1 w1
    Hclosed Hreach Hcall) as Hbridge.
  pose proof (E.invoke_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall
    (body_ready _ _ _ _ _ _ Hreach Hr)) as [Hr1 _].
  destruct (normal_run_lifts specs _ _ _ _ _ _ _ _ _ (entry_rep specs inventory) requests
    (A.trusted_host_contract completed) Hshutdown Hr1) as [Hsegments Hwf].
  assert (Hr2 : R.ready s2 m2).
  { exact (P.run_ready _ _ _ _ _ _ _ Hsegments Hr1). }
  assert (Hq : stream_wf q).
  { apply Hwf. exact (proj1 (proj2 (proj2 (P.C.program_invoke_continuity _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)))). }
  replace (first ++ calltrace ++ tail ++ [ProcessExit (process_status status)])
    with ((first ++ calltrace) ++ (tail ++ [ProcessExit (process_status status)]))
    by (repeat rewrite app_assoc; reflexivity).
  eapply P.run_trans; [exact Hbridge|]. eapply P.run_trans; [exact Hsegments|].
  eapply P.program_next with (trace := [ProcessExit (process_status status)]) (tail := []); [|constructor].
  apply A.trusted_host_completion_step; assumption.
Qed.

(** Finite-observation safety is separate from witnessed completion. It
    includes unfinished/resource leaves, promises at most one exit event,
    and retains the shared nonfailure classification for application stops.
    It does not establish native coverage of the outer relation. *)
Theorem trusted_hi_observations : forall specs inventory requests completed
    s m w argc argv envp args environment fuel trace last,
  (forall s m s' m' w, R.safepoint s m s' m' -> entry_rep specs inventory m w ->
    stdio_ready m w -> entry_rep specs inventory m' w /\ stdio_ready m' w) ->
  A.trusted_entry_contract (entry_rep specs inventory) s m w argc argv envp args environment ->
  P.run (entry_rep specs inventory) requests (boundary specs) (A.trusted_host_contract completed)
    (P.Application (P.M.Running (hi_entry m fuel, s) w)) trace last ->
  P.runtime_ready last /\ (P.exit_count trace <= 1)%nat /\
  forall why ms w', last = P.Application (P.M.Stopped why ms w') -> ~ failure_ending why.
Proof.
  intros specs inventory requests completed s m w argc argv envp args environment fuel trace last
    Hstable Hentry Hrun.
  pose proof (A.trusted_entry_body (entry_rep specs inventory) s m w
    argc argv envp args environment fuel Hentry) as Hbody.
  destruct Hentry as (_ & Hr & _). split; [eapply P.run_ready; eauto|]. split.
  - eapply P.at_most_one_exit; eauto.
  - intros why ms w' ->. eapply P.application_stopped_never_panics; eauto. exact Hbody.
Qed.

End Selected.

(** Logical instances exercise admission and cutpoints, not native libc.
    In particular the named callback below is a fixture, not an assertion
    that arbitrary user callbacks belong to the trusted libc boundary. *)
Module SelectedChecks.
Module S := Selected InterpRuntime.
Module P := S.P.

(** One admitted callback retains an actual readable object capability. *)
Definition callback_valid (m : mem) (entry : registration) : Prop :=
  registration_callback entry =
    OnExit (TAtom "fixture_cleanup") (WPtr (mkPtr 3072 (Obj 3072))) /\
  access_res m 3072 (Obj 3072) 8 Read 8 = Some ok.

(** The pending inventory and currently running callback need valid arguments;
    consumed history alone does not retain dead argument objects. *)
Definition callbacks_valid m sh : Prop :=
  Forall (callback_valid m) (shutdown_pending sh) /\
  match shutdown_at sh with InCallback active => callback_valid m active | _ => True end.

(** Selection of a new registration is checked independently of token freshness. *)
Definition action_selected m (action : shutdown_action) : Prop :=
  match action with
  | InvokeCallback entry _ | RegisterCallback entry => callback_valid m entry
  | _ => True
  end.

(** A memory-backed fixture with separate readable argument and writable stdout
    roots. Neither root may be released; no allocations are authorized. *)
Definition specs : S.segments :=
  S.mkSegments
    (fun m w sh => fixture_rep m w /\ callbacks_valid m sh /\
      stream_wf (shutdown_stdout sh) /\ shutdown_unique sh)
    (fun m _ _ action => action_selected m action)
    (fun _ _ _ _ => [stdout_span; mkSpan (mkPtr 3072 (Obj 3072)) 8])
    (fun _ _ _ _ => [stdout_span]) (fun _ _ _ _ => [])
    (fun _ _ _ _ _ _ => False)
    (fun _ _ _ w _ _ _ w' => w' = w)
    (fun _ _ => puts_panic).

(** A nonempty inventory, with a retained capability rather than an integer address. *)
Definition entry : registration :=
  mkRegistration 0 (OnExit (TAtom "fixture_cleanup") (WPtr (mkPtr 3072 (Obj 3072)))).

(** The entry representation is inhabited for every well-formed logical queue. *)
Example nonempty_entry : S.entry_rep specs [entry] hello_mem hello_world.
Proof.
  intros q Hwf. split; [split; reflexivity|]. split.
  - split; [|exact I]. constructor; [split; reflexivity|constructor].
  - split; [exact Hwf|]. repeat constructor. simpl. tauto.
Qed.

(** A fresh token cannot authorize an unknown callback, even where the logical
    register rule permits it. No invocation witness is needed for rejection. *)
Example unknown_callback_rejected : forall s,
  let sh := mkShutdown (InCallback entry) 0 [] [0%nat] stdout_initial in
  let unknown := mkRegistration 1 (AtExit (TAtom "unknown")) in
  ~ P.shutdown_admissible (S.boundary specs) s hello_mem hello_world sh (RegisterCallback unknown).
Proof.
  intros s sh unknown [_ [_ [_ [[Hname _] _]]]]. discriminate Hname.
Qed.

(** Keeping the token and address while losing the retained capability's live
    bounds invalidates the entry, rather than silently removing its behavior. *)
Example expired_argument_rejected : forall s,
  let dead := mkMem (m_bytes hello_mem)
    [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2064 Heap Live;
     mkRegion 3072 3072 Heap Freed] (m_aux hello_mem) in
  ~ P.shutdown_admissible (S.boundary specs) s dead hello_world
    (mkShutdown Handlers 0 [entry] [] stdout_initial) (InvokeCallback entry 0).
Proof.
  intros s dead [_ [_ [_ [[_ Hread] _]]]]. discriminate Hread.
Qed.

(** A selected segment really has no release ownership, even of its readable
    callback argument. Reuse the existing asymmetric footprint regression. *)
Example argument_release_rejected :
  ~ local_effect (S.segment_sources specs (mkShutdown Tls 0 [entry] [] stdout_initial) EmptyTls
      hello_mem hello_world)
    (S.segment_writes specs (mkShutdown Tls 0 [entry] [] stdout_initial) EmptyTls hello_mem hello_world)
    (S.segment_releases specs (mkShutdown Tls 0 [entry] [] stdout_initial) EmptyTls hello_mem hello_world)
    [] hello_mem
    (mkMem (m_bytes hello_mem)
      [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2064 Heap Live;
       mkRegion 3072 3072 Heap Freed] (m_aux hello_mem)).
Proof.
  intros (_ & Hr & _). destruct (Hr 3072 (mkRegion 3072 3072 Heap Freed) eq_refl)
    as (reg & Hreg & [H | ([] & _)]).
  change (Some (mkRegion 3072 3080 Heap Live) = Some reg) in Hreg.
  injection Hreg as <-. discriminate H.
Qed.

(** Read authority for the argument is not write authority for its bytes. *)
Example argument_write_rejected :
  ~ local_effect (S.segment_sources specs (mkShutdown Tls 0 [entry] [] stdout_initial) EmptyTls
      hello_mem hello_world)
    (S.segment_writes specs (mkShutdown Tls 0 [entry] [] stdout_initial) EmptyTls hello_mem hello_world)
    [] [] hello_mem (store_bytes hello_mem 3072 1 7).
Proof.
  intros (_ & _ & Hw & _).
  assert (Hn : ~ write_authority [stdout_span] [] hello_mem 3072).
  { intros [(root & [<- | []] & _ & Hin) | (base & reg & [] & _)];
      unfold span_contains in Hin; simpl in Hin; lia. }
  destruct (Hw _ Hn) as [Hb _]. discriminate Hb.
Qed.

(** An identity-memory fixture completes a selected, independently admissible
    logical action. Its full invocation—not merely a prefix—supplies the post. *)
Lemma fixture_invocation : forall m w sh action sh',
  S.libc_valid specs m w sh -> action_selected m action ->
  shutdown_step sh action sh' -> S.libc_valid specs m w sh' ->
  S.E.invoke (S.selected_contract specs sh action) CVoid [] []
    InterpRuntime.start m w (P.action_events action) (CallReturn [])
    InterpRuntime.start m w.
Proof.
  intros m w sh action sh' Hvalid Hselect Hstep Hvalid'.
  eapply S.E.invoke_normal with (born := []).
  - split; reflexivity.
  - split; [reflexivity|]. split; [exact Hvalid|]. split; [exact Hselect|]. exists sh'. exact Hstep.
  - split; [constructor|reflexivity].
  - split; [reflexivity|]. exists sh'. split; [exact Hstep|]. auto.
  - intros why Hbad. discriminate Hbad.
  - intros values Heq. injection Heq as <-. split; constructor.
  - intros status Hbad. discriminate Hbad.
Qed.

(** The adapter's successful-invocation theorem is inhabited with a nonempty
    admitted inventory and retains the active callback's readable argument. *)
Example nonempty_callback_realizes :
  exists target, P.realizes (S.boundary specs) InterpRuntime.start hello_mem hello_world
    (mkShutdown Handlers 0 [entry] [] stdout_initial) (InvokeCallback entry 0) []
    InterpRuntime.start hello_mem hello_world target.
Proof.
  apply S.invocation_realizes; [apply hello_ready; split; vm_compute; congruence|].
  eapply fixture_invocation with
    (sh' := mkShutdown (InCallback entry) 0 [] [0%nat] stdout_initial).
  - exact (nonempty_entry stdout_initial stdout_initial_wf).
  - split; reflexivity.
  - constructor.
  - split; [split; reflexivity|]. split.
    + split; [constructor|split; reflexivity].
    + split; [exact stdout_initial_wf|]. repeat constructor. simpl. tauto.
Qed.

(** Valid completed cleanup cutpoints retain the same memory and consumed
    inventory while output obligations evolve. No terminal leaf is resumed. *)
Definition cleanup (q : stream_state) : shutdown_state := mkShutdown Cleanup 0 [] [0%nat] q.

(** All well-formed fixture cleanup snapshots satisfy the logical post. *)
Lemma cleanup_valid : forall q, stream_wf q -> S.libc_valid specs hello_mem hello_world (cleanup q).
Proof.
  intros q Hwf. split; [split; reflexivity|]. split; [split; constructor|].
  split; [exact Hwf|]. repeat constructor. simpl. tauto.
Qed.

(** Each completed cutpoint comes from a real contract invocation. *)
Lemma cleanup_realized : forall q action q',
  (forall bytes, action <> Accept bytes) -> stream_step q action q' -> stream_wf q ->
  P.realizes (S.boundary specs) InterpRuntime.start hello_mem hello_world (cleanup q)
    (ShutdownOutput action) [] InterpRuntime.start hello_mem hello_world (cleanup q').
Proof.
  intros q action q' Hnot Hstream Hwf.
  assert (Hstep : shutdown_step (cleanup q) (ShutdownOutput action) (cleanup q'))
    by (apply shutdown_cleanup_output; assumption).
  assert (Hcall := fixture_invocation hello_mem hello_world (cleanup q) (ShutdownOutput action) (cleanup q')
    (cleanup_valid _ Hwf) I Hstep
    (cleanup_valid _ (stream_step_wf _ _ _ Hstream Hwf))).
  assert (Hevents : P.action_events (ShutdownOutput action) = []).
  { destruct action; try reflexivity. exfalso. apply (Hnot bytes). reflexivity. }
  rewrite Hevents in Hcall.
  destruct (S.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as [born Hprefix].
  assert (Hr := hello_ready InterpRuntime.start ltac:(split; vm_compute; congruence)).
  eapply P.realize_action with (born := born).
  - exact Hstep.
  - split; [exact Hr|apply cleanup_valid; exact Hwf].
  - eapply S.selected_admits; [split; [exact Hr|apply cleanup_valid; exact Hwf]|exact I|exact Hstep].
  - exact Hprefix.
  - split; [exact Hstep|]. split; [symmetry; exact Hevents|].
    apply cleanup_valid. eapply stream_step_wf; eauto.
  - symmetry. exact Hevents.
  - split; [exact Hr|]. apply cleanup_valid. eapply stream_step_wf; eauto.
Qed.

(** Delivery, a zero-progress error, and discard are three completed segments
    with exact intermediate queues. Silent observations do not mean delivery
    and discard are the same operation. *)
Example completed_mixed_cleanup : forall rep requests host,
  P.run rep requests (S.boundary specs) host
    (P.ShuttingDown InterpRuntime.start hello_mem hello_world
      (cleanup (mkStream ByteOriented [65; 66] false))) []
    (P.ShuttingDown InterpRuntime.start hello_mem hello_world
      (cleanup (mkStream ByteOriented [] true))).
Proof.
  intros rep requests host.
  eapply P.program_next with (trace := []) (tail := [])
    (mid := P.ShuttingDown InterpRuntime.start hello_mem hello_world
      (cleanup (mkStream ByteOriented [66] false))).
  - apply P.program_shutdown with (action := ShutdownOutput (Deliver [65])).
    apply cleanup_realized; [discriminate|apply (stream_deliver [65] [66] false); discriminate|].
    split; [repeat constructor; lia|reflexivity].
  - eapply P.program_next with (trace := []) (tail := [])
      (mid := P.ShuttingDown InterpRuntime.start hello_mem hello_world
        (cleanup (mkStream ByteOriented [66] true))).
    + apply P.program_shutdown with (action := ShutdownOutput OutputError).
      apply cleanup_realized; [discriminate|constructor|]. split; [repeat constructor; lia|reflexivity].
    + eapply P.program_next with (trace := []) (tail := []).
      * apply P.program_shutdown with (action := ShutdownOutput (Discard [66])).
        apply cleanup_realized; [discriminate|apply (stream_discard [66] [] true); discriminate|].
        split; [repeat constructor; lia|reflexivity].
      * constructor.
Qed.

(** A successful logical entry with argv, environment, the generated hi
    literal, stdout storage and the nonempty admitted callback inventory. *)
Definition completion_memory : mem :=
  startup_store (copy_c_bytes
    (mkMem (m_bytes hello_mem)
      (mkRegion 65552 65560 GlobalData Live :: mkRegion 4096 4112 Heap Live ::
       mkRegion 4200 4208 Heap Live :: m_regions hello_mem) (m_aux hello_mem))
    65552 hello_bytes) 4096 hi_literal.

(** The concrete startup vectors and retained callback argument are genuine
    readable capabilities; a logical queue is not a physical FILE claim. *)
Lemma completion_entry_image :
  startup_at completion_memory 1 entry_argv entry_envp [hello_bytes] [] /\
  P.H.hi_before_call (S.entry_rep specs [entry]) completion_memory hello_world.
Proof.
  split.
  - split; [lia|]. split; [reflexivity|]. split.
    + split; [reflexivity|]. exists hi_literal. split; [vm_compute; repeat split; congruence|].
      split; [vm_compute; repeat split; try congruence; lia|]. vm_compute. repeat split; congruence.
    + vm_compute. repeat split; congruence.
  - split.
    + intros q Hwf. split; [split; reflexivity|]. split.
      * split; [|exact I]. constructor; [split; reflexivity|constructor].
      * split; [exact Hwf|]. repeat constructor. simpl. tauto.
    + split.
      * split; [reflexivity|]. constructor; [|constructor].
        split; [simpl; lia|]. exists 2048, (mkRegion 2048 2064 Heap Live). repeat split; reflexivity.
      * split; [reflexivity|]. vm_compute. repeat split; try congruence; lia.
Qed.

(** Every static object is below the actual entry allocator state, and the
    vector/literal stores do not write above that state. *)
Lemma completion_ready : InterpRuntime.ready InterpRuntime.start completion_memory.
Proof.
  pose proof (hello_ready InterpRuntime.start ltac:(split; vm_compute; congruence)) as [Hpos [Hobj Hbytes]].
  split; [exact Hpos|]. split.
  - intros b reg E. change (object_region b
      (mkRegion 65552 65560 GlobalData Live :: mkRegion 4096 4112 Heap Live ::
       mkRegion 4200 4208 Heap Live :: m_regions hello_mem) = Some reg) in E.
    cbn -[Z.eqb] in E.
    destruct (65552 =? b) eqn:E1.
    + apply Z.eqb_eq in E1. subst b. injection E as <-. simpl. split; [vm_compute; repeat split; congruence|].
      split; [vm_compute; congruence|discriminate].
    + destruct (4096 =? b) eqn:E2.
      * apply Z.eqb_eq in E2. subst b. injection E as <-. simpl. split; [vm_compute; repeat split; congruence|].
        split; [vm_compute; congruence|discriminate].
      * destruct (4200 =? b) eqn:E3.
        -- apply Z.eqb_eq in E3. subst b. injection E as <-. simpl. split; [vm_compute; repeat split; congruence|].
           split; [vm_compute; congruence|discriminate].
        -- apply Hobj. exact E.
  - intros a Ha. destruct (Hbytes a Ha) as [Hb Haux]. change (4294967296 <= a) in Ha.
    assert (Hrange : ((4096 <=? a) && (a <? 4096 + 8)) = false).
    { apply andb_false_iff. right. apply Z.ltb_ge. lia. }
    assert (Hslot : (a =? 4096) = false) by (apply Z.eqb_neq; lia).
    unfold completion_memory, startup_store. cbn -[copy_c_bytes Z.leb Z.ltb Z.eqb Z.add].
    rewrite Hrange, Hslot, copy_c_bytes_aux, copy_c_bytes_outside by (right; simpl; lia).
    exact (conj Hb Haux).
Qed.

(** The actual puts invocation keeps the nonempty inventory and accepts the
    bytes before the later hard exit, without asserting descriptor delivery. *)
Lemma completion_puts :
  S.E.invoke (program_puts (S.entry_rep specs [entry]) fixture_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start completion_memory (mkProgramWorld hello_world stdout_initial [entry])
    [StreamBytes 1 (hello_bytes ++ [10])] (CallReturn [WInt 6])
    InterpRuntime.start completion_memory (mkProgramWorld hello_world ProgramChecks.buffered [entry]).
Proof.
  destruct (proj2 completion_entry_image) as [Hr [Hw Hl]].
  pose proof (P.H.hi_literal_checked completion_memory Hl) as Hstr.
  assert (Hpost : puts_stream_post [WPtr hi_literal] completion_memory stdout_initial
    [StreamBytes 1 (hello_bytes ++ [10])] (CallReturn [WInt 6]) ProgramChecks.buffered).
  { exists hi_literal, hello_bytes, [Accept (hello_bytes ++ [10])], 6.
    split; [reflexivity|]. split; [exact Hstr|]. split;
      [exact puts_buffered_acceptance|split; reflexivity]. }
  eapply S.E.invoke_normal with (born := []).
  - split; [right; exists (TAtom "v1"); reflexivity|]. exists (Tmp (TAtom "v0")). reflexivity.
  - split.
    + split; [exact Hr|]. split; [exact Hw|]. exists hi_literal, hello_bytes. auto.
    + split; [split; [exact stdout_initial_wf|repeat constructor; simpl; tauto]|discriminate].
  - split; [constructor|]. split.
    + split; [exact Hr|]. split; [exact Hw|]. split.
      * apply stdio_delegates_refl; [reflexivity|exact (proj2 Hw)].
      * right. exists hi_literal, hello_bytes, (hello_bytes ++ [10]), ([] : list Z).
        split; [reflexivity|]. split; [exact Hstr|]. split; reflexivity.
    + split; [reflexivity|]. eapply P.C.program_post_prefix; exact Hpost.
  - split; [|exact Hpost].
    exact (protocol_puts_post hello_bytes stdout_initial [Accept (hello_bytes ++ [10])] 6 ProgramChecks.buffered
      completion_memory hi_literal hello_world [] completion_memory hello_world
      puts_buffered_acceptance Hstr Hw).
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt 6). split; reflexivity.
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Three genuine logical cutpoints: TLS, callback entry, then the callback's
    hard exit. Tokens are consumed once, and accepted bytes stay outstanding. *)
Lemma completion_shutdown :
  S.normal_run specs InterpRuntime.start completion_memory hello_world
    (mkShutdown Tls 0 [entry] [] ProgramChecks.buffered) []
    InterpRuntime.start completion_memory hello_world
    (mkShutdown (HandedOff HardExit) 258 [] [0%nat] ProgramChecks.buffered).
Proof.
  assert (Hwf : stream_wf ProgramChecks.buffered) by (split; [repeat constructor; lia|reflexivity]).
  assert (Hvalid : forall phase pending consumed,
    callbacks_valid completion_memory (mkShutdown phase 0 pending consumed ProgramChecks.buffered) ->
    shutdown_unique (mkShutdown phase 0 pending consumed ProgramChecks.buffered) ->
    S.libc_valid specs completion_memory hello_world
      (mkShutdown phase 0 pending consumed ProgramChecks.buffered)).
  { intros phase pending consumed Hcallbacks Hunique. split; [split; reflexivity|].
    split; [exact Hcallbacks|]. split; assumption. }
  assert (Htls := (proj1 (proj2 completion_entry_image)) ProgramChecks.buffered Hwf).
  assert (Hhandlers : S.libc_valid specs completion_memory hello_world
    (mkShutdown Handlers 0 [entry] [] ProgramChecks.buffered)).
  { apply Hvalid; [split; [constructor; [split; reflexivity|constructor]|exact I]|].
    repeat constructor. simpl. tauto. }
  assert (Hactive : S.libc_valid specs completion_memory hello_world
    (mkShutdown (InCallback entry) 0 [] [0%nat] ProgramChecks.buffered)).
  { apply Hvalid; [split; [constructor|split; reflexivity]|]. repeat constructor. simpl. tauto. }
  assert (Hhard : S.libc_valid specs completion_memory hello_world
    (mkShutdown (HandedOff HardExit) 258 [] [0%nat] ProgramChecks.buffered)).
  { split; [split; reflexivity|]. split; [split; constructor|]. split; [exact Hwf|].
    repeat constructor. simpl. tauto. }
  eapply S.normal_next with (action := EmptyTls) (trace := []) (tail := [])
    (sh1 := mkShutdown Handlers 0 [entry] [] ProgramChecks.buffered).
  - constructor.
  - eapply fixture_invocation; [exact Htls|exact I|constructor|exact Hhandlers].
  - eapply S.normal_next with (action := InvokeCallback entry 0) (trace := []) (tail := [])
      (sh1 := mkShutdown (InCallback entry) 0 [] [0%nat] ProgramChecks.buffered).
    + constructor.
    + eapply fixture_invocation; [exact Hhandlers|split; reflexivity|constructor|exact Hactive].
    + eapply S.normal_next with (action := Handoff HardExit 258) (trace := []) (tail := []).
      * constructor. intros kind Hbad. discriminate.
      * eapply fixture_invocation; [exact Hactive|exact I|constructor; intros; discriminate|exact Hhard].
      * constructor.
Qed.

(** Host completion is witnessed only at this full handoff snapshot. *)
Definition completion_host : P.host_boundary :=
  fun s m w sh => s = InterpRuntime.start /\ m = completion_memory /\ w = hello_world /\
    sh = mkShutdown (HandedOff HardExit) 258 [] [0%nat] ProgramChecks.buffered.

(** A different status or an invented empty queue does not match the witness. *)
Example completion_host_rejects_changed_snapshot :
  ~ completion_host InterpRuntime.start completion_memory hello_world
    (mkShutdown (HandedOff HardExit) 0 [] [0%nat] ProgramChecks.buffered) /\
  ~ completion_host InterpRuntime.start completion_memory hello_world
    (mkShutdown (HandedOff HardExit) 258 [] [0%nat] (mkStream ByteOriented [] false)).
Proof. split; intros (_ & _ & _ & Hsnapshot); discriminate Hsnapshot. Qed.

(** This full logical path uses the composition theorem, an actual returning
    puts, nonempty callback admission, and a supplied exact host witness.
    The observed exit is 258 mod 256 = 2, not main's original zero status. *)
Example nonempty_hi_to_hard_completion :
  P.run (S.entry_rep specs [entry]) fixture_requests (S.boundary specs)
    (S.A.trusted_host_contract completion_host)
    (P.Application (P.M.Running (hi_entry completion_memory 10, InterpRuntime.start)
      (mkProgramWorld hello_world stdout_initial [entry])))
    [StreamBytes 1 (hello_bytes ++ [10]); ProcessExit 2]
    (P.Finished InterpRuntime.start completion_memory hello_world
      (mkShutdown (HandedOff HardExit) 258 [] [0%nat] ProgramChecks.buffered)).
Proof.
  replace ([StreamBytes 1 (hello_bytes ++ [10]); ProcessExit 2]) with
    ([] ++ [StreamBytes 1 (hello_bytes ++ [10])] ++ [] ++ [ProcessExit (process_status 258)])
    by reflexivity.
  eapply S.trusted_hi_completion with (inventory := [entry]) (argc := 1)
    (argv := entry_argv) (envp := entry_envp) (args := [hello_bytes]) (environment := []) (n := 6).
  - apply HiChecks.interpreter_stdio_stable.
  - split; [exact (proj1 completion_entry_image)|]. split; [exact completion_ready|].
    split; [exact (proj2 completion_entry_image)|]. split.
    + split; [exact stdout_initial_wf|repeat constructor; simpl; tauto].
    + discriminate.
  - reflexivity.
  - apply P.H.hi_reaches_call. lia.
  - exact completion_puts.
  - exact completion_shutdown.
  - repeat split; reflexivity.
Qed.

End SelectedChecks.

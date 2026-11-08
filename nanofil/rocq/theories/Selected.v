(** Selected libc lifecycle segments, over the existing external-call
    effect discipline. Admission precedes behavior existence. Successful
    invocations supply their own logical endpoint and allocator readiness;
    neither is inferred from an unfinished prefix. Native satisfaction and
    coverage remain trusted obligations, not theorems of this adapter. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Identity
  ExternalCalls Stdio Shutdown Hi Composition HiArtifact Program.
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
Lemma fixture_invocation : forall sh action sh',
  S.libc_valid specs hello_mem hello_world sh -> action_selected hello_mem action ->
  shutdown_step sh action sh' -> S.libc_valid specs hello_mem hello_world sh' ->
  S.E.invoke (S.selected_contract specs sh action) CVoid [] []
    InterpRuntime.start hello_mem hello_world (P.action_events action) (CallReturn [])
    InterpRuntime.start hello_mem hello_world.
Proof.
  intros sh action sh' Hvalid Hselect Hstep Hvalid'.
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
  assert (Hcall := fixture_invocation (cleanup q) (ShutdownOutput action) (cleanup q')
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

End SelectedChecks.

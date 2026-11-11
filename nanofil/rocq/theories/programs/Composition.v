(** A trusted puts contract with one continuous logical stdout and
    registration inventory. The additional guarantees are libc obligations,
    not a FILE implementation or a native coverage proof. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  ExternalCalls Stdio Shutdown ExternalMachine Hi.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Keep the capability-backed stdio world, output obligations and exit
    registrations together; shutdown must not choose a new stdout state. *)
Record program_world : Type := mkProgramWorld {
  program_stdio : stdio_world;
  program_stdout : stream_state;
  program_pending : list registration
}.

(** Entry supplies well-formed logical output and distinct registration instances. *)
Definition program_world_wf (w : program_world) : Prop :=
  stream_wf (program_stdout w) /\
  NoDup (map registration_token (program_pending w)).

(** A prefix has either no acceptance observation or one cumulative summary.
    An empty trace must not hide accepted bytes. It is not an incremental
    sequence that can be concatenated with another cumulative summary. *)
Definition prefix_observation (trace : list event) (actions : list stream_action) : Prop :=
  (trace = [] /\ accepted actions = []) \/ trace = puts_observation actions.

(** Original argument memory fixes this call's source string. Its finite
    stream evolution may settle old output but accepts only a prefix of
    this string and newline. No eventual return or resumability is asserted. *)
Definition puts_stream_prefix (xs : list word) (m : mem)
    (q : stream_state) (trace : list event) (q' : stream_state) : Prop :=
  exists p bytes actions tail,
    xs = [WPtr p] /\ c_string m p bytes /\
    stream_run q actions q' /\ bytes ++ [10] = accepted actions ++ tail /\
    prefix_observation trace actions.

(** Returning puts couples the exact before/after stdout states to its
    result. The ordinary contract still owns memory authority and ABI. *)
Definition puts_stream_post (xs : list word) (m : mem)
    (q : stream_state) (trace : list event) (ending : call_end)
    (q' : stream_state) : Prop :=
  exists p bytes actions result,
    xs = [WPtr p] /\ c_string m p bytes /\
    puts_protocol bytes q actions result q' /\
    trace = puts_observation actions /\ ending = CallReturn [WInt result].

(** This strengthened contract retains puts' original capabilities, memory
    footprints and requests. Trusted prefix guarantees connect every normal,
    resource or unfinished endpoint to stdout and preserve registrations. *)
Definition program_puts (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
    : contract program_world :=
  mkContract program_world (RClass W) puts_abi
    (fun xs m w => puts_pre rep xs m (program_stdio w) /\
      program_world_wf w /\ orientation (program_stdout w) <> WideOriented)
    (fun _ _ w => stdio_roots (program_stdio w))
    (fun _ _ w => stdio_roots (program_stdio w)) (fun _ _ _ => [])
    (fun xs m w => requests xs m (program_stdio w))
    (fun xs m w born trace m' w' =>
      puts_prefix rep xs m (program_stdio w) born trace m' (program_stdio w') /\
      program_pending w' = program_pending w /\
      puts_stream_prefix xs m (program_stdout w) trace (program_stdout w'))
    (fun xs m w born trace ending m' w' =>
      puts_post xs m (program_stdio w) born trace ending m' (program_stdio w') /\
      puts_stream_post xs m (program_stdout w) trace ending (program_stdout w'))
    resource_reason puts_panic.

(** Every observed prefix carries an exact accounting witness, including
    prefixes which block or end for lack of resources. *)
Lemma puts_stream_prefix_accounting : forall xs m q trace q',
  puts_stream_prefix xs m q trace q' ->
  exists actions, stream_run q actions q' /\ prefix_observation trace actions /\
    outstanding q ++ accepted actions = resolved actions ++ outstanding q'.
Proof.
  intros xs m q trace q' (p & bytes & actions & tail & Hx & Hstr & Hrun & Hb & Hobs).
  exists actions. repeat split; auto. apply stream_accounting. exact Hrun.
Qed.

(** Stream well-formedness is derived from actual protocol steps, not
    stipulated independently at a prefix endpoint. *)
Lemma puts_stream_prefix_wf : forall xs m q trace q',
  puts_stream_prefix xs m q trace q' -> stream_wf q -> stream_wf q'.
Proof.
  intros xs m q trace q' (p & bytes & actions & tail & _ & _ & Hrun & _) Hwf.
  eapply stream_run_wf; eauto.
Qed.

(** No stream action turns a nonwide stream into a wide one. *)
Lemma stream_run_nonwide : forall q actions q',
  stream_run q actions q' -> orientation q <> WideOriented ->
  orientation q' <> WideOriented.
Proof.
  intros q actions q' H. induction H; [auto|]. intros Ho.
  apply IHstream_run. destruct H; simpl; discriminate.
Qed.

(** Prefix output errors remain set; normal completion is not required. *)
Lemma puts_stream_prefix_error : forall xs m q trace q',
  puts_stream_prefix xs m q trace q' ->
  stream_error q = true -> stream_error q' = true.
Proof.
  intros xs m q trace q' (p & bytes & actions & tail & _ & _ & Hrun & _) Herr.
  eapply stream_error_sticky; eauto.
Qed.

(** Neither normal nor unfinished puts prefixes can report process exit. *)
Lemma puts_stream_prefix_exit_free : forall xs m q trace q' status,
  puts_stream_prefix xs m q trace q' -> ~ In (ProcessExit status) trace.
Proof.
  intros xs m q trace q' status (p & bytes & actions & tail & _ & _ & _ & _ & Hobs).
  destruct Hobs as [[-> _]| ->]; simpl; intuition discriminate.
Qed.

(** The strengthened contract is conservative over the existing memory/effect
    boundary: forgetting logical output and registrations gives ordinary puts. *)
Module Composition (R : Runtime).
Module H := Hi R.
Module M := H.M.
Module E := M.E.

(** Projection does not re-run the call or change its exact effect path. *)
Theorem program_prefix_projects : forall rep requests xs s m w born trace s' m' w',
  E.prefix (program_puts rep requests) xs s m w born trace s' m' w' ->
  E.prefix (puts_contract rep requests) xs s m (program_stdio w)
    born trace s' m' (program_stdio w').
Proof.
  intros rep requests xs s m w born trace s' m' w' [He [Hp _]]. split; assumption.
Qed.

(** Raw prefixes do not include contract preconditions: entry well-formedness
    is an explicit premise, even when the call never returns. *)
Theorem program_prefix_continuity : forall rep requests xs s m w born trace s' m' w',
  E.prefix (program_puts rep requests) xs s m w born trace s' m' w' ->
  program_world_wf w ->
  program_pending w' = program_pending w /\
  puts_stream_prefix xs m (program_stdout w) trace (program_stdout w') /\
  program_world_wf w'.
Proof.
  intros rep requests xs s m w born trace s' m' w' [He [Hp [Hpending Hstream]]] [Hwf Hnd].
  split; [exact Hpending|]. split; [exact Hstream|]. split.
  - eapply puts_stream_prefix_wf; eauto.
  - rewrite Hpending. exact Hnd.
Qed.

(** Every strengthened completion is an existing puts completion; the
    additional world cannot mint capabilities or escape resource checks. *)
Theorem program_invoke_projects : forall rep requests r args xs s m w trace ending s' m' w',
  E.invoke (program_puts rep requests) r args xs s m w trace ending s' m' w' ->
  E.invoke (puts_contract rep requests) r args xs s m (program_stdio w)
    trace ending s' m' (program_stdio w').
Proof.
  intros rep requests r args xs s m w trace ending s' m' w' H.
  destruct H as [trace ending s' m' w' born Ha [Hpre _] Hp [Hpost _] Hnot Hret Hexit
    |why trace s' m' w' born Ha [Hpre _] Hp Hfailure Hresource].
  - eapply E.invoke_normal with (born := born); eauto using program_prefix_projects.
  - eapply E.invoke_resource with (born := born); eauto using program_prefix_projects.
Qed.

(** Normal and resource completions preserve the inventory and provide the
    same stdout continuity witness as an unfinished call observation. *)
Theorem program_invoke_continuity : forall rep requests r args xs s m w trace ending s' m' w',
  E.invoke (program_puts rep requests) r args xs s m w trace ending s' m' w' ->
  program_pending w' = program_pending w /\
  puts_stream_prefix xs m (program_stdout w) trace (program_stdout w') /\
  program_world_wf w'.
Proof.
  intros rep requests r args xs s m w trace ending s' m' w' H.
  destruct H.
  all: eapply program_prefix_continuity; [eassumption|exact (proj1 (proj2 H0))].
Qed.

(** A normal protocol execution is also a finite stream prefix, using
    the same actions, source memory, observations and endpoint. *)
Lemma program_post_prefix : forall xs m q trace ending q',
  puts_stream_post xs m q trace ending q' ->
  puts_stream_prefix xs m q trace q'.
Proof.
  intros xs m q trace ending q' (p & bytes & actions & result & Hx & Hstr &
    [Ho [Hrun [tail [Hb Hr]]]] & Htrace & Hend).
  exists p, bytes, actions, tail. split; [exact Hx|]. split; [exact Hstr|].
  split; [exact Hrun|]. split; [exact Hb|]. right. exact Htrace.
Qed.

(** Existing memory/effect evidence can be enriched by an explicit protocol
    witness; this does not conjure a native puts execution from stream actions. *)
Theorem program_return_lift : forall rep requests r args xs s m w trace values s' m' w',
  E.invoke (puts_contract rep requests) r args xs s m (program_stdio w)
    trace (CallReturn values) s' m' (program_stdio w') ->
  program_world_wf w -> orientation (program_stdout w) <> WideOriented ->
  program_pending w' = program_pending w ->
  puts_stream_post xs m (program_stdout w) trace (CallReturn values) (program_stdout w') ->
  E.invoke (program_puts rep requests) r args xs s m w trace (CallReturn values) s' m' w'.
Proof.
  intros rep requests r args xs s m w trace values s' m' w' H Hwf Ho Hpending Hstream.
  inversion H; subst.
  eapply E.invoke_normal; [eassumption| | | |eassumption|eassumption|eassumption].
  - split; [eassumption|]. auto.
  - split; [exact (proj1 H2)|]. split; [exact (proj2 H2)|].
    split; [exact Hpending|]. eapply program_post_prefix; eauto.
  - split; eassumption.
Qed.

End Composition.

(** ## Inhabited protocol boundaries, not native coverage *)
Module CompositionChecks.
Module C := Composition InterpRuntime.

(** The same real main literal and libc root as the body checks, with one
    actual registration instance retained across puts. *)
Definition world (q : stream_state) : program_world :=
  mkProgramWorld hello_world q [exit_first].

(** This entry inventory has distinct tokens and the initial stdout is ready. *)
Lemma initial_world_wf : program_world_wf (world stdout_initial).
Proof. split; [exact stdout_initial_wf|]. repeat constructor; simpl; tauto. Qed.

(** A returning EOF can leave exactly its accepted prefix outstanding. *)
Lemma eof_buffered : forall acc tail,
  hello_bytes ++ [10] = acc ++ tail -> Forall (fun b => 0 <= b < 256) acc ->
  C.E.invoke (program_puts fixture_rep fixture_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start HiChecks.memory (world stdout_initial) [StreamBytes 1 acc]
    (CallReturn [WInt (2 ^ 32 - 1)]) InterpRuntime.start HiChecks.memory
    (world (mkStream ByteOriented acc false)).
Proof.
  intros acc tail Hb Hbytes.
  destruct HiChecks.entry_pre as [Hr [Hw Hl]].
  pose proof (C.H.hi_literal_checked HiChecks.memory Hl) as Hstr.
  apply C.program_return_lift.
  - eapply C.E.invoke_normal with (born := []).
    + split; [right; exists (TAtom "v1"); reflexivity|]. exists (Tmp (TAtom "v0")). reflexivity.
    + split; [exact Hr|]. split; [exact Hw|]. exists hi_literal, hello_bytes. auto.
    + split; [constructor|]. split; [exact Hr|]. split; [exact Hw|]. split.
      * apply stdio_delegates_refl; [reflexivity|exact (proj2 Hw)].
      * right. exists hi_literal, hello_bytes, acc, tail. repeat split; auto.
    + exists hi_literal, hello_bytes, acc, tail, (2 ^ 32 - 1).
      split; [reflexivity|]. split; [exact Hstr|]. split; [exact Hb|].
      split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|exact Hw].
    + intros why Hbad. discriminate.
    + intros values Heq. injection Heq as <-. split.
      * exists (WInt (2 ^ 32 - 1)). split; reflexivity.
      * constructor; [exact I|constructor].
    + intros status Hbad. discriminate.
  - exact initial_world_wf.
  - discriminate.
  - reflexivity.
  - exists hi_literal, hello_bytes, [Accept acc], (2 ^ 32 - 1).
    split; [reflexivity|]. split.
    + apply HiChecks.H.hi_literal_checked. exact (proj2 (proj2 HiChecks.entry_pre)).
    + split.
      * split; [discriminate|]. split.
        -- eapply stream_next; [apply stream_accept; [discriminate|exact Hbytes]|constructor].
        -- exists tail. split; [simpl; rewrite app_nil_r; exact Hb|]. right. reflexivity.
      * split; [|reflexivity]. unfold puts_observation, accepted. simpl. rewrite app_nil_r. reflexivity.
Qed.

(** Partial acceptance is not dropped or replaced by an unrelated shutdown state. *)
Example partial_eof_keeps_exact_output :
  C.E.invoke (program_puts fixture_rep fixture_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start HiChecks.memory (world stdout_initial) [StreamBytes 1 [104; 101]]
    (CallReturn [WInt (2 ^ 32 - 1)]) InterpRuntime.start HiChecks.memory
    (world (mkStream ByteOriented [104; 101] false)).
Proof. apply (eof_buffered _ [108; 108; 111; 10]); [reflexivity|repeat constructor; lia]. Qed.

(** EOF permits both no acceptance and acceptance of the complete newline. *)
Example eof_empty_and_full :
  (exists w', C.E.invoke (program_puts fixture_rep fixture_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start HiChecks.memory (world stdout_initial) [StreamBytes 1 []]
    (CallReturn [WInt (2 ^ 32 - 1)]) InterpRuntime.start HiChecks.memory w') /\
  (exists w', C.E.invoke (program_puts fixture_rep fixture_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start HiChecks.memory (world stdout_initial) [StreamBytes 1 (hello_bytes ++ [10])]
    (CallReturn [WInt (2 ^ 32 - 1)]) InterpRuntime.start HiChecks.memory w').
Proof.
  split; eexists.
  - apply (eof_buffered _ (hello_bytes ++ [10])); [reflexivity|constructor].
  - apply (eof_buffered _ []); [reflexivity|repeat constructor; lia].
Qed.

(** Oversize refusal remains a resource outcome, not a normal puts result. *)
Definition big_requests (_ : list word) (_ : mem) (_ : stdio_world) (align size : Z) : Prop :=
  align = 16 /\ size = 2 ^ 48.

(** This is an actual completed resource invocation AFTER partial acceptance.
    It retains output and the registration list without invoking normal exit. *)
Example resource_after_partial_acceptance :
  C.E.invoke (program_puts fixture_rep big_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start HiChecks.memory (world stdout_initial) [StreamBytes 1 [104; 101]]
    (CallResource TooBig) InterpRuntime.start HiChecks.memory
    (world (mkStream ByteOriented [104; 101] false)).
Proof.
  destruct HiChecks.entry_pre as [Hr [Hw Hl]].
  pose proof (C.H.hi_literal_checked HiChecks.memory Hl) as Hstr.
  eapply C.E.invoke_resource with (born := []).
  - split; [right; exists (TAtom "v1"); reflexivity|]. exists (Tmp (TAtom "v0")). reflexivity.
  - split.
    + split; [exact Hr|]. split; [exact Hw|]. exists hi_literal, hello_bytes. auto.
    + split; [exact initial_world_wf|discriminate].
  - split; [constructor|]. split.
    + split; [exact Hr|]. split; [exact Hw|]. split.
      * apply stdio_delegates_refl; [reflexivity|exact (proj2 Hw)].
      * right. exists hi_literal, hello_bytes, ([104; 101]), ([108; 108; 111; 10]).
        split; [reflexivity|]. split; [exact Hstr|]. split; reflexivity.
    + split; [reflexivity|]. exists hi_literal, hello_bytes, ([Accept [104; 101]]), ([108; 108; 111; 10]).
      split; [reflexivity|]. split; [exact Hstr|]. split.
      * eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|constructor].
      * split; [reflexivity|]. right. reflexivity.
  - apply C.E.failure_big with (align := 16) (size := 2 ^ 48); [split; reflexivity|].
    unfold max_allocation_size. lia.
  - right. reflexivity.
Qed.

(** Empty observations can deliver OLD pending bytes without new acceptance. *)
Example silent_prefix_can_deliver :
  puts_stream_prefix [WPtr hi_literal] HiChecks.memory
    (mkStream ByteOriented [65; 66] false) [] (mkStream ByteOriented [] false).
Proof.
  exists hi_literal, hello_bytes, ([Deliver [65; 66]]), (hello_bytes ++ [10]).
  split; [reflexivity|]. split.
  - apply HiChecks.H.hi_literal_checked. exact (proj2 (proj2 HiChecks.entry_pre)).
  - split.
    + eapply stream_next; [apply (stream_deliver [65; 66] [] false); discriminate|constructor].
    + split; [reflexivity|]. left. split; reflexivity.
Qed.

(** A silent summary cannot hide any newly accepted bytes. *)
Example silent_acceptance_rejected : ~ prefix_observation [] [Accept [104]].
Proof. intros [[_ Hb]|Ht]; discriminate. Qed.

(** Changing the inventory violates the strengthened prefix even if all
    memory and byte observations could satisfy the ordinary contract. *)
Example inventory_mutation_rejected : forall born trace m' q,
  ~ contract_prefix (program_puts fixture_rep fixture_requests)
    [WPtr hi_literal] HiChecks.memory (world stdout_initial) born trace m'
    (mkProgramWorld hello_world q []).
Proof. intros born trace m' q [_ [Hpending _]]. discriminate Hpending. Qed.

(** A wide-oriented stream cannot enter this strengthened contract, even EOF. *)
Example wide_entry_rejected :
  ~ contract_pre (program_puts fixture_rep fixture_requests) [WPtr hi_literal]
    HiChecks.memory (world (mkStream WideOriented [] false)).
Proof. intros [_ [_ Hwide]]. apply Hwide. reflexivity. Qed.

(** Endpoint equality does not identify a unique delivery history: when
    error is already set, delivery and error-discard can end identically. *)
Example histories_not_unique :
  stream_run (mkStream ByteOriented [65] true) [Deliver [65]] (mkStream ByteOriented [] true) /\
  stream_run (mkStream ByteOriented [65] true) [Discard [65]] (mkStream ByteOriented [] true).
Proof.
  split; eapply stream_next; [apply (stream_deliver [65] [] true); discriminate|constructor|
    apply (stream_discard [65] [] true); discriminate|constructor].
Qed.

End CompositionChecks.

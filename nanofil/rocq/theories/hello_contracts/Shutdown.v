(** Serialized shutdown of the selected user-glibc: callbacks, stdout
    obligations and a soft or hard host-exit handoff. This is a logical
    lifecycle, not native callback execution or host termination.
    In particular, a handoff does not itself emit [ProcessExit]. *)

From Stdlib Require Import ZArith List Bool Lia Sorting.Permutation.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics ExternalCalls LibcCalls Startup Stdio.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Callback calling conventions retain their argument, not just its address. *)
Inductive exit_callback : Type :=
| AtExit (function : name)
| OnExit (function : name) (argument : word)
| CxaExit (function : name) (argument : word).

(** A registration instance: registering one function twice gives two tokens. *)
Record registration : Type := mkRegistration {
  registration_token : nat;
  registration_callback : exit_callback
}.

(** Soft handoff calls host exit; hard handoff calls host _Exit. *)
Inductive handoff_kind : Type := SoftExit | HardExit.

(** The selected TLS destructor loop is empty. Done is derived from phase:
    registration has closed in Cleanup and cannot reopen. *)
Inductive shutdown_phase : Type :=
| Tls | Handlers | InCallback (active : registration) | Cleanup
| HandedOff (kind : handoff_kind).

(** Pending registrations are newest first; consumed tokens retain history
    even when a recursive exit abandons the active callback. *)
Record shutdown_state : Type := mkShutdown {
  shutdown_at : shutdown_phase;
  shutdown_status : Z;
  shutdown_pending : list registration;
  shutdown_consumed : list nat;
  shutdown_stdout : stream_state
}.

(** Protocol actions are not arbitrary callback traces or native events. *)
Inductive shutdown_action : Type :=
| EmptyTls | InvokeCallback (entry : registration) (status : Z)
| ReturnCallback | RegisterCallback (entry : registration) | RecursiveExit (status : Z)
| ShutdownOutput (action : stream_action) | StartCleanup
| Handoff (kind : handoff_kind) (status : Z).

(** The protocol permits finite unfinished callbacks/cleanup. Successful
    registration is conditional, and fresh tokens cannot reuse an instance.
    Cleanup only projects settlement/error, not all of native _IO_cleanup.
    Hard exit does not flush or discard outstanding output. *)
Inductive shutdown_step : shutdown_state -> shutdown_action -> shutdown_state -> Prop :=
| shutdown_tls : forall status pending consumed q,
    shutdown_step (mkShutdown Tls status pending consumed q) EmptyTls
      (mkShutdown Handlers status pending consumed q)
| shutdown_invoke : forall status entry pending consumed q,
    shutdown_step (mkShutdown Handlers status (entry :: pending) consumed q)
      (InvokeCallback entry status)
      (mkShutdown (InCallback entry) status pending
        (consumed ++ [registration_token entry]) q)
| shutdown_return : forall status entry pending consumed q,
    shutdown_step (mkShutdown (InCallback entry) status pending consumed q) ReturnCallback
      (mkShutdown Handlers status pending consumed q)
| shutdown_register : forall status active entry pending consumed q,
    ~ In (registration_token entry) (consumed ++ map registration_token pending) ->
    shutdown_step (mkShutdown (InCallback active) status pending consumed q)
      (RegisterCallback entry)
      (mkShutdown (InCallback active) status (entry :: pending) consumed q)
| shutdown_recursive : forall status active pending consumed q status',
    shutdown_step (mkShutdown (InCallback active) status pending consumed q) (RecursiveExit status')
      (mkShutdown Tls status' pending consumed q)
| shutdown_callback_output : forall status active pending consumed q action q',
    stream_step q action q' ->
    shutdown_step (mkShutdown (InCallback active) status pending consumed q)
      (ShutdownOutput action) (mkShutdown (InCallback active) status pending consumed q')
| shutdown_cleanup : forall status consumed q,
    shutdown_step (mkShutdown Handlers status [] consumed q) StartCleanup
      (mkShutdown Cleanup status [] consumed q)
| shutdown_cleanup_output : forall status consumed q action q',
    (forall bytes, action <> Accept bytes) -> stream_step q action q' ->
    shutdown_step (mkShutdown Cleanup status [] consumed q) (ShutdownOutput action)
      (mkShutdown Cleanup status [] consumed q')
| shutdown_soft : forall status consumed q,
    shutdown_step (mkShutdown Cleanup status [] consumed q) (Handoff SoftExit status)
      (mkShutdown (HandedOff SoftExit) status [] consumed q)
| shutdown_hard : forall s status,
    (forall kind, shutdown_at s <> HandedOff kind) ->
    shutdown_step s (Handoff HardExit status)
      (mkShutdown (HandedOff HardExit) status (shutdown_pending s)
        (shutdown_consumed s) (shutdown_stdout s)).

(** A source and selected action fix the logical endpoint. This lets a
    caller name its next cutpoint without supplying endpoint validity again. *)
Lemma shutdown_step_target : forall sh action left right,
  shutdown_step sh action left -> shutdown_step sh action right -> left = right.
Proof.
  intros sh action left right Hl Hr. inversion Hl; subst; inversion Hr; subst; try reflexivity.
  all: match goal with H1 : stream_step ?q ?a ?q1, H2 : stream_step ?q ?a ?q2 |- _ =>
    assert (q1 = q2) by (eapply stream_step_target; eauto); subst; reflexivity end.
Qed.

(** A finite shutdown prefix; no rule promises eventual completion. *)
Inductive shutdown_run : shutdown_state -> list shutdown_action -> shutdown_state -> Prop :=
| shutdown_refl : forall s, shutdown_run s [] s
| shutdown_next : forall s action s1 actions s',
    shutdown_step s action s1 -> shutdown_run s1 actions s' ->
    shutdown_run s (action :: actions) s'.

(** All pending and consumed registration-instance tokens are distinct. *)
Definition shutdown_unique (s : shutdown_state) : Prop :=
  NoDup (shutdown_consumed s ++ map registration_token (shutdown_pending s)).

(** Moving a fresh registration token into the pending stack preserves uniqueness. *)
Lemma shutdown_unique_insert : forall (before after : list nat) token,
  NoDup (before ++ after) -> ~ In token (before ++ after) ->
  NoDup (before ++ token :: after).
Proof.
  intros before after token Hnd Hfresh.
  apply (Permutation_NoDup (Permutation_middle before after token)).
  constructor; assumption.
Qed.

(** Pop-before-call and fresh successful registration preserve instance uniqueness. *)
Lemma shutdown_step_unique : forall s action s',
  shutdown_step s action s' -> shutdown_unique s -> shutdown_unique s'.
Proof.
  intros s action s' H Hunique. destruct H; unfold shutdown_unique in *; simpl in *; auto.
  - rewrite <- app_assoc. exact Hunique.
  - apply shutdown_unique_insert; assumption.
Qed.

(** No registration instance is invoked twice, even across recursive exit. *)
Theorem shutdown_run_unique : forall s actions s',
  shutdown_run s actions s' -> shutdown_unique s -> shutdown_unique s'.
Proof.
  intros s actions s' H. induction H; [auto|]. intros Hu.
  apply IHshutdown_run. eapply shutdown_step_unique; eauto.
Qed.

(** Tokens invoked by one action; registering and returning invoke none. *)
Definition invoked_by (action : shutdown_action) : list nat :=
  match action with InvokeCallback entry _ => [registration_token entry] | _ => [] end.

(** Consumed history grows by exactly the invoked instances, in invocation order. *)
Lemma shutdown_step_consumed : forall s action s',
  shutdown_step s action s' ->
  shutdown_consumed s' = shutdown_consumed s ++ invoked_by action.
Proof.
  intros s action s' H. destruct H; simpl; try reflexivity; symmetry; apply app_nil_r.
Qed.

(** The history accounts for every callback invocation in a finite run. *)
Theorem shutdown_consumption : forall s actions s',
  shutdown_run s actions s' ->
  shutdown_consumed s' = shutdown_consumed s ++ flat_map invoked_by actions.
Proof.
  intros s actions s' H. induction H; simpl; [symmetry; apply app_nil_r|].
  rewrite IHshutdown_run, (shutdown_step_consumed _ _ _ H), app_assoc. reflexivity.
Qed.

(** Every invoked token occurs once in the trace, not merely in final pending state. *)
Theorem shutdown_invocations_unique : forall s actions s',
  shutdown_run s actions s' -> shutdown_unique s ->
  NoDup (flat_map invoked_by actions).
Proof.
  intros s actions s' H Hu.
  pose proof (shutdown_run_unique _ _ _ H Hu) as Hfinal.
  unfold shutdown_unique in Hfinal.
  apply NoDup_app_remove_r in Hfinal.
  rewrite (shutdown_consumption _ _ _ H) in Hfinal.
  apply NoDup_app_remove_l in Hfinal. exact Hfinal.
Qed.

(** Recursive exit and _exit install their own signed status, not the old exit's. *)
Lemma shutdown_step_status : forall s action s',
  shutdown_step s action s' ->
  shutdown_status s' = shutdown_status s \/ action = RecursiveExit (shutdown_status s') \/
  action = Handoff HardExit (shutdown_status s').
Proof. intros s action s' H. destruct H; simpl; auto. Qed.

(** Cleanup and either handoff have closed registration. *)
Definition shutdown_closed (phase : shutdown_phase) : Prop :=
  match phase with Cleanup | HandedOff _ => True | _ => False end.

(** Closing registration is permanent through every remaining finite prefix. *)
Theorem shutdown_closed_sticky : forall s actions s',
  shutdown_run s actions s' -> shutdown_closed (shutdown_at s) ->
  shutdown_closed (shutdown_at s').
Proof.
  intros s actions s' H. induction H; [auto|]. intros Hclosed.
  apply IHshutdown_run. destruct H; simpl in *; tauto.
Qed.

(** A user-glibc handoff has no further lifecycle step. *)
Theorem shutdown_handoff_stopped : forall s kind action s',
  shutdown_at s = HandedOff kind -> ~ shutdown_step s action s'.
Proof.
  intros s kind action s' Hat H. destruct H; simpl in Hat; try discriminate.
  apply (H kind). exact Hat.
Qed.

(** Once cleanup starts, registration cannot succeed. *)
Theorem shutdown_done_no_registration : forall s entry s',
  shutdown_at s = Cleanup -> ~ shutdown_step s (RegisterCallback entry) s'.
Proof. intros s entry s' Hat H. inversion H; subst. discriminate. Qed.

(** Project only the stdout actions; handoff is not an output error/discard. *)
Definition shutdown_output (action : shutdown_action) : list stream_action :=
  match action with ShutdownOutput a => [a] | _ => [] end.

(** The stdout projection is exactly a stream run, including unfinished obligations. *)
Theorem shutdown_stream_run : forall s actions s',
  shutdown_run s actions s' ->
  stream_run (shutdown_stdout s) (flat_map shutdown_output actions) (shutdown_stdout s').
Proof.
  intros s actions s' H. induction H; [constructor|].
  destruct H; simpl in *; try exact IHshutdown_run.
  - eapply stream_next; [eassumption|exact IHshutdown_run].
  - eapply stream_next; [eassumption|exact IHshutdown_run].
Qed.

(** Shutdown neither loses accepted bytes nor mistakes error discard for delivery. *)
Theorem shutdown_output_accounting : forall s actions s',
  shutdown_run s actions s' ->
  outstanding (shutdown_stdout s) ++ accepted (flat_map shutdown_output actions) =
  resolved (flat_map shutdown_output actions) ++ outstanding (shutdown_stdout s').
Proof. intros. apply stream_accounting. apply shutdown_stream_run. assumption. Qed.

(** Host completion is a separate, uninstantiated contract. Requiring its
    witness does not claim native host handlers or loader finalization safe. *)
Inductive shutdown_observation (host_complete : handoff_kind -> Z -> stream_state -> Prop)
    : shutdown_state -> list event -> Prop :=
| observe_host_exit : forall kind status pending consumed q,
    host_complete kind status q ->
    shutdown_observation host_complete (mkShutdown (HandedOff kind) status pending consumed q)
      [ProcessExit (process_status status)].

(** Completion contributes exactly one exit observation, never a callback trace. *)
Theorem shutdown_observation_single : forall host s events,
  shutdown_observation host s events ->
  events = [ProcessExit (process_status (shutdown_status s))].
Proof. intros host s events H. destruct H. reflexivity. Qed.

(** Read main's W-class return as a signed C int, before callbacks see it. *)
Definition main_status (bits : Z) : Z := sign_extension (2 ^ 32) (2 ^ 31) bits.

(** Signed interpretation does not change the final process low byte. *)
Lemma main_status_low_byte : forall bits,
  process_status (main_status bits) = process_status bits.
Proof.
  intros bits. unfold main_status, sign_extension, process_status.
  assert (Hmod : (bits mod 2 ^ 32) mod 256 = bits mod 256).
  { apply Z.mod_mod_divide. exists (2 ^ 24). reflexivity. }
  destruct (2 ^ 31 <=? bits mod 2 ^ 32); [|exact Hmod].
  rewrite Zminus_mod, Hmod.
  replace (2 ^ 32 mod 256) with 0 by reflexivity.
  rewrite Z.sub_0_r, Z.mod_mod by lia. reflexivity.
Qed.

(** No locals means the core return invalidates exactly nothing. *)
Lemma return_no_locals_memory : forall c,
  fr_locals (c_frame c) = [] ->
  invalidate_locals (fr_locals (c_frame c)) (c_mem c) = Some (c_mem c).
Proof. intros c H. rewrite H. reflexivity. Qed.

(** Evidence for the narrow main-return bridge: no callers or locals,
    non-doomed W return, and an actual evaluated integer at the return site. *)
Definition main_return_site (ge : genv) (c : config) (bits : Z) : Prop :=
  exists label value,
    fr_at (c_frame c) = Exec label [] (JRet value) /\
    fr_doomed (c_frame c) = None /\ fr_locals (c_frame c) = [] /\
    c_callers c = [] /\ fn_ret (fr_fn (c_frame c)) = RClass W /\
    value_x ge (fr_env (c_frame c)) W value = Some (WInt bits).

(** This return really produces the core terminal, and its retained snapshot
    is final memory. No successor is added to ExternalMachine.Stopped. *)
Theorem main_return_step : forall ge c bits,
  main_return_site ge c bits ->
  Semantics.step ge c = Done (Ret (WInt bits)) /\
  invalidate_locals (fr_locals (c_frame c)) (c_mem c) = Some (c_mem c).
Proof.
  intros ge c bits (label & value & Hat & Hd & Hl & Hc & Hr & Hv).
  split; [|apply return_no_locals_memory; assumption].
  unfold Semantics.step. rewrite Hat. unfold jump_step. rewrite Hd, Hr, Hv.
  unfold return_step. rewrite Hl, Hc. reflexivity.
Qed.

(** A doomed return cannot use this bridge, regardless of its evaluated word. *)
Lemma main_return_not_doomed : forall ge c bits why,
  main_return_site ge c bits -> fr_doomed (c_frame c) <> Some why.
Proof. intros ge c bits why (_ & _ & _ & Hd & _). rewrite Hd. discriminate. Qed.

(** A live-local return needs a different final-memory argument. *)
Lemma main_return_no_live_locals : forall ge c bits,
  main_return_site ge c bits -> fr_locals (c_frame c) = [].
Proof. intros ge c bits (_ & _ & _ & _ & Hl & _). exact Hl. Qed.

(** Main initializes the lifecycle only with actual return-site evidence. *)
Definition main_shutdown (ge : genv) (c : config) (bits : Z)
    (pending : list registration) (q : stream_state) (s : shutdown_state) : Prop :=
  main_return_site ge c bits /\
  s = mkShutdown Tls (main_status bits) pending [] q.

(** The two's-complement -1 reaches callbacks as -1, and the host reports 255. *)
Example main_minus_one : main_status 4294967295 = -1 /\
  process_status (main_status 4294967295) = 255.
Proof. vm_compute. auto. Qed.

(** ## Public lifecycle boundaries *)

(** Two registrations of the same function remain distinct instances. *)
Definition exit_first : registration := mkRegistration 1 (AtExit (TInt 42)).
(** The second registration deliberately repeats the function, not its token. *)
Definition exit_second : registration := mkRegistration 2 (AtExit (TInt 42)).
(** A handler dynamically registered by the newest callback. *)
Definition exit_added : registration := mkRegistration 3 (AtExit (TInt 43)).

(** A dynamically added callback runs before the older pending registration. *)
Example shutdown_dynamic_lifo : forall q,
  shutdown_run (mkShutdown Tls 31 [exit_second; exit_first] [] q)
    [EmptyTls; InvokeCallback exit_second 31; RegisterCallback exit_added;
     ReturnCallback; InvokeCallback exit_added 31; ReturnCallback;
     InvokeCallback exit_first 31; ReturnCallback; StartCleanup; Handoff SoftExit 31]
    (mkShutdown (HandedOff SoftExit) 31 [] [2; 3; 1]%nat q).
Proof.
  intros q.
  eapply shutdown_next; [apply shutdown_tls|].
  eapply shutdown_next; [apply shutdown_invoke|].
  eapply shutdown_next; [apply shutdown_register; simpl; intuition congruence|].
  eapply shutdown_next; [apply shutdown_return|].
  eapply shutdown_next; [apply shutdown_invoke|].
  eapply shutdown_next; [apply shutdown_return|].
  eapply shutdown_next; [apply shutdown_invoke|].
  eapply shutdown_next; [apply shutdown_return|].
  eapply shutdown_next; [apply shutdown_cleanup|].
  eapply shutdown_next; [apply shutdown_soft|]. constructor.
Qed.

(** Recursive exit abandons the active callback and supplies -1 to older ones. *)
Example shutdown_recursive_status : forall q,
  shutdown_run (mkShutdown Tls 31 [exit_second; exit_first] [] q)
    [EmptyTls; InvokeCallback exit_second 31; RecursiveExit (-1); EmptyTls;
     InvokeCallback exit_first (-1); ReturnCallback; StartCleanup; Handoff SoftExit (-1)]
    (mkShutdown (HandedOff SoftExit) (-1) [] [2; 1]%nat q).
Proof.
  intros q.
  eapply shutdown_next; [apply shutdown_tls|].
  eapply shutdown_next; [apply shutdown_invoke|].
  eapply shutdown_next; [apply shutdown_recursive|].
  eapply shutdown_next; [apply shutdown_tls|].
  eapply shutdown_next; [apply shutdown_invoke|].
  eapply shutdown_next; [apply shutdown_return|].
  eapply shutdown_next; [apply shutdown_cleanup|].
  eapply shutdown_next; [apply shutdown_soft|]. constructor.
Qed.

(** An active registration instance cannot be registered again with its old token. *)
Example shutdown_no_instance_reuse : forall q s',
  ~ shutdown_step (mkShutdown (InCallback exit_second) 31 [exit_first] [2]%nat q)
      (RegisterCallback exit_second) s'.
Proof. intros q s' H. inversion H; subst. simpl in *. tauto. Qed.

(** A callback's _exit(98) replaces exit(31), leaving handlers and output untouched. *)
Example shutdown_hard_no_flush :
  shutdown_step
    (mkShutdown (InCallback exit_second) 31 [exit_first] [2]%nat
      (mkStream ByteOriented [65; 90] false))
    (Handoff HardExit 98)
    (mkShutdown (HandedOff HardExit) 98 [exit_first] [2]%nat
      (mkStream ByteOriented [65; 90] false)).
Proof. apply shutdown_hard. intros kind H. discriminate. Qed.

(** Hard exit can replace status after cleanup has closed registration too. *)
Example shutdown_cleanup_hard : forall q,
  shutdown_step (mkShutdown Cleanup 31 [] [2; 1]%nat q) (Handoff HardExit 98)
    (mkShutdown (HandedOff HardExit) 98 [] [2; 1]%nat q).
Proof. intros q. apply shutdown_hard. intros kind H. discriminate. Qed.

(** Its conditional host observation reports the hard exit's own status. *)
Example shutdown_hard_observation : forall host q,
  host HardExit 98 q ->
  shutdown_observation host (mkShutdown (HandedOff HardExit) 98 [exit_first] [2]%nat q)
    [ProcessExit 98].
Proof. intros host q H. apply observe_host_exit. exact H. Qed.

(** Partial delivery followed by output error can leave a byte outstanding at handoff. *)
Example shutdown_partial_error :
  shutdown_run (mkShutdown Cleanup 0 [] [] (mkStream ByteOriented [65; 66; 90] false))
    [ShutdownOutput (Deliver [65]); ShutdownOutput (Discard [66]); Handoff SoftExit 0]
    (mkShutdown (HandedOff SoftExit) 0 [] [] (mkStream ByteOriented [90] true)).
Proof.
  eapply shutdown_next.
  - apply shutdown_cleanup_output; [intros bytes H; discriminate|].
    apply (stream_deliver [65] [66; 90] false). discriminate.
  - eapply shutdown_next.
    + apply shutdown_cleanup_output; [intros bytes H; discriminate|].
      apply (stream_discard [66] [90] false). discriminate.
    + eapply shutdown_next; [apply shutdown_soft|]. constructor.
Qed.

(** A concrete no-locals main return: there is no invented stopped-state evidence. *)
Definition returning_main (m : mem) : config :=
  let f := mkFunc (TInt 0) (TInt 0) (RClass W) [] [] in
  mkConfig (mkFrame f [] [] None (Exec (TInt 1) [] (JRet (Const 4294967295)))) [] m 10.

(** The return-site predicate checks the concrete return value and core transition. *)
Example returning_main_bridge : forall ge m,
  main_return_site ge (returning_main m) 4294967295.
Proof. intros ge m. exists (TInt 1), (Const 4294967295). repeat split; reflexivity. Qed.

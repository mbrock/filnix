(** A logical stdout protocol, not a native FILE representation.

    Accepted bytes become ordered output obligations. Delivery and
    error-induced discard settle exact prefixes, preserving their
    interleaving. Outstanding obligations are NOT physical buffer
    contents: a direct-output path can accept and deliver in succession.
    Delivery means descriptor acceptance, not device durability. The
    error flag is not yet connected to native ferror.

    This protocol has no memory effects or allocator. Native buffering,
    allocation/fallback, capability roots and shutdown require separate
    realization obligations. In particular, a protocol step cannot mint
    write authority or establish ExternalCalls.effects. *)

From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Values Memory ExternalCalls.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Inductive stream_orientation : Type := Unoriented | ByteOriented | WideOriented.

Record stream_state : Type := mkStream {
  orientation : stream_orientation;
  outstanding : list Z;
  stream_error : bool
}.

Definition stream_wf (q : stream_state) : Prop :=
  Forall (fun b => 0 <= b < 256) (outstanding q) /\
  (outstanding q <> [] -> orientation q = ByteOriented).

Inductive stream_action : Type :=
| Accept (bytes : list Z)
| Deliver (bytes : list Z)
| Discard (bytes : list Z)
| OutputError.

(** The error indicator is sticky, not a ban on later output. Discard
    here means output-error abandonment, not seek/purge or fclose. A
    zero-progress failure records an error without settling any bytes. *)
Inductive stream_step : stream_state -> stream_action -> stream_state -> Prop :=
| stream_accept : forall q bytes,
    orientation q <> WideOriented -> Forall (fun b => 0 <= b < 256) bytes ->
    stream_step q (Accept bytes)
      (mkStream ByteOriented (outstanding q ++ bytes) (stream_error q))
| stream_deliver : forall bytes rest err,
    bytes <> [] ->
    stream_step (mkStream ByteOriented (bytes ++ rest) err) (Deliver bytes)
      (mkStream ByteOriented rest err)
| stream_discard : forall bytes rest err,
    bytes <> [] ->
    stream_step (mkStream ByteOriented (bytes ++ rest) err) (Discard bytes)
      (mkStream ByteOriented rest true)
| stream_output_error : forall pending err,
    stream_step (mkStream ByteOriented pending err) OutputError
      (mkStream ByteOriented pending true).

Inductive stream_run : stream_state -> list stream_action -> stream_state -> Prop :=
| stream_refl : forall q, stream_run q [] q
| stream_next : forall q action q1 actions q',
    stream_step q action q1 -> stream_run q1 actions q' ->
    stream_run q (action :: actions) q'.

Definition accepted_by (action : stream_action) : list Z :=
  match action with Accept bytes => bytes | _ => [] end.

Definition resolved_by (action : stream_action) : list Z :=
  match action with Deliver bytes | Discard bytes => bytes | _ => [] end.

Definition accepted (actions : list stream_action) : list Z := flat_map accepted_by actions.
Definition resolved (actions : list stream_action) : list Z := flat_map resolved_by actions.

Lemma stream_step_accounting : forall q action q',
  stream_step q action q' ->
  outstanding q ++ accepted_by action = resolved_by action ++ outstanding q'.
Proof.
  intros q action q' H. destruct H; simpl; try reflexivity; apply app_nil_r.
Qed.

(** Every old/new obligation is either resolved in FIFO order or still
    outstanding. Resolutions include BOTH delivery and abandonment;
    replacing them by delivery alone would promise lossless output. *)
Theorem stream_accounting : forall q actions q',
  stream_run q actions q' ->
  outstanding q ++ accepted actions = resolved actions ++ outstanding q'.
Proof.
  intros q actions q' H. induction H.
  - simpl. apply app_nil_r.
  - unfold accepted, resolved in *. simpl.
    rewrite app_assoc, (stream_step_accounting _ _ _ H).
    rewrite <- app_assoc, IHstream_run, app_assoc. reflexivity.
Qed.

Lemma stream_step_wf : forall q action q',
  stream_step q action q' -> stream_wf q -> stream_wf q'.
Proof.
  intros q action q' H [Hbytes Horient]. destruct H; split; simpl in *; auto.
  - apply Forall_app. auto.
  - apply Forall_app in Hbytes. tauto.
  - apply Forall_app in Hbytes. tauto.
Qed.

Theorem stream_run_wf : forall q actions q',
  stream_run q actions q' -> stream_wf q -> stream_wf q'.
Proof.
  intros q actions q' H. induction H; [auto|]. intros Hwf.
  apply IHstream_run. eapply stream_step_wf; eauto.
Qed.

Theorem stream_error_sticky : forall q actions q',
  stream_run q actions q' -> stream_error q = true -> stream_error q' = true.
Proof.
  intros q actions q' H. induction H; auto. intros Herr.
  apply IHstream_run. destruct H; simpl in *; auto.
Qed.

(** One puts invocation aggregates its acceptance actions into the
    existing cumulative StreamBytes event. Delivery/discard actions
    remain internal observations; no descriptor-write event is added. *)
Definition puts_observation (actions : list stream_action) : list event :=
  [StreamBytes 1 (accepted actions)].

Definition puts_protocol (bytes : list Z) (q : stream_state)
    (actions : list stream_action) (result : Z) (q' : stream_state) : Prop :=
  orientation q <> WideOriented /\ stream_run q actions q' /\
  exists tail, bytes ++ [10] = accepted actions ++ tail /\
    ((tail = [] /\ 0 <= result < 2 ^ 31) \/ result = 2 ^ 32 - 1).

(** This proves only the existing acceptance/result postcondition.
    String memory and final stdio readiness are independent premises;
    the native representation, footprints and effects are NOT derived
    from this pure protocol. Nor is native execution coverage claimed. *)
Theorem protocol_puts_post : forall bytes q actions result q' m p w born m' w',
  puts_protocol bytes q actions result q' -> c_string m p bytes -> stdio_ready m' w' ->
  puts_post [WPtr p] m w born (puts_observation actions)
    (CallReturn [WInt result]) m' w'.
Proof.
  intros bytes q actions result q' m p w born m' w' (_ & _ & tail & Hbytes & Hresult) Hstr Hready.
  exists p, bytes, (accepted actions), tail, result.
  split; [reflexivity|]. split; [exact Hstr|]. split; [exact Hbytes|].
  split; [exact Hresult|]. split; [reflexivity|]. split; [reflexivity|exact Hready].
Qed.

(** ## Observable protocol boundaries *)

Definition stdout_initial : stream_state := mkStream Unoriented [] false.

Example stdout_initial_wf : stream_wf stdout_initial.
Proof. unfold stream_wf, stdout_initial. simpl. split; [constructor|congruence]. Qed.

Example puts_buffered_acceptance :
  puts_protocol hello_bytes stdout_initial [Accept (hello_bytes ++ [10])] 6
    (mkStream ByteOriented (hello_bytes ++ [10]) false).
Proof.
  split; [discriminate|]. split.
  - eapply stream_next; [apply stream_accept; [discriminate|] | constructor].
    repeat constructor; lia.
  - exists []. split; [reflexivity|]. left. split; [reflexivity|lia].
Qed.

Example puts_buffered_observation :
  puts_observation [Accept (hello_bytes ++ [10])] = [StreamBytes 1 [104; 101; 108; 108; 111; 10]].
Proof. reflexivity. Qed.

(** Prior output precedes this call; some is delivered, some discarded
    on error, and later output still succeeds with the error flag set. *)
Example partial_delivery_discard_later_output :
  stream_run (mkStream ByteOriented [65; 66] false)
    [Accept [67; 68]; Deliver [65]; Discard [66; 67]; Accept [69]; Deliver [68; 69]]
    (mkStream ByteOriented [] true).
Proof.
  eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|].
  eapply stream_next; [apply (stream_deliver [65] [66; 67; 68] false); discriminate|].
  eapply stream_next; [apply (stream_discard [66; 67] [68] false); discriminate|].
  eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|].
  eapply stream_next; [apply (stream_deliver [68; 69] [] true); discriminate|constructor].
Qed.

Example error_without_progress :
  stream_run (mkStream ByteOriented [65] false) [OutputError; OutputError]
    (mkStream ByteOriented [65] true).
Proof. eapply stream_next; [constructor|]. eapply stream_next; constructor. Qed.

Example puts_eof_without_acceptance :
  puts_protocol [] (mkStream ByteOriented [65] false) [OutputError] (2 ^ 32 - 1)
    (mkStream ByteOriented [65] true).
Proof.
  split; [discriminate|]. split.
  - eapply stream_next; constructor.
  - exists [10]. split; [reflexivity|]. right. reflexivity.
Qed.

Example puts_success_requires_newline :
  ~ puts_protocol hello_bytes stdout_initial [Accept hello_bytes] 5
    (mkStream ByteOriented hello_bytes false).
Proof.
  intros (_ & _ & tail & Hbytes & [[-> _] | Hresult]); discriminate.
Qed.

Example no_wide_acceptance : forall pending err bytes q',
  ~ stream_step (mkStream WideOriented pending err) (Accept bytes) q'.
Proof. intros pending err bytes q' H. inversion H. contradiction. Qed.

Example no_out_of_order_delivery : forall q',
  ~ stream_step (mkStream ByteOriented [65; 66] false) (Deliver [66]) q'.
Proof. intros q' H. inversion H; subst; simpl in *; discriminate. Qed.

Example no_invalid_byte_acceptance : forall q q',
  ~ stream_step q (Accept [256]) q'.
Proof. intros q q' H. inversion H as [q0 bytes Ho Hb | | |]. inversion Hb. lia. Qed.

Example no_wide_eof_summary : forall bytes,
  ~ puts_protocol bytes (mkStream WideOriented [] false) [] (2 ^ 32 - 1)
    (mkStream WideOriented [] false).
Proof. intros bytes [Ho _]. apply Ho. reflexivity. Qed.

Example puts_partial_eof :
  puts_protocol [65; 66] stdout_initial [Accept [65]; OutputError] (2 ^ 32 - 1)
    (mkStream ByteOriented [65] true).
Proof.
  split; [discriminate|]. split.
  - eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|].
    eapply stream_next; constructor.
  - exists ([66; 10]). split; [reflexivity|]. right. reflexivity.
Qed.

Example puts_full_eof :
  puts_protocol [65] stdout_initial [Accept [65]; Accept [10]; OutputError] (2 ^ 32 - 1)
    (mkStream ByteOriented [65; 10] true).
Proof.
  split; [discriminate|]. split.
  - eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|].
    eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|].
    eapply stream_next; constructor.
  - exists []. split; [reflexivity|]. right. reflexivity.
Qed.

Example cumulative_acceptance_observation :
  puts_observation [Accept [65]; Deliver [65]; Accept [66; 10]] =
    [StreamBytes 1 [65; 66; 10]] /\
  puts_observation [OutputError] = [StreamBytes 1 []].
Proof. split; reflexivity. Qed.

Example discard_is_not_delivery :
  resolved [Deliver [65]; Discard [66; 67]; Deliver [68; 69]] = [65; 66; 67; 68; 69] /\
  [65; 68; 69] ++ [66; 67] <> [65; 66; 67; 68; 69].
Proof. split; [reflexivity|discriminate]. Qed.

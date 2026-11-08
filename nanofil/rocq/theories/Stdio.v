(** A logical stdout protocol, not a native FILE representation
    ([milestone 3b](../../docs/formal.md#campaign-4-milestone-3b-ordered-stdout-obligations)).

    Accepted bytes become ordered output obligations. Delivery and
    error-induced discard settle exact prefixes, preserving their
    interleaving. Outstanding obligations are NOT physical buffer
    contents: a direct-output path can accept and deliver in succession.
    Delivery means descriptor acceptance, not device durability. The
    error flag is not yet connected to native ferror.

    This protocol has no memory effects or allocator. Native buffering,
    allocation/fallback, capability roots and shutdown require separate
    realization [[obligation|obligations]]. In particular, a protocol
    step cannot mint write authority or establish [effects]. *)

From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Values Memory ExternalCalls.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** A C stream's orientation: not yet chosen, bytes, or wide
    characters. The first output fixes it. *)
Inductive stream_orientation : Type := Unoriented | ByteOriented | WideOriented.

(** The logical state of stdout: its orientation, the outstanding
    output obligations (bytes accepted but not yet delivered or
    discarded, in order), and the sticky error flag. *)
Record stream_state : Type := mkStream {
  orientation : stream_orientation;
  outstanding : list Z;
  stream_error : bool
}.

(** A well-formed stream state q: every outstanding obligation is a
    byte, and a stream with any is byte-oriented. *)
Definition stream_wf (q : stream_state) : Prop :=
  Forall (fun b => 0 <= b < 256) (outstanding q) /\
  (outstanding q <> [] -> orientation q = ByteOriented).

(** One protocol action: accept bytes as new obligations, deliver bytes
    to the descriptor, discard bytes after an output error, or record an
    output error that settled nothing. *)
Inductive stream_action : Type :=
| Accept (bytes : list Z)
| Deliver (bytes : list Z)
| Discard (bytes : list Z)
| OutputError.

(** One protocol step, from state q by an action:
    - accept appends bytes to the obligations of a stream that is not
      wide, orienting it to bytes;
    - deliver and discard consume a nonempty exact prefix of the
      obligations, discard also setting the error flag;
    - an output error only sets the error flag.

    The error indicator is sticky, not a ban on later output. Discard
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

(** A finite sequence of [stream_step]s, from q by actions to q'. *)
Inductive stream_run : stream_state -> list stream_action -> stream_state -> Prop :=
| stream_refl : forall q, stream_run q [] q
| stream_next : forall q action q1 actions q',
    stream_step q action q1 -> stream_run q1 actions q' ->
    stream_run q (action :: actions) q'.

(** The bytes an action accepts: an accept's, otherwise none. *)
Definition accepted_by (action : stream_action) : list Z :=
  match action with Accept bytes => bytes | _ => [] end.

(** The bytes an action settles: a delivery's or a discard's, otherwise
    none. *)
Definition resolved_by (action : stream_action) : list Z :=
  match action with Deliver bytes | Discard bytes => bytes | _ => [] end.

(** All bytes the actions accept, in order. *)
Definition accepted (actions : list stream_action) : list Z := flat_map accepted_by actions.
(** All bytes the actions settle, delivered or discarded, in order. *)
Definition resolved (actions : list stream_action) : list Z := flat_map resolved_by actions.

(** One step's accounting: the old obligations followed by what the
    action accepts equal what it settles followed by the new
    obligations. *)
Lemma stream_step_accounting : forall q action q',
  stream_step q action q' ->
  outstanding q ++ accepted_by action = resolved_by action ++ outstanding q'.
Proof.
  intros q action q' H. destruct H; simpl; try reflexivity; apply app_nil_r.
Qed.

(** For a whole [stream_run], the old obligations followed by all
    [accepted] bytes equal all [resolved] bytes followed by the
    remaining obligations. Every old or new obligation is either
    resolved in first-in, first-out order or still outstanding.
    Resolutions include BOTH delivery and abandonment;
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

(** A step keeps the stream state well formed ([stream_wf]). *)
Lemma stream_step_wf : forall q action q',
  stream_step q action q' -> stream_wf q -> stream_wf q'.
Proof.
  intros q action q' H [Hbytes Horient]. destruct H; split; simpl in *; auto.
  - apply Forall_app. auto.
  - apply Forall_app in Hbytes. tauto.
  - apply Forall_app in Hbytes. tauto.
Qed.

(** So does a whole run. *)
Theorem stream_run_wf : forall q actions q',
  stream_run q actions q' -> stream_wf q -> stream_wf q'.
Proof.
  intros q actions q' H. induction H; [auto|]. intros Hwf.
  apply IHstream_run. eapply stream_step_wf; eauto.
Qed.

(** Once set, the error flag stays set through any run. *)
Theorem stream_error_sticky : forall q actions q',
  stream_run q actions q' -> stream_error q = true -> stream_error q' = true.
Proof.
  intros q actions q' H. induction H; auto. intros Herr.
  apply IHstream_run. destruct H; simpl in *; auto.
Qed.

(** The events of one puts call that took the actions: one cumulative
    [StreamBytes] event on stdout with all the bytes accepted, even when
    that is none. Delivery and discard actions remain internal
    observations; no descriptor-write event is added. *)
Definition puts_observation (actions : list stream_action) : list event :=
  [StreamBytes 1 (accepted actions)].

(** A puts of the string bytes, from stream state q, runs the actions to
    q' and returns result: the stream is not wide; the actions accept a
    prefix of the string and its newline; and the result is a
    nonnegative int if all was accepted, or else EOF (2^32 - 1), which
    is also allowed after full acceptance. *)
Definition puts_protocol (bytes : list Z) (q : stream_state)
    (actions : list stream_action) (result : Z) (q' : stream_state) : Prop :=
  orientation q <> WideOriented /\ stream_run q actions q' /\
  exists tail, bytes ++ [10] = accepted actions ++ tail /\
    ((tail = [] /\ 0 <= result < 2 ^ 31) \/ result = 2 ^ 32 - 1).

(** A [puts_protocol] run, given a [c_string] argument and a final
    [stdio_ready] world, meets [puts_post] with [puts_observation] as its
    trace. This proves only the existing acceptance and result
    postcondition.
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

(** stdout at startup: unoriented, nothing outstanding, no error. *)
Definition stdout_initial : stream_state := mkStream Unoriented [] false.

(** The initial stdout is well formed. *)
Example stdout_initial_wf : stream_wf stdout_initial.
Proof. unfold stream_wf, stdout_initial. simpl. split; [constructor|congruence]. Qed.

(** puts of hello from the initial stdout may accept hello and its
    newline and return 6, delivering nothing yet: they stay
    outstanding. *)
Example puts_buffered_acceptance :
  puts_protocol hello_bytes stdout_initial [Accept (hello_bytes ++ [10])] 6
    (mkStream ByteOriented (hello_bytes ++ [10]) false).
Proof.
  split; [discriminate|]. split.
  - eapply stream_next; [apply stream_accept; [discriminate|] | constructor].
    repeat constructor; lia.
  - exists []. split; [reflexivity|]. left. split; [reflexivity|lia].
Qed.

(** Its observation is the one event of hello and a newline. *)
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

(** Output errors that settle nothing leave the obligations in place and
    set the error flag. *)
Example error_without_progress :
  stream_run (mkStream ByteOriented [65] false) [OutputError; OutputError]
    (mkStream ByteOriented [65] true).
Proof. eapply stream_next; [constructor|]. eapply stream_next; constructor. Qed.

(** puts may return EOF having accepted nothing, after an output
    error. *)
Example puts_eof_without_acceptance :
  puts_protocol [] (mkStream ByteOriented [65] false) [OutputError] (2 ^ 32 - 1)
    (mkStream ByteOriented [65] true).
Proof.
  split; [discriminate|]. split.
  - eapply stream_next; constructor.
  - exists [10]. split; [reflexivity|]. right. reflexivity.
Qed.

(** puts cannot succeed having accepted the string without its
    newline. *)
Example puts_success_requires_newline :
  ~ puts_protocol hello_bytes stdout_initial [Accept hello_bytes] 5
    (mkStream ByteOriented hello_bytes false).
Proof.
  intros (_ & _ & tail & Hbytes & [[-> _] | Hresult]); discriminate.
Qed.

(** A wide-oriented stream accepts no bytes. *)
Example no_wide_acceptance : forall pending err bytes q',
  ~ stream_step (mkStream WideOriented pending err) (Accept bytes) q'.
Proof. intros pending err bytes q' H. inversion H. contradiction. Qed.

(** Delivery must start with the oldest obligation. *)
Example no_out_of_order_delivery : forall q',
  ~ stream_step (mkStream ByteOriented [65; 66] false) (Deliver [66]) q'.
Proof. intros q' H. inversion H; subst; simpl in *; discriminate. Qed.

(** A value that is not a byte cannot be accepted. *)
Example no_invalid_byte_acceptance : forall q q',
  ~ stream_step q (Accept [256]) q'.
Proof. intros q q' H. inversion H as [q0 bytes Ho Hb | | |]. inversion Hb. lia. Qed.

(** puts on a wide-oriented stream is no protocol run, even one that
    does nothing and returns EOF. *)
Example no_wide_eof_summary : forall bytes,
  ~ puts_protocol bytes (mkStream WideOriented [] false) [] (2 ^ 32 - 1)
    (mkStream WideOriented [] false).
Proof. intros bytes [Ho _]. apply Ho. reflexivity. Qed.

(** puts may return EOF having accepted part of its string. *)
Example puts_partial_eof :
  puts_protocol [65; 66] stdout_initial [Accept [65]; OutputError] (2 ^ 32 - 1)
    (mkStream ByteOriented [65] true).
Proof.
  split; [discriminate|]. split.
  - eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|].
    eapply stream_next; constructor.
  - exists ([66; 10]). split; [reflexivity|]. right. reflexivity.
Qed.

(** puts may return EOF having accepted its whole string and newline. *)
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

(** The observation gathers all accepted bytes into one event, skipping
    deliveries, and is one empty event when nothing was accepted. *)
Example cumulative_acceptance_observation :
  puts_observation [Accept [65]; Deliver [65]; Accept [66; 10]] =
    [StreamBytes 1 [65; 66; 10]] /\
  puts_observation [OutputError] = [StreamBytes 1 []].
Proof. split; reflexivity. Qed.

(** Resolutions keep discards in their place among deliveries: moving
    the discarded bytes after the delivered ones gives another order. *)
Example discard_is_not_delivery :
  resolved [Deliver [65]; Discard [66; 67]; Deliver [68; 69]] = [65; 66; 67; 68; 69] /\
  [65; 68; 69] ++ [66; 67] <> [65; 66; 67; 68; 69].
Proof. split; [reflexivity|discriminate]. Qed.

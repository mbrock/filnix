(** Returning diagnostics on the consumer's same libc world and machine.
    Native diagnostic representation stays trusted. The frame below owns
    no diagnostic pool: it separates future write roots, not all retained
    sources or future release rights. *)
From iris.proofmode Require Import proofmode.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Identity ExternalCalls
  ExternalMachine Stdio Shutdown Streams Formatting Diagnostics Libc LibcStreams
  Pieces Heap ContractFrame Logic StringLogic LentLogic LibcStreamLogic
  LibcErrnoLogic LibcStreamTokens LibcStreamAdapter.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Preserve callback inventory, not the whole shutdown record: flushing
    stdout changes its authoritative protocol. Neither FILE inventory is
    frozen, and parser compatibility (including sampled errno) is separate. *)
Definition libc_diagnostic_frame (w w' : libc_world) : Prop :=
  libc_stdout w' = libc_stdout w /\ libc_stderr w' = libc_stderr w /\
  libc_locale (fst w') = libc_locale (fst w) /\
  libc_errno (fst w') = libc_errno (fst w) /\
  shutdown_at (snd w') = shutdown_at (snd w) /\
  shutdown_status (snd w') = shutdown_status (snd w) /\
  shutdown_pending (snd w') = shutdown_pending (snd w) /\
  shutdown_consumed (snd w') = shutdown_consumed (snd w).

(** Keep the native sources, writes, requests and segment interpretation.
    Readiness at both endpoints includes the independent FILE envelope. *)
Definition libc_diagnostic_context rep (native : diagnostic_context libc_world) :=
  mkDiagnosticContext libc_world
    (fun m w => diagnostic_ready native m w /\ libc_stream_ready rep m w)
    (diagnostic_sources native) (diagnostic_writes native)
    (diagnostic_requests native) (diagnostic_segments native)
    (fun w w' => diagnostic_frame native w w' /\ libc_diagnostic_frame w w').

(** Only this status-zero wrapper is an ordinary returning error symbol.
    Nonzero diagnostics still belong to the separate ending protocol. *)
Definition libc_error_contract rep requests wide native : contract libc_world :=
  error_contract (error_format_contract (libc_stream_model rep requests wide)
    libc_stdout libc_stderr (libc_diagnostic_context rep native)).

(** Exact open observations cannot be framed unchanged through acceptance
    or settlement. Open-only and completed-closed names can. *)
Definition diagnostic_name (d : stream_token) (h : gmap piece pval) : Prop :=
  match h !! PName (token_key d) with
  | None | Some (VStreamOpen _) | Some (VStream _ None) => True
  | Some _ => False
  end.

Definition libc_diagnostic_wi rep native out err b o m w h : Prop :=
  stream_tokens_wi rep out err b o m w h /\
  roots_apart (diagnostic_writes native w)
    (stream_data_heap (token_base out) (token_base err) h) m /\
  diagnostic_name out h /\ diagnostic_name err h.

(** Transport only what the permitted name constructors actually observe. *)
Lemma diagnostic_current : forall d w w' h h',
  h' !! PName (token_key d) = h !! PName (token_key d) ->
  diagnostic_name d h -> stream_current d w h ->
  ((exists info, libc_stream_at w (token_handle d) = Some info) ->
    exists info, libc_stream_at w' (token_handle d) = Some info) ->
  (libc_stream_at w (token_handle d) = None ->
    libc_stream_at w' (token_handle d) = None /\
    libc_stream_state w' (token_handle d) = libc_stream_state w (token_handle d)) ->
  stream_current d w' h' /\ diagnostic_name d h'.
Proof.
  intros d w w' h h' Hkey Hname Hcurrent Hopen Hclosed.
  unfold stream_current, diagnostic_name in *. rewrite Hkey.
  destruct (h !! PName (token_key d)) as [v|]; [|auto].
  destruct v; try contradiction.
  - destruct pending as [[physical fifo]|]; [contradiction|].
    destruct Hcurrent as [-> [Hlookup Hfifo]].
    destruct (Hclosed Hlookup) as [Hlookup' Hstate].
    split; [split; [reflexivity|split; [exact Hlookup'|rewrite Hstate; exact Hfifo]]|exact I].
  - destruct Hcurrent as [-> Hlookup]. split; [split; [reflexivity|auto]|exact I].
Qed.

Module LibcDiagnosticLogicOn (R : Runtime) (LG : StreamFrameLogic R).
Module M := LG.L.M.
Module T := LibcStreamTokensOn R LG.

(** The empty return list comes from the supplied machine's normal branch,
    never from a resource prefix. The same invocation also supplies the
    formatting observations and both FILE delegations. *)
Lemma error_returned : forall rep requests wide native r args xs
    s m w trace values s' m' w',
  M.E.invoke (libc_error_contract rep requests wide native) r args xs
    s m w trace (CallReturn values) s' m' w' ->
  values = [] /\ exists born,
    M.E.prefix (libc_error_contract rep requests wide native) xs
      s m w born trace s' m' w'.
Proof.
  intros rep requests wide native r args xs s m w trace values s' m' w' Hi.
  split.
  - inversion Hi; subst.
    match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      apply error_post_void in Hpost; injection Hpost; auto end.
  - eapply M.E.invoke_prefix; exact Hi.
Qed.

(** Sample only the already-owned errno byte keys. Life projection omits
    neither private bytes nor auxiliary pieces. Future FILE release
    separation is restored against the FULL heap, including both lives. *)
Theorem error_frame : forall rep requests wide native out err b o r args xs
    s m w trace values s' m' w' h old,
  M.E.invoke (libc_error_contract rep requests wide native) r args xs
    s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m ->
  libc_diagnostic_wi rep native out err b o m w h ->
  length old = 4%nat ->
  (forall l v, (l, v) ∈ byte_ps b o old -> h !! l = Some v) ->
  exists ys, values = [] /\ length ys = 4%nat /\
    (byte_ps b o ys).*1 = (byte_ps b o old).*1 /\
    agrees m' (overwrite (byte_ps b o ys) h) /\ live_disjoint m' /\ R.ready s' m' /\
    libc_diagnostic_wi rep native out err b o m' w' (overwrite (byte_ps b o ys) h).
Proof.
  intros rep requests wide native out err b o r args xs s m w trace values s' m' w' h old
    Hi Ha Hd Hr [Hpair [Hroots [Honame Hename]]] Hlen Howned.
  destruct Hpair as (Howf & Hewf & Hbase & Hkey & Hout & Herr & Hoc & Hec & Hprivate).
  destruct (Hprivate out (or_introl eq_refl)) as [Howi Horelease].
  destruct (Hprivate err (or_intror eq_refl)) as [Hewi Herelease].
  set (dh := stream_data_heap (token_base out) (token_base err) h).
  pose proof (stream_data_agrees (token_base out) (token_base err) m h Ha) as Hdata.
  change (agrees m dh) in Hdata.
  destruct (error_returned rep requests wide native r args xs s m w trace values s' m' w' Hi)
    as [Hvalues [born Hp]].
  pose proof (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' Hpers].
  destruct (LG.prefix_agrees_out _ _ _ _ _ _ _ _ _ _ _ dh (errno_keys b o)
    (span_contains (errno_span b o)) Hp Hr Hd) as (Hexcept & Hids & Hd' & Hborn).
  - intros l v Hl _. exact (Hdata l v Hl).
  - intros l v Hl Hmem. eapply agree_piece_registered; [exact Hmem|exact (Hdata l v Hl)].
  - change (roots_out (libc_stream_writes w (libc_stdout w) ++
      libc_stream_writes w (libc_stderr w) ++ diagnostic_writes native w) dh m
      (span_contains (errno_span b o))).
    intros root a Hin Hspan Hown. apply in_app_or in Hin as [Hin|Hin].
    + rewrite Hout in Hin. eapply errno_roots_out;
        [exact (proj1 (proj2 Howi))|exact (proj1 (proj2 (proj2 Howi)))|exact Hin|exact Hspan|exact Hown].
    + apply in_app_or in Hin as [Hin|Hin].
      * rewrite Herr in Hin. eapply errno_roots_out;
          [exact (proj1 (proj2 Hewi))|exact (proj1 (proj2 (proj2 Hewi)))|exact Hin|exact Hspan|exact Hown].
      * exfalso. exact (Hroots root a Hin Hspan Hown).
  - exact (proj2 (proj2 (proj2 (proj2 Howi)))).
  - intros base l v Hin. contradiction.
  - destruct (proj2 Hp) as [Hformat Htrace].
    destruct Hformat as (status & errnum & fmt & rest & text & body & info & info' & segments & pieces & actions &
      Hxs & Hstring & Hformat & Hsegments & Hpieces & Hinfo & Hopen & Hid & Hid' & Hrun &
      Haccepted & Hflush & Hready & Hframe & Houtdel & Herrdel & Hrootdel & Htrace' & Haux).
    destruct Hready as [Hnative Hready]. destruct Hframe as [Hnativeframe Hframe].
    change (libc_diagnostic_frame w w') in Hframe.
    destruct Hframe as (Hout' & Herr' & Hlocale & Herrno & Hphase & Hstatus & Hpending & Hconsumed).
    assert (He : libc_errno (fst w') = mkPtr (b + o) (Obj b)).
    { rewrite Herrno. exact (proj1 (proj2 Howi)). }
    assert (Hbytes : all_agree m' (byte_ps b o (errno_bytes m' b o))).
    { apply errno_bytes_agree. rewrite <- He. exact (proj1 (proj2 (proj2 Hready))). }
    set (ys := errno_bytes m' b o).
    assert (Hkeys : (byte_ps b o ys).*1 = (byte_ps b o old).*1).
    { rewrite !byte_ps_keys. unfold ys, errno_bytes. rewrite length_map length_seq Hlen. reflexivity. }
    set (h' := overwrite (byte_ps b o ys) h).
    set (dh' := stream_data_heap (token_base out) (token_base err) h').
    assert (Hlifeoff : forall base, PLive base ∉ (byte_ps b o ys).*1).
    { intros base Hin. rewrite byte_ps_keys in Hin.
      apply list_elem_of_fmap in Hin as (i & E & _). discriminate E. }
    assert (Hcommute : dh' = overwrite (byte_ps b o ys) dh).
    { unfold dh', h', dh. apply stream_data_overwrite; apply Hlifeoff. }
    assert (Hkeysfull : memory_keys_from h' h).
    { intros l v Hl Hmem. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin|[_ Hold]]; [|eauto].
      assert (Hinold : l ∈ (byte_ps b o old).*1).
      { rewrite <- Hkeys. apply list_elem_of_fmap. exists (l, v). auto. }
      apply list_elem_of_fmap in Hinold as ([key oldv] & E & Hinold). simpl in E. subst key.
      exists oldv. exact (Howned _ _ Hinold). }
    assert (Hkeysdata : memory_keys_from dh' dh).
    { intros l v Hl Hmem. apply stream_data_lookup in Hl as (Hl & Hno & Hne).
      destruct (Hkeysfull l v Hl Hmem) as [oldv Hold]. exists oldv.
      unfold dh. rewrite stream_data_lookup_ne; assumption. }
    assert (Hdata' : agrees m' dh').
    { rewrite Hcommute. intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin|[Hnot Hold]].
      - exact (all_agree_elem _ _ _ _ Hbytes Hin).
      - apply Hexcept; [exact Hold|]. rewrite <- (errno_bytes_keys m' b o). exact Hnot. }
    assert (Ha' : agrees m' h').
    { eapply stream_data_restore; [exact Ha|exact Hdata'|exact Hpers| | | |].
      - apply overwrite_out, Hlifeoff.
      - apply overwrite_out, Hlifeoff.
      - intros reg Hlive. eapply T.prefix_handle_live; [exact Hp|exact Hr|exact Hd|exact Hlive|].
        intros Hnil. contradiction.
      - intros reg Hlive. eapply T.prefix_handle_live; [exact Hp|exact Hr|exact Hd|exact Hlive|].
        intros Hnil. contradiction. }
    assert (Hnamekeys : forall d, h' !! PName (token_key d) = h !! PName (token_key d)).
    { intros d. apply overwrite_out. rewrite byte_ps_keys.
      intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E. }
    assert (Hcurrent : stream_current out w' h' /\ diagnostic_name out h').
    { eapply diagnostic_current; [apply Hnamekeys|exact Honame|exact Hoc| |].
      - intros [i Hi0]. unfold diagnostic_flush in Hflush.
        cbn [stream_at stream_state_at libc_stream_model] in Hflush.
        rewrite Hout Hi0 in Hflush. destruct Hflush as (i' & Hi' & _).
        exists i'. exact Hi'.
      - intros Hclosed. unfold diagnostic_flush in Hflush.
        cbn [stream_at stream_state_at libc_stream_model] in Hflush.
        rewrite Hout Hclosed in Hflush. exact Hflush. }
    assert (Hcurrenterr : stream_current err w' h' /\ diagnostic_name err h').
    { eapply diagnostic_current; [apply Hnamekeys|exact Hename|exact Hec| |].
      - intros _. exists info'. rewrite <- Herr. exact (proj1 (proj2 Hopen)).
      - intros Hclosed. change (libc_stream_at w (libc_stderr w) = Some info) in Hinfo.
        rewrite Herr Hclosed in Hinfo. discriminate Hinfo. }
    assert (Hprivate' : forall d, d = out \/ d = err ->
      libc_errno_wi rep (token_handle d) b o m' w' dh' /\
      ids_apart (libc_stream_releases w' (token_handle d)) h').
    { intros d Hdsel. destruct (Hprivate d Hdsel) as [Hwi Hrel].
      assert (Hdelegate : stream_delegates (libc_stream_model rep requests wide)
        w (token_handle d) born m' w').
      { destruct Hdsel as [-> | ->]; [rewrite <- Hout|rewrite <- Herr]; assumption. }
      assert (Hwi' : libc_errno_wi rep (token_handle d) b o m' w' dh').
      { eapply errno_wi_endpoint; [exact Hwi|exact Hdata|exact Hpers|exact Hd'|
          exact Hready|exact Herrno|exact Hdelegate|exact Hborn|exact Hkeysdata]. }
      split; [exact Hwi'|]. intros base l v Hin Hl Hmem.
      destruct (decide (l = PLive (token_base out))) as [->|Hno].
      - simpl. intros E. subst base. eapply libc_handle_not_released;
          [exact Hready|left; reflexivity| |exact Hin]. rewrite Hout' Hout. exact (proj1 Howf).
      - destruct (decide (l = PLive (token_base err))) as [->|Hne].
        + simpl. intros E. subst base. eapply libc_handle_not_released;
            [exact Hready|right; reflexivity| |exact Hin]. rewrite Herr' Herr. exact (proj1 Hewf).
        + apply (proj1 (proj2 (proj2 (proj2 Hwi'))) base l v Hin); [|exact Hmem].
          unfold dh'. rewrite stream_data_lookup_ne; assumption. }
    assert (Hroots' : roots_apart (diagnostic_writes native w') dh' m').
    { intros root a Hin Hspan (l & v & reg & Hl & Hmem & Hlive & Hrange).
      destruct (Hkeysdata l v Hl Hmem) as [oldv Hold].
      assert (Howned' : owned_live dh m' a).
      { exists l, oldv, reg. auto. }
      destruct (Hrootdel root Hin) as [_ Hauth].
      assert (Hapart : roots_apart (diagnostic_writes native w) dh m').
      { intros oldroot addr Holdroot Holdspan (key & val & rr & Hlookup & Hmemory & Hlive' & Hbounds).
        apply (Hroots oldroot addr Holdroot Holdspan).
        exists key, val, rr. split; [exact Hlookup|]. split; [exact Hmemory|]. split; [|exact Hbounds].
        eapply registered_live_back; [exact Hpers| |exact Hlive'].
        eapply agree_piece_registered; [exact Hmemory|exact (Hdata key val Hlookup)]. }
      exact (owned_not_authority (diagnostic_writes native w) born dh m' a Hd' Hapart Hborn Howned'
        (Hauth a Hspan)). }
    exists ys. split; [exact Hvalues|]. split.
    { unfold ys, errno_bytes. rewrite length_map length_seq. reflexivity. }
    split; [exact Hkeys|]. split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|].
    split.
    + split; [exact Howf|]. split; [exact Hewf|]. split; [exact Hbase|]. split; [exact Hkey|].
      split; [rewrite Hout'; exact Hout|]. split; [rewrite Herr'; exact Herr|].
      split; [exact (proj1 Hcurrent)|]. split; [exact (proj1 Hcurrenterr)|exact Hprivate'].
    + exact (conj Hroots' (conj (proj2 Hcurrent) (proj2 Hcurrenterr))).
Qed.

End LibcDiagnosticLogicOn.

(** Logical contract controls, not native FILEs or native diagnostic-pool
    realization. Both initial stdout states have actual admitted calls. *)
Module LibcDiagnosticChecks.
Module D := LibcDiagnosticLogicOn InterpRuntime StreamHandleChecks.LG.
Module F := LibcStreamChecks.
Module T := StreamTokenChecks.

Definition native := mkDiagnosticContext libc_world
  (fun _ _ => True) (fun _ _ => []) (fun _ => []) (fun _ _ _ => False)
  (fun _ _ _ body segments => segments = [body; [10]]) (fun _ _ => True).
Definition context := libc_diagnostic_context (fun _ _ => True) native.
Definition spec := libc_error_contract (fun _ _ => True)
  (fun _ _ _ _ => False) (fun _ _ _ _ _ => False) native.
Definition fmt := mkPtr 4096 (Ro 4096).
Definition words := [WInt 0; WInt 0; WPtr fmt].
Definition args := [Arg W (Const 0); Arg W (Const 0); Arg P (Const 0)].

Definition final_world (opened : bool) : libc_world :=
  (mkLibcPayload (libc_locale (fst conversion_world))
    (mkStdioWorld opened [mkSpan (libc_errno (fst conversion_world)) 4])
    (libc_errno (fst conversion_world))
    (mkLibcStreams F.out_file F.err_file true (mkStream ByteOriented [67; 10] false))
    (libc_getopt (fst conversion_world)),
   mkShutdown Handlers 0 [] [] (mkStream ByteOriented [] true)).

Lemma final_ready : forall opened,
  libc_stream_ready (fun _ _ => True) T.changed_errno (final_world opened).
Proof.
  intros opened. destruct (T.changed_ready opened)
    as (Hrep & Hlocale & He & _ & _ & Hu & Hstatus & Hphase & Hdistinct & Hroots & Hout & Herr & Hsep).
  split; [exact Hrep|]. split; [exact Hlocale|]. split; [exact He|].
  split.
  { change (stream_wf (mkStream ByteOriented [] true)).
    cbn [stream_wf outstanding orientation]. split; [apply Forall_nil|intros _; reflexivity]. }
  split.
  { change (stream_wf (mkStream ByteOriented [67; 10] false)).
    cbn [stream_wf outstanding orientation]. split; [repeat constructor; lia|intros _; reflexivity]. }
  split; [exact Hu|]. split; [exact Hstatus|]. split; [exact Hphase|].
  split; [exact Hdistinct|]. split; [exact Hroots|].
  split; [exact Hout|]. split; [exact Herr|exact Hsep].
Qed.

Definition heap (opened : bool) : gmap piece pval :=
  <[PName (-2) := if opened then VStreamOpen (token_handle T.out)
    else VStream (token_handle T.out) None]>
    (<[PName (-3) := VStreamOpen (token_handle T.err)]> StreamHandleChecks.heap).

Lemma heap_agrees : forall opened, agrees conversion_mem (heap opened).
Proof.
  intros opened l v Hl. unfold heap in Hl.
  apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]].
  - subst l v. destruct opened; exact I.
  - apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]]; [subst l v; exact I|].
    exact (StreamHandleChecks.heap_agrees l v Hl).
Qed.

Lemma entry_wi : forall opened,
  libc_diagnostic_wi (fun _ _ => True) native T.out T.err 5120 0
    conversion_mem (F.world opened) (heap opened).
Proof.
  intros opened.
  assert (Hkeys : forall l v, stream_data_heap 1024 2048 (heap opened) !! l = Some v ->
    mem_piece l -> l ∈ errno_keys 5120 0).
  { intros l v Hl Hmem. apply stream_data_lookup in Hl as (Hl & Hno & Hne).
    unfold heap in Hl.
    apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]]; [subst l; contradiction|].
    apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]]; [subst l; contradiction|].
    unfold StreamHandleChecks.heap in Hl.
    apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]]; [subst l; contradiction|].
    apply lookup_insert_Some in Hl as [[El Ev]|[_ Hl]]; [subst l; contradiction|].
    unfold HelloErrnoChecks.heap in Hl. apply elem_of_list_to_map_2 in Hl.
    change (l ∈ (byte_ps 5120 0 [0; 0; 0; 0]).*1).
    apply list_elem_of_fmap. exists (l, v). auto. }
  split.
  - split; [split; [reflexivity|simpl; lia]|]. split; [split; [reflexivity|simpl; lia]|].
    split; [discriminate|]. split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold stream_current, heap. cbn [T.out token_key]. rewrite lookup_insert_eq.
      destruct opened.
      - split; [reflexivity|]. exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7). reflexivity.
      - split; [reflexivity|]. split; reflexivity. }
    split.
    { unfold stream_current, heap. cbn [T.err token_key].
      rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_eq.
      split; [reflexivity|]. exists (mkStreamInfo 2 stdout_initial 3). destruct opened; reflexivity. }
    intros d [-> | ->].
    all: split; [|intros base l v Hin; destruct opened; contradiction].
    all: split; [apply F.ready|].
    all: split; [reflexivity|].
    all: split; [intros root a Hin; destruct opened; contradiction|].
    all: split; [intros base l v Hin; destruct opened; contradiction|].
    all: intros l v Hl Hnot; destruct l as [base|base off|base off|key]; try exact I.
    all: exfalso; apply Hnot; eapply Hkeys; [exact Hl|exact I].
  - split; [intros root a []|]. unfold diagnostic_name, heap. cbn [T.out T.err token_key].
    rewrite lookup_insert_eq. rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_eq.
    destruct opened; auto.
Qed.

Lemma admitted : forall opened, contract_pre spec words conversion_mem (F.world opened).
Proof.
  intros opened. split.
  - split.
    + exists 0, 0, fmt, [], [67], [67], (mkStreamInfo 2 stdout_initial 3).
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split.
      * vm_compute. repeat split; congruence.
      * split; [apply format_literal; [lia|discriminate|constructor]|].
        split; [split; [exact I|apply F.ready]|]. split; [constructor|]. split.
        -- destruct (libc_stream_open (fun _ _ => True) (fun _ _ _ _ => False)
             (fun _ _ _ _ _ => False) conversion_mem (F.world opened) (file_handle F.err_file)
             F.err_file (F.ready opened) ltac:(destruct opened; reflexivity)) as [info Hopen].
           destruct Hopen as [Hr [Hlookup Hrest]].
           assert (info = mkStreamInfo 2 stdout_initial 3) as ->.
           { destruct opened; injection Hlookup; auto. }
           exact (conj Hr (conj Hlookup Hrest)).
        -- split; [discriminate|destruct opened; discriminate].
    + exists 0, 0, fmt, []. split; [reflexivity|lia].
  - exists 0, fmt, []. split; [reflexivity|lia].
Qed.

Lemma format_prefix : forall opened,
  error_format_prefix F.model libc_stdout libc_stderr context words conversion_mem
    (F.world opened) [] [StreamBytes 2 [67; 10]] T.changed_errno (final_world opened).
Proof.
  intros opened.
  exists 0, 0, fmt, [], [67], [67], (mkStreamInfo 2 stdout_initial 3),
    (mkStreamInfo 2 (mkStream ByteOriented [67; 10] false) 3),
    [[67]; [10]], [[67]; [10]], [Accept [67; 10]].
  split; [reflexivity|]. split; [vm_compute; repeat split; congruence|].
  split; [apply format_literal; [lia|discriminate|constructor]|].
  split; [reflexivity|]. split.
  - repeat (constructor; [exists []; reflexivity|]). constructor.
  - split; [destruct opened; reflexivity|]. split.
    + split; [apply final_ready|]. split; [destruct opened; reflexivity|].
      split; [reflexivity|]. split.
      * split; [split; [repeat constructor; lia|reflexivity]|simpl; lia].
      * change (Forall (writable_span T.changed_errno) [errno_span 5120 0]).
        constructor; [exact (proj1 (proj2 (proj1 (proj2 (proj2 (final_ready opened))))))|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. split.
      * eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|constructor].
      * split; [reflexivity|]. split.
        -- destruct opened.
           ++ exists (mkStreamInfo 1 (mkStream ByteOriented [] true) 7).
              split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
              split; [reflexivity|apply F.close_settles].
           ++ split; reflexivity.
        -- split; [split; [exact I|apply final_ready]|].
           split; [split; [exact I|repeat split; reflexivity]|]. split.
           ++ destruct opened.
              ** split.
                 --- intros root [E|[]]. subst root. split.
                     +++ right. left. exists (mkSpan (mkPtr 5120 (Obj 5120)) 0).
                         split; [right; left; reflexivity|reflexivity].
                     +++ intros a Ha. left. exists (errno_span 5120 0).
                         split; [left; reflexivity|]. split.
                         *** exact (proj1 (proj2 (proj1 (proj2 (proj2 (final_ready true)))))).
                         *** exact Ha.
                 --- split.
                     +++ intros source Hin. left. exists source. split; [exact Hin|reflexivity].
                     +++ intros x []; contradiction.
              ** split; [intros root []|]. split; intros x []; contradiction.
           ++ split.
              ** split.
                 --- intros root [E|[]]. subst root. split.
                     +++ right. left. exists (mkSpan (mkPtr 5120 (Obj 5120)) 0).
                         split; [right; left; reflexivity|reflexivity].
                     +++ intros a Ha. left. exists (errno_span 5120 0).
                         split; [left; reflexivity|]. split.
                         *** exact (proj1 (proj2 (proj1 (proj2 (proj2 (final_ready opened)))))).
                         *** exact Ha.
                 --- split.
                     +++ intros source Hin. left. exists source. split; [destruct opened; exact Hin|reflexivity].
                     +++ intros x []; destruct opened; contradiction.
              ** split; [intros root []|]. split; [right; reflexivity|]. intros a _ _. reflexivity.
Qed.

Lemma returning_call : forall opened,
  D.M.E.invoke spec CVoid args words InterpRuntime.start conversion_mem (F.world opened)
    [StreamBytes 2 [67; 10]] (CallReturn []) InterpRuntime.start T.changed_errno (final_world opened).
Proof.
  intros opened. eapply D.M.E.invoke_normal with (born := []).
  - split; [reflexivity|]. split.
    + split; [reflexivity|]. exists (Const 0), (Const 0), (Const 0), []. split; [reflexivity|constructor].
    + exists (Const 0), (Const 0), (Const 0), []. reflexivity.
  - apply admitted.
  - split.
    + eapply D.M.E.effects_local; [apply local_store_bytes|constructor].
      intros a Ha. left. exists (errno_span 5120 0).
      split; [apply in_or_app; right; apply in_or_app; left; destruct opened; left; reflexivity|].
      split.
      * exact (proj1 (proj2 (proj1 (proj2 (proj2 (F.ready opened)))))).
      * unfold span_contains, errno_span. simpl. lia.
    + split; [apply format_prefix|constructor; [reflexivity|constructor]].
  - split; [split; [apply format_prefix|reflexivity]|reflexivity].
  - intros why Hbad. discriminate Hbad.
  - intros vs Hvs. injection Hvs as <-. split; [reflexivity|constructor].
  - intros status Hbad. discriminate Hbad.
Qed.

(** Apply the actual frame with both lives/names and all errno bytes.
    The last sampled byte is one, not its old zero. Closed stdout stays
    a completed-closed observation; open stderr survives FIFO acceptance. *)
Example framed_return : forall opened,
  exists ys, length ys = 4%nat /\
    agrees T.changed_errno (overwrite (byte_ps 5120 0 ys) (heap opened)) /\
    libc_diagnostic_wi (fun _ _ => True) native T.out T.err 5120 0
      T.changed_errno (final_world opened) (overwrite (byte_ps 5120 0 ys) (heap opened)) /\
    (overwrite (byte_ps 5120 0 ys) (heap opened)) !! PByte 5120 3 = Some (VByte 1) /\
    (overwrite (byte_ps 5120 0 ys) (heap opened)) !! PName (-2) =
      Some (if opened then VStreamOpen (token_handle T.out) else VStream (token_handle T.out) None) /\
    (overwrite (byte_ps 5120 0 ys) (heap opened)) !! PName (-3) =
      Some (VStreamOpen (token_handle T.err)).
Proof.
  intros opened.
  destruct (D.error_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) native T.out T.err 5120 0 CVoid args words
    InterpRuntime.start conversion_mem (F.world opened) [StreamBytes 2 [67; 10]] []
    InterpRuntime.start T.changed_errno (final_world opened) (heap opened) [0; 0; 0; 0]
    (returning_call opened) (heap_agrees opened) HelloErrnoChecks.disjoint HelloErrnoChecks.ready
    (entry_wi opened) eq_refl) as (ys & _ & Hlen & Hkeys & Ha & Hd & Hr & Hw).
  - intros l v Hin. destruct (MemLogic.byte_ps_elem _ _ _ _ _ Hin) as (i & x & Hi & -> & ->).
    unfold heap, StreamHandleChecks.heap.
    repeat (rewrite lookup_insert_ne; [|discriminate]).
    unfold HelloErrnoChecks.heap. apply elem_of_list_to_map_1; [|exact Hin].
    change (base.NoDup [PByte 5120 0; PByte 5120 1; PByte 5120 2; PByte 5120 3]).
    repeat (apply base.NoDup_cons_2; [set_solver|]). apply base.NoDup_nil_2.
  - exists ys. split; [exact Hlen|]. split; [exact Ha|]. split; [exact Hw|]. split.
    + destruct ys as [|a [|b [|c [|d rest]]]]; try discriminate Hlen.
      assert (rest = []) as -> by (destruct rest; [reflexivity|discriminate Hlen]).
      assert (Hl : (overwrite (byte_ps 5120 0 [a; b; c; d]) (heap opened)) !!
        PByte 5120 3 = Some (VByte d)).
      { cbn [byte_ps overwrite]. repeat (rewrite lookup_insert_ne; [|discriminate]). apply lookup_insert_eq. }
      destruct (Ha _ _ Hl) as [_ Hbyte].
      destruct (Hbyte (mkRegion 5120 5128 Heap Live) eq_refl eq_refl) as (_ & _ & Hvalue).
      change (1 = d) in Hvalue. rewrite Hvalue. exact Hl.
    + split.
      * rewrite overwrite_out; [unfold heap; apply lookup_insert_eq|].
        rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E.
      * rewrite overwrite_out.
        -- unfold heap. rewrite lookup_insert_ne; [|discriminate]. apply lookup_insert_eq.
        -- rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E.
Qed.

Example evolving_protocols :
  libc_diagnostic_frame (F.world true) (final_world true) /\
  shutdown_pending (snd (final_world true)) = shutdown_pending (snd (F.world true)) /\
  snd (final_world true) <> snd (F.world true) /\
  outstanding (libc_stream_state (final_world true) (token_handle T.err)) = [67; 10].
Proof.
  split; [repeat split; reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
  intros H. apply (f_equal shutdown_stdout) in H. discriminate H.
Qed.

Example exact_snapshot_rejected : forall pending fifo,
  ~ diagnostic_name T.out
    (<[PName (-2) := VStream (token_handle T.out) (Some (pending, fifo))]> (heap true)).
Proof. intros. unfold diagnostic_name. cbn [T.out token_key]. rewrite lookup_insert_eq. exact (fun H => H). Qed.

Example exact_open_becomes_stale :
  stream_current T.out (F.world true) T.open_heap /\
  ~ stream_current T.out (final_world true) T.open_heap.
Proof.
  split; [exact (proj1 T.open_snapshots_current)|]. unfold stream_current, T.open_heap.
  cbn [T.out token_key]. rewrite lookup_insert_eq.
  intros [_ [info [Hlookup [_ Hfifo]]]].
  change (Some (mkStreamInfo 1 (mkStream ByteOriented [] true) 7) = Some info) in Hlookup.
  injection Hlookup as <-. discriminate Hfifo.
Qed.

Definition writing_native := mkDiagnosticContext libc_world
  (diagnostic_ready native) (diagnostic_sources native)
  (fun _ => [mkSpan (mkPtr 1024 (Obj 1024)) 1])
  (diagnostic_requests native) (diagnostic_segments native) (diagnostic_frame native).

Example private_byte_rejected : forall m w h v,
  h !! PByte 1024 0 = Some v -> live_at m 1024 (token_region T.out) ->
  ~ libc_diagnostic_wi (fun _ _ => True) writing_native T.out T.err 5120 0 m w h.
Proof.
  intros m w h v Hl Hlive [_ [Hroots _]].
  exact (StreamHandleChecks.private_byte_rejected m h v Hl Hlive Hroots).
Qed.

Example private_aux_rejected : forall m w h v,
  h !! PAux 1024 0 = Some v -> live_at m 1024 (token_region T.out) ->
  ~ libc_diagnostic_wi (fun _ _ => True) writing_native T.out T.err 5120 0 m w h.
Proof.
  intros m w h v Hl Hlive [_ [Hroots _]].
  exact (StreamHandleChecks.private_aux_rejected m h v Hl Hlive Hroots).
Qed.

Example nonzero_not_returning : forall m w,
  ~ contract_pre spec [WInt 1; WInt 0; WPtr fmt] m w.
Proof.
  intros m w. apply nonzero_error_not_returning with (status := 1).
  - exists 0, fmt, []. split; [reflexivity|lia].
  - lia.
Qed.

End LibcDiagnosticChecks.

(** Composite stdout/stderr contracts. FILE metadata and physical counts
    live in [libc_streams]; stdout's only logical protocol lives in
    [shutdown_stdout]. Native representation and exclusive ownership
    remain trusted premises, not consequences of writable addresses.
    Closed handles retain identity and protocol, but grant no authority. *)
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls LibcCalls
  ExternalMachine Locale Stdio Shutdown Streams Formatting Libc.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Exact handle comparison includes capability, not merely address. *)
Definition same_file (p q : ptr) : bool :=
  (ptr_addr p =? ptr_addr q) && cap_eqb (ptr_cap p) (ptr_cap q).

(** Stdout's stable represented handle. *)
Definition libc_stdout (w : libc_world) : ptr :=
  file_handle (libc_stdout_file (libc_streams (fst w))).
(** Stderr's stable represented handle. *)
Definition libc_stderr (w : libc_world) : ptr :=
  file_handle (libc_stderr_file (libc_streams (fst w))).

(** Selection is capability-sensitive even for a consumed handle. *)
Definition libc_file_at (w : libc_world) (p : ptr) : option libc_file :=
  if same_file p (libc_stdout w) then
    if stdout_usable (libc_stdio (fst w)) then Some (libc_stdout_file (libc_streams (fst w))) else None
  else if same_file p (libc_stderr w) then
    if libc_stderr_open (libc_streams (fst w)) then Some (libc_stderr_file (libc_streams (fst w))) else None
  else None.

(** Lookup survives consumption and never restores a saved stdout FIFO. *)
Definition libc_stream_state (w : libc_world) (p : ptr) : stream_state :=
  if same_file p (libc_stdout w) then shutdown_stdout (snd w)
  else if same_file p (libc_stderr w) then libc_stderr_state (libc_streams (fst w))
  else stdout_initial.

(** Only active handles expose physical counts and ordinary stream calls. *)
Definition libc_stream_at (w : libc_world) (p : ptr) : option stream_info :=
  match libc_file_at w p with
  | Some file => Some (mkStreamInfo (if same_file p (libc_stdout w) then 1 else 2)
      (libc_stream_state w p) (file_pending file))
  | None => None
  end.

(** These sources belong to FILE state, not to a caller's format strings.
    A zero-length handle span supplies its capability, not extra bytes. *)
Definition file_sources (file : libc_file) : list span :=
  mkSpan (file_handle file) 0 :: file_reads file ++ file_roots file.

(** Errno's fixed capability supports its scalar write root in generic
    delegation. It grants no readable aux slot and is excluded from the
    private FILE pools by [file_errno_apart]. *)
Definition libc_stream_sources (w : libc_world) (p : ptr) : list span :=
  match libc_file_at w p with
  | Some file => file_sources file ++ [mkSpan (libc_errno (fst w)) 0]
  | None => []
  end.

(** Active roots only; closing retires historical buffer authority. *)
Definition libc_stream_writes (w : libc_world) (p : ptr) : list span :=
  match libc_file_at w p with
  | Some file => file_roots file ++ [mkSpan (libc_errno (fst w)) 4]
  | None => []
  end.

(** Only FILE-private spans may change pointer aux; the extra scalar
    errno root in [libc_stream_writes] may not do so. *)
Definition libc_stream_aux_roots (w : libc_world) (p : ptr) : list span :=
  match libc_file_at w p with Some file => file_roots file | None => [] end.

(** Exclusive heaps are not inferred from the handle or its roots. *)
Definition libc_stream_releases (w : libc_world) (p : ptr) : list Z :=
  match libc_file_at w p with Some file => file_owned file | None => [] end.

(** Errno is a fixed scalar output, not FILE-private retained authority.
    Entry and endpoint representations independently establish this,
    including complete aux-loaded capabilities in private sources. *)
Definition file_errno_apart (m : mem) (cell : ptr) (file : libc_file) : Prop :=
  (forall root, In root (file_roots file) -> spans_apart root (mkSpan cell 4)) /\
  (forall base, ptr_cap cell = Obj base \/ ptr_cap cell = Ro base ->
    ~ In base (file_owned file) /\
    ~ available_cap (file_sources file) [] m (Obj base) /\
    ~ available_cap (file_sources file) [] m (Ro base)).

(** Structural obligations for an ACTIVE FILE. The supplied native
    representation additionally owns close rights and excludes caller
    setvbuf storage and static FILE identities from [file_owned]. *)
Definition libc_file_ready (m : mem) (cell : ptr) (file : libc_file) : Prop :=
  ptr_addr (file_handle file) <> 0 /\ readable_bytes m (file_handle file) 1 /\
  0 <= file_pending file < 2 ^ 64 /\
  Forall (writable_span m) (file_roots file) /\
  Forall (fun source => readable_bytes m (span_ptr source) (span_size source)) (file_reads file) /\
  Forall (locale_heap m) (file_owned file) /\ file_errno_apart m cell file.

(** Legacy puts roots are the same active stdout inventory, not a second grant.
    Historical roots in closed FILE records are deliberately omitted. *)
Definition libc_active_roots (w : libc_world) : list span :=
  (if stdout_usable (libc_stdio (fst w)) then
    file_roots (libc_stdout_file (libc_streams (fst w))) else []) ++
  [mkSpan (libc_errno (fst w)) 4].

(** A selected close cannot release either stable FILE, locale storage,
    or authority retained by the other active FILE. Exclusive ownership
    against caller storage still belongs to the native representation. *)
Definition libc_release_separated (m : mem) (w : libc_world) : Prop :=
  forall p file, libc_file_at w p = Some file -> forall base,
    In base (file_owned file) ->
    ~ In base (locale_owned (libc_locale (fst w))) /\
    (forall q other, libc_file_at w q = Some other ->
      file_handle other <> file_handle file -> ~ In base (file_owned other)) /\
    ~ available_cap
      (mkSpan (libc_stdout w) 0 :: mkSpan (libc_stderr w) 0 ::
       locale_private_sources (libc_locale (fst w)) ++
       (if same_file p (libc_stdout w) then
          match libc_file_at w (libc_stderr w) with Some other => file_sources other | None => [] end
        else match libc_file_at w (libc_stdout w) with Some other => file_sources other | None => [] end))
      [] m (Obj base) /\
    ~ available_cap
      (mkSpan (libc_stdout w) 0 :: mkSpan (libc_stderr w) 0 ::
       locale_private_sources (libc_locale (fst w)) ++
       (if same_file p (libc_stdout w) then
          match libc_file_at w (libc_stderr w) with Some other => file_sources other | None => [] end
        else match libc_file_at w (libc_stdout w) with Some other => file_sources other | None => [] end))
      [] m (Ro base).

(** Endpoint readiness permits either FILE closed.
    It keeps locale/errno and shutdown structure coherent; it does not
    establish native representation, exclusive ownership or progress. *)
Definition libc_stream_ready (rep : mem -> libc_world -> Prop) m w : Prop :=
  rep m w /\ locale_ready (fun _ _ => True) m (libc_locale (fst w)) /\
  errno_cell m (libc_errno (fst w)) /\
  stream_wf (shutdown_stdout (snd w)) /\
  stream_wf (libc_stderr_state (libc_streams (fst w))) /\
  shutdown_unique (snd w) /\ -(2 ^ 31) <= shutdown_status (snd w) < 2 ^ 31 /\
  (match shutdown_at (snd w) with
   | InCallback active => In (registration_token active) (shutdown_consumed (snd w))
   | _ => True end) /\
  ptr_addr (libc_stdout w) <> ptr_addr (libc_stderr w) /\
  stdio_roots (libc_stdio (fst w)) = libc_active_roots w /\
  (stdout_usable (libc_stdio (fst w)) = true ->
    libc_file_ready m (libc_errno (fst w)) (libc_stdout_file (libc_streams (fst w)))) /\
  (libc_stderr_open (libc_streams (fst w)) = true ->
    libc_file_ready m (libc_errno (fst w)) (libc_stderr_file (libc_streams (fst w)))) /\
  libc_release_separated m w.

(** Stream calls preserve current locale, errno identity and lifecycle
    inventory. Only the selected FILE's state may change. Shared native
    metadata still needs the independent memory frame, not disjoint locks. *)
Definition libc_stream_frame (p : ptr) (w w' : libc_world) : Prop :=
  libc_stdout w' = libc_stdout w /\ libc_stderr w' = libc_stderr w /\
  libc_locale (fst w') = libc_locale (fst w) /\ libc_errno (fst w') = libc_errno (fst w) /\
  shutdown_at (snd w') = shutdown_at (snd w) /\
  shutdown_status (snd w') = shutdown_status (snd w) /\
  shutdown_pending (snd w') = shutdown_pending (snd w) /\
  shutdown_consumed (snd w') = shutdown_consumed (snd w) /\
  if same_file p (libc_stdout w) then
    libc_stderr_file (libc_streams (fst w')) = libc_stderr_file (libc_streams (fst w)) /\
    libc_stderr_open (libc_streams (fst w')) = libc_stderr_open (libc_streams (fst w)) /\
    libc_stderr_state (libc_streams (fst w')) = libc_stderr_state (libc_streams (fst w))
  else
    libc_stdout_file (libc_streams (fst w')) = libc_stdout_file (libc_streams (fst w)) /\
    stdout_usable (libc_stdio (fst w')) = stdout_usable (libc_stdio (fst w)) /\
    shutdown_stdout (snd w') = shutdown_stdout (snd w).

(** Concrete projections, with only native allocation policy and wide
    settlement remaining realization parameters. Wide conversion needs
    its own effects/representation witness even if settlement succeeds. *)
Definition libc_stream_model rep requests wide : stream_model libc_world :=
  mkStreamModel libc_world libc_stream_at libc_stream_state (libc_stream_ready rep)
    libc_stream_sources libc_stream_writes libc_stream_aux_roots libc_stream_releases
    (fun w p align size => exists file, libc_file_at w p = Some file /\ requests w p align size)
    libc_stream_frame wide.

(** Reached ordinary entries. The fallback composes with the remaining
    libc registry; it cannot override these six actual plain symbols. *)
Definition libc_stream_registry rep requests wide
    (fallback : name -> option (contract libc_world)) (symbol : name) : option (contract libc_world) :=
  let model := libc_stream_model rep requests wide in
  if name_eqb symbol (TAtom "ferror") then Some (ferror_contract model) else
  if name_eqb symbol (TAtom "__fpending") then Some (fpending_contract model) else
  if name_eqb symbol (TAtom "fclose") then Some (fclose_contract model) else
  if name_eqb symbol (TAtom "printf") then Some (printf_contract model libc_stdout) else
  if name_eqb symbol (TAtom "fprintf") then Some (fprintf_contract model) else
  if name_eqb symbol (TAtom "fputs") then Some (fputs_contract model) else fallback symbol.

(** Lookup laws are definitional, independent of the fallback registry. *)
Lemma libc_stream_registry_entries : forall rep requests wide fallback,
  let model := libc_stream_model rep requests wide in
  let registry := libc_stream_registry rep requests wide fallback in
  registry (TAtom "ferror") = Some (ferror_contract model) /\
  registry (TAtom "__fpending") = Some (fpending_contract model) /\
  registry (TAtom "fclose") = Some (fclose_contract model) /\
  registry (TAtom "printf") = Some (printf_contract model libc_stdout) /\
  registry (TAtom "fprintf") = Some (fprintf_contract model) /\
  registry (TAtom "fputs") = Some (fputs_contract model).
Proof. intros. repeat split; reflexivity. Qed.

(** Exact comparison accepts a retained handle with its own capability. *)
Lemma same_file_refl : forall p, same_file p p = true.
Proof.
  intros [a c]. unfold same_file. simpl. rewrite Z.eqb_refl.
  destruct c; simpl; try apply Z.eqb_refl; try apply term_eqb_refl; reflexivity.
Qed.

(** Stdout always projects the authoritative shutdown protocol, closed
    or open; there is no pre-close snapshot to restore. *)
Lemma libc_stdout_protocol : forall w,
  libc_stream_state w (libc_stdout w) = shutdown_stdout (snd w).
Proof. intros. unfold libc_stream_state. rewrite same_file_refl. reflexivity. Qed.

(** A forged capability at the very same address is not the FILE. *)
Lemma libc_file_forged : forall w a,
  same_file (mkPtr a CNone) (libc_stdout w) = false ->
  same_file (mkPtr a CNone) (libc_stderr w) = false ->
  libc_stream_at w (mkPtr a CNone) = None.
Proof. intros w a Ho He. unfold libc_stream_at, libc_file_at. rewrite Ho, He. reflexivity. Qed.

(** An active selected FILE has the structural representation obligations
    of its own inventory entry, not those of a sibling handle. *)
Lemma libc_file_at_ready : forall rep m w p file,
  libc_stream_ready rep m w -> libc_file_at w p = Some file ->
  libc_file_ready m (libc_errno (fst w)) file.
Proof.
  intros rep m w p file (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & Hre & _) Hfile.
  unfold libc_file_at in Hfile.
  destruct (same_file p (libc_stdout w));
    [destruct (stdout_usable (libc_stdio (fst w))) eqn:Ho|
     destruct (same_file p (libc_stderr w));
       [destruct (libc_stderr_open (libc_streams (fst w))) eqn:He|]];
    try discriminate; injection Hfile as <-; auto.
Qed.

(** Admission follows from represented endpoint structure and an active
    exact handle; no output success or chosen query result is assumed. *)
Lemma libc_stream_open : forall rep requests wide m w p file,
  libc_stream_ready rep m w -> libc_file_at w p = Some file ->
  exists info, stream_open (libc_stream_model rep requests wide) m w p info.
Proof.
  intros rep requests wide m w p file Hready Hfile.
  pose proof Hready as (_ & _ & Herrno & Hout & Herr & _ & _ & _ & _ & _ & Hro & Hre & _).
  pose proof (libc_file_at_ready rep m w p file Hready Hfile) as Hfile_ready.
  destruct Hfile_ready as (_ & _ & Hpending & Hroots & _).
  exists (mkStreamInfo (if same_file p (libc_stdout w) then 1 else 2)
    (libc_stream_state w p) (file_pending file)).
  split; [exact Hready|]. split.
  - unfold stream_at, libc_stream_model, libc_stream_at. rewrite Hfile. reflexivity.
  - split; [reflexivity|]. split.
    + split; [|exact Hpending]. unfold libc_stream_state.
      destruct (same_file p (libc_stdout w)); [exact Hout|].
      destruct (same_file p (libc_stderr w)) eqn:He; [exact Herr|].
      apply stdout_initial_wf.
    + change (Forall (writable_span m) (libc_stream_writes w p)).
      unfold libc_stream_writes. rewrite Hfile. apply Forall_app. split; [exact Hroots|].
      constructor; [exact (proj1 (proj2 Herrno))|constructor].
Qed.

(** Query/close admission is shared and independent of their outcomes. *)
Lemma libc_stream_admitted : forall rep requests wide m w p file,
  libc_stream_ready rep m w -> libc_file_at w p = Some file ->
  stream_call_pre (libc_stream_model rep requests wide) [WPtr p] m w.
Proof.
  intros. destruct (libc_stream_open rep requests wide m w p file H H0) as [info Ho].
  exists p, info. auto.
Qed.

(** Narrow literal/vararg interpretation is separate from the selected
    FILE representation. All errors and partial acceptance stay admitted. *)
Lemma libc_output_admitted : forall rep requests wide api xs m w file bytes,
  libc_stream_ready rep m w ->
  libc_file_at w (output_target api libc_stdout w xs) = Some file ->
  orientation (libc_stream_state w (output_target api libc_stdout w xs)) <> WideOriented ->
  output_text api m xs bytes ->
  output_pre api (libc_stream_model rep requests wide) libc_stdout xs m w.
Proof.
  intros rep requests wide api xs m w file bytes Hr Hfile Ho Htext.
  destruct (libc_stream_open rep requests wide m w _ file Hr Hfile) as [info Hopen].
  exists info, bytes. split; [exact Hopen|].
  destruct Hopen as (_ & _ & Hstate & _). rewrite Hstate. auto.
Qed.

(** An unchanged active endpoint delegates its fixed scalar errno root
    as well as its private roots; it needs no new allocation or owner. *)
Lemma libc_stream_delegates_refl : forall rep requests wide m w p,
  libc_stream_ready rep m w ->
  stream_delegates (libc_stream_model rep requests wide) w p [] m w.
Proof.
  intros rep requests wide m w p Hr. unfold stream_delegates.
  cbn [stream_writes stream_sources stream_releases libc_stream_model].
  split.
  - intros root Hin. destruct (libc_file_at w p) as [file|] eqn:Hfile.
    2: { unfold libc_stream_writes in Hin. rewrite Hfile in Hin. contradiction. }
    destruct (libc_stream_open rep requests wide m w p file Hr Hfile)
      as (info & _ & _ & _ & _ & Hw).
    change (Forall (writable_span m) (libc_stream_writes w p)) in Hw.
    assert (Hwr : writable_span m root) by (rewrite Forall_forall in Hw; exact (Hw root Hin)).
    split.
    + right. left. unfold libc_stream_writes in Hin. rewrite Hfile in Hin.
      unfold libc_stream_sources. rewrite Hfile. apply in_app_or in Hin as [Hin|Hin].
      * exists root. split; [|reflexivity]. apply in_or_app. left.
        unfold file_sources. right. apply in_or_app. right. exact Hin.
      * simpl in Hin. destruct Hin as [<-|[]].
        exists (mkSpan (libc_errno (fst w)) 0). split; [|reflexivity].
        apply in_or_app. right. simpl. auto.
    + intros a Ha. left. exists root. auto.
  - split.
    + intros source Hin. left. exists source. auto.
    + intros base Hin. left. exact Hin.
Qed.

(** The same libc errno/locale/conversion registry stays usable after
    closing stdout; writable retired roots are not required. *)
Lemma libc_stream_ready_libc : forall rep m w,
  libc_stream_ready rep m w -> libc_ready rep m w.
Proof.
  intros rep m w (Hrep & Hlocale & Herrno & Hout & Herr & Hu & Hstatus & Hphase &
    Hdistinct & Hroots & Hro & Hre & Hrelease).
  split; [exact Hrep|]. split; [exact Hlocale|]. split.
  - rewrite Hroots. unfold libc_active_roots. apply Forall_app. split.
    + destruct (stdout_usable (libc_stdio (fst w))) eqn:Ho; [|constructor].
      destruct (Hro eq_refl) as (_ & _ & _ & Hr & _). exact Hr.
    + constructor; [exact (proj1 (proj2 Herrno))|constructor].
  - auto.
Qed.

(** Keeping the world unchanged is a valid logical frame. *)
Lemma libc_stream_frame_refl : forall p w, libc_stream_frame p w w.
Proof. intros. unfold libc_stream_frame. repeat split; destruct (same_file p (libc_stdout w)); auto. Qed.

(** Errno is scalar-only even when its entry aux is nonempty. The
    frame is required at all call prefixes, including resource stops. *)
Lemma libc_stream_errno_aux : forall rep requests wide m w p file m',
  libc_stream_ready rep m w -> libc_file_at w p = Some file ->
  stream_aux_frame (libc_stream_model rep requests wide) m w p m' ->
  m_aux m' (ptr_addr (libc_errno (fst w))) = m_aux m (ptr_addr (libc_errno (fst w))).
Proof.
  intros rep requests wide m w p file m' Hr Hfile Hframe.
  pose proof (libc_file_at_ready rep m w p file Hr Hfile)
    as (_ & _ & _ & _ & _ & _ & Hapart & _).
  pose proof Hr as (_ & _ & (_ & Hcell & _) & _).
  apply Hframe.
  - eapply write_authority_in with (roots := [mkSpan (libc_errno (fst w)) 4]) (born := []).
    left. exists (mkSpan (libc_errno (fst w)) 4). split; [simpl; auto|].
    split; [exact Hcell|]. unfold span_contains. simpl. lia.
  - change (~ write_authority (libc_stream_aux_roots w p) [] m (ptr_addr (libc_errno (fst w)))).
    unfold libc_stream_aux_roots. rewrite Hfile.
    intros [(root & Hin & _ & Ha)|(base & reg & [] & _)].
    specialize (Hapart root Hin). unfold spans_apart, span_contains in *. simpl in *. lia.
Qed.

(** The registry and projections use the consumer's actual machine. *)
Module LibcStreamsOn (R : Runtime) (M : ExternalMachineSig R).
Module E := M.E.
Module S := StreamsOn R M.
Module F := FormattingOn R M.
Module C := LibcOn R M.

(** A logical unchanged query has an independently admitted prefix.
    This is nonvacuity, not a claim that native locking changes nothing. *)
Theorem query_unchanged_prefix : forall rep requests wide p file s m w,
  libc_stream_ready rep m w -> libc_file_at w p = Some file ->
  E.prefix (ferror_contract (libc_stream_model rep requests wide)) [WPtr p]
    s m w [] [] s m w.
Proof.
  intros rep requests wide p file s m w Hr Hfile.
  destruct (libc_stream_open rep requests wide m w p file Hr Hfile) as [info Ho].
  split; [constructor|]. exists p, info.
  split; [reflexivity|]. split; [exact (proj1 (proj2 Ho))|].
  split; [exact Ho|]. split; [apply libc_stream_frame_refl|].
  split; [apply libc_stream_delegates_refl; exact Hr|]. split; [reflexivity|].
  split; [unfold stream_aux_frame|]; intros; reflexivity.
Qed.

(** The concrete ferror query admits either sticky-error value without
    assuming that the caller sees a successful output history. *)
Theorem ferror_unchanged : forall rep requests wide r args p file s m w,
  stream_query_abi W r args -> libc_stream_ready rep m w ->
  libc_file_at w p = Some file ->
  E.invoke (ferror_contract (libc_stream_model rep requests wide)) r args [WPtr p]
    s m w [] (CallReturn [WInt (if stream_error (libc_stream_state w p) then 1 else 0)]) s m w.
Proof.
  intros rep requests wide r args p file s m w Habi Hr Hfile.
  destruct (libc_stream_open rep requests wide m w p file Hr Hfile) as [info Ho].
  eapply S.ferror_return with (born := []).
  - exact Habi.
  - exists p, info. auto.
  - eapply query_unchanged_prefix; eauto.
  - exists p, info, (if stream_error (libc_stream_state w p) then 1 else 0).
    split; [reflexivity|]. split; [exact (proj1 (proj2 Ho))|].
    split; [exact Ho|]. split; [apply libc_stream_frame_refl|].
    split; [apply libc_stream_delegates_refl; exact Hr|].
    split; [reflexivity|]. split; [reflexivity|].
    destruct Ho as (_ & _ & Hstate & _). rewrite Hstate.
    cbn [stream_state_at libc_stream_model].
    destruct (stream_error (libc_stream_state w p)); split; [lia|split; congruence|lia|split; congruence].
Qed.

(** Physical pending, not the logical FIFO length, is the query result. *)
Theorem fpending_unchanged : forall rep requests wide r args p file s m w,
  stream_query_abi L r args -> libc_stream_ready rep m w ->
  libc_file_at w p = Some file ->
  E.invoke (fpending_contract (libc_stream_model rep requests wide)) r args [WPtr p]
    s m w [] (CallReturn [WInt (file_pending file)]) s m w.
Proof.
  intros rep requests wide r args p file s m w Habi Hr Hfile.
  destruct (libc_stream_open rep requests wide m w p file Hr Hfile) as [info Ho].
  assert (Hpending : stream_pending info = file_pending file).
  { destruct Ho as (_ & Hinfo & _). change (libc_stream_at w p = Some info) in Hinfo.
    unfold libc_stream_at in Hinfo. rewrite Hfile in Hinfo. injection Hinfo as <-. reflexivity. }
  assert (Hrange : 0 <= file_pending file < 2 ^ 64).
  { destruct Ho as (_ & _ & _ & [_ Hrange] & _). rewrite Hpending in Hrange. exact Hrange. }
  eapply E.invoke_normal with (born := []).
  - exact Habi.
  - exists p, info. auto.
  - exact (query_unchanged_prefix rep requests wide p file s m w Hr Hfile).
  - exists p, info. split; [reflexivity|]. split; [exact (proj1 (proj2 Ho))|].
    split; [exact Ho|]. split; [apply libc_stream_frame_refl|].
    split; [apply libc_stream_delegates_refl; exact Hr|]. split; [reflexivity|].
    rewrite Hpending. reflexivity.
  - intros why Hbad. discriminate.
  - intros values Hvalues. injection Hvalues as <-. split.
    + exists (WInt (file_pending file)). split; [reflexivity|]. simpl.
      rewrite Z.mod_small by exact Hrange. reflexivity.
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** The old exact errno lookup is still admitted with closed stdout. *)
Theorem errno_after_close : forall rep r args s m w,
  errno_location_abi r args -> libc_stream_ready rep m w ->
  E.invoke (C.errno_contract rep) r args [] s m w []
    (CallReturn [WPtr (libc_errno (fst w))]) s m w.
Proof. intros. apply C.errno_admitted; [exact H|]. apply libc_stream_ready_libc. exact H0. Qed.

(** Returning and resource-ending output expose the same represented
    world/frame/provenance cutpoint. Normal-result facts are separate. *)
Theorem output_world : forall rep requests wide api r args xs s m w trace ending s' m' w',
  E.invoke (output_contract api (libc_stream_model rep requests wide) libc_stdout)
    r args xs s m w trace ending s' m' w' ->
  libc_stream_ready rep m' w' /\
  libc_stream_frame (output_target api libc_stdout w xs) w w' /\
  exists born,
    stream_delegates (libc_stream_model rep requests wide) w
      (output_target api libc_stdout w xs) born m' w' /\
    stream_aux_frame (libc_stream_model rep requests wide) m w
      (output_target api libc_stdout w xs) m'.
Proof.
  intros rep requests wide api r args xs s m w trace ending s' m' w' Hcall.
  destruct (E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (born & He & info & info' & bytes & actions & tail &
      Hinfo & Htext & Hbytes & Hrun & Hopen & Hid & Hframe & Hdelegate & Htrace & Haux).
  split; [exact (proj1 Hopen)|]. split; [exact Hframe|]. exists born. auto.
Qed.

(** Ordinary narrow output results remain canonical, including errors. *)
Theorem output_returned : forall rep requests wide api r args xs s m w trace values s' m' w',
  E.invoke (output_contract api (libc_stream_model rep requests wide) libc_stdout)
    r args xs s m w trace (CallReturn values) s' m' w' ->
  exists result, values = [WInt result] /\ 0 <= result < 2 ^ 32.
Proof. intros. eapply F.output_returned; eauto. Qed.

End LibcStreamsOn.

(** Logical controls, not a claim that these tiny objects are native
    FILEs. Physical pending counts deliberately differ from FIFO length. *)
Module LibcStreamChecks.
Module M := ExternalMachine InterpRuntime.
Module C := LibcStreamsOn InterpRuntime M.

(** Static handles live in separate existing fixture objects. *)
Definition out_file := mkLibcFile (mkPtr 1024 (Obj 1024)) 7 [] [] [].
(** Stderr has a different physical count. *)
Definition err_file := mkLibcFile (mkPtr 2048 (Obj 2048)) 3 [] [] [].
(** Close retires stdout after settling its two logical obligations;
    physical pending is deliberately not the FIFO length. *)
Definition world (opened : bool) : libc_world :=
  (mkLibcPayload (libc_locale (fst conversion_world))
    (mkStdioWorld opened [mkSpan (libc_errno (fst conversion_world)) 4])
    (libc_errno (fst conversion_world))
    (mkLibcStreams out_file err_file true stdout_initial)
    (libc_getopt (fst conversion_world)),
   mkShutdown Handlers 0 [] [] (mkStream ByteOriented (if opened then [65; 66] else []) true)).

(** Neither stream's private zero-length source exposes errno authority. *)
Lemma empty_file_errno : forall a n,
  a <> 5120 -> file_errno_apart conversion_mem (mkPtr 5120 (Obj 5120))
    (mkLibcFile (mkPtr a (Obj a)) n [] [] []).
Proof.
  intros a n Hne. split; [intros root []|]. intros base [Hbase|Hbase];
    [injection Hbase as <-|discriminate]. split; [intros []|]. split;
    intros [Hnone|[(source & Hin & Hcap)|[(source & addr & Hin & Ha & Hsize & _)|(b & [] & _)]]];
    try discriminate; simpl in Hin; destruct Hin as [<-|[]]; simpl in *;
    [congruence|unfold span_contains in Ha; simpl in Ha; lia|discriminate|
     unfold span_contains in Ha; simpl in Ha; lia].
Qed.

(** Both represented open FILE entries satisfy their structural slice. *)
Lemma files_ready :
  libc_file_ready conversion_mem (mkPtr 5120 (Obj 5120)) out_file /\
  libc_file_ready conversion_mem (mkPtr 5120 (Obj 5120)) err_file.
Proof.
  assert (Hread : forall a, a = 1024 \/ a = 2048 ->
      readable_bytes conversion_mem (mkPtr a (Obj a)) 1).
  { intros a [-> | ->]; split; [simpl; lia| |simpl; lia|].
    all: split.
    1: { exists 1024, (mkRegion 1024 1056 GlobalData Live). auto. }
    2: { exists 2048, (mkRegion 2048 2056 Stack Live). auto. }
    all: split; [reflexivity|].
    all: intros i Hi; assert (i = 0) as -> by lia; vm_compute; split; congruence. }
  split; unfold out_file, err_file, libc_file_ready; split; [discriminate| |discriminate|].
  all: split; [apply Hread; auto|].
  all: split; [simpl; lia|].
  all: split; [constructor|].
  all: split; [constructor|].
  all: split; [constructor|apply empty_file_errno; lia].
Qed.

(** Closed stdout is a nonempty represented state, not a vacuous pre. *)
Lemma ready : forall opened, libc_stream_ready (fun _ _ => True) conversion_mem (world opened).
Proof.
  intros opened. pose proof (proj1 (conversion_pre 1 ltac:(lia))) as (_ & Hl & _ & He & _).
  split; [exact I|]. split; [exact Hl|]. split; [exact He|].
  split; [split; [destruct opened; repeat constructor; lia|reflexivity]|].
  split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|].
  split; [exact I|]. split; [simpl; lia|]. split; [destruct opened; reflexivity|].
  split; [intros _; exact (proj1 files_ready)|].
  split; [intros _; exact (proj2 files_ready)|].
  intros p file Hfile base Hin. unfold libc_file_at in Hfile.
  destruct (same_file p (libc_stdout (world opened)));
    [destruct opened|destruct (same_file p (libc_stderr (world opened)))];
    try discriminate; injection Hfile as <-; contradiction.
Qed.

(** Same registered errno contract, after stdout closes, returns exactly
    the original capability and snapshot. *)
Example closed_errno :
  M.E.invoke (C.C.errno_contract (fun _ _ => True)) CVoid [] []
    InterpRuntime.start conversion_mem (world false) []
    (CallReturn [WPtr (mkPtr 5120 (Obj 5120))])
    InterpRuntime.start conversion_mem (world false).
Proof. apply C.errno_after_close; [split; [left; reflexivity|reflexivity]|apply ready]. Qed.

(** After stdout closes, stderr remains queryable with its own count. *)
Example stderr_pending_after_close :
  M.E.invoke (fpending_contract (libc_stream_model (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ _ => False))) CVoid [Arg P (Const 0)]
    [WPtr (file_handle err_file)] InterpRuntime.start conversion_mem (world false) []
    (CallReturn [WInt 3]) InterpRuntime.start conversion_mem (world false).
Proof.
  apply C.fpending_unchanged with (file := err_file).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - apply ready.
  - reflexivity.
Qed.

(** Seven physical pending bytes are not the two logical obligations. *)
Example stdout_pending_not_fifo :
  M.E.invoke (fpending_contract (libc_stream_model (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ _ => False))) CVoid [Arg P (Const 0)]
    [WPtr (file_handle out_file)] InterpRuntime.start conversion_mem (world true) []
    (CallReturn [WInt 7]) InterpRuntime.start conversion_mem (world true).
Proof.
  apply C.fpending_unchanged with (file := out_file).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - apply ready.
  - reflexivity.
Qed.

(** A closed handle cannot be queried again, regardless of the registry. *)
Example closed_query_rejected : forall rep requests wide,
  ~ stream_call_pre (libc_stream_model rep requests wide)
    [WPtr (file_handle out_file)] conversion_mem (world false).
Proof.
  intros rep requests wide (p & info & Hxs & _ & Hinfo & _).
  injection Hxs as <-. discriminate Hinfo.
Qed.

(** A genuine completed fclose, not merely a chosen closed fixture:
    error-discard settles the old FIFO and EOF still consumes the handle. *)
Definition model := libc_stream_model (fun _ _ => True)
  (fun _ _ _ _ => False) (fun _ _ _ _ _ => False).

Lemma close_settles : forall complete,
  stream_settlement model (world true) (file_handle out_file)
    (mkStream ByteOriented [65; 66] true) (mkStream ByteOriented [] true) complete.
Proof.
  intros. exists [Discard [65; 66]]. split.
  - eapply stream_next; [exact (stream_discard [65; 66] [] true ltac:(discriminate))|constructor].
  - split; reflexivity.
Qed.

Lemma close_frame : libc_stream_frame (file_handle out_file) (world true) (world false).
Proof. repeat split; reflexivity. Qed.

Lemma close_delegates : stream_delegates model (world true) (file_handle out_file)
  [] conversion_mem (world false).
Proof. split; [intros root []|]. split; intros x []; contradiction. Qed.

Example close_then_errno :
  M.E.invoke (fclose_contract model) CVoid [Arg P (Const 0)]
    [WPtr (file_handle out_file)] InterpRuntime.start conversion_mem (world true) []
    (CallReturn [WInt stream_eof]) InterpRuntime.start conversion_mem (world false) /\
  M.E.invoke (C.C.errno_contract (fun _ _ => True)) CVoid [] []
    InterpRuntime.start conversion_mem (world false) []
    (CallReturn [WPtr (mkPtr 5120 (Obj 5120))])
    InterpRuntime.start conversion_mem (world false).
Proof.
  split; [|exact closed_errno].
  eapply M.E.invoke_normal with (born := []).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - apply libc_stream_admitted with (file := out_file); [apply ready|reflexivity].
  - split; [constructor|]. exists (file_handle out_file),
      (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7), (mkStream ByteOriented [] true).
    split; [reflexivity|]. split; [reflexivity|]. split; [apply close_settles|].
    split; [reflexivity|]. split; [apply ready|]. split; [apply close_frame|].
    split; [apply close_delegates|]. split; [reflexivity|]. split; [left; reflexivity|].
    unfold stream_aux_frame. intros; reflexivity.
  - exists (file_handle out_file), (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7),
      (mkStream ByteOriented [] true), stream_eof.
    split; [reflexivity|]. split; [reflexivity|]. split; [apply close_settles|].
    split; [reflexivity|]. split; [right; reflexivity|]. split; [reflexivity|].
    split; [intros base []|]. split; [apply ready|]. split; [apply close_frame|]. auto.
  - intros why Hbad. discriminate.
  - intros values Hvalues. injection Hvalues as <-. split.
    + exists (WInt stream_eof). split; reflexivity.
    + repeat constructor.
  - intros status Hbad. discriminate.
Qed.

(** The private-aux frame rejects clobbering a nontrivial errno aux,
    independently of the scalar byte-write permission. *)
Example errno_aux_clobber_rejected : forall m m',
  in_object m 5120 -> m_aux m 5120 = Obj 1024 -> m_aux m' 5120 = CNone ->
  ~ stream_aux_frame model m (world true) (file_handle out_file) m'.
Proof.
  intros m m' Hin Hold Hnew Hframe.
  assert (Houtside : ~ write_authority
    (stream_aux_roots model (world true) (file_handle out_file)) [] m 5120).
  { intros [(root & [] & _)|(base & reg & [] & _)]. }
  specialize (Hframe 5120 Hin Houtside). rewrite Hold, Hnew in Hframe. discriminate.
Qed.

(** Query-only byte framing protects the last errno byte too, even
    though ordinary effects authorize all four scalar errno writes. *)
Example query_errno_byte_clobber_rejected : forall spec s m' s' trace ending,
  (spec = ferror_contract model \/ spec = fpending_contract model) ->
  m_bytes m' 5123 <> m_bytes conversion_mem 5123 ->
  ~ M.E.invoke spec CVoid [Arg P (Const 0)] [WPtr (file_handle out_file)]
    s conversion_mem (world true) trace ending s' m' (world true).
Proof.
  intros spec s m' s' trace ending Hspec Hchanged Hcall.
  destruct Hspec as [-> | ->].
  all: (
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (born & _ & p & info & Hxs & _ & _ & _ & _ & _ & _ & Hbytes);
    injection Hxs as <-;
    apply Hchanged, Hbytes;
    [exists 5120, (mkRegion 5120 5128 Heap Live); split; [reflexivity|simpl; lia]
    |intros [(root & [] & _)|(base & reg & [] & _)] ]).
Qed.

(** Two active, different FILEs may not both own the same release. *)
Example overlapping_release_rejected : forall m w p file q other base,
  libc_file_at w p = Some file -> libc_file_at w q = Some other ->
  file_handle other <> file_handle file ->
  In base (file_owned file) -> In base (file_owned other) ->
  ~ libc_release_separated m w.
Proof.
  intros m w p file q other base Hp Hq Hne Hin Hother Hsep.
  destruct (Hsep p file Hp base Hin) as (_ & Howners & _).
  exact (Howners q other Hq Hne Hother).
Qed.

(** Stable FILE capability identities cannot enter an active release
    pool, even when the memory happens to classify them as Heap. *)
Example static_handle_release_rejected : forall m w p file base,
  libc_file_at w p = Some file -> ptr_cap (libc_stdout w) = Obj base ->
  In base (file_owned file) -> ~ libc_release_separated m w.
Proof.
  intros m w p file base Hp Hcap Hin Hsep.
  destruct (Hsep p file Hp base Hin) as (_ & _ & Hnot & _).
  apply Hnot. right. left. exists (mkSpan (libc_stdout w) 0).
  split; [left; reflexivity|]. simpl. symmetry. exact Hcap.
Qed.

End LibcStreamChecks.

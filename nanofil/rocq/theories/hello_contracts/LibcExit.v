(** Hard exit as a trusted nonreturning external-call summary over the
    consumer's exact machine. This does not replace Ending's request
    interceptor or execute its soft-exit loop. Host completion remains
    independent of the request; no callback or stdout obligation is
    silently settled by _exit. *)
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics
  ExternalCalls ExternalMachine Startup Stdio Shutdown Ending Libc.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Canonical C int bits, before signed shutdown status and low-byte
    host status are distinguished. *)
Definition hard_exit_words (xs : list word) (bits : Z) : Prop :=
  xs = [WInt bits] /\ 0 <= bits < 2 ^ 32.

(** A hard request changes only the shutdown phase/status. Payload,
    registrations, consumed history and stdout all retain their identity. *)
Definition hard_exit_endpoint xs (w w' : libc_world) (bits : Z) : Prop :=
  hard_exit_words xs bits /\ fst w' = fst w /\
  exit_request HardExit (main_status bits) (snd w) (snd w').

(** Readiness alone does not exclude an already completed handoff. *)
Definition hard_exit_pre rep xs m (w : libc_world) : Prop :=
  libc_ready rep m w /\ exists bits,
    hard_exit_words xs bits /\ forall kind, shutdown_at (snd w) <> HandedOff kind.

(** Finite prefixes may be before the request, after the request but
    blocked in the host, or host-completed. Only the last emits exit.
    Observable termination leaves no mutable caller-memory continuation. *)
Definition hard_exit_prefix (host : mem -> libc_world -> Prop)
    xs m w (born : list Z) trace m' w' : Prop :=
  born = [] /\ m' = m /\
  ((trace = [] /\ w' = w) \/ exists bits,
    hard_exit_endpoint xs w w' bits /\
    (trace = [] \/ (trace = [ProcessExit (process_status (main_status bits))] /\ host m' w'))).

(** A completed host exit is not a synthetic ordinary void return. *)
Definition hard_exit_post (host : mem -> libc_world -> Prop)
    xs (m : mem) w (born : list Z) trace ending m' w' : Prop :=
  exists bits, hard_exit_endpoint xs w w' bits /\
    trace = [ProcessExit (process_status (main_status bits))] /\
    ending = CallExit (process_status (main_status bits)) /\ host m' w'.

(** The host witness is trusted behind this contract, not assumed to
    exist for each admitted call. No allocation or resource leaf is added. *)
Definition libc_hard_exit_contract rep host : contract libc_world :=
  mkContract libc_world RVoid exit_abi (hard_exit_pre rep)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (hard_exit_prefix host) (hard_exit_post host) (fun _ => False) puts_panic.

(** Only the two hard-exit aliases are summarized here. Soft exit stays
    with the explicit lifecycle, callback execution and cleanup boundary. *)
Definition libc_hard_exit_registry rep host
    (fallback : name -> option (contract libc_world)) symbol : option (contract libc_world) :=
  if name_eqb symbol (TAtom "_exit") || name_eqb symbol (TAtom "_Exit")
  then Some (libc_hard_exit_contract rep host) else fallback symbol.

(** Admission needs no host-completion promise. *)
Lemma hard_exit_admitted : forall rep host xs bits m w,
  libc_ready rep m w -> hard_exit_words xs bits ->
  (forall kind, shutdown_at (snd w) <> HandedOff kind) ->
  contract_pre (libc_hard_exit_contract rep host) xs m w.
Proof. intros. split; [exact H|]. exists bits. auto. Qed.

(** All invocation and step facts use the supplied machine's inductives. *)
Module LibcExitOn (R : Runtime) (M : ExternalMachineSig R).
Module E := M.E.

(** An admitted call has an unchanged unfinished prefix even with a
    false host witness. There is no completion/progress theorem here. *)
Theorem hard_exit_wait : forall rep host xs s m w,
  hard_exit_pre rep xs m w ->
  E.prefix (libc_hard_exit_contract rep host) xs s m w [] [] s m w.
Proof.
  intros. split; [constructor|]. split; [reflexivity|]. split; [reflexivity|]. left. auto.
Qed.

(** The explicit request cutpoint also needs no host completion. *)
Theorem hard_exit_requested : forall rep host xs bits s m w w',
  hard_exit_endpoint xs w w' bits ->
  E.prefix (libc_hard_exit_contract rep host) xs s m w [] [] s m w'.
Proof.
  intros. split; [constructor|]. split; [reflexivity|]. split; [reflexivity|]. right.
  exists bits. split; [exact H|]. left. reflexivity.
Qed.

(** Construct a completed invocation only from an independent endpoint
    host witness; arguments and phase admission are checked separately. *)
Theorem hard_exit_completed : forall rep host r args xs bits s m w w',
  exit_abi r args -> hard_exit_pre rep xs m w ->
  hard_exit_endpoint xs w w' bits -> host m w' ->
  E.invoke (libc_hard_exit_contract rep host) r args xs s m w
    [ProcessExit (process_status (main_status bits))]
    (CallExit (process_status (main_status bits))) s m w'.
Proof.
  intros rep host r args xs bits s m w w' Habi Hpre Hend Hhost.
  eapply E.invoke_normal with (born := []).
  - exact Habi.
  - exact Hpre.
  - split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    right. exists bits. split; [exact Hend|]. right. auto.
  - exists bits. auto.
  - intros why Hbad. discriminate.
  - intros values Hbad. discriminate.
  - intros status Hstatus. injection Hstatus as <-. exists []. reflexivity.
Qed.

(** No normal or resource rule can produce an ordinary return. *)
Theorem hard_exit_no_return : forall rep host r args xs s m w trace values s' m' w',
  ~ E.invoke (libc_hard_exit_contract rep host) r args xs s m w
    trace (CallReturn values) s' m' w'.
Proof.
  intros rep host r args xs s m w trace values s' m' w' Hcall. inversion Hcall; subst.
  match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
    destruct Hpost as (bits & _ & _ & Hbad & _); discriminate Hbad end.
Qed.

(** An actual completed call supplies the exact current snapshot and
    the global request relation used by Ending, not a sibling invoke. *)
Theorem hard_exit_exact : forall rep host r args xs s m w trace ending s' m' w',
  E.invoke (libc_hard_exit_contract rep host) r args xs s m w trace ending s' m' w' ->
  s' = s /\ m' = m /\ exists bits,
    hard_exit_endpoint xs w w' bits /\
    trace = [ProcessExit (process_status (main_status bits))] /\
    ending = CallExit (process_status (main_status bits)) /\ host m' w'.
Proof.
  intros rep host r args xs s m w trace ending s' m' w' Hcall.
  destruct Hcall as [trace ending s' m' w' born Habi Hpre [He Hp] Hpost Hresource Hvalues Hexit
    |why trace s' m' w' born Habi Hpre Hp Hfailure Hresource]; [|contradiction].
  destruct Hp as [Hborn [Hm _]]. subst born m'. split.
  - clear -He. induction He; [reflexivity|exact IHHe|contradiction].
  - split; [reflexivity|exact Hpost].
Qed.

(** Ordinary-machine dispatch preserves external-site precedence and
    terminates in this very machine. Ending separately intercepts these
    symbols; relating its host/representation predicates is a further
    compatibility obligation, not an automatic executor equivalence. *)
Theorem hard_exit_step : forall rep host registry ge c site xs s w trace status s' m' w',
  external_site ge c site ->
  registry (site_name site) = Some (libc_hard_exit_contract rep host) ->
  map_option (arg_x ge (fr_env (c_frame c))) (site_args site) = Some xs ->
  E.invoke (libc_hard_exit_contract rep host) (site_result site) (site_args site) xs
    s (c_mem c) w trace (CallExit status) s' m' w' ->
  M.step registry ge (M.Running (c, s) w) trace
    (M.Stopped (ExternalExit status) (M.P.I.RM.with_mem c m', s') w').
Proof. intros. eapply M.step_exit; eauto. Qed.

End LibcExitOn.

(** Controls distinguish full signed shutdown status from the host byte,
    and requests from completed termination. *)
Module LibcExitChecks.
Module M := ExternalMachine InterpRuntime.
Module X := LibcExitOn InterpRuntime M.

Definition before : libc_world :=
  (fst conversion_world, mkShutdown Handlers 0
    [mkRegistration 9 (AtExit (TAtom "cleanup"))] [8%nat]
    (mkStream ByteOriented [65; 66] false)).
Definition after : libc_world :=
  (fst before, mkShutdown (HandedOff HardExit) (-257)
    (shutdown_pending (snd before)) (shutdown_consumed (snd before))
    (shutdown_stdout (snd before))).

Example signed_status_endpoint : hard_exit_endpoint [WInt (2 ^ 32 - 257)] before after (2 ^ 32 - 257).
Proof.
  split; [split; [reflexivity|lia]|]. split; [reflexivity|].
  change (exit_request HardExit (-257) (snd before) (snd after)).
  apply request_hard. intros kind. discriminate.
Qed.

Example host_status_byte : process_status (main_status (2 ^ 32 - 257)) = 255.
Proof. vm_compute. reflexivity. Qed.

(** Pending callbacks, consumed history and outstanding bytes survive;
    no hard-exit summary pretends to run callbacks or flush. *)
Example hard_request_retains_obligations :
  shutdown_pending (snd after) = [mkRegistration 9 (AtExit (TAtom "cleanup"))] /\
  shutdown_consumed (snd after) = [8%nat] /\ outstanding (shutdown_stdout (snd after)) = [65; 66].
Proof. repeat split; reflexivity. Qed.

Example blocked_host_prefix :
  M.E.prefix (libc_hard_exit_contract (fun _ _ => True) (fun _ _ => False))
    [WInt (2 ^ 32 - 257)] InterpRuntime.start conversion_mem before [] []
    InterpRuntime.start conversion_mem after.
Proof. eapply X.hard_exit_requested. exact signed_status_endpoint. Qed.

Example false_host_no_completion : forall rep r args xs s m w trace ending s' m' w',
  ~ M.E.invoke (libc_hard_exit_contract rep (fun _ _ => False))
    r args xs s m w trace ending s' m' w'.
Proof.
  intros rep r args xs s m w trace ending s' m' w' Hcall.
  destruct (X.hard_exit_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & bits & _ & _ & _ & Hfalse). exact Hfalse.
Qed.

Example already_handed_off_rejected : forall rep m,
  ~ hard_exit_pre rep [WInt 0] m after.
Proof.
  intros rep m (_ & bits & _ & Hphase). apply (Hphase HardExit). reflexivity.
Qed.

End LibcExitChecks.

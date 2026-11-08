(** The application proof describes the checked module actually generated
    from hi.c. The shared program-fixture gate regenerates HiCode.v;
    this equality connects that artifact to the source-shaped body. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls
  Startup Stdio Shutdown ExternalMachine Composition Panics HiCode Hi Transport Program.
Import ListNotations.
Open Scope Z_scope.

(** Decoding the pinned -O output gives exactly the module used by Hi.v,
    including its literal bytes, result and actual temporary argument. *)
Theorem hi_generated_module : decode_module hi_term = Some hi_module.
Proof. reflexivity. Qed.

(** The generated main ignores its launcher words. This application-entry
    theorem is stronger than restricting them to startup_at; it does not
    prove the native launcher reaches an entry satisfying these premises. *)
Module HiProgram (R : Runtime).
Module P := Program R.

(** Defined main and an actual call frame, then independent admissibility
    and shared-classification safety for every fuel and launcher input.
    The exact runtime state after startup is retained, not reset to start.
    Opaque stdio validity and its safepoint stability remain explicit. *)
Theorem hi_launcher_words_safe : forall rep requests s_entry m w argc argv envp,
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
    rep m' w /\ stdio_ready m' w) ->
  P.H.hi_before_call rep m (program_stdio w) ->
  program_world_wf w -> orientation (program_stdout w) <> WideOriented ->
  exists fr,
    find_fn P.H.hi_genv (TAtom "main") = Some (Defined hi_function) /\
    call_frame hi_function (main_arguments argc argv envp) = Some fr /\
    forall fuel, R.ready s_entry m ->
      (forall trace c s w' site,
        P.M.run (P.registry rep requests) P.H.hi_genv
          (P.M.Running (mkConfig fr [] m fuel, s_entry) w) trace (P.M.Running (c, s) w') ->
        external_site P.H.hi_genv c site ->
        P.M.admissible (P.registry rep requests) P.H.hi_genv c w' site) /\
      (forall b host trace why ms w',
        P.run rep requests b host
          (P.Application (P.M.Running (mkConfig fr [] m fuel, s_entry) w)) trace
          (P.Application (P.M.Stopped why ms w')) -> ~ failure_ending why).
Proof.
  intros rep requests s_entry m w argc argv envp Hstable Hpre Hwf Ho.
  assert (Hentry : forall fuel, P.body_inv rep
    (P.M.Running (hi_entry m fuel, s_entry) w)).
  { intros fuel. split; [apply P.H.hi_body_entry; exact Hpre|]. auto. }
  exists (c_frame (hi_entry m 0)). split; [reflexivity|]. split; [reflexivity|].
  intros fuel Hready. split.
  - intros trace c s w' site Hrun Hsite.
    eapply P.all_calls_admissible; [exact Hstable|apply Hentry|exact Hrun|exact Hsite].
  - intros b host trace why ms w' Hrun.
    eapply P.application_stopped_never_panics with
      (st := P.Application (P.M.Running (hi_entry m fuel, s_entry) w));
      [exact Hstable|apply Hentry|exact Hrun].
Qed.

(** The named trusted successful-entry image for this generated program.
    Native launcher/libc/TLS satisfaction is trusted, probed by libc-entry.c,
    not proved by these predicates or by startup's copy lemmas. Constructor
    and environment obligations are not permissions for arbitrary callbacks. *)
Definition trusted_entry_contract rep s m w argc argv envp args environment : Prop :=
  startup_at m argc argv envp args environment /\ R.ready s m /\
  P.H.hi_before_call rep m (program_stdio w) /\
  program_world_wf w /\ orientation (program_stdout w) <> WideOriented.

(** Every successful trusted entry supplies the real application invariant,
    retaining the exact runtime and memory, for any execution fuel. *)
Lemma trusted_entry_body : forall rep s m w argc argv envp args environment fuel,
  trusted_entry_contract rep s m w argc argv envp args environment ->
  P.body_inv rep (P.M.Running (hi_entry m fuel, s) w).
Proof.
  intros rep s m w argc argv envp args environment fuel (_ & _ & Hpre & Hwf & Ho).
  split; [apply P.H.hi_body_entry; exact Hpre|]. auto.
Qed.

(** The trusted entry image suffices for application-only nonfailure.
    Entry refusal or unfinished startup is not a successful-entry image;
    this theorem promises neither native startup success nor termination. *)
Theorem trusted_entry_never_panics : forall rep requests s m w argc argv envp args environment
    fuel b host trace why ms w',
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
    rep m' w /\ stdio_ready m' w) ->
  trusted_entry_contract rep s m w argc argv envp args environment ->
  P.run rep requests b host (P.Application (P.M.Running (hi_entry m fuel, s) w)) trace
    (P.Application (P.M.Stopped why ms w')) -> ~ failure_ending why.
Proof.
  intros rep requests s m w argc argv envp args environment fuel b host trace why ms w'
    Hstable Hentry Hrun.
  eapply P.application_stopped_never_panics;
    [exact Hstable| |exact Hrun]. eapply trusted_entry_body; exact Hentry.
Qed.

(** A named trusted successful-completion specification. The explicit
    completed witness concerns this exact handoff, not mere readiness.
    Native satisfaction is probed by libc-exit.c, not proved. Finished
    remembers the handoff snapshot, not native postmortem memory, and
    completion does not assert that outstanding output was delivered. *)
Definition trusted_host_contract (completed : P.host_boundary) : P.host_boundary :=
  fun s m w sh => R.ready s m /\ stream_wf (shutdown_stdout sh) /\
    (exists kind, shutdown_at sh = HandedOff kind) /\ completed s m w sh.

(** Readiness and a handoff must not invent a missing native completion. *)
Example missing_host_completion_rejected : forall s m w sh,
  ~ trusted_host_contract (fun _ _ _ _ => False) s m w sh.
Proof. intros s m w sh (_ & _ & _ & Hmissing). exact Hmissing. Qed.

(** An explicitly witnessed completion permits one terminal observation.
    Reaching a ready handoff alone proves no native eventual completion. *)
Theorem trusted_host_completion_step : forall (completed : P.host_boundary)
    rep requests b s m w kind status pending consumed q,
  R.ready s m -> stream_wf q ->
  completed s m w (mkShutdown (HandedOff kind) status pending consumed q) ->
  P.step rep requests b (trusted_host_contract completed)
    (P.ShuttingDown s m w (mkShutdown (HandedOff kind) status pending consumed q))
    [ProcessExit (process_status status)]
    (P.Finished s m w (mkShutdown (HandedOff kind) status pending consumed q)).
Proof.
  intros completed rep requests b s m w kind status pending consumed q Hr Hwf Hcomplete.
  apply P.program_complete. split; [exact Hr|]. split; [exact Hwf|].
  split; [exists kind; reflexivity|exact Hcomplete].
Qed.

End HiProgram.

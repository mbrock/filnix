(** The application proof describes the checked module actually generated
    from hi.c. The shared program-fixture gate regenerates HiCode.v;
    this equality connects that artifact to the source-shaped body. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls
  Startup Stdio ExternalMachine Composition Panics HiCode Hi Transport Program.
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

End HiProgram.

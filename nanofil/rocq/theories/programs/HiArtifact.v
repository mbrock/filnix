(** When the test suite compiles `hi.c` with `nanofil -O`, it writes the
    checked IR module into `HiCode.v`. This module links that generated
    compiler artifact to the whole-program safety proof and defines the
    trusted entry and exit boundaries used by the C startup and shutdown
    harness. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls LibcCalls
  Startup Stdio Shutdown ExternalMachine Composition Panics HiCode Hi Transport Program.
Import ListNotations.
Open Scope Z_scope.

(** Decoding the saved compiler output yields the exact same module that
    `Hi.v` verifies, including its string literal, return type, and temporary
    names. *)
Theorem hi_generated_module : decode_module hi_term = Some hi_module.
Proof. reflexivity. Qed.

(** Because the compiled `c: main` function takes no parameters, it ignores
    whatever launcher words `argc`, `argv`, and `envp` the C runtime passes.
    This functor lifts the body safety proof to any launcher arguments over
    a given [[runtime]] R, without claiming that native startup itself
    reaches `c: main`. *)
Module HiProgram (R : Runtime).
Module P := Program R.

(** Calling the generated `c: main` function with any launcher arguments
    produces a valid call frame, and every finite run keeps external calls
    admissible without panicking, provided the entry memory and stream
    representation remain valid across safepoints. *)
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

(** The trusted entry contract packages the preconditions that the native C
    launcher and libc startup must establish before entering `c: main`. The
    C probe `libc-entry.c` checks these conditions dynamically rather than
    proving them in Rocq. *)
Definition trusted_entry_contract rep s m w argc argv envp args environment : Prop :=
  startup_at m argc argv envp args environment /\ R.ready s m /\
  P.H.hi_before_call rep m (program_stdio w) /\
  program_world_wf w /\ orientation (program_stdout w) <> WideOriented.

(** Every state satisfying the trusted entry contract also satisfies the
    whole-program invariant for any amount of execution [[fuel]]. *)
Lemma trusted_entry_body : forall rep s m w argc argv envp args environment fuel,
  trusted_entry_contract rep s m w argc argv envp args environment ->
  P.body_inv rep (P.M.Running (hi_entry m fuel, s) w).
Proof.
  intros rep s m w argc argv envp args environment fuel (_ & _ & Hpre & Hwf & Ho).
  split; [apply P.H.hi_body_entry; exact Hpre|]. auto.
Qed.

(** Once startup establishes the trusted entry contract, no finite run of
    `c: main` can end in a capability panic or contract violation. This
    theorem assumes startup succeeded and does not prove that the program
    terminates. *)
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

(** The trusted host contract wraps a completion predicate with runtime
    readiness, a well-formed output stream, and a recorded shutdown handoff.
    It captures the snapshot at process exit without claiming that buffered
    bytes were flushed natively. *)
Definition trusted_host_contract (completed : P.host_boundary) : P.host_boundary :=
  fun s m w sh => R.ready s m /\ stream_wf (shutdown_stdout sh) /\
    (exists kind, shutdown_at sh = HandedOff kind) /\ completed s m w sh.

(** Runtime readiness and a shutdown handoff alone cannot satisfy the host
    contract when the native completion predicate is false. *)
Example missing_host_completion_rejected : forall s m w sh,
  ~ trusted_host_contract (fun _ _ _ _ => False) s m w sh.
Proof. intros s m w sh (_ & _ & _ & Hmissing). exact Hmissing. Qed.

(** When an explicit completion witness holds at shutdown, the outer machine
    can take one final step into the finished state with the exit status. *)
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

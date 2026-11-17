(** We want to prove that hi_atexit never panics from the moment the
    runtime first calls into glibc, not only from the moment main
    starts. Startup makes three calls after it has created the thread:
    it initializes libc, runs the constructors and then calls main.
    The proof of the startup body takes a contract for each of those
    calls as a premise. This module proves those contracts for the
    hi_atexit image, in the world that startup ends in.

    ## The late calls

    By the time of these calls, startup has created the thread and
    registered both handlers, and nothing changes the world after that.
    Main writes to stdout, which can set errno, and it exits holding a
    lock in the thread's name. Both needs are met in that world. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Logic.
From Glibc Require Import OsWorld OsRegistry OsStart StartCtors HiAtexitGe HiAtexitModule HiAtexitInitial
  StartLogic StartCallMainSpec StartCallMain StartCtorRunnerSpec StartCtorRunner StartLibcStartMain HiAtexitStartBridge.
Import ListNotations.
Open Scope Z_scope.

Section hi.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).

(** The proofs below all talk about the same running program: hi_atexit
    after startup has made thread tb. This abbreviation names it. *)
Local Abbreviation P tb := (program_of (final_world w0 tb) glibc_os_registry hge).

(** ## The call of main *)

(** Startup calls main through `c: __libc_start_call_main`. Main's own
    contract is [hi_main_spec], and since main never returns, no exit
    status is ever allowed. *)
Definition hi_cm_spec (tb : Z) : fspec Σ :=
  start_call_main_spec (glibc_program := P tb) (TAtom "main") (hi_main_spec (final_world w0 tb))
    (fun _ => False%I).

(** Startup can call main safely once the thread exists and errno has
    its home. So the call keeps its contract in the final world when the
    image's `c: __libc_errno` is the world's errno cell and the thread
    object has an address. *)
Lemma hi_call_main_has_spec tb :
  lookup (TAtom "__libc_errno") hi_globals = Some (ow_errno_cell w0) -> 0 < tb < 2 ^ 64 ->
  HasSpec glibc_os_registry (os_wi (final_world w0 tb)) hge
    (TAtom "glibc_libc_start#__libc_start_call_main") (hi_cm_spec tb).
Proof using Type.
  intros He Htb. destruct (hi_final_world_facts w0 tb He Htb) as (Herr & Hself & _).
  pose proof (hi_main_has_spec (final_world w0 tb) Herr Hself) as Hmain.
  pose proof (hi_exit_never_false (final_world w0 tb)) as Hexit.
  assert (Hdef : Defines hge "glibc_libc_start#__libc_start_call_main" start_call_main_fn)
    by (vm_compute; reflexivity).
  exact (start_call_main_has_spec (glibc_program := P tb) (TAtom "main")
    (hi_main_spec (final_world w0 tb)) (fun _ => False%I) eq_refl
    ltac:(split; vm_compute; reflexivity)).
Qed.

(** ## The constructor runner *)

(** The image's runner meets the runner's contract in the final world. *)
Lemma hi_ctor_runner_has_spec tb :
  HasSpec glibc_os_registry (os_wi (final_world w0 tb)) hge ctor_runner_name
    (ctor_runner_spec (glibc_program := P tb)).
Proof using Type.
  assert (Hdef : Defines hge "zrun_deferred_global_ctors" start_ctor_runner_fn)
    by (vm_compute; reflexivity).
  exact (ctor_runner_has_spec (glibc_program := P tb)).
Qed.

End hi.

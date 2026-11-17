(** We want to prove that GNU Hello never panics from the moment the
    runtime first calls into glibc, not only from the moment main
    starts. After it has created the thread, startup initializes libc,
    runs the constructors and then calls main. The proof of the startup
    body takes a contract for each of those calls as a premise.
    [StartMainHiAtexit](../startup/StartMainHiAtexit.v) proves them for
    the hi_atexit image. This module proves the call of main and the
    constructor runner for Hello, in the world that startup ends in.

    Some library calls that Hello's main makes, such as the locale calls,
    are not proved yet. Main's contract in
    [HelloStartBridge](HelloStartBridge.v) takes their contracts as
    parameters, and so does this module. The facts about the program
    are computed from the linked module, whatever memory the loader
    builds for it. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic HelloMain.
From Glibc Require Import OsWorld OsRegistry OsStart StartCtors StartLogic StartCallMainSpec StartCallMain
  StartCtorRunnerSpec StartCtorRunner StartLibcStartMain HelloImageModule HelloImageFnLink
  HelloGlibcDebts HelloGlibcLibsT HelloStartBridge.
Import ListNotations.
Open Scope Z_scope.

Section hello.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Context (g : list (name * ptr)) (m : mem) (fr : word -> mem -> option (res unit * mem)).
Context (Hi : initial_memory hello_image_module = Some (g, m)).

(** This is the linked Hello program. *)
Local Abbreviation hello_ge := (mkGenv hello_image_module g fr).

(** Every exit of Hello goes through `c: exit`, which never returns. *)
Lemma hello_exit_never_false w :
  HasSpec glibc_os_registry (os_wi w) hello_ge (TAtom "__GI_exit") (exit_never_spec (Σ := Σ) (fun _ => False%I)).
Proof using Type.
  intros st. eexists. split; [vm_compute; reflexivity|].
  split; [eexists; reflexivity|]. intros fr' Φ _. cbn [fs_pre exit_never_spec]. iIntros "[]".
Qed.

(** The constructor runner of the image meets the runner's contract in
    the final world, for every thread that startup makes. *)
Lemma hello_ctor_runner_has_spec tb :
  HasSpec glibc_os_registry (os_wi (final_world w0 tb)) hello_ge ctor_runner_name
    (ctor_runner_spec (glibc_program := program_of (final_world w0 tb) glibc_os_registry hello_ge)).
Proof using Type.
  assert (Hdef : Defines hello_ge "zrun_deferred_global_ctors" start_ctor_runner_fn)
    by (vm_compute; reflexivity).
  exact (ctor_runner_has_spec (glibc_program := program_of (final_world w0 tb) glibc_os_registry hello_ge)).
Qed.

(** ## The call of main

    Startup does not know in advance which thread it will make, and the
    world after startup names that thread. The open library calls must
    therefore have contracts for every thread, but they need to hold
    only for the threads that startup can make, which fit below 2^48. *)

Context (o : hello_objs) (debt : forall tb, HelloCore (final_world w0 tb) hello_ge o) (X0 X : iProp Σ)
  (Lb : forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 ->
     HelloLibs (final_world w0 tb) hello_ge o (hd_priv (final_world w0 tb) hello_ge o (debt tb)) X0 X)
  (Hy : hello_layout hello_ge o).

Local Abbreviation P tb := (program_of (final_world w0 tb) glibc_os_registry hello_ge).

(** Startup calls main through `c: __libc_start_call_main`. Main's
    contract is [hello_main_spec], and since main never returns, no
    exit status is ever allowed. *)
Definition hello_cm_spec (tb : Z) : fspec Σ :=
  start_call_main_spec (glibc_program := P tb) (TAtom "main")
    (hello_main_spec (final_world w0 tb) hello_ge o (debt tb) X0) (fun _ => False%I).

(** Whatever thread startup makes, calling main through
    `c: __libc_start_call_main` is safe and meets this contract. *)
Lemma hello_call_main_has_spec tb : 0 < tb -> tb + 2496 <= 2 ^ 48 ->
  HasSpec glibc_os_registry (os_wi (final_world w0 tb)) hello_ge
    (TAtom "glibc_libc_start#__libc_start_call_main") (hello_cm_spec tb).
Proof using Hi Lb Hy.
  intros Ht0 Ht1.
  pose proof (hello_main_has_spec (final_world w0 tb) hello_ge o (debt tb) X0 X (Lb tb Ht0 Ht1) Hy
    (hello_image_main g fr)) as Hmain.
  pose proof (hello_exit_never_false (final_world w0 tb)) as Hexit.
  assert (Hdef : Defines hello_ge "glibc_libc_start#__libc_start_call_main" start_call_main_fn)
    by (vm_compute; reflexivity).
  assert (Hext : os_ext hello_ge "zthread_self_cookie").
  { assert (C : absent_ok hello_image_module "zthread_self_cookie" = true) by (vm_compute; reflexivity).
    exact (absent_ok_sound _ _ _ fr _ Hi C). }
  exact (start_call_main_has_spec (glibc_program := P tb) (TAtom "main")
    (hello_main_spec (final_world w0 tb) hello_ge o (debt tb) X0) (fun _ => False%I) eq_refl Hext).
Qed.

End hello.

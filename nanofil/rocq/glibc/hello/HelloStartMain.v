(** We want to prove that GNU Hello never panics from the moment the
    runtime first calls into glibc, not only from the moment main
    starts. After it has created the thread, startup initializes libc,
    runs the constructors and then calls main. The proof of the startup
    body takes a contract for each of those calls as a premise.
    [StartMainHiAtexit](../hi_atexit/StartMainHiAtexit.v) proves them for
    the hi_atexit image. This module proves early init, the
    constructor runner and the call of main for Hello, in the world that startup ends in.

    Main's contract in [HelloStartBridge](HelloStartBridge.v) takes
    the library proofs as parameters, and so does this module. The facts about the program
    are computed from the linked module, whatever memory the loader
    builds for it. *)

From Glibc Require Import HelloObjects GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic.
From Glibc Require Import OsWorld OsRegistry OsStart StartCtors StartLogic StartCallMainSpec StartCallMain
  StartCtorRunnerSpec StartCtorRunner StartLibcStartMain HelloImageModule HelloImageFnLink ImageEraseMem
  HelloGlibcDebts HelloStartBridge HelloImageEarly
  StartCode StartTunableGetVal StartTunableIsInitialized
  StartClockGettime StartGetrlimit StartCtypeInit
  StartPthreadTunables StartPtmallocInit
  StartEarlyInitSpec StartEarlyInit StartTlsInitTpSpec StartTlsInitTp StartSetupTlsSpec StartSetupTls.
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

(** This tactic proves that a symbol exists. It computes the pointer
    first, because computing with an unknown pointer does not end. *)
Local Ltac has_sym :=
  lazymatch goal with |- exists p, lookup ?n ?g = Some p =>
    let v := eval vm_compute in (lookup n g) in
    lazymatch v with Some ?p => exists p; vm_compute; reflexivity end end.

(** Startup sets up the allocator, the character tables and the thread
    defaults before it runs any constructor. The function that does so,
    `c: __libc_early_init`, keeps its contract in the final world,
    because every function it calls is Hello's own code and every
    system call it makes is left to the runtime. *)
Lemma hello_early_init_has_spec tb :
  HasSpec glibc_os_registry (os_wi (final_world w0 tb)) hello_ge (TAtom "__libc_early_init")
    (early_init_spec (glibc_program := program_of (final_world w0 tb) glibc_os_registry hello_ge)).
Proof using Hi.
  pose (Pg := program_of (final_world w0 tb) glibc_os_registry hello_ge).
  destruct (hello_loaded_tables g m Hi) as [Eg _].
  assert (X : forall s, absent_ok hello_image_module s = true -> os_ext hello_ge s)
    by (intros s Hs; exact (absent_ok_sound _ _ _ fr _ Hi Hs)).
  assert (D1 : Defines hello_ge "__tunable_get_val" start_tunable_get_val_fn) by (vm_compute; reflexivity).
  assert (D2 : Defines hello_ge "__tunable_is_initialized" start_tunable_is_initialized_fn) by (vm_compute; reflexivity).
  assert (D3 : Defines hello_ge "__GI___clock_gettime" start_clock_gettime_fn) by (vm_compute; reflexivity).
  assert (D4 : Defines hello_ge "__GI___getrlimit" start_getrlimit_fn) by (vm_compute; reflexivity).
  assert (D5 : Defines hello_ge "__GI___ctype_init" start_ctype_init_fn) by (vm_compute; reflexivity).
  assert (D6 : Defines hello_ge "__pthread_tunables_init" start_pthread_tunables_init_fn) by (vm_compute; reflexivity).
  assert (D7 : Defines hello_ge "__ptmalloc_init" start_ptmalloc_init_fn) by (vm_compute; reflexivity).
  assert (D8 : Defines hello_ge "__getrandom_early_init" start_getrandom_early_init_fn) by (vm_compute; reflexivity).
  assert (D9 : Defines hello_ge "__libc_early_init" start_early_init_fn) by (vm_compute; reflexivity).
  pose proof (tunable_size_has_spec (glibc_program := Pg)) as Hsize.
  pose proof (tunable_int_has_spec (glibc_program := Pg)) as Hint.
  pose proof (tunable_is_initialized_has_spec (glibc_program := Pg)) as Hinit.
  pose proof (clock_gettime_has_spec (glibc_program := Pg) eq_refl
    (X "zsys_clock_gettime" ltac:(vm_compute; reflexivity))) as Hclock.
  pose proof (getrlimit_has_spec (glibc_program := Pg) eq_refl
    (X "zsys_getrlimit" ltac:(vm_compute; reflexivity))) as Hrlim.
  pose proof (ctype_init_has_spec (glibc_program := Pg)) as Hctype.
  assert (Hcb : exists cb, lookup (TAtom "glibc_pthread_mutex_conf#_dl_tunable_set_mutex_spin_count")
    (ge_globals hello_ge) = Some cb) by (cbn [ge_globals]; rewrite Eg; has_sym).
  destruct Hcb as [cb Hcb].
  pose proof (pthread_tunables_init_has_spec (glibc_program := Pg) cb Hcb) as Hpth.
  pose proof (getrandom_early_init_has_spec (glibc_program := Pg)) as Hgre.
  assert (Hcbs : Forall (fun n => exists p, lookup (TAtom n) (ge_globals hello_ge) = Some p) pm_callbacks)
    by (cbn [ge_globals]; rewrite Eg; repeat constructor; has_sym).
  pose proof (ptmalloc_init_has_spec (glibc_program := Pg) eq_refl
    (X "zsys_getrandom" ltac:(vm_compute; reflexivity)) Hcbs) as Hpm.
  exact (early_init_has_spec (glibc_program := Pg)).
Qed.

(** ## The thread

    Before it calls early init, startup makes the thread through
    `c: __libc_setup_tls`, which sets the thread's cookie and then calls
    `c: __tls_init_tp` in the world that names the new thread. Both are
    Hello's own code, and the thread calls they make are left to the
    runtime. *)

(** For every thread object tb, `c: __tls_init_tp` meets its contract in
    the world whose cookie names tb. *)
Lemma hello_tls_init_tp_has_spec tb :
  HasSpec glibc_os_registry (os_wi (start_world w0 (mkPtr tb (Obj tb)) false false)) hello_ge
    (TAtom "__tls_init_tp") (tls_init_tp_spec hello_ge tb).
Proof using Hi.
  assert (X : forall s, absent_ok hello_image_module s = true -> os_ext hello_ge s)
    by (intros s Hs; exact (absent_ok_sound _ _ _ fr _ Hi Hs)).
  assert (D : Defines hello_ge "__tls_init_tp" start_tls_init_tp_fn) by (vm_compute; reflexivity).
  exact (tls_init_tp_has_spec (glibc_program := program_of (start_world w0 (mkPtr tb (Obj tb)) false false)
    glibc_os_registry hello_ge) tb eq_refl eq_refl eq_refl
    (X "zthread_self_cookie" ltac:(vm_compute; reflexivity)) (X "zthread_self_id" ltac:(vm_compute; reflexivity))
    (X "zthread_self" ltac:(vm_compute; reflexivity)) eq_refl).
Qed.

(** With the key k of the world's ghost state, `c: __libc_setup_tls`
    meets its contract in the world that startup starts from. *)
Lemma hello_setup_tls_has_spec k :
  HasSpec glibc_os_registry (os_wi_start w0 k) hello_ge (TAtom "__libc_setup_tls") (setup_tls_spec hello_ge k).
Proof using Hi.
  apply (setup_tls_has_spec glibc_os_registry hello_ge w0 k hello_tls_init_tp_has_spec).
  - vm_compute. reflexivity.
  - reflexivity.
  - assert (C : absent_ok hello_image_module "zthread_set_self_cookie" = true) by (vm_compute; reflexivity).
    exact (absent_ok_sound _ _ _ fr _ Hi C).
Qed.

(** ## The call of main

    Startup does not know in advance which thread it will make, and the
    world after startup names that thread. The library calls must
    therefore have contracts for every thread, but they need to hold
    only for the threads that startup can make, which fit below 2^48. *)

Context (o : hello_objs) (priv : Z -> iProp Σ) (X0 X : iProp Σ)
  (Lb : forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 ->
     HelloLibs (final_world w0 tb) hello_ge o (priv tb) X0 X)
  (Hy : hello_layout hello_ge o).

Local Abbreviation P tb := (program_of (final_world w0 tb) glibc_os_registry hello_ge).

(** Startup calls main through `c: __libc_start_call_main`. Main's
    contract is [hello_main_spec], and since main never returns, no
    exit status is ever allowed. *)
Definition hello_cm_spec (tb : Z) : fspec Σ :=
  start_call_main_spec (glibc_program := P tb) (TAtom "main")
    (hello_main_spec (final_world w0 tb) hello_ge o (priv tb) X0) (fun _ => False%I).

(** Whatever thread startup makes, calling main through
    `c: __libc_start_call_main` is safe and meets this contract. *)
Lemma hello_call_main_has_spec tb : 0 < tb -> tb + 2496 <= 2 ^ 48 ->
  HasSpec glibc_os_registry (os_wi (final_world w0 tb)) hello_ge
    (TAtom "glibc_libc_start#__libc_start_call_main") (hello_cm_spec tb).
Proof using Hi Lb Hy.
  intros Ht0 Ht1.
  pose proof (hello_main_has_spec (final_world w0 tb) hello_ge o (priv tb) X0 X (Lb tb Ht0 Ht1) Hy
    (hello_image_main g fr)) as Hmain.
  pose proof (hello_exit_never_false (final_world w0 tb)) as Hexit.
  assert (Hdef : Defines hello_ge "glibc_libc_start#__libc_start_call_main" start_call_main_fn)
    by (vm_compute; reflexivity).
  assert (Hext : os_ext hello_ge "zthread_self_cookie").
  { assert (C : absent_ok hello_image_module "zthread_self_cookie" = true) by (vm_compute; reflexivity).
    exact (absent_ok_sound _ _ _ fr _ Hi C). }
  exact (start_call_main_has_spec (glibc_program := P tb) (TAtom "main")
    (hello_main_spec (final_world w0 tb) hello_ge o (priv tb) X0) (fun _ => False%I) eq_refl Hext).
Qed.

End hello.

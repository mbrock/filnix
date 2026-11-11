(** The linked hi_atexit program cannot panic after main begins in the
    prepared state defined here. Preparation starts from the actual
    loader image and succeeds. The resulting memory supplies all the
    state needed by main and exit, so safety requires no further
    assumptions about library calls.

    The theorem starts at initialized main, not at process launch. It
    does not prove libc startup or show that unchanged --ctors performs
    these writes. Output and closing may fail without invalidating
    safety. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From Nanofil Require Import Values Memory Runtime Run Pieces Heap Language Logic.
From Glibc Require Import OsWorld OsRegistry HiAtexitBase HiAtexitGe HiAtexitModule
  HiAtexitInitial HiAtexitPrepare HiAtexitEntryMemory HiAtexitEntryImage
  HiAtexitMain HiAtexitWorld HiAtexitEntryOwn.
Open Scope Z_scope.
Import HLG HLG.L.

(** Preparation really succeeds on the linked image. The resulting
    objects do not overlap, its allocation cursor is ready, and its
    memory satisfies both the heap assertions and OS checks. *)
Theorem hi_atexit_initialized_entry :
  initial_memory hi_module = Some (hi_globals, hi_m0) /\
  hi_host_prepare hi_m0 InterpRuntime.start hi_entry_saved_jmp =
    Some (hi_prepared_memory, 4294969872, hi_entry_world 4294967296) /\
  InterpRuntime.ready 4294969872 hi_prepared_memory /\
  live_disjoint hi_prepared_memory /\
  agrees hi_prepared_memory (list_to_map hi_entry_ps) /\
  os_wi (hi_entry_world 4294967296) hi_prepared_memory (hi_entry_world 4294967296)
    (list_to_map hi_entry_ps).
Proof.
  split; [exact hi_initial|]. split; [exact (hi_host_prepare_success _)|].
  split; [exact (hi_entry_ready _)|]. split; [exact (hi_entry_live_disjoint _)|].
  split; [exact hi_entry_heap_agrees|]. apply hi_entry_os_wi. exact hi_entry_heap_agrees.
Qed.

(** The adequacy construction uses only invariant and heap resources. *)
Definition hi_atexitΣ : gFunctors := #[invΣ; gen_heapΣ piece pval].

(** The chosen resource universe supports Iris invariants. *)
#[local] Instance hi_atexit_inv : invGpreS hi_atexitΣ.
Proof. apply subG_invΣ. apply _. Qed.

(** Iris can record ownership of the prepared memory in this universe. *)
#[local] Instance hi_atexit_heap : gen_heapGpreS piece pval hi_atexitΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** At every fuel, no stopped labelled execution from the prepared
    main entry has a failure ending: no panic, stuck step or rejected
    contract. There is no assumed resource package or library-safety
    premise. The named preparation is the entry boundary, not an
    asserted machine prefix from the untouched loader image. *)
Theorem hi_atexit_never_panics fuel :
  labelled_safe glibc_os_registry hge hi_main_frame hi_prepared_memory 4294969872
    (hi_entry_world 4294967296) fuel (fun _ => True).
Proof.
  apply (heap_labelled_safe hi_atexitΣ glibc_os_registry (os_wi (hi_entry_world 4294967296))
    hge hi_main_frame hi_prepared_memory 4294969872 (hi_entry_world 4294967296)
    (list_to_map hi_entry_ps) (fun _ => True)).
  - exact (hi_entry_ready _).
  - exact (hi_entry_live_disjoint _).
  - exact hi_entry_heap_agrees.
  - apply hi_entry_os_wi. exact hi_entry_heap_agrees.
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact hi_entry_nodup].
    iIntros "H". iMod (hi_entry_own with "H") as "H".
    iApply (hi_main_wp with "H"); [reflexivity|cbn; lia| |].
    + apply hi_loop_env. reflexivity.
    + apply hi_exit_lock_env; [reflexivity|]. cbn. lia.
Qed.

(** Before GNU Hello's `c: main` runs, startup calls `c: __libc_early_init`
    and then the constructor runner, and both calls take globals of glibc
    from the memory that the loader builds.
    [StartImageEarly](../startup/StartImageEarly.v) lists those globals
    over records of addresses and shows that the hi_atexit image holds
    them. This module shows the same for Hello, so that the proof of
    Hello's startup can make the two calls.

    The memory of the whole Hello image is too large to compute, so the
    module takes the route of [HelloImageCpu](HelloImageCpu.v). It loads
    a copy of the image in which every other object is blank, checks the
    lists there, and carries the result over to the real memory. The
    records are computed from the loader's symbols and regions, so a
    relink of Hello changes no line here. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsWorld OsRegistry StartCtors StartTunableGetValSpec StartCtypeInitSpec
  StartPtmallocInitSpec StartEarlyInitSpec StartImageUnique StartImageEarly.
From Glibc Require Import HelloImageErase HelloImageEraseMem HelloImagePieces HelloImageModule HelloImageLoad.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## The records and the lists *)

Definition hello_ei_objs : ei_objs := Eval vm_compute in ei_objs_in img_globals img_regions.
Definition hello_ct_objs : ct_objs := Eval vm_compute in ct_objs_in img_globals img_regions.
Definition hello_pm_objs : pm_objs := Eval vm_compute in pm_objs_in img_globals img_regions.
Definition hello_runner_objs := Eval vm_compute in runner_objs_in img_globals img_regions.

Definition hello_early_ps : list (piece * pval) := early_ps hello_ei_objs hello_pm_objs hello_ct_objs.
Definition hello_runner_ps : list (piece * pval) := runner_ps hello_runner_objs.

(** Whatever memory the loader builds for Hello, its symbols and its
    regions are the ones that [HelloImageLoad](HelloImageLoad.v)
    computes. *)
Lemma hello_loaded_tables g m : initial_memory hello_image_module = Some (g, m) ->
  g = img_globals /\ m_regions m = img_regions.
Proof.
  intros Hi.
  assert (C : option_map (fun gm => (fst gm, m_regions (snd gm))) (initial_memory hello_image_module) =
              Some (img_globals, img_regions)) by (rewrite hello_loaded_eq; vm_compute; reflexivity).
  rewrite Hi in C. cbn [option_map fst snd] in C. injection C as -> ->. split; reflexivity.
Qed.

(** ## The checks on the smaller copies

    The lists are checked in copies of the image that are small enough
    to compute. One copy keeps the objects of early init and the runner.
    Reading a byte of a copy costs a step for every byte that the copy
    keeps, so the 2,300 pieces of the main arena are checked in a second
    copy that keeps only the arena. *)

Definition hello_early_skel : module := Eval vm_compute in erase early_keep hello_image_module.
Lemma hello_early_skel_eq : erase early_keep hello_image_module = hello_early_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_early_kept : module := Eval vm_compute in kept_objects early_keep hello_image_module.
Lemma hello_early_kept_incl : incl hello_early_kept hello_image_module.
Proof.
  assert (E : kept_objects early_keep hello_image_module = hello_early_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Definition hello_arena_skel : module := Eval vm_compute in erase arena_keep hello_image_module.
Lemma hello_arena_skel_eq : erase arena_keep hello_image_module = hello_arena_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_arena_kept : module := Eval vm_compute in kept_objects arena_keep hello_image_module.
Lemma hello_arena_kept_incl : incl hello_arena_kept hello_image_module.
Proof.
  assert (E : kept_objects arena_keep hello_image_module = hello_arena_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_early_check :
  match initial_memory hello_early_skel with
  | Some (g, m') => pieces_ok early_keep hello_early_kept g m'
      (early_main_ps hello_ei_objs hello_pm_objs hello_ct_objs ++ hello_runner_ps)
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma hello_arena_check :
  match initial_memory hello_arena_skel with
  | Some (g, m') => pieces_ok arena_keep hello_arena_kept g m' (arena_ps hello_pm_objs)
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The lists in the real memory *)

(** Hello starts with both lists, in whatever memory the loader builds
    for it, and neither list names a piece twice. *)
Theorem hello_early_runner_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_early_ps /\ all_agree m hello_runner_ps.
Proof.
  intros E.
  destruct (image_pieces early_keep hello_early_kept hello_image_module g m
    (early_main_ps hello_ei_objs hello_pm_objs hello_ct_objs ++ hello_runner_ps)
    hello_early_kept_incl E hello_image_names hello_image_zero) as (m1 & E1 & _ & P1).
  destruct (image_pieces arena_keep hello_arena_kept hello_image_module g m (arena_ps hello_pm_objs)
    hello_arena_kept_incl E hello_image_names hello_image_zero) as (m2 & E2 & _ & P2).
  pose proof hello_early_check as C1. rewrite <- hello_early_skel_eq, E1 in C1.
  pose proof hello_arena_check as C2. rewrite <- hello_arena_skel_eq, E2 in C2.
  apply P1, all_agree_app in C1 as [A1 A3]. split; [|exact A3].
  unfold hello_early_ps, early_ps. apply all_agree_app. split; [exact A1 | exact (P2 C2)].
Qed.

Lemma hello_early_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_early_ps.
Proof. intros E. exact (proj1 (hello_early_runner_agree g m E)). Qed.

Lemma hello_runner_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_runner_ps.
Proof. intros E. exact (proj2 (hello_early_runner_agree g m E)). Qed.

Lemma hello_early_nodup : NoDup hello_early_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

Lemma hello_runner_nodup : NoDup hello_runner_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

(** ## The pure premises *)

Section hello.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Context (g : list (name * ptr)) (m : mem) (fr : word -> mem -> option (res unit * mem)).
Context (Hi : initial_memory hello_image_module = Some (g, m)).
Local Notation hello_program := (program_of w0 glibc_os_registry (mkGenv hello_image_module g fr)).

(** Hello's symbols name the objects of early init where the records
    say, and each object is aligned and large enough. The allocator's
    `c: errno` must be the world's. *)
Lemma hello_early_ok :
  ow_errno w0 = Some (mkPtr (pm_eb hello_pm_objs) (Obj (pm_eb hello_pm_objs))) ->
  ei_ok (glibc_program := hello_program) hello_ei_objs /\ ct_ok (glibc_program := hello_program) hello_ct_objs /\
  pm_ok (glibc_program := hello_program) hello_pm_objs /\
  tunable_slot_ok (glibc_program := hello_program) (pm_tl hello_pm_objs) (pm_tlreg hello_pm_objs) 27.
Proof using Hi.
  intros Herr. destruct (hello_loaded_tables g m Hi) as [-> _].
  unfold ei_ok, ct_ok, pm_ok, tunable_slot_ok, program_ge, program_world. cbn [program_of ge_globals].
  cbv [pm_size_ids pm_int_ids app].
  repeat match goal with
  | |- _ /\ _ => split
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor
  end.
  all: first [exact Herr | vm_compute; reflexivity | vm_compute; congruence].
Qed.

(** Hello's symbols name the runner's flag and table where the record
    says, and both fit. *)
Lemma hello_runner_ok :
  lookup ctor_flag_name g = Some (mkPtr hello_runner_objs.1.1 (Obj hello_runner_objs.1.1)) /\
  lookup ctor_table_name g = Some (mkPtr hello_runner_objs.2.1 (Ro hello_runner_objs.2.1)) /\
  hello_runner_objs.1.1 + 1 <= r_end hello_runner_objs.1.2 /\ hello_runner_objs.2.1 mod 8 = 0 /\
  hello_runner_objs.2.1 + ctor_table_size 3 <= r_end hello_runner_objs.2.2.
Proof using Hi.
  destruct (hello_loaded_tables g m Hi) as [-> _].
  repeat split; first [vm_compute; reflexivity | vm_compute; congruence].
Qed.

End hello.

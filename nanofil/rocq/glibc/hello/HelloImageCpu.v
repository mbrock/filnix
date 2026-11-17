(** The startup code of glibc calls `c: init_cpu_features`, and the
    contract of that call in [CpuInitSpec](../startup/CpuInitSpec.v)
    asks for eighteen global objects.
    [StartImageCpu](../startup/StartImageCpu.v) shows that the
    hi_atexit program starts with those objects in a state that the
    contract accepts. This module shows the same for GNU Hello, so
    that the proof of Hello's startup can make the call.

    The memory of the whole Hello image is too large to compute. The
    module therefore takes the route of
    [HelloImageCtors](HelloImageCtors.v). It loads a copy of the image
    in which every other object is blank. It reads the eighteen
    objects in the copy and checks them there. A theorem about the
    copy then carries the result over to the real memory.

    Every address comes from the record [hello_icf_objs] of
    [CpuHello](../startup/CpuHello.v), which is computed from the
    loaded image. So a relink of Hello changes no line here. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list_numbers.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv HelloImageErase HelloImageEraseMem HelloImagePieces
  HelloImageModule HelloImageLoad CpuInitSpec CpuPlace CpuHello StartImageUnique StartImageCpu.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv.
Open Scope Z_scope.

(** ## The smaller copy of the image *)

(** This module is the Hello image with every object blank except the
    eighteen. The function [icf_keep] says which objects stay. *)
Definition hello_cpu_skel : module := Eval vm_compute in erase icf_keep hello_image_module.

(** The constant above is what erasing the image gives. *)
Lemma hello_cpu_skel_eq : erase icf_keep hello_image_module = hello_cpu_skel.
Proof. vm_compute. reflexivity. Qed.

(** These are the eighteen objects as items of the image. *)
Definition hello_cpu_kept : module := Eval vm_compute in kept_objects icf_keep hello_image_module.

(** Each of those items is an item of the image. *)
Lemma hello_cpu_kept_incl : incl hello_cpu_kept hello_image_module.
Proof.
  assert (E : kept_objects icf_keep hello_image_module = hello_cpu_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

(** This memory is what the loader builds for the smaller copy. *)
Definition hello_cpu_mem : mem :=
  match initial_memory hello_cpu_skel with Some (_, m) => m | None => empty_mem end.

(** ## The contents of the eighteen objects *)

(** These are the 4896 bytes of the tunable table in Hello. *)
Definition hello_tunable_bytes : list Z := Eval vm_compute in
  bytes_at hello_cpu_mem (icf_tl hello_icf_objs) 4896.

(** These are the bytes of the fifteen small globals in Hello, in the
    order of [icf_small_globals]. *)
Definition hello_small_bytes : list (list Z) := Eval vm_compute in
  zip_with (fun q g => bytes_at hello_cpu_mem (fst q) (snd g)) (icf_small hello_icf_objs) icf_small_globals.

(** This list says what the eighteen objects hold when Hello starts.
    The feature structure holds 528 zero bytes. The tunable table and
    the small globals hold the bytes that were read above. The
    descriptor table holds the rows that the function searches. *)
Definition hello_cpu_globals_ps : list (piece * pval) :=
  obj_ps (icf_cf hello_icf_objs, icf_cfreg hello_icf_objs) (repeat 0 528%nat) ++
  obj_ps (icf_tl hello_icf_objs, icf_tlreg hello_icf_objs) hello_tunable_bytes ++
  obj_ps (icf_kn hello_icf_objs, icf_knreg hello_icf_objs) icf_known_bytes ++
  concat (zip_with obj_ps (icf_small hello_icf_objs) hello_small_bytes).

(** ## The list against the loaded program *)

(** The smaller copy holds every entry of the list, and each entry
    lies in one of the eighteen objects. *)
Lemma hello_cpu_check :
  match initial_memory hello_cpu_skel with
  | Some (g, m') => pieces_ok icf_keep hello_cpu_kept g m' hello_cpu_globals_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** Hello really starts with these contents, in whatever memory the
    loader builds for it. The theorem [image_pieces] carries the check
    on the copy over to that memory. *)
Theorem hello_cpu_globals_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_cpu_globals_ps.
Proof.
  intros E.
  destruct (image_pieces icf_keep hello_cpu_kept hello_image_module g m hello_cpu_globals_ps
    hello_cpu_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_cpu_check as C. rewrite <- hello_cpu_skel_eq in C. rewrite E' in C. exact (P C).
Qed.

(** No object and no byte occurs twice in the list, so a proof can
    own all of it at once. *)
Lemma hello_cpu_globals_nodup : NoDup hello_cpu_globals_ps.*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.

(** The tunable table of Hello has contents that the contract allows.
    It has its full size, it holds only bytes, and the type codes and
    cleared flags are where the function reads them. *)
Lemma hello_tunable_ok : icf_tunables_ok hello_tunable_bytes.
Proof.
  split; [vm_compute; reflexivity|]. split; [apply bytes_ok; vm_compute; reflexivity|].
  apply fixed_in_ok. vm_compute. reflexivity.
Qed.

(** ## From the list to the precondition *)

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Context (g : list (name * ptr)) (fr : word -> mem -> option (res unit * mem)).
Local Notation hello_program := (program_of w0 glibc_os_registry (mkGenv hello_image_module g fr)).

(** The function `c: init_cpu_features` reads the saved XSAVE bit of
    the feature structure and the type codes of the tunable table, and
    it searches the rows of the descriptor table. In Hello the bit
    starts clear, the codes start in place and the rows are there. So
    the function may be called on the eighteen objects as Hello starts
    with them. *)
Lemma hello_cpu_globals_own :
  pts hello_cpu_globals_ps ⊢ icf_owns (glibc_program := hello_program) hello_icf_objs.
Proof using Type.
  assert (Hk : length icf_known_bytes = 544%nat) by (vm_compute; reflexivity).
  pose proof (smalls_own w0 (mkGenv hello_image_module g fr) icf_small_globals (icf_small hello_icf_objs)
                hello_small_bytes ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hsm.
  rewrite /hello_cpu_globals_ps. revert Hsm.
  generalize (concat (zip_with obj_ps (icf_small hello_icf_objs) hello_small_bytes)). intros sm Hsm.
  rewrite !pts_app !obj_ps_own (repeat_length 0 528) Hk. cbn [fst snd].
  iIntros "((Lcf & Hcf & Acf) & (Ltl & Htl & Atl) & (Lkn & Hkn & Akn) & Hs)".
  rewrite /icf_owns. iFrame "Lcf Ltl Lkn". iSplitL "Hcf Acf".
  { iExists (repeat 0 528%nat), (repeat CNone 528%nat). rewrite pts_app. iFrame "Hcf Acf". iPureIntro.
    split; [apply repeat_length|]. split; [apply repeat_length|].
    split; [apply bytes_ok; vm_compute; reflexivity|]. vm_compute. discriminate. }
  iSplitL "Htl Atl".
  { iExists hello_tunable_bytes, (repeat CNone (length hello_tunable_bytes)). rewrite pts_app. iFrame "Htl Atl".
    iPureIntro. split; [exact hello_tunable_ok|]. rewrite repeat_length. vm_compute. reflexivity. }
  iSplitL "Hkn Akn"; [rewrite /icf_known; iFrame "Hkn Akn"|].
  iApply (Hsm with "Hs").
Qed.

End image.

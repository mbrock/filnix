(** The initial hi_atexit image supplies the eighteen objects read by CPU initialization. *)

From Glibc Require Fix.
From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list_numbers.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv HiAtexitModule HiAtexitGe HiAtexitInitial
  ImageErase ImageEraseMem ImagePieces CpuInitSpec CpuHiAtexit StartImageUnique.
From Glibc Require Import ImageObjectPieces.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv.
Open Scope Z_scope.
From Glibc Require Import StartImageCpu.

(** These are the 4896 bytes of the tunable table in hi_atexit. *)
Definition hi_tunable_bytes : list Z := Eval vm_compute in
  bytes_at (hi_erased icf_keep) (icf_tl hi_icf_objs) 4896.

(** These are the bytes of the fifteen small globals in hi_atexit, in
    the order of [icf_small_globals]. *)
Definition hi_small_bytes : list (list Z) := Eval vm_compute in
  zip_with (fun q g => bytes_at (hi_erased icf_keep) (fst q) (snd g)) (icf_small hi_icf_objs) icf_small_globals.

(** This list says what the eighteen objects hold when hi_atexit
    starts. The feature structure holds 528 zero bytes. The tunable
    table and the small globals hold the bytes that were read above.
    The descriptor table holds the rows that the function searches. *)
Definition hi_cpu_globals_ps : list (piece * pval) :=
  obj_ps (icf_cf hi_icf_objs, icf_cfreg hi_icf_objs) (repeat 0 528%nat) ++
  obj_ps (icf_tl hi_icf_objs, icf_tlreg hi_icf_objs) hi_tunable_bytes ++
  obj_ps (icf_kn hi_icf_objs, icf_knreg hi_icf_objs) icf_known_bytes ++
  concat (zip_with obj_ps (icf_small hi_icf_objs) hi_small_bytes).

(** ## The list against the loaded program *)

(** The linked program really starts with these contents. The check
    runs on the smaller memory, and the theorem [image_pieces] carries
    its result over to the full initial memory. *)
Lemma hi_cpu_globals_agree : all_agree hi_m0 hi_cpu_globals_ps.
Proof.
  destruct (image_pieces icf_keep hi_module hi_module hi_globals hi_m0 hi_cpu_globals_ps (incl_refl _)
    hi_initial hi_module_names hi_module_zeros) as (m' & E & _ & H).
  apply H. assert (Hm : m' = hi_erased icf_keep) by (unfold hi_erased; rewrite E; reflexivity).
  rewrite Hm. vm_cast_no_check (eq_refl true).
Qed.

(** No object and no byte occurs twice in the list, so a proof can
    own all of it at once. *)
Lemma hi_cpu_globals_nodup : NoDup hi_cpu_globals_ps.*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.

(** ## Three checks on plain lists *)

(** The tunable table of hi_atexit has contents that the contract
    allows. It has its full size, it holds only bytes, and the type
    codes and cleared flags are where the function reads them. *)
Lemma hi_tunable_ok : icf_tunables_ok hi_tunable_bytes.
Proof.
  split; [vm_compute; reflexivity|]. split; [apply bytes_ok; vm_compute; reflexivity|].
  apply fixed_in_ok. vm_compute. reflexivity.
Qed.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Local Notation hi_program := (program_of w0 glibc_os_registry hge).

(** The function `c: init_cpu_features` reads the saved XSAVE bit of
    the feature structure and the type codes of the tunable table, and
    it searches the rows of the descriptor table. In hi_atexit the bit
    starts clear, the codes start in place and the rows are there. So
    the function may be called on the eighteen objects as the program
    starts with them. *)
Lemma hi_cpu_globals_own :
  pts hi_cpu_globals_ps ⊢ icf_owns (glibc_program := hi_program) hi_icf_objs.
Proof using Type.
  assert (Hk : length icf_known_bytes = 544%nat) by (vm_compute; reflexivity).
  pose proof (StartImageCpu.smalls_own w0 hge icf_small_globals (icf_small hi_icf_objs) hi_small_bytes
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hsm.
  rewrite /hi_cpu_globals_ps. revert Hsm.
  generalize (concat (zip_with obj_ps (icf_small hi_icf_objs) hi_small_bytes)). intros sm Hsm.
  rewrite !pts_app !obj_ps_own (repeat_length 0 528) Hk. cbn [fst snd].
  iIntros "((Lcf & Hcf & Acf) & (Ltl & Htl & Atl) & (Lkn & Hkn & Akn) & Hs)".
  rewrite /icf_owns. iFrame "Lcf Ltl Lkn". iSplitL "Hcf Acf".
  { iExists (repeat 0 528%nat), (repeat CNone 528%nat). rewrite pts_app. iFrame "Hcf Acf". iPureIntro.
    split; [apply repeat_length|]. split; [apply repeat_length|].
    split; [apply bytes_ok; vm_compute; reflexivity|]. vm_compute. discriminate. }
  iSplitL "Htl Atl".
  { iExists hi_tunable_bytes, (repeat CNone (length hi_tunable_bytes)). rewrite pts_app. iFrame "Htl Atl".
    iPureIntro. split; [exact hi_tunable_ok|]. rewrite repeat_length. vm_compute. reflexivity. }
  iSplitL "Hkn Akn"; [rewrite /icf_known; iFrame "Hkn Akn"|].
  iApply (Hsm with "Hs").
Qed.

End image.

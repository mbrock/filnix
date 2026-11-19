(** Hello flushes wide stdout when its buffer fills and again when it
    closes the stream. Both writes use the C locale's ASCII converter.
    This module checks how the loaded image writes the resulting bytes
    to the file descriptor for stdout. *)

From Glibc Require Import HelloObjects HelloWConvConsts Unit_io_write_os Unit_libio_fileops_os
  GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String List ZArith.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap.
From Glibc Require Import Fix OsWorld OsBlocks OsRegistry FileInv LibioLogic
  LibioWIdle LibioCleanupExit LibioWCloseIt
  LibioWConvAscii LibioWDoWriteLoop LibioWDoWriteUse LibioWOverflowWrite
  HelloImageModule HelloImageLoad HelloImageLayout HelloGlibcLibsT HelloStartFacts.
From Glibc Require HelloWConvImage.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance image_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (ho_eb ob).
Local Abbreviation tw := (mkPtr (img_a "glibc_wcsmbsload#to_wc") (Ro (img_a "glibc_wcsmbsload#to_wc"))).
Local Abbreviation tm := (mkPtr (img_a "glibc_wcsmbsload#to_mb") (Ro (img_a "glibc_wcsmbsload#to_mb"))).
Context (Hfd : In 1 (ow_fds w)) (Herr : ow_errno w = Some (mkPtr eb (Obj eb))).

#[local] Instance image_syswrite : Defines hge "__GI___write" Unit_io_write_os.fn___GI___libc_write.
Proof using Type. vm_compute; reflexivity. Qed.
#[local] Instance image_dowrite : Defines hge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write.
Proof using Type. vm_compute; reflexivity. Qed.
#[local] Instance image_codecvt : Defines hge "__libio_codecvt_out" codecvt_out_fn.
Proof using Type. vm_compute; reflexivity. Qed.

(** The stream calls its byte writer through a jump table, so the
    image must supply its address as well as its body. *)
Local Lemma image_file_write : ge_fn hge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write.
Proof using Type.
  exists (img_addr "_IO_new_file_write"). split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|split; vm_compute; congruence].
Qed.

(** Closing stdout lends the conversion the whole locale cell while
    the close holds the stream's lock. *)
Lemma hello_close_write : forall E : iProp Σ, (E ⊢ □ wconv_ro) ->
  (E ⊢ wlocale (DfracOwn 1) ∗ (wlocale (DfracOwn 1) -∗ E)) ->
  forall fb freg wd, wclose_write_rule 1 (ho_vb ob) fb (ho_vreg ob) freg eb wd tw tm E.
Proof using Hfd Herr.
  exact (wclose_write_ok (glibc_program := image_program) holds_os_glibc (hk_sys _ _ (hello_link_all _ R.free_succeeds))
    image_file_write 1 (ho_vb ob) (ho_vreg ob) eb tw tm Hfd Herr wconv_ro _ (HelloWConvImage.hello_codecvt_out_image w _)).
Qed.

(** Printing lends the same conversion half the locale cell. A failed
    write may also change errno, so the caller must take it back without
    requiring its old value. *)
Lemma hello_pending_write (E : iProp Σ) :
  (E ⊢ □ (vtables_ro hge (ho_vb ob) (ho_vreg ob) ∗ wvtables_ro hge (ho_vb ob) ∗ wconv_ro)) ->
  (E ⊢ wlocale (DfracOwn (1/2)) ∗ errno_any eb ∗ (wlocale (DfracOwn (1/2)) -∗ errno_any eb -∗ E)) ->
  wdo_pending_spec (ho_vb ob) (ow_self w) 1 E.
Proof using Hfd Herr.
  exact (wdo_pending_ok (glibc_program := image_program) holds_os_glibc (hk_sys _ _ (hello_link_all _ R.free_succeeds))
    image_file_write 1 (ho_vb ob) (ho_vreg ob) eb Hfd Herr _ (HelloWConvImage.hello_codecvt_out_image w _) (ow_self w) E).
Qed.

End image.

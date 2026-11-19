(** Hello's C locale links the ASCII converter to glibc's transliteration
    tables. Printing and closing stdout lend different shares of the
    locale cells, but both run the same conversion code. *)

From Glibc Require Import HelloWConvConsts.
From Glibc Require Import GlibcProgram.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String ZArith.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap.
From Glibc Require Import Fix OsWorld OsRegistry FileInv HelloImageModule HelloImageLoad
  LibioWConvAscii LibioWConvOut LibioWConvLast LibioWConvTranslit LibioWDoWriteLoop LibioWDoWriteUse.
Import Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance image_program : GlibcProgram Σ := program_of w glibc_os_registry hge.

#[local] Instance image_ascii : Defines hge "__gconv_transform_internal_ascii" glibc_internal_ascii.
Proof using Type. vm_compute; reflexivity. Qed.
#[local] Instance image_translit : Defines hge "__GI___gconv_transliterate" glibc_translit.
Proof using Type. vm_compute; reflexivity. Qed.

(** Transliteration calls the ASCII converter through the function
    pointer stored in its step descriptor. *)
Local Lemma image_ascii_pointer : function_check_res hge (mkPtr (img_a "__gconv_transform_internal_ascii")
  (Fn (TAtom "__gconv_transform_internal_ascii"))) = Some ok.
Proof using Type. vm_compute; reflexivity. Qed.

(** The last step accepts any share of the locale cells and returns
    that same share when conversion stops. *)
Lemma hello_ia_last_image dl : ia_last_rule dl.
Proof using Type.
  exact (wp_ia_last (translit_rule_holds image_ascii_pointer ltac:(vm_compute; reflexivity)) dl).
Qed.

(** When Hello flushes a wide stream, it calls this converter to turn
    the pending characters into bytes. *)
Lemma hello_codecvt_out_image dl : codecvt_out_rule wconv_ro (wlocale dl).
Proof using Type. apply (codecvt_out_ok dl (hello_ia_last_image dl) image_ascii_pointer). vm_compute; reflexivity. Qed.
End image.

(** Hello uses the C locale's built-in converter, so glibc only reads
    the tables that describe the conversion step. Startup can share
    those tables and gnulib's locale names with every call without
    lending a caller permission to change them. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import List String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap Logic.
From Glibc Require Import Fix WordString HelloGetoptTable StartImageEarly HelloImageLoad HelloImageMbsObjs HelloLocaleState.
Import ListNotations LG0.
Open Scope Z_scope.

Section objects.
Context `{!gen_heapGS piece pval Σ}.

Local Lemma mbs_life_cons n ps : ptsq DfracDiscarded (mbs_life n :: ps) ⊣⊢
  liveq DfracDiscarded (img_addr n) (img_obj n).2 ∗ ptsq DfracDiscarded ps.
Proof using Type. apply (ptsq_app _ [_]). Qed.

(** Starting at offset 32 in the character type data, glibc follows
    three pointers to the ASCII step. The step has no shared-library
    handle, and its function pointer names the converter in the image. *)
Lemma hello_conv_tables : hello_conv_ro ⊢
  pcellq DfracDiscarded (img_addr "_nl_C_LC_CTYPE") 32 (mbs_ro "glibc_C_ctype#lc_ctype_data") ∗
  liveq DfracDiscarded (img_addr "glibc_C_ctype#lc_ctype_data") (img_obj "glibc_C_ctype#lc_ctype_data").2 ∗
  pcellq DfracDiscarded (img_addr "glibc_C_ctype#lc_ctype_data") 0 (mbs_ro "__wcsmbs_gconv_fcts_c") ∗
  liveq DfracDiscarded (img_addr "__wcsmbs_gconv_fcts_c") (img_obj "__wcsmbs_gconv_fcts_c").2 ∗
  pcellq DfracDiscarded (img_addr "__wcsmbs_gconv_fcts_c") 0 (mbs_ro "glibc_wcsmbsload#to_wc") ∗
  liveq DfracDiscarded (img_addr "glibc_wcsmbsload#to_wc") (img_obj "glibc_wcsmbsload#to_wc").2 ∗
  pcellq DfracDiscarded (img_addr "glibc_wcsmbsload#to_wc") 0 null ∗
  pcellq DfracDiscarded (img_addr "glibc_wcsmbsload#to_wc") 40 mbs_ascii_fct.
Proof using Type.
  rewrite /hello_conv_ro. iIntros "[H _]". iRevert "H". rewrite /hello_mbs_objs_ps ptsq_app /hello_mbs_conv_ps.
  repeat first [rewrite mbs_life_cons | rewrite ptsq_app]. iIntros "[$ _]".
Qed.

(** Gnulib compares the name that glibc returns with its own string
    literal. The bytes for that second string come from a different
    object, even though the two names are equal. *)
Lemma hello_conv_c_name : hello_conv_ro ⊢
  word_string DfracDiscarded (mbs_ro "hard-locale#str.31") [67].
Proof using Type.
  rewrite /hello_conv_ro. iIntros "[H _]". iRevert "H". rewrite /hello_mbs_objs_ps /hello_mbs_ro_ps !ptsq_app.
  iIntros "[_ [H _]]". iExists (img_addr "hard-locale#str.31"), (img_obj "hard-locale#str.31").2, (lit_words hello_c_text).
  iSplit; [iPureIntro; apply str_shape_b_sound; vm_compute; reflexivity|].
  replace (wstart (mbs_ro "hard-locale#str.31") - img_addr "hard-locale#str.31") with 0 by (vm_compute; reflexivity).
  rewrite /lit_ps (ptsq_app _ [_]). iExact "H".
Qed.

End objects.

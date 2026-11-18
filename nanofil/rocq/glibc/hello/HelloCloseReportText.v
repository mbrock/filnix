(** Error prints the pointer that strerror returns. For a known errno
    that pointer names a table entry. Otherwise it names the caller's
    array, which snprintf has just filled. Both paths leave a string
    that the next formatter can read. *)

From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import List String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine ExternalCalls Pieces Heap Language Logic MemLogic HelloLeaf.
From Glibc Require Import Fix FileInv OsWorld OsRegistry LibioLogic WordString PrintfOut PrintfSpec StrerrorCode
  HelloImageLoad HelloImageModule StartImageEarly HelloGetoptTable HelloGetoptDiagImage HelloGetoptDiagTcb
  HelloCloseReportImage HelloCloseReportMessages HelloCloseReportLocale HelloCloseReportStrerror HelloCloseReportSnprintf.
Import ListNotations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Section text.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance text_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Local Notation dq := DfracDiscarded.

Local Lemma report_literal b r ws s : str_shape (mkPtr b (Ro b)) b r ws s ->
  ptsq dq (lit_ps b r ws) ⊢ word_string dq (mkPtr b (Ro b)) s.
Proof using Type.
  intros Hs. iIntros "H". iExists b,r,ws. iSplit; [done|].
  replace (wstart (mkPtr b (Ro b)) - b) with 0 by (unfold wstart; cbn; rewrite (ss_align _ _ _ _ _ Hs); lia).
  rewrite /lit_ps (ptsq_app _ [_]). iExact "H".
Qed.

(** The table shares also cover strerror's two literals and the format
    that error uses to append the translated message to its report. *)
Lemma report_text_literals : ptsq dq hello_errlist_ps ⊢
  word_string dq unknown_fmt [37;115;37;100] ∗
  word_string dq unknown_prefix [85;110;107;110;111;119;110;32;101;114;114;111;114;32] ∗
  word_string dq (hello_sym "glibc_error#str.252") [58;32;37;115].
Proof using Type.
  rewrite /hello_errlist_ps (ptsq_app _ [_;_]) (ptsq_app _ (cell _ _ _)) (ptsq_app _ (List.concat _)).
  iIntros "(_ & _ & _ & H)". iEval (cbn [err_formats flat_map]; rewrite !ptsq_app) in "H".
  iDestruct "H" as "(Hfmt & Hprefix & Htext & _)". iSplitL "Hfmt"; last iSplitL "Hprefix".
  all: iApply (report_literal with "[$]"); apply str_shape_b_sound; vm_compute; reflexivity.
Qed.

(** The report can release the scratch object after it prints the text.
    Until then it needs only the returned string, not a second claim on
    the bytes of the same object. The locale state is returned intact. *)
Lemma wp_report_message_string (Herr : ow_errno w = Some (mkPtr eb (Obj eb)))
    tb tr v tid treg cf k db Φ :
  dtx_tcb_at (glibc_program := text_program) tb tr -> 0 <= v < 2^32 -> 0 <= k < 2^32 ->
  0 < db -> db mod 16 = 0 -> db+1024 <= 2^48 ->
  call_frame glibc_strerror_r [WInt k; WPtr (mkPtr db (Obj db)); WInt 1024] = Some cf ->
  let G := report_locale w R.free tb tr v tid treg in
  ptsq dq hello_errlist_ps -∗ printf_ro -∗ obj db (heap_req 4 1024) -∗ G -∗
  ▷ (∀ p s, word_string dq p s -∗ G -∗ Φ (Ret (WPtr p))) -∗ WP (ERun cf : sexpr) {{ Φ }}.
Proof using Type.
  intros Htr Hv Hk Hd Ha Hfit Hcf G. iIntros "#Htab #Hpro Hdb HG HK".
  iApply wp_fupd. iApply (wp_report_strerror w Herr tb tr v tid treg cf k (mkPtr db (Obj db)) 1024 with "Htab HG");
    [exact Htr|exact Hv|exact Hk|lia|exact Hcf|].
  iNext. destruct (err_at k) as [[[b r] s]|].
  - iIntros "#Hs HG". iModIntro. iApply ("HK" with "Hs HG").
  - iIntros "HG". iDestruct (report_locale_lend with "HG") as "(Hl & He & Herr & Hback)".
    iDestruct (report_text_literals with "Htab") as "(#Hfmt & #Hprefix & _)".
    iDestruct (obj_zero_block with "Hdb") as "(Hd & Hx & Ha)"; [compute; discriminate|].
    set (dr := mkRegion db (db+1024) Heap Live).
    iApply (wp_report_snprintf w Herr db dr k unknown_fmt unknown_prefix with "Hpro Hfmt [] Hd [Hx Ha] He");
      try assumption; try reflexivity; try (unfold dr; cbn [r_end]; lia).
    + iRight. iExists unknown_prefix, _, 0%nat. iFrame "Hprefix". iPureIntro. split; [reflexivity|lia].
    + iExists (replicate 1024 0), (replicate 1024 CNone). rewrite Z.sub_diag. iFrame "Hx Ha".
      iPureIntro. rewrite !length_replicate. split_and!; [lia|reflexivity|by apply Forall_replicate].
    + iNext. iIntros (n s Hn) "He Hs". iExists n. iSplit; [done|].
      iMod (word_string_persist with "Hs") as "#Hs". iModIntro.
      iApply ("HK" with "Hs [Hl He Herr Hback]"). iApply ("Hback" with "Hl He Herr").
Qed.
End text.

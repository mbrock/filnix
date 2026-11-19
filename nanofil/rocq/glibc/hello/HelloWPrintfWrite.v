(** When Hello fills stdout's wide buffer, glibc needs the locale to
    convert the characters and may write errno if the flush fails.
    Hello keeps the locale pointer with getopt's warning state and
    errno with its streams. This proof lends both at once and returns
    the new value of errno to the streams. *)

From Glibc Require Import HelloWConvConsts.
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String List ZArith.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Logic.
From Glibc Require Import Fix OsWorld OsBlocks OsRegistry FileInv LibioLogic LibioWIdle
  LibioWConvAscii LibioWOverflowWrite HelloGlibcDebts HelloStartHdGetopt
  HelloImageModule HelloImageLoad HelloImageLayout HelloLocaleState HelloCloseStdoutWideCall
  HelloWDoWriteImage HelloWPrintfCall.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section write.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance write_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Context (tb : Z) (N priv : iProp Σ)
  (HP : priv ⊣⊢ N ∗ hello_hd_getopt w R.free tb ∗ (N ∗ hello_priv_rest w R.free)).
Local Abbreviation E := (wprintf_E w R.free priv).

(** The formatter can read both of stdout's jump tables. Its private
    state also supplies the constants that the ASCII converter reads. *)
Local Lemma print_tables : E ⊢ □ (vtables_ro hge (ho_vb ob) (ho_vreg ob) ∗ wvtables_ro hge (ho_vb ob) ∗ wconv_ro).
Proof using HP.
  iIntros "(_ & Hp & #Hro)". iDestruct (HP with "Hp") as "(_ & _ & _ & Hloc & Hconv & _)".
  iDestruct "Hloc" as "(_ & _ & _ & _ & _ & Hct & _)".
  iDestruct (hello_wconv_ro with "[Hct Hconv]") as "#Hcv"; [iSplitL "Hct"; [iExact "Hct"|iExact "Hconv"]|].
  iPoseProof (hello_ro_wvtables with "Hro") as "#Hwv". iPoseProof "Hro" as "[Hvt _]".
  iModIntro. iSplitR; [iExact "Hvt"|]. iSplitR; [iExact "Hwv"|iExact "Hcv"].
Qed.

(** Glibc reads the locale pointer to find the converter. It does not
    change the pointer, so Hello can lend it permission to read and
    recover permission to write when the call returns. *)
Local Lemma print_locale_errno (Hfd2 : In 2 (ow_fds w)) :
  E ⊢ wlocale (DfracOwn (1/2)) ∗ errno_any (ho_eb ob) ∗
    (wlocale (DfracOwn (1/2)) -∗ errno_any (ho_eb ob) -∗ E).
Proof using HP.
  iIntros "((Ho & Hs & Hi & Hl & Ht & He & Hn) & Hp & #Hro)".
  iDestruct (HP with "Hp") as "(HN & HG & HN' & (Hcat & Hcats) & Hconv & Hr)".
  iDestruct (hd_locale_lend w tb Hfd2 with "[$HG $Ht $He $Hs]") as "((Ha & Hb & Hc) & Ht & He & Hs & WG)".
  assert (Half : forall b k p, pcell b k p ⊣⊢@{iPropI Σ} pcellq (DfracOwn (1/2)) b k p ∗ pcellq (DfracOwn (1/2)) b k p)
    by (intros; rewrite /pcellq -ptsq_split Qp.div_2; done).
  iDestruct (Half with "Hcat") as "[H1 H2]".
  iSplitL "Ha Hb Hc H1"; [iFrame "Ha Hb Hc H1"|]. iSplitL "He"; [iExact "He"|].
  iIntros "(Ha & Hb & Hc & H1) He". iDestruct ("WG" with "[$Ha $Hb $Hc]") as "HG".
  rewrite /wprintf_E. iSplitL "Ho Hs Hi Hl Ht He Hn"; [iFrame "Ho Hs Hi Hl Ht He Hn"|].
  iSplitL; [|iExact "Hro"]. iApply HP. iSplitL "HN"; [iExact "HN"|]. iSplitL "HG"; [iExact "HG"|].
  iSplitL "HN'"; [iExact "HN'"|]. iSplitL "H1 H2 Hcats".
  - iSplitR "Hcats"; [iApply Half; iFrame "H1 H2"|iExact "Hcats"].
  - iSplitL "Hconv"; [iExact "Hconv"|iExact "Hr"].
Qed.

(** The formatter can flush stdout without asking main for any extra
    memory. Its jump tables, locale and errno come from the state that
    Hello lends it for the rest of the call. *)
Lemma hello_wprintf_pending (Hfd1 : In 1 (ow_fds w)) (Hfd2 : In 2 (ow_fds w))
  (Herr : ow_errno w = Some (mkPtr (ho_eb ob) (Obj (ho_eb ob)))) :
  wdo_pending_spec (ho_vb ob) (ow_self w) 1 E.
Proof using HP.
  exact (hello_pending_write w Hfd1 Herr E print_tables (print_locale_errno Hfd2)).
Qed.

End write.

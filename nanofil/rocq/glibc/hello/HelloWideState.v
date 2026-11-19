(** Hello's wide print call makes stdout wide, and that needs the
    resource that [wfwide_res] names: the thread's locale pointer, the
    C locale's converter table, the constants that orientation copies
    and the free conversion lock. Hello owns all of these from the start,
    spread over its streams and its private state. This file shows how
    main lends them to the call and gets them back unchanged. *)

From Glibc Require Fix.
From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv StartImageCpu HelloImageModule HelloImageLoad HelloImageLayout
  HelloImageWideObjs HelloStartHdGetopt HelloGlibcDebts HelloLocaleState HelloConvObjects
  HelloConvState Mbrtowc LibioWFwide.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section state.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance wide_program : GlibcProgram Σ := program_of w glibc_os_registry hge.

(** ## The conversion lock

    Glibc guards its table of converters with a lock, which is free
    whenever no setup of a conversion is running. Making stdout wide
    takes that lock and frees it again before it returns. Hello finds
    the lock as four zero bytes in its image and keeps them with
    close_stdout's globals. *)

(** The lock's four zero bytes form a free lock. The capability slots
    beside them stay with the rest of close_stdout's globals. *)
Lemma gconv_lock_lend : pts hello_close_rest_ps ⊢ gconv_lock_free ∗ (gconv_lock_free -∗ pts hello_close_rest_ps).
Proof using Type.
  rewrite /hello_close_rest_ps pts_app pts_app pts_app (obj_ps_own (img_ob "__gconv_lock")).
  iIntros "(A & B & C & Hl & Hb & Ha)".
  iSplitL "Hl Hb". { iSplitL "Hl"; [iExact "Hl"|]. iSplit; [iPureIntro; lia|]. iExact "Hb". }
  iIntros "(Hl & _ & Hb)". iFrame.
Qed.

(** ## Lending the orientation's resource

    Main holds its streams and its private state between calls. The
    orientation's resource is spread over both: the locale pointer sits
    with getopt's warning state, which main completes from its streams,
    the global locale's first word sits in the locale part, the
    constants sit in the read-only part, and the lock sits with
    close_stdout's globals. *)

(** Main lends the call what making stdout wide needs, and it gets
    all of it back unchanged. It lends only half of the global locale's
    first word, because the locale part keeps the other half. The
    private state must split as it does for the narrow conversion. The
    loan never reads stdout, so main can keep stdout apart in either
    orientation. *)
Lemma hello_wfwide_lend tb (Hfd : In 2 (ow_fds w)) (N priv S : iProp Σ) :
  (priv ⊣⊢ N ∗ hello_hd_getopt w fr tb ∗ (N ∗ hello_priv_rest w fr)) ->
  hello_stdio_wide w hge hello_image_objs S ∗ priv ⊢
  wfwide_res (DfracOwn (1/2)) ∗ (wfwide_res (DfracOwn (1/2)) -∗ hello_stdio_wide w hge hello_image_objs S ∗ priv).
Proof using Type.
  intros HP. iIntros "[Hio Hp]". iDestruct (HP with "Hp") as "(HN & HG & HN' & Hloc & #Hro & Hr)".
  iDestruct (hello_hd_lend w fr tb Hfd N N S with "[$Hio $HN $HG $HN']") as "[[HN (%x & %Hx & HG)] Hb]".
  iDestruct (conv_dgx_lend with "HG") as "(_ & (Ht & Hp & Hg & %es & %Les & He) & HG)".
  iDestruct "Hloc" as "(Hcat & Hnames & Hl & Hc & Hcl & #Hct & Hcnt)".
  iPoseProof "Hct" as "[#Hcc _]". iPoseProof (hello_conv_tables with "Hro") as "#Htab".
  iPoseProof "Hro" as "[_ Hwo]". iEval (rewrite /hello_wide_objs_ps ptsq_app) in "Hwo". iDestruct "Hwo" as "[#Hwf _]".
  iDestruct "Hr" as "(Hgro & Hcr & Hrest)". iDestruct (gconv_lock_lend with "Hcr") as "[Hlk Hcr]".
  assert (Half : forall b k p, pcell b k p ⊣⊢@{iPropI Σ} pcellq (DfracOwn (1/2)) b k p ∗ pcellq (DfracOwn (1/2)) b k p)
    by (intros; rewrite /pcellq -ptsq_split Qp.div_2; done).
  iDestruct (Half with "Hcat") as "[Hca Hcb]".
  iSplitL "Ht Hp Hg Hca Hlk".
  { iFrame "Ht Hp Hg Hca Hlk Hwf". iSplit; [iExact "Hcc" | iExact "Htab"]. }
  iIntros "((Ht & Hp & Hg & Hca) & _ & _ & Hlk)".
  iDestruct ("HG" with "Ht Hp Hg [%] He") as "HG"; [exact Les|].
  iDestruct ("Hb" with "[HN HG]") as "[Hio (HN & HG & HN')]".
  { iFrame "HN". iExists x. iSplit; [done|iExact "HG"]. }
  iSplitL "Hio"; [iExact "Hio"|]. iApply HP. iSplitL "HN"; [iExact "HN"|].
  iSplitL "HG"; [iExact "HG"|]. iSplitL "HN'"; [iExact "HN'"|].
  iDestruct ("Hcr" with "Hlk") as "Hcr".
  iSplitL "Hca Hcb Hnames Hl Hc Hcl Hcnt".
  { iSplitL "Hca Hcb"; [iApply Half; iFrame "Hca Hcb"|]. iFrame "Hnames Hl Hc Hcl Hct Hcnt". }
  iSplit; [iExact "Hro"|]. iFrame "Hgro Hcr Hrest".
Qed.

End state.

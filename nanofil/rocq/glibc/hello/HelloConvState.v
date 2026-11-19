(** The conversion needs the thread's locale pointer and errno at the
    same time. Getopt keeps the pointer with the resources it needs to
    print a warning. Hello lends those resources to the conversion and
    puts them back even when a rejected byte has changed errno. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import HelloBodies.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv WordString LocalenameLogic DcgettextRealV
  StartCtypeInitSpec StartImageEarly HelloGetoptDiagLock HelloGetoptDiagTcb HelloGetoptDiagGettext
  HelloImageModule HelloImageLoad HelloImageLayout HelloImageEarly HelloImageLocaleObjs HelloImageMbsObjs
  HelloStartGetopt HelloStartGetoptRules HelloStartHdGetopt HelloGlibcDebts HelloLocaleState HelloConvObjects
  Mbrtowc HelloConvString.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section state.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance conv_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation gl := (ct_gl hello_ct_objs).
Local Abbreviation ts := (ct_lt hello_ct_objs).
Local Abbreviation cv := (mkPtr (img_a "_nl_C_name") (Ro (img_a "_nl_C_name"))).
Local Abbreviation eb := (img_a "__libc_errno").

(** When glibc rejects a byte, it writes an error code into errno.
    Getopt can still print its next warning: it needs the locale to
    stay the same, but it does not need errno to keep its old value. *)
Lemma conv_dgx_lend tb v tid treg : hello_dgx w fr tb v tid treg ⊢
  word_string DfracDiscarded cv [67] ∗
  (live ts (ct_ltreg hello_ct_objs) ∗ pcell ts 0 (mkPtr gl (Obj gl)) ∗ live gl (ct_glreg hello_ct_objs) ∗
   ∃ es, ⌜length es = 4%nat⌝ ∗ bytes eb 0 es) ∗
  (live ts (ct_ltreg hello_ct_objs) -∗ pcell ts 0 (mkPtr gl (Obj gl)) -∗ live gl (ct_glreg hello_ct_objs) -∗
   ∀ es, ⌜length es = 4%nat⌝ -∗ bytes eb 0 es -∗ hello_dgx w fr tb v tid treg).
Proof using Type.
  rewrite /hello_dgx /hello_dg_G /dlk_G /dlk_G0 /dtx_G /dtx_G0 /dgx_G /dgx_before /dcg_before_v.
  iIntros "(%s1 & %s2 & %s3 & %Hr & %tr & %jb & %Hc & Hcl & Hj & Hx & ((%bs & H1 & H2 & H3 & H4 & H5 & HC & H7 & He) & HS & HL))".
  iDestruct "H1" as "(Hd & Hcat & #Hcv & Hreads)".
  iDestruct "HC" as "(Ht & Hp & Hg & Hname & Hstr)".
  iDestruct "He" as (cs [Lbs Lcs]) "He". iEval (rewrite pts_app) in "He". iDestruct "He" as "[He Ha]".
  iSplitR; [iExact "Hcv"|].
  iSplitL "Ht Hp Hg He".
  { rewrite /live /pcell !pts_ptsq. iFrame "Ht Hp Hg". iExists bs. iSplit; [done | iExact "He"]. }
  iIntros "Ht Hp Hg" (es Les) "He". iExists s1, s2, s3. iSplit; [done|].
  iExists tr, jb. iSplit; [done|]. iFrame "Hcl Hj Hx HS HL". iExists es.
  iFrame "H2 H3 H4 H5 H7". iSplitL "Hd Hcat Hreads"; [iFrame "Hd Hcat Hcv Hreads"|].
  iSplitL "Ht Hp Hg Hname Hstr"; [iFrame "Ht Hp Hg Hname Hstr"|].
  iExists cs. iSplit; [done|]. rewrite pts_app. iFrame "He Ha".
Qed.

(** The first name in the global locale belongs to LC_CTYPE. The
    other categories keep their pointers throughout the query. *)
Lemma conv_name_lend : pts hello_locale_objs_ps ⊢ pcell gl 128 cv ∗ (pcell gl 128 cv -∗ pts hello_locale_objs_ps).
Proof using Type.
  set (slot := length (ptr_ps gl 128 cv)). set (i := (slot * (length hello_locale_cats + 3))%nat).
  set (pre := take i hello_locale_objs_ps). set (post := drop (i + slot) hello_locale_objs_ps).
  assert (E : hello_locale_objs_ps = pre ++ ptr_ps gl 128 cv ++ post) by (vm_compute; reflexivity).
  rewrite {1 2}E (pts_app pre) (pts_app (ptr_ps gl 128 cv)).
  iIntros "(Hpre & Hn & Hpost)". iSplitL "Hn"; [iExact "Hn"|]. iIntros "Hn". iFrame.
Qed.

(** The conversion borrows the first two links of the converter path
    from the thread and the global locale. It reads the rest from the
    constant tables. When it finishes, Hello gets its streams and its
    private state back, including the current value of errno. *)
Lemma hello_conv_lend tb (Hfd : In 2 (ow_fds w)) (N priv : iProp Σ) :
  (priv ⊣⊢ N ∗ hello_hd_getopt w fr tb ∗ (N ∗ hello_priv_rest w fr)) ->
  hello_stdio w hge hello_image_objs ∗ priv ⊢
  mbr_tables ∗ word_string DfracDiscarded cv [67] ∗
  word_string DfracDiscarded (mkPtr (img_a "hard-locale#str.31") (Ro (img_a "hard-locale#str.31"))) [67] ∗
  conv_cells (DfracOwn (1/2)) (DfracOwn (1/2)) ∗
  (conv_cells (DfracOwn (1/2)) (DfracOwn (1/2)) -∗ hello_stdio w hge hello_image_objs ∗ priv).
Proof using Type.
  intros HP. iIntros "[Hio Hp]". iDestruct (HP with "Hp") as "(HN & HG & HN' & Hloc & #Hro & Hr)".
  iDestruct (hello_hd_lend w fr tb Hfd N N with "[$Hio $HN $HG $HN']") as "[[HN (%x & %Hx & HG)] Hb]".
  iDestruct (conv_dgx_lend with "HG") as "(#Hcv & (Ht & Hp & Hg & He) & HG)".
  iDestruct "Hloc" as "(Hcat & Hnames & Hl & Hc & Hcl & #Hct & Hcnt)".
  iDestruct (conv_name_lend with "Hnames") as "[Hname Hnames]".
  iPoseProof "Hct" as "[#Hcc _]". iPoseProof (hello_conv_tables with "Hro") as "#Htab".
  iPoseProof (hello_conv_c_name with "Hro") as "#Hlit".
  iSplitR; [iSplit; [iExact "Hcc" | iExact "Htab"]|]. iFrame "Hcv Hlit".
  assert (Half : forall b k p, pcell b k p ⊣⊢@{iPropI Σ} pcellq (DfracOwn (1/2)) b k p ∗ pcellq (DfracOwn (1/2)) b k p)
    by (intros; rewrite /pcellq -ptsq_split Qp.div_2; done).
  iDestruct (Half with "Hcat") as "[Hca Hcb]". iDestruct (Half with "Hname") as "[Hna Hnb]".
  iSplitL "Ht Hp Hg Hca Hna He"; [iFrame "Ht Hp Hg Hca Hna He"|].
  iIntros "((Ht & Hp & Hg & Hca) & Hna & %es & %Les & He)".
  iDestruct ("HG" with "Ht Hp Hg [%] He") as "HG"; [exact Les|].
  iDestruct ("Hb" with "[HN HG]") as "[Hio (HN & HG & HN')]".
  { iFrame "HN". iExists x. iSplit; [done|iExact "HG"]. }
  iSplitL "Hio"; [iExact "Hio"|]. iApply HP. iSplitL "HN"; [iExact "HN"|].
  iSplitL "HG"; [iExact "HG"|]. iSplitL "HN'"; [iExact "HN'"|].
  iSplitR "Hr"; [|iSplit; [iExact "Hro"|iExact "Hr"]].
  iSplitL "Hca Hcb". { iApply Half. iFrame "Hca Hcb". }
  iSplitL "Hnames Hna Hnb". { iApply "Hnames". iApply Half. iFrame "Hna Hnb". }
  iFrame "Hl Hc Hcl Hct Hcnt".
Qed.

(** The conversion call that main makes returns the length of the
    greeting. That number fits below the error sentinel, and its
    buffer holds the wide characters that main will print. *)
Lemma hello_mbsrtowcs tb (Hfd : In 2 (ow_fds w)) (Herr : ow_errno w = Some (mkPtr eb (Obj eb))) (N priv : iProp Σ) :
  (priv ⊣⊢ N ∗ hello_hd_getopt w fr tb ∗ (N ∗ hello_priv_rest w fr)) -> mbsrtowcs w hge hello_image_objs priv.
Proof using Type.
  intros HP bd b4 b6 g s n H4 H6 Hd. exists mbs_fn. split; [vm_compute; reflexivity|].
  split; [eexists; reflexivity|]. intros f Φ Hf. injection Hf as <-.
  iIntros "(_ & Hio & Hp & Hbuf & H4 & Hs & H6) HK".
  iDestruct (hello_conv_lend tb Hfd N priv HP with "[$Hio $Hp]") as "(#Htab & #Hcv & #Hlit & Hcells & Hb)".
  iApply (hello_conv_string w fr Herr _ _ bd b4 b6 g s Φ H4 H6 Hd with "Htab Hcv Hlit Hcells Hbuf H4 Hs H6").
  iNext. iIntros (ws [Hws Hlen]) "Hcells Hbuf". iDestruct ("Hb" with "Hcells") as "[Hio Hp]".
  iApply "HK". iExists (Z.of_nat (length s)), ws. iSplit; [iPureIntro; split_and!; first [done | lia]|].
  iFrame "Hio Hp Hbuf".
Qed.

End state.

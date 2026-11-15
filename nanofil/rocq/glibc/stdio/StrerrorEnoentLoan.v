(** Translating an error message reads the calling thread's id while taking
    three locks. Each read needs permission to access the same live thread.
    This proof divides that permission between the locks and rejoins it
    before printing. The caller keeps cancellation disabled throughout. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap
  Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic SysWrappers
  AllocLogic HiAtexitAlloc GetoptMallocGlibc StpcpyCode TfindCode TfindEmpty
  LocalenameCode LocalenameLogic RdlockCode RwunlockCode RdlockLogic RwunlockLogic
  StrlenLogic MemFwdCode WordString DcgettextCode DcigettextCode DcigettextRoute
  DcigettextPreRules DcigettextSecure DcgettextC DcgettextLocale DcgettextRwlock DcgettextReal DcgettextRealV
  StrerrorCode ErrlistCode ErrlistEnoent ErrlistFacts ErrorText ErrorTextPrint StrerrorEnoent Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section loan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb)))
  (Hreg : holds_os registry) (Hext : sys_external ge).
Context (dom : ptr) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
  (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (ic : cap) (dqi : dfrac) (ireg : region)
  (sec : Z) (dqs : dfrac) (secreg : region) (v : Z) (tc dd : ptr)
  (dq : dfrac) (mpb tcb dmb : Z) (mpr tcr dr : region)
  (dqr : dfrac) (rb ro : Z) (rreg : region) (gb go : Z) (greg : region) (dqg : dfrac) (lp : ptr) (lb : Z) (lreg : region)
  (dql dqn dqt : dfrac) (treg : region)
  (lk1 : ptr) (a1 : Z) (ar1 : region) (r1 cw1 sh1 fl1 : Z)
  (lk2 : ptr) (a2 : Z) (ar2 : region) (r2 cw2 sh2 fl2 : Z)
  (lkt : ptr) (a3 : Z) (ar3 : region) (r3 cw3 sh3 fl3 : Z) (tb : Z) (tbreg : region) (tid : Z).

(** The translation state contains one errno block and the thread-id cell,
    but no thread lifetime. The caller supplies the lifetime separately. *)
Definition enoent_translation_pack (bs : list Z) : iProp Σ :=
  dcg_before_v eb dom [108;105;98;99] dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
    (rw_lock a1 ar1 r1 cw1 sh1 fl1) (rw_lock a2 ar2 r2 cw2 sh2 fl2)
    (rw_lock a3 ar3 r3 cw3 sh3 fl3)
    (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg)
    (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs ∗ int_cell tb 720 tid.

Let translation := enoent_translation eb dom dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg
  sec dqs secreg v dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
  a1 ar1 r1 cw1 sh1 fl1 (DfracOwn (1 / 2)) (DfracOwn (1 / 2))
  a2 ar2 r2 cw2 sh2 fl2 (DfracOwn (1 / 2 / 2)) (DfracOwn (1 / 2 / 2))
  a3 ar3 r3 cw3 sh3 fl3 (DfracOwn (1 / 2 / 2)) (DfracOwn (1 / 2 / 2)) tb tbreg tid.

(** Splitting and rejoining the owned shares is reversible. Discarding
    lifetime permission would prevent the caller from recovering full ownership. *)
Lemma enoent_translation_borrow bs :
  live tb tbreg ∗ enoent_translation_pack bs ⊣⊢ translation bs.
Proof.
  assert (Hsplit : forall ps, pts ps ⊣⊢
    ptsq (DfracOwn (1 / 2)) ps ∗ ptsq (DfracOwn (1 / 2 / 2)) ps ∗ ptsq (DfracOwn (1 / 2 / 2)) ps).
  { intros ps. rewrite -(ptsq_split (1 / 2 / 2) (1 / 2 / 2)) Qp.div_2
      -(ptsq_split (1 / 2) (1 / 2)) Qp.div_2. done. }
  assert (Hl : live tb tbreg ⊣⊢ liveq (DfracOwn (1 / 2)) tb tbreg ∗ liveq (DfracOwn (1 / 2 / 2)) tb tbreg ∗
    liveq (DfracOwn (1 / 2 / 2)) tb tbreg) by (rewrite /live /liveq; apply Hsplit).
  assert (Hi : int_cell tb 720 tid ⊣⊢ int_cellq (DfracOwn (1 / 2)) tb 720 tid ∗
    int_cellq (DfracOwn (1 / 2 / 2)) tb 720 tid ∗ int_cellq (DfracOwn (1 / 2 / 2)) tb 720 tid).
  { rewrite /int_cell /int_cellq /bytes /bytesq Hsplit. iSplit.
    - iIntros "(%H & A & B & C)". iSplitL "A"; [iSplit; [done | iExact "A"]|].
      iSplitL "B"; iSplit; done.
    - iIntros "((%H & A) & (_ & B) & (_ & C))". iSplit; [done|]. iSplitL "A"; [iExact "A"|].
      iSplitL "B"; [iExact "B" | iExact "C"]. }
  rewrite /enoent_translation_pack /translation /enoent_translation /dcg_before_v /rw_held /rw_self Hl Hi. iSplit.
  - iIntros "((Ht1 & Ht2 & Ht3) & (Hr & H1 & H2 & H3 & HK & HC & HM & He) & Hi1 & Hi2 & Hi3)".
    iSplitL "Hr"; [iExact "Hr"|].
    iSplitL "H1 Ht1 Hi1"; [iSplitL "H1"; [iExact "H1"|]; iSplitL "Ht1"; [iExact "Ht1" | iExact "Hi1"]|].
    iSplitL "H2 Ht2 Hi2"; [iSplitL "H2"; [iExact "H2"|]; iSplitL "Ht2"; [iExact "Ht2" | iExact "Hi2"]|].
    iSplitL "H3 Ht3 Hi3"; [iSplitL "H3"; [iExact "H3"|]; iSplitL "Ht3"; [iExact "Ht3" | iExact "Hi3"]|].
    iSplitL "HK"; [iExact "HK"|]. iSplitL "HC"; [iExact "HC"|]. iSplitL "HM"; [iExact "HM" | iExact "He"].
  - iIntros "(Hr & (H1 & Ht1 & Hi1) & (H2 & Ht2 & Hi2) & (H3 & Ht3 & Hi3) & HK & HC & HM & He)".
    iSplitL "Ht1 Ht2 Ht3"; [iSplitL "Ht1"; [iExact "Ht1"|]; iSplitL "Ht2"; [iExact "Ht2" | iExact "Ht3"]|].
    iSplitR "Hi1 Hi2 Hi3"; [|iSplitL "Hi1"; [iExact "Hi1"|]; iSplitL "Hi2"; [iExact "Hi2" | iExact "Hi3"]].
    iSplitL "Hr"; [iExact "Hr"|]. iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "HK"; [iExact "HK"|]. iSplitL "HC"; [iExact "HC"|].
    iSplitL "HM"; [iExact "HM" | iExact "He"].
Qed.

Context `{!Defines ge "__get_errlist" glibc_get_errlist,
  !Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
  !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
  !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
  !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name,
  !Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock,
  !Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock,
  !Defines ge "free" free_fn, !Defines ge "malloc" malloc_fn, !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}.
Context (Hheap : dci_heap_glibc mpb tcb)
  (Hlk1 : rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid) (Hlk2 : rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid)
  (Hlkt : rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid) (Hlocale : locale_cells gb go greg lp lb lreg)
  (Hrb : 0 < rb) (Hro : 0 <= ro) (Hral : (rb + ro) mod 8 = 0) (Hre : rb + ro + 8 <= r_end rreg) (Hrr : r_end rreg <= 2 ^ 48)
  (Hglobals : dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec)
  (Hbounds : dci_bounds db dbreg nb ib ic ireg k sec secreg)
  (Hv : 0 <= v < 2 ^ 32) (Hsecure : v = 0 \/ dci_strchr_links)
  (Hdomain : lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom).

(** Strerror returns the same message pointer and keeps the scratch buffer
    intact. It also returns all permission to access the thread. The caller
    keeps its cancellation setting, argument cursor and FILE memory separate. *)
Lemma error_strerror_enoent_thread_call lenb lenr tab tabr mid mb mr bs (E : iProp Σ) :
  lookup (TAtom "_sys_errlist_internal_len") (ge_globals ge) = Some (mkPtr lenb (Ro lenb)) ->
  lookup (TAtom "_sys_errlist_internal") (ge_globals ge) = Some (mkPtr tab (Ro tab)) ->
  lookup (TAtom "glibc_errlist_data_gen#str.249") (ge_globals ge) = Some mid ->
  0 < lenb -> lenb + 8 <= r_end lenr -> r_end lenr <= 2 ^ 48 ->
  0 < tab -> tab mod 8 = 0 -> tab + 24 <= r_end tabr -> r_end tabr <= 2 ^ 48 ->
  string_ok mid mb mr enoent_chars ->
  forall b, exists fr, call_frame glibc_strerror_r [WInt 2;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ live tb tbreg -∗
      (enoent_lookup_cells lenb lenr tab tabr mid mr ∗ enoent_translation_pack bs ∗
       bytesq DfracDiscarded mb (ptr_addr mid - mb) (enoent_chars ++ [0]) ∗ E) -∗
      WP (ERun fr : gexpr) {{ result, ∃ p, ⌜result = Ret (WPtr p) /\ p = mid⌝ ∗
        live tb tbreg ∗ error_text_buffer error_borrowed_text b p ∗
        enoent_lookup_cells lenb lenr tab tabr mid mr ∗ enoent_translation_pack (le_bytes (dci_w bs) 4) ∗ E }}).
Proof.
  intros Hlen Htable Hmessage Hlenb Hlene Hlenr Htab Htal Htabe Htabr Hstring b.
  destruct (error_strerror_enoent_call eb Herr Hreg Hext dom dqd nb nc k cat dqc cv p276 p277 db dqb dbreg
    ib ic dqi ireg sec dqs secreg v tc dd dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg
    dql dqn dqt treg lk1 a1 ar1 r1 cw1 sh1 fl1 (DfracOwn (1 / 2)) (DfracOwn (1 / 2))
    lk2 a2 ar2 r2 cw2 sh2 fl2 (DfracOwn (1 / 2 / 2)) (DfracOwn (1 / 2 / 2))
    lkt a3 ar3 r3 cw3 sh3 fl3 (DfracOwn (1 / 2 / 2)) (DfracOwn (1 / 2 / 2)) tb tbreg tid
    Hheap Hlk1 Hlk2 Hlkt Hlocale Hrb Hro Hral Hre Hrr Hglobals Hbounds Hv Hsecure Hdomain
    lenb lenr tab tabr mid mb mr bs E Hlen Htable Hmessage Hlenb Hlene Hlenr Htab Htal Htabe Htabr Hstring b)
    as (fr & Hfr & Hcall).
  exists fr. split; [done |]. iIntros "Hobj Hlife (Hlookup & Hpack & Htext & HE)".
  iAssert (translation bs) with "[Hlife Hpack]" as "Htranslation".
  { rewrite -enoent_translation_borrow. iFrame. }
  iApply (wp_wand with "[Hobj Hlookup Htranslation Htext HE]").
  { iApply (Hcall with "Hobj [$Hlookup $Htranslation $Htext $HE]"). }
  iIntros (result) "H". iDestruct "H" as (p Hp) "(Hbuffer & Hlookup & Htranslation & HE)".
  iAssert (translation (le_bytes (dci_w bs) 4)) with "[Htranslation]" as "Htranslation"; [iExact "Htranslation" |].
  iEval (rewrite -enoent_translation_borrow) in "Htranslation".
  iDestruct "Htranslation" as "[Hlife Hpack]". iExists p. iFrame. done.
Qed.
End loan.

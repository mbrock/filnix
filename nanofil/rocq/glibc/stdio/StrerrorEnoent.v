(** ENOENT uses the error table and the C-locale translation route. The
    caller supplies the table, static text and all translation resources.
    This proof returns the same borrowed pointer and leaves the supplied
    scratch buffer unchanged. It does not cover unknown errors or acquire
    static ownership from the program image. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic SysWrappers
  AllocLogic HiAtexitAlloc GetoptMallocGlibc StpcpyCode TfindCode TfindEmpty
  LocalenameCode LocalenameLogic RdlockCode RwunlockCode RdlockLogic RwunlockLogic
  StrlenLogic MemFwdCode WordString DcgettextCode DcigettextCode DcigettextRoute
  DcigettextPreRules DcigettextSecure DcgettextC DcgettextLocale DcgettextRwlock DcgettextReal DcgettextRealV
  StrerrorCode ErrlistCode ErrlistEnoent ErrlistFacts ErrorText ErrorTextPrint Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section known.
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
  (lk1 : ptr) (a1 : Z) (ar1 : region) (r1 cw1 sh1 fl1 : Z) (q1 i1 : dfrac)
  (lk2 : ptr) (a2 : Z) (ar2 : region) (r2 cw2 sh2 fl2 : Z) (q2 i2 : dfrac)
  (lkt : ptr) (a3 : Z) (ar3 : region) (r3 cw3 sh3 fl3 : Z) (q3 i3 : dfrac) (tb : Z) (tbreg : region) (tid : Z).

(** Translating a message needs permission to read the locale and cache,
    take locks and allocate temporary storage. The caller supplies those
    permissions here, together with the libc domain string and errno.
    The current errno value need not equal the saved error number 2. *)
Definition enoent_translation (bs : list Z) : iProp Σ :=
  dcg_before_v eb dom [108;105;98;99] dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
    (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
    (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
    (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg)
    (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs.

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

(** For error number 2, strerror returns the table's message after calling
    gettext. The proof follows both calls and preserves the caller's other
    memory, including any scratch buffer. It does not access a FILE. *)
Lemma wp_strerror_enoent fr buf len lenb lenr tab tabr mid mr bs (E : iProp Σ) Φ :
  call_frame glibc_strerror_r [WInt 2;WPtr buf;WInt len] = Some fr ->
  lookup (TAtom "_sys_errlist_internal_len") (ge_globals ge) = Some (mkPtr lenb (Ro lenb)) ->
  lookup (TAtom "_sys_errlist_internal") (ge_globals ge) = Some (mkPtr tab (Ro tab)) ->
  0 < lenb -> lenb + 8 <= r_end lenr -> r_end lenr <= 2 ^ 48 ->
  0 < tab -> tab mod 8 = 0 -> tab + 24 <= r_end tabr -> r_end tabr <= 2 ^ 48 ->
  0 < ptr_addr mid < 2 ^ 64 ->
  enoent_lookup_cells lenb lenr tab tabr mid mr -∗ enoent_translation bs -∗ E -∗
  ▷ (enoent_lookup_cells lenb lenr tab tabr mid mr -∗
    enoent_translation (le_bytes (dci_w bs) 4) -∗ E -∗ Φ (Ret (WPtr mid))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Defines0 Defines1 Defines10 Defines11 Defines12 Defines13 Defines2 Defines3 Defines4 Defines5 Defines6 Defines7 Defines8 Defines9 Hbounds Hdomain Herr Hext Hglobals Hheap Hlk1 Hlk2 Hlkt Hlocale Hral Hrb Hre Hreg Hro Hrr Hsecure Hv.
  intros Hfr Hlen Htable Hlenb Hlene Hlenr Htab Htal Htabe Htabr Hmid.
  iIntros "Hlookup Htranslation HE HK". cbn in Hfr. injection Hfr as <-.
  step. iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_get_errlist_enoent with "Hlookup"); try eassumption; try reflexivity; try lia.
  iNext. iIntros "Hlookup". iExists _. iSplit; [iPureIntro; reflexivity |]. iNext.
  step. step. step. branch_as true. step. step_global Hdomain.
  iApply (wp_dcgettext_c_real_v eb Herr Hreg Hext with "Htranslation"); try eassumption; try (vx).
  iNext. iIntros (q) "[-> Htranslation]".
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" with "Hlookup Htranslation HE").
Qed.

(** This adapter supplies ErrorText's existing strerror premise for error 2.
    It returns the whole scratch buffer even though the result is borrowed.
    The caller's E can contain its narrow text readiness and FILE fields;
    neither those fields nor a second FILE lifetime are manufactured here. *)
Lemma error_strerror_enoent_call lenb lenr tab tabr mid mb mr bs (E : iProp Σ) :
  lookup (TAtom "_sys_errlist_internal_len") (ge_globals ge) = Some (mkPtr lenb (Ro lenb)) ->
  lookup (TAtom "_sys_errlist_internal") (ge_globals ge) = Some (mkPtr tab (Ro tab)) ->
  lookup (TAtom "glibc_errlist_data_gen#str.249") (ge_globals ge) = Some mid ->
  0 < lenb -> lenb + 8 <= r_end lenr -> r_end lenr <= 2 ^ 48 ->
  0 < tab -> tab mod 8 = 0 -> tab + 24 <= r_end tabr -> r_end tabr <= 2 ^ 48 ->
  string_ok mid mb mr enoent_chars ->
  forall b, exists fr, call_frame glibc_strerror_r [WInt 2;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗
      (enoent_lookup_cells lenb lenr tab tabr mid mr ∗ enoent_translation bs ∗
       bytesq DfracDiscarded mb (ptr_addr mid - mb) (enoent_chars ++ [0]) ∗ E) -∗
      WP (ERun fr : gexpr) {{ result, ∃ p, ⌜result = Ret (WPtr p) /\ p = mid⌝ ∗
        error_text_buffer error_borrowed_text b p ∗
        enoent_lookup_cells lenb lenr tab tabr mid mr ∗ enoent_translation (le_bytes (dci_w bs) 4) ∗ E }}).
Proof using Defines0 Defines1 Defines10 Defines11 Defines12 Defines13 Defines2 Defines3 Defines4 Defines5 Defines6 Defines7 Defines8 Defines9 Hbounds Hdomain Herr Hext Hglobals Hheap Hlk1 Hlk2 Hlkt Hlocale Hral Hrb Hre Hreg Hro Hrr Hsecure Hv.
  intros Hlen Htable Hmessage Hlenb Hlene Hlenr Htab Htal Htabe Htabr Hstring b.
  eexists. split; [reflexivity |]. iIntros "Hobj (Hlookup & Htranslation & #Htext & HE)".
  iDestruct (obj_zero_block with "Hobj") as "(Hbl & Hbytes & Haux)"; [compute; discriminate |].
  assert (Hmid : 0 < ptr_addr mid < 2 ^ 64).
  { destruct Hstring as (_ & Hb & Ha & He & Hr & _). cbn in He. lia. }
  iApply (wp_strerror_enoent _ (mkPtr b (Obj b)) 1024 lenb lenr tab tabr mid mr bs
    (live b (mkRegion b (b + 1024) Heap Live) ∗ bytes b 0 (replicate 1024 0) ∗ E)%I
    with "Hlookup Htranslation [$Hbl $Hbytes $HE]"); try assumption; try reflexivity.
  iNext. iIntros "Hlookup Htranslation (Hbl & Hbytes & HE)".
  iDestruct "Hlookup" as "(#Hll & #Hlen & #Htl & #Hentry & Hml)".
  iAssert (□ live_capq DfracDiscarded (ptr_cap mid) mr)%I with "[Hml]" as "#HmessageLife".
  { destruct (proj1 Hstring) as [Hcap | Hcap]; rewrite Hcap;
      iDestruct "Hml" as "#Hl"; iModIntro; iExact "Hl". }
  iExists mid. iSplit; [done |]. iSplitL "Hbl Hbytes".
  - iExists (replicate 1024 0). iSplit; [iPureIntro; apply length_replicate |]. iFrame.
    iRight. iExists mb, mr, enoent_chars. iFrame "HmessageLife Htext". done.
  - iFrame. unfold enoent_lookup_cells. iFrame "#".
Qed.
End known.

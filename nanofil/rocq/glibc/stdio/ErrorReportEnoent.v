(** Error prints the text for ENOENT after its main message. Printing that
    message may change errno, but the error number to translate remains
    two. The proof composes these calls while keeping their permissions
    to access errno and the calling thread separate.

    Each formatter must return a stream that the following call can use.
    A stream in wide mode cannot enter the next narrow call. The final
    flush also requires an empty buffer; printing a newline does not
    establish that condition. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap
  Language Logic MemLogic StringLogic.
From Glibc Require Import StrerrorEnoentLoan ErrorErrnoLoan ErrorReportNormal
  ErrorTextTail ErrorTextTailNormal ErrorTextPrint FxprintfNormalCall ErrorFlushShort
  DcigettextRouteV DcgettextLocale DcgettextRwlock DcigettextPreRules DcigettextSecure
  ErrlistCode ErrlistEnoent ErrlistFacts StrerrorCode AllocLogic HiAtexitAlloc GetoptMallocGlibc
  StpcpyCode TfindCode TfindEmpty LocalenameCode LocalenameLogic RdlockCode RwunlockCode RdlockLogic
  StrlenLogic MemFwdCode WordString DcgettextCode DcigettextCode DcigettextRoute
  DcgettextC DcgettextReal DcgettextRealV StrerrorEnoent
  OsWorld OsBlocks OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode VfxprintfNarrow ErrorNewline PrintfStateCode ErrorCode
  ErrorCall ErrorEntry ErrorText ErrorMessage ErrorMessageNormal FflushCode FileSyncCode.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section report.
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
Let pack := enoent_translation_pack eb dom dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg
  sec dqs secreg v dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
  a1 ar1 r1 cw1 sh1 fl1 a2 ar2 r2 cw2 sh2 fl2 a3 ar3 r3 cw3 sh3 fl3 tb tid.

(** These resources exclude errno's bytes and auxiliary slots. They contain
    the thread-id permission, but no thread lifetime or cancellation cell. *)
Definition error_enoent_translation_rest : iProp Σ :=
  dci_reads_v dom [108;105;98;99] dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v ∗
  rw_lock a1 ar1 r1 cw1 sh1 fl1 ∗ rw_lock a2 ar2 r2 cw2 sh2 fl2 ∗ rw_lock a3 ar3 r3 cw3 sh3 fl3 ∗
  tfind_root dqr rb ro rreg ∗ locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg ∗
  hi_malloc_state dq mpb tcb dmb mpr tcr dr ∗ int_cell tb 720 tid.

Lemma error_enoent_translation_pack bs :
  error_enoent_translation_rest ∗ errno_own eb bs ⊣⊢ pack bs.
Proof.
  rewrite /error_enoent_translation_rest /pack /enoent_translation_pack /dcg_before_v.
  iSplit.
  - iIntros "[(Hr & H1 & H2 & H3 & HK & HC & HM & Hi) He]".
    iSplitL "Hr H1 H2 H3 HK HC HM He"; [|iExact "Hi"].
    iSplitL "Hr"; [iExact "Hr" |]. iSplitL "H1"; [iExact "H1" |].
    iSplitL "H2"; [iExact "H2" |]. iSplitL "H3"; [iExact "H3" |].
    iSplitL "HK"; [iExact "HK" |]. iSplitL "HC"; [iExact "HC" |].
    iSplitL "HM"; [iExact "HM" |]. iExact "He".
  - iIntros "[(Hr & H1 & H2 & H3 & HK & HC & HM & He) Hi]".
    iSplitL "Hr H1 H2 H3 HK HC HM Hi"; [|iExact "He"].
    iSplitL "Hr"; [iExact "Hr" |]. iSplitL "H1"; [iExact "H1" |].
    iSplitL "H2"; [iExact "H2" |]. iSplitL "H3"; [iExact "H3" |].
    iSplitL "HK"; [iExact "HK" |]. iSplitL "HC"; [iExact "HC" |].
    iSplitL "HM"; [iExact "HM" |]. iExact "Hi".
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
Context (lenb : Z) (lenr : region) (tab : Z) (tabr : region) (mid : ptr) (mb : Z) (mr : region)
  (Hlen : lookup (TAtom "_sys_errlist_internal_len") (ge_globals ge) = Some (mkPtr lenb (Ro lenb)))
  (Htable : lookup (TAtom "_sys_errlist_internal") (ge_globals ge) = Some (mkPtr tab (Ro tab)))
  (Hmessage : lookup (TAtom "glibc_errlist_data_gen#str.249") (ge_globals ge) = Some mid)
  (Hlenb : 0 < lenb) (Hlene : lenb + 8 <= r_end lenr) (Hlenr : r_end lenr <= 2 ^ 48)
  (Htab : 0 < tab) (Htal : tab mod 8 = 0) (Htabe : tab + 24 <= r_end tabr) (Htabr : r_end tabr <= 2 ^ 48)
  (Hstring : string_ok mid mb mr enoent_chars).
Context (ereg : region) (old sgb : Z) (sgreg : region)
  (fb : Z) (freg : region) (fl slb : Z) (slreg : region) (md tm tn : Z) (tr : region)
  (nn : Z) (nr : region) (sb : Z) (sreg : region) (off vb : Z) (vreg : region) (flushframe : frame)
  (fmt : ptr) (fmtb : Z) (fmtreg : region) (dqf dqbytes : dfrac) (chars : list Z)
  (ys : list word) (flags : Z) (wide : ptr) (widefn : func) (wideframe : frame)
  (RM X E : iProp Σ) (QM : Z -> Z -> Z -> iProp Σ).
Let lookup_own := enoent_lookup_cells lenb lenr tab tabr mid mr.
Let static_own := bytesq DfracDiscarded mb (ptr_addr mid - mb) (enoent_chars ++ [0]).
Let format_own := (live_capq dqf (ptr_cap fmt) fmtreg ∗ bytesq dqbytes fmtb (ptr_addr fmt - fmtb) (chars ++ [0]))%I.
Let text_format := (live_capq DfracDiscarded (Ro tn) tr ∗ bytesq DfracDiscarded tn 0 [58;32;37;115;0])%I.
(** Every formatter returns the actual errno resource, with no promise that
    its bytes equal either the saved error or the translation's result. *)
Let resources := (live eb ereg ∗ lookup_own ∗ (∃ bs, pack bs) ∗ X)%I.
Let RT := resources.
Let QT (_ m : Z) := (⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ single_ro ge sb sreg ∗
  live_capq DfracDiscarded (Ro nn) nr ∗ bytesq DfracDiscarded nn 0 [10;0] ∗ resources)%I.
Let RN := (live_capq DfracDiscarded (Ro tn) tr ∗ bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ resources)%I.
Let SN offset (_ m : Z) := (⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗
  error_short_flush_resources fb offset vb vreg sb sreg ∗ RN)%I.
Let Q := error_newline_done fb fl slb slreg nn nr (SN (2 ^ 64 - 1)).
Let P := (∃ now, lookup_own ∗ pack (le_bytes now 4) ∗ static_own ∗ live eb ereg ∗
  single_ro ge sb sreg ∗ error_text_fields fb fl slb slreg tm tn tr ∗ X)%I.
Let text_ready := (single_ro ge sb sreg ∗ error_text_fields fb fl slb slreg tm tn tr ∗ RT)%I.
Let fields := error_message_fields fb fl slb slreg fmt fmtb fmtreg dqf dqbytes chars eb ereg QM.
Context (Hold : old = 0 \/ old = 1) (Hself : ow_self w0 = mkPtr tb (Obj tb))
  (Htb : 0 < tb) (Hta : tb mod 8 = 0) (Hte : tb + 796 <= r_end tbreg) (Htr : r_end tbreg <= 2 ^ 63)
  (Hcancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate))
  (Hg : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sgb (Obj sgb)))
  (Hgb : 0 < sgb) (Hga : sgb mod 8 = 0) (Hge : sgb + 8 <= r_end sgreg) (Hgr : r_end sgreg <= 2 ^ 63)
  (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg) (Hfr : r_end freg <= 2 ^ 63)
  (Huser : Z.land fl 32768 = 0) (Hbackup : Z.land fl 256 = 0)
  (Htn : 0 <= tn < 2 ^ 64) (Hnn : 0 <= nn < 2 ^ 64)
  (Hmd : md = 0 \/ md = 2 ^ 32 - 1) (Htm : tm = 0 \/ tm = 2 ^ 32 - 1)
  (Hfmtr : 0 <= ptr_addr fmt < 2 ^ 64) (Hfmtstring : string_ok fmt fmtb fmtreg chars)
  (Herrno : error_errno_bounds eb ereg)
  (Htext : lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some (mkPtr tn (Ro tn)))
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some (mkPtr nn (Ro nn)))
  (Hfx : find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf))
  (Hvfx : find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf))
  (Hstr : find_fn ge (TAtom "__GI___strerror_r") = Some (Defined glibc_strerror_r))
  (Hflush : find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined glibc__IO_fflush))
  (Hfframe : call_frame glibc__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some flushframe)
  (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync)
  (Hwide : lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide)
  (Hwidefn : find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn))
  (Hwideframe : call_frame widefn [WPtr wide;WPtr (mkPtr fb (Obj fb))] = Some wideframe)
  (Hwidecall : forall r en m, 0 < m < 2 ^ 31 -> ⊢ live fb freg -∗ int_cell fb 192 m -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en m) -∗
    WP (ERun wideframe : gexpr) {{ w, ∃ result, ⌜w = Ret (WInt result)⌝ ∗ live fb freg ∗ int_cell fb 192 m ∗
      (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en m) }})
  (Hproducer : forall r en m, int_cell fb 192 m ∗ QM r en m ⊢
    single_ro ge sb sreg ∗ int_cell fb 192 tm ∗ text_format ∗ X)
  (Htextformat : forall b p ap, vfxprintf_formatter fb freg fl slb slreg (mkPtr tn (Ro tn)) ap 0 tm DfracDiscarded tr
    (fun q => fx_va q [WPtr null;WPtr (mkPtr tn (Ro tn));WPtr p])
    (bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ RT)%I
    (fun r => bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ m, int_cell fb 192 m ∗ QT r m)%I)
  (Hnewlineformat : forall m, m = 0 \/ m = 2 ^ 32 - 1 -> forall ap,
    vfxprintf_formatter fb freg fl slb slreg (mkPtr nn (Ro nn)) ap 0 m DfracDiscarded nr
      (fun q => fx_va q [WPtr null;WPtr (mkPtr nn (Ro nn))])
      (bytesq DfracDiscarded nn 0 [10;0] ∗ RN)%I
      (fun r => bytesq DfracDiscarded nn 0 [10;0] ∗ ∃ m', int_cell fb 192 m' ∗ SN off r m')%I).

(** The concrete call returns the thread lifetime before text printing.
    Its input errno is existentially supplied by the preceding message. *)
Lemma error_report_enoent_strcall b :
  exists fr, call_frame glibc_strerror_r [WInt 2;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ live tb tbreg -∗ P -∗ WP (ERun fr : gexpr)
      {{ w, ∃ p, ⌜w = Ret (WPtr p)⌝ ∗ live tb tbreg ∗ error_text_buffer error_borrowed_text b p ∗ text_ready }}).
Proof.
  destruct (error_strerror_enoent_thread_call eb Herr Hreg Hext dom dqd nb nc k cat dqc cv p276 p277 db dqb dbreg
    ib ic dqi ireg sec dqs secreg v tc dd dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg
    dql dqn dqt treg lk1 a1 ar1 r1 cw1 sh1 fl1 lk2 a2 ar2 r2 cw2 sh2 fl2 lkt a3 ar3 r3 cw3 sh3 fl3 tb tbreg tid
    Hheap Hlk1 Hlk2 Hlkt Hlocale Hrb Hro Hral Hre Hrr Hglobals Hbounds Hv Hsecure Hdomain
    lenb lenr tab tabr mid mb mr [] emp Hlen Htable Hmessage Hlenb Hlene Hlenr Htab Htal Htabe Htabr Hstring b)
    as (fr & Hframe & _).
  exists fr. split; [done |]. iIntros "Hb Ht HP".
  iDestruct "HP" as (now) "(Hlookup & Hpack & Hstatic & He & Hs & Hfields & HX)".
  destruct (error_strerror_enoent_thread_call eb Herr Hreg Hext dom dqd nb nc k cat dqc cv p276 p277 db dqb dbreg
    ib ic dqi ireg sec dqs secreg v tc dd dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg
    dql dqn dqt treg lk1 a1 ar1 r1 cw1 sh1 fl1 lk2 a2 ar2 r2 cw2 sh2 fl2 lkt a3 ar3 r3 cw3 sh3 fl3 tb tbreg tid
    Hheap Hlk1 Hlk2 Hlkt Hlocale Hrb Hro Hral Hre Hrr Hglobals Hbounds Hv Hsecure Hdomain
    lenb lenr tab tabr mid mb mr (le_bytes now 4) emp Hlen Htable Hmessage Hlenb Hlene Hlenr Htab Htal Htabe Htabr Hstring b)
    as (fr' & Hframe' & Hcall).
  assert (fr' = fr) by congruence. subst fr'.
  iApply (wp_wand with "[Hb Ht Hlookup Hpack Hstatic]").
  { iApply (Hcall with "Hb Ht [$Hlookup $Hpack $Hstatic]"). }
  iIntros (w) "H". iDestruct "H" as (p [-> Hp]) "(Ht & Hb & Hlookup & Hpack & _)".
  iExists p. iSplit; [done |]. iFrame "Ht Hb". unfold text_ready, RT, resources. iFrame.
Qed.

(** The report assembles errno from the actual message return, then calls
    concrete strerror and the narrow text and newline wrappers. The final
    flush uses the returned short-buffer permissions, not an emptiness
    inference from the newline. The original message cursor and format
    return once, outside the translation resources. *)
Lemma wp_error_report_enoent e from ap cb countb countreg count Φ :
  error_inputs e 0 2 fmt ap flags cb ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr countb (Obj countb)) ->
  0 < countb -> countb + 4 <= r_end countreg -> r_end countreg <= 2 ^ 63 ->
  vfxprintf_formatter fb freg fl slb slreg fmt ap (flags mod 2 ^ 32) md dqf fmtreg
    (fun p => error_va p (WInt 0 :: WInt 2 :: WPtr fmt :: ys))
    (bytesq dqbytes fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ RM)%I
    (fun r => bytesq dqbytes fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
      ∃ en m, live eb ereg ∗ int_cell eb 0 en ∗ int_cell fb 192 m ∗ QM (r mod 2 ^ 32) en m)%I ->
  live countb countreg -∗ int_cell countb 0 count -∗ live tb tbreg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sgb sgreg -∗ pcell sgb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
  error_va ap (WInt 0 :: WInt 2 :: WPtr fmt :: ys) -∗
  (single_ro ge sb sreg ∗ int_cell fb 0 fl ∗ pcell fb 136 (mkPtr slb (Obj slb)) ∗
    lock_state slb slreg 0 0 null ∗ int_cell fb 192 md ∗ format_own ∗ RM) -∗
  error_enoent_translation_rest -∗ error_errno_aux eb -∗ lookup_own -∗ static_own -∗ E -∗
  (live countb countreg -∗ int_cell countb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch error_borrowed_text 2 -∗
    live tb tbreg -∗ int_cell tb 792 old -∗ live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sgb sgreg -∗ pcell sgb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
    error_va ap (WInt 0 :: WInt 2 :: WPtr fmt :: ys) -∗ format_own -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof.
  intros Hinputs Hcount Hcb Hce Hcr Hformat.
  iIntros "Hcl Hcount Ht Hflag Hbl Hsaved Hgl Hgp Hl HV HP Hrest Haux Hlookup Hstatic HE HK".
  iDestruct "HP" as "(Hs & Hfl & Hlp & Hlk & Hmd & [Hfmt Hbytes] & HRM)".
  iApply (wp_error_message_normal Hreg Hext fb freg fl slb slreg md fmt fmtb fmtreg dqf dqbytes chars
    ap 0 2 ys flags sb sreg sgb sgreg eb ereg RM
    (live countb countreg ∗ int_cell countb 0 count ∗ live tb tbreg ∗ int_cell tb 792 1 ∗
      live cb (mkRegion cb (cb + 16) Heap Live) ∗ int_cell cb 0 old ∗
      error_enoent_translation_rest ∗ error_errno_aux eb ∗ lookup_own ∗ static_own ∗ E)%I QM
    with "Hgl Hgp Hl HV [$Hs $Hfl $Hlp $Hlk $Hmd $Hfmt $Hbytes $HRM] [$Hcl $Hcount $Ht $Hflag $Hbl $Hsaved $Hrest $Haux $Hlookup $Hstatic $HE]");
    try eassumption; try (rewrite Hself; cbn; lia).
  iIntros (e' predecessor r en m Hinputs') "Hgl Hgp Hl HV Hreturned Hfields (Hcl & Hcount & Ht & Hflag & Hbl & Hsaved & Hrest & Haux & Hlookup & Hstatic & HE)".
  iDestruct "Hfields" as "(Hfl & Hlp & Hlk & Hfmt & Hbytes & Hspare & HQM)".
  iDestruct (error_message_errno_loan with "Hreturned Hspare Haux") as (now Hnow) "(He & Herrno & Hmode)".
  iDestruct (Hproducer r en m with "[$Hmode $HQM]") as "(Hs & Hmode & Htf & HX)".
  iAssert P with "[Hrest Herrno Hlookup Hstatic He Hs Hmode Htf HX Hfl Hlp Hlk]" as "HP".
  { iExists now. iSplitL "Hlookup"; [iExact "Hlookup" |]. iSplitL "Hrest Herrno".
    - rewrite -error_enoent_translation_pack. iFrame.
    - iFrame "Hstatic He Hs HX". unfold error_text_fields. iDestruct "Htf" as "[Htf Htb]". iFrame. }
  assert (Hflushcall : ⊢ live fb freg -∗ error_newline_done fb fl slb slreg nn nr (SN off) -∗
    WP (ERun flushframe : gexpr) {{ w, ∃ z, ⌜w = Ret (WInt z)⌝ ∗ live fb freg ∗ Q }}).
  { iIntros "Hl Hdone". iApply (wp_wand with "[Hl Hdone]").
    { iApply (wp_error_flush_short Hreg Hext Hsync flushframe fb freg fl off slb slreg nn nr vb vreg sb sreg RN
        with "Hl Hdone"); try assumption; rewrite Hself; cbn; lia. }
    iIntros (w) "H". iDestruct "H" as (z [-> Hz]) "[Hl HQ]". iExists z. iFrame. done. }
  iApply (wp_error_text_tail_thread_loan Hreg Hext tb tbreg old sgb sgreg (mkPtr fb (Obj fb)) (DfracOwn 1) freg
    (mkPtr nn (Ro nn)) glibc_fxprintf (fxprintf_normal_frame null (mkPtr nn (Ro nn)) []) glibc__IO_fflush flushframe
    (error_text_newline_ready fb fl slb slreg nn nr sb sreg RN)
    (error_newline_done fb fl slb slreg nn nr (SN off)) Q text_ready
    (error_va ap (WInt 0 :: WInt 2 :: WPtr fmt :: ys) ∗ format_own ∗ E)%I
    Hold Hself Htb Hta Hte Htr Hcancel Hg Hgb Hga Hge ltac:(cbn; lia)
    Hnewline Hfx ltac:(apply fxprintf_normal_call_frame) Hflush Hfframe Hflushcall
    P (error_text_done fb fl slb slreg tn tr QT)
    with "Hcl Hcount Ht Hflag Hbl Hsaved Hgl Hgp Hl HP [$HV $Hfmt $Hbytes $HE]"); try eassumption.
  - iIntros "Hgl Hgp Hl Hready". iDestruct "Hready" as (m' Hnarrow) "HR".
    iApply (wp_error_newline Hreg Hext fb freg fl slb slreg m' nn nr sb sreg sgb sgreg RN (SN off)
      with "Hgl Hgp Hl HR"); try assumption; try (rewrite Hself; cbn; lia).
    apply Hnewlineformat; done.
  - lia.
  - exact error_report_enoent_strcall.
  - intros b p. exists (fxprintf_normal_frame null (mkPtr tn (Ro tn)) [WPtr p]).
    split; [apply fxprintf_normal_call_frame |]. iIntros "Hgl Hgp Hl Hb HT".
    iApply (wp_error_text_print Hreg Hext fb freg fl slb slreg tm tn tr sb sreg sgb sgreg b p RT QT
      with "Hgl Hgp Hl Hb HT"); try assumption; try (rewrite Hself; cbn; lia).
    apply Htextformat.
  - cbn. exact (error_text_to_newline fb fl slb slreg tn tr nn nr sb sreg resources).
  - iIntros "Hcl Hcount Hscratch Ht Hflag Hbl Hsaved Hgl Hgp Hl HQ (HV & Hfmt & HE)".
    iApply ("HK" with "Hcl Hcount Hscratch Ht Hflag Hbl Hsaved Hgl Hgp Hl HV Hfmt HQ HE").
Qed.
End report.

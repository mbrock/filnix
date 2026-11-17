(** A public error call can print the default program-name prefix and an
    ENOENT report after stdout has closed. This proof uses the real strerror
    lookup and translation, and both real flushes. The formatters must still
    supply the actual modes and memory permissions needed by the next call.

    The translation locks read the current thread's id. The caller supplies
    permission to read it, and receives that permission back. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap
  Language Logic MemLogic StringLogic Identity VariadicLogic.
From Glibc Require Import StrerrorEnoentLoan ErrorErrnoLoan ErrorReportEnoent
  ErrorTextTail ErrorTextTailNormal ErrorTextPrint FxprintfNormalCall ErrorFlushShort
  DcigettextRouteV DcgettextLocale DcgettextRwlock DcigettextPreRules DcigettextSecure
  ErrlistCode ErrlistEnoent ErrlistFacts StrerrorCode AllocLogic HiAtexitAlloc GetoptMallocGlibc
  StpcpyCode TfindCode TfindEmpty LocalenameCode LocalenameLogic RdlockCode RwunlockCode RdlockLogic
  StrlenLogic MemFwdCode WordString DcgettextCode DcigettextCode DcigettextRoute
  DcgettextC DcgettextReal DcgettextRealV StrerrorEnoent
  OsWorld OsBlocks OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode VfxprintfNarrow ErrorNewline PrintfStateCode ErrorCode
  ErrorCall ErrorEntry ErrorText ErrorMessage ErrorMessageNormal FflushCode FileSyncCode
  ErrorPrefix HelloErrorPrefix HelloErrorClosed HelloErrorCall HelloErrorReturning HelloErrorDefaultCall.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section returning.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Lock placement needs only enough of the actual thread region to read
    the id. Replacing the region in this pure condition does not create
    or change any lifetime permission. *)
Lemma error_rw_ready_region lk a ar tb before after r cw tid :
  rw_ready lk a ar tb before r cw tid ->
  tb + 796 <= r_end after -> r_end after <= 2 ^ 63 ->
  rw_ready lk a ar tb after r cw tid.
Proof using Type.
  unfold rw_ready, rw_place. intros ((? & ? & ? & ? & ? & ? & ? & ? & ?) & ? & ? & ? & ?) ? ?.
  repeat split; try assumption; lia.
Qed.

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
Let rest_own := error_enoent_translation_rest dom dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg
  sec dqs secreg v dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
  a1 ar1 r1 cw1 sh1 fl1 a2 ar2 r2 cw2 sh2 fl2 a3 ar3 r3 cw3 sh3 fl3 tb tid.
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
  (ys : list word) (wide : ptr) (widefn : func) (wideframe : frame)
  (RM X : iProp Σ) (QM : Z -> Z -> Z -> iProp Σ).
Let lookup_own := enoent_lookup_cells lenb lenr tab tabr mid mr.
Let static_own := bytesq DfracDiscarded mb (ptr_addr mid - mb) (enoent_chars ++ [0]).
Let format_own := (live_capq dqf (ptr_cap fmt) fmtreg ∗ bytesq dqbytes fmtb (ptr_addr fmt - fmtb) (chars ++ [0]))%I.
Let text_format := (live_capq DfracDiscarded (Ro tn) tr ∗ bytesq DfracDiscarded tn 0 [58;32;37;115;0])%I.
Let resources := (live eb ereg ∗ lookup_own ∗ (∃ bs, pack bs) ∗ X)%I.
Let QT (_ m : Z) := (⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ single_ro ge sb sreg ∗
  live_capq DfracDiscarded (Ro nn) nr ∗ bytesq DfracDiscarded nn 0 [10;0] ∗ resources)%I.
Let RN := (live_capq DfracDiscarded (Ro tn) tr ∗ bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ resources)%I.
Let SN offset (_ m : Z) := (⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ error_short_flush_resources fb offset vb vreg sb sreg ∗ RN)%I.
Let Q := error_newline_done fb fl slb slreg nn nr (SN (2 ^ 64 - 1)).
Let fields := error_message_fields fb fl slb slreg fmt fmtb fmtreg dqf dqbytes chars eb ereg QM.
Let message_ready := (single_ro ge sb sreg ∗ int_cell fb 0 fl ∗ pcell fb 136 (mkPtr slb (Obj slb)) ∗
  lock_state slb slreg 0 0 null ∗ int_cell fb 192 md ∗ format_own ∗ RM)%I.
Context (Hold : old = 0 \/ old = 1) (Hself : ow_self w0 = mkPtr tb (Obj tb))
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
    (bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ resources)%I
    (fun r => bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ m, int_cell fb 192 m ∗ QT r m)%I)
  (Hnewlineformat : forall m, m = 0 \/ m = 2 ^ 32 - 1 -> forall ap,
    vfxprintf_formatter fb freg fl slb slreg (mkPtr nn (Ro nn)) ap 0 m DfracDiscarded nr
      (fun q => fx_va q [WPtr null;WPtr (mkPtr nn (Ro nn))])
      (bytesq DfracDiscarded nn 0 [10;0] ∗ RN)%I
      (fun r => bytesq DfracDiscarded nn 0 [10;0] ∗ ∃ m', int_cell fb 192 m' ∗ SN off r m')%I)
  (Hformat : forall ap, vfxprintf_formatter fb freg fl slb slreg fmt ap 0 md dqf fmtreg
    (fun p => error_va p (WInt 0 :: WInt 2 :: WPtr fmt :: ys))
    (bytesq dqbytes fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ RM)%I
    (fun r => bytesq dqbytes fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
      ∃ en m, live eb ereg ∗ int_cell eb 0 en ∗ int_cell fb 192 m ∗ QM (r mod 2 ^ 32) en m)%I).

Context (ofb : Z) (ofreg : region) (ovb olb : Z) (olreg : region) (ob : Z) (oreg : region)
  (pb : Z) (preg : region) (pnb : Z) (pnreg : region) (pname : ptr) (dqname : dfrac) (namer : region)
  (ovreg : region) (osb : Z) (osreg : region)
  (countb : Z) (countreg : region) (count : Z)
  (pmd pxb : Z) (pxreg : region) (nameb : Z) (dqnb : dfrac) (namechars : list Z)
  (PR K Ready : iProp Σ) (PQ : Z -> Z -> iProp Σ).
Let loan := error_stdout_loan ofb ofreg ob oreg.
Let private := error_private_cells pb preg null DfracDiscarded preg pnb pnreg pname dqname namer.
Let name := error_prefix_name pname nameb namer dqnb namechars.
Let kept := (error_closed_flush ofb ovb olb olreg ovreg osb osreg K ∗ name)%I.
Let stderr_loan := (live sgb sgreg ∗ pcell sgb 0 (mkPtr fb (Obj fb)) ∗ live fb freg)%I.
Let prefix := mkPtr pxb (Ro pxb).
Let returned := error_returned ofb ofreg ob oreg pb preg null DfracDiscarded preg pnb pnreg pname dqname namer
  2 fmt ys old sgb sgreg fb (DfracOwn 1) freg countb countreg count error_borrowed_text (format_own ∗ Q)%I kept.

(** The prefix-to-message exchange is only a permission exchange. It must
    justify the actual returned mode and supply the translation resources;
    looking up a name or printing a prefix supplies neither of those. *)
Context (Hpost : Ready ⊢ live countb countreg ∗ int_cell countb 0 count ∗
  stderr_loan ∗ message_ready ∗ rest_own ∗ error_errno_aux eb ∗ lookup_own ∗ static_own ∗ kept)
  (Hcount : lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr countb (Obj countb)))
  (Hcountb : 0 < countb) (Hcounte : countb + 4 <= r_end countreg) (Hcountr : r_end countreg <= 2 ^ 63).

(** This endpoint has no custom callback, report, strerror or flush contract.
    Its call premises are the four formatters and the report's fallback.
    Cancellation is disabled for the report and restored to its saved state. *)
Lemma wp_call_error_enoent_zero f e ls l args rest j (D E : iProp Σ) Φ :
  let flush := error_closed_flush ofb ovb olb olreg ovreg osb osreg D in
  map_option (arg_x ge e) args = Some (WInt 0 :: WInt 2 :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "error") = Some (Defined glibc_error) -> forallb snapshot_word ys = true ->
  find_fn ge (TAtom "__error_internal") = Some (Defined glibc_error_internal) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  0 < ofb -> ofb mod 8 = 0 -> ofb + 224 <= r_end ofreg -> r_end ofreg <= 2 ^ 63 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr pnb (Obj pnb)) ->
  0 < pnb -> pnb mod 8 = 0 -> pnb + 8 <= r_end pnreg -> r_end pnreg <= 2 ^ 63 ->
  0 <= ptr_addr pname < 2 ^ 64 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  0 <= pxb < 2 ^ 64 -> pmd = 0 \/ pmd = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  (D ⊢ stderr_loan ∗ error_prefix_fields fb fl slb slreg pmd pxb pxreg ∗ name ∗ PR) ->
  (forall r m, error_closed_flush ofb ovb olb olreg ovreg osb osreg
    (stderr_loan ∗ error_prefix_fields fb fl slb slreg m pxb pxreg ∗ name ∗ PQ r m) ⊢ Ready) ->
  (forall fx_ap, vfxprintf_formatter fb freg fl slb slreg prefix fx_ap 0 pmd DfracDiscarded pxreg
    (fun q => fx_va q [WPtr null;WPtr prefix;WPtr pname])
    (bytesq DfracDiscarded pxb 0 [37;115;58;32;0] ∗ live_capq dqname (ptr_cap pname) namer ∗ name ∗ PR)%I
    (fun r => bytesq DfracDiscarded pxb 0 [37;115;58;32;0] ∗ live_capq dqname (ptr_cap pname) namer ∗
      name ∗ ∃ m, int_cell fb 192 m ∗ PQ r m)%I) ->
  error_thread_ready old -∗ loan -∗ private -∗ flush -∗ E -∗
  ▷ (returned -∗ E -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call CVoid (Global (TAtom "error")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Defines0 Defines1 Defines10 Defines11 Defines12 Defines13 Defines2 Defines3 Defines4 Defines5 Defines6 Defines7 Defines8 Defines9 Hal Hbackup Hbounds Hcancel Hcount Hcountb Hcounte Hcountr Hdomain Hend Herr Herrno Hext Hfb Hfframe Hflush Hfmtr Hfmtstring Hformat Hfr Hfx Hg Hga Hgb Hge Hglobals Hgr Hheap Hlen Hlenb Hlene Hlenr Hlk1 Hlk2 Hlkt Hlocale Hmd Hmessage Hnewline Hnewlineformat Hnn Hold Hpost Hproducer Hral Hrb Hre Hreg Hro Hrr Hsecure Hself Hstr Hstring Hsync Htab Htabe Htable Htabr Htal Htext Htextformat Htm Htn Huser Hv Hvfx Hwide Hwidecall Hwidefn Hwideframe Q.
  intros flush Hargs Hpublic Hys Hinternal Ho Hob Hoa Hoe Hor Hofb Hofa Hofe Hofr
    Hp Hpb Hpa Hpe Hpr Hn Hnb Hna Hne Hnr Hnu Hprefix Hpxb Hpmd Hself0 Hselfr Hlend Hready Hprefixformat.
  iIntros "Ht Ho Hp Hflush HE HK".
  iApply (wp_call_error_default_closed ofb ofreg ovb olb olreg ob oreg pb preg pnb pnreg pname dqname namer
    Hreg Hext Hsync f e ls l args rest j 0 2 fmt ys old ovreg osb osreg prefix glibc_fxprintf
    (fxprintf_normal_frame null prefix [WPtr pname]) D Ready returned E
    with "Ht Ho Hp Hflush HE HK"); try assumption; try (split; lia).
  { apply (wp_error_closed_prefix Hreg Hext ofb ovb olb olreg pname dqname namer
      fb freg fl slb slreg pmd pxb pxreg sgb sgreg nameb dqnb namechars ovreg osb osreg D PR Ready PQ);
      assumption. }
  intros actual_tb actual_reg jb ap Hthread Htb Hta Hte Htr.
  assert (actual_tb = tb) by (rewrite Hself in Hthread; injection Hthread; auto). subst actual_tb.
  assert (Hlk1' : rw_ready lk1 a1 ar1 tb actual_reg r1 cw1 tid) by (eapply error_rw_ready_region; eassumption).
  assert (Hlk2' : rw_ready lk2 a2 ar2 tb actual_reg r2 cw2 tid) by (eapply error_rw_ready_region; eassumption).
  assert (Hlkt' : rw_ready lkt a3 ar3 tb actual_reg r3 cw3 tid) by (eapply error_rw_ready_region; eassumption).
  iIntros (env from saved Hinputs) "Ht Hflag Hsavedl Hsaved Ho Hp Hready [Hva Hcleanup]".
  iDestruct (Hpost with "Hready") as "(Hnl & Hcount & [Hsl [Hsp Hfl]] & HP & Hrest & Haux & Hlookup & Hstatic & HK)".
  iApply (wp_error_report_enoent eb Herr Hreg Hext dom dqd nb nc k cat dqc cv p276 p277 db dqb dbreg
    ib ic dqi ireg sec dqs secreg v tc dd dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg
    dql dqn dqt treg lk1 a1 ar1 r1 cw1 sh1 fl1 lk2 a2 ar2 r2 cw2 sh2 fl2 lkt a3 ar3 r3 cw3 sh3 fl3 tb actual_reg tid
    Hheap Hlk1' Hlk2' Hlkt' Hlocale Hrb Hro Hral Hre Hrr Hglobals Hbounds Hv Hsecure Hdomain
    lenb lenr tab tabr mid mb mr Hlen Htable Hmessage Hlenb Hlene Hlenr Htab Htal Htabe Htabr Hstring
    ereg old sgb sgreg fb freg fl slb slreg md tm tn tr nn nr sb sreg off vb vreg flushframe
    fmt fmtb fmtreg dqf dqbytes chars ys 0 wide widefn wideframe RM X
    (loan ∗ private ∗ error_cleanup_fields tb jb ∗ kept)%I QM
    with "Hnl Hcount Ht Hflag Hsavedl Hsaved Hsl Hsp Hfl Hva HP Hrest Haux Hlookup Hstatic [$Ho $Hp $Hcleanup $HK]");
    try eassumption.
  { apply Hformat. }
  iIntros "Hnl Hcount Hscratch Ht Hflag Hsavedl Hsaved Hsl Hsp Hfl Hva Hfmt HQ (Ho & Hp & Hcleanup & HK)".
  iSplit; [done |]. unfold returned, error_returned.
  iExists ap, saved. iSplitL "Ht Hflag Hcleanup".
  { unfold error_thread_ready. iExists tb, actual_reg, jb. iFrame. done. }
  iFrame "Ho Hp Hsavedl Hsaved Hnl Hcount Hscratch Hsl Hsp Hfl Hva Hfmt HQ HK".
Qed.
End returning.

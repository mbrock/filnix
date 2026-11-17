(** A returning error report prints its message, optional errno text and
    newline before flushing stderr and restoring cancellation. This rule
    composes the actual narrow message call with the two normal wrappers.
    Formatter, fallback, strerror and flush implementations remain explicit
    contracts.

    Printing can leave stderr in a positive mode. In particular, the ENOMEM
    fallback preserves that mode, so this rule cannot establish readiness
    for the next narrow call on that path. The caller must prove each
    readiness exchange; the rule does not repair the mode. It retains the
    original cursor and message format permissions throughout the report. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap
  Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode VfxprintfNarrow ErrorNewline PrintfStateCode ErrorCode
  ErrorCall ErrorEntry ErrorText ErrorTextPrint ErrorTextTailNormal ErrorMessage
  ErrorMessageNarrow ErrorMessageNormal.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section report.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (tb : Z) (treg : region) (old : Z) (gb : Z) (greg : region)
  (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (md tm tn : Z) (tr : region)
  (nn : Z) (nr : region) (sb : Z) (sreg : region) (flushfn : func) (flushframe : frame)
  (fmt : ptr) (fmtb : Z) (fmtreg : region) (dqf dqb : dfrac) (chars : list Z)
  (errnum : Z) (ys : list word) (flags eb : Z) (ereg : region)
  (wide : ptr) (widefn : func) (wideframe : frame)
  (P0 RM P RT RN : iProp Σ) (QM : Z -> Z -> Z -> iProp Σ)
  (QT SN : Z -> Z -> iProp Σ) (Q E : iProp Σ).
Let format_own := (live_capq dqf (ptr_cap fmt) fmtreg ∗
  bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]))%I.
Let message_ready := (single_ro ge sb sreg ∗ int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗
  lock_state lb lbreg 0 0 null ∗ int_cell fb 192 md ∗ format_own ∗ RM)%I.
Let remaining r en m := (int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗
  lock_state lb lbreg 0 0 null ∗ error_message_spare fb eb ereg r en m ∗ QM r en m)%I.
Let fields := error_message_fields fb fl lb lbreg fmt fmtb fmtreg dqf dqb chars eb ereg QM.
Let text_ready := (single_ro ge sb sreg ∗ error_text_fields fb fl lb lbreg tm tn tr ∗ RT)%I.
Context (Hold : old = 0 \/ old = 1) (Hself : ow_self w0 = mkPtr tb (Obj tb))
  (Htb : 0 < tb) (Hta : tb mod 8 = 0) (Hte : tb + 796 <= r_end treg) (Htr : r_end treg <= 2 ^ 63)
  (Hcancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate))
  (Hg : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)))
  (Hgb : 0 < gb) (Hga : gb mod 8 = 0) (Hge : gb + 8 <= r_end greg) (Hgr : r_end greg <= 2 ^ 63)
  (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg) (Hfr : r_end freg <= 2 ^ 63)
  (Huser : Z.land fl 32768 = 0) (Htn : 0 <= tn < 2 ^ 64) (Hnn : 0 <= nn < 2 ^ 64)
  (Hmd : md = 0 \/ md = 2 ^ 32 - 1) (Htm : tm = 0 \/ tm = 2 ^ 32 - 1)
  (Hfmtr : 0 <= ptr_addr fmt < 2 ^ 64) (Hstring : StringLogic.string_ok fmt fmtb fmtreg chars)
  (Herrno : error_errno_bounds eb ereg)
  (Htext : lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some (mkPtr tn (Ro tn)))
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some (mkPtr nn (Ro nn)))
  (Hfx : find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf))
  (Hvfx : find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf))
  (Hflush : find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn))
  (Hfframe : call_frame flushfn [WPtr (mkPtr fb (Obj fb))] = Some flushframe)
  (Hwide : lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide)
  (Hwidefn : find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn))
  (Hwideframe : call_frame widefn [WPtr wide;WPtr (mkPtr fb (Obj fb))] = Some wideframe)
  (Hwidecall : forall r en m, 0 < m < 2 ^ 31 -> ⊢ live fb freg -∗ int_cell fb 192 m -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en m) -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ result, ⌜v = Ret (WInt result)⌝ ∗
      live fb freg ∗ int_cell fb 192 m ∗
      (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en m) }})
  (Hentry : P0 ⊢ message_ready)
  (Htext_exchange : forall r en m, error_message_returned fb freg eb ereg r en m ∗ remaining r en m ⊢ P)
  (Htextformat : forall b p ap, vfxprintf_formatter fb freg fl lb lbreg (mkPtr tn (Ro tn)) ap 0 tm DfracDiscarded tr
    (fun q => fx_va q [WPtr null;WPtr (mkPtr tn (Ro tn));WPtr p])
    (bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ RT)%I
    (fun r => bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ m, int_cell fb 192 m ∗ QT r m)%I)
  (Hnewlineformat : forall m, m = 0 \/ m = 2 ^ 32 - 1 -> forall ap,
    vfxprintf_formatter fb freg fl lb lbreg (mkPtr nn (Ro nn)) ap 0 m DfracDiscarded nr
      (fun q => fx_va q [WPtr null;WPtr (mkPtr nn (Ro nn))])
      (bytesq DfracDiscarded nn 0 [10;0] ∗ RN)%I
      (fun r => bytesq DfracDiscarded nn 0 [10;0] ∗ ∃ m', int_cell fb 192 m' ∗ SN r m')%I)
  (Hflushcall : ⊢ live fb freg -∗ error_newline_done fb fl lb lbreg nn nr SN -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live fb freg ∗ Q }}).

(** The supplied state must justify entering the narrow message call.
    Message handling then returns the permissions used to prepare errno
    text or, for zero errno, the newline directly. The original message
    format stays separate from both exchanges and returns to the caller. *)
Lemma wp_error_report_normal_zero e from ap cb countb countreg count strerrorfn Φ :
  error_inputs e 0 errnum fmt ap flags cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr countb (Obj countb)) ->
  0 < countb -> countb + 4 <= r_end countreg -> r_end countreg <= 2 ^ 63 ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ P -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer error_borrowed_text b p ∗ text_ready }})) ->
  ((if decide (errnum = 0) then P else error_text_done fb fl lb lbreg tn tr QT) ⊢
    error_text_newline_ready fb fl lb lbreg nn nr sb sreg RN) ->
  vfxprintf_formatter fb freg fl lb lbreg fmt ap (flags mod 2 ^ 32) md dqf fmtreg
    (fun p => error_va p (WInt 0 :: WInt errnum :: WPtr fmt :: ys))
    (bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ RM)%I
    (fun r => bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
      ∃ en m, live eb ereg ∗ int_cell eb 0 en ∗ int_cell fb 192 m ∗ QM (r mod 2 ^ 32) en m)%I ->
  live countb countreg -∗ int_cell countb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
  error_va ap (WInt 0 :: WInt errnum :: WPtr fmt :: ys) -∗ P0 -∗ E -∗
  (live countb countreg -∗ int_cell countb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch error_borrowed_text errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
    error_va ap (WInt 0 :: WInt errnum :: WPtr fmt :: ys) -∗ format_own -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Hal Hcancel Hend Hentry Herrno Hext Hfb Hfframe Hflush Hflushcall Hfmtr Hfr Hfx Hg Hga Hgb Hge Hgr Hmd Hnewline Hnewlineformat Hnn Hold Hreg Hself Hstring Hta Htb Hte Htext Htext_exchange Htextformat Htm Htn Htr Huser Hvfx Hwide Hwidecall Hwidefn Hwideframe.
  intros Hinputs Herr Hcount Hcb Hce Hcr Hstr Hstrcall Hready Hformat.
  iIntros "Hcl Hcount Ht Hflag Hbl Hsaved Hgl Hgp Hl HV HP HE HK".
  iDestruct (Hentry with "HP") as "HP".
  iDestruct "HP" as "(Hs & Hfl & Hlp & Hlk & Hmd & [Hfmt Hbytes] & HRM)".
  iApply (wp_error_message_normal Hreg Hext fb freg fl lb lbreg md fmt fmtb fmtreg dqf dqb chars
    ap 0 errnum ys flags sb sreg gb greg eb ereg RM
    (live countb countreg ∗ int_cell countb 0 count ∗ live tb treg ∗ int_cell tb 792 1 ∗
      live cb (mkRegion cb (cb + 16) Heap Live) ∗ int_cell cb 0 old ∗ E)%I QM
    with "Hgl Hgp Hl HV [$Hs $Hfl $Hlp $Hlk $Hmd $Hfmt $Hbytes $HRM] [$Hcl $Hcount $Ht $Hflag $Hbl $Hsaved $HE]");
    try eassumption; try (rewrite Hself; cbn; lia).
  iIntros (e' predecessor r en m Hinputs') "Hgl Hgp Hl HV Hreturned Hfields (Hcl & Hcount & Ht & Hflag & Hbl & Hsaved & HE)".
  iDestruct "Hfields" as "(Hfl & Hlp & Hlk & Hfmt & Hbytes & Hspare & HQM)".
  iDestruct (Htext_exchange r en m with "[$Hreturned $Hfl $Hlp $Hlk $Hspare $HQM]") as "HP".
  iApply (wp_error_text_tail_normal Hreg Hext tb treg old gb greg fb freg fl lb lbreg tm tn tr
    nn nr sb sreg flushfn flushframe P RT RN QT SN Q
    (error_va ap (WInt 0 :: WInt errnum :: WPtr fmt :: ys) ∗ format_own ∗ E)%I
    with "Hcl Hcount Ht Hflag Hbl Hsaved Hgl Hgp Hl HP [$HV $Hfmt $Hbytes $HE]"); try eassumption.
  iIntros "Hcl Hcount Hscratch Ht Hflag Hbl Hsaved Hgl Hgp Hl HQ (HV & Hfmt & HE)".
  iApply ("HK" with "Hcl Hcount Hscratch Ht Hflag Hbl Hsaved Hgl Hgp Hl HV Hfmt HQ HE").
Qed.
End report.

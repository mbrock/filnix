(** Error prints errno text before its newline and stderr flush. Both print
    calls use the normal NULL-stream wrapper and borrow the same stream.
    This proof requires a narrow mode at the second call, rather than
    assuming that the first formatter preserves the mode.

    The caller supplies separate text and newline format resources. Strerror,
    both formatters and the final flush still require explicit contracts.
    Failed print results and changes to errno remain permitted. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode FxprintfNormalCall VfxprintfNarrow ErrorNewline
  PrintfStateCode ErrorCode ErrorEntry ErrorText ErrorTextPrint ErrorTextTail.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section returning.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The next wrapper needs the actual returned mode to be narrow. This
    condition excludes positive modes without changing the text rule. *)
Definition error_text_newline_ready fb fl lb lbreg nb nreg sb sreg (R : iProp Σ) : iProp Σ :=
  ∃ md, ⌜md = 0 \/ md = 2 ^ 32 - 1⌝ ∗ single_ro ge sb sreg ∗
    error_newline_fields fb fl lb lbreg md nb nreg ∗ R.

(** A formatter can establish readiness by returning a narrow mode and
    the newline format resources. The exchange keeps the text format too;
    it neither borrows nor duplicates a stream lifetime. *)
Lemma error_text_to_newline fb fl lb lbreg tn tr nn nr sb sreg (R : iProp Σ) :
  error_text_done fb fl lb lbreg tn tr
    (fun _ md => ⌜md = 0 \/ md = 2 ^ 32 - 1⌝ ∗ single_ro ge sb sreg ∗
      live_capq DfracDiscarded (Ro nn) nr ∗ bytesq DfracDiscarded nn 0 [10;0] ∗ R)%I ⊢
  error_text_newline_ready fb fl lb lbreg nn nr sb sreg
    (live_capq DfracDiscarded (Ro tn) tr ∗ bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ R)%I.
Proof.
  iIntros "H". iDestruct "H" as (r md) "(Hfields & %Hmd & Hs & Hnf & Hnb & HR)".
  iDestruct "Hfields" as "(Hfl & Hlp & Hlk & Hmd & Htf & Htb)".
  iExists md. iSplit; [done |]. unfold error_newline_fields. iFrame.
Qed.

Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (tb : Z) (treg : region) (old : Z) (gb : Z) (greg : region)
  (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (md tn : Z) (tr : region)
  (nn : Z) (nr : region) (sb : Z) (sreg : region) (flushfn : func) (flushframe : frame)
  (P RT RN : iProp Σ) (QT SN : Z -> Z -> iProp Σ) (Q E : iProp Σ).
Let ready := error_text_newline_ready fb fl lb lbreg nn nr sb sreg RN.
Let text_ready := (single_ro ge sb sreg ∗ error_text_fields fb fl lb lbreg md tn tr ∗ RT)%I.
Let text_done := error_text_done fb fl lb lbreg tn tr QT.
Context (Hold : old = 0 \/ old = 1) (Hself : ow_self w0 = mkPtr tb (Obj tb))
  (Htb : 0 < tb) (Hta : tb mod 8 = 0) (Hte : tb + 796 <= r_end treg) (Htr : r_end treg <= 2 ^ 63)
  (Hcancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate))
  (Hg : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)))
  (Hgb : 0 < gb) (Hga : gb mod 8 = 0) (Hge : gb + 8 <= r_end greg) (Hgr : r_end greg <= 2 ^ 63)
  (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg) (Hfr : r_end freg <= 2 ^ 63)
  (Huser : Z.land fl 32768 = 0) (Htn : 0 <= tn < 2 ^ 64) (Hnn : 0 <= nn < 2 ^ 64)
  (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Htext : lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some (mkPtr tn (Ro tn)))
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some (mkPtr nn (Ro nn)))
  (Hfx : find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf))
  (Hvfx : find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf))
  (Hflush : find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn))
  (Hfframe : call_frame flushfn [WPtr (mkPtr fb (Obj fb))] = Some flushframe)
  (Htextformat : forall b p ap, vfxprintf_formatter fb freg fl lb lbreg (mkPtr tn (Ro tn)) ap 0 md DfracDiscarded tr
    (fun q => fx_va q [WPtr null;WPtr (mkPtr tn (Ro tn));WPtr p])
    (bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ RT)%I
    (fun r => bytesq DfracDiscarded tn 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ md', int_cell fb 192 md' ∗ QT r md')%I)
  (Hnewlineformat : forall md', md' = 0 \/ md' = 2 ^ 32 - 1 -> forall ap,
    vfxprintf_formatter fb freg fl lb lbreg (mkPtr nn (Ro nn)) ap 0 md' DfracDiscarded nr
      (fun q => fx_va q [WPtr null;WPtr (mkPtr nn (Ro nn))])
      (bytesq DfracDiscarded nn 0 [10;0] ∗ RN)%I
      (fun r => bytesq DfracDiscarded nn 0 [10;0] ∗ ∃ md'', int_cell fb 192 md'' ∗ SN r md'')%I)
  (Hflushcall : ⊢ live fb freg -∗ error_newline_done fb fl lb lbreg nn nr SN -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live fb freg ∗ Q }}).

(** Zero errno skips text printing. For nonzero errno, the separate
    readiness entailment must justify the next narrow call from what text
    actually returned. Both routes then reload stderr, flush and restore
    the saved cancellation flag. *)
Lemma wp_error_text_tail_normal e from errnum fmt ap mode cb countb countreg count strerrorfn Φ :
  error_inputs e 0 errnum fmt ap mode cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr countb (Obj countb)) ->
  0 < countb -> countb + 4 <= r_end countreg -> r_end countreg <= 2 ^ 63 ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ P -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer error_borrowed_text b p ∗ text_ready }})) ->
  ((if decide (errnum = 0) then P else text_done) ⊢ ready) ->
  live countb countreg -∗ int_cell countb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗ P -∗ E -∗
  (live countb countreg -∗ int_cell countb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch error_borrowed_text errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof.
  intros Hinputs Herr Hcount Hcb Hce Hcr Hstr Hstrcall Hready.
  iIntros "Hcl Hcount Ht Hflag Hbl Hsaved Hgl Hgp Hl HP HE HK".
  iApply (wp_error_text_tail_zero_loans Hreg Hext tb treg old gb greg (mkPtr fb (Obj fb)) (DfracOwn 1) freg
    (mkPtr nn (Ro nn)) glibc_fxprintf (fxprintf_normal_frame null (mkPtr nn (Ro nn)) []) flushfn flushframe
    ready (error_newline_done fb fl lb lbreg nn nr SN) Q text_ready E
    with "Hcl Hcount Ht Hflag Hbl Hsaved Hgl Hgp Hl HP HE HK"); try eassumption.
  { cbn. lia. }
  { apply fxprintf_normal_call_frame. }
  { iIntros "Hgl Hgp Hl Hready". iDestruct "Hready" as (md' Hnarrow) "HR".
    iApply (wp_error_newline Hreg Hext fb freg fl lb lbreg md' nn nr sb sreg gb greg RN SN
      with "Hgl Hgp Hl HR"); try assumption; try (rewrite Hself; cbn; lia).
    apply Hnewlineformat; done. }
  intros b p. exists (fxprintf_normal_frame null (mkPtr tn (Ro tn)) [WPtr p]).
  split; [apply fxprintf_normal_call_frame |]. iIntros "Hgl Hgp Hl Hb HT".
  iApply (wp_error_text_print Hreg Hext fb freg fl lb lbreg md tn tr sb sreg gb greg b p RT QT
    with "Hgl Hgp Hl Hb HT"); try assumption; try (rewrite Hself; cbn; lia).
  apply Htextformat.
Qed.
End returning.

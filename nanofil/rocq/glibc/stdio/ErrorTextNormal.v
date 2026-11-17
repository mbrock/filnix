(** Error counts each report and prints errno text when requested.
    Strerror supplies the text, and the normal printf wrapper prints it.
    This proof returns the borrowed stderr pointer and stream before error
    attempts its final newline.

    Zero skips both calls and leaves the supplied resources unchanged.
    Nonzero returns the scratch buffer, borrowed text and unlocked stream.
    The next newline must check the returned mode before using its narrow
    wrapper; this proof does not assume that printing preserved the mode. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode FxprintfNormalCall VfxprintfNarrow ErrorCode ErrorEntry ErrorText ErrorTextPrint.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section text.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (md nb : Z) (nreg : region)
  (sb : Z) (sreg : region) (gb : Z) (greg : region)
  (P R E : iProp Σ) (Q : Z -> Z -> iProp Σ).
Let loan := (live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗ live fb freg)%I.
Let ready := (single_ro ge sb sreg ∗ error_text_fields fb fl lb lbreg md nb nreg ∗ R)%I.
Let returned := error_text_done fb fl lb lbreg nb nreg Q.
Context (Hg : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)))
  (Hgb : 0 < gb) (Hga : gb mod 8 = 0) (Hge : gb + 8 <= r_end greg) (Hgr : r_end greg <= 2 ^ 63)
  (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg) (Hfr : r_end freg <= 2 ^ 63)
  (Huser : Z.land fl 32768 = 0) (Hnb : 0 <= nb < 2 ^ 64) (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64)
  (Htext : lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some (mkPtr nb (Ro nb)))
  (Hfx : find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf))
  (Hvfx : find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf))
  (Hformat : forall b p ap, vfxprintf_formatter fb freg fl lb lbreg (mkPtr nb (Ro nb)) ap 0 md DfracDiscarded nreg
    (fun q => fx_va q [WPtr null;WPtr (mkPtr nb (Ro nb));WPtr p])
    (bytesq DfracDiscarded nb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ R)%I
    (fun r => bytesq DfracDiscarded nb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ md', int_cell fb 192 md' ∗ Q r md')%I).

(** Strerror supplies either terminated buffer contents or a readable
    borrowed string. The original message cursor remains in the frame;
    the text wrapper makes a separate snapshot containing the text pointer. *)
Lemma wp_error_text_normal e from status errnum fmt ap mode cb countb countreg count strerrorfn Φ :
  error_inputs e status errnum fmt ap mode cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr countb (Obj countb)) ->
  0 < countb -> countb + 4 <= r_end countreg -> r_end countreg <= 2 ^ 63 ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ P -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer error_borrowed_text b p ∗ ready }})) ->
  live countb countreg -∗ int_cell countb 0 count -∗
  live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗ P -∗ E -∗
  (∀ e' predecessor, ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    live countb countreg -∗ int_cell countb 0 ((count + 1) mod 2 ^ 32) -∗
    error_text_scratch error_borrowed_text errnum -∗
    live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
    (if decide (errnum = 0) then P else returned) -∗ E -∗
    WP (ERun (mkFrame glibc_error_internal e' [] None
      (Enter (TAtom "iw_2.L92") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Hal Hend Hext Hfb Hformat Hfr Hfx Hg Hga Hgb Hge Hgr Hmd Hnb Hreg Hself Hselfr Htext Huser Hvfx sb sreg.
  intros Hinputs Herr Hcount Hcb Hce Hcr Hstr Hstrcall.
  iIntros "Hcl Hcount Hgl Hgp Hl HP HE HK".
  iApply (wp_error_text_loan e from status errnum fmt ap mode cb countb countreg count
    (mkPtr nb (Ro nb)) strerrorfn glibc_fxprintf error_borrowed_text loan P ready returned E
    with "Hcl Hcount [$Hgl $Hgp $Hl] HP HE [HK]"); try assumption.
  { intros b p. exists (fxprintf_normal_frame null (mkPtr nb (Ro nb)) [WPtr p]).
    split; [apply fxprintf_normal_call_frame |].
    iIntros "(Hgl & Hgp & Hl) Hb HR".
    iApply (wp_wand with "[Hgl Hgp Hl Hb HR]").
    { iApply (wp_error_text_print Hreg Hext fb freg fl lb lbreg md nb nreg sb sreg gb greg b p R Q
        with "Hgl Hgp Hl Hb HR"); try assumption; apply Hformat. }
    iIntros (v) "H". iDestruct "H" as (r ->) "(Hgl & Hgp & Hl & Hb & HQ)".
    iExists r. iFrame "Hb HQ". iSplit; [done |]. unfold loan. iFrame. }
  iIntros (e' predecessor Hinputs') "Hcl Hcount Hscratch (Hgl & Hgp & Hl) HQ HE".
  iApply ("HK" with "[%] Hcl Hcount Hscratch Hgl Hgp Hl HQ HE"); done.
Qed.
End text.

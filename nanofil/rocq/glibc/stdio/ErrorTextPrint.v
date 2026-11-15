(** Error prints errno text with the format ": %s" and a string returned
    by strerror. This proof follows the normal printf wrapper, borrowing
    stderr from the caller and returning it after printing.

    The text can occupy the scratch buffer or separate borrowed memory.
    The formatter receives the bytes and lifetime from that alternative,
    without requiring another copy of the buffer's lifetime. Its result
    may indicate failure, and its returned stream mode may have changed. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode FxprintfNormalCall FxprintfNormalNull VfxprintfNarrow ErrorText.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section text.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A borrowed string carries permission to read its bytes through the NUL.
    A pointer value or an address range alone cannot supply that permission. *)
Definition error_borrowed_text p : iProp Σ :=
  ∃ b reg chars, ⌜StringLogic.string_ok p b reg chars⌝ ∗
    live_capq DfracDiscarded (ptr_cap p) reg ∗
    bytesq DfracDiscarded b (ptr_addr p - b) (chars ++ [0]).

Definition error_text_fields fb fl lb lbreg md nb nreg : iProp Σ :=
  int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
  int_cell fb 192 md ∗ live_capq DfracDiscarded (Ro nb) nreg ∗
  bytesq DfracDiscarded nb 0 [58;32;37;115;0].

(** Printing returns the unlocked stream and its actual mode. A following
    newline can use the narrow wrapper only if that mode is still narrow. *)
Definition error_text_done fb fl lb lbreg nb nreg (Q : Z -> Z -> iProp Σ) : iProp Σ :=
  ∃ r md, error_text_fields fb fl lb lbreg md nb nreg ∗ Q r md.

Lemma wp_error_text_print (Hregistry : holds_os registry) (Hext : sys_external ge)
    fb freg fl lb lbreg md nb nreg sb sreg gb greg b p
    (R : iProp Σ) (Q : Z -> Z -> iProp Σ) :
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= nb < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  (forall ap, vfxprintf_formatter fb freg fl lb lbreg (mkPtr nb (Ro nb)) ap 0 md DfracDiscarded nreg
    (fun q => fx_va q [WPtr null;WPtr (mkPtr nb (Ro nb));WPtr p])
    (bytesq DfracDiscarded nb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ R)%I
    (fun r => bytesq DfracDiscarded nb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ md', int_cell fb 192 md' ∗ Q r md')%I) ->
  live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
  error_text_buffer error_borrowed_text b p -∗
  (single_ro ge sb sreg ∗ error_text_fields fb fl lb lbreg md nb nreg ∗ R) -∗
  WP (ERun (fxprintf_normal_frame null (mkPtr nb (Ro nb)) [WPtr p]) : gexpr)
    {{ v, ∃ k, ⌜v = Ret (WInt k)⌝ ∗ live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗
      live fb freg ∗ error_text_buffer error_borrowed_text b p ∗ error_text_done fb fl lb lbreg nb nreg Q }}.
Proof.
  intros Hg Hgb Hga Hge Hgr Hfb Hal Hend Hreg Huser Hnb Hmd Hself Hselfr Hfn Hformat.
  iIntros "Hgl Hgp Hl Hb (#Hs & (Hfl & Hlp & Hlk & Hmd & Hfmt & Htext) & HR)".
  iApply (wp_fxprintf_normal_null Hregistry Hext fb freg fl lb lbreg (mkPtr nb (Ro nb)) [WPtr p] md
    DfracDiscarded nreg sb sreg gb greg
    (bytesq DfracDiscarded nb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ R)%I emp
    (fun r => bytesq DfracDiscarded nb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ md', int_cell fb 192 md' ∗ Q r md')%I
    with "Hs Hgl Hgp Hl Hfl Hlp Hlk Hmd Hfmt [$Htext $Hb $HR] [] []"); try assumption; try reflexivity.
  { done. }
  iNext. iIntros (r) "Hgl Hgp Hl Hfl Hlp Hlk Hfmt _ (Htext & Hb & Hmode) _".
  iDestruct "Hmode" as (md') "[Hmd HQ]".
  iExists (r mod 2 ^ 32). iSplit; [done |]. iFrame "Hgl Hgp Hl Hb".
  iExists r, md'. unfold error_text_fields. iFrame "Hfl Hlp Hlk Hmd Hfmt Htext HQ".
Qed.
End text.

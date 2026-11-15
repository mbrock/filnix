(** Printing the final newline needs the same stderr pointer and stream
    that error will use for its subsequent flush. This rule lends them to
    the actual normal formatter and returns them together. The caller
    supplies the newline bytes and permission to read them; looking up
    a global address does not supply either resource. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode FxprintfNormalCall FxprintfNormalNull VfxprintfNarrow.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section newline.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

Definition error_newline_fields fb fl lb lbreg md nb nreg : iProp Σ :=
  int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
  int_cell fb 192 md ∗ live_capq DfracDiscarded (Ro nb) nreg ∗ bytesq DfracDiscarded nb 0 [10;0].

(** The stream may have a different mode after formatting. Keeping that
    actual mode allows the flush contract to state which modes it accepts. *)
Definition error_newline_done fb fl lb lbreg nb nreg (Q : Z -> Z -> iProp Σ) : iProp Σ :=
  ∃ r md, error_newline_fields fb fl lb lbreg md nb nreg ∗ Q r md.

Lemma wp_error_newline (Hregistry : holds_os registry) (Hext : sys_external ge)
    fb freg fl lb lbreg md nb nreg sb sreg gb greg
    (R : iProp Σ) (Q : Z -> Z -> iProp Σ) :
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= nb < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  (forall ap, vfxprintf_formatter fb freg fl lb lbreg (mkPtr nb (Ro nb)) ap 0 md DfracDiscarded nreg
    (fun p => fx_va p [WPtr null;WPtr (mkPtr nb (Ro nb))])
    (bytesq DfracDiscarded nb 0 [10;0] ∗ R)%I
    (fun r => bytesq DfracDiscarded nb 0 [10;0] ∗ ∃ md', int_cell fb 192 md' ∗ Q r md')%I) ->
  live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗
  live_capq (DfracOwn 1) (Obj fb) freg -∗
  (single_ro ge sb sreg ∗ error_newline_fields fb fl lb lbreg md nb nreg ∗ R) -∗
  WP (ERun (fxprintf_normal_frame null (mkPtr nb (Ro nb)) []) : gexpr)
    {{ v, ∃ k, ⌜v = Ret (WInt k)⌝ ∗ live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗
      live_capq (DfracOwn 1) (Obj fb) freg ∗ error_newline_done fb fl lb lbreg nb nreg Q }}.
Proof.
  intros Hg Hgb Hga Hge Hgr Hfb Hal Hend Hreg Huser Hnb Hmd Hself Hselfr Hfn Hformat.
  iIntros "Hgl Hgp Hl (#Hs & (Hfl & Hlp & Hlk & Hmd & Hfmt & Htext) & HR)".
  iApply (wp_fxprintf_normal_null Hregistry Hext fb freg fl lb lbreg (mkPtr nb (Ro nb)) [] md
    DfracDiscarded nreg sb sreg gb greg (bytesq DfracDiscarded nb 0 [10;0] ∗ R)%I emp
    (fun r => bytesq DfracDiscarded nb 0 [10;0] ∗ ∃ md', int_cell fb 192 md' ∗ Q r md')%I
    with "Hs Hgl Hgp Hl Hfl Hlp Hlk Hmd Hfmt [$Htext $HR] [] []"); try assumption; try reflexivity.
  { done. }
  iNext. iIntros (r) "Hgl Hgp Hl Hfl Hlp Hlk Hfmt _ (Htext & Hmode) _".
  iDestruct "Hmode" as (md') "[Hmd HQ]".
  iExists (r mod 2 ^ 32). iSplit; [done |]. iFrame "Hgl Hgp Hl".
  iExists r, md'. unfold error_newline_fields. iFrame "Hfl Hlp Hlk Hmd Hfmt Htext HQ".
Qed.
End newline.

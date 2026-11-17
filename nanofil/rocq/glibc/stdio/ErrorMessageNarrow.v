(** Error sends its original variadic cursor to the message formatter.
    This rule follows the actual narrow vfxprintf path through stream
    selection, lock acquisition, formatting and release. The formatter
    implementation remains an explicit contract.

    The caller supplies a full stream lifetime and readable format bytes.
    The original cursor returns unchanged; no wrapper snapshot replaces it.
    The initial mode must be zero or UINT_MAX, but formatting may change
    the mode and errno. Positive initial modes remain outside this rule. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces
  Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  ErrorCall ErrorFailure ErrorMessage FxprintfNormalCode VfxprintfSelect VfxprintfCall VfxprintfNarrow.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section message.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Error reads the stream mode only after a failure with errno ENOMEM.
    That path keeps permission to read the mode with the pending fields.
    The other paths keep it here; success also keeps errno here because
    error does not read it. Each path retains one permission per cell. *)
Definition error_message_spare fb eb ereg r en md : iProp Σ :=
  (if decide (2 ^ 31 <= r mod 2 ^ 32) then
    if decide (en = 12) then emp else int_cell fb 192 md
   else live eb ereg ∗ int_cell eb 0 en ∗ int_cell fb 192 md)%I.

(** The formatter receives the original error snapshot and format bytes.
    Its returned errno is independent of the saved error argument. The
    result determines which fields the existing error continuation borrows. *)
Lemma wp_error_message_narrow (Hregistry : holds_os registry) (Hext : sys_external ge)
    fb freg fl lb lbreg md fmt fmtb fmtreg dqf dqb chars ap flags status errnum ys
    sb sreg eb ereg (R E : iProp Σ) (Q : Z -> Z -> Z -> iProp Σ) :
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= ptr_addr fmt < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  StringLogic.string_ok fmt fmtb fmtreg chars -> error_errno_bounds eb ereg ->
  vfxprintf_formatter fb freg fl lb lbreg fmt ap flags md dqf fmtreg
    (fun p => error_va p (WInt status :: WInt errnum :: WPtr fmt :: ys))
    (bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ R)%I
    (fun r => bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
      ∃ en md', live eb ereg ∗ int_cell eb 0 en ∗ int_cell fb 192 md' ∗ Q r en md')%I ->
  live fb freg -∗ error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) -∗
  (single_ro ge sb sreg ∗ int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗
    lock_state lb lbreg 0 0 null ∗ int_cell fb 192 md ∗
    live_capq dqf (ptr_cap fmt) fmtreg ∗
    bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ R) -∗ E -∗
  WP (ERun (vfxprintf_frame (mkPtr fb (Obj fb)) fmt ap flags) : gexpr)
    {{ v, ∃ r en md', ⌜v = Ret (WInt (r mod 2 ^ 32))⌝ ∗ live fb freg ∗
      error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) ∗
      error_message_pending fb freg eb ereg r en md' ∗
      (int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
       live_capq dqf (ptr_cap fmt) fmtreg ∗ bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
       error_message_spare fb eb ereg r en md' ∗ Q r en md' ∗ E) }}.
Proof using Type.
  intros Hfb Hal Hend Hreg Huser Hfmt Hmd Hself Hselfr Hstring Herrno Hformat.
  iIntros "Hl HV (#Hs & Hfl & Hlp & Hlk & Hmd & Hfmt & Hbytes & HR) HE".
  iApply (wp_vfxprintf_explicit Hregistry Hext fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    (fun p => error_va p (WInt status :: WInt errnum :: WPtr fmt :: ys))
    (bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ R)%I E
    (fun r => bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
      ∃ en md', live eb ereg ∗ int_cell eb 0 en ∗ int_cell fb 192 md' ∗ Q r en md')%I
    with "Hs Hl Hfl Hlp Hlk Hmd Hfmt HV [$Hbytes $HR] HE []"); try assumption.
  iNext. iIntros (r) "Hl Hfl Hlp Hlk Hfmt HV (Hbytes & Hout) HE".
  iDestruct "Hout" as (en md') "(Hel & Hen & Hmd & HQ)".
  iExists r, en, md'. iSplit; [done |]. iFrame "Hl HV Hfl Hlp Hlk Hfmt Hbytes HQ HE".
  unfold error_message_pending, error_message_spare, error_mode_own.
  destruct (decide (2 ^ 31 <= r mod 2 ^ 32));
    destruct (decide (en = 12)); iFrame; try done.
  iSplit; [iPureIntro; exact Herrno |]. iPureIntro. lia.
Qed.
End message.

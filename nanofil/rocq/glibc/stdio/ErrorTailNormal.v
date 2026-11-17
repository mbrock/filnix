(** Error prints a newline and then flushes the same stderr stream.
    This proof connects those steps without making a second copy of the
    stream's ownership. The newline runs through the captured __fxprintf
    wrapper. Its formatter and the subsequent flush still need their own
    contracts, which may allow failure and changes to errno. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode FxprintfNormalCall VfxprintfNarrow ErrorNewline
  PrintfStateCode ErrorCode ErrorEntry ErrorTail.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section tail.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (tb : Z) (treg : region) (old : Z) (gb : Z) (greg : region)
  (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (md nb : Z) (nreg : region)
  (sb : Z) (sreg : region) (flushfn : func) (flushframe : frame)
  (R : iProp Σ) (S : Z -> Z -> iProp Σ) (Q E : iProp Σ).
Context (Hold : old = 0 \/ old = 1) (Hself : ow_self w0 = mkPtr tb (Obj tb))
  (Htb : 0 < tb) (Hta : tb mod 8 = 0) (Hte : tb + 796 <= r_end treg) (Htr : r_end treg <= 2 ^ 63)
  (Hcancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate))
  (Hg : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)))
  (Hgb : 0 < gb) (Hga : gb mod 8 = 0) (Hge : gb + 8 <= r_end greg) (Hgr : r_end greg <= 2 ^ 63)
  (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg) (Hfr : r_end freg <= 2 ^ 63)
  (Huser : Z.land fl 32768 = 0) (Hnb : 0 <= nb < 2 ^ 64) (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some (mkPtr nb (Ro nb)))
  (Hfx : find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf))
  (Hvfx : find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf))
  (Hflush : find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn))
  (Hfframe : call_frame flushfn [WPtr (mkPtr fb (Obj fb))] = Some flushframe)
  (Hformat : forall ap, vfxprintf_formatter fb freg fl lb lbreg (mkPtr nb (Ro nb)) ap 0 md DfracDiscarded nreg
    (fun p => fx_va p [WPtr null;WPtr (mkPtr nb (Ro nb))])
    (bytesq DfracDiscarded nb 0 [10;0] ∗ R)%I
    (fun r => bytesq DfracDiscarded nb 0 [10;0] ∗ ∃ md', int_cell fb 192 md' ∗ S r md')%I)
  (Hflushcall : ⊢ live_capq (DfracOwn 1) (Obj fb) freg -∗ error_newline_done fb fl lb lbreg nb nreg S -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq (DfracOwn 1) (Obj fb) freg ∗ Q }}).

(** The status-zero route restores the saved cancellation flag. Nonzero
    status still stops at the exact normal-exit call, with that flag saved
    and cancellation disabled. No exit behavior is inferred here. *)
Lemma wp_error_tail_normal e from status errnum fmt ap mode cb Φ :
  error_inputs e status errnum fmt ap mode cb -> 0 <= status < 2 ^ 32 ->
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live_capq (DfracOwn 1) (Obj fb) freg -∗
  (single_ro ge sb sreg ∗ error_newline_fields fb fl lb lbreg md nb nreg ∗ R) -∗ E -∗
  ((live tb treg -∗ int_cell tb 792 old -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live_capq (DfracOwn 1) (Obj fb) freg -∗ Q -∗ E -∗ Φ RetVoid) ∧
    (∀ e', ⌜status <> 0⌝ -∗ ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
      live tb treg -∗ int_cell tb 792 1 -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live_capq (DfracOwn 1) (Obj fb) freg -∗ Q -∗ E -∗
      WP (ERun (mkFrame glibc_error_internal e' [] None
        (Enter (TAtom "iw_2.L100") (Some (TAtom "iw_2.L92")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L92") (Some from))) : gexpr) {{ Φ }}.
Proof using Hal Hcancel Hend Hext Hfb Hfframe Hflush Hflushcall Hformat Hfr Hfx Hg Hga Hgb Hge Hgr Hmd Hnb Hnewline Hold Hreg Hself Hta Htb Hte Htr Huser Hvfx.
  intros Hinputs Hstatus. iIntros "Ht Hflag Hcl Hsaved Hgl Hgp Hl HR HE HK".
  iApply (wp_error_tail_loan Hreg Hext tb treg old gb greg (mkPtr fb (Obj fb)) (DfracOwn 1) freg
    (mkPtr nb (Ro nb)) glibc_fxprintf (fxprintf_normal_frame null (mkPtr nb (Ro nb)) []) flushfn flushframe
    (single_ro ge sb sreg ∗ error_newline_fields fb fl lb lbreg md nb nreg ∗ R)%I
    (error_newline_done fb fl lb lbreg nb nreg S) Q E
    with "Ht Hflag Hcl Hsaved Hgl Hgp Hl HR HE HK"); try assumption.
  { cbn. lia. }
  { apply fxprintf_normal_call_frame. }
  apply (wp_error_newline Hreg Hext fb freg fl lb lbreg md nb nreg sb sreg gb greg R S);
    try assumption; rewrite Hself; cbn; lia.
Qed.
End tail.

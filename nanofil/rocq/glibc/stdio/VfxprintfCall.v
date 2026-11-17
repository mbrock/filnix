(** The normal formatter accepts either stderr through a null argument or
    a nonnull stream directly. Only the null case needs the global stderr
    cell. Both rules retain the original format, cursor and mode flags,
    and return the formatter's result even when it indicates failure. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfNormalCode VfxprintfNarrow VfxprintfSelect Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section entry.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hregistry : holds_os registry) (Hext : sys_external ge).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (fmt ap : ptr) (flags md : Z)
  (dqf : dfrac) (fmtreg : region) (sb : Z) (sreg : region)
  (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> iProp Σ) (Φ : outcome -> iProp Σ).
Context (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg)
  (Hreg : r_end freg <= 2 ^ 63) (Huser : Z.land fl 32768 = 0)
  (Hfmtr : 0 <= ptr_addr fmt < 2 ^ 64) (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64)
  (Hcall : vfxprintf_formatter fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q).

Lemma wp_vfxprintf_null gb greg :
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  single_ro ge sb sreg -∗ live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗
  live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r, live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗
    live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
    lock_state lb lbreg 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (vfxprintf_frame null fmt ap flags) : gexpr) {{ Φ }}.
Proof using Hal Hcall Hend Hext Hfb Hfmtr Hmd Hreg Hregistry Hself Hselfr Huser.
  intros Hg Hgb Hga Hge Hgr. iIntros "#Hs Hgl Hgp Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iApply (wp_live_fit1 with "Hgl"). iIntros ([Hg0 Hg48]) "Hgl".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  unfold vfxprintf_frame. step. step. step. step. branch.
  step. step. check "Hgl". load "Hgl" "Hgp" "Hl". step.
  iApply (wp_vfxprintf_selected Hregistry Hext fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    V R (live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗ E)%I Q Φ
    with "Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR [$Hgl $Hgp $HE] [HK]"); try assumption; try lk_prove.
  { left. split; [reflexivity | lk_prove]. }
  iNext. iIntros (r) "Hl Hfl Hlp Hlk Hfmt HV HQ (Hgl & Hgp & HE)".
  iApply ("HK" with "Hgl Hgp Hl Hfl Hlp Hlk Hfmt HV HQ HE").
Qed.

(** The explicit-stream route needs no stderr lookup or cell ownership. *)
Lemma wp_vfxprintf_explicit :
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r, live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
    lock_state lb lbreg 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (vfxprintf_frame (mkPtr fb (Obj fb)) fmt ap flags) : gexpr) {{ Φ }}.
Proof using Hal Hcall Hend Hext Hfb Hfmtr Hmd Hreg Hregistry Hself Hselfr Huser.
  iIntros "#Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  unfold vfxprintf_frame. step. step. step. step. branch_as true.
  iApply (wp_vfxprintf_selected Hregistry Hext fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    V R E Q Φ with "Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK"); try assumption; try lk_prove.
  right. split; [reflexivity | lk_prove].
Qed.
End entry.

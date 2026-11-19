(** The normal formatter acquires a free stream lock directly in a
    single-threaded process. This rule follows the checked owner load and
    both stores before entering the narrow formatter. It excludes user
    locks, recursive ownership and contention rather than assuming that
    those paths succeed. *)
From Glibc Require Import Unit_stdioZ2dcommon_fxprintf_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsThread OsRegistry SysWrappers FileInv LibioLogic
  LibioCloseSteps VfxprintfNarrow Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section acquire.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hregistry : holds_os registry) (Hext : sys_external ge).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Lemma wp_vfxprintf_acquire e fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> Z -> region -> Z -> region -> iProp Σ) Φ :
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v13") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v4") e = Some (WPtr ap) ->
  lookup (TAtom "v6") e = Some (WInt flags) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= ptr_addr fmt < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  vfxprintf_formatter fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r fl' freg' lb' lbreg', ⌜Z.land fl' 32768 = 0 /\ fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ -∗
    live fb freg' -∗ int_cell fb 0 fl' -∗ pcell fb 136 (mkPtr lb' (Obj lb')) -∗
    lock_state lb' lbreg' 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r fl' freg' lb' lbreg' -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_fxprintf_os.fn___vfxprintf e [] None (Enter (TAtom "L24") (Some (TAtom "L10")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hpr Hchk Hz Hfmt Hap Hflags Hfb Hal Hend Hreg Huser Hfmtr Hmd Hself Hselfr Hcall.
  iIntros "#Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlk" as "(%Hk & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)".
  destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hl0 Hl48]) "Hbl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  step. iApply OsThread.wp_zthread_self_cookie;
    try (apply (reg_of registry Hregistry); reflexivity);
    try (apply (ext_fn ge Hext); cbn; tauto);
    try (apply (ext_data ge Hext); cbn; tauto); [exact Hself |]. iNext.
  step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_null "Hbl" "Hbo".
  step. step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0".
  load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo". step.
  iAssert (lock_state lb lbreg 1 0 (ow_self w0)) with "[Hbl Hb0 Hb4 Hbo]" as "Hlk".
  { iSplit; [iPureIntro; lia |]. iFrame "Hbl".
    iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"] |].
    iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"] |]. iExact "Hbo". }
  iApply (wp_vfxprintf_narrow _ (TAtom "L29") fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    V R E Q with "Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK"); try assumption; lk_prove.
Qed.
End acquire.

(** Error reporting flushes stdout with cancellation disabled. Fflush can
    still acquire the stream's free lock: it records the current thread as
    owner without reading the cancellation flag or cleanup chain. This rule
    covers a single-threaded process and requires a nonnull thread identifier. *)
From Glibc Require Import Unit_libio_iofflush_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsThread OsRegistry SysWrappers FileInv LibioLogic
  LibioCloseSteps Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section acquire.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Ltac self_side := first [apply (reg_of registry Hreg); reflexivity |
  apply (ext_fn ge Hext); cbn; tauto | apply (ext_data ge Hext); cbn; tauto].

(** A nonnull stream with locking enabled reaches L22 with this thread as
    owner and count zero. Null streams, user locks and contended locks are
    outside this rule, rather than being replaced by the free-lock route. *)
Lemma wp_fflush_acquire fr fb freg fl lb lbreg sb sreg Φ :
  call_frame Unit_libio_iofflush_os.fn___GI__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> ptr_addr (ow_self w0) <> 0 ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  (∀ e, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
          lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb)))⌝ -∗
    live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
    lock_state lb lbreg 1 0 (ow_self w0) -∗
    WP (ERun (mkFrame Unit_libio_iofflush_os.fn___GI__IO_fflush e [] None
      (Enter (TAtom "L22") (Some (TAtom "L32")))) : gexpr) {{ Φ }}) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hregion Huser Hsz.
  iIntros "#Hs Hl Hfl Hlp Hlk HK". cbn in Hfr. injection Hfr as <-.
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlk" as "(%Hk & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)".
  destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hl0 Hl48]) "Hbl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  iDestruct "Hfl" as "[%Hflr Hfl]".
  step. step. step. step. branch_as true.
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. iApply OsThread.wp_zthread_self_cookie; try self_side; [exact Hsz |]. iNext.
  step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl".
  load_null "Hbl" "Hbo". step. step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl".
  store_int "Hbl" "Hb0". load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo". step.
  iApply ("HK" with "[%] Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo]").
  - split; lk_prove.
  - iSplit; [done | iExact "Hfl"].
  - iSplit; [iPureIntro; lia |]. iFrame "Hbl".
    iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"] |].
    iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"] |]. iExact "Hbo".
Qed.
End acquire.

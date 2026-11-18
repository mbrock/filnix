(** Error messages go to stderr when the caller does not specify a stream.
    The function __vfxprintf loads that stream from the global pointer;
    an explicit stream bypasses the load. Both routes inspect the stream's
    flags before taking its lock. The proof requires an existing byte-oriented
    stream with a free lock in a single-threaded process. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfNormalCode VfxprintfNarrow VfxprintfAcquire Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Definition vfxprintf_frame fp fmt ap flags :=
  mkFrame glibc_vfxprintf (put (TAtom "v6") (WInt flags)
    (put (TAtom "v4") (WPtr ap) (put (TAtom "v2") (WPtr fmt) (put (TAtom "v0") (WPtr fp) []))))
    [] None (Enter (TAtom "start") None).
Lemma vfxprintf_call_frame fp fmt ap flags :
  call_frame glibc_vfxprintf [WPtr fp;WPtr fmt;WPtr ap;WInt flags] = Some (vfxprintf_frame fp fmt ap flags).
Proof. reflexivity. Qed.

Section select.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hregistry : holds_os registry) (Hext : sys_external ge).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (fmt ap : ptr) (flags md : Z)
  (dqf : dfrac) (fmtreg : region) (sb : Z) (sreg : region)
  (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> Z -> region -> Z -> region -> iProp Σ) (Φ : outcome -> iProp Σ).
Context (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg)
  (Hreg : r_end freg <= 2 ^ 63) (Huser : Z.land fl 32768 = 0)
  (Hfmtr : 0 <= ptr_addr fmt < 2 ^ 64) (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64)
  (Hcall : vfxprintf_formatter fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q).

(** The flags check before locking leads to taking the lock. *)
Lemma wp_vfxprintf_selected e from :
  (from = TAtom "L8" /\ lookup (TAtom "v16") e = Some (WPtr (mkPtr fb (Obj fb)))) \/
  (from = TAtom "start" /\ lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb)))) ->
  lookup (TAtom "v13") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v4") e = Some (WPtr ap) ->
  lookup (TAtom "v6") e = Some (WInt flags) ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r fl' freg' lb' lbreg', ⌜Z.land fl' 32768 = 0 /\ fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ -∗
    live fb freg' -∗ int_cell fb 0 fl' -∗ pcell fb 136 (mkPtr lb' (Obj lb')) -∗
    lock_state lb' lbreg' 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r fl' freg' lb' lbreg' -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_vfxprintf e [] None (Enter (TAtom "L10") (Some from))) : gexpr) {{ Φ }}.
Proof using Hal Hcall Hend Hext Hfb Hfmtr Hmd Hreg Hregistry Hself Hselfr Huser.
  intros Hselect Hz Hfmt Hap Hflags. iIntros "#Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iDestruct "Hfl" as "[%Hflr Hfl]".
  destruct Hselect as [[-> Hv] | [-> Hv]]; step; check "Hl"; load_s32 "Hl" "Hfl"; step; step; branch_as false;
    iApply (wp_vfxprintf_acquire Hregistry Hext _ fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
      V R E Q with "Hs Hl [Hfl] Hlp Hlk Hmd Hfmt HV HR HE HK");
    try assumption; try lk_prove; (iSplit; [done | iExact "Hfl"]).
Qed.

End select.

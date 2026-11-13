(** Printf's staged-byte overflow path either records failure or selects its
    next buffer and returns. A heap-backed stream supplies the storage needed
    for selection, even when overflow changes its write pointers.

    This composition follows both caller branches and restores the stream's
    exact cancellation flags and held lock count. The overflow call remains
    an explicit contract; this file does not prove a stream backend succeeds. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode PrintfBufferFileCode PrintfBufferOverflowCaller
  PrintfBufferOverflowHeapSwitch.
Import ListNotations.
Open Scope Z_scope.

(** The caller and selection share the stream's memory and OS interpretation. *)
Module PrintfBufferOverflowHeapCallerOn (R : Runtime) (LG0 : LogicSig R).
Module HC := PrintfBufferOverflowCallerOn R LG0.
Module HS := PrintfBufferOverflowHeapSwitchOn R LG0.
Import HS.HS HC.OC.CS HC.OC.CS.SW HC.OC.CS.SW.FI.ML HC.OC.CS.SW.FI.LG
  HC.OC.CS.SW.FI.L HC.OC.CS.SW.OW HC.OC.CS.SW.FI HC.OC.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance heap_caller_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (vb : Z) (self : ptr) (mode flags2 : Z) (held : option Z) (E : iProp Σ).
Context (Hoverflow : find_fn ge (TAtom "__GI___overflow") = Some (Defined glibc___overflow)).
Context (Hswitch : find_fn ge (TAtom "__printf_buffer_to_file_switch") =
  Some (Defined glibc___printf_buffer_to_file_switch)).
Context (Hcall : HC.OC.printf_overflow_call_spec w0 registry ge
  (fun fp => printf_heap_stream w0 vb self fp mode flags2 held) E).

(** EOF clears the printf mode without changing its three buffer pointers.
    Every other result runs the checked selection and returns its new pointers.
    Both continuations receive the same stream predicate and framed resources. *)
Lemma wp_printf_overflow_heap_caller e from bb breg fb ch bufmode oldbase oldptr oldend Φ :
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb < 2 ^ 64 -> 0 <= ch < 256 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗
  int_cell bb 32 bufmode -∗ printf_heap_stream w0 vb self (mkPtr fb (Obj fb)) mode flags2 held -∗ E -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  (live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗
    int_cell bb 32 0 -∗ printf_heap_stream w0 vb self (mkPtr fb (Obj fb)) mode flags2 held -∗ E -∗
    pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗ Φ RetVoid) -∗
  (∀ db k eo : Z,
    let start := if k <? eo then mkPtr (db + k) (Obj db) else mkPtr (bb + 48) (Obj bb) in
    let stop := if k <? eo then mkPtr (db + eo) (Obj db) else mkPtr (bb + 176) (Obj bb) in
    live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ bytes bb 48 [ch] -∗
    int_cell bb 32 bufmode -∗ printf_heap_stream w0 vb self (mkPtr fb (Obj fb)) mode flags2 held -∗ E -∗
    pcell bb 0 start -∗ pcell bb 8 start -∗ pcell bb 16 stop -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L74") from)) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hba Hbe Hbr Hfb Hfr Hch Hv0 Hchk.
  assert (Hframed : HC.OC.printf_overflow_call_spec w0 registry ge
    (fun fp => printf_heap_stream w0 vb self fp mode flags2 held)
    (E ∗ pcell bb 0 oldbase ∗ pcell bb 8 oldptr ∗ pcell bb 16 oldend)).
  { intros fr fp c Ψ Hc Hframe. iIntros "HF (HE & Hb & Hp & He) HK".
    iApply (Hcall fr fp c with "HF HE"); try assumption.
    iNext. iIntros (r Hr) "HF HE".
    iApply ("HK" $! r with "[%] HF [HE Hb Hp He]"); [done | iFrame]. }
  iIntros "Hb Hfp Hch Hm HF HE Hbase Hptr Hend Hfail Hselect".
  iApply (HC.wp_printf_overflow_caller w0 registry ge
    (fun fp => printf_heap_stream w0 vb self fp mode flags2 held)
    (E ∗ pcell bb 0 oldbase ∗ pcell bb 8 oldptr ∗ pcell bb 16 oldend) Hoverflow Hframed
    e from bb breg fb ch bufmode with "Hb Hfp Hch Hm HF [HE Hbase Hptr Hend] [Hfail] [Hselect]");
    try assumption; try lia.
  - iIntros "HF".
    iDestruct (printf_heap_stream_live with "HF") as (dq reg) "[Hl Hclose]".
    iExists reg, dq. iFrame.
  - iFrame.
  - iIntros "Hb Hfp Hch Hm HF (HE & Hbase & Hptr & Hend)".
    iApply ("Hfail" with "Hb Hfp Hch Hm HF HE Hbase Hptr Hend").
  - iIntros (e' Hv0') "Hb Hfp Hch Hm HF (HE & Hbase & Hptr & Hend)".
    iApply (HS.wp_printf_overflow_heap_switch w0 registry ge Hswitch
      e' (Some (TAtom "L74")) bb breg vb self (mkPtr fb (Obj fb)) mode flags2 held
      with "Hb Hfp HF Hbase Hptr Hend"); try assumption.
    iNext. iIntros (db k eo) "Hb Hfp HF Hbase Hptr Hend".
    iApply ("Hselect" $! db k eo with "Hb Hfp Hch Hm HF HE Hbase Hptr Hend").
Qed.

End rules.
End PrintfBufferOverflowHeapCallerOn.

(** After overflow returns, printf must choose where to store its next bytes.
    The stream's write pointers identify any remaining space in its heap buffer.
    Reading those pointers leaves the stream ready for later writes and preserves
    its cancellation flags and held lock count.

    The selection does not write to the stream or promise that overflow succeeds.
    It uses heap space when available and printf's staging array otherwise. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode PrintfBufferOverflowSwitch PrintfStreamHeap.
Import ListNotations.
Open Scope Z_scope.

(** The selection and heap predicate use the same memory and OS interpretation. *)
Module PrintfBufferOverflowHeapSwitchOn (R : Runtime) (LG0 : LogicSig R).
Module HS := PrintfStreamHeapOn R LG0.
Module OS := PrintfBufferOverflowSwitchOn R LG0.
Import HS HS.PS.PI HS.PS.PI.CS HS.PS.PI.CS.SW HS.PS.PI.CS.SW.FI.ML
  HS.PS.PI.CS.SW.FI.LG HS.PS.PI.CS.SW.FI.L HS.PS.PI.CS.SW.OW
  HS.PS.PI.CS.SW.FI HS.PS.PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance heap_switch_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hswitch : find_fn ge (TAtom "__printf_buffer_to_file_switch") =
  Some (Defined glibc___printf_buffer_to_file_switch)).

(** The checked switch borrows the stream's pointer cells and restores them.
    Its continuation receives the selected pointers and the original IO-ready
    stream, so later calls need not reconstruct readiness from bare ownership. *)
Lemma wp_printf_overflow_heap_switch e from bb breg vb self fp mode flags2 held
    oldbase oldptr oldend Φ :
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  live bb breg -∗ pcell bb 40 fp -∗ printf_heap_stream w0 vb self fp mode flags2 held -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  ▷ (∀ db k eo : Z,
    let start := if k <? eo then mkPtr (db + k) (Obj db) else mkPtr (bb + 48) (Obj bb) in
    let stop := if k <? eo then mkPtr (db + eo) (Obj db) else mkPtr (bb + 176) (Obj bb) in
    live bb breg -∗ pcell bb 40 fp -∗ printf_heap_stream w0 vb self fp mode flags2 held -∗
    pcell bb 0 start -∗ pcell bb 8 start -∗ pcell bb 16 stop -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L88") from)) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hba Hbe Hbr Hv0.
  iIntros "Hb Hfp HF Hbase Hptr Hend HK".
  iDestruct "HF" as "(%fb & %freg & %st & %db & %dreg & %sz & %k & %we & %xs & %fl & %tw & %off & %col & %Hp & Hf & Hst & Hrest)".
  pose proof Hp as (Hfp & Hfb & Hfa & Hfe & Hfr & _). subst fp.
  iDestruct "Hst" as "(%Hd & Hd & Hxs & Hfl & Htw & Hoff & H0 & H1 & H2 & H3 & Hwp & Hwe & H6 & H7)".
  pose proof Hd as (Hdb & Hde & Hdr & Hsz & Hk & Hlen & Hbytes & Hwc & Hwa).
  remember (ptr_addr we - db) as eo eqn:Heo.
  assert (Hwe : we = mkPtr (db + eo) (Obj db)).
  { destruct we as [a c]. cbn in *. subst c. f_equal; lia. }
  rewrite Hwe.
  iApply (OS.wp_printf_overflow_switch_owned w0 registry ge Hswitch e from bb breg fb freg
    db dreg k eo (DfracOwn 1%Qp) (DfracOwn 1%Qp)
    with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); try assumption; try (unfold file_size in *; lia).
  iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend".
  iApply ("HK" $! db k eo with "Hb Hfp [Hf Hd Hxs Hfl Htw Hoff H0 H1 H2 H3 Hwp Hwe H6 H7 Hrest] Hbase Hptr Hend").
  iExists fb, freg, st, db, dreg, sz, k, we, xs, fl, tw, off, col.
  iFrame "Hf Hrest". iSplit; [done|].
  rewrite /OB.ovf_state Hwe. iFrame. iPureIntro. rewrite -Hwe. exact Hd.
Qed.

End rules.
End PrintfBufferOverflowHeapSwitchOn.

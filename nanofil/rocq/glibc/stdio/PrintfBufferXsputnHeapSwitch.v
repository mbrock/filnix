(** After xsputn reports the requested count, printf chooses where to store
    its next bytes. Reading the heap stream's write pointers leaves the stream
    ready for later calls, with the same cancellation flags and lock count.

    This proof supplies the storage needed by the L40 selection. It does not
    prove the preceding stream call or assume that such a call accepts all bytes. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode PrintfBufferXsputnSwitch PrintfStreamHeap.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioOverflowBase LibioPutsInv OsWorld PrintfBufferXsputnSwitch PrintfStreamHeap SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Import PrintfStreamHeap LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (B : Z -> Z -> iProp Σ).
Local Instance heap_switch_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hswitch : find_fn ge (TAtom "__printf_buffer_to_file_switch") =
  Some (Defined glibc___printf_buffer_to_file_switch)).

(** Selection uses remaining heap space or falls back to printf's staging array.
    The continuation receives the selected pointers and the original stream,
    retaining its readiness for later writes without promising their success. *)
Lemma wp_printf_xsputn_heap_switch e from bb breg vb self fp mode flags2 held
    oldbase oldptr oldend Φ :
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  live bb breg -∗ pcell bb 40 fp -∗ printf_heap_stream_with B w0 vb self fp mode flags2 held -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  ▷ (∀ db k eo : Z,
    let start := if k <? eo then mkPtr (db + k) (Obj db) else mkPtr (bb + 48) (Obj bb) in
    let stop := if k <? eo then mkPtr (db + eo) (Obj db) else mkPtr (bb + 176) (Obj bb) in
    live bb breg -∗ pcell bb 40 fp -∗ printf_heap_stream_with B w0 vb self fp mode flags2 held -∗
    pcell bb 0 start -∗ pcell bb 8 start -∗ pcell bb 16 stop -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L40") from)) : sexpr) {{ Φ }}.
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
  iApply (PrintfBufferXsputnSwitch.wp_printf_xsputn_switch_owned w0 registry ge Hswitch e from bb breg fb freg
    db dreg k eo (DfracOwn 1%Qp) (DfracOwn 1%Qp)
    with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); try assumption; try (unfold file_size in *; lia).
  iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend".
  iApply ("HK" $! db k eo with "Hb Hfp [Hf Hd Hxs Hfl Htw Hoff H0 H1 H2 H3 Hwp Hwe H6 H7 Hrest] Hbase Hptr Hend").
  iExists fb, freg, st, db, dreg, sz, k, we, xs, fl, tw, off, col.
  iFrame "Hf Hrest". iSplit; [done|].
  rewrite /LibioOverflowBase.ovf_state Hwe. iFrame. iPureIntro. rewrite -Hwe. exact Hd.
Qed.

End rules.

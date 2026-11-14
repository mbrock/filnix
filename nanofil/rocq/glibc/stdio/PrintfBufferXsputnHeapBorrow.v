(** Printf reads FILE's jump-table field before calling xsputn.
    The heap stream owns that field and the permission to access FILE.
    This rule lends both and restores the entire stream when they return. *)
From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic PrintfBufferXsputnHeapSwitch.
From Glibc Require FileInv OsWorld PrintfStreamHeap.
From Glibc Require Import Fix.
Open Scope Z_scope.


Import PrintfStreamHeap FileInv FileInv.ML FileInv.LG FileInv.L OsWorld.

Section rules.
Context `{!gen_heapGS piece pval Σ}.
Context (B : Z -> Z -> iProp Σ).

(** The caller must return the same field and lifetime before invoking xsputn.
    Closing the borrow restores the exact mode, cancellation flags and lock count. *)
Lemma printf_heap_vtable_borrow w0 vb self mode flags2 held fb :
  printf_heap_stream_with B w0 vb self (mkPtr fb (Obj fb)) mode flags2 held -∗
  ∃ freg dqf, ⌜fb + 224 <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
    liveq dqf fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
    (liveq dqf fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
      printf_heap_stream_with B w0 vb self (mkPtr fb (Obj fb)) mode flags2 held).
Proof.
  iIntros "(%fb' & %freg & %st & %db & %dreg & %sz & %k & %we & %xs & %fl & %tw & %off & %col & %Hp & Hf & Hst & Hf2 & Hfd & Hcol & Hmd & Hvt & Htail)".
  pose proof Hp as (Hfp & Hfb & Hfa & Hfe & Hfr & _).
  injection Hfp as Heq. subst fb'.
  iExists freg, (DfracOwn 1%Qp). iSplit; [iPureIntro; unfold file_size in *; lia|].
  iFrame "Hf Hvt". iIntros "Hf Hvt".
  iExists fb, freg, st, db, dreg, sz, k, we, xs, fl, tw, off, col. iFrame "Hf Hst Hf2 Hfd Hcol Hmd Hvt Htail". done.
Qed.

End rules.

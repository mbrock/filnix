(** Glibc must find an idle allocator before puts can allocate stdout's
    buffer. This file constructs that starting state from fields checked
    against the linked memory, including the cache pointer and empty bins. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import HiAtexitBase HiAtexitAlloc HiAtexitSetb HiAtexitInitial.
Import ListNotations.
Open Scope Z_scope.
Import HLG HLG.L.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Owning a flattened image is owning each of its constituent images. *)
Lemma hi_pts_concat pss : pts (concat pss) ⊣⊢ [∗ list] ps ∈ pss, pts ps.
Proof. induction pss as [|ps pss IH]; cbn [concat]; rewrite ?pts_app ?IH; done. Qed.

(** Puts can use the allocator's initial fields directly. The proof
    supplies its allocation precondition without assuming extra storage. *)
Lemma hi_allocator_own : pts hi_allocator_ps ⊢
  hi_malloc_state (DfracOwn 1) 66464 66624 65680 hi_mp_reg hi_tc_reg hi_dummy_reg.
Proof.
  rewrite /hi_allocator_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hmp & Hmax & Htc & Htcp & Hdm & Hbins & _)".
  rewrite /hi_malloc_state /HAL.tcache_idle.
  iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iFrame "Hmp Hmax Htc Htcp Hdm".
  rewrite hi_pts_concat big_sepL_fmap /pcellq /null. done.
Qed.

End resources.

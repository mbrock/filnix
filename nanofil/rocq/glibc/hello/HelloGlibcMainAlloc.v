(** This file exposes glibc's idle allocator resources without exporting
    the allocator's proofs into every main-block substitution. The
    concrete predicate remains identical to AllocLogic.v's tcache_idle. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import AllocLogic.
Open Scope Z_scope.

(** The interface exposes the exact cells read by the allocation prelude. *)
Module Type HelloAllocSig (R : Runtime) (LG0 : LogicSig R).
Import LG0 LG0.L.
(** The allocator reads its size limit, dummy pointer and empty bins. *)
Definition tcache_idle `{!gen_heapGS piece pval Σ} (dq : dfrac)
    (mp_b tc_b dummy_b : Z) (mp_reg tc_reg dummy_reg : region) : iProp Σ :=
  ⌜0 <= mp_b /\ mp_b + 128 <= r_end mp_reg <= 2 ^ 64 /\ 0 <= tc_b /\ tc_b mod 8 = 0 /\
   tc_b + 8 <= r_end tc_reg <= 2 ^ 64 /\ 0 <= dummy_b /\ dummy_b mod 8 = 0 /\
   dummy_b + 664 <= r_end dummy_reg <= 2 ^ 64⌝ ∗
  liveq dq mp_b mp_reg ∗ icellq dq mp_b 120 1041 ∗
  liveq dq tc_b tc_reg ∗ pcellq dq tc_b 0 (mkPtr dummy_b (Ro dummy_b)) ∗
  liveq dq dummy_b dummy_reg ∗ [∗ list] i ∈ seqZ 0 64, pcellq dq dummy_b (152 + 8 * i) null.
End HelloAllocSig.

(** The existing allocator proof supplies the concrete resource definition. *)
Module HelloGlibcMainAllocOn (R : Runtime) (LG0 : LogicSig R) : HelloAllocSig R LG0.
(** The allocator implementation supplies its idle-state predicate. *)
Module A := AllocOn R LG0.
(** The allocator reads its size limit, dummy pointer and empty bins. *)
Definition tcache_idle := @A.tcache_idle.
End HelloGlibcMainAllocOn.

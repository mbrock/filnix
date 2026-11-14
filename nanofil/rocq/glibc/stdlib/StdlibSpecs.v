(** Allocation contracts describe the object returned to a caller and the
    memory that the caller lends. The world interpretation records which
    allocation and deallocation operations preserve the runtime's invariants. *)

From Glibc Require Import GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap ExternalCalls Runtime Logic MemLogic.
Import Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section contracts.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (wi : mem -> world -> gmap piece pval -> Prop).

(** The allocator returns a fresh, aligned object when allocation preserves the world. *)
Definition malloc2_spec : fspec Σ :=
  FSpec Z (fun n => [WInt n])
    (fun n => ⌜0 <= n < 2 ^ 64 /\
      forall m wd h base, fresh m (heap_req 16 n) base -> wi m wd h ->
        wi (allocated m (heap_req 16 n) base) wd (overwrite (obj_ps base (heap_req 16 n)) h)⌝)%I
    (fun n v => ∃ base,
      ⌜v = Ret (WPtr (mkPtr base (Obj base))) /\ 0 < base /\ base mod 16 = 0 /\
        base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ ∗ obj base (heap_req 16 n))%I.

End contracts.

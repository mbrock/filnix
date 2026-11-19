(** Proofs about a loaded image describe the pointers and objects that
    its callers can read. A pointer occupies address bytes and a capability
    slot. An object containing only bytes has an empty capability in each
    slot. These lists describe both layouts in the initial heap. *)

From Stdlib Require Import ZArith List.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Values Memory Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv.
Import ListNotations FileInv.ML FileInv.LG.
Open Scope Z_scope.

(** A pointer in memory is its capability slot and its address bytes. *)
Definition ptr_ps (b o : Z) (p : ptr) : list (piece * pval) :=
  (PAux b o, VAux (ptr_cap p)) :: cell b o (ptr_addr p).

(** This list holds one whole object. The object lies at the address
    and in the region that the pair q gives. It holds the bytes xs,
    and it holds no pointer. *)
Definition obj_ps (q : Z * region) (xs : list Z) : list (piece * pval) :=
  (PLive (fst q), VLive (snd q)) :: byte_ps (fst q) 0 xs ++ aux_ps (fst q) 0 (repeat CNone (length xs)).

Section ownership.
Context `{!gen_heapGS piece pval Σ}.

(** Owning the list of one object is owning its lifetime, its bytes
    and its empty pointer slots. *)
Lemma obj_ps_own q xs :
  pts (obj_ps q xs) ⊣⊢ live (fst q) (snd q) ∗ bytes (fst q) 0 xs ∗ auxes (fst q) 0 (repeat CNone (length xs)).
Proof using Type.
  change (obj_ps q xs) with
    ([(PLive (fst q), VLive (snd q))] ++ (byte_ps (fst q) 0 xs ++ aux_ps (fst q) 0 (repeat CNone (length xs))))%list.
  rewrite !pts_app. done.
Qed.

End ownership.

(** The parser reads a long-option table in 32-byte entries and stops at a
    null name. A caller shares each field and the bytes of each name. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List.
From Nanofil Require Import Values Memory Pieces Heap Logic.
From Glibc Require Import Fix OsMemLogic WordString LongOption.
Import Fix.LG0.
Open Scope Z_scope.

Section table.
Context `{!gen_heapGS piece pval Σ}.

(** The entry x lies at offset o of the table object tb. The caller
    shares its name pointer and name, the argument field, the flag
    pointer and the value. *)
Definition opt_entry (tb o : Z) (x : lopt) : iProp Σ :=
  pcellq DfracDiscarded tb o (lo_name x) ∗ word_string DfracDiscarded (lo_name x) (lo_str x) ∗
  int_cellq DfracDiscarded tb (o + 8) (lo_has x) ∗ pcellq DfracDiscarded tb (o + 16) (lo_flag x) ∗
  int_cellq DfracDiscarded tb (o + 24) (lo_val x).

(** The table at lo holds the entries os and then a null name. The
    table starts at an eight-byte boundary of the object tb, which may be
    read-only, and every entry and the null name lie inside that object
    below 2^48. *)
Definition opt_table (lo : ptr) (os : list lopt) : iProp Σ :=
  ∃ tb treg, ⌜(ptr_cap lo = Obj tb \/ ptr_cap lo = Ro tb) /\ 0 < tb /\ tb <= ptr_addr lo /\
     ptr_addr lo mod 8 = 0 /\ ptr_addr lo + 32 * Z.of_nat (List.length os) + 8 <= r_end treg /\
     r_end treg <= 2 ^ 48⌝ ∗
   liveq DfracDiscarded tb treg ∗
   ([∗ list] k ↦ x ∈ os, opt_entry tb (ptr_addr lo - tb + 32 * Z.of_nat k) x) ∗
   pcellq DfracDiscarded tb (ptr_addr lo - tb + 32 * Z.of_nat (List.length os)) null.

(** A shared table stays shared. *)
Global Instance opt_table_persistent lo os : Persistent (opt_table lo os).
Proof using Type. rewrite /opt_table /opt_entry /int_cellq /pcellq /liveq. apply _. Qed.

End table.

Section targets.
Context `{!gen_heapGS piece pval Σ}.

(** The caller owns the integer v at p. The four bytes at p lie inside
    the object of p's capability, at a four-byte boundary below 2^48,
    and the caller owns that object's whole lifetime, so it may store
    there. *)
Definition int_at (p : ptr) (v : Z) : iProp Σ :=
  ∃ tb treg, ⌜ptr_cap p = Obj tb /\ 0 < tb <= ptr_addr p /\ ptr_addr p mod 4 = 0 /\
     ptr_addr p + 4 <= r_end treg /\ r_end treg <= 2 ^ 48⌝ ∗
   live tb treg ∗ int_cell tb (ptr_addr p - tb) v.

(** The flag targets F are distinct integers that the caller owns. *)
Definition flags_own (F : list ptr) : iProp Σ := ⌜base.NoDup F⌝ ∗ [∗ list] f ∈ F, ∃ v, int_at f v.

(** The caller's longind pointer li is null or points at an integer that
    the caller owns. *)
Definition longind_own (li : ptr) : iProp Σ := ⌜li = null⌝ ∨ ∃ v, int_at li v.

End targets.

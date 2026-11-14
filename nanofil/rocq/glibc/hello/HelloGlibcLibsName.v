(** This file discharges the program-name call in Hello's library interface.
    The proof uses the closed glibc proof, which in turn proves the calls
    of memrchr and memcmp. Its sealed interface keeps those proofs out of
    later functor substitutions. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloName.
From Glibc Require Import OsWorld OsRegistry WordString HelloGlibcProgCells HelloGlibcProgName HelloGlibcMainNameSearch
  HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require HelloGlibcProgName OsWorld.
From Glibc Require Import Fix.
Open Scope Z_scope.

(** The interface exposes only the proved program-name triple. *)
Module Type HelloLibsNameSig (D : HelloDebtsT).
Import LG0 LG0.L D D.SW.FI.ML.
(** The call stores the suffix pointers selected from the argument string. *)
Parameter libs_name : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (w0 : os_world) (ge : genv) (o : hello_objs), hello_link ge o -> forall p s x y z,
  D.fn_triple w0 ge (TAtom "set_program_name") [WPtr p]
    (D.hello_ro ge o ∗ word_string DfracDiscarded p s ∗ D.ncells o x y z)
    (fun r => ⌜r = RetVoid⌝ ∗ D.ncells o (ptr_add p (Z.of_nat (name_idx s)))
       (ptr_add p (Z.of_nat (name_idx s))) (ptr_add p (Z.of_nat (short_idx s))))%I.
End HelloLibsNameSig.

(** The implementation instantiates the closed proof once. *)
Module HelloGlibcLibsNameOn (D : HelloDebtsT)
  : HelloLibsNameSig D.
(** The name proof supplies the control flow and cell stores. *)
Module PN := HelloGlibcProgName.
(** The sealed search proofs discharge basename and directory comparisons. *)
Module NS := HelloGlibcMainNameSearchOn.
Import LG0 LG0.L D D.SW.FI.ML.

Section libs.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs).
(** The OS interpretation survives collector safepoints. *)
Local Instance name_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The call runs with the concrete glibc OS registry. *)
Local Instance name_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** The call stores the suffix pointers selected from the argument string. *)
Lemma libs_name : hello_link ge o -> forall p s x y z,
  D.fn_triple w0 ge (TAtom "set_program_name") [WPtr p]
    (D.hello_ro ge o ∗ word_string DfracDiscarded p s ∗ D.ncells o x y z)
    (fun r => ⌜r = RetVoid⌝ ∗ D.ncells o (ptr_add p (Z.of_nat (name_idx s)))
       (ptr_add p (Z.of_nat (name_idx s))) (ptr_add p (Z.of_nat (short_idx s))))%I.
Proof.
  intros Hk p s x y z. exists set_program_name_fn. split; [exact (hk_name _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  assert (E : invocation set_program_name_fn [WPtr p] = fr)
    by (unfold invocation; rewrite Hfr; reflexivity). subst fr.
  iIntros "(Hro & Hs & Hn) HK".
  iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & _ & #Hlp & #Htp & _)".
  iApply (HelloGlibcProgName.set_program_name_glibc w0 glibc_os_registry ge
    (hk_strrchr _ _ Hk) (hk_gi_strlen _ _ Hk) (hk_memeq _ _ Hk) (hk_strncmp _ _ Hk)
    (ho_pb o) (ho_nb o) (ho_nsb o) (ho_preg o) (ho_nreg o) (ho_nsreg o) (ho_lp o) (ho_tp o)
    (hk_pb _ _ Hk) (hk_nb _ _ Hk) (hk_nsb _ _ Hk) (hk_lp _ _ Hk) (hk_tp _ _ Hk)
    (hk_pb_at _ _ Hk) (hk_nb_at _ _ Hk) (hk_nsb_at _ _ Hk)
    (NS.name_memrchr w0 glibc_os_registry ge (hk_memrchr _ _ Hk))
    (NS.name_memcmp w0 glibc_os_registry ge (hk_memcmp _ _ Hk))
    DfracDiscarded p s x y z with "Hs Hlp Htp Hn"); [left; reflexivity|].
  iNext. iIntros "_ Hn". iApply "HK". iSplit; [done|iExact "Hn"].
Qed.
End libs.
End HelloGlibcLibsNameOn.

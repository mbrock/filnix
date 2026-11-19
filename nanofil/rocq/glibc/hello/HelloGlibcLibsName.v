From Glibc Require Import GlibcProgram.
(** This file discharges the program-name call in Hello's library interface.
    The proof uses glibc's reverse search and byte comparison to find the
    part of the program name that Hello stores. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic StringLogic MemLogic.
From Glibc Require Import IRFrames HelloBodies.
From Glibc Require Import OsWorld OsRegistry WordString HelloGlibcProgCells HelloGlibcProgName MemrchrLogic MemcmpLogic
  HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require HelloGlibcProgName OsWorld.
From Glibc Require Import Fix.
Open Scope Z_scope.

Import LG0 LG0.L HelloGlibcDebts HelloGlibcDebts.SW.FI.ML.

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
  fn_triple w0 ge (TAtom "set_program_name") [WPtr p]
    (hello_ro ge o ∗ word_string DfracDiscarded p s ∗ ncells o x y z)
    (fun r => ⌜r = RetVoid⌝ ∗ ncells o (ptr_add p (Z.of_nat (name_idx s)))
       (ptr_add p (Z.of_nat (name_idx s))) (ptr_add p (Z.of_nat (short_idx s))))%I.
Proof using Type.
  intros Hk p s x y z. exists set_program_name_fn. split; [exact (hk_name _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  assert (E : invocation set_program_name_fn [WPtr p] = fr)
    by (unfold invocation; rewrite Hfr; reflexivity). subst fr.
  iIntros "(Hro & Hs & Hn) HK".
  iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & _ & #Hlp & #Htp & _)".
  iApply (HelloGlibcProgName.set_program_name_glibc (glibc_program := program_of w0 glibc_os_registry ge)
    (Hstrrchr := (hk_strrchr _ _ Hk)) (Hstrlen := (hk_gi_strlen _ _ Hk)) (Hmemeq := (hk_memeq _ _ Hk)) (Hstrncmp := (hk_strncmp _ _ Hk))
    (ho_pb o) (ho_nb o) (ho_nsb o) (ho_preg o) (ho_nreg o) (ho_nsreg o) (ho_lp o) (ho_tp o)
    (hk_pb _ _ Hk) (hk_nb _ _ Hk) (hk_nsb _ _ Hk) (hk_lp _ _ Hk) (hk_tp _ _ Hk)
    (hk_pb_at _ _ Hk) (hk_nb_at _ _ Hk) (hk_nsb_at _ _ Hk)
    (MemrchrLogic.glibc_memrchr_spec glibc_os_registry (os_wi w0) ge (hk_memrchr _ _ Hk))
    (MemcmpLogic.glibc_memcmp_small glibc_os_registry (os_wi w0) ge (hk_memcmp _ _ Hk))
    DfracDiscarded p s x y z with "Hs Hlp Htp Hn"); [left; reflexivity|].
  iNext. iIntros "_ Hn". iApply "HK". iSplit; [done|iExact "Hn"].
Qed.
End libs.

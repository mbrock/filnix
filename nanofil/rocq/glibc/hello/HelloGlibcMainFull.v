(** This file composes the proved blocks of GNU Hello's main function.
    The loop dispatches to version, help or operand processing; operand
    processing either exits or reaches the greeting. Every path uses the
    same concrete resources and the same remaining M4 and M6 debts. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry HelloGlibcDebts HelloGlibcLibsT
  HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop
  HelloGlibcMainVersion HelloGlibcMainHelpEnd HelloGlibcMainHelp HelloGlibcMainOperands
  HelloGlibcMainTail HelloGlibcMainGreet.
From Glibc Require HelloGlibcDebts HelloGlibcMainDispatch HelloGlibcMainGreet HelloGlibcMainHelp HelloGlibcMainLoop HelloGlibcMainOperands HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcMainVersion.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The greeting proof includes the preceding blocks through its dependencies. *)
(** The block proofs use the concrete debt record, not an abstract replacement. *)
(** The proof stages share the greeting's existing dependency chain. *)
Import HelloGlibcMainOperands HelloGlibcMainHelp HelloGlibcMainVersion HelloGlibcMainLoop HelloGlibcMainDispatch HelloGlibcMainStart.
Import LG0 LG0.L HelloGlibcDebts.
Section main.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (debt : HelloGlibcDebts.HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloGlibcDebts.HelloLibs w0 ge o (HelloGlibcDebts.hd_priv w0 ge o debt) X0 X) (Hy : hello_layout ge o).
(** The call runs with the concrete glibc OS registry. *)
Local Instance full_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** Every path is safe when its library calls and remaining debts hold. *)
Lemma main_full av ar p0 ps x y z a i Φ : 0 <= i <= Z.of_nat (length (p0 :: ps)) ->
  HelloGlibcDebts.hello_ro ge o -∗ ([∗ list] q ∈ p0 :: ps, HelloGlibcDebts.str_ro q) -∗ HelloGlibcDebts.argv_own av ar (p0 :: ps) -∗
  HelloGlibcDebts.ncells o x y z -∗ X0 -∗ HelloGlibcDebts.hello_stdio w0 ge o -∗ HelloGlibcDebts.hd_priv w0 ge o debt -∗ HelloGlibcDebts.getopt_cells o a i -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length (p0 :: ps))); WPtr (mkPtr av (Obj av))]) :
    language.expr (nanofil_lang glibc_os_registry ge)) {{ Φ }}.
Proof.
  intros Hi. iIntros "#Hro #Hps Hav Hnc HX0 Hio Hpv Hgo".
  iApply (main_start w0 ge o debt X0 X Lb Hy av ar p0 ps x y z with "Hro Hps Hav Hnc HX0 Hio Hpv").
  iNext. iIntros (e b4 b6 pn sn [Hvars [Hb4 Hb6]]) "Hav Hnc #Hpn #Hsn HX Hio Hpv Hgc Hb6".
  iApply (main_loop w0 ge o debt X Hy av ar b4 b6 pn sn with "Hro [] [Hav Hnc HX Hio Hpv Hgc Hb6 Hgo] []").
  - iPureIntro. split; [left; split; reflexivity|]. exact (conj Hvars (conj Hb4 (conj Hb6 Hi))).
  - iApply (loop_res_fold with "Hav Hps Hgo Hgc [] Hnc Hpn Hsn HX Hio Hpv Hb6").
    iApply (HelloGlibcMainSteps.lit_ro with "Hro"). cbn; tauto.
  - iSplit.
    + iApply (main_version w0 ge o debt X0 X Lb Hy with "Hro").
    + iSplit.
      * iApply (main_help w0 ge o debt X0 X Lb Hy with "Hro").
      * iApply (main_operands w0 ge o debt X0 X Lb Hy with "Hro").
        iApply (HelloGlibcMainGreet.main_join w0 ge o debt X0 X Lb Hy with "Hro").
Qed.
End main.

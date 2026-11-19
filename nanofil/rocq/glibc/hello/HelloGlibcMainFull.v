(** This file composes the proved blocks of GNU Hello's main function.
    The loop dispatches to version, help or operand processing; operand
    processing either exits or reaches the greeting. Every path passes
    the library's private state from one call to the next. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic StringLogic MemLogic.
From Glibc Require Import IRFrames HelloBodies.
From Glibc Require Import OsWorld OsRegistry HelloGlibcDebts
  HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop
  HelloGlibcMainVersion HelloGlibcMainHelp HelloGlibcMainOperands
  HelloGlibcMainGreet.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The greeting proof includes the preceding blocks through its dependencies. *)
(** The proof stages share the greeting's existing dependency chain. *)
Import HelloGlibcMainOperands HelloGlibcMainHelp HelloGlibcMainVersion HelloGlibcMainLoop HelloGlibcMainDispatch HelloGlibcMainStart.
Import LG0 LG0.L HelloGlibcDebts.
Section main.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (priv X0 X : iProp Σ)
  (Lb : HelloGlibcDebts.HelloLibs w0 ge o priv X0 X) (Hy : hello_layout ge o).
(** The call runs with the concrete glibc OS registry. *)
Local Instance full_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** Main hands the argument vector to the option parser and reads the
    options it returns. The caller supplies the parser's state at the
    index where parsing starts. *)
Lemma main_full_state av ar p0 ps x y z a i (S : list ptr -> Z -> iProp Σ) Φ :
  0 <= i <= Z.of_nat (length (p0 :: ps)) -> loop_getopt w0 ge o priv av ar S ->
  HelloGlibcDebts.hello_ro ge o -∗ ([∗ list] q ∈ p0 :: ps, HelloGlibcDebts.str_ro q) -∗ HelloGlibcDebts.argv_own av ar (p0 :: ps) -∗
  HelloGlibcDebts.ncells o x y z -∗ X0 -∗ HelloGlibcDebts.hello_stdio w0 ge o -∗ priv -∗ HelloGlibcDebts.getopt_cells o a i -∗
  S (p0 :: ps) i -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length (p0 :: ps))); WPtr (mkPtr av (Obj av))]) :
    language.expr (nanofil_lang glibc_os_registry ge)) {{ Φ }}.
Proof using Type*.
  intros Hi Hgr. iIntros "#Hro #Hps Hav Hnc HX0 Hio Hpv Hgo HS".
  iApply (main_start w0 ge o priv X0 X Lb Hy av ar p0 ps x y z with "Hro Hps Hav Hnc HX0 Hio Hpv").
  iNext. iIntros (e b4 b6 pn sn [Hvars [Hb4 Hb6]]) "Hav Hnc #Hpn #Hsn HX Hio Hpv Hgc Hb6".
  iApply (main_loop w0 ge o priv X Hy av ar b4 b6 pn sn S _ Hgr with "Hro [] [Hav Hnc HX Hio Hpv Hgc Hb6 Hgo HS] []").
  - iPureIntro. split; [left; split; reflexivity|]. exact (conj Hvars (conj Hb4 (conj Hb6 Hi))).
  - iApply (loop_res_fold with "Hav Hps Hgo Hgc [] Hnc Hpn Hsn HX Hio Hpv Hb6 HS").
    iApply (HelloGlibcMainSteps.lit_ro with "Hro"). cbn; tauto.
  - iSplit.
    + iApply (main_version w0 ge o priv X0 X Lb Hy with "Hro").
    + iSplit.
      * iApply (main_help w0 ge o priv X0 X Lb Hy with "Hro").
      * iApply (main_operands w0 ge o priv X0 X Lb Hy with "Hro").
        iApply (HelloGlibcMainGreet.main_join w0 ge o priv X0 X Lb Hy with "Hro").
Qed.
End main.

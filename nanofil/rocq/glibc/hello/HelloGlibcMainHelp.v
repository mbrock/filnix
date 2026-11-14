(** This file proves the `--help` exit of GNU Hello's `main`, linked
    with userland glibc: the block `iw_1.L39`.

    The help branch queries the message locale, prints the usage line
    and help text, and prints the bug-reporting address. Locale and
    output calls use the explicit remaining obligations. The final help
    proof supplies the continuation through the optional translation note
    and exit. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop
  HelloGlibcMainVersion HelloGlibcMainHelpEnd.
From Glibc Require HelloGlibcDebts HelloGlibcMainDispatch HelloGlibcMainHelpEnd HelloGlibcMainLoop HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcMainVersion.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The help-ending module supplies the final output and exit steps. *)
Import HelloGlibcMainHelpEnd HelloGlibcMainVersion HelloGlibcMainLoop HelloGlibcMainDispatch HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcDebts HelloGlibcDebts.FB HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.

Section help.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o (hd_priv w0 ge o D) X0 X) (Hy : hello_layout ge o)
  (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance help_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance help_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation combines the stream state and the callees' private state. *)
Local Notation io := (hello_stdio w0 ge o ∗ hd_priv w0 ge o D)%I.

(** The help branch prints the usage text before exiting. *)
Lemma main_help Φ :
  hello_ro ge o -∗ loop_exit w0 ge o D X av ar b4 b6 pn sn "iw_1.L39" "iw_1.L50" Φ.
Proof.
  iIntros "#Hro" (e ps a i g lose [Hf [Hpr Hlose]]) "Hr".
  iDestruct "Hr" as "(_ & _ & _ & _ & _ & Hnc & #Hpn & #Hsn & HX & Hio & Hpv & _)".
  iPoseProof "Hro" as "(_ & _ & #Hsol & #Hsoc & _)".
  iDestruct "Hio" as "(Hfo & Hfe & Hfi & Hls & Htc & Hen)".
  step. step_global (hy_so _ _ Hy).
  iApply (wp_std_stream with "Hsol Hsoc Hfo"); [lk_prove | exact (hy_so_at _ _ Hy) |]. iIntros "Hfo".
  iAssert (hello_stdio w0 ge o) with "[Hfo Hfe Hfi Hls Htc Hen]" as "Hio".
  { iSplitL "Hfo"; [iExact "Hfo"|]. iSplitL "Hfe"; [iExact "Hfe"|]. iSplitL "Hfi"; [iExact "Hfi"|].
    iSplitL "Hls"; [iExact "Hls"|]. iSplitL "Htc"; [iExact "Htc" | iExact "Hen"]. }
  (* setlocale (LC_MESSAGES, NULL). *)
  iApply (wp_call_ptr w0 ge _ _ _
            (fun q => hello_stdio w0 ge o ∗ hd_priv w0 ge o D ∗ (⌜ptr_addr q = 0⌝ ∨ str_ro q))%I with "[Hio Hpv]");
    [exact (hd_setlocale_query _ _ _ D) | reflexivity |
     iSplitR; [iExact "Hro" | iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]] |].
  iNext. iIntros (q) "(Hio & Hpv & Hq)".
  iAssert io with "[Hio Hpv]" as "Hio"; [iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]|].
  (* The usage line, with program_name. *)
  step_global (hy_lits _ _ Hy "hello#str.54" ltac:(cbn; tauto)).
  step_global (hy_pb _ _ Hy).
  iDestruct "Hnc" as "(Hpl & Hpc & Hncr)".
  iApply (wp_name_load with "Hpl Hpc Hpn"); [exact Hy | lk_prove |]. iIntros "Hpl Hpc".
  iApply (wp_print w0 ge o D with "Hro Hio [] [-]"); [right; left; split; [reflexivity | eexists; reflexivity] | vx | |].
  { iSplitL; [iApply (arg_out o)|]. iSplitL; [iApply str_ro_arg; iApply (lit_ro with "Hro"); cbn; tauto|].
    iSplitL; [iApply (str_ro_arg with "Hpn") | done]. }
  iNext. iIntros (n0) "Hio".
  iAssert (names o) with "[Hpl Hpc Hncr]" as "Hn".
  { iApply (names_intro o pn sn with "[Hpl Hpc Hncr] Hpn Hsn").
    iSplitL "Hpl"; [iExact "Hpl"|]. iSplitL "Hpc"; [iExact "Hpc" | iExact "Hncr"]. }
  (* The help text. *)
  step_global (hy_lits _ _ Hy "hello#str.55" ltac:(cbn; tauto)).
  iApply (wp_fputs w0 ge o D "hello#str.55" with "Hro Hio"); [cbn; tauto | lk_prove | lk_prove |]. iNext. iIntros (n1) "Hio".
  step_global (hy_lits _ _ Hy "hello#str.56" ltac:(cbn; tauto)).
  iApply (wp_fputs w0 ge o D "hello#str.56" with "Hro Hio"); [cbn; tauto | lk_prove | lk_prove |]. iNext. iIntros (n2) "Hio".
  step_global (hy_lits _ _ Hy "hello#str.57" ltac:(cbn; tauto)).
  iApply (wp_fputs w0 ge o D "hello#str.57" with "Hro Hio"); [cbn; tauto | lk_prove | lk_prove |]. iNext. iIntros (n3) "Hio".
  step_global (hy_lits _ _ Hy "hello#str.58" ltac:(cbn; tauto)).
  iApply (wp_fputs w0 ge o D "hello#str.58" with "Hro Hio"); [cbn; tauto | lk_prove | lk_prove |]. iNext. iIntros (n4) "Hio".
  step_global (hy_lits _ _ Hy "hello#str.56" ltac:(cbn; tauto)).
  iApply (wp_fputs w0 ge o D "hello#str.56" with "Hro Hio"); [cbn; tauto | lk_prove | lk_prove |]. iNext. iIntros (n5) "Hio".
  step_global (hy_lits _ _ Hy "hello#str.59" ltac:(cbn; tauto)).
  iApply (wp_fputs w0 ge o D "hello#str.59" with "Hro Hio"); [cbn; tauto | lk_prove | lk_prove |]. iNext. iIntros (n6) "Hio".
  step_global (hy_lits _ _ Hy "hello#str.60" ltac:(cbn; tauto)).
  iApply (wp_fputs w0 ge o D "hello#str.60" with "Hro Hio"); [cbn; tauto | lk_prove | lk_prove |]. iNext. iIntros (n7) "Hio".
  iApply (wp_call_void with "[Hio]");
    [exact (hd_emit_bug _ _ _ D) | reflexivity | iSplitR; [iExact "Hro" | iExact "Hio"] |].
  iNext. iIntros "Hio".
  (* The note on translations, when the message locale is not English. *)
  iApply (help_note w0 ge o D X0 X Lb Hy with "Hro Hio Hq Hn HX"); lk_prove.
Qed.

End help.

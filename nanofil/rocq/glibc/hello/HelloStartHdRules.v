(** GNU Hello's main calls getopt, and getopt warns about a bad option.
    The proof of main assumes that each warning can be printed and that
    it gives back what it borrowed. This module proves those facts for
    the objects that Hello's image holds. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv PrintfSpec GetoptDiag GetoptLongDiag DcgettextLocale
  StartCtypeInitSpec HelloGlibcDebts HelloImageModule HelloImageLoad HelloImageLayout HelloImageEarly
  HelloGetoptDiagImage HelloStartGetoptRules HelloStartHdGetopt.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)) (Hfr : frees_heap fr).

Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance hr_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation gl := (ct_gl hello_ct_objs).

(** The thread's locale pointer is a global of eight bytes that points at
    the global locale, whose category names start at offset 128. *)
Lemma hello_locale_cells :
  locale_cells (ct_lt hello_ct_objs) 0 (ct_ltreg hello_ct_objs) (mkPtr gl (Obj gl)) gl (ct_glreg hello_ct_objs).
Proof using Type. unfold locale_cells. cbn [ge_globals program_ge hr_program]. vm_compute. intuition congruence. Qed.

Context (Herr : ow_errno w = Some (mkPtr eb (Obj eb))).

(** Nobody has proved glibc's formatter yet, so its contract is a
    hypothesis. *)
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w) hge (TAtom "__vfprintf_internal") vfprintf_spec}.
Context (tb : Z).

(** After a report, T holds the same resources as G. *)
Definition hello_getopt_T : ptr -> ptr -> iProp Σ := fun mid q =>
  (∃ x : Z * Z * region, ⌜0 <= x.1.1 < 2 ^ 32⌝ ∗
    hello_dg_T w fr (ct_lt hello_ct_objs) 0 (ct_ltreg hello_ct_objs) (DfracOwn 1) (mkPtr gl (Obj gl)) gl
      (ct_glreg hello_ct_objs) (DfracOwn 1) DfracDiscarded DfracDiscarded x.2
      (mkPtr (img_a "_nl_C_name") (Ro (img_a "_nl_C_name"))) (DfracOwn (1/2)) (DfracOwn (1/2/2)) (DfracOwn (1/2/2))
      tb (DfracOwn 1) x.1.1 x.1.2 mid q)%I.

(** Getopt can warn about a short option or a long option. Between two
    warnings, main can lend out the thread's cleanup fields. These facts
    hold even when the warnings carry an extra part N. *)
Theorem hello_hd_rules (N : iProp Σ) :
  getopt_diag_rule w glibc_os_registry hge (N ∗ hello_getopt_E w fr tb)%I (fun mid q => N ∗ hello_getopt_T mid q)%I
    (ho_err ob) hello_dom /\
  getopt_ldiag_rule w glibc_os_registry hge (N ∗ hello_getopt_E w fr tb)%I (fun mid q => N ∗ hello_getopt_T mid q)%I
    (ho_err ob) hello_dom /\
  (N ∗ hello_getopt_E w fr tb ⊢ tcb_cleanup_inv (ow_self w) ∗ (tcb_cleanup_inv (ow_self w) -∗ N ∗ hello_getopt_E w fr tb)).
Proof using Hfr Herr Hvf.
  pose proof hello_locale_cells as Hloc.
  split; [apply getopt_diag_rule_sep_l|split; [apply getopt_ldiag_rule_sep_l|]].
  - apply (getopt_diag_rule_ex w glibc_os_registry hge (fun x : Z * Z * region => 0 <= x.1.1 < 2 ^ 32) _ _ _ _
      (0, 0, mkRegion 0 0 Heap Live)); [cbn; lia|].
    intros [[v tid] treg] Hv. exact (hello_dg_diag w fr Hfr Herr _ _ _ _ _ _ _ _ _ _ _ _ Hloc _ _ _ _ _ v tid Hv).
  - apply (getopt_ldiag_rule_ex w glibc_os_registry hge (fun x : Z * Z * region => 0 <= x.1.1 < 2 ^ 32) _ _ _ _
      (0, 0, mkRegion 0 0 Heap Live)); [cbn; lia|].
    intros [[v tid] treg] Hv. exact (hello_dg_ldiag w fr Hfr Herr _ _ _ _ _ _ _ _ _ _ _ _ Hloc _ _ _ _ _ v tid Hv).
  - iIntros "[HN (%x & %Hx & HG)]". iDestruct (hello_dg_lend with "HG") as "[Hc Hb]". iFrame "Hc".
    iIntros "Hc". iFrame "HN". iExists x. iSplit; [done | iApply ("Hb" with "Hc")].
Qed.

End rules.

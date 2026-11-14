(** This file proves the option loop of GNU Hello's `main`, linked
    with userland glibc: the block `iw_1.L8`, which calls
    `getopt_long`, entered from the start block or again from the
    dispatch on the option it returned.

    The parser contract preserves the streams and may permute the
    argument vector. A greeting option supplies a read-only string.
    The end-of-options result leaves the loop; every other result
    reaches the dispatch proof. Guarded induction justifies the back edges. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart
  HelloGlibcMainDispatch.
From Glibc Require HelloGlibcDebts HelloGlibcMainDispatch HelloGlibcMainStart HelloGlibcMainSteps.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** Dispatch supplies the option branches and their shared step rules. *)
Import HelloGlibcMainDispatch HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcDebts HelloGlibcDebts.FB HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.

Section loop.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X : iProp Σ)
  (Hy : hello_layout ge o) (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance loop_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance loop_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation selects the loop's owned resources. *)
Local Notation res := (loop_res w0 ge o D X av ar b4 b6 pn sn).
(** This notation selects the loop's exit continuations. *)
Local Notation exits := (loop_exits w0 ge o D X av ar b4 b6 pn sn).

(** This tactic reads the error flag preserved on a loop back edge. *)
Ltac phi_kept H := cbn -[put]; rewrite H; cbn -[put]; rewrite Z.mod_small; [reflexivity | lia].

(** This tactic computes call arguments after rewriting a bounded value. *)
Ltac vxa H := cbn -[put];
  repeat match goal with |- context [lookup ?k ?E] =>
    let L := fresh "Hlk" in assert (L : lookup k E = _) by lk_prove; rewrite L; clear L end;
  cbn -[put]; rewrite ?H; reflexivity.

(** The option loop reaches version, help or operand processing.
    A back edge preserves the invariant and may continue the loop. *)
Lemma main_loop Φ :
  hello_ro ge o -∗
  ∀ from e lose ps a i g,
  ⌜loop_entry from e lose /\ loop_facts e av b4 b6 ps i⌝ -∗ res ps a i g -∗ exits Φ -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom from)))) : gexpr) {{ Φ }}.
Proof.
  iIntros "#Hro". iLöb as "IH". iIntros (from e lose ps a i g [Hent Hf]) "Hr HK".
  iDestruct "Hr" as "(Hav & #Hps & Hgo & Hgc & #Hg & Hnc & #Hpn & #Hsn & HX & Hio & Hpv & Hb6)".
  pose proof Hf as ((H0 & H2 & H4 & H6 & Hc1) & Hb4 & Hb6 & Hi).
  assert (Hlose : lose = 0 \/ lose = 1).
  { destruct Hent as [[_ ->] | [[_ ->] | [_ [_ Hl]]]]; auto. }
  (* Enter iw_1.L8: pr.2 is lose. *)
  eapply step_wand; [eapply (wp_enter _ _ _ _ _ _ _ _ _ (put (TAtom "iw_1.pr.2") (WInt lose) e)); inst;
    [reflexivity | destruct Hent as [[-> ->] | [[-> ->] | [[-> | ->] [Hpr _]]]];
     [vx | vx | phi_kept Hpr | phi_kept Hpr]] |].
  cbn [b_insts b_jump].
  (* getopt_long (argc, argv, "g:t", longopts, NULL). *)
  step_global (hy_lits _ _ Hy "hello#str.69" ltac:(cbn; tauto)).
  step_global (hy_lits _ _ Hy "hello#parse_options.longopts.64" ltac:(cbn; tauto)).
  iDestruct "Hav" as "(%Havp & Havl & Havs)".
  assert (Hargc : Z.of_nat (length ps) mod 2 ^ 32 = Z.of_nat (length ps)).
  { apply Z.mod_small. destruct Havp as (_ & _ & H31 & _). split; [lia|].
    change (2 ^ 31) with 2147483648 in H31. change (2 ^ 32) with 4294967296. lia. }
  iAssert (argv_own av ar ps) with "[Havl Havs]" as "Hav"; [iFrame; iPureIntro; exact Havp|].
  iApply (wp_call_intn _ _ _ _ _
            (fun code => ∃ ps' a' i', ⌜Permutation ps ps' /\ 0 <= i' <= Z.of_nat (length ps)⌝ ∗
               hello_stdio w0 ge o ∗ hd_priv w0 ge o D ∗ argv_own av ar ps' ∗ getopt_cells o a' i' ∗
               (if code =? 103 then str_ro a' else True))%I with "[Hav Hgo Hio Hpv]");
    [eapply fn_triple_mono; [exact (hd_getopt _ _ _ D av ar ps a i)|];
     iIntros (r) "(%code & %ps' & %a' & %i' & %Hp & Hio & Hpv & Hav & Hgo & Hga)";
     destruct Hp as (-> & Hc & Hp & Hi'); iExists code; iSplit; [iPureIntro; split; [reflexivity | exact Hc]|];
     iExists ps', a', i'; iSplit; [iPureIntro; split; assumption|];
     iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv"|]; iSplitL "Hav"; [iExact "Hav"|];
     iSplitL "Hgo"; [iExact "Hgo" | iExact "Hga"] | vxa Hargc |
     iSplitR; [iExact "Hro"|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv"|];
     iSplitL "Hav"; [iExact "Hav"|]; iSplitR; [iExact "Hps" | iExact "Hgo"] |].
  iNext. iIntros (code Hcode) "(%ps' & %a' & %i' & %Hpost & Hio & Hpv & Hav & Hgo & Hga)".
  destruct Hpost as (Hperm & Hi').
  iAssert ([∗ list] q ∈ ps', str_ro q)%I as "#Hps'".
  { rewrite -(big_opL_permutation (fun q => str_ro q) ps ps' Hperm). iExact "Hps". }
  pose proof (Permutation_length Hperm) as Hlen.
  (* Whether getopt_long returned -1. *)
  step.
  destruct (Z.eq_dec code 4294967295) as [-> | Hn1].
  { (* The end of the options. *)
    (branch_symbolic; LeavesLogic.decide_branch). iDestruct "HK" as "[_ [_ HK]]".
    iPoseProof (loop_res_fold with "Hav Hps' Hgo Hgc Hg Hnc Hpn Hsn HX Hio Hpv Hb6") as "Hr".
    iApply ("HK" $! _ ps' a' i' g lose with "[%] Hr").
    split; [|split; [lk_prove | exact Hlose]].
    split; [rewrite -Hlen; unfold start_vars; repeat split; lk_prove | split; [exact Hb4 | split; [exact Hb6 | lia]]]. }
  (* Any other code: the dispatch, with the loop as its way back. *)
  (branch_symbolic; LeavesLogic.decide_branch). iPoseProof (loop_res_fold with "Hav Hps' Hgo Hgc Hg Hnc Hpn Hsn HX Hio Hpv Hb6") as "Hr".
  iApply (loop_dispatch w0 ge o D X Hy av ar b4 b6 pn sn Φ _ lose ps' a' i' g code with "Hro Hr Hga IH HK");
    [| lk_prove | exact Hlose | lk_prove | exact Hcode | exact Hn1].
  split; [rewrite -Hlen; unfold start_vars; repeat split; lk_prove | split; [exact Hb4 | split; [exact Hb6 | lia]]].
Qed.

End loop.

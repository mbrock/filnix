(** This file proves the greeting of GNU Hello's `main`, linked with
    userland glibc, from the block `iw_1.join` to `exit` or `error`.

    Hello loads the selected greeting, measures it and allocates enough
    space for its wide-character form. Conversion failure reaches the
    error-reporting branch; success reaches the printing branch.
    The tail proof supplies both continuations. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsBlocks OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop
  HelloGlibcMainVersion HelloGlibcMainHelpEnd HelloGlibcMainHelp HelloGlibcMainOperands
  HelloGlibcMainTail.
Import ListNotations.
Open Scope Z_scope.

(** The greeting proof shares one [[runtime]] and logic instance. *)
Module HelloGlibcMainGreetOn (R : Runtime) (LG0 : LogicSig R).
(** The tail module supplies the success and conversion-failure exits. *)
Module Tl := HelloGlibcMainTailOn R LG0.
Import Tl Tl.Op Tl.Op.Hp Tl.Op.Hp.He Tl.Op.Hp.He.Vn Tl.Op.Hp.He.Vn.Lp Tl.Op.Hp.He.Vn.Lp.Dp Tl.Op.Hp.He.Vn.Lp.Dp.St
  Tl.Op.Hp.He.Vn.Lp.Dp.St.S Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D.FB
  Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D.SW Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.ML
  Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.LG Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.L
  Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D.SW.OW Tl.Op.Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.

(** This tactic computes call arguments whose values fit their integer bounds. *)
Ltac vxm := cbn -[put];
  repeat match goal with |- context [lookup ?k ?E] =>
    let L := fresh "Hlk" in assert (L : lookup k E = _) by lk_prove; rewrite L; clear L end;
  cbn -[put]; unwrap; reflexivity.

Section greet.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o (hd_priv w0 ge o D) X0 X) (Hy : hello_layout ge o)
  (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance greet_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance greet_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation combines the stream state and the callees' private state. *)
Local Notation io := (hello_stdio w0 ge o ∗ hd_priv w0 ge o D)%I.

(** The terminator and four-byte scaling fit when the greeting length is below 2^48. *)
Lemma greet_len x : 0 <= x < 2 ^ 48 ->
  (x mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = x + 1 /\
  ((x + 1) mod 2 ^ 64 * 2 ^ ((2 mod 2 ^ 32) mod 64)) mod 2 ^ 64 = 4 * (x + 1).
Proof.
  intros Hx. change (2 ^ ((2 mod 2 ^ 32) mod 64)) with 4.
  change (2 ^ 48) with 281474976710656 in Hx. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small x); [|lia]. rewrite (Z.mod_small 1); [|lia]. rewrite (Z.mod_small (x + 1)); [|lia].
  rewrite Z.mod_small; [|lia]. split; [reflexivity | lia].
Qed.

(** The greeting branch converts the selected text and prints it or reports an error. *)
Lemma main_join Φ : hello_ro ge o -∗ join_cont w0 ge o D X b4 b6 Φ.
Proof.
  iIntros "#Hro" (e g [(H4 & Hc1 & H6) [Hb4 Hb6]]) "Hgc #Hg Hb6 Hio Hn HX".
  pose proof Hb4 as (Hb40 & Hb416 & Hb448).
  iDestruct "Hgc" as "(Hl4 & Hp4 & Hy4 & Hc4)".
  st.
  rule1 "Hl4" ltac:(eapply wp_renew; ins;
    [reflexivity | vx | reflexivity | reflexivity | arith | cbn [r_end]; arith | arith]).
  iApply (wp_load_str w0 ge _ _ _ _ _ _ _ _ _ _ _ (DfracOwn 1) (DfracOwn 1) with "Hl4 Hp4 Hg");
    [lk_prove | arith | apply mod16_mod8; exact Hb416 |].
  iNext. iIntros "Hl4 Hp4".
  iDestruct "Hg" as (s) "#Hs". iDestruct (str_len_bound with "Hs") as %Hsl.
  iApply (wp_call_long w0 ge _ _ _ (fun n => ⌜n = Z.of_nat (length s)⌝)%I with "Hs");
    [eapply fn_triple_mono; [exact (hl_strlen _ _ _ _ _ _ Lb DfracDiscarded g s)|];
     iIntros (r) "[-> _]"; iExists _; iSplit; [iPureIntro; split; [reflexivity | lia] | done] | vx |].
  iNext. iIntros (n Hn ->).
  destruct (greet_len (Z.of_nat (length s))) as (E1 & E2); [lia|].
  eapply step_wand; [eapply (wp_let_as w0 ge (WInt (Z.of_nat (length s) + 1))); ins;
    [reflexivity | reflexivity | vx | intros ?; reflexivity | f_equal; exact E1] |].
  eapply step_wand; [eapply (wp_let_as w0 ge (WInt (4 * (Z.of_nat (length s) + 1)))); ins;
    [reflexivity | reflexivity | vx | intros ?; reflexivity | f_equal; exact E2] |].
  set (N := 4 * (Z.of_nat (length s) + 1)).
  assert (HN : 0 <= N < 2 ^ 64) by (unfold N; change (2 ^ 48) with 281474976710656 in Hsl;
                                    change (2 ^ 64) with 18446744073709551616; lia).
  iApply (wp_call_ptr w0 ge _ _ _ (fun q => ∃ bd, ⌜q = mkPtr bd (Obj bd) /\ 0 < bd /\ bd mod 16 = 0 /\
                                         bd + req_extent (wreq N) <= 2 ^ 48⌝ ∗ obj bd (wreq N))%I with "Hro");
    [eapply fn_triple_mono; [exact (hl_xmalloc _ _ _ _ _ _ Lb N HN)|];
     iIntros (r) "(%bd & %Hr & Hobj)"; destruct Hr as (-> & Hr); iExists _; iSplit; [done|];
     iExists bd; iSplit; [iPureIntro; split; [reflexivity | exact Hr] | iExact "Hobj"] | vxm |].
  iNext. iIntros (q) "(%bd & %Hbd & Hobj)". destruct Hbd as (-> & Hbd0 & Hbd16 & Hbde).
  iPoseProof (obj_wbuf with "Hobj") as "Hwb"; [unfold N; lia|].
  iAssert (gcell b4 g) with "[Hl4 Hp4 Hy4 Hc4]" as "Hgc".
  { iSplitL "Hl4"; [iExact "Hl4"|]. iSplitL "Hp4"; [iExact "Hp4"|]. iSplitL "Hy4"; [iExact "Hy4" | iExact "Hc4"]. }
  iDestruct "Hio" as "[Hio Hpv]".
  iApply (wp_call_long w0 ge _ _ _
            (fun k => ∃ ws, ⌜k <> 2 ^ 64 - 1 -> wide_terminated ws⌝ ∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o D ∗
                        wbuf bd N ws)%I with "[Hio Hpv Hwb Hgc Hb6]");
    [eapply fn_triple_mono; [exact (hd_mbsrtowcs _ _ _ D bd b4 b6 g s)|];
     iIntros (r) "(%k & %ws & %Hk & Hio & Hpv & Hwb)"; destruct Hk as (-> & Hk & Hw);
     iExists k; iSplit; [iPureIntro; split; [reflexivity | exact Hk]|];
     iExists ws; iSplit; [iPureIntro; exact Hw|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv" | iExact "Hwb"] |
     vxm |
     iSplitR; [iExact "Hro"|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv"|];
     iSplitL "Hwb"; [iExact "Hwb"|]; iSplitL "Hgc"; [iExact "Hgc"|]; iSplitR; [iExact "Hs" | iExact "Hb6"] |].
  iNext. iIntros (k Hk) "(%ws & %Hw & Hio & Hpv & Hwb)".
  st.
  destruct (Z.eq_dec k (2 ^ 64 - 1)) as [-> | Hk1].
  - br. iApply (join_fail w0 ge o D X0 X Lb Hy with "Hro [Hio Hpv] Hn HX"). iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"].
  - br. iApply (join_print w0 ge o D X0 X Lb Hy with "Hro [Hio Hpv] Hn HX Hwb"); [lk_prove | exact Hbd0 | exact (Hw Hk1) |].
    iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"].
Qed.

End greet.
End HelloGlibcMainGreetOn.

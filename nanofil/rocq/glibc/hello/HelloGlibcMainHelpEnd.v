(** This file proves the end of the `--help` exit of GNU Hello's
    `main`, linked with userland glibc, and the printing calls the
    exits share.

    After printing the bug address, Hello prints a translation note
    when the message locale is present and does not start with "en_".
    It then compares the standard output and error streams to choose
    its exit status. Comparison and exit use concrete library proofs;
    printing remains an explicit obligation. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop
  HelloGlibcMainVersion.
Import ListNotations.
Open Scope Z_scope.

(** The help-ending proof shares one [[runtime]] and logic instance. *)
Module HelloGlibcMainHelpEndOn (R : Runtime) (LG0 : LogicSig R).
(** The version module supplies the common output and exit rules. *)
Module Vn := HelloGlibcMainVersionOn R LG0.
Import Vn Vn.Lp Vn.Lp.Dp Vn.Lp.Dp.St Vn.Lp.Dp.St.S Vn.Lp.Dp.St.S.D Vn.Lp.Dp.St.S.D.FB
  Vn.Lp.Dp.St.S.D.SW Vn.Lp.Dp.St.S.D.SW.FI.ML Vn.Lp.Dp.St.S.D.SW.FI.LG
  Vn.Lp.Dp.St.S.D.SW.FI.L Vn.Lp.Dp.St.S.D.SW.OW Vn.Lp.Dp.St.S.D.SW.FI.

Section help_end.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o (hd_priv w0 ge o D) X0 X) (Hy : hello_layout ge o)
  (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance help_end_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance help_end_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation combines the stream state and the callees' private state. *)
Local Notation io := (hello_stdio w0 ge o ∗ hd_priv w0 ge o D)%I.

(** `stdout` is an argument a printing debt may be handed. *)
Lemma arg_out : ⊢ arg_ro o (WPtr (ho_out o)).
Proof. iLeft. iPureIntro. right. left. reflexivity. Qed.

(** A call of `fprintf` or `fputs` at one of `main`'s sites: it returns
    an int and keeps the stdio state. *)
Lemma wp_print g xs f e ls lab d args rest j Ψ :
  print_site ge o g xs -> map_option (arg_x ge e) args = Some xs ->
  hello_ro ge o -∗ io -∗ ([∗ list] x ∈ xs, arg_ro o x) -∗
  ▷ (∀ n, io -∗ WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hs Hx. iIntros "#Hro [Hio Hpv] Hxs HK".
  iApply (wp_call_int with "[Hio Hpv Hxs]"); [exact (hd_print _ _ _ D g xs Hs) | exact Hx |
    iSplitR; [iExact "Hro"|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv" | iExact "Hxs"] |].
  iNext. iIntros (n _) "HQ". iApply ("HK" with "HQ").
Qed.

(** The help branch prints the selected literal to stdout. *)
Lemma wp_fputs s f e ls lab d vs vo rest j Ψ :
  In s fputs_lits -> lookup vs e = Some (WPtr (sym_ptr ge s)) -> lookup vo e = Some (WPtr (ho_out o)) ->
  hello_ro ge o -∗ io -∗
  ▷ (∀ n, io -∗ WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global (TAtom "fputs"))
                                             [Arg P (Tmp vs); Arg P (Tmp vo)] :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hs Hvs Hvo. iIntros "#Hro Hio HK".
  iApply (wp_print with "Hro Hio [] HK"); [left; split; [reflexivity | exists s; split; [exact Hs | reflexivity]] |
    cbn; rewrite Hvs Hvo; reflexivity |].
  iSplitL; [|iSplitL; [iApply arg_out | done]]. iApply str_ro_arg. iApply (lit_ro with "Hro").
  unfold fputs_lits in Hs. cbn. cbn in Hs. tauto.
Qed.

(** Help compares stdout with stderr and exits with the resulting status. *)
Lemma help_L32 e from Ψ :
  lookup (TAtom "iw_1.v41") e = Some (WPtr (ho_out o)) ->
  hello_ro ge o -∗ io -∗ names o -∗ X -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.iw_1.L32") (Some (TAtom from)))) : gexpr) {{ Ψ }}.
Proof.
  intros Hv41. iIntros "#Hro [Hio Hpv] Hn HX".
  iPoseProof "Hro" as "(_ & _ & _ & _ & #Hsel & #Hsec & _)".
  iDestruct "Hio" as "(Hfo & Hfe & Hfi & Hls & Htc & Hen)".
  st. st_global (hy_se _ _ Hy).
  iApply (wp_std_stream with "Hsel Hsec Hfe"); [lk_prove | exact (hy_se_at _ _ Hy) |]. iIntros "Hfe".
  iAssert (hello_stdio w0 ge o) with "[Hfo Hfe Hfi Hls Htc Hen]" as "Hio".
  { iSplitL "Hfo"; [iExact "Hfo"|]. iSplitL "Hfe"; [iExact "Hfe"|]. iSplitL "Hfi"; [iExact "Hfi"|].
    iSplitL "Hls"; [iExact "Hls"|]. iSplitL "Htc"; [iExact "Htc" | iExact "Hen"]. }
  st. st. st.
  eapply step_wand; [eapply wp_branch; ins; vx |].
  lazymatch goal with |- context [if ?c then _ else _] => destruct c end; cbn [Z.eqb edge_label].
  - st. iApply (wp_exit_call w0 ge o D X0 X Lb with "Hro Hio Hpv Hn HX"). vx.
  - st. st. st. iApply (wp_exit_call w0 ge o D X0 X Lb with "Hro Hio Hpv Hn HX"). vx.
Qed.

(** A read-only string's address is positive and a machine word. *)
Lemma str_ro_pos q : str_ro q ⊢ ⌜0 < ptr_addr q < 2 ^ 64⌝.
Proof.
  iIntros "(%s & %b & %reg & %ws & %Hsh & _)". iPureIntro.
  pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh).
  pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *.
  pose proof (Z.mod_pos_bound (ptr_addr q) 8 ltac:(lia)). lia.
Qed.

(** Help prints the translation note when a non-null locale does not
    start with "en_", then proceeds to the final stream comparison. *)
Lemma help_note e q Ψ :
  lookup (TAtom "iw_1.v41") e = Some (WPtr (ho_out o)) -> lookup (TAtom "iw_1.iw_1.v3") e = Some (WPtr q) ->
  hello_ro ge o -∗ io -∗ (⌜ptr_addr q = 0⌝ ∨ str_ro q) -∗ names o -∗ X -∗
  WP (ERun (mkFrame main_fn e [] None (Exec (TAtom "iw_1.L39")
    [Let (TAtom "iw_1.iw_1.v34") L Ptoi [Tmp (TAtom "iw_1.iw_1.v3")];
     Let (TAtom "iw_1.iw_1.v35") W (Cmp Ne L) [Tmp (TAtom "iw_1.iw_1.v34"); Const 0]]
    (JBranch (Tmp (TAtom "iw_1.iw_1.v35")) (To (TAtom "iw_1.iw_1.L36")) (To (TAtom "iw_1.iw_1.L37"))))) : gexpr)
    {{ Ψ }}.
Proof.
  intros Hv41 Hv3. iIntros "#Hro Hio Hq Hn HX".
  (* The note on translations, when the message locale is not English. *)
  iDestruct "Hq" as "[%Hq0 | #Hq]".
  - st. st. br. st. br. iApply (help_L32 with "Hro Hio Hn HX"). lk_prove.
  - iDestruct (str_ro_pos with "Hq") as %Hqa.
    st. st. br. st. st_global (hy_lits _ _ Hy "hello#str.61" ltac:(cbn; tauto)).
    iDestruct "Hq" as (s1) "#Hw1".
    iDestruct (lit_ro ge o "hello#str.61" with "Hro") as (s2) "#Hw2"; [cbn; tauto|].
    iApply (wp_call_intn w0 ge _ _ _ (fun _ => True)%I with "[]");
      [eapply fn_triple_mono; [exact (hl_strncmp _ _ _ _ _ _ Lb q (sym_ptr ge "hello#str.61") s1 s2)|];
       iIntros (r) "(%k & %Hk)"; iExists k; iSplit; [iPureIntro; exact Hk | done] | vx |
       iSplitL; [iExact "Hw1" | iExact "Hw2"] |].
    iNext. iIntros (k Hk) "_". st. st. st.
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + br. iApply (help_L32 with "Hro Hio Hn HX"). lk_prove.
    + br. st. st_global (hy_lits _ _ Hy "hello#str.62" ltac:(cbn; tauto)).
      st_global (hy_lits _ _ Hy "hello#str.63" ltac:(cbn; tauto)).
      iApply (wp_print with "Hro Hio [] [-]"); [right; right; left; split; reflexivity | vx | |].
      { iSplitL; [iApply arg_out|]. iSplitL; [iApply str_ro_arg; iApply (lit_ro with "Hro"); cbn; tauto|].
        iSplitL; [iApply str_ro_arg; iApply (lit_ro with "Hro"); cbn; tauto | done]. }
      iNext. iIntros (n8) "Hio". st. iApply (help_L32 with "Hro Hio Hn HX"). lk_prove.
Qed.

End help_end.
End HelloGlibcMainHelpEndOn.

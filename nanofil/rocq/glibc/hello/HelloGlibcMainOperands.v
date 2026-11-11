(** This file proves Hello's operand check after option parsing.
    An unknown option or an extra operand causes an error hint and an
    exit with status one. Otherwise the program proceeds to the greeting.

    The check preserves the streams, program names and exit-handler
    state until the selected continuation consumes them. Output and
    error reporting use the explicit M4 obligations; exit uses the
    concrete glibc proof. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop
  HelloGlibcMainVersion HelloGlibcMainHelpEnd HelloGlibcMainHelp.
Import ListNotations.
Open Scope Z_scope.

(** The greeting reads the saved greeting pointer and conversion-state pointer. *)
Definition join_vars (e : env) (b4 b6 : Z) : Prop :=
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
  lookup (TAtom "v6") e = Some (WPtr (mkPtr b6 (Obj b6))).

(** A bounded argument index can be widened and scaled without wrapping. *)
Lemma operand_index av i : 0 < av -> av + 8 * i + 8 <= 2 ^ 48 -> 0 <= i < 2 ^ 31 ->
  extension Sw (i mod 2 ^ 32) mod 2 ^ 64 = i /\
  (i mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64 = 8 * i /\
  (av mod 2 ^ 64 + (8 * i) mod 2 ^ 64) mod 2 ^ 64 = av + 8 * i.
Proof.
  intros H0 H1 H2. change (2 ^ 48) with 281474976710656 in H1. change (2 ^ 31) with 2147483648 in H2.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  change (2 ^ ((3 mod 4294967296) mod 64)) with 8.
  rewrite (Z.mod_small i 4294967296); [|lia]. rewrite (Z.mod_small i); [|lia].
  rewrite (Z.mod_small (i * 8)); [|lia]. rewrite (Z.mod_small (8 * i)); [|lia]. rewrite (Z.mod_small av); [|lia].
  rewrite (Z.mod_small (av + 8 * i)); [|lia]. split; [|split; [lia | reflexivity]].
  unfold extension, sign_extension. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
  rewrite (Z.mod_small i); [|lia]. destruct (2147483648 <=? i) eqn:E; [apply Z.leb_le in E; lia|].
  apply Z.mod_small. lia.
Qed.

(** A `c: int` below 2^31 reads as itself when sign-extended. *)
Lemma sext_small x : 0 <= x < 2 ^ 31 -> sign_extension (2 ^ 32) (2 ^ 31) (x mod 2 ^ 32) = x.
Proof.
  intros Hx. unfold sign_extension. rewrite Zmod_mod (Z.mod_small x); [|lia].
  destruct (2 ^ 31 <=? x) eqn:E; [apply Z.leb_le in E; lia | reflexivity].
Qed.

(** The operand proof shares one [[runtime]] and logic instance. *)
Module HelloGlibcMainOperandsOn (R : Runtime) (LG0 : LogicSig R).
(** The help module supplies the common output and exit rules. *)
Module Hp := HelloGlibcMainHelpOn R LG0.
Import Hp Hp.He Hp.He.Vn Hp.He.Vn.Lp Hp.He.Vn.Lp.Dp Hp.He.Vn.Lp.Dp.St Hp.He.Vn.Lp.Dp.St.S Hp.He.Vn.Lp.Dp.St.S.D
  Hp.He.Vn.Lp.Dp.St.S.D.FB Hp.He.Vn.Lp.Dp.St.S.D.SW Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.ML
  Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.LG Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.L
  Hp.He.Vn.Lp.Dp.St.S.D.SW.OW Hp.He.Vn.Lp.Dp.St.S.D.SW.FI.

Section operands.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o (hd_priv w0 ge o D) X0 X) (Hy : hello_layout ge o)
  (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance operands_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance operands_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation selects values of the linked language. *)
Local Notation gval := (language.val (nanofil_lang glibc_os_registry ge)).
(** This notation combines the stream state and the callees' private state. *)
Local Notation io := (hello_stdio w0 ge o ∗ hd_priv w0 ge o D)%I.

(** The greeting continuation receives the selected text, conversion
    state, streams, program names and registered exit handler. *)
Definition join_cont (Φ : gval -> iProp Σ) : iProp Σ :=
  ∀ e g, ⌜join_vars e b4 b6 /\ fresh16 b4 /\ fresh16 b6⌝ -∗
    gcell b4 g -∗ str_ro g -∗ obj b6 (heap_req 4 8) -∗ io -∗ names o -∗ X -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.join") (Some (TAtom "iw_1.L60")))) : gexpr) {{ Φ }}.

(** The option-index load checks its cell before reading the signed integer. *)
Lemma wp_optind_load f e ls lab vc chk d rest j i Ψ :
  lookup vc e = Some (WPtr (mkPtr (ho_oi o) (Obj (ho_oi o)))) -> 0 <= i < 2 ^ 31 ->
  live (ho_oi o) (ho_oireg o) -∗ int_cell (ho_oi o) 0 i -∗
  (live (ho_oi o) (ho_oireg o) -∗ int_cell (ho_oi o) 0 i -∗
   WP (ERun (mkFrame f (put d (WInt i) (put chk (WPtr (mkPtr (ho_oi o) (Obj (ho_oi o)))) e)) ls None
               (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Let chk A (Check 0 4 Read 1) [Tmp vc] ::
                  Let d W (RawLoad (LdNarrow Sw) 0) [Tmp chk] :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hv Hi. pose proof (hy_oi_at _ _ Hy) as (Hoi0 & Hoie & Hoir). iIntros "Hl [%Hi32 Hb] HK".
  rule1 "Hl" ltac:(eapply wp_check_read; ins; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  rule2 "Hl" "Hb" ltac:(eapply wp_raw_load_sub_bytes_dq; ins;
    [reflexivity | cbn -[put lookup]; rewrite Symbolic.lookup_after_put_same; reflexivity | reflexivity |
     apply load_sw_int; lia | left; reflexivity | arith]).
  iApply ("HK" with "Hl [Hb]"). iSplit; [iPureIntro; lia | iExact "Hb"].
Qed.

(** The two operand-load blocks use distinct names for the same sequence of steps. *)
Definition op_names (b : bool) : name * name * name * name * name * name :=
  if b then (TAtom "iw_1.v72", TAtom "iw_1.v73", TAtom "iw_1.v74", TAtom "iw_1.v75", TAtom "chk11", TAtom "iw_1.v76")
  else (TAtom "iw_1.v86", TAtom "iw_1.v87", TAtom "iw_1.v88", TAtom "iw_1.v89", TAtom "chk13", TAtom "iw_1.v90").

(** An equality rewrites the computed result before the caller resumes. *)
Lemma wp_let_as w f e ls lab d k op args rest j classes xs w' Ψ :
  general_op op = true -> op_arg_classes op k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res op k xs m = Some (OpRes (RVal w') m)) -> w' = w ->
  ⊢ ▷ WP (ERun (mkFrame f (put d w e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }} -∗
    WP (ERun (mkFrame f e ls None (Exec lab (Let d k op args :: rest) j)) : gexpr) {{ Ψ }}.
Proof. intros Hg Hc Hx Ho <-. iIntros "H". iApply (wp_let with "H"); eassumption. Qed.

(** An equality rewrites the computed address before the caller resumes. *)
Lemma wp_flight_as n f e ls lab d op args lw rest j xs n' c Ψ :
  map_option (flight_arg_x ge e) args = Some xs -> alu op L xs = Some (WInt n') -> flight_cap ge e lw = Some c ->
  n' = n ->
  ⊢ ▷ WP (ERun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }} -∗
    WP (ERun (mkFrame f e ls None (Exec lab (Flight d op args lw :: rest) j)) : gexpr) {{ Ψ }}.
Proof. intros Hx Ha Hc <-. iIntros "H". iApply (wp_flight with "H"); eassumption. Qed.

(** This tactic checks and loads the operand after selecting the block's names. *)
Ltac operand_steps Havp a i :=
  pose proof Havp as (Hav0 & Hav8 & H31 & Havend & Har);
  let Ei := fresh "Ei" in let E8 := fresh "E8" in let Ea := fresh "Ea" in
  destruct (operand_index a i) as (Ei & E8 & Ea); [lia | lia | lia |];
  eapply step_wand; [eapply (wp_let_as (WInt i)); ins; [reflexivity | reflexivity | vx | intros ?; reflexivity | f_equal; exact Ei] |];
  eapply step_wand; [eapply (wp_let_as (WInt (8 * i))); ins;
    [reflexivity | reflexivity | vx | intros ?; reflexivity |
     cbn; f_equal; first [exact E8 | rewrite (Z.mod_small i) in E8; [exact E8 | lia] | rewrite Zmod_mod; exact E8]] |];
  eapply step_wand; [eapply (wp_flight_as (a + 8 * i)); ins; [vx | reflexivity | vx | exact Ea] |];
  rule1 "Hal" ltac:(eapply wp_check_read; ins; [reflexivity | vx | left; reflexivity | arith | arith | arith]);
  iApply (wp_argv_load _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.to_nat i) with "[Hal Hsl] Hps");
    [apply Symbolic.lookup_after_put_same | rewrite Z2Nat.id; lia | lia | iFrame "Hal Hsl"; iPureIntro; assumption |];
    iExact "HK".

(** Loading an operand widens and scales the option index before
    checking and reading its argument slot. The final slot holds null. *)
Lemma wp_operand_load (b : bool) f e ls lab rest j ps i Ψ :
  let '(vi, ve, vs, va, chk, d) := op_names b in
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup vi e = Some (WInt i) ->
  0 <= i <= Z.of_nat (length ps) ->
  argv_own av ar ps -∗ ([∗ list] q ∈ ps, str_ro q) -∗
  ▷ (argv_own av ar ps -∗
     WP (ERun (mkFrame f (put d (WPtr (nth (Z.to_nat i) (ps ++ [null]) null))
                            (put chk (WPtr (mkPtr (av + 8 * i) (Obj av)))
                              (put va (WPtr (mkPtr (av + 8 * i) (Obj av)))
                                (put vs (WInt (8 * i)) (put ve (WInt i) e))))) ls None
                 (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Let ve L (Ext Sw) [Tmp vi] :: Let vs L Shl [Tmp ve; Const 3] ::
                  Flight va Add [FAddress (Tmp (TAtom "v2")); FValue (Tmp vs)] (LowerOf (Tmp (TAtom "v2"))) ::
                  Let chk A (Check 0 8 Read 8) [Tmp va] ::
                  Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [Tmp chk] :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof.
  destruct b; cbn [op_names]; intros H2 Hvi Hi; iIntros "(%Havp & Hal & Hsl) #Hps HK"; operand_steps Havp av i.
Qed.

(** The operand argv[k], k at most argc, is an argument a debt may be
    handed: a read-only string or null. *)
Lemma nth_arg_ro ps (k : nat) : ([∗ list] q ∈ ps, str_ro q) ⊢ arg_ro o (WPtr (nth k (ps ++ [null]) null)).
Proof.
  iIntros "#Hps". destruct (decide (k < length ps)%nat) as [Hk | Hk].
  - rewrite app_nth1; [|lia]. iApply str_ro_arg. iApply (big_sepL_elem_of with "Hps").
    apply list_elem_of_In, nth_In. lia.
  - rewrite app_nth2; [|lia]. destruct (k - length ps)%nat as [|[|n]]; cbn; iLeft; iPureIntro; left; reflexivity.
Qed.

(** The hint on `stderr`, from `iw_1.L113` entered from any block:
    `stderr` and `program_name` are loaded, `fprintf` prints the hint,
    and `exit (1)` is called. *)
Lemma operand_hint e from Ψ :
  hello_ro ge o -∗ io -∗ names o -∗ X -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L113") (Some (TAtom from)))) : gexpr) {{ Ψ }}.
Proof.
  iIntros "#Hro [Hio Hpv] Hn HX".
  iPoseProof "Hro" as "(_ & _ & _ & _ & #Hsel & #Hsec & _)".
  iDestruct "Hio" as "(Hfo & Hfe & Hfi & Hls & Htc & Hen)".
  st. st_global (hy_se _ _ Hy).
  iApply (wp_std_stream with "Hsel Hsec Hfe"); [lk_prove | exact (hy_se_at _ _ Hy) |]. iIntros "Hfe".
  iAssert (hello_stdio w0 ge o) with "[Hfo Hfe Hfi Hls Htc Hen]" as "Hio".
  { iSplitL "Hfo"; [iExact "Hfo"|]. iSplitL "Hfe"; [iExact "Hfe"|]. iSplitL "Hfi"; [iExact "Hfi"|].
    iSplitL "Hls"; [iExact "Hls"|]. iSplitL "Htc"; [iExact "Htc" | iExact "Hen"]. }
  st_global (hy_lits _ _ Hy "hello#str.79" ltac:(cbn; tauto)).
  st_global (hy_pb _ _ Hy).
  iDestruct "Hn" as (x y z) "((Hpl & Hpc & Hncr) & #Hx & #Hy' & #Hz)".
  iApply (wp_name_load with "Hpl Hpc Hx"); [exact Hy | lk_prove |]. iIntros "Hpl Hpc".
  iAssert io with "[Hio Hpv]" as "Hio"; [iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]|].
  iApply (wp_print w0 ge o D with "Hro Hio [] [-]"); [right; right; right; split; [reflexivity | eexists; reflexivity] | vx | |].
  { iSplitL; [iLeft; iPureIntro; right; right; reflexivity|].
    iSplitL; [iApply str_ro_arg; iApply (lit_ro with "Hro"); cbn; tauto|].
    iSplitL; [iApply (str_ro_arg with "Hx") | done]. }
  iNext. iIntros (n) "[Hio Hpv]".
  iApply (wp_exit_call w0 ge o D X0 X Lb with "Hro Hio Hpv [Hpl Hpc Hncr] HX"); [reflexivity|].
  iExists x, y, z. iSplitL; [|iSplitR; [iExact "Hx" | iSplitR; [iExact "Hy'" | iExact "Hz"]]].
  iSplitL "Hpl"; [iExact "Hpl"|]. iSplitL "Hpc"; [iExact "Hpc" | iExact "Hncr"].
Qed.

(** A remaining operand is reported before Hello prints its error hint and exits. *)
Lemma operand_L55 e ps i Ψ :
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> 0 <= i <= Z.of_nat (length ps) ->
  hello_ro ge o -∗ io -∗ names o -∗ X -∗ argv_own av ar ps -∗ ([∗ list] q ∈ ps, str_ro q) -∗
  live (ho_oi o) (ho_oireg o) -∗ int_cell (ho_oi o) 0 i -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L55") (Some (TAtom "iw_1.L60")))) : gexpr) {{ Ψ }}.
Proof.
  intros H2 Hi. iIntros "#Hro [Hio Hpv] Hn HX Hav #Hps Hoil Hoic".
  iAssert (⌜Z.of_nat (length ps) < 2 ^ 31⌝)%I with "[Hav]" as %H31; [iDestruct "Hav" as "[%Hp _]"; iPureIntro; tauto|].
  assert (Hi31 : 0 <= i < 2 ^ 31) by lia.
  st. st_global (hy_oi _ _ Hy).
  iApply (wp_optind_load with "Hoil Hoic"); [lk_prove | exact Hi31 |]. iIntros "Hoil Hoic".
  iApply (wp_operand_load true with "Hav Hps"); [lk_prove | lk_prove | exact Hi |]. iNext. iIntros "Hav".
  iPoseProof (nth_arg_ro ps (Z.to_nat i) with "Hps") as "#Hq".
  st. st.
  eapply step_wand; [eapply wp_branch; ins; vx |].
  lazymatch goal with |- context [if ?c then _ else _] => destruct c end; decide_branch.
  - st. st_global (hy_lits _ _ Hy "hello#str.77" ltac:(cbn; tauto)).
    st_global (hy_lits _ _ Hy "hello#str.78" ltac:(cbn; tauto)).
    st_global (hy_oi _ _ Hy).
    iApply (wp_optind_load with "Hoil Hoic"); [lk_prove | exact Hi31 |]. iIntros "Hoil Hoic".
    iApply (wp_operand_load false with "Hav Hps"); [lk_prove | lk_prove | exact Hi |]. iNext. iIntros "Hav".
    iApply (wp_call_void with "[Hio Hpv Hn]");
      [exact (hd_error_operand _ _ _ D (nth (Z.to_nat i) (ps ++ [null]) null)) | vx |
       iSplitR; [iExact "Hro"|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv"|];
       iSplitL "Hn"; [iExact "Hn" | iExact "Hq"] |].
    iNext. iIntros "(Hio & Hpv & Hn)". st.
    iApply (operand_hint with "Hro [Hio Hpv] Hn HX"). iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"].
  - iApply (operand_hint with "Hro [Hio Hpv] Hn HX"). iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"].
Qed.

(** The operand check either proceeds to the greeting or exits with status one. *)
Lemma main_operands Φ :
  hello_ro ge o -∗ join_cont Φ -∗ loop_exit w0 ge o D X av ar b4 b6 pn sn "iw_1.L10" "iw_1.L8" Φ.
Proof.
  iIntros "#Hro HJ" (e ps a i g lose [Hf [Hpr Hlose]]) "Hr".
  destruct Hf as ((H0 & H2 & H4 & H6 & Hc1) & Hb4 & Hb6 & Hi).
  iDestruct "Hr" as "(Hav & #Hps & (Hoal & Hoac & Hoil & Hoic) & Hgc & #Hg & Hnc & #Hpn & #Hsn & HX & Hio & Hpv & Hb6)".
  iPoseProof (names_intro o pn sn with "Hnc Hpn Hsn") as "Hn".
  iAssert io with "[Hio Hpv]" as "Hio"; [iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]|].
  st. destruct Hlose as [-> | ->].
  - (* No unknown option: optind against argc. *)
    br. st. st_global (hy_oi _ _ Hy).
    iAssert (⌜Z.of_nat (length ps) < 2 ^ 31⌝)%I with "[Hav]" as %H31; [iDestruct "Hav" as "[%Hp _]"; iPureIntro; tauto|].
    iApply (wp_optind_load with "Hoil Hoic"); [lk_prove | lia |]. iIntros "Hoil Hoic".
    destruct (Z.lt_dec i (Z.of_nat (length ps))) as [Hlt | Hge].
    + eapply step_wand; [eapply (wp_let_as (WInt 1)); ins; [reflexivity | reflexivity | vx | intros ?; reflexivity |
        rewrite !sext_small; [| lia | lia]; f_equal; apply Z.ltb_lt in Hlt; rewrite Hlt; reflexivity] |].
      st. st. br. iApply (operand_L55 with "Hro Hio Hn HX Hav Hps Hoil Hoic"); [lk_prove | lia].
    + eapply step_wand; [eapply (wp_let_as (WInt 0)); ins; [reflexivity | reflexivity | vx | intros ?; reflexivity |
        rewrite !sext_small; [| lia | lia]; f_equal; rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity | lia]] |].
      st. st. br. iApply ("HJ" with "[%] Hgc Hg Hb6 Hio Hn HX").
      split; [split; [lk_prove | split; lk_prove] | split; assumption].
  - (* An unknown option: the operand check, then the hint. *)
    br. st. br. iApply (operand_L55 with "Hro Hio Hn HX Hav Hps Hoil Hoic"); [lk_prove | lia].
Qed.

End operands.
End HelloGlibcMainOperandsOn.

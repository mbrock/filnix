(** This file proves Hello's version branch over userland glibc.
    The branch loads stdout, obtains the four author names, prints
    the version and exits with status zero.

    Name translation and version output remain explicit obligations.
    Exit uses the concrete glibc proof and invokes the registered callback.
    Shared load rules also support the other exit branches. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop.
From Glibc Require HelloGlibcDebts HelloGlibcMainDispatch HelloGlibcMainLoop HelloGlibcMainStart HelloGlibcMainSteps LibioLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The loop module supplies the exit state and the shared step rules. *)
Import HelloGlibcMainLoop HelloGlibcMainDispatch HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcDebts HelloGlibcDebts.FB HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.

Section version.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o (hd_priv w0 ge o D) X0 X) (Hy : hello_layout ge o)
  (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance version_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance version_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** The name cells holding the suffixes pn and sn of argv's first
    argument are [names]. *)
Lemma names_intro : ncells o pn pn sn -∗ str_ro pn -∗ str_ro sn -∗ names o.
Proof.
  iIntros "Hn #Hp #Hs". iExists pn, pn, sn. iSplitL "Hn"; [iExact "Hn"|].
  iSplitR; [iExact "Hp"|]. iSplitR; [iExact "Hp" | iExact "Hs"].
Qed.

(** A standard-stream load checks its shared pointer cell before reading it. *)
Lemma wp_std_stream f e ls lab vc chk d rest j sb sreg g Ψ :
  lookup vc e = Some (WPtr (mkPtr sb (Obj sb))) ->
  0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48 ->
  liveq DfracDiscarded sb sreg -∗ pcellq DfracDiscarded sb 0 g -∗ file_inv (ho_vb o) (ow_self w0) g -∗
  (file_inv (ho_vb o) (ow_self w0) g -∗
   WP (ERun (mkFrame f (put d (WPtr g) (put chk (WPtr (mkPtr sb (Obj sb))) e)) ls None (Exec lab rest j)) : gexpr)
     {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Let chk A (Check 0 8 Read 8) [Tmp vc] ::
                  Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [Tmp chk] :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof.
  intros Hv (Hs0 & Hs8 & Hse & Hsr). iIntros "Hl Hc Hf HK".
  rule1 "Hl" ltac:(eapply LibioLogic.wp_check_read_dq; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iApply (wp_load_stream with "Hl Hc Hf"); [apply Symbolic.lookup_after_put_same | lia | exact Hs8 |].
  iNext. iIntros "Hf". iApply ("HK" with "Hf").
Qed.

(** A program-name load checks its cell before reading the read-only name pointer. *)
Lemma wp_name_load f e ls lab vc chk d rest j x Ψ :
  hello_layout ge o -> lookup vc e = Some (WPtr (mkPtr (ho_pb o) (Obj (ho_pb o)))) ->
  live (ho_pb o) (ho_preg o) -∗ pcell (ho_pb o) 0 x -∗ str_ro x -∗
  (live (ho_pb o) (ho_preg o) -∗ pcell (ho_pb o) 0 x -∗
   WP (ERun (mkFrame f (put d (WPtr x) (put chk (WPtr (mkPtr (ho_pb o) (Obj (ho_pb o)))) e)) ls None
               (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Let chk A (Check 0 8 Read 8) [Tmp vc] ::
                  Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [Tmp chk] :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof.
  intros Hl Hv. pose proof (hy_pb_at _ _ Hl) as (Hp0 & Hp8 & Hpe & Hpr). iIntros "Hl Hc Hx HK".
  rule1 "Hl" ltac:(eapply wp_check_read; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iApply (wp_load_str w0 ge _ _ _ _ _ _ _ _ _ _ _ (DfracOwn 1) (DfracOwn 1) with "Hl Hc Hx");
    [apply Symbolic.lookup_after_put_same | lia | exact Hp8 |].
  iNext. iIntros "Hl Hc". iApply ("HK" with "Hl Hc").
Qed.

(** Exit consumes the streams, private state, names and registered handler without returning. *)
Lemma wp_exit_call f e ls lab r args rest j n Ψ :
  map_option (arg_x ge e) args = Some [WInt n] ->
  hello_ro ge o -∗ hello_stdio w0 ge o -∗ hd_priv w0 ge o D -∗ names o -∗ X -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global (TAtom "exit")) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hx. iIntros "#Hro Hio Hpv Hn HX".
  iApply (wp_call_never with "[Hio Hpv Hn HX]"); [exact (hl_exit _ _ _ _ _ _ Lb n) | exact Hx |].
  iSplitR; [iExact "Hro"|]. iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hpv"; [iExact "Hpv"|].
  iSplitL "Hn"; [iExact "Hn" | iExact "HX"].
Qed.

(** A call of `proper_name` on an author's literal s: the result q is
    a read-only string, and the stdio state is kept. *)
Lemma wp_proper_name s f e ls lab d v rest j Ψ :
  In s author_lits -> lookup v e = Some (WPtr (sym_ptr ge s)) ->
  hello_ro ge o -∗ hello_stdio w0 ge o -∗ hd_priv w0 ge o D -∗
  ▷ (∀ q, hello_stdio w0 ge o -∗ hd_priv w0 ge o D -∗ str_ro q -∗
       WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Call (CResult d P) (Global (TAtom "proper_name")) [Arg P (Tmp v)] :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof.
  intros Hs Hv. iIntros "#Hro Hio Hpv HK".
  iApply (wp_call_ptr w0 ge _ _ _ (fun q => hello_stdio w0 ge o ∗ hd_priv w0 ge o D ∗ str_ro q)%I
            with "[Hio Hpv]");
    [exact (hd_proper_name _ _ _ D s Hs) | cbn; rewrite Hv; reflexivity |
     iSplitR; [iExact "Hro" | iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]] |].
  iNext. iIntros (q) "(Hio & Hpv & Hq)". iApply ("HK" with "Hio Hpv Hq").
Qed.

(** The version branch runs from the loop exit to successful termination. *)
Lemma main_version Φ :
  hello_ro ge o -∗ loop_exit w0 ge o D X av ar b4 b6 pn sn "iw_1.L21" "iw_1.L19" Φ.
Proof.
  iIntros "#Hro" (e ps a i g lose [Hf [Hpr Hlose]]) "Hr".
  iDestruct "Hr" as "(Hav & #Hps & Hgo & Hgc & #Hg & Hnc & #Hpn & #Hsn & HX & Hio & Hpv & Hb6)".
  iPoseProof "Hro" as "(_ & _ & #Hsol & #Hsoc & _)".
  iDestruct "Hio" as "(Hfo & Hfe & Hfi & Hls & Htc & Hen)".
  step. step_global (hy_so _ _ Hy).
  iApply (wp_std_stream with "Hsol Hsoc Hfo"); [lk_prove | exact (hy_so_at _ _ Hy) |]. iIntros "Hfo".
  iAssert (hello_stdio w0 ge o) with "[Hfo Hfe Hfi Hls Htc Hen]" as "Hio".
  { iSplitL "Hfo"; [iExact "Hfo"|]. iSplitL "Hfe"; [iExact "Hfe"|]. iSplitL "Hfi"; [iExact "Hfi"|].
    iSplitL "Hls"; [iExact "Hls"|]. iSplitL "Htc"; [iExact "Htc" | iExact "Hen"]. }
  step_global (hy_lits _ _ Hy "hello#str.70" ltac:(cbn; tauto)).
  step_global (hy_lits _ _ Hy "hello#str.63" ltac:(cbn; tauto)).
  step_global (hy_lits _ _ Hy "hello#str.71" ltac:(cbn; tauto)).
  step_global (hy_lits _ _ Hy "hello#str.72" ltac:(cbn; tauto)).
  iApply (wp_proper_name "hello#str.72" with "Hro Hio Hpv"); [cbn; tauto | lk_prove |]. iNext. iIntros (q1) "Hio Hpv #Hq1".
  step_global (hy_lits _ _ Hy "hello#str.73" ltac:(cbn; tauto)).
  iApply (wp_proper_name "hello#str.73" with "Hro Hio Hpv"); [cbn; tauto | lk_prove |]. iNext. iIntros (q2) "Hio Hpv #Hq2".
  step_global (hy_lits _ _ Hy "hello#str.74" ltac:(cbn; tauto)).
  iApply (wp_proper_name "hello#str.74" with "Hro Hio Hpv"); [cbn; tauto | lk_prove |]. iNext. iIntros (q3) "Hio Hpv #Hq3".
  step_global (hy_lits _ _ Hy "hello#str.75" ltac:(cbn; tauto)).
  iApply (wp_proper_name "hello#str.75" with "Hro Hio Hpv"); [cbn; tauto | lk_prove |]. iNext. iIntros (q4) "Hio Hpv #Hq4".
  iApply (wp_call_void with "[Hio Hpv]");
    [exact (hd_version_etc _ _ _ D q1 q2 q3 q4) | vx |
     iSplitR; [iExact "Hro"|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv"|];
     iSplitR; [iExact "Hq1"|]; iSplitR; [iExact "Hq2"|]; iSplitR; [iExact "Hq3" | iExact "Hq4"] |].
  iNext. iIntros "[Hio Hpv]".
  iApply (wp_exit_call with "Hro Hio Hpv [Hnc] HX"); [reflexivity |].
  iApply (names_intro with "Hnc Hpn Hsn").
Qed.

End version.

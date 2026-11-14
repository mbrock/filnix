(** This file proves how Hello dispatches the option returned by its parser.
    Version and help options leave the loop. A greeting option replaces
    the selected text, and an unknown option records an error before
    parsing continues.

    Each branch preserves the loop's owned resources. Greeting changes
    keep the selected string read-only, and the error flag remains zero
    or one. The loop proof supplies the continuation for each back edge. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart.
From Glibc Require HelloGlibcDebts HelloGlibcMainStart HelloGlibcMainSteps.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** The option loop keeps the initialized temporaries and two fresh
    objects. Its argument count bounds the current option index. *)
Definition loop_facts (e : env) (av b4 b6 : Z) (ps : list ptr) (i : Z) : Prop :=
  start_vars e (Z.of_nat (length ps)) av b4 b6 /\ fresh16 b4 /\ fresh16 b6 /\ 0 <= i <= Z.of_nat (length ps).

(** Each incoming edge selects the error flag carried into the loop.
    Initialization selects zero, an invalid option selects one, and
    greeting changes preserve the previous flag. *)
Definition loop_entry (from : string) (e : env) (lose : Z) : Prop :=
  (from = "start"%string /\ lose = 0) \/ (from = "iw_1.L52"%string /\ lose = 1) \/
  ((from = "iw_1.L35"%string \/ from = "iw_1.L42"%string) /\
   lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)).


(** The start-block module supplies the initialized state and shared rules. *)
Import HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcDebts HelloGlibcDebts.FB HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.

Section dispatch.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X : iProp Σ)
  (Hy : hello_layout ge o) (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance dispatch_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance dispatch_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation selects values of the linked language. *)
Local Notation gval := (language.val (nanofil_lang glibc_os_registry ge)).

(** The loop owns the argument vector, option globals, greeting cell,
    name cells, exit handlers, streams and conversion state. The callees
    retain their private state, and all argument strings remain read-only. *)
Definition loop_res (ps : list ptr) (a : ptr) (i : Z) (g : ptr) : iProp Σ :=
  argv_own av ar ps ∗ ([∗ list] q ∈ ps, str_ro q) ∗ getopt_cells o a i ∗ gcell b4 g ∗ str_ro g ∗
  ncells o pn pn sn ∗ str_ro pn ∗ str_ro sn ∗ X ∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o D ∗
  obj b6 (heap_req 4 8).

(** A loop exit passes the invariant and the bounded error flag to its target block. *)
Definition loop_exit (lab from : string) (Φ : gval -> iProp Σ) : iProp Σ :=
  ∀ e ps a i g lose,
    ⌜loop_facts e av b4 b6 ps i /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)⌝ -∗
    loop_res ps a i g -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom lab) (Some (TAtom from)))) : gexpr) {{ Φ }}.

(** This tactic reads the error flag preserved on a loop back edge. *)
Ltac phi_kept H := cbn -[put]; rewrite H; cbn -[put]; rewrite Z.mod_small; [reflexivity | lia].

(** This tactic computes call arguments after rewriting a bounded value. *)
Ltac vxa H := cbn -[put];
  repeat match goal with |- context [lookup ?k ?E] =>
    let L := fresh "Hlk" in assert (L : lookup k E = _) by lk_prove; rewrite L; clear L end;
  cbn -[put]; rewrite ?H; reflexivity.

(** This tactic preserves the loop facts when the environment gains bindings. *)
Ltac lf := split; [unfold start_vars; repeat split; lk_prove | split; [assumption | split; [assumption | lia]]].

(** An exit retains the initialized temporaries and the current error flag. *)
Ltac lfacts := split; [lf | split; [lk_prove | assumption]].

(** The loop may continue to version, help or operand processing. *)
Definition loop_exits (Φ : gval -> iProp Σ) : iProp Σ :=
  loop_exit "iw_1.L21" "iw_1.L19" Φ ∧ loop_exit "iw_1.L39" "iw_1.L50" Φ ∧ loop_exit "iw_1.L10" "iw_1.L8" Φ.

(** A back edge re-enters the loop with its invariant and exit continuations. *)
Definition loop_again (Φ : gval -> iProp Σ) : iProp Σ :=
  ∀ from e lose ps a i g,
    ⌜loop_entry from e lose /\ loop_facts e av b4 b6 ps i⌝ -∗ loop_res ps a i g -∗ loop_exits Φ -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom from)))) : gexpr) {{ Φ }}.

(** The loop invariant combines these owned resources. *)
Lemma loop_res_fold ps a i g :
  argv_own av ar ps -∗ ([∗ list] q ∈ ps, str_ro q) -∗ getopt_cells o a i -∗ gcell b4 g -∗ str_ro g -∗
  ncells o pn pn sn -∗ str_ro pn -∗ str_ro sn -∗ X -∗ hello_stdio w0 ge o -∗ hd_priv w0 ge o D -∗
  obj b6 (heap_req 4 8) -∗ loop_res ps a i g.
Proof.
  iIntros "H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12".
  iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|]. iSplitL "H3"; [iExact "H3"|].
  iSplitL "H4"; [iExact "H4"|]. iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|].
  iSplitL "H7"; [iExact "H7"|]. iSplitL "H8"; [iExact "H8"|]. iSplitL "H9"; [iExact "H9"|].
  iSplitL "H10"; [iExact "H10"|]. iSplitL "H11"; [iExact "H11" | iExact "H12"].
Qed.

(** Storing a new greeting renews the checked pointer before updating its cell. *)
Lemma greeting_store f e ls lab d v rest j g q Φ :
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b4 (Obj b4))) ->
  lookup v (put d (WPtr (mkPtr b4 (Obj b4))) e) = Some (WPtr q) -> fresh16 b4 ->
  gcell b4 g -∗
  (gcell b4 q -∗ WP (ERun (mkFrame f (put d (WPtr (mkPtr b4 (Obj b4))) e) ls None (Exec lab rest j)) : gexpr)
                  {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Let d A (Renew 0 8 Write 8) [Tmp (TAtom "chk1"); Tmp (TAtom "v4")] ::
                  RawStorePointer 0 (Tmp v) (Tmp d)
                    [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] :: rest) j)) : gexpr)
    {{ Φ }}.
Proof.
  intros Hc1 H4 Hv (Hb40 & Hb416 & Hb448). iIntros "(Hl4 & Hp4 & Hy4 & Hc4) HK".
  rule1 "Hl4" ltac:(eapply wp_renew; inst;
    [reflexivity | vx | reflexivity | reflexivity | arith | cbn [r_end]; arith | arith]).
  rule2 "Hl4" "Hp4" ltac:(eapply wp_raw_store_pointer; inst;
    [cbn -[put lookup]; rewrite Hv; reflexivity |
     cbn -[put lookup]; rewrite Symbolic.lookup_after_put_same; reflexivity |
     reflexivity | arith | arith | wi_store]).
  iApply "HK". iFrame.
Qed.

(** Each nonterminal option either selects an exit or returns to the loop
    with an updated greeting or error flag. *)
Lemma loop_dispatch Φ e lose ps a i g code :
  loop_facts e av b4 b6 ps i -> lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) -> lose = 0 \/ lose = 1 ->
  lookup (TAtom "iw_1.v15") e = Some (WInt code) -> 0 <= code < 2 ^ 32 -> code <> 4294967295 ->
  hello_ro ge o -∗ loop_res ps a i g -∗ (if code =? 103 then str_ro a else True) -∗ ▷ loop_again Φ -∗
  loop_exits Φ -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L19") (Some (TAtom "iw_1.L8")))) : gexpr) {{ Φ }}.
Proof.
  intros Hf Hpr Hlose Hv15 Hcode Hn1. iIntros "#Hro Hr Hga IH HK".
  iDestruct "Hr" as "(Hav & #Hps & Hgo & Hgc & #Hg & Hnc & #Hpn & #Hsn & HX & Hio & Hpv & Hb6)".
  pose proof Hf as ((H0 & H2 & H4 & H6 & Hc1) & Hb4 & Hb6 & Hi).
  step. step.
  destruct (Z.eq_dec code 129) as [-> | H129].
  { (* --version. *)
    (branch_symbolic; LeavesLogic.decide_branch). iDestruct "HK" as "[HK _]".
    iPoseProof (loop_res_fold with "Hav Hps Hgo Hgc Hg Hnc Hpn Hsn HX Hio Hpv Hb6") as "Hr".
    iApply ("HK" $! _ ps a i g lose with "[%] Hr"). lfacts. }
  (branch_symbolic; LeavesLogic.decide_branch). step. step.
  destruct (Z.eq_dec code 103) as [-> | H103].
  { (* -g: the greeting is optarg. *)
    iEval (cbn) in "Hga". iDestruct "Hga" as "#Ha".
    (branch_symbolic; LeavesLogic.decide_branch). step. step_global (hy_oa _ _ Hy).
    iDestruct "Hgo" as "(Hoal & Hoac & Hoil & Hoic)".
    pose proof (hy_oa_at _ _ Hy) as (Hoa0 & Hoa8 & Hoae & Hoar).
    rule1 "Hoal" ltac:(eapply wp_check_read; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
    iApply (wp_load_str w0 ge _ _ _ _ _ _ _ _ _ _ _ (DfracOwn 1) (DfracOwn 1) with "Hoal Hoac Ha");
      [lk_prove | arith | exact Hoa8 |].
    iNext. iIntros "Hoal Hoac".
    iApply (greeting_store with "Hgc"); [lk_prove | lk_prove | lk_prove | exact Hb4 |]. iIntros "Hgc".
    iApply wp_goto. iNext. cbn [edge_label].
    iAssert (getopt_cells o a i) with "[Hoal Hoac Hoil Hoic]" as "Hgo".
    { iSplitL "Hoal"; [iExact "Hoal"|]. iSplitL "Hoac"; [iExact "Hoac"|]. iSplitL "Hoil"; [iExact "Hoil" | iExact "Hoic"]. }
    iPoseProof (loop_res_fold with "Hav Hps Hgo Hgc Ha Hnc Hpn Hsn HX Hio Hpv Hb6") as "Hr".
    iApply ("IH" $! "iw_1.L35"%string _ lose ps a i a with "[%] Hr HK").
    split; [right; right; split; [left; reflexivity | split; [lk_prove | exact Hlose]]|]. lf. }
  (branch_symbolic; LeavesLogic.decide_branch). step. step.
  destruct (Z.eq_dec code 128) as [-> | H128].
  { (* --help. *)
    (branch_symbolic; LeavesLogic.decide_branch). iDestruct "HK" as "[_ [HK _]]".
    iPoseProof (loop_res_fold with "Hav Hps Hgo Hgc Hg Hnc Hpn Hsn HX Hio Hpv Hb6") as "Hr".
    iApply ("HK" $! _ ps a i g lose with "[%] Hr"). lfacts. }
  (branch_symbolic; LeavesLogic.decide_branch). step. step.
  destruct (Z.eq_dec code 116) as [-> | H116].
  { (* -t: the traditional greeting. *)
    (branch_symbolic; LeavesLogic.decide_branch). step. step_global (hy_lits _ _ Hy "hello#str.76" ltac:(cbn; tauto)).
    iAssert (str_ro (sym_ptr ge "hello#str.76")) as "#Ht"; [iApply (lit_ro with "Hro"); cbn; tauto|].
    iApply (greeting_store with "Hgc"); [lk_prove | lk_prove | lk_prove | exact Hb4 |]. iIntros "Hgc".
    iApply wp_goto. iNext. cbn [edge_label].
    iPoseProof (loop_res_fold with "Hav Hps Hgo Hgc Ht Hnc Hpn Hsn HX Hio Hpv Hb6") as "Hr".
    iApply ("IH" $! "iw_1.L42"%string _ lose ps a i (sym_ptr ge "hello#str.76") with "[%] Hr HK").
    split; [right; right; split; [right; reflexivity | split; [lk_prove | exact Hlose]]|]. lf. }
  (* Any other option: an unknown one, and pr.2 becomes 1. *)
  iApply wp_branch; [vx|]. iNext. decide_branch.
  iPoseProof (loop_res_fold with "Hav Hps Hgo Hgc Hg Hnc Hpn Hsn HX Hio Hpv Hb6") as "Hr".
  iApply ("IH" $! "iw_1.L52"%string _ 1 ps a i g with "[%] Hr HK").
  split; [right; left; split; reflexivity|]. lf.
Qed.

End dispatch.

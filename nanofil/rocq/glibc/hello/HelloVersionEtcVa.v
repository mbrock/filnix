(** GNU Hello prints its version text with gnulib's `c: version_etc`.
    The function takes the authors as variable arguments and hands a
    cursor over them to `c: version_etc_va`, which copies them into an
    array, counts them, and calls `c: version_etc_arn`. The module
    [HelloVersionEtc](HelloVersionEtc.v) proves the last of the three.
    This module proves the other two for Hello's four authors. *)

From Glibc Require Import GlibcProgram GlibcTactics GlibcSpec LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry WordString FileInv FileIdle LibioLogic LibioFputsSpec
  PrintfSpec NarrowFormat NarrowArgs AllocRo VaArgRound FxprintfStream HelloVersionLits HelloGlibcDebts
  HelloGlibcLibsT HelloGlibcMainSteps HelloEmitBug CodePrelude HelloVersionEtc.
From Glibc Require Import HelloImageModule HelloImageLoad HelloImageDec01.
From Glibc Require HelloGlibcDebts LibioLogic.
From Glibc Require Import Fix.
Import ListNotations.
Import HelloGlibcDebts HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG
  HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This block is the loop header of [version_etc_va_fn]. *)
Definition va12 : block := Eval vm_compute in vblk "L12".

(** A branch whose condition is now closed follows its selected edge. *)
Ltac close_branch :=
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** The variadic rules read the copy of the arguments that a call
    makes at entry and move a cursor over it. *)
Module VeVL := VariadicLogicOn R LG0.
Import VeVL.

Section va.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
(** Every lemma here holds for any program that places Hello's objects
    and links the version functions to their code. *)
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hy : hello_layout ge o) (Hk : hello_link ge o)
  (Hl : emit_link ge) (Hv : version_link ge).

Local Definition va_program : GlibcProgram Σ := program_of w0 glibc_os_registry ge.

Local Instance va_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
Local Instance va_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** The version text goes to stdout, and a failed write sets errno.
    So the world must have descriptor 1 open and must register Hello's
    errno object. The two print calls are trusted to keep their
    contracts here, and other modules prove those contracts. *)
Context (Herr : ow_errno w0 = Some (mkPtr (ho_eb o) (Obj (ho_eb o)))) (Hfd : In 1 (ow_fds w0)).
Context `{Hfputs : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fputs") (fputs_spec (glibc_program := va_program))}.
Context `{Hfprintf : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fprintf") (fprintf_spec (glibc_program := va_program))}.

(** The array of authors comes from a fresh allocation of 80 zero
    bytes, so its first five cells hold null. *)
Lemma va_array_zero b :
  obj b (heap_req 8 80) -∗ live b (mkRegion b (b + 80) Heap Live) ∗
    pcell b 0 null ∗ pcell b 8 null ∗ pcell b 16 null ∗ pcell b 24 null ∗ pcell b 32 null.
Proof using Type.
  iIntros "Hobj". iDestruct (obj_zero_block with "Hobj") as "(Hl & Hx & Ha)"; [compute; discriminate |].
  iSplitL "Hl"; [iExact "Hl" |].
  iDestruct (zero_cell_prefix b 0 72 with "Hx Ha") as "(H0 & Hx & Ha)".
  iDestruct (zero_cell_prefix b 8 64 with "Hx Ha") as "(H1 & Hx & Ha)".
  iDestruct (zero_cell_prefix b 16 56 with "Hx Ha") as "(H2 & Hx & Ha)".
  iDestruct (zero_cell_prefix b 24 48 with "Hx Ha") as "(H3 & Hx & Ha)".
  iDestruct (zero_cell_prefix b 32 40 with "Hx Ha") as "(H4 & _ & _)".
  iFrame "H0 H1 H2 H3 H4".
Qed.

(** The registers that hold the arguments and the array keep their
    values through every round of the loop. *)
Definition va_saved (e : env) (p0 pc pp pv : ptr) (cb b : Z) : Prop :=
  lookup (TAtom "v0") e = Some (WPtr p0) /\ lookup (TAtom "v2") e = Some (WPtr pc) /\
  lookup (TAtom "v4") e = Some (WPtr pp) /\ lookup (TAtom "v6") e = Some (WPtr pv) /\
  lookup (TAtom "v8") e = Some (WPtr (mkPtr cb (Obj cb))) /\ lookup (TAtom "v11") e = Some (WPtr (mkPtr b (Obj b))).

(** One round of the copy loop reads a non-null author through the
    cursor, stores it in cell i of the array, and moves the cursor on
    by one word. *)
Lemma va_round (i : nat) q e p0 pc pp pv cb cr sb sr b Ψ :
  (i < 4)%nat -> va_saved e p0 pc pp pv cb b ->
  cb mod 8 = 0 -> 0 < sb -> sb mod 8 = 0 -> sb + 72 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 < b -> b mod 8 = 0 -> b + 80 <= 2 ^ 48 ->
  pts (va_cursor_ps cb cr (mkPtr (sb + 32 + 8 * i) (Ro sb))) -∗ live sb sr -∗ pcell sb (32 + 8 * i) q -∗ str_ro q -∗
  live b (mkRegion b (b + 80) Heap Live) -∗ pcell b (8 * i) null -∗
  ▷ (∀ e', ⌜va_saved e' p0 pc pp pv cb b⌝ -∗
     pts (va_cursor_ps cb cr (mkPtr (sb + 32 + 8 * (i + 1)) (Ro sb))) -∗ live sb sr -∗ pcell sb (32 + 8 * i) q -∗
     live b (mkRegion b (b + 80) Heap Live) -∗ pcell b (8 * i) q -∗
     WP (ERun (mkFrame version_etc_va_fn (put (TAtom "pr.1") (WInt (i + 1)) e') [] None
           (Exec (TAtom "L12") (b_insts va12) (b_jump va12))) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame version_etc_va_fn (put (TAtom "pr.1") (WInt i) e) [] None
        (Exec (TAtom "L12") (b_insts va12) (b_jump va12))) : gexpr) {{ Ψ }}.
Proof.
  intros Hi (Hv0 & Hv2 & Hv4 & Hv6 & Hv8 & Hv11) Hcb Hsb Hs8 Hsend Hsmax Hb Hb8 Hbend.
  iIntros "Hcur Hsl Hsc #Hq Hl Hc HK".
  cbn [va12 b_insts b_jump]. step. branch_symbolic.
  rewrite (Z.mod_small i); [|lia]. change (10 mod 2 ^ 64) with 10. replace (Z.of_nat i <? 10) with true by (symmetry; apply Z.ltb_lt; lia).
  close_branch. step. step. step.
  cbn [ptr_addr ptr_cap]. rewrite (Z.mod_small i); [|lia]. change ((3 mod 2 ^ 32) mod 64) with 3.
  replace ((i * 2 ^ 3) mod 2 ^ 64) with (8 * i) by (rewrite Z.mod_small; lia).
  replace ((b mod 2 ^ 64 + (8 * i) mod 2 ^ 64) mod 2 ^ 64) with (b + 8 * i) by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  iDestruct (str_ro_range with "Hq") as %Hqr. iDestruct "Hq" as (s) "#Hs".
  iApply (wp_va_arg_str (glibc_program := va_program) with "Hcur Hsl Hsc Hs"); [vx | exact Hcb | exact Hsb | lia | lia | exact Hsmax | lia | Z.div_mod_to_equations; lia | lia |].
  iNext. iIntros "Hcur Hsl Hsc _".
  assert (Hiz : 0 <= Z.of_nat i <= 3) by lia.
  check "Hl". store "Hl" "Hc".
  step. step. step. step. step.
  rewrite (Z.mod_small (ptr_addr q)); [|lia]. repeat change (0 mod 2 ^ 64) with 0.
  replace (ptr_addr q =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  branch_symbolic. close_branch. step. step. step. step.
  change (1 mod 2 ^ 64) with 1.
  replace (((i mod 2 ^ 64 + 1) mod 2 ^ 64) mod 2 ^ 64) with (Z.of_nat (i + 1)) by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  replace (sb + (32 + 8 * i) + 8) with (sb + 32 + 8 * (i + 1)) by lia.
  rewrite Nat2Z.inj_add. cbn [edge_label]. iApply ("HK" with "[%] Hcur Hsl Hsc Hl Hc"). unfold va_saved; split_and!; lk_prove.
  Qed.

(** The function copies four authors, reads the null that ends them,
    and calls the array helper. It leaves the cursor after the null,
    and it gives back stdout, errno and every cell it read. *)
Lemma va_triple pc pp pv cb cr sb sr q1 q2 q3 q4 (R : iProp Σ) :
  cb mod 8 = 0 -> 0 < sb -> sb mod 8 = 0 -> sb + 72 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  fn_triple w0 ge (TAtom "version_etc_va")
    [WPtr (ho_out o); WPtr pc; WPtr pp; WPtr pv; WPtr (mkPtr cb (Obj cb))]
    (hello_ro ge o ∗ out_idle w0 o ∗ errno_any (ho_eb o) ∗ str_ro pc ∗ str_ro pp ∗ str_ro pv ∗
     pts (va_cursor_ps cb cr (mkPtr (sb + 32) (Ro sb))) ∗ live sb sr ∗
     pcell sb 32 q1 ∗ pcell sb 40 q2 ∗ pcell sb 48 q3 ∗ pcell sb 56 q4 ∗ pcell sb 64 null ∗
     str_ro q1 ∗ str_ro q2 ∗ str_ro q3 ∗ str_ro q4 ∗ R)
    (fun r => ⌜r = RetVoid⌝ ∗ out_idle w0 o ∗ errno_any (ho_eb o) ∗
     pts (va_cursor_ps cb cr (mkPtr (sb + 72) (Ro sb))) ∗ live sb sr ∗
     pcell sb 32 q1 ∗ pcell sb 40 q2 ∗ pcell sb 48 q3 ∗ pcell sb 56 q4 ∗ pcell sb 64 null ∗ R)%I.
Proof.
  intros Hcb Hsb Hs8 Hsend Hsmax.
  exists version_etc_va_fn. split; [exact (vl_va _ Hv)|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-.
  iIntros "(#Hro & Hout & He & #Hc & #Hp & #Hv & Hcur & Hsl & S0 & S1 & S2 & S3 & S4 & #Q1 & #Q2 & #Q3 & #Q4 & HR) HK".
  step. iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence | intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b Hbb) "Hobj". change (0 < b /\ b mod 16 = 0 /\ b + 80 <= 2 ^ 48) in Hbb. destruct Hbb as (Hb & Hb16 & Hbend).
  assert (Hb8 : b mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (va_array_zero with "Hobj") as "(Hl & A0 & A1 & A2 & A3 & A4)". step. step.
  change (0 mod 2 ^ 64) with (Z.of_nat 0). cbn [edge_label].
  iRevert "Hcur". replace (sb + 32) with (sb + 32 + 8 * Z.of_nat 0) by lia. iIntros "Hcur".
  iApply (va_round 0 q1 _ (ho_out o) pc pp pv cb cr sb sr b with "Hcur Hsl S0 Q1 Hl A0"); [lia | unfold va_saved; split_and!; lk_prove | exact Hcb | exact Hsb | exact Hs8 | lia | exact Hsmax | exact Hb | exact Hb8 | exact Hbend |].
  iNext. iIntros (e1 He1) "Hcur Hsl S0 Hl A0".
  iApply (va_round 1 q2 _ (ho_out o) pc pp pv cb cr sb sr b with "Hcur Hsl S1 Q2 Hl A1"); [lia | exact He1 | exact Hcb | exact Hsb | exact Hs8 | lia | exact Hsmax | exact Hb | exact Hb8 | exact Hbend |].
  iNext. iIntros (e2 He2) "Hcur Hsl S1 Hl A1".
  iApply (va_round 2 q3 _ (ho_out o) pc pp pv cb cr sb sr b with "Hcur Hsl S2 Q3 Hl A2"); [lia | exact He2 | exact Hcb | exact Hsb | exact Hs8 | lia | exact Hsmax | exact Hb | exact Hb8 | exact Hbend |].
  iNext. iIntros (e3 He3) "Hcur Hsl S2 Hl A2".
  iApply (va_round 3 q4 _ (ho_out o) pc pp pv cb cr sb sr b with "Hcur Hsl S3 Q4 Hl A3"); [lia | exact He3 | exact Hcb | exact Hsb | exact Hs8 | lia | exact Hsmax | exact Hb | exact Hb8 | exact Hbend |].
  iNext. iIntros (e4 He4) "Hcur Hsl S3 Hl A3". destruct He4 as (He40 & He42 & He44 & He46 & He48 & He411).
  change (Z.of_nat 3 + 1) with 4. change (8 * 4) with 32. cbn [va12 b_insts b_jump].
  step. branch_symbolic. close_branch. step. step. step.
  cbn [ptr_addr ptr_cap]. change ((4 mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64) with 32.
  replace ((b mod 2 ^ 64 + 32 mod 2 ^ 64) mod 2 ^ 64) with (b + 32) by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  iApply (wp_va_arg_ptr (glibc_program := va_program) _ _ _ _ _ _ _ _ cb cr _ sb sr 64 null (DfracOwn 1) [] with "Hcur Hsl S4 []");
    [vx | exact Hcb | exact Hsb | lia | lia | exact Hsmax | lia | cbn; Z.div_mod_to_equations; lia | cbn; lia | left; reflexivity | by rewrite /ptsq |].
  iNext. iIntros "Hcur Hsl S4 _".
  check "Hl". store "Hl" "A4".
  step. step. step. step.
  step. branch_symbolic. close_branch. step.
  iApply (wp_call_fn w0 ge _ _ _ _ _ _ _ _ _ _ _ _ _
    (arn_triple w0 ge o Hk Hl Hv Herr Hfd pc pp pv b q1 q2 q3 q4
       (pts (va_cursor_ps cb cr (mkPtr (sb + 64 + 8) (Ro sb))) ∗ live sb sr ∗
        pcell sb 32 q1 ∗ pcell sb 40 q2 ∗ pcell sb 48 q3 ∗ pcell sb 56 q4 ∗ pcell sb 64 null ∗ R) Hb Hb8 Hbend)
    with "[Hout He Hl A0 A1 A2 A3 Hcur Hsl S0 S1 S2 S3 S4 HR]"); [vx | |].
  { iSplitR; [iExact "Hro"|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "He"; [iExact "He"|].
    iSplitR; [iExact "Hc"|]. iSplitR; [iExact "Hp"|]. iSplitR; [iExact "Hv"|]. iSplitL "Hl"; [iExact "Hl"|].
    iSplitL "A0"; [iExact "A0"|]. iSplitL "A1"; [iExact "A1"|]. iSplitL "A2"; [iExact "A2"|]. iSplitL "A3"; [iExact "A3"|].
    iSplitR; [iExact "Q1"|]. iSplitR; [iExact "Q2"|]. iSplitR; [iExact "Q3"|]. iSplitR; [iExact "Q4"|].
    iSplitL "Hcur"; [iExact "Hcur"|]. iSplitL "Hsl"; [iExact "Hsl"|].
    iSplitL "S0"; [iExact "S0"|]. iSplitL "S1"; [iExact "S1"|]. iSplitL "S2"; [iExact "S2"|]. iSplitL "S3"; [iExact "S3"|].
    iSplitL "S4"; [iExact "S4"|]. iExact "HR". }
  iIntros (r) "(-> & Hout & He & _ & _ & _ & _ & _ & Hcur & Hsl & S0 & S1 & S2 & S3 & S4 & HR)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. iApply wp_ret_void. iNext. iApply "HK".
  replace (sb + 64 + 8) with (sb + 72) by lia. iSplitR; [done|].
  iSplitL "Hout"; [iExact "Hout"|]. iSplitL "He"; [iExact "He"|]. iSplitL "Hcur"; [iExact "Hcur"|].
  iSplitL "Hsl"; [iExact "Hsl"|]. iSplitL "S0"; [iExact "S0"|]. iSplitL "S1"; [iExact "S1"|].
  iSplitL "S2"; [iExact "S2"|]. iSplitL "S3"; [iExact "S3"|]. iSplitL "S4"; [iExact "S4"|]. iExact "HR".
Qed.

(** Hello calls `c: version_etc` once, with these nine arguments. *)
Definition ve_args (p0 pc pp pv q1 q2 q3 q4 : ptr) : list word :=
  [WPtr p0; WPtr pc; WPtr pp; WPtr pv; WPtr q1; WPtr q2; WPtr q3; WPtr q4; WPtr null].

(** These cells of the entry copy hold the authors and the null after them. *)
Definition ve_cells sb (q1 q2 q3 q4 : ptr) : list (piece * pval) :=
  [(PLive sb, VLive (mkRegion sb (sb + 80) Heap Live))] ++
  ((PAux sb 32, VAux (ptr_cap q1)) :: cell sb 32 (ptr_addr q1)) ++
  ((PAux sb 40, VAux (ptr_cap q2)) :: cell sb 40 (ptr_addr q2)) ++
  ((PAux sb 48, VAux (ptr_cap q3)) :: cell sb 48 (ptr_addr q3)) ++
  ((PAux sb 56, VAux (ptr_cap q4)) :: cell sb 56 (ptr_addr q4)) ++
  ((PAux sb 64, VAux CNone) :: cell sb 64 0).

(** The entry copy holds the five cells that the loop reads. *)
Lemma ve_snapshot_cells p0 pc pp pv q1 q2 q3 q4 sb :
  pts (snapshot_ps (ve_args p0 pc pp pv q1 q2 q3 q4) sb (heap_req 16 72)) -∗
  live sb (mkRegion sb (sb + 80) Heap Live) ∗
  pcell sb 32 q1 ∗ pcell sb 40 q2 ∗ pcell sb 48 q3 ∗ pcell sb 56 q4 ∗ pcell sb 64 null.
Proof using Type.
  iIntros "Hps".
  iAssert (pts (ve_cells sb q1 q2 q3 q4)) with "[Hps]" as "Hps".
  { iApply (big_sepL_submseteq with "Hps"). apply NoDup_submseteq.
    - apply (NoDup_fmap_1 fst). apply (NoDup_fmap_1 (fun p => match p with
        | PLive _ => (0, 0) | PByte _ o => (1, o) | PAux _ o => (2, o) | PName k => (3, k) end)).
      apply (bool_decide_eq_true_1 _). vm_compute. reflexivity.
    - intros [l v]. unfold ve_cells. rewrite !elem_of_app. intros [Hlive | [H0 | [H1 | [H2 | [H3 | H4]]]]].
      + apply elem_of_cons in Hlive as [Hlive | Hfalse]; [|inversion Hfalse]. injection Hlive as -> ->.
        unfold snapshot_ps, obj_ps. apply list_elem_of_fmap.
        exists (PLive sb, VLive (mkRegion sb (sb + 80) Heap Live)). split; [reflexivity | left; reflexivity].
      + apply (snapshot_ps_pointer _ 4 q1); [reflexivity | vm_compute; congruence | exact H0].
      + apply (snapshot_ps_pointer _ 5 q2); [reflexivity | vm_compute; congruence | exact H1].
      + apply (snapshot_ps_pointer _ 6 q3); [reflexivity | vm_compute; congruence | exact H2].
      + apply (snapshot_ps_pointer _ 7 q4); [reflexivity | vm_compute; congruence | exact H3].
      + apply (snapshot_ps_pointer _ 8 null); [reflexivity | vm_compute; congruence | exact H4]. }
  iEval (rewrite /ve_cells !pts_app) in "Hps". iExact "Hps".
Qed.

(** The entry function allocates the cursor, points it at the authors
    in its copy of the arguments, and calls `c: version_etc_va`. The
    copy and the cursor are not given back, because nothing reads them
    after the call. *)
Lemma version_etc_triple pc pp pv q1 q2 q3 q4 (R : iProp Σ) :
  fn_triple w0 ge (TAtom "version_etc") (ve_args (ho_out o) pc pp pv q1 q2 q3 q4)
    (hello_ro ge o ∗ out_idle w0 o ∗ errno_any (ho_eb o) ∗ str_ro pc ∗ str_ro pp ∗ str_ro pv ∗
     str_ro q1 ∗ str_ro q2 ∗ str_ro q3 ∗ str_ro q4 ∗ R)
    (fun r => ⌜r = RetVoid⌝ ∗ out_idle w0 o ∗ errno_any (ho_eb o) ∗ R)%I.
Proof.
  exists version_etc_fn. split; [exact (vl_etc _ Hv)|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-.
  iIntros "(#Hro & Hout & He & #Hc & #Hp & #Hv & #Q1 & #Q2 & #Q3 & #Q4 & HR) HK".
  iApply VeVL.wp_snapshot; [discriminate | reflexivity | intros ? ? ? ? Hf Hw; exact (os_wi_snapshot _ _ _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb Hsnap) "Hsnap". change (0 < sb /\ sb mod 16 = 0 /\ sb + 80 <= 2 ^ 48) in Hsnap. destruct Hsnap as (Hsb & Hs16 & Hsend).
  assert (Hs8 : sb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (ve_snapshot_cells with "Hsnap") as "(Hsl & S0 & S1 & S2 & S3 & S4)".
  step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb Hc) "Hobj".
  change (0 < cb /\ cb mod 16 = 0 /\ cb + 32 <= 2 ^ 48) in Hc. destruct Hc as (Hcb & Hcmod & Hcend).
  assert (Hc8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hx & Ha)"; [compute; discriminate |].
  iAssert (live cb (mkRegion cb (cb + 32) Heap Live)) with "Hcl" as "Hcl".
  iDestruct (zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hcc & _ & _)".
  iApply VeVL.wp_va_args; [reflexivity |]. iNext. check "Hcl". store "Hcl" "Hcc".
  cbn [ptr_addr ptr_cap]. rewrite (Z.mod_small (sb + 32)); [|lia].
  iAssert (pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + 32) (Ro sb)))) with "[Hcl Hcc]" as "Hcur".
  { replace (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + 32) (Ro sb))) with
      ([(PLive cb, VLive (mkRegion cb (cb + 32) Heap Live))] ++ ((PAux cb 0, VAux (Ro sb)) :: cell cb 0 (sb + 32)))%list
      by reflexivity.
    rewrite pts_app. iFrame "Hcl Hcc". }
  iApply (wp_call_fn w0 ge _ _ _ _ _ _ _ _ _ _ _ _ _
    (va_triple pc pp pv cb (mkRegion cb (cb + 32) Heap Live) sb (mkRegion sb (sb + 80) Heap Live) q1 q2 q3 q4 R
       Hc8 Hsb Hs8 ltac:(cbn; lia) ltac:(cbn; lia))
    with "[Hout He Hcur Hsl S0 S1 S2 S3 S4 HR]"); [vx | |].
  { iSplitR; [iExact "Hro"|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "He"; [iExact "He"|].
    iSplitR; [iExact "Hc"|]. iSplitR; [iExact "Hp"|]. iSplitR; [iExact "Hv"|].
    iSplitL "Hcur"; [iExact "Hcur"|]. iSplitL "Hsl"; [iExact "Hsl"|].
    iSplitL "S0"; [iExact "S0"|]. iSplitL "S1"; [iExact "S1"|]. iSplitL "S2"; [iExact "S2"|]. iSplitL "S3"; [iExact "S3"|].
    iSplitL "S4"; [iExact "S4"|].
    iSplitR; [iExact "Q1"|]. iSplitR; [iExact "Q2"|]. iSplitR; [iExact "Q3"|]. iSplitR; [iExact "Q4"|]. iExact "HR". }
  iIntros (r) "(-> & Hout & He & _ & _ & _ & _ & _ & _ & _ & HR)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. iApply wp_ret_void. iNext. iApply "HK".
  iSplitR; [done|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "He"; [iExact "He"|]. iExact "HR".
Qed.

End va.

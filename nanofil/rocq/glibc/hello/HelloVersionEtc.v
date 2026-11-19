(** GNU Hello prints its version text with gnulib's `c: version_etc`.

    The function takes a variable number of arguments: the stream, the
    command name, the package, the version, and a list of author names
    that ends with a null pointer. It copies the authors into an array,
    counts them, and calls `c: version_etc_arn`, which prints the
    heading line, the copyright line, the license and the authors with
    `c: fprintf` and `c: fputs`. This module reads the three compiled
    functions from the Hello image and proves `c: version_etc_arn` over
    the contracts of those two calls. The module
    [HelloVersionEtcVa](HelloVersionEtcVa.v) proves the other two. *)

From Glibc Require Import HelloObjects.
From Glibc Require Import HelloLiterals HelloImage_versionZ2detc GlibcProgram GlibcTactics GlibcSpec
  OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry WordString FileInv LibioLogic LibioFputsSpec
  PrintfSpec NarrowFormat NarrowArgs AllocRo HelloVersionLits HelloGlibcDebts
  HelloGlibcLibsT HelloGlibcMainSteps HelloEmitBug CodePrelude.
From Glibc Require Import Fix.
Import ListNotations.
Import HelloGlibcDebts HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The three functions *)

(** The proofs read the code of the three functions from the image. *)
Definition version_etc_fn : func := HelloImage_versionZ2detc.fn_version_etc.
Definition version_etc_va_fn : func := HelloImage_versionZ2detc.fn_version_etc_va.
Definition version_etc_arn_fn : func := HelloImage_versionZ2detc.fn_version_etc_arn.

(** The function [ablk] finds the block of [version_etc_arn_fn] that has label l. *)
Definition ablk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks version_etc_arn_fn) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** The function [vblk] finds the block of [version_etc_va_fn] that has label l. *)
Definition vblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks version_etc_va_fn) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.

(** A program links the three names to that code. The module
    [HelloVersionEtcCall](HelloVersionEtcCall.v) shows that the Hello
    image does. *)
Record version_link (ge : genv) : Prop := mkVersionLink {
  vl_etc : find_fn ge (TAtom "version_etc") = Some (Defined version_etc_fn);
  vl_va : find_fn ge (TAtom "version_etc_va") = Some (Defined version_etc_va_fn);
  vl_arn : find_fn ge (TAtom "version_etc_arn") = Some (Defined version_etc_arn_fn)
}.

Section version.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
(** Every lemma here holds for any program that places Hello's objects
    and links the version functions to their code. *)
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hy : hello_layout ge o) (Hk : hello_link ge o)
  (Hl : emit_link ge) (Hv : version_link ge).

Local Definition ve_program : GlibcProgram Σ := program_of w0 glibc_os_registry ge.

Local Instance ve_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
Local Instance ve_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** The version text goes to stdout, and a failed write sets errno.
    So the world must have descriptor 1 open and must register Hello's
    errno object. The two print calls are trusted to keep their
    contracts here, and other modules prove those contracts. *)
Context (Herr : ow_errno w0 = Some (mkPtr (ho_eb o) (Obj (ho_eb o)))) (Hfd : In 1 (ow_fds w0)).
Context `{Hfputs : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fputs") (fputs_spec (glibc_program := ve_program))}.
Context `{Hfprintf : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fprintf") (fprintf_spec (glibc_program := ve_program))}.

(** A string of the version text is in [version_lits]. *)
Ltac lit_in := cbn [version_lits]; repeat (first [left; reflexivity | right]).

(** The formatter's grammar accepts a list of arguments that fits the
    directives of a format. *)
Ltac narrow_args_by :=
  repeat first
    [ apply args_end
    | apply args_literal; [reflexivity|]
    | apply args_percent
    | eapply args_conversion; [constructor; unfold promoted_int; lia|] ].

(** A read-only string starts at a nonzero address. *)
Lemma str_ro_range q : str_ro q ⊢ ⌜0 < ptr_addr q < 2 ^ 64⌝.
Proof using Type.
  iIntros "(%s & %b & %reg & %ws & %Hsh & _)". iPureIntro.
  pose proof (Z.mod_pos_bound (ptr_addr q) 8 ltac:(lia)).
  pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh).
  pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *. lia.
Qed.

(** Each of Hello's own strings is read-only. *)
Lemma hello_lit_ro s : In s hello_lits -> hello_ro ge o ⊢ str_ro (sym_ptr ge s).
Proof using Type.
  intros Hin. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _)".
  iApply (big_sepL_elem_of with "Hs"). apply list_elem_of_In. exact Hin.
Qed.

(** A call `c: fprintf (stdout, fmt, ...)` with one of the version
    formats and arguments that fit it gives stdout and errno back. *)
Lemma wp_fprintf_site f e ls lab d args rest j n bytes ds ys Ψ :
  In (n, bytes) version_lits -> parse_narrow bytes = Some ds -> narrow_args ds ys ->
  forallb snapshot_word ys = true ->
  map_option (arg_x ge e) args = Some (WPtr (ho_out o) :: WPtr (sym_ptr ge n) :: ys) ->
  hello_ro ge o -∗ out_idle w0 o -∗ errno_any (ho_eb o) -∗ ([∗ list] a ∈ ys, str_arg a) -∗
  ▷ (∀ x, out_idle w0 o -∗ errno_any (ho_eb o) -∗
     WP (ERun (mkFrame f (put d x e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global (TAtom "fprintf")) args :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof using Herr Hfd Hk Hfprintf.
  intros Hin Hp Ha Hs Hx. iIntros "#Hro Hout He Hys HK".
  iApply (wp_call_spec glibc_os_registry (os_wi w0) ge (TAtom "fprintf") (fprintf_spec (glibc_program := ve_program))
    (PfIn (ho_vb o) (ho_out o) 1 (sym_ptr ge n) DfracDiscarded bytes ds ys [] (ho_eb o))
    with "[Hout He Hys]"); [exact Hx| |].
  { cbn [fs_pre fprintf_spec]. unfold pf_fits, pf_pre.
    cbn [pf_vb pf_fp pf_fd pf_fmt pf_dq pf_bytes pf_ds pf_ys pf_rest pf_eb ve_program program_of program_world program_ge].
    iSplit; [iPureIntro; split_and!; [exact Hp | exact (narrow_fits_all _ _ Ha) | exact Hs | exact Herr | exact Hfd |
      exact (hk_errno_at _ _ Hk)]|].
    iPoseProof "Hro" as "(Hvt & Hsg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _)".
    iFrame "Hout He Hys". iSplitR; [iApply (version_lit _ _ _ Hin with "Hro")|].
    iSplitR; [iExact "Hpr"|]. iSplitR; [iExists _, _, _; iFrame "Hvt Hsg"|].
    iApply (malloc_ro_of_hello_ro with "Hro"); exact Hk. }
  iIntros (v) "(%r & [-> %Hr] & Hout & _ & He)". iExists _. iSplit; [iPureIntro; reflexivity|].
  iNext. iApply ("HK" with "Hout He").
Qed.

(** Loading an author's pointer from the array reads a cell that the
    function owns. The pointer's string lends the lifetime of its
    object for the load. *)
Lemma wp_load_author f e ls lab d c rest j p b reg off x Ψ :
  lookup c e = Some (WPtr p) -> ptr_cap p = Obj b -> ptr_addr p = b + off -> 0 <= b -> 0 <= off -> b + off < 2 ^ 64 ->
  (b + off) mod 8 = 0 ->
  live b reg -∗ pcell b off x -∗ str_ro x -∗
  ▷ (live b reg -∗ pcell b off x -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead])
                                             [Tmp c] :: rest) j)) : gexpr) {{ Ψ }}.
Proof using Type.
  intros Hc Hcap Ha Hb0 Ho0 Hb64 Hb8. iIntros "Hl Hp Hs HK". iDestruct (str_ro_cap with "Hs") as (reg') "[Hk %Hq]".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ b reg off x reg' (DfracOwn 1) (DfracOwn 1) DfracDiscarded
            with "Hl Hp Hk");
    [reflexivity | cbn; rewrite Hc; reflexivity | left; exact Hcap |
     unfold raw_address; rewrite Ha Z.add_0_r; apply Z.mod_small; lia | exact Hb8 | exact Hq |].
  iNext. iIntros "Hl Hp _". iApply ("HK" with "Hl Hp").
Qed.

(** The array helper prints the version text for four authors. *)
Lemma arn_triple pc pp pv b q1 q2 q3 q4 (R : iProp Σ) :
  0 < b -> b mod 8 = 0 -> b + 80 <= 2 ^ 48 ->
  fn_triple w0 ge (TAtom "version_etc_arn")
    [WPtr (ho_out o); WPtr pc; WPtr pp; WPtr pv; WPtr (mkPtr b (Obj b)); WInt 4]
    (hello_ro ge o ∗ out_idle w0 o ∗ errno_any (ho_eb o) ∗ str_ro pc ∗ str_ro pp ∗ str_ro pv ∗
     live b (mkRegion b (b + 80) Heap Live) ∗ pcell b 0 q1 ∗ pcell b 8 q2 ∗ pcell b 16 q3 ∗ pcell b 24 q4 ∗
     str_ro q1 ∗ str_ro q2 ∗ str_ro q3 ∗ str_ro q4 ∗ R)
    (fun r => ⌜r = RetVoid⌝ ∗ out_idle w0 o ∗ errno_any (ho_eb o) ∗
     live b (mkRegion b (b + 80) Heap Live) ∗ pcell b 0 q1 ∗ pcell b 8 q2 ∗ pcell b 16 q3 ∗ pcell b 24 q4 ∗ R)%I.
Proof using Herr Hfd Hfprintf Hfputs Hk Hl Hv.
  intros Hb Hb8 Hbend.
  exists version_etc_arn_fn. split; [exact (vl_arn _ Hv)|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-.
  iIntros "(#Hro & Hout & He & #Hc & #Hp & #Hv & Hl & H0 & H1 & H2 & H3 & #Q1 & #Q2 & #Q3 & #Q4 & HR) HK".
  iDestruct (str_ro_range with "Hc") as %Hpc. step. step. step. branch_symbolic.
  rewrite (Z.mod_small (ptr_addr pc)); [|lia]. change (0 mod 2 ^ 64) with 0.
  replace (ptr_addr pc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn -[put].
  step.
  step_global (lit_lookup ge Hl "version-etc#str.41" _ ltac:(lit_in)).
  iApply (wp_fprintf_site _ _ _ _ _ _ _ _ "version-etc#str.41" _ _ [WPtr pc; WPtr pp; WPtr pv]
  with "Hro Hout He [Hc Hp Hv]"); [lit_in | vm_compute; reflexivity | narrow_args_by | reflexivity | vx | |].
  { cbn [big_opL]. iSplit; [iApply str_ro_arg; iExact "Hc"|]. iSplit; [iApply str_ro_arg; iExact "Hp"|].
  iSplit; [iApply str_ro_arg; iExact "Hv"|]. done. }
  iNext. iIntros (x23) "Hout He".
  step. step.
  destruct (el_domain _ Hl) as [p43 L43].
  step_global (lit_lookup ge Hl "version_etc_copyright" _ ltac:(lit_in)). step_global L43.
  step_global (lit_lookup ge Hl "version-etc#str.44" _ ltac:(lit_in)).
  iApply (wp_fprintf_site _ _ _ _ _ _ _ _ "version_etc_copyright" _ _ [WPtr (sym_ptr ge "version-etc#str.44"); WInt 2026]
  with "Hro Hout He [Hro]"); [lit_in | vm_compute; reflexivity | narrow_args_by | reflexivity | vx | |].
  { cbn [big_opL]. iSplit; [iApply str_arg_ro; iApply (version_lit ge o (_, _) with "Hro"); lit_in|]. iSplit; done. }
  iNext. iIntros (x33) "Hout He".
  step_global (lit_lookup ge Hl "version-etc#str.45" [10] ltac:(lit_in)).
  iApply (wp_fputs_site w0 ge o Hk Herr Hfd _ _ _ _ _ _ _ _ "version-etc#str.45" [10] with "Hro Hout He"); [lit_in | vx |].
  iNext. iIntros (x36) "Hout He".
  step_global L43.
  step_global (lit_lookup ge Hl "version-etc#str.46" _ ltac:(lit_in)).
  step_global (lit_lookup ge Hl "version-etc#str.47" _ ltac:(lit_in)).
  iApply (wp_fprintf_site _ _ _ _ _ _ _ _ "version-etc#str.46" _ _ [WPtr (sym_ptr ge "version-etc#str.47")]
  with "Hro Hout He [Hro]"); [lit_in | vm_compute; reflexivity | narrow_args_by | reflexivity | vx | |].
  { cbn [big_opL]. iSplit; [iApply str_arg_ro; iApply (version_lit ge o (_, _) with "Hro"); lit_in|]. done. }
  iNext. iIntros (x41) "Hout He".
  step_global (lit_lookup ge Hl "version-etc#str.45" [10] ltac:(lit_in)).
  iApply (wp_fputs_site w0 ge o Hk Herr Hfd _ _ _ _ _ _ _ _ "version-etc#str.45" [10] with "Hro Hout He"); [lit_in | vx |].
  iNext. iIntros (x44) "Hout He".
  step. branch. step. step. branch. step. step. branch. step. step. branch. step. step. branch. step.
  step_global L43. step_global (lit_lookup ge Hl "version-etc#str.51" _ ltac:(lit_in)).
  check "Hl".
  iApply (wp_load_author with "Hl H0 Q1"); [lk_prove | reflexivity | cbn; lia | lia | lia | lia | rewrite Z.add_0_r; exact Hb8 |].
  iNext. iIntros "Hl H0".
  step. check "Hl".
  iApply (wp_load_author with "Hl H1 Q2"); [lk_prove | reflexivity | cbn; rewrite !(Z.mod_small _ (2 ^ 64)); lia | lia | lia | lia | a2 |].
  iNext. iIntros "Hl H1".
  step. check "Hl".
  iApply (wp_load_author with "Hl H2 Q3"); [lk_prove | reflexivity | cbn; rewrite !(Z.mod_small _ (2 ^ 64)); lia | lia | lia | lia | a2 |].
  iNext. iIntros "Hl H2".
  step. check "Hl".
  iApply (wp_load_author with "Hl H3 Q4"); [lk_prove | reflexivity | cbn; rewrite !(Z.mod_small _ (2 ^ 64)); lia | lia | lia | lia | a2 |].
  iNext. iIntros "Hl H3".
  iApply (wp_fprintf_site _ _ _ _ _ _ _ _ "version-etc#str.51" _ _ [WPtr q1; WPtr q2; WPtr q3; WPtr q4]
  with "Hro Hout He [Q1 Q2 Q3 Q4]"); [lit_in | vm_compute; reflexivity | narrow_args_by | reflexivity | vx | |].
  { cbn [big_opL]. iSplit; [iApply str_ro_arg; iExact "Q1"|]. iSplit; [iApply str_ro_arg; iExact "Q2"|].
  iSplit; [iApply str_ro_arg; iExact "Q3"|]. iSplit; [iApply str_ro_arg; iExact "Q4"|]. done. }
  iNext. iIntros (x98) "Hout He".
  step. step. iApply wp_ret_void. iNext. iApply "HK". iFrame. done.
  Qed.

End version.

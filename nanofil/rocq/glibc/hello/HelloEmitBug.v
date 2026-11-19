(** Hello's help text ends with gnulib's `c: emit_bug_reporting_address`,
    which prints where to report bugs. The function is one block. It
    loads stdout, writes an empty line with `c: fputs`, and prints three
    lines with `c: printf`. This module proves that block over the
    contracts of those two calls, so the function is safe as soon as
    the two contracts are proved.

    Each call must leave stdout ready for the next one. The contracts
    of both calls say this directly: each takes stdout idle and gives it
    back idle. The two contracts are hypotheses here. The printf proof
    derives the contract of `c: printf` from the formatter's contract,
    and the libio proof will discharge the contract of `c: fputs`. *)

From Glibc Require Import GlibcProgram GlibcTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import HelloBodies.

From Glibc Require Import OsWorld OsBlocks OsRegistry WordString FileInv FileIdle LibioLogic LibioFputsSpec
  PrintfSpec NarrowFormat NarrowArgs AllocRo HelloVersionLits HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require Import HelloImageModule HelloImageLoad.
From Glibc Require Import Fix.
Import ListNotations.
Import HelloGlibcDebts HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG
  HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.
Open Scope Z_scope.

(** ## The link

    A proof about the real program has to know which body a call runs
    and where each string lives. The record below collects those facts
    for the linked program. *)

(** The linked program runs gnulib's body of the function, and every
    string of the version text, as well as the text domain that the
    body copies without using, has a symbol. *)
Record emit_link (ge : genv) : Prop := mkEmitLink {
  el_fn : find_fn ge (TAtom "emit_bug_reporting_address") =
    Some (Defined emit_bug_reporting_address_fn);
  el_lits : forall ns, In ns version_lits -> lookup (TAtom ns.1) (ge_globals ge) = Some (sym_ptr ge ns.1);
  el_domain : is_Some (lookup (TAtom "version-etc#str.43") (ge_globals ge))
}.

Section emit.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hy : hello_layout ge o) (Hk : hello_link ge o)
  (Hl : emit_link ge).

(** The contracts of the two calls are stated for a program bundle. *)
Local Definition emit_program : GlibcProgram Σ := program_of w0 glibc_os_registry ge.

Local Instance emit_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
Local Instance emit_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** stdout is idle between calls and writes to descriptor 1. *)
Definition out_idle : iProp Σ := file_idle (ho_vb o) (ow_self w0) (ho_out o) 1.

(** errno is the object that the world registers, and descriptor 1 is open. *)
Context (Herr : ow_errno w0 = Some (mkPtr (ho_eb o) (Obj (ho_eb o)))) (Hfd : In 1 (ow_fds w0)).

(** The contracts of `c: fputs` and `c: printf` are hypotheses. *)
Context `{Hfputs : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fputs") (fputs_spec (glibc_program := emit_program))}.
Context `{Hprintf : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "printf") (printf_spec (glibc_program := emit_program))}.

(** Each string of the version text is read-only with its bytes. *)
Lemma version_lit ns : In ns version_lits -> hello_ro ge o ⊢ word_string DfracDiscarded (sym_ptr ge ns.1) ns.2.
Proof using Type.
  intros Hin. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [Hv _])".
  iApply (big_sepL_elem_of with "Hv"). apply list_elem_of_In. exact Hin.
Qed.

(** The allocator's read-only share in [hello_ro] is what the two
    calls borrow when they allocate a buffer. *)
Lemma malloc_ro_of_hello_ro : hello_ro ge o ⊢ malloc_ro (glibc_program := emit_program).
Proof using Hk.
  iIntros "(_ & _ & _ & _ & _ & _ & _ & Htc & _)".
  iExists (ho_mp o), (ho_tc o), (ho_dm o), (ho_mpreg o), (ho_tcreg o), (ho_dmreg o).
  iSplit; [iPureIntro; split; [exact (hk_mp _ _ Hk) | exact (hk_tc _ _ Hk)]|]. iExact "Htc".
Qed.

(** Loading stdout checks its shared cell and reads the stream's
    pointer. The idle stream lends its object's lifetime for the read. *)
Lemma wp_out_load f e ls lab vc chk d rest j Ψ :
  lookup vc e = Some (WPtr (mkPtr (ho_so o) (Obj (ho_so o)))) ->
  hello_ro ge o -∗ out_idle -∗
  (out_idle -∗
   WP (ERun (mkFrame f (put d (WPtr (ho_out o)) (put chk (WPtr (mkPtr (ho_so o) (Obj (ho_so o)))) e)) ls None
     (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Let chk A (Check 0 8 Read 8) [Tmp vc] ::
                  Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [Tmp chk] :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof using Hy.
  intros Hv. pose proof (hy_so_at _ _ Hy) as (Hs0 & Hs8 & Hse & Hsr).
  iIntros "(_ & _ & Hl & Hc & _) Hf HK".
  rule1 "Hl" ltac:(eapply OsMemLogic.wp_check_read_dq; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iDestruct "Hf" as "(%fb & %freg & %st & %nb & %Hp & Hfl & Hrest)".
  pose proof Hp as (Hg & Hal & Hfb & Hend & Hreg & _).
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ho_so o) (ho_soreg o) 0 (ho_out o) freg
            DfracDiscarded DfracDiscarded (DfracOwn 1) with "Hl Hc [Hfl]");
    [reflexivity | vx | left; reflexivity |
     cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia | rewrite Z.add_0_r; exact Hs8 |
     rewrite Hg; cbn; unfold file_size in *; lia | rewrite Hg; iExact "Hfl" |].
  iNext. iIntros "_ _ Hfl". iApply "HK". iExists fb, freg, st, nb.
  iSplit; [iPureIntro; exact Hp|]. rewrite Hg. iSplitL "Hfl"; [iExact "Hfl"|iExact "Hrest"].
Qed.

(** A read-only string is a valid string argument. *)
Lemma str_arg_ro p bs : word_string DfracDiscarded p bs ⊢ str_arg (WPtr p).
Proof using Type.
  iIntros "Hs". iRight. iExists p, bs, 0%nat. iFrame "Hs". iPureIntro. split; [|lia].
  destruct p as [a c]. unfold ptr_add. cbn. rewrite Z.add_0_r. reflexivity.
Qed.

(** A call `c: printf (fmt, ...)` with one of the version formats and
    arguments that fit it gives stdout and errno back. The call site
    binds the result in d. *)
Lemma wp_printf_site f e ls lab d args rest j n bytes ds ys Ψ :
  In (n, bytes) version_lits -> parse_narrow bytes = Some ds -> narrow_args ds ys ->
  forallb snapshot_word ys = true ->
  map_option (arg_x ge e) args = Some (WPtr (sym_ptr ge n) :: ys) ->
  hello_ro ge o -∗ out_idle -∗ errno_any (ho_eb o) -∗ ([∗ list] a ∈ ys, str_arg a) -∗
  ▷ (∀ x, out_idle -∗ errno_any (ho_eb o) -∗
     WP (ERun (mkFrame f (put d x e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global (TAtom "printf")) args :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof using Herr Hfd Hy Hk Hprintf.
  intros Hin Hp Ha Hs Hx. iIntros "#Hro Hout He Hys HK".
  pose proof (hy_so_at _ _ Hy) as (Hs0 & Hs8 & Hse & Hsr).
  iApply (wp_call_spec glibc_os_registry (os_wi w0) ge (TAtom "printf") (printf_spec (glibc_program := emit_program))
    (DfracDiscarded, PfIn (ho_vb o) (ho_out o) 1 (sym_ptr ge n) DfracDiscarded bytes ds ys [] (ho_eb o))
    with "[Hout He Hys]"); [exact Hx| |].
  { cbn [fs_pre printf_spec pf_pre pf_vb pf_fp pf_fd pf_fmt pf_dq pf_bytes pf_ys pf_eb
      emit_program program_of program_world program_ge].
    iSplit; [iPureIntro; split_and!; [exact Hp | exact (narrow_fits_all _ _ Ha) | exact Hs | exact Herr | exact Hfd |
      exact (hk_errno_at _ _ Hk)]|].
    iPoseProof "Hro" as "(Hv & Hsg & Hsol & Hsoc & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _)".
    iSplitR; [iExists (ho_so o), (ho_soreg o); iSplit; [iPureIntro; split_and!; [exact (hy_so _ _ Hy) | exact Hs8 | exact Hse]|];
      iSplitR; [iExact "Hsol" | iExact "Hsoc"]|].
    iFrame "Hout He Hys". iSplitR; [iApply (version_lit _ Hin with "Hro")|].
    iSplitR; [iExact "Hpr"|]. iSplitR; [iExists _, _, _; iFrame "Hv Hsg"|].
    iApply (malloc_ro_of_hello_ro with "Hro"). }
  iIntros (v) "(_ & %r & [-> %Hr] & Hout & _ & He)". iExists _. iSplit; [iPureIntro; reflexivity|].
  iNext. iApply ("HK" with "Hout He").
Qed.

(** A call `c: fputs (s, stdout)` with one of the version strings
    gives stdout and errno back. *)
Lemma wp_fputs_site f e ls lab d args rest j n bytes Ψ :
  In (n, bytes) version_lits ->
  map_option (arg_x ge e) args = Some [WPtr (sym_ptr ge n); WPtr (ho_out o)] ->
  hello_ro ge o -∗ out_idle -∗ errno_any (ho_eb o) -∗
  ▷ (∀ x, out_idle -∗ errno_any (ho_eb o) -∗
     WP (ERun (mkFrame f (put d x e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global (TAtom "fputs")) args :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof using Herr Hfd Hk Hfputs.
  intros Hin Hx. iIntros "#Hro Hout He HK".
  iApply (wp_call_spec glibc_os_registry (os_wi w0) ge (TAtom "fputs") (fputs_spec (glibc_program := emit_program))
    (FputsIn (ho_vb o) (sym_ptr ge n) DfracDiscarded bytes (ho_out o) 1 (ho_eb o)) with "[Hout He]"); [exact Hx| |].
  { cbn [fs_pre fputs_spec fi_vb fi_p fi_dq fi_s fi_fp fi_fd fi_eb emit_program program_of program_world program_ge].
    iSplit; [iPureIntro; split; [exact Herr | exact Hfd]|].
    iSplitR; [iApply (version_lit _ Hin with "Hro")|].
    iFrame "Hout He". iSplitR; [iPoseProof "Hro" as "(Hv & Hs & _)"; iExists _, _, _; iFrame "Hv Hs"|].
    iApply (malloc_ro_of_hello_ro with "Hro"). }
  iIntros (v) "(%r & [-> %Hr] & _ & Hout & He)". iExists _. iSplit; [iPureIntro; reflexivity|].
  iNext. iApply ("HK" with "Hout He").
Qed.

(** A string of the version text has a symbol in the linked program. *)
Ltac lit_in := cbn [version_lits]; repeat (first [left; reflexivity | right]).
Lemma lit_lookup n bytes : In (n, bytes) version_lits -> lookup (TAtom n) (ge_globals ge) = Some (sym_ptr ge n).
Proof using Hl. intros Hin. exact (el_lits _ Hl (n, bytes) Hin). Qed.

(** The formatter's grammar accepts a list of arguments that fits the
    directives of a format. *)
Ltac narrow_args_by :=
  repeat first
    [ apply args_end
    | apply args_literal; [reflexivity|]
    | apply args_percent
    | eapply args_conversion; [constructor; unfold promoted_int; lia|] ].

(** The block copies the text domain three times without using it,
    writes an empty line, and prints the bug address, the home page and
    the general help address. Each call gives stdout and errno back, so
    the function returns them, and it touches nothing else. *)
Lemma emit_bug_triple (R : iProp Σ) :
  fn_triple w0 ge (TAtom "emit_bug_reporting_address") []
    (hello_ro ge o ∗ out_idle ∗ errno_any (ho_eb o) ∗ R)
    (fun r => ⌜r = RetVoid⌝ ∗ out_idle ∗ errno_any (ho_eb o) ∗ R)%I.
Proof using Type*.
  exists emit_bug_reporting_address_fn. split; [exact (el_fn _ Hl)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  iIntros "(#Hro & Hout & He & HR) HK".
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump emit_bug_reporting_address_start].
  destruct (el_domain _ Hl) as [p43 L43].
  step_global (lit_lookup "version-etc#str.45" [10] ltac:(lit_in)). step_global (hy_so _ _ Hy).
  iApply (wp_out_load with "Hro Hout"); [lk_prove|]. iIntros "Hout".
  iApply (wp_fputs_site _ _ _ _ _ _ _ _ "version-etc#str.45" [10] with "Hro Hout He"); [lit_in | vx |].
  iNext. iIntros (x3) "Hout He".
  step_global L43.
  step_global (lit_lookup "version-etc#str.58" _ ltac:(lit_in)).
  step_global (lit_lookup "version-etc#str.59" _ ltac:(lit_in)).
  iApply (wp_printf_site _ _ _ _ _ _ _ _ "version-etc#str.58" _ _ [WPtr (sym_ptr ge "version-etc#str.59")]
    with "Hro Hout He [Hro]"); [lit_in | vm_compute; reflexivity | narrow_args_by | reflexivity | vx | |].
  { cbn [big_opL]. iSplit; [|done]. iApply str_arg_ro. iApply (version_lit (_, _) with "Hro"). lit_in. }
  iNext. iIntros (x7) "Hout He".
  step_global L43.
  step_global (lit_lookup "version-etc#str.60" _ ltac:(lit_in)).
  step_global (lit_lookup "version-etc#str.61" _ ltac:(lit_in)).
  step_global (lit_lookup "version-etc#str.62" _ ltac:(lit_in)).
  iApply (wp_printf_site _ _ _ _ _ _ _ _ "version-etc#str.60" _ _
    [WPtr (sym_ptr ge "version-etc#str.61"); WPtr (sym_ptr ge "version-etc#str.62")]
    with "Hro Hout He [Hro]"); [lit_in | vm_compute; reflexivity | narrow_args_by | reflexivity | vx | |].
  { cbn [big_opL]. iSplit; [|iSplit; [|done]]; iApply str_arg_ro; iApply (version_lit (_, _) with "Hro"); lit_in. }
  iNext. iIntros (x12) "Hout He".
  step_global L43.
  step_global (lit_lookup "version-etc#str.63" _ ltac:(lit_in)).
  step_global (lit_lookup "version-etc#str.64" _ ltac:(lit_in)).
  iApply (wp_printf_site _ _ _ _ _ _ _ _ "version-etc#str.63" _ _ [WPtr (sym_ptr ge "version-etc#str.64")]
    with "Hro Hout He [Hro]"); [lit_in | vm_compute; reflexivity | narrow_args_by | reflexivity | vx | |].
  { cbn [big_opL]. iSplit; [|done]. iApply str_arg_ro. iApply (version_lit (_, _) with "Hro"). lit_in. }
  iNext. iIntros (x16) "Hout He".
  iApply wp_ret_void. iNext. iApply "HK". iFrame "Hout He HR". done.
Qed.
End emit.

(** ## Hello's image

    Hello's linked image has gnulib's body and a symbol for every
    string. *)

(** Every string of the version text has a symbol in the image. *)
Lemma version_lits_placed :
  forallb (fun ns : string * list Z => if lookup (TAtom ns.1) img_globals then true else false) version_lits = true.
Proof. vm_compute. reflexivity. Qed.

Lemma emit_link_image fr : emit_link (mkGenv hello_image_module img_globals fr).
Proof.
  constructor.
  - vm_compute. reflexivity.
  - intros ns Hin. pose proof version_lits_placed as P. rewrite forallb_forall in P.
    specialize (P ns Hin). unfold sym_ptr. cbn [ge_globals].
    destruct (lookup (TAtom ns.1) img_globals); [reflexivity | discriminate].
  - vm_compute. eexists. reflexivity.
Qed.

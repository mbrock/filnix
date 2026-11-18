(** Main prints its help text with `c: fputs` and three lines with
    `c: fprintf`: the usage line and the translation-bugs line go to
    stdout, and the hint to try `--help` goes to stderr. The proof of
    main needs each of these calls to keep the standard streams that
    main holds. This module proves that from the contracts of glibc's
    `c: fputs` and `c: fprintf`, and the image proof in
    [HelloVersionEtcCall](HelloVersionEtcCall.v) supplies those
    contracts. *)

From Glibc Require Import GlibcProgram GlibcTactics GlibcSpec LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry WordString FileInv FileIdle LibioLogic LibioFputsSpec
  PrintfSpec NarrowFormat NarrowArgs AllocRo HelloGlibcDebts HelloGlibcLibsT HelloEmitBug HelloVersionEtc.
From Glibc Require HelloGlibcDebts.
From Glibc Require Import Fix.
Import ListNotations.
Import HelloGlibcDebts HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG
  HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.
Open Scope Z_scope.

Section sites.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
(** The lemmas hold for any program that places Hello's objects. *)
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hy : hello_layout ge o) (Hk : hello_link ge o).

Local Definition print_program : GlibcProgram Σ := program_of w0 glibc_os_registry ge.

(** Stdout and stderr write to descriptors 1 and 2, and a failed write
    sets errno, so the world must have both descriptors open and must
    register Hello's errno object. *)
Context (Herr : ow_errno w0 = Some (mkPtr (ho_eb o) (Obj (ho_eb o))))
  (Hfd1 : In 1 (ow_fds w0)) (Hfd2 : In 2 (ow_fds w0)).
Context `{Hfputs : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fputs") (fputs_spec (glibc_program := print_program))}.
Context `{Hfprintf : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fprintf") (fprintf_spec (glibc_program := print_program))}.

(** A contract proves a call that passes its arguments. The caller's
    state must give the contract's precondition for some input x with
    those arguments, and a frame F x that the call does not touch. The
    postcondition with the frame must give back the caller's state. *)
Lemma triple_of_spec n (s : fspec Σ) x0 xs (P : iProp Σ) (Q : outcome -> iProp Σ) (F : fs_binder s -> iProp Σ) :
  GlibcSpec.HasSpec glibc_os_registry (os_wi w0) ge n s -> fs_args s x0 = xs ->
  (P ⊢ ∃ x, ⌜fs_args s x = xs⌝ ∗ fs_pre s x ∗ F x) -> (forall x r, fs_post s x r ∗ F x ⊢ Q r) ->
  fn_triple w0 ge n xs P Q.
Proof using Type.
  intros Hs Hx0 HP HQ. destruct (Hs x0) as (gf & Hg & Hfr & _).
  exists gf. split; [exact Hg|]. split; [rewrite -Hx0; exact Hfr|]. intros fr Φ Hf.
  iIntros "HP HK". iDestruct (HP with "HP") as (x Hx) "[Hpre HF]".
  destruct (Hs x) as (gf' & Hg' & _ & Ht). rewrite Hg in Hg'. injection Hg' as <-.
  rewrite -Hx in Hf. iApply (Ht fr Φ Hf with "Hpre"). iIntros (r) "Hq". iApply "HK". iApply HQ. iFrame.
Qed.

(** The format named n has the bytes bs in [print_fmts], so
    [hello_ro] holds it with those bytes. *)
Lemma print_fmt n bs : In (n, bs) print_fmts -> hello_ro ge o ⊢ word_string DfracDiscarded (sym_ptr ge n) bs.
Proof using Type.
  intros Hin. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf)".
  iApply (big_sepL_elem_of (fun ns => word_string DfracDiscarded (sym_ptr ge ns.1) ns.2) _ (n, bs) with "Hf").
  apply list_elem_of_In. exact Hin.
Qed.

(** A call `c: fputs (s, stdout)` with one of the help strings keeps
    the streams and any state P. *)
Lemma fputs_site_hello (P : iProp Σ) s :
  In s fputs_lits ->
  fn_triple w0 ge (TAtom "fputs") [WPtr (sym_ptr ge s); WPtr (ho_out o)]
    (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P ∗ [∗ list] x ∈ skipn 2 [WPtr (sym_ptr ge s); WPtr (ho_out o)], str_arg x)%I
    (ret_int (hello_stdio w0 ge o ∗ P))%I.
Proof using Type*.
  intros Hin.
  assert (Hl : In s hello_lits) by (cbn in Hin |- *; tauto).
  apply (triple_of_spec (TAtom "fputs") (fputs_spec (glibc_program := print_program))
    (FputsIn (ho_vb o) (sym_ptr ge s) DfracDiscarded [] (ho_out o) 1 (ho_eb o)) _ _ _
    (fun x => (file_idle (ho_vb o) (ow_self w0) (ho_err o) 2 ∗ (FB.stream_life (ho_in o) ∗ FB.exit_stream false (ho_in o)) ∗
      io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗ tcb_cleanup_inv (ow_self w0) ∗ error_count ge) ∗ P ∗
      ⌜fi_fp x = ho_out o /\ fi_eb x = ho_eb o /\ fi_vb x = ho_vb o /\ fi_fd x = 1⌝)%I
    Hfputs eq_refl).
  - iIntros "(#Hro & (Hout & Hse & Hin & Hio & Htcb & He & Hec) & HP & _)".
    iDestruct (hello_lit_ro _ _ _ Hl with "Hro") as (bs) "#Hs".
    iExists (FputsIn (ho_vb o) (sym_ptr ge s) DfracDiscarded bs (ho_out o) 1 (ho_eb o)).
    iSplit; [done|].
    cbn [fs_pre fputs_spec fi_vb fi_p fi_dq fi_s fi_fp fi_fd fi_eb print_program program_of program_world program_ge].
    iSplitR "Hse Hin Hio Htcb Hec HP".
    + iSplit; [iPureIntro; split; [exact Herr | exact Hfd1]|].
      iSplitR; [iExact "Hs"|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "He"; [iExact "He"|].
      iSplitR; [iPoseProof "Hro" as "(Hv & Hsg & _)"; iExists _, _, _; iFrame "Hv Hsg"|].
      iApply (malloc_ro_of_hello_ro with "Hro"); exact Hk.
    + iFrame. done.
  - intros [vb p dq bs fp fd eb] r. cbn [fs_post fputs_spec fi_vb fi_p fi_dq fi_s fi_fp fi_fd fi_eb].
    iIntros "[(%n & [-> %Hn] & _ & Hout & He) ((Hse & Hin & Hio & Htcb & Hec) & HP & %Hx)]".
    destruct Hx as (-> & -> & -> & ->).
    iExists n. iSplit; [iPureIntro; split; [reflexivity | destruct Hn as [-> | ->]; lia]|]. iFrame.
Qed.

(** The formatter's grammar accepts a list of arguments that fits the
    directives of a format. *)
Ltac narrow_args_by :=
  repeat first
    [ apply args_end
    | apply args_literal; [reflexivity|]
    | apply args_percent
    | eapply args_conversion; [constructor|] ].

(** Stdout and stderr are both in [hello_stdio], so a call can borrow
    either one while the rest of [hello_stdio] waits. *)
Lemma stdio_out_split :
  hello_stdio w0 ge o ⊣⊢ file_idle (ho_vb o) (ow_self w0) (ho_out o) 1 ∗
    (file_idle (ho_vb o) (ow_self w0) (ho_err o) 2 ∗ (FB.stream_life (ho_in o) ∗ FB.exit_stream false (ho_in o)) ∗
     io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗ tcb_cleanup_inv (ow_self w0) ∗ errno_any (ho_eb o) ∗ error_count ge).
Proof using Type. reflexivity. Qed.

Lemma stdio_err_split :
  hello_stdio w0 ge o ⊣⊢ file_idle (ho_vb o) (ow_self w0) (ho_err o) 2 ∗
    (file_idle (ho_vb o) (ow_self w0) (ho_out o) 1 ∗ (FB.stream_life (ho_in o) ∗ FB.exit_stream false (ho_in o)) ∗
     io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗ tcb_cleanup_inv (ow_self w0) ∗ errno_any (ho_eb o) ∗ error_count ge).
Proof using Type.
  rewrite /hello_stdio. iSplit; iIntros "(A & B & C)"; iFrame.
Qed.

(** A call `c: fprintf (fp, fmt, q)` with one of main's formats keeps
    the streams and any state P, when fp is stdout or stderr and the
    argument q fits the format. *)
Lemma fprintf_site_hello (P R : iProp Σ) fp fd n bs ds q :
  (hello_stdio w0 ge o ⊣⊢ file_idle (ho_vb o) (ow_self w0) fp fd ∗ R) -> In fd (ow_fds w0) ->
  (R ⊢ ∃ R', errno_any (ho_eb o) ∗ R' ∗ (errno_any (ho_eb o) -∗ R' -∗ R)) ->
  In (n, bs) print_fmts -> parse_narrow bs = Some ds -> narrow_args ds [WPtr q] ->
  fn_triple w0 ge (TAtom "fprintf") [WPtr fp; WPtr (sym_ptr ge n); WPtr q]
    (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P ∗ [∗ list] x ∈ skipn 2 [WPtr fp; WPtr (sym_ptr ge n); WPtr q], str_arg x)%I
    (ret_int (hello_stdio w0 ge o ∗ P))%I.
Proof using Type*.
  intros Hsplit Hfd HR Hin Hp Ha.
  set (x := PfIn (ho_vb o) fp fd (sym_ptr ge n) DfracDiscarded bs ds [WPtr q] [] (ho_eb o)).
  apply (triple_of_spec (TAtom "fprintf") (fprintf_spec (glibc_program := print_program)) x _ _ _
    (fun y => ⌜y = x⌝ ∗ (∃ R', R' ∗ (errno_any (ho_eb o) -∗ R' -∗ R)) ∗ P)%I Hfprintf eq_refl).
  - iIntros "(#Hro & Hio & HP & Hq)". rewrite Hsplit. iDestruct "Hio" as "[Hf HR]".
    iDestruct (HR with "HR") as (R') "(He & HR' & Hback)".
    iExists x. iSplit; [done|].
    cbn [fs_pre fprintf_spec]. unfold pf_fits, pf_pre.
    cbn [x pf_vb pf_fp pf_fd pf_fmt pf_dq pf_bytes pf_ds pf_ys pf_rest pf_eb print_program program_of program_world program_ge].
    iSplitR "HR' Hback HP".
    + iSplit; [iPureIntro; split_and!; [exact Hp | exact (narrow_fits_all _ _ Ha) | reflexivity | exact Herr | exact Hfd |
        exact (hk_errno_at _ _ Hk)]|].
      iPoseProof "Hro" as "(Hvt & Hsg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _)".
      iSplitL "Hf"; [iExact "Hf"|]. iSplitR; [iApply (print_fmt _ _ Hin with "Hro")|].
      iSplitL "Hq"; [iExact "Hq"|]. iSplitL "He"; [iExact "He"|].
      iSplitR; [iExact "Hpr"|]. iSplitR; [iExists _, _, _; iFrame "Hvt Hsg"|].
      iApply (malloc_ro_of_hello_ro with "Hro"); exact Hk.
    + iSplit; [done|]. iSplitR "HP"; [iExists R'; iFrame|iExact "HP"].
  - intros y r. iIntros "[Hpost (-> & HF)]". iRevert "Hpost HF". iIntros "Hpost HF".
    cbn [fs_post fprintf_spec]. unfold pf_post.
    cbn [x pf_vb pf_fp pf_fd pf_fmt pf_dq pf_bytes pf_ds pf_ys pf_rest pf_eb print_program program_of program_world program_ge].
    iDestruct "Hpost" as "(%k & [-> %Hk'] & Hf & _ & He)". iDestruct "HF" as "((%R' & HR' & Hback) & HP)".
    iExists k. iSplit; [done|]. rewrite Hsplit. iFrame "HP Hf". iApply ("Hback" with "He HR'").
Qed.

(** The rest of [hello_stdio] after either stream holds errno, which
    the formatter borrows. *)
Lemma stdio_rest_errno (A B C D E : iProp Σ) :
  A ∗ B ∗ C ∗ D ∗ errno_any (ho_eb o) ∗ E ⊢
  ∃ R', errno_any (ho_eb o) ∗ R' ∗ (errno_any (ho_eb o) -∗ R' -∗ A ∗ B ∗ C ∗ D ∗ errno_any (ho_eb o) ∗ E).
Proof using Type.
  iIntros "(A & B & C & D & He & E)". iExists (A ∗ B ∗ C ∗ D ∗ E)%I. iFrame "He".
  iSplitL "A B C D E"; [iFrame|]. iIntros "He (A & B & C & D & E)". iFrame.
Qed.

(** The parsed directives of a format, or none. *)
Local Definition parsed (bs : list Z) : list narrow_directive :=
  match parse_narrow bs with Some ds => ds | None => [] end.

(** Each print site of main keeps the streams and any state P. The
    help strings go through `c: fputs`, and the three formats through
    `c: fprintf`. *)
Lemma print_hello (P : iProp Σ) g xs :
  print_site ge o g xs ->
  fn_triple w0 ge g xs (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P ∗ [∗ list] x ∈ skipn 2 xs, str_arg x)%I
    (ret_int (hello_stdio w0 ge o ∗ P))%I.
Proof using Type*.
  intros [(-> & s & Hin & ->) | [(-> & q & ->) | [(-> & ->) | (-> & q & ->)]]].
  - exact (fputs_site_hello P s Hin).
  - apply (fprintf_site_hello P _ _ 1 "hello#str.54" (snd (nth 1 print_fmts ("", [])))
      (parsed (snd (nth 1 print_fmts ("", []))))
      q stdio_out_split Hfd1 (stdio_rest_errno _ _ _ _ _));
      [cbn; tauto | vm_compute; reflexivity | vm_compute; narrow_args_by].
  - apply (fprintf_site_hello P _ _ 1 "hello#str.62" (snd (nth 2 print_fmts ("", [])))
      (parsed (snd (nth 2 print_fmts ("", []))))
      _ stdio_out_split Hfd1 (stdio_rest_errno _ _ _ _ _));
      [cbn; tauto | vm_compute; reflexivity | vm_compute; narrow_args_by].
  - apply (fprintf_site_hello P _ _ 2 "hello#str.79" (snd (nth 3 print_fmts ("", [])))
      (parsed (snd (nth 3 print_fmts ("", []))))
      q stdio_err_split Hfd2 (stdio_rest_errno _ _ _ _ _));
      [cbn; tauto | vm_compute; reflexivity | vm_compute; narrow_args_by].
Qed.

End sites.

(** When Hello runs with `--version`, it prints its version text with
    one call of `c: version_etc`. The proof of main needs that call to
    keep the standard streams that main holds. This module states the
    call in that form and checks that the Hello image runs the code
    that the other version proofs read. *)

From Glibc Require Import GlibcProgram GlibcTactics GlibcSpec LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry WordString FileInv FileIdle LibioLogic LibioFputsSpec
  PrintfSpec NarrowFormat NarrowArgs AllocRo VaArgRound FxprintfStream HelloVersionLits HelloGlibcDebts
  HelloGlibcLibsT HelloGlibcMainSteps HelloEmitBug CodePrelude HelloVersionEtc HelloVersionEtcVa
  PrintfWrap FprintfCode PrintfCode HelloImageLayout LibioFflushSpec LibioFflushIdle HelloErrorOperandCall
  HelloPrintSites.
From Glibc Require LibioCleanupExit.
From Glibc Require Import SysCode LibioReadCode LibioDoWriteCode FileSyncCode FflushCode.
From Glibc Require Import HelloImageModule HelloImageLoad HelloImageDec01.
From Glibc Require HelloGlibcDebts LibioLogic.
From Glibc Require Import Fix.
Import ListNotations.
Import HelloGlibcDebts HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG
  HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.

(** The Hello image defines the three functions as the code that the
    proofs read. *)
Lemma version_link_image fr : version_link (mkGenv hello_image_module img_globals fr).
Proof. constructor; vm_compute; reflexivity. Qed.

Import VeVL.

Section call.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
(** Every lemma here holds for any program that places Hello's objects
    and links the version functions to their code. *)
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hy : hello_layout ge o) (Hk : hello_link ge o)
  (Hl : emit_link ge) (Hv : version_link ge).

Local Definition call_program : GlibcProgram Σ := program_of w0 glibc_os_registry ge.

(** The version text goes to stdout, and a failed write sets errno.
    So the world must have descriptor 1 open and must register Hello's
    errno object. The two print calls are trusted to keep their
    contracts here, and other modules prove those contracts. *)
Context (Herr : ow_errno w0 = Some (mkPtr (ho_eb o) (Obj (ho_eb o)))) (Hfd : In 1 (ow_fds w0)).
Context `{Hfputs : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fputs") (fputs_spec (glibc_program := call_program))}.
Context `{Hfprintf : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "fprintf") (fprintf_spec (glibc_program := call_program))}.
Context `{Hprintf : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "printf") (printf_spec (glibc_program := call_program))}.

(** The call keeps the standard streams and any state P of the
    caller. The call uses only stdout and errno from [hello_stdio], and
    it reads Hello's three strings through [hello_ro]. *)
Lemma version_etc_hello (P : iProp Σ) q1 q2 q3 q4 :
  fn_triple w0 ge (TAtom "version_etc")
    [WPtr (ho_out o); WPtr (sym_ptr ge "hello#str.70"); WPtr (sym_ptr ge "hello#str.63");
     WPtr (sym_ptr ge "hello#str.71"); WPtr q1; WPtr q2; WPtr q3; WPtr q4; WPtr null]
    (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P ∗ str_ro q1 ∗ str_ro q2 ∗ str_ro q3 ∗ str_ro q4)%I
    (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio w0 ge o ∗ P)%I.
Proof using Type*.
  destruct (version_etc_triple w0 ge o Hk Hl Hv Herr Hfd (sym_ptr ge "hello#str.70") (sym_ptr ge "hello#str.63")
    (sym_ptr ge "hello#str.71") q1 q2 q3 q4
    ((file_idle (ho_vb o) (ow_self w0) (ho_err o) 2 ∗ (HelloGlibcDebts.FB.stream_life (ho_in o) ∗ HelloGlibcDebts.FB.exit_stream false (ho_in o)) ∗
      io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗ tcb_cleanup_inv (ow_self w0) ∗ error_count ge) ∗ P)%I)
    as (f & Hg & Hfr & Ht).
  exists f. split; [exact Hg|]. split; [exact Hfr|]. intros fr Φ Hf.
  iIntros "(#Hro & (Hout & Hse & Hin & Hio & Htcb & He & Hec) & HP & #Q1 & #Q2 & #Q3 & #Q4) HK".
  iApply (Ht fr Φ Hf with "[Hout Hse Hin Hio Htcb He Hec HP]").
  - iSplitR; [iExact "Hro"|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "He"; [iExact "He"|].
    iSplitR; [iApply (hello_lit_ro with "Hro"); cbn; tauto|].
    iSplitR; [iApply (hello_lit_ro with "Hro"); cbn; tauto|].
    iSplitR; [iApply (hello_lit_ro with "Hro"); cbn; tauto|].
    iSplitR; [iExact "Q1"|]. iSplitR; [iExact "Q2"|]. iSplitR; [iExact "Q3"|]. iSplitR; [iExact "Q4"|].
    iSplitR "HP"; [|iExact "HP"]. iSplitL "Hse"; [iExact "Hse"|]. iSplitL "Hin"; [iExact "Hin"|].
    iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Htcb"; [iExact "Htcb" | iExact "Hec"].
  - iIntros (r) "(-> & Hout & He & (Hse & Hin & Hio & Htcb & Hec) & HP)". iApply "HK".
    iSplitR; [done|]. iSplitR "HP"; [|iExact "HP"]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "Hse"; [iExact "Hse"|].
    iSplitL "Hin"; [iExact "Hin"|]. iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Htcb"; [iExact "Htcb"|]. iSplitL "He"; [iExact "He" | iExact "Hec"].
Qed.

(** The bug-report address is printed in the same way. *)
Lemma emit_bug_hello (P : iProp Σ) :
  fn_triple w0 ge (TAtom "emit_bug_reporting_address") [] (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P)%I
    (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio w0 ge o ∗ P)%I.
Proof using Type*.
  destruct (emit_bug_triple w0 ge o Hy Hk Hl Herr Hfd
    ((file_idle (ho_vb o) (ow_self w0) (ho_err o) 2 ∗
      (HelloGlibcDebts.FB.stream_life (ho_in o) ∗ HelloGlibcDebts.FB.exit_stream false (ho_in o)) ∗
      io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗ tcb_cleanup_inv (ow_self w0) ∗ error_count ge) ∗ P)%I)
    as (f & Hg & Hfr & Ht).
  exists f. split; [exact Hg|]. split; [exact Hfr|]. intros fr Φ Hf.
  iIntros "(#Hro & (Hout & Hse & Hin & Hio & Htcb & He & Hec) & HP) HK".
  iApply (Ht fr Φ Hf with "[Hout Hse Hin Hio Htcb He Hec HP]").
  - iSplitR; [iExact "Hro"|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "He"; [iExact "He"|].
    iSplitR "HP"; [|iExact "HP"]. iSplitL "Hse"; [iExact "Hse"|]. iSplitL "Hin"; [iExact "Hin"|].
    iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Htcb"; [iExact "Htcb" | iExact "Hec"].
  - iIntros (r) "(-> & Hout & He & (Hse & Hin & Hio & Htcb & Hec) & HP)". iApply "HK".
    iSplitR; [done|]. iSplitR "HP"; [|iExact "HP"]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "Hse"; [iExact "Hse"|].
    iSplitL "Hin"; [iExact "Hin"|]. iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Htcb"; [iExact "Htcb"|]. iSplitL "He"; [iExact "He" | iExact "Hec"].
Qed.

(** Hello's main prints with several calls, and none of them may
    disturb what the other callees keep for later. This lemma collects
    the two proofs above and the caller's proofs of the error report
    and the print sites into one record for that kept state P. *)
Lemma hello_prints_of (P : iProp Σ) :
  (forall q, fn_triple w0 ge (TAtom "error")
     [WInt 0; WInt 0; WPtr (sym_ptr ge "hello#str.77"); WPtr (sym_ptr ge "hello#str.78"); WPtr q]
     (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P ∗ names o ∗ str_arg (WPtr q))%I
     (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio w0 ge o ∗ P ∗ names o)%I) ->
  (forall g xs, print_site ge o g xs ->
     fn_triple w0 ge g xs (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P ∗ [∗ list] x ∈ skipn 2 xs, str_arg x)%I
       (ret_int (hello_stdio w0 ge o ∗ P))%I) ->
  HelloPrints w0 ge o P.
Proof using Type*.
  intros Herr_op Hprint.
  constructor; [exact (version_etc_hello P) | exact (emit_bug_hello P) | exact Herr_op | exact Hprint].
Qed.

End call.

(** The real Hello image runs the three calls safely when glibc's
    formatter and `c: fputs` keep their contracts. The image's
    `c: fprintf` and `c: printf` are glibc's own wrappers, and they are
    proved from the formatter's contract. The image's `c: fflush` and
    the functions it calls are glibc's own, so its contract is proved
    here. The error report also needs stderr open and a thread with an
    identity. *)
Lemma hello_prints_image `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} w0 fr (P : iProp Σ) :
  hello_layout (mkGenv hello_image_module img_globals fr) hello_image_objs ->
  hello_link (mkGenv hello_image_module img_globals fr) hello_image_objs ->
  ow_errno w0 = Some (mkPtr (ho_eb hello_image_objs) (Obj (ho_eb hello_image_objs))) -> In 1 (ow_fds w0) ->
  In 2 (ow_fds w0) -> hello_os_layout w0 hello_image_objs ->
  HasSpec glibc_os_registry (os_wi w0) (mkGenv hello_image_module img_globals fr) (TAtom "__vfprintf_internal")
    (vfprintf_spec (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module img_globals fr))) ->
  HasSpec glibc_os_registry (os_wi w0) (mkGenv hello_image_module img_globals fr) (TAtom "fputs")
    (fputs_spec (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module img_globals fr))) ->
  HelloPrints w0 (mkGenv hello_image_module img_globals fr) hello_image_objs P.
Proof.
  intros Hy Hk Herr Hfd Hfd2 Hos Hvf Hfputs.
  set (ge := mkGenv hello_image_module img_globals fr) in *.
  assert (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync)
    by (exists (img_addr "_IO_new_file_sync"); split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; congruence]]).
  assert (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
    by (exists (img_addr "_IO_new_file_write"); split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; congruence]]).
  assert (Dw : Defines ge "__GI___write" glibc___libc_write) by (unfold Defines; vm_compute; reflexivity).
  assert (Dd : Defines ge "_IO_new_do_write" glibc__IO_new_do_write) by (unfold Defines; vm_compute; reflexivity).
  assert (Dff : Defines ge "__GI__IO_fflush" glibc__IO_fflush) by (unfold Defines; vm_compute; reflexivity).
  assert (Hself : ptr_addr (ow_self w0) <> 0) by (destruct Hos as [? _]; lia).
  pose proof (fflush_has_spec (glibc_program := program_of w0 glibc_os_registry ge)
    LibioCleanupExit.holds_os_glibc (hk_sys _ _ Hk) Hsync Hfw Hself) as Hff.
  assert (Df : Defines (mkGenv hello_image_module img_globals fr) "fprintf" glibc_fprintf)
    by (unfold Defines; vm_compute; reflexivity).
  assert (Dp : Defines (mkGenv hello_image_module img_globals fr) "printf" glibc_printf)
    by (unfold Defines; vm_compute; reflexivity).
  pose proof (fprintf_has_spec (glibc_program := program_of w0 glibc_os_registry _) "fprintf") as Hfp.
  pose proof (printf_has_spec (glibc_program := program_of w0 glibc_os_registry _) "printf") as Hpp.
  exact (hello_prints_of w0 _ hello_image_objs Hy Hk (emit_link_image fr) (version_link_image fr) Herr Hfd P
    (error_operand_hello w0 _ hello_image_objs Hy Hk (hello_error_link_image fr) Hos Herr Hfd Hfd2 P)
    (print_hello w0 _ hello_image_objs Hy Hk Herr Hfd Hfd2 P)).
Qed.

(** GNU Hello remembers a stream's pending bytes and error flag before
    closing it. This proof closes stderr when its internal buffer is empty.
    It follows the queries, fclose and both errno branches in the compiled
    code. The remaining streams stay available to the caller.
    The proof does not cover pending output or the diagnostics in close_stdout. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic HelloClose.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  SysCode SysWrappers LibioReadCode LibioDoWriteCode LibioCloseItCode LibioGenCode LibioUnlinkCode
  LibioFcloseCode FileInv LibioLogic LibioCloseSteps LibioRead LibioPendingShort LibioFcloseShort
  HelloCloseStream HelloCloseErrno LeavesLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps
  LibioFcloseTail.
Open Scope Z_scope.

Section close.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
#[local] Hint Opaque live pcell int_cell icell bytes errno_any lock_state io_list_inv vtables_ro single_ro
  tcb_cleanup_inv stream_life : typeclass_instances.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__fpending" glibc___fpending}
  `{!Defines ge "ferror" glibc__IO_ferror}
  `{!Defines ge "fclose" glibc__IO_new_fclose}
  `{!Defines ge "__GI___close_nocancel" glibc___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  `{!Defines ge "__GI__IO_setb" glibc__IO_setb}
  `{!Defines ge "_IO_new_do_write" glibc__IO_new_do_write}
  `{!Defines ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers}
  `{!Defines ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer}
  `{!Defines ge "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore}
  `{!Defines ge "__GI__IO_un_link" glibc__IO_un_link}
  `{!Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish)
  `{!Defines ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink}
  `{!Defines ge "__errno_location" errno_location_fn}.

(** Both return outcomes preserve cleanup, errno, caller resources and the
    remaining list with its stream lifetimes. The query needs NEED_LOCK
    clear; fclose takes and releases the initially free stream lock.
    Neither a successful close nor a clear error flag is assumed. *)
Lemma wp_hello_close_stream_stderr_short_empty pre post fb freg fl f2 fd off rp re rb we be eb vb vreg
    lb lbreg sb sreg fcp pin pout md (E : iProp Σ) Φ :
  let fp := mkPtr fb (Obj fb) in
  let buf := mkPtr (fb + off_shortbuf) (Obj fb) in
  let Q := (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
    ([∗ list] g ∈ pre ++ post, stream_life g) ∗ errno_any eb ∗ E)%I in
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout -> ptr_addr pout <> fb ->
  0 <= ptr_addr pout < 2 ^ 64 ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= f2 < 2 ^ 32 -> Z.land f2 32 = 0 -> Z.land f2 io_need_lock = 0 -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_no_writes = 0 -> Z.land fl io_currently_putting <> 0 ->
  Z.land fl io_user_buf <> 0 -> has fl io_user_lock = false ->
  has fl io_linked = true -> has fl io_is_filebuf = true ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> 0 < lb -> md = 0 ∨ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_offset off -∗ errno_any eb -∗
  pcell fb 8 rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb 32 buf -∗ pcell fb 40 buf -∗
  pcell fb 48 we -∗ pcell fb off_buf_base buf -∗ pcell fb off_buf_end be -∗
  int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗ E -∗
  (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ Q -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (hello_close_stream_frame fp) : gexpr) {{ Φ }}.
Proof.
  intros fp buf Q Hglobal Hgerr Hgout Hout Houtr Hgin Hin Hinr Hcleanup Hfcr Hfb Hfal Hfend Hfreg
    Hf2r Hf232 Hnl Hfdr Hfl Hnw Hcp Hub Hul Hlnk Hfb8 He Hlb Hmd. subst fp buf.
  iIntros "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Hoff Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hmode Hvtp
    H80 H96 Hlp Hlk Hio Hlives HE HK".
  unfold file_size in Hfend. unfold hello_close_stream_frame. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_glibc___fpending_short_empty with "Hl Hmode Hwp Hwb");
    [reflexivity | close_side | close_side | close_side | close_side | exact Hmd |].
  iNext. iIntros "Hl Hmode Hwp Hwb". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (LibioRead.wp_glibc__IO_ferror with "Hl Hfl Hfl2");
    [reflexivity | close_side | close_side | close_side | close_side | exact Hnl |].
  iNext. iIntros "Hl Hfl Hfl2". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_glibc__IO_new_fclose_stderr_short_empty Hreg Hext Hfc Hff
    with "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Hoff Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hmode Hvtp
      H80 H96 Hlp Hlk Hio Hlives HE"); try close_side; try exact Hmd.
  iNext. iIntros (k Hk) "Htcb _ _ _ _ _ Herr H8 H16 H24 H32 H40 H48 Hbb Hbe Hmode Hvtp
    H80 H96 Hlp Hlk Hio Hlives Hlinks HE".
  iClear "H8 H16 H24 H32 H40 H48 Hbb Hbe Hmode Hvtp H80 H96 Hlp Hlk Hlinks". resume.
  repeat first [step | branch_cases].
  all: lazymatch goal with
  | |- context [Exec (TAtom "L27") _ _] =>
      iApply (wp_close_stream_L27 eb He Hglobal _ _
        (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
         ([∗ list] g ∈ pre ++ post, stream_life g) ∗ E)%I
        with "Herr [Htcb Hio Hlives HE] [HK]"); [reflexivity|iFrame|];
      iIntros (r Hr) "Herr (Htcb & Hio & Hlives & HE)";
      iApply ("HK" with "[%] [$Htcb $Hio $Hlives $Herr $HE]"); exact Hr
  | |- context [Exec (TAtom "L38") _ _] =>
      iApply (wp_close_stream_L38 eb He Hglobal _
        (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
         ([∗ list] g ∈ pre ++ post, stream_life g) ∗ E)%I
        with "Herr [Htcb Hio Hlives HE] [HK]"); [iFrame|];
      iIntros "Herr (Htcb & Hio & Hlives & HE)";
      iApply ("HK" with "[%] [$Htcb $Hio $Hlives $Herr $HE]"); auto
  | |- _ => iApply wp_ret; [reflexivity | reflexivity |]; iNext;
      iApply ("HK" with "[%] [$Htcb $Hio $Hlives $Herr $HE]"); auto
  end.
Qed.
End close.

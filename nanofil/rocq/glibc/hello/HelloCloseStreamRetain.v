(** Hello may flush stdout again while reporting a close error. This rule
    keeps the closed FILE memory returned by fclose instead of discarding
    it. It preserves the same success and failure decisions as close_stream;
    the two errno blocks receive the retained memory with the other state. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloClose.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  SysCode LibioReadCode LibioDoWriteCode LibioGenCode LibioUnlinkCode LibioCloseItCode LibioFcloseCode
  FileInv LibioLogic SysWrappers AllocLogic LibioCloseSteps LibioRead HiAtexitFclose
  HelloClosedStdout.
From Glibc Require LibioFcloseTail.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps LibioFcloseTail.
Open Scope Z_scope.

(** Calling the checked close_stream body binds its stream argument. *)
Definition hello_close_stream_frame p :=
  mkFrame close_stream_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).

Section close.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
#[local] Hint Opaque live pcell int_cell icell bytes errno_any lock_state io_list_inv vtables_ro single_ro
  tcb_cleanup_inv stream_life closed_stdout : typeclass_instances.

(** The remaining errno blocks receive the same retained state as ordinary
    returns. Their callers must handle both the errno read and reset. *)
Definition close_stream_errno_paths (Q : iProp Σ) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ e l, ⌜l = "L27"%string ∨ l = "L38"%string⌝ -∗
    ⌜∃ k, lookup (TAtom "v14") e = Some (WInt k)⌝ -∗ Q -∗
    WP (ERun (mkFrame close_stream_fn e [] None
      (Exec (TAtom l) (b_insts (cs_block l)) (b_jump (cs_block l)))) : gexpr) {{ Φ }}.

Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__fpending" glibc___fpending}
  `{!Defines ge "ferror" glibc__IO_ferror}
  `{!Defines ge "fclose" glibc__IO_new_fclose}
  `{!Defines ge "__GI___write" glibc___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  `{!Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None)
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
  `{!Defines ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink}.

(** The remaining list, its stream lifetimes, errno and thread cleanup
    survive closing stdout. The caller may frame the stdin and stderr
    fields in E. No premise requires a successful write or close. *)
Lemma wp_hello_close_stream_stdout_retained pre post fb freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg
    lb lbreg sb sreg fcp pin md (E : iProp Σ) Φ :
  let n := Z.of_nat (length xs) in
  let fp := mkPtr fb (Obj fb) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  let Q := (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
    ([∗ list] g ∈ pre ++ post, stream_life g) ∗ errno_any eb ∗ closed_stdout fb freg vb lb lbreg ∗ E)%I in
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb -> 0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> Z.land f2 32 = 0 -> Z.land f2 io_need_lock = 0 -> 0 <= f2 < 2 ^ 32 ->
  In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 -> Z.land fl io_no_writes = 0 ->
  Z.land fl io_currently_putting <> 0 -> Z.land fl io_user_buf = 0 -> has fl io_user_lock = false ->
  has fl io_linked = true -> has fl io_is_filebuf = true ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> r_kind breg = Heap ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 < lb ->
  md = 0 ∨ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 72 null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗ E -∗
  (close_stream_errno_paths Q Φ ∧ (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ Q -∗ Φ (Ret (WInt r)))) -∗
  WP (ERun (hello_close_stream_frame fp) : gexpr) {{ Φ }}.
Proof.
  intros n fp wb base Q Hgout Hgin Hin Hinr Hfcg Hfcr Hfb Hfal Hfend Hfreg Hf22 Hf232 Hnl Hf2r Hfd
    Hfdr Hfl Happ Hnw Hcp Hub Hul Hlnk Hfb8 He Hbk Hb Hi Hbend Hbreg Hy Hbe Hbec Hlb Hmd.
  iIntros "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol
    Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives HE HK".
  subst fp wb base. unfold file_size in Hfend.
  unfold hello_close_stream_frame. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (LibioRead.wp_glibc___fpending _ _ _ md (mkPtr (bb + i + n) (Obj bb)) (mkPtr (bb + i) (Obj bb)) breg
    with "Hl Hmode Hwp Hwb Hbl");
    [reflexivity | close_side | close_side | close_side | close_side | exact Hmd | reflexivity | cbn; lia | cbn; lia |].
  iNext. iIntros "Hl Hmode Hwp Hwb Hbl". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (LibioRead.wp_glibc__IO_ferror with "Hl Hfl Hfl2");
    [reflexivity | close_side | close_side | close_side | close_side | exact Hnl |].
  iNext. iIntros "Hl Hfl Hfl2". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (hi_fclose_stdout Hreg Hext Hfw Hfh Hzf Hzg Hfc Hff _ pre post fb freg fl f2 fd tw off bb breg i xs
    rp rb we be eb vb vreg lb lbreg sb sreg fcp pin md
    with "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase
      Hbend Hcol Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives").
  all: lazymatch goal with
  | |- environments.envs_entails _ _ => idtac
  | |- _ => first [assumption | reflexivity | lia]
  end.
  iNext. iIntros (r fl' k tw' [Hpost Hk])
    "Htcb Hl Hclosed _ _ _ Hoff Herr H8 H16 H24 H32 H40 H48 Hbb Hbe Hcol Hmd Hvtp H72 H80 H96 Hlp Hlk Hio Hlives Hchain".
  iEval (rewrite stdout_closed_flags) in "Hclosed".
  iAssert (closed_stdout fb freg vb lb lbreg) with "[Hl Hclosed H8 H16 H32 H40 Hoff Hvtp Hlp Hlk]" as "Hclosed".
  { unfold closed_stdout, closed_stdout_fields. iFrame. }
  iClear "H24 H48 Hbb Hbe Hcol Hmd H72 H80 H96 Hchain".
  resume.
  iAssert Q with "[$Htcb $Hio $Hlives $Herr $Hclosed $HE]" as "HQ".
  repeat first [step | branch_cases].
  all: lazymatch goal with
  | |- context [Call _ (Global (TAtom "__errno_location")) _] =>
    iDestruct "HK" as "[HK _]"; iApply ("HK" with "[%] [%] HQ");
      [auto | eexists; reflexivity]
  | |- _ => iApply wp_ret; [reflexivity | reflexivity |]; iNext;
    iDestruct "HK" as "[_ HK]"; iApply ("HK" with "[%] HQ"); auto
  end.
Qed.
End close.

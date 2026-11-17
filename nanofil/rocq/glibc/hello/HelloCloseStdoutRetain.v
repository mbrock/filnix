(** Hello keeps the closed stdout object available while deciding whether
    to report an error or close stderr. This rule carries the memory returned
    by fclose to either result. The diagnostic remains an exact continuation
    at L0; its caller may lend the retained object to error reporting. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic HelloClose.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  SysCode SysWrappers LibioReadCode LibioDoWriteCode LibioCloseItCode LibioGenCode LibioUnlinkCode
  LibioFcloseCode FileInv LibioLogic LibioCloseSteps HelloCloseStream HelloCloseErrno HelloCloseShort
  HelloCloseDispatch HelloCloseStdout HelloCloseRetain HelloClosedStdout LeavesLogic AllocLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps
  LibioFcloseTail.
Open Scope Z_scope.

Section close.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
#[local] Hint Opaque live pcell int_cell icell bytes errno_any lock_state io_list_inv vtables_ro single_ro
  tcb_cleanup_inv stream_life closed_stdout : typeclass_instances.

#[local] Hint Opaque stderr_short_fields : typeclass_instances.

Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__fpending" glibc___fpending}
  `{!Defines ge "ferror" glibc__IO_ferror}
  `{!Defines ge "fclose" glibc__IO_new_fclose}
  `{!Defines ge "__GI___write" glibc___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  `{!Defines ge "free" free_fn} (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None)
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
  `{!Defines ge "__errno_location" errno_location_fn}
  `{!Defines ge "close_stream" close_stream_fn}
  `{!Defines ge "_exit" glibc__exit}.

(** The diagnostic must still be able to use stderr after stdout is closed.
    The caller supplies its proof starting at L0, with stderr's fields,
    its lifetime, the remaining list, errno and the global cells.
    The other path closes stderr and returns the caller's remaining streams. *)
Lemma wp_hello_close_stdout_to_diagnostic_retained rest fb freg fl f2 fd tw off bb breg i xs rp rr we be eb vb vreg
    lb lbreg sb sreg fcp pin md rb ob oreg sc screg xc xcreg status ib ireg flag (E : iProp Σ) Φ :
  let n := Z.of_nat (length xs) in
  let fp := mkPtr fb (Obj fb) in
  let ep := mkPtr rb (Obj rb) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let cells := (live ob oreg ∗ pcell ob 0 fp ∗ live sc screg ∗ pcell sc 0 ep ∗
    live xc xcreg ∗ int_cell xc 0 status ∗ live ib ireg ∗ bytes ib 0 [flag])%I in
  let state := (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (ep :: rest) ∗
    ([∗ list] g ∈ ep :: rest, stream_life g) ∗ errno_any eb ∗ cells ∗ stderr_short_fields rb vb ∗
    closed_stdout fb freg vb lb lbreg ∗ E)%I in
  let done := (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge rest ∗
    ([∗ list] g ∈ rest, stream_life g) ∗ errno_any eb ∗ cells ∗ closed_stdout fb freg vb lb lbreg ∗ E)%I in
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sc (Obj sc)) ->
  0 < sc -> sc mod 8 = 0 -> sc + 8 <= r_end screg -> r_end screg <= 2 ^ 63 ->
  lookup (TAtom "exit_failure") (ge_globals ge) = Some (mkPtr xc (Obj xc)) ->
  0 < xc -> xc + 4 <= r_end xcreg -> r_end xcreg <= 2 ^ 63 ->
  lookup (TAtom "closeout#ignore_EPIPE") (ge_globals ge) = Some (mkPtr ib (Obj ib)) ->
  0 < ib -> ib + 1 <= r_end ireg -> r_end ireg <= 2 ^ 63 -> 0 <= flag < 256 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some ep -> fb <> rb ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin ->
  ptr_addr pin <> fb -> ptr_addr pin <> rb -> 0 <= ptr_addr pin < 2 ^ 64 ->
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
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rr -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 72 null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (ep :: fp :: rest) -∗ ([∗ list] g ∈ ep :: rest, stream_life g) -∗
  cells -∗ stderr_short_fields rb vb -∗ E -∗
  ((∀ e, state -∗ WP (ERun (mkFrame close_stdout_fn e [] None
      (Enter (TAtom "L0") (Some (TAtom "L8")))) : gexpr) {{ Φ }}) ∧ (done -∗ Φ RetVoid)) -∗
  WP (ERun (mkFrame close_stdout_fn [] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros n fp ep wb cells state done Hgstdout Hob Hoba Hobe Hobr Hgstderr Hsc Hsca Hsce Hscr
    Hgexit Hxc Hxce Hxcr Hgignore Hib Hibe Hibr Hflag Hglobal Hgout Hgerr Hdistinct Hgin Hin Hinerr Hinr
    Hcleanup Hfcr Hfb Hfal Hfend Hfreg Hf22 Hf232 Hnl Hf2r Hfd Hfdr Hfl Happ Hnw Hcp Hub Hul Hlnk Hfb8
    He Hbk Hb Hi Hbend Hbreg Hy Hbe Hbec Hlb Hmd. subst fp ep wb.
  iIntros "#Hvt #Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrr Hwb Hwp Hwe Hbase Hbend
    Hcol Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives Hcells Hrs HE HK".
  iDestruct "Hcells" as "(Hol & Hop & Hsl & Hsp & Hxl & Hstatus & Hil & Hib)".
  unfold file_size in Hfend.
  iApply (wp_live_fit1 with "Hol"). iIntros ([Ho0 Ho48]) "Hol".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hol". load "Hol" "Hop" "Hl".
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_hello_close_stream_stdout_full_retained Hreg Hext Hfw Hfh Hzf Hzg Hfc Hff
    [mkPtr rb (Obj rb)] rest fb freg fl f2 fd tw off bb breg i xs rp rr we be eb vb vreg
    lb lbreg sb sreg fcp pin md (cells ∗ stderr_short_fields rb vb ∗ E)%I
    with "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrr Hwb Hwp Hwe Hbase Hbend
      Hcol Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives [Hol Hop Hsl Hsp Hxl Hstatus Hil Hib Hrs HE]"); try assumption.
  { iFrame. }
  iIntros (r Hr) "(Htcb & Hio & Hlives & Herr & Hclosed & (Hol & Hop & Hsl & Hsp & Hxl & Hstatus & Hil & Hib) & Hrs & HE)".
  resume.
  iApply (wp_close_stdout_dispatch _ r ib ireg flag eb
    (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (mkPtr rb (Obj rb) :: rest) ∗
     ([∗ list] g ∈ mkPtr rb (Obj rb) :: rest, stream_life g) ∗ live ob oreg ∗ pcell ob 0 (mkPtr fb (Obj fb)) ∗
     live sc screg ∗ pcell sc 0 (mkPtr rb (Obj rb)) ∗ live xc xcreg ∗ int_cell xc 0 status ∗
     stderr_short_fields rb vb ∗ closed_stdout fb freg vb lb lbreg ∗ E)%I
    with "Hil Hib Herr [Htcb Hio Hlives Hol Hop Hsl Hsp Hxl Hstatus Hrs Hclosed HE] [HK]");
    try assumption; [destruct Hr as [-> | ->]; reflexivity | iFrame |].
  iSplit.
  - iIntros (e) "Hil Hib Herr (Htcb & Hio & Hlives & Hol & Hop & Hsl & Hsp & Hxl & Hstatus & Hrs & Hclosed & HE)".
    iDestruct "HK" as "[_ HK]".
    iDestruct "Hlives" as "[HrLife Hlives]".
    iEval (unfold stream_life) in "HrLife".
    iDestruct "HrLife" as (gb greg [Hptr [Hrb [Hrbal [Hrbe Hrbr]]]]) "Hrl".
    assert (gb = rb) by congruence. subst gb.
    iEval (unfold stderr_short_fields) in "Hrs".
    iDestruct "Hrs" as (rfl rf2 rfd roff rrp rre rrr rwe rbe rmd rlb rlbreg Hprops)
      "(Hrfl & Hrfl2 & Hrfd & Hroff & Hrrp & Hrre & Hrrr & Hrwb & Hrwp & Hrwe & Hrbase & Hrbend & Hrmode & Hrvtp & Hr80 & Hr96 & Hrlp & Hrlk)".
    destruct Hprops as (Hrfl & Hrf2 & Hr232 & Hrnl & Hrfd & Hrnw & Hrcp & Hrub & Hrul & Hrln & Hrfb & Hrlb & Hrmd).
    iApply (wp_hello_close_stdout_stderr_short_empty Hreg Hext Hfc Hff e [] rest rb greg rfl rf2 rfd roff
      rrp rre rrr rwe rbe eb vb vreg rlb rlbreg sb sreg fcp pin (mkPtr fb (Obj fb)) rmd sc screg xc xcreg status
      (live ob oreg ∗ pcell ob 0 (mkPtr fb (Obj fb)) ∗ live ib ireg ∗ bytes ib 0 [flag] ∗
        closed_stdout fb freg vb lb lbreg ∗ E)%I
      with "Hvt Hs Htcb Hrl Hrfl Hrfl2 Hrfd Hroff Herr Hrrp Hrre Hrrr Hrwb Hrwp Hrwe Hrbase Hrbend Hrmode Hrvtp
        Hr80 Hr96 Hrlp Hrlk Hio Hlives [Hsl Hsp Hxl Hstatus] [Hol Hop Hil Hib Hclosed HE] [HK]"); try close_side; try exact Hrmd.
    + iFrame.
    + iFrame.
    + iIntros "(Htcb & Hio & Hlives & Herr & (Hsl & Hsp & Hxl & Hstatus) & Hol & Hop & Hil & Hib & Hclosed & HE)".
      iApply "HK". iFrame.
  - iIntros (e) "Hil Hib Herr (Htcb & Hio & Hlives & Hol & Hop & Hsl & Hsp & Hxl & Hstatus & Hrs & Hclosed & HE)".
    iDestruct "HK" as "[HK _]". iApply "HK". iFrame.
Qed.
End close.

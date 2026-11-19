(** Hello registers gnulib's `c: close_stdout` with `c: atexit`. When
    the callback runs, the wide greeting has already made stdout wide.
    The callback closes stdout first. If that fails, it reports the
    failure on stderr and exits; otherwise it closes stderr too. This
    file proves the callback when stdout is wide and stderr is narrow.
    [HelloCloseStdoutIdle](HelloCloseStdoutIdle.v) proves the narrow
    case, and this proof follows it step for step. The error report is
    a premise here, because another proof covers the call to
    `c: error`. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloClose.
From Glibc Require Import Unit_io_close_nocancel_os Unit_io_write_os Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_fileops_os.
From Glibc Require Import Unit_libio_genops_os Unit_libio_iofclose_os Unit_libio_wgenops_os Unit_nptl_libcZ2dcleanup_os Unit_posix__exit_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  FileInv FileIdle LibioLogic SysWrappers LibioCloseSteps LeavesLogic AllocLogic
  LibioWIdle LibioSetb LibioWFwide LibioWOverflowWrite LibioWCloseIt LibioWRelease Mbrtowc HelloImageLoad
  HelloImageWFwideObjs HelloImageWReleaseObjs HelloWClosedStdout HelloClosedStdout HelloCloseErrno
  HelloCloseDispatch HelloCloseDiagnostic HelloCloseStreamIdle HelloCloseStdoutIdle HelloCloseStreamWide.
From Glibc Require LibioFcloseTail.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps LibioFcloseTail.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation tw := (rop (img_a "glibc_wcsmbsload#to_wc")).
Local Abbreviation tm := (rop (img_a "glibc_wcsmbsload#to_mb")).

(** ## Loading wide stdout

    The callback reads `c: stdout` from its global before it closes the
    stream, and the read checks that the stream is still alive. These
    rules are [wp_load_idle_ptr] and [wp_load_idle] for a stream held
    as [file_wide]: they lend the stream's lifetime to the read. *)

Section load.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The pointer load reads the global's cell and checks the life of
    the stream it points to. *)
Lemma wp_load_wide_ptr f e ls lab d c rest j sb sreg vb self g fd Ψ :
  lookup c e = Some (WPtr (mkPtr sb (Obj sb))) -> 0 <= sb < 2 ^ 64 -> sb mod 8 = 0 ->
  liveq DfracDiscarded sb sreg -∗ pcellq DfracDiscarded sb 0 g -∗ file_wide ge vb self g fd -∗
  ▷ (file_wide ge vb self g fd -∗
     WP (ERun (mkFrame f (put d (WPtr g) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead])
                                             [Tmp c] :: rest) j)) : gexpr) {{ Ψ }}.
Proof using Type.
  intros Hc Hb0 Hb8. iIntros "Hl Hp Hf HK".
  iDestruct "Hf" as (fb freg st nb wd w t1 t2 Hp) "(Hfl & Hrest)".
  pose proof Hp as (Hg & Hal & Hfb & Hend & Hreg & _).
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb sreg 0 g freg DfracDiscarded DfracDiscarded
            (DfracOwn 1) with "Hl Hp [Hfl]");
    [reflexivity | cbn; rewrite Hc; reflexivity | left; reflexivity |
     cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia | rewrite Z.add_0_r; exact Hb8 |
     subst g; cbn; unfold file_size in *; lia | subst g; iExact "Hfl" |].
  iNext. iIntros "_ _ Hfl". iApply "HK". iExists fb, freg, st, nb, wd, w, t1, t2. iFrame. iSplit; [iPureIntro; exact Hp|].
  subst g. iExact "Hfl".
Qed.

(** The code first checks that the global's cell is readable, then
    loads the stream's address from it. *)
Lemma wp_load_wide f e ls lab vc chk d rest j sb sreg vb self g fd Ψ :
  lookup vc e = Some (WPtr (mkPtr sb (Obj sb))) ->
  0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48 ->
  liveq DfracDiscarded sb sreg -∗ pcellq DfracDiscarded sb 0 g -∗ file_wide ge vb self g fd -∗
  (file_wide ge vb self g fd -∗
   WP (ERun (mkFrame f (put d (WPtr g) (put chk (WPtr (mkPtr sb (Obj sb))) e)) ls None (Exec lab rest j)) : gexpr)
     {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Let chk A (Check 0 8 Read 8) [Tmp vc] ::
                  Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [Tmp chk] :: rest) j)) : gexpr)
    {{ Ψ }}.
Proof using Type.
  intros Hv (Hs0 & Hs8 & Hse & Hsr). iIntros "Hl Hc Hf HK".
  rule1 "Hl" ltac:(eapply LibioLogic.wp_check_read_dq; inst; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  iApply (wp_load_wide_ptr with "Hl Hc Hf"); [apply Symbolic.lookup_after_put_same | lia | exact Hs8 |].
  iNext. iIntros "Hf". iApply ("HK" with "Hf").
Qed.
End load.

(** ## The exit callback on wide stdout

    The callback closes wide stdout first. When that close fails, it
    reports the failure on stderr and exits with the failure status.
    Otherwise it closes stderr, which is still narrow, and exits only if
    that close fails. The converter's loan L and the free conversion
    lock go with the caller's frame E on every path. *)

Section close.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
#[local] Hint Opaque live pcell int_cell icell bytes errno_any lock_state io_list_inv vtables_ro single_ro
  wvtables_ro tcb_cleanup_inv stream_life closed_stdout closed_wide file_idle file_wide gconv_lock_free : typeclass_instances.

Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__fpending" Unit_libio___fpending_os.fn___fpending}
  `{!Defines ge "ferror" Unit_libio_ferror_os.fn__IO_ferror}
  `{!Defines ge "fclose" Unit_libio_iofclose_os.fn__IO_new_fclose}
  `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{!Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None)
  `{!Defines ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close)
  `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}
  `{!Defines ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers}
  `{!Defines ge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer}
  `{!Defines ge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore}
  `{!Defines ge "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link}
  `{!Defines ge "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish)
  `{!Defines ge "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink}
  `{!Defines ge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb}
  `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn}
  `{!Defines ge "__errno_location" LeavesLogic.errno_location_fn}
  `{!Defines ge "close_stream" close_stream_fn}
  `{!Defines ge "_exit" Unit_posix__exit_os.fn___GI__exit}.

(** The callback either returns with stdin as the only open stream, or
    it exits. A failed close of stdout prints a message without a file
    name, which the premise on errorframe covers. The caller says how to
    build the message's resource R from the closed wide stdout and what
    else the callback holds. *)
Lemma wp_close_stdout_wide fo fe pin fcp vb vreg sb sreg eb ob oreg sc screg xc xcreg status ib ireg flag
    nb nreg fmt text namedfmt errorfn errorframe (L R Q E : iProp Σ) Φ :
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 <= ob /\ ob mod 8 = 0 /\ ob + 8 <= r_end oreg /\ r_end oreg <= 2 ^ 48 ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sc (Obj sc)) ->
  0 <= sc /\ sc mod 8 = 0 /\ sc + 8 <= r_end screg /\ r_end screg <= 2 ^ 48 ->
  lookup (TAtom "exit_failure") (ge_globals ge) = Some (mkPtr xc (Obj xc)) ->
  0 < xc -> xc + 4 <= r_end xcreg -> r_end xcreg <= 2 ^ 63 ->
  lookup (TAtom "closeout#ignore_EPIPE") (ge_globals ge) = Some (mkPtr ib (Obj ib)) ->
  0 < ib -> ib + 1 <= r_end ireg -> r_end ireg <= 2 ^ 63 -> 0 <= flag < 256 ->
  lookup (TAtom "closeout#file_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "closeout#str.52") (ge_globals ge) = Some namedfmt ->
  lookup (TAtom "closeout#str.53") (ge_globals ge) = Some text ->
  lookup (TAtom "closeout#str.55") (ge_globals ge) = Some fmt ->
  find_fn ge (TAtom "error") = Some (Defined errorfn) ->
  (forall n, call_frame errorfn [WInt 0; WInt n; WPtr fmt; WPtr text] = Some (errorframe n)) ->
  (forall n, 0 <= n < 2 ^ 32 -> ⊢ errno_any eb -∗ R -∗
    WP (ERun (errorframe n) : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ errno_any eb ∗ Q }}) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fo ->
  lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fe ->
  ptr_addr fo <> ptr_addr fe -> 0 <= ptr_addr fo < 2 ^ 64 ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin ->
  ptr_addr pin <> ptr_addr fo -> ptr_addr pin <> ptr_addr fe -> 0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  lookup (TAtom "__gconv_lock") (ge_globals ge) = Some (objp (img_a "__gconv_lock")) ->
  lookup (TAtom "glibc_wcsmbsload#to_wc") (ge_globals ge) = Some tw ->
  lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) = Some tm ->
  find_fn ge (TAtom "__gconv_release_step") = Some (Defined glibc_gconv_release_step) ->
  (forall fb freg wd, wclose_write_rule 1 vb fb vreg freg eb wd tw tm L) ->
  In 1 (ow_fds w0) -> In 2 (ow_fds w0) ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  liveq DfracDiscarded ob oreg -∗ pcellq DfracDiscarded ob 0 fo -∗
  liveq DfracDiscarded sc screg -∗ pcellq DfracDiscarded sc 0 fe -∗
  live xc xcreg -∗ int_cell xc 0 status -∗ live ib ireg -∗ bytes ib 0 [flag] -∗
  live nb nreg -∗ pcell nb 0 null -∗
  file_wide ge vb (ow_self w0) fo 1 -∗ file_idle vb (ow_self w0) fe 2 -∗ errno_any eb -∗
  L -∗ mbr_tables -∗ ptsq DfracDiscarded hello_wfwide_ps -∗ ptsq DfracDiscarded hello_wrelease_ps -∗
  gconv_lock_free -∗ io_list_inv ge [fe; fo; pin] -∗ stream_life pin -∗ E -∗
  (((∃ fb freg lb lr wd, ⌜fo = objp fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
      closed_wide fb freg vb lb lr tw tm wd) -∗
      file_idle vb (ow_self w0) fe 2 -∗ tcb_cleanup_inv (ow_self w0) -∗ L -∗ gconv_lock_free -∗ E -∗ R) ∧
   (tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge [pin] -∗ stream_life pin -∗ L -∗ gconv_lock_free -∗ E -∗
      Φ RetVoid)) -∗
  WP (ERun (mkFrame close_stdout_fn [] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hgo Hob Hgse Hsc Hgx Hxc Hxce Hxcr Hgi Hib Hibe Hibr Hflag Hgn Hnb Hnba Hnbe Hnbr
    Hnamed Htext Hfmt Herrfn Hframe Hcall Hglobal He Hgfo Hgfe Hoe Hfor Hgin Hio Hie Hinr Hfcg Hfcr
    Hgl Htw Htm Hrel Hwrite Hfd1 Hfd2.
  iIntros "#Hvt #Hwv #Hs Htcb #Hol #Hop #Hsl #Hsp Hxl Hstatus Hil Hib Hnl Hnp Hout Herf Herr HL #Hmb #Hfwp #Hwrp Hlk
    Hio Hin HE HK".
  step. step.
  iApply (wp_load_wide with "Hol Hop Hout"); [reflexivity | exact Hob |]. iIntros "Hout".
  iDestruct (file_idle_life with "Herf") as "[Hel Heb]".
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_close_stream_wide Hreg Hext Hfree Hfc Hff [fe] [pin] fo 1 pin fcp vb vreg sb sreg eb L
    ((stream_life fe -∗ file_idle vb (ow_self w0) fe 2) ∗ E ∗ live xc xcreg ∗ int_cell xc 0 status ∗ live ib ireg ∗
     bytes ib 0 [flag] ∗ live nb nreg ∗ pcell nb 0 null)%I
    with "Hvt Hwv Hs Htcb Hout Herr HL Hmb Hfwp Hwrp Hlk Hio [Hel Hin] [Heb HE Hxl Hstatus Hil Hib Hnl Hnp]");
    try first [reflexivity | eassumption | lia].
  { cbn [app big_opL]. iFrame. }
  { iFrame. }
  iIntros (r Hr) "(Herr & Htcb & Hio & Hlives & Hc & HL & Hlk & Heb & HE & Hxl & Hstatus & Hil & Hib & Hnl & Hnp)".
  resume.
  iApply (wp_close_stdout_dispatch _ r ib ireg flag eb
    (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge ([fe] ++ [pin]) ∗ ([∗ list] g ∈ [fe] ++ [pin], stream_life g) ∗
     (∃ fb freg lb lr wd, ⌜fo = objp fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
      closed_wide fb freg vb lb lr tw tm wd) ∗ L ∗ gconv_lock_free ∗
     (stream_life fe -∗ file_idle vb (ow_self w0) fe 2) ∗ E ∗ live xc xcreg ∗ int_cell xc 0 status ∗
     live nb nreg ∗ pcell nb 0 null)%I
    with "Hil Hib Herr [Htcb Hio Hlives Hc HL Hlk Heb HE Hxl Hstatus Hnl Hnp] [HK]");
    try assumption; [destruct Hr as [-> | ->]; reflexivity | iFrame |].
  iSplit.
  - iIntros (e') "Hil Hib Herr (Htcb & Hio & Hlives & Hc & HL & Hlk & Heb & HE & Hxl & Hstatus & Hnl & Hnp)".
    cbn [app big_opL]. iDestruct "Hlives" as "(Hel & Hin & _)".
    iDestruct ("Heb" with "Hel") as "Herf".
    step. step.
    iApply (wp_load_idle with "Hsl Hsp Herf"); [reflexivity | exact Hsc |]. iIntros "Herf".
    iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
    iApply (wp_close_stream_idle Hreg Hext Hfw Hfh Hzf Hzg Hfc Hff [] [pin] fe 2 pin fo fcp vb vreg sb sreg eb
      ((((∃ fb freg lb lr wd, ⌜fo = objp fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
          closed_wide fb freg vb lb lr tw tm wd) -∗
          file_idle vb (ow_self w0) fe 2 -∗ tcb_cleanup_inv (ow_self w0) -∗ L -∗ gconv_lock_free -∗ E -∗ R) ∧
        (tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge [pin] -∗ stream_life pin -∗ L -∗ gconv_lock_free -∗ E -∗
          Φ RetVoid)) ∗
       L ∗ gconv_lock_free ∗ E ∗ live xc xcreg ∗ int_cell xc 0 status)%I
      with "Hvt Hs Htcb Herf Herr Hio [Hin] [HK HL Hlk HE Hxl Hstatus]");
      try first [reflexivity | eassumption | lia].
    { right. exact (conj Hoe (conj Hfor Hgfe)). }
    { cbn [app big_opL]. iFrame. }
    { iFrame. }
    iIntros (r2 Hr2) "(Herr & Htcb & Hio & Hlives & Hc2 & HK & HL & Hlk & HE & Hxl & Hstatus)".
    resume. destruct Hr2 as [-> | ->].
    + step. branch. step. iApply wp_ret_void. iNext. iDestruct "HK" as "[_ HK]".
      cbn [app big_opL]. iDestruct "Hlives" as "[Hin _]". iApply ("HK" with "Htcb Hio Hin HL Hlk HE").
    + step. branch. step. step.
      iApply (wp_live_fit1 with "Hxl"). iIntros ([Hxc0 Hxc48]) "Hxl".
      check "Hxl". iEval (unfold int_cell) in "Hstatus".
      iDestruct "Hstatus" as "[%Hst Hbytes]".
      load_s32 "Hxl" "Hbytes".
      iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
      iApply (SysWrappers.wp_glibc__exit Hreg Hext). reflexivity.
  - iIntros (e') "Hil Hib Herr (Htcb & Hio & Hlives & Hc & HL & Hlk & Heb & HE & Hxl & Hstatus & Hnl & Hnp)".
    cbn [app big_opL]. iDestruct "Hlives" as "(Hel & Hin & _)".
    iDestruct ("Heb" with "Hel") as "Herf".
    iDestruct "HK" as "[HR _]".
    iDestruct ("HR" with "Hc Herf Htcb HL Hlk HE") as "HR".
    iAssert (live_cap (ptr_cap null) xcreg) as "Hpl"; [cbn; done|].
    iApply (wp_close_stdout_diagnostic Hreg Hext e' nb nreg null xcreg xc xcreg status eb fmt text namedfmt
      errorfn errorframe R Q (live ib ireg ∗ bytes ib 0 [flag])%I Φ
      with "Hnl Hnp Hpl Hxl Hstatus Herr HR [Hil Hib]"); try first [eassumption | lia | cbn; lia].
    { iFrame. }
    iIntros (e2 Hnz). exfalso. apply Hnz. reflexivity.
Qed.
End close.

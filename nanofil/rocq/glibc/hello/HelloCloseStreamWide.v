(** Hello prints its greeting with `c: wprintf`, and that makes stdout
    wide. So at exit, gnulib's `c: close_stream` closes a wide stdout.
    Before it calls `c: fclose`, it asks `c: __fpending` whether output
    is waiting and asks `c: ferror` whether the stream saw an error.
    This file proves both questions and the whole call for a stream
    held as [file_wide]. The fclose step is [wp_fclose_wide] from
    [HelloFcloseWide](HelloFcloseWide.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloClose.
From Glibc Require Import Unit_io_close_nocancel_os Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import Unit_libio_iofclose_os Unit_libio_wgenops_os Unit_nptl_libcZ2dcleanup_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  FileInv FileIdle LibioLogic SysWrappers LibioCloseSteps LibioRead
  LibioWIdle LibioWXsputnWindow LibioWXsputnRoom LibioWOverflowWrite LibioWCloseIt LibioSetb
  LibioWFwide LibioWFcloseTail
  LibioWRelease Mbrtowc HelloImageLoad HelloImageWFwideObjs HelloImageWReleaseObjs HelloWClosedStdout
  HelloFcloseWide HelloCloseStreamRetain HelloCloseErrno Fix.
From Glibc Require LibioFcloseTail.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps LibioFcloseTail.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).

(** ## Queries on a wide stream

    Close_stream asks two questions before it closes the stream, and
    neither changes the stream. On a wide stream `c: __fpending` counts
    the wide characters between the wide write base and the wide write
    pointer, and `c: ferror` reads the narrow flags as it does on any
    stream. The two rules below give the [file_wide] stream back
    unchanged, so the caller can go on to the wide fclose. *)

Section queries.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** On a wide stream, `c: __fpending (fp)` counts the characters that
    wait in the wide buffer. It reads the wide write pointer and the
    wide write base, and each load checks that the buffer they point
    into is still alive. The wide data owns both cursors and that
    buffer, so the proof borrows them with [close_cursors] and puts
    them back after the loads. *)
Lemma wp_fpending_wide fr fp vb self fd Φ :
  call_frame Unit_libio___fpending_os.fn___fpending [WPtr fp] = Some fr ->
  file_wide ge vb self fp fd -∗
  ▷ (∀ n, ⌜0 <= n < 2 ^ 64⌝ -∗ file_wide ge vb self fp fd -∗ Φ (Ret (WInt n))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr. iIntros "Hf HK".
  iDestruct "Hf" as (fb freg st nb wd w tw tm H) "(Hl & HF & Hlk & Hb & Hdata)".
  pose proof H as (-> & Hal & Hfb & Hend & Hfrg & _ & _ & Hmode & _ & _ & _ & _ & Hwd & _).
  iDestruct (close_cursors with "Hdata") as (wr i j (Hw0 & Hwa & Hwe & Hwr & B & Hi & Hj))
    "(Hw & P0 & P1 & P3 & P4 & Hwb & Hback)".
  iDestruct "HF" as "(%L & Hfl & Hps & Hfd & Hf2 & Ho & %Lc & Hcol & Hlp & Hoff & Hcv & Hwdp & Hfrl & Hfrb & Hmd & Hwt & Hvtp)".
  rewrite Hwd Hmode. iDestruct "Hmd" as "[%Rm Hmd]".
  injection Hfr as <-. unfold file_size in Hend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([? ?]) "Hl". iApply (wp_live_fit1 with "Hw"). iIntros ([? ?]) "Hw".
  step. step. norm. check "Hl". load_s32 "Hl" "Hmd". step. closed_ints. branch.
  step. step. norm. check "Hl". load "Hl" "Hwdp" "Hw". step. check "Hw". load_wpos "Hw" "P4" "Hwb".
  load "Hl" "Hwdp" "Hw". step. check "Hw". load_wpos "Hw" "P3" "Hwb".
  step. step. step. step.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "[%]"). all: try (apply Z.mod_pos_bound; lia).
  iExists fb, freg, st, nb, wd, w, tw, tm. iFrame "Hl Hlk Hb". iSplit; [done|].
  iSplitR "Hw P0 P1 P3 P4 Hwb Hback".
  - rewrite /file_fields Hwd Hmode. iFrame "Hfl Hps Hfd Hf2 Ho Hcol Hlp Hoff Hcv Hwdp Hfrl Hfrb Hwt Hvtp".
    iSplit; [done|]. iSplit; [done|]. iSplit; [iPureIntro; exact Rm|iExact "Hmd"].
  - iExists wr, (window_slots wd w i j). iApply ("Hback" with "Hw P0 P1 P3 P4 Hwb").
Qed.

(** The call `c: ferror (fp)` reads the error bit of the flags. A wide
    stream between calls needs no lock, as [wflags_ok] says, so the
    call takes no lock and changes nothing. *)
Lemma wp_ferror_wide fr fp vb self fd Φ :
  call_frame Unit_libio_ferror_os.fn__IO_ferror [WPtr fp] = Some fr ->
  file_wide ge vb self fp fd -∗
  ▷ (∀ e, ⌜e = 0 \/ e = 1⌝ -∗ file_wide ge vb self fp fd -∗ Φ (Ret (WInt e))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr. iIntros "Hf HK".
  iDestruct "Hf" as (fb freg st nb wd w tw tm H) "(Hl & HF & Hlk & Hb & Hdata)".
  pose proof H as (-> & Hal & Hfb & Hend & Hfrg & F & _).
  pose proof F as (_ & _ & _ & _ & _ & Hnl).
  iDestruct "HF" as "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hrest)".
  iApply (wp_glibc__IO_ferror with "Hl Hfl Hf2");
    try first [exact Hfr | exact Hnl | unfold file_size in *; lia].
  iNext. iIntros "Hl Hfl Hf2".
  iApply ("HK" with "[%] [-]"); [destruct (_ =? 0); auto|].
  iExists fb, freg, st, nb, wd, w, tw, tm. iFrame "Hl Hlk Hb Hdata". iSplitR; [iPureIntro; exact H|].
  rewrite /file_fields. iFrame. done.
Qed.
End queries.

(** ## Close_stream on a wide stream

    Hello's exit callback needs only to know whether closing stdout
    succeeded. The rule below chains the two queries with the wide
    fclose and proves the blocks that read or clear errno, so its
    caller sees only a return of 0 or `c: EOF`. The converter's loan L
    and the free conversion lock pass through the call and come back. *)

Section close.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation tw := (rop (img_a "glibc_wcsmbsload#to_wc")).
Local Abbreviation tm := (rop (img_a "glibc_wcsmbsload#to_mb")).
#[local] Hint Opaque live pcell int_cell icell bytes errno_any lock_state io_list_inv vtables_ro single_ro
  wvtables_ro tcb_cleanup_inv stream_life closed_wide file_wide gconv_lock_free : typeclass_instances.

Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge)
  (Hfc : ge_fn ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close)
  (Hff : ge_fn ge "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish)
  `{!Defines ge "__fpending" Unit_libio___fpending_os.fn___fpending}
  `{!Defines ge "ferror" Unit_libio_ferror_os.fn__IO_ferror}
  `{!Defines ge "fclose" Unit_libio_iofclose_os.fn__IO_new_fclose}
  `{!Defines ge "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link}
  `{!Defines ge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer}
  `{!Defines ge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore}
  `{!Defines ge "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish}
  `{!Defines ge "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink}
  `{!Defines ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel}
  `{!Defines ge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb}
  `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{!Defines ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers}
  `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn}
  `{!Defines ge "__errno_location" LeavesLogic.errno_location_fn}.

(** When close_stream returns on wide stdout, the result is 0 or
    `c: EOF`. Either way the caller gets back the closed stream, errno
    and the other streams. It also gets back the loan L that the
    converter borrowed, the free conversion lock and its own frame F. *)
Lemma wp_close_stream_wide pre post fp fd pin fcp vb vr sb sr eb (L F : iProp Σ) Φ :
  let Q := (errno_any eb ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
    ([∗ list] g ∈ pre ++ post, stream_life g) ∗
    (∃ fb freg lb lr wd, ⌜fp = objp fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
      closed_wide fb freg vb lb lr tw tm wd) ∗ L ∗ gconv_lock_free ∗ F)%I in
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> ptr_addr fp ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  lookup (TAtom "__gconv_lock") (ge_globals ge) = Some (objp (img_a "__gconv_lock")) ->
  lookup (TAtom "glibc_wcsmbsload#to_wc") (ge_globals ge) = Some tw ->
  lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) = Some tm ->
  find_fn ge (TAtom "__gconv_release_step") = Some (Defined glibc_gconv_release_step) ->
  fd <> 0 -> ow_errno w0 = Some (objp eb) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (objp eb) ->
  (forall fb freg wd, wclose_write_rule fd vb fb vr freg eb wd tw tm L) ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ single_ro ge sb sr -∗ tcb_cleanup_inv (ow_self w0) -∗
  file_wide ge vb (ow_self w0) fp fd -∗ errno_any eb -∗ L -∗
  mbr_tables -∗ ptsq DfracDiscarded hello_wfwide_ps -∗ ptsq DfracDiscarded hello_wrelease_ps -∗ gconv_lock_free -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗ F -∗
  (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ Q -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (hello_close_stream_frame fp) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Q Hgout Hgin Hin Hinr Hfcg Hfcr Hgl Htw Htm Hrel Hfd0 He Hglobal Hwrite.
  iIntros "#Hvt #Hwv #Hs Htcb Hf Herr HL #Hmb #Hfw #Hwr Hlk Hio Hlives HF HK".
  iAssert (close_stream_errno_paths Q Φ ∧ (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ Q -∗ Φ (Ret (WInt r))))%I
    with "[HK]" as "HK".
  { iSplit; [|iExact "HK"]. iApply (close_stream_errno_complete eb He Hglobal). iExact "HK". }
  unfold hello_close_stream_frame. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_fpending_wide with "Hf"); [reflexivity|].
  iNext. iIntros (n Hn) "Hf". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_ferror_wide with "Hf"); [reflexivity|].
  iNext. iIntros (e He') "Hf". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_fclose_wide Hreg Hext Hfree Hfc Hff _ pre post fp fd pin fcp vb vr sb sr eb L
    with "Hvt Hwv Hs Htcb Hf Herr HL Hmb Hfw Hwr Hlk Hio Hlives"); try first [reflexivity | eassumption].
  iNext. iIntros (k Hk) "Htcb Hio Hlives Hc Herr HL Hlk". resume.
  iAssert Q with "[$Htcb $Hio $Hlives $Herr $Hc $HL $Hlk $HF]" as "HQ".
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

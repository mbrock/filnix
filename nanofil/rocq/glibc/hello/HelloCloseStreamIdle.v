(** At exit Hello calls gnulib's `c: close_stream` on stdout and then
    on stderr. That function asks `c: __fpending` whether output waits,
    asks `c: ferror` whether the stream saw an error, and then calls
    `c: fclose`. This file proves the call for a stream held as
    [file_idle], as Hello holds both standard streams between calls.
    The fclose step is [wp_fclose_idle] from [HelloCloseIdle](HelloCloseIdle.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloClose.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  SysCode LibioReadCode LibioDoWriteCode LibioGenCode LibioUnlinkCode LibioCloseItCode LibioFcloseCode
  FileInv FileIdle LibioLogic SysWrappers AllocLogic LibioCloseSteps LibioRead LibioPendingShort
  HelloClosedStdout HelloCloseIdle HelloCloseStreamRetain.
From Glibc Require LibioFcloseTail.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps LibioFcloseTail.
Open Scope Z_scope.

(** ## Queries on an idle stream

    Close_stream asks two questions before it closes the stream, and
    neither changes the stream. The two rules below answer them for a
    stream held as [file_idle] and give the stream back unchanged, so
    the caller can go on to fclose. *)

Section queries.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The call `c: __fpending (fp)` subtracts the write base from the
    write pointer. With no buffer both pointers are null, and with the
    short buffer both point at it. With a heap buffer both point into
    the buffer, whose lifetime [buf_idle] owns, so the loads can check
    the pointers' capability. *)
Lemma wp_fpending_idle fr fp vb self fd Φ :
  call_frame glibc___fpending [WPtr fp] = Some fr ->
  file_idle vb self fp fd -∗
  ▷ (∀ n, ⌜0 <= n < 2 ^ 64⌝ -∗ file_idle vb self fp fd -∗ Φ (Ret (WInt n))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr. iIntros "Hf HK".
  iDestruct "Hf" as (fb freg st nb Hp) "(Hl & Hf & Hlk & Hb & Hw)".
  pose proof Hp as (-> & Hal & Hfb & Hend & Hfreg & Hok & Hidle & Hvtb & Hbok & Hshort).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb &
    Hmd & Htot & Hvtp)".
  destruct st as [fl ps fdd f2 oldoff col lk off cv wd frl frb md tw vt].
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable] in *.
  destruct ps as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]]; try discriminate Hlen.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  pose proof Hidle as Hidle'. unfold idle_ok in Hidle'. cbn [fs_mode] in Hidle'.
  destruct Hidle' as (_ & _ & Hmd0 & _).
  iAssert (▷ ∀ n, ⌜0 <= n < 2 ^ 64⌝ -∗ live fb freg -∗ int_cell fb off_mode md -∗
    pcell fb off_write_ptr p4 -∗ pcell fb off_write_base p3 -∗ buf_idle nb -∗ Φ (Ret (WInt n)))%I
    with "[- Hl Hmd P3 P4 Hb]" as "HK".
  { iNext. iIntros (n Hn) "Hl Hmd P4 P3 Hb". iApply ("HK" $! n Hn).
    iExists fb, freg, (mkFstate fl [p0; p1; p2; p3; p4; p5; p6; p7; p8; p9; p10; p11] fdd f2 oldoff col lk off
      cv wd frl frb md tw vt), nb.
    iFrame "Hl Hlk Hb Hw". iSplitR; [iPureIntro; exact Hp|].
    rewrite /file_fields. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
      fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable big_opL].
    iFrame "Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfd Hf2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp".
    iPureIntro. split; done. }
  destruct nb as [| |bb sz|bb]; cbn [buf_ptrs_ok take] in Hbok.
  4: { iDestruct "Hb" as "[]". }
  - (* No buffer: both pointers are null. *)
    cbn in Hbok. injection Hbok; intros; subst.
    iApply (wp_glibc___fpending _ fb freg md null null freg with "Hl Hmd P4 P3 []");
      try first [exact Hfr | exact Hmd0 | reflexivity | unfold file_size in *; cbn; lia | done].
    iNext. iIntros "Hl Hmd P4 P3 _".
    iApply ("HK" with "[%] Hl Hmd P4 P3 Hb"). apply Z.mod_pos_bound. lia.
  - (* The short buffer: both pointers point at it. *)
    destruct Hbok as (E6 & E7 & _). cbn [nth] in E6, E7.
    unfold short_idle, fs_ptr in Hshort. cbn [fs_flags fs_ptrs nth] in Hshort.
    destruct Hshort as (_ & _ & E43 & _ & E36). subst p4 p3 p6.
    change (fb + 131) with (fb + off_shortbuf).
    iApply (wp_glibc___fpending_short_empty with "Hl Hmd P4 P3");
      try first [exact Hfr | exact Hmd0 | unfold file_size in *; lia].
    iNext. iIntros "Hl Hmd P4 P3".
    iApply ("HK" with "[%] Hl Hmd P4 P3 Hb"). lia.
  - (* A heap buffer: both pointers point into it. *)
    destruct Hbok as (E6 & E7 & Hall).
    repeat rewrite Forall_cons_iff in Hall.
    destruct Hall as (_ & _ & _ & [Hc3 Ha3] & [Hc4 Ha4] & _).
    iDestruct "Hb" as (breg xs cs Hbp) "(Hbl & Hxs & Hcs)".
    pose proof Hbp as (_ & Hbe & Hbreg & Hb0 & _).
    destruct p3 as [a3 c3], p4 as [a4 c4]. cbn [ptr_addr ptr_cap] in *. subst c3 c4.
    iApply (wp_glibc___fpending _ fb freg md (mkPtr a4 (Obj bb)) (mkPtr a3 (Obj bb)) breg
      with "Hl Hmd P4 P3 [Hbl]");
      try first [exact Hfr | exact Hmd0 | reflexivity | unfold file_size in *; cbn; lia].
    { cbn [ptr_cap live_cap]. iExact "Hbl". }
    iNext. iIntros "Hl Hmd P4 P3 Hbl". iEval (cbn [ptr_cap live_cap]) in "Hbl".
    iApply ("HK" with "[%] Hl Hmd P4 P3 [Hbl Hxs Hcs]").
    { apply Z.mod_pos_bound. lia. }
    iExists breg, xs, cs. iFrame. done.
Qed.

(** The call `c: ferror (fp)` reads the error bit of the flags. The
    flags of an idle stream say that the stream needs no lock, so the
    call takes no lock and changes nothing. *)
Lemma wp_ferror_idle fr fp vb self fd Φ :
  call_frame glibc__IO_ferror [WPtr fp] = Some fr ->
  file_idle vb self fp fd -∗
  ▷ (∀ e, ⌜e = 0 \/ e = 1⌝ -∗ file_idle vb self fp fd -∗ Φ (Ret (WInt e))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr. iIntros "Hf HK".
  iDestruct "Hf" as (fb freg st nb Hp) "(Hl & Hf & Hlk & Hb & Hw)".
  pose proof Hp as (-> & Hal & Hfb & Hend & Hfreg & Hok & _).
  pose proof Hok as (_ & _ & _ & _ & _ & Hnl & _).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hrest)".
  iApply (wp_glibc__IO_ferror with "Hl Hfl Hf2");
    try first [exact Hfr | exact Hnl | unfold file_size in *; lia].
  iNext. iIntros "Hl Hfl Hf2".
  iApply ("HK" with "[%] [-]"); [destruct (_ =? 0); auto|].
  iExists fb, freg, st, nb. iFrame "Hl Hlk Hb Hw". iSplitR; [iPureIntro; exact Hp|].
  rewrite /file_fields. iFrame. done.
Qed.
End queries.

(** ## Close_stream on an idle stream

    The rule below chains the two queries and [wp_fclose_idle]. Like
    [wp_hello_close_stream_stdout_retained], it hands the paths that
    read or reset errno to the caller through [close_stream_errno_paths],
    because what those paths do next depends on the caller. *)

Section close.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
#[local] Hint Opaque live pcell int_cell icell bytes errno_any lock_state io_list_inv vtables_ro single_ro
  tcb_cleanup_inv stream_life closed_stdout file_idle : typeclass_instances.

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

(** Close_stream on idle stdout or stderr returns 0 or `c: EOF`, or
    reaches one of the two errno paths. Every outcome holds the closed
    stream, errno and the rest of the stream list, and the caller may
    frame any other resources in E. *)
Lemma wp_close_stream_idle pre post fp fd pin pout fcp vb vreg sb sreg eb (E : iProp Σ) Φ :
  let Q := (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
    ([∗ list] g ∈ pre ++ post, stream_life g) ∗ errno_any eb ∗
    (∃ fb freg lb lbreg, ⌜fp = mkPtr fb (Obj fb)⌝ ∗ closed_stdout fb freg vb lb lbreg) ∗ E)%I in
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some pout ->
  (pout = fp \/ (ptr_addr pout <> ptr_addr fp /\ 0 <= ptr_addr pout < 2 ^ 64 /\
    lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some fp)) ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> ptr_addr fp ->
  0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  fd <> 0 -> In fd (ow_fds w0) -> ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  file_idle vb (ow_self w0) fp fd -∗ errno_any eb -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗ E -∗
  (close_stream_errno_paths Q Φ ∧ (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ Q -∗ Φ (Ret (WInt r)))) -∗
  WP (ERun (hello_close_stream_frame fp) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Q Hgout Hout Hgin Hin Hinr Hfcg Hfcr Hfd0 Hfd He.
  iIntros "#Hvt #Hs Htcb Hf Herr Hio Hlives HE HK".
  unfold hello_close_stream_frame. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_fpending_idle with "Hf"); [reflexivity|].
  iNext. iIntros (n Hn) "Hf". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_ferror_idle with "Hf"); [reflexivity|].
  iNext. iIntros (e He') "Hf". resume. step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_fclose_idle Hreg Hext Hff Hfw Hfh Hzf Hzg Hfc _ pre post fp fd pin pout fcp vb vreg sb sreg eb
    with "Hvt Hs Htcb Hf Herr Hio Hlives"); try first [reflexivity | eassumption].
  iNext. iIntros (k Hk) "Htcb Hio Hlives Hc Herr". resume.
  iAssert Q with "[$Htcb $Hio $Hlives $Herr $Hc $HE]" as "HQ".
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

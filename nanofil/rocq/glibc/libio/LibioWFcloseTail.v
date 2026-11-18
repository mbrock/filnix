(** Once wide stdout has closed its descriptor, fclose removes it from
    the stream list and calls the finish slot in its wide jump table.
    The file finish function sees a closed descriptor and no buffers.
    Fclose then releases the two converters, but keeps the static FILE
    and its wide data for a later flush during error reporting. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  LibioUnlinkCode LibioFcloseCode LibioFinish LibioFcloseTail LibioWIdle LibioWFwide LibioWRelease
  LibioWFcloseRelease Mbrtowc HelloImageLoad HelloImageWFwideObjs HelloImageWReleaseObjs StartImageEarly Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation dq := DfracDiscarded.
Local Abbreviation tw := (rop (img_a "glibc_wcsmbsload#to_wc")).
Local Abbreviation tm := (rop (img_a "glibc_wcsmbsload#to_mb")).
Local Abbreviation reg e s x := (lookup (TAtom s) e = Some x).
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section tail.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}
  `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish)
  (Hunlink : unlink_spec w0 registry ge) (Hunlinked : unlink_unlinked_spec w0 registry ge).

(** Error reporting can flush stdout after fclose returns. To keep the
    wide data for that flush, the caller lends the release functions
    the three pointers they read and takes them back afterward. *)
Local Lemma wide_release_loan vb wd : wide_data vb tw tm wd WbNone -∗ ∃ wr,
  ⌜0 < wd /\ wd mod 8 = 0 /\ wd+232 <= r_end wr /\ r_end wr <= 2^63⌝ ∗
  live wd wr ∗ pcell wd 72 null ∗ pcell wd 104 tw ∗ pcell wd 160 tm ∗
  (live wd wr -∗ pcell wd 72 null -∗ pcell wd 104 tw -∗ pcell wd 160 tm -∗ wide_data vb tw tm wd WbNone).
Proof using Type.
  iIntros "(%wr & %ps & %ib & %ie & %ob & %oe & %ifl & %ic & %ofl & %oc & %sb & %sc & %H & Hw & Hps & Hs & Ha & Hin & Hout & Hsb & Hpad & Hsc & Hvt & Hb)".
  pose proof H as (Hp & Hal & He & Hr & (_ & D & A) & _).
  assert (Ps : ps = replicate 11 null) by (rewrite <-(take_drop 8 ps), A, D; done). subst ps.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _)".
  iDestruct "Hin" as (si Lsi) "[Htw Hin]". iDestruct "Hout" as (so Lso) "[Htm Hout]".
  iExists wr. iSplit; [done|]. iFrame "Hw P9 Htw Htm". iIntros "Hw P9 Htw Htm".
  iExists wr, (replicate 11 null), ib, ie, ob, oe, ifl, ic, ofl, oc, sb, sc. iSplit; [done|].
  iSplitL "Hw"; [iExact "Hw"|]. iSplitL "P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10"; [cbn [replicate big_sepL]; iFrame|].
  iSplitL "Hs"; [iExact "Hs"|]. iSplitL "Ha"; [iExact "Ha"|].
  iSplitL "Htw Hin". { iExists si. iSplit; [done|]. iSplitL "Htw"; [iExact "Htw"|iExact "Hin"]. }
  iSplitL "Htm Hout". { iExists so. iSplit; [done|]. iSplitL "Htm"; [iExact "Htm"|iExact "Hout"]. }
  iFrame "Hsb Hpad Hsc Hvt Hb".
Qed.

(** The wide finish slot names the same file finish function as the
    narrow slot. The positive mode sends the caller to conversion
    cleanup rather than the narrow backup check. Both paths preserve
    the descriptor result that fclose saved before unlinking. *)
Lemma wp_fclose_wide_L8 e from k pre post fb freg fl lb lr sb sr fcp vb vr wd pin Φ :
  reg e "v0" (WPtr (objp fb)) -> reg e "chk0" (WPtr (objp fb)) -> reg e "pr.1" (WInt k) -> 0 <= k < 2^32 ->
  reg (ge_globals ge) "_IO_2_1_stdout_" (objp fb) -> reg (ge_globals ge) "_IO_2_1_stdin_" pin ->
  ptr_addr pin <> fb -> 0 <= ptr_addr pin < 2^64 -> reg (ge_globals ge) "glibc_genops#flush_cleanup" fcp ->
  0 <= ptr_addr fcp < 2^64 -> reg (ge_globals ge) "__gconv_lock" (objp (img_a "__gconv_lock")) ->
  find_fn ge (TAtom "__gconv_release_step") = Some (Defined glibc_gconv_release_step) ->
  0 < fb -> fb mod 8 = 0 -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> 0 < lb ->
  0 <= fl < 2^32 -> has fl io_user_lock = false -> has fl io_linked = true ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ single_ro ge sb sr -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (objp lb) -∗ lock_state lb lr 0 0 null -∗
  io_list_inv ge (pre ++ objp fb :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  int_cell fb off_fileno (2^32-1) -∗ int_cell fb off_mode 1 -∗ pcell fb off_vtable (mkPtr (vb+vt_wfile) (Ro vb)) -∗
  pcell fb off_buf_base null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_wide (objp wd) -∗ pcell fb off_codecvt (mkPtr (wd+104) (Obj wd)) -∗ wide_data vb tw tm wd WbNone -∗
  mbr_tables -∗ ptsq dq hello_wfwide_ps -∗ ptsq dq hello_wrelease_ps -∗ gconv_lock_free -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     live fb freg -∗ int_cell fb off_flags (Z.land fl 4294967167) -∗ pcell fb off_lock (objp lb) -∗ lock_state lb lr 0 0 null -∗
     pcell fb off_vtable (mkPtr (vb+vt_wfile) (Ro vb)) -∗ pcell fb off_wide (objp wd) -∗ wide_data vb tw tm wd WbNone -∗
     gconv_lock_free -∗ Φ (Ret (WInt k))) -∗
  WP (ERun (mkFrame glibc__IO_new_fclose e [] None (Enter (TAtom "L8") (Some from))) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hv Hc Hk Hkr Hout Hin Hne Hpr Hfc Hfcr Hgl Hrel Hfb Hal He Hr Hlb Hfl Hul Hln.
  iIntros "#Hvt #Hwvt #Hs Ht Hl Hfl Hlp Hlk Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 Hwd Hcv Hdata #Hmb #Hfw #Hwr Hgl HK".
  unfold file_size in He. iApply (wp_live_fit1 with "Hl"). iIntros ([? ?]) "Hl".
  step. iApply wp_call_bind; [vx|exact Hunl|reflexivity|]. iNext.
  iApply (Hunlink with "Hs Ht Hl Hfl Hlp Hlk Hio Hlives"); try close_side.
  iNext. iIntros "Ht Hl Hfl Hlp Hlk Hio Hlives _". resume.
  iPoseProof (wvtables_slot ge vb slot_finish "_IO_new_file_finish" with "Hwvt") as "#Hsf"; [cbn; tauto|].
  iAssert (live_capq dq (ptr_cap (sym_ptr ge "_IO_new_file_finish")) vr) as "Hcap".
  { rewrite (ge_fn_cap _ _ _ Hff). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvr) & Hvl & _)". unfold io_vtables_size in Hvend.
  step. check "Hl". iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity|vx|left; reflexivity|a2|a2|cbn; unfold vt_wfile; lia|]. iNext. iIntros "Hl Hvtp _".
  step. step_global Hvg. do 3 step. unfold vt_wfile. norm. replace (vb+840-vb) with 840 by lia. branch. step. step.
  check_read_dq "Hvl" by a2. iNext. iIntros "_". iApply (wp_raw_load_pointer_dq with "Hvl Hsf Hcap");
    [reflexivity|vx|right; reflexivity|a2|a2|apply (ge_fn_addr _ _ _ Hff)|]. iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx|apply (ge_fn_check _ _ _ Hff)|]. iNext.
  iApply wp_raw_call_bind; [vx|apply (ge_fn_cap _ _ _ Hff)|apply (ge_fn_check _ _ _ Hff)|vx|
    apply (ge_fn_find _ _ _ Hff)|reflexivity|reflexivity|]. iNext.
  iDestruct "Hlk" as "(%Hb & Hll & Hb0 & Hb4 & Hbo)". destruct Hb as (Hla & Hle & Hlr).
  iApply (wp_live_fit1 with "Hll"). iIntros ([? ?]) "Hll".
  pose proof (unlink_has fl). assert (0 <= Z.land fl 4294967167 < 2^32) by (apply land_lt32; lia).
  iApply (wp_glibc__IO_new_file_finish_closed Hunlinked with "Hl Hfd Hfl Hbb H80 H96 Hlp Hll"); try close_side.
  iNext. iIntros "Hl _ Hfl _ _ _ Hlp Hll". resume. iDestruct "Hmode" as "[%Hmr Hmode]".
  step. check "Hl". load_s32 "Hl" "Hmode". step. branch.
  iDestruct (wide_release_loan with "Hdata") as (wr (Hp & Ha & Hw & Hlim)) "(Hwl & H72 & H104 & H160 & Hback)".
  iApply (wp_fclose_wide_release with "Hmb Hfw Hwr Hgl Hl Hwd Hcv Hwl H72 H104 H160"); try close_side.
  iNext. iIntros "Hgl Hl Hwd _ Hwl H72 H104 H160". iDestruct ("Hback" with "Hwl H72 H104 H160") as "Hdata".
  iApply ("HK" with "Ht Hio Hlives Hl Hfl Hlp [Hll Hb0 Hb4 Hbo] Hvtp Hwd Hdata Hgl"). iFrame. done.
Qed.
End tail.

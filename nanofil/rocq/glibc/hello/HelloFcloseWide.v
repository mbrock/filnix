(** Hello's diagnostic flushes stdout even when closing stdout failed.
    A wide stdout keeps its wide jump table after the close. This proof
    returns the closed stream that the diagnostic needs, together with
    the result of the flush and descriptor close. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode SysWrappers FileInv FileIdle LibioLogic LibioCloseSteps
  LibioFcloseCode LibioCloseItCode LibioGenCode LibioReadCode LibioUnlinkCode LibioWAllocCode LibioFcloseAcquire
  LibioFcloseTail LibioCloseItEnd LibioFclose LibioFinish LibioUnlink LibioSetb LibioWIdle LibioWRelease
  LibioWOverflowWrite LibioWFwide LibioWCloseItMid LibioWCloseIt LibioWFcloseTail Mbrtowc HelloImageLoad
  HelloImageWFwideObjs HelloImageWReleaseObjs StartImageEarly HelloClosedStdout HelloWClosedStdout Fix.
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

Section fclose.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge)
  (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish)
  `{Hunl : !Defines ge "__GI__IO_un_link" glibc__IO_un_link}
  `{Hpush : !Defines ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer}
  `{Hpop : !Defines ge "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore}
  `{Hdf : !Defines ge "__GI__IO_default_finish" glibc__IO_default_finish}
  `{Hci : !Defines ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink}
  `{Hcn : !Defines ge "__GI___close_nocancel" glibc___close_nocancel}
  `{Hwsb : !Defines ge "__GI__IO_wsetb" glibc__IO_wsetb}
  `{Hsb : !Defines ge "__GI__IO_setb" glibc__IO_setb}
  `{Hum : !Defines ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers}
  `{Hdw : !Defines ge "__GI__IO_wdo_write" wdo_write_fn}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The caller lends the converter any locale state it needs through E.
    Fclose holds the stream lock during conversion and returns both
    that loan and the free conversion lock on success or failure. *)
Lemma wp_fclose_wide fr pre post fp fd pin fcp vb vr sb sr eb (E : iProp Σ) Φ :
  call_frame glibc__IO_new_fclose [WPtr fp] = Some fr ->
  reg (ge_globals ge) "_IO_2_1_stdout_" fp -> reg (ge_globals ge) "_IO_2_1_stdin_" pin ->
  ptr_addr pin <> ptr_addr fp -> 0 <= ptr_addr pin < 2^64 ->
  reg (ge_globals ge) "glibc_genops#flush_cleanup" fcp -> 0 <= ptr_addr fcp < 2^64 ->
  reg (ge_globals ge) "__gconv_lock" (objp (img_a "__gconv_lock")) ->
  reg (ge_globals ge) "glibc_wcsmbsload#to_wc" tw -> reg (ge_globals ge) "glibc_wcsmbsload#to_mb" tm ->
  find_fn ge (TAtom "__gconv_release_step") = Some (Defined glibc_gconv_release_step) ->
  fd <> 0 -> ow_errno w0 = Some (objp eb) ->
  (forall fb freg wd, wclose_write_rule fd vb fb vr freg eb wd tw tm E) ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ single_ro ge sb sr -∗ tcb_cleanup_inv (ow_self w0) -∗
  file_wide ge vb (ow_self w0) fp fd -∗ errno_any eb -∗ E -∗
  mbr_tables -∗ ptsq dq hello_wfwide_ps -∗ ptsq dq hello_wrelease_ps -∗ gconv_lock_free -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2^32-1⌝ -∗ tcb_cleanup_inv (ow_self w0) -∗
     io_list_inv ge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ fb freg lb lr wd, ⌜fp = objp fb /\ fb mod 8 = 0 /\ fb+file_size <= r_end freg /\ r_end freg <= 2^63⌝ ∗
       closed_wide fb freg vb lb lr tw tm wd) -∗ errno_any eb -∗ E -∗ gconv_lock_free -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Ho Hi Hne Hpr Hfcp Hfcpr Hgl Htw Htm Hrel Hfd Herr Hwrite.
  iIntros "#Hvt #Hwv #Hs Ht Hf He HE #Hmb #Hfw #Hwr Hgl Hio Hlives HK".
  iDestruct "Hf" as (fb freg st nb wd w t1 t2 Ok) "(Hl & HF & Hlk & Hb & Hdata)".
  pose proof Ok as (-> & Hal & Hfb & Hfe & Hfrg & F & I & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & _).
  rewrite Htw in T1. rewrite Htm in T2. injection T1 as <-. injection T2 as <-.
  pose proof F as (Hfl & _ & Hfile & _ & Hul & _).
  pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlp0).
  iDestruct "Hlk" as (lb lr L) "Hlk". cbn [with_mode0 fs_lock] in Hlp0. rewrite L in Hlp0. cbn [ptr_addr] in Hlp0, Hne.
  iDestruct "HF" as "(%N & Hfl & Hps & Hfd & Hf2 & Hold & %M & Hcol & Hlp & Hoff & Hcv & Hwd & Hrl & Hrb & Hmode & Htot & Hvtp)".
  rewrite L. iAssert (int_cell fb off_flags (fs_flags st) -∗ pcell fb off_lock (objp lb) -∗ file_fields fb st)%I
    with "[Hps Hfd Hf2 Hold Hcol Hoff Hcv Hwd Hrl Hrb Hmode Htot Hvtp]" as "HF".
  { iIntros "Hfl Hlp". rewrite /file_fields L. by iFrame. }
  iApply (wp_fclose_start Hreg Hext _ _ _ _ _ _ _ _ _ Hfr with "Hs Ht Hl Hfl Hlp Hlk"); try close_side.
  iIntros (e from [Hv Hc]) "Ht Hl Hfl Hlp Hlk". unfold file_size in Hfe.
  iApply (wp_live_fit1 with "Hl"). iIntros ([? ?]) "Hl". iDestruct "Hfl" as "[_ Hfl]".
  unfold has, io_is_filebuf in Hfile. apply negb_true_iff, Z.eqb_neq in Hfile.
  assert (0 <= Z.land (fs_flags st) 8192 < 2^32) by (apply land_lt32; lia).
  step. check "Hl". load_s32 "Hl" "Hfl". step. branch_as false. step.
  iDestruct ("HF" with "[$Hfl //] Hlp") as "HF".
  iApply wp_call_bind; [vx|exact Hci|reflexivity|]. iNext.
  iApply (wp_wclose_it Hreg Hext Hfree Hfc fd vb fb vr freg eb wd tw tm E (Hwrite fb freg wd)
    with "Hvt Hwv He HE Hl HF Hb Hdata"); try assumption; try reflexivity.
  iNext. iIntros (k st' nb' w' (K & L' & Ok')) "He HE Hl HF Hdata". resume.
  pose proof Ok' as (_ & _ & _ & _ & _ & _ & I' & Mode & Vt & _ & _ & _ & Wd & Cv & _).
  unfold widle_ok, with_mode0, fs_ptr in I'. cbn [fs_ptrs fs_flags] in I'.
  destruct I' as (_ & _ & _ & _ & N9 & N11 & _ & _ & _ & _ & _ & _ & Hlinked & _).
  iDestruct "HF" as "(%Len & Hfl & Hps & Hfd & [%F2 Hf2] & _ & _ & _ & Hlp & Hoff & Hcv & Hwd & _ & _ & Hmode & _ & Hvtp)".
  cbn [wclosed_state fs_ptrs fs_flags fs_flags2 fs_lock fs_vtable fs_mode fs_wide fs_codecvt fs_fileno fs_offset] in *.
  rewrite L' L Mode Vt Wd Cv.
  destruct (fs_ptrs st') as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 rest]]]]]]]]]]]]; try discriminate Len.
  cbn in N9, N11. subst p9 p11. iEval (cbn [replicate drop app]) in "Hps".
  iDestruct "Hps" as "(_ & _ & _ & _ & _ & _ & Hbb & _ & _ & H80 & _ & H96 & _)".
  step. check "Hl". load_s32 "Hl" "Hf2". step. step. step. load_s32 "Hl" "Hf2". step. step. step. check "Hl". store_int "Hl" "Hf2". step.
  iDestruct "Hfl" as "[%Hclr Hfl]". assert (Hkr : 0 <= k < 2^32) by (destruct K; lia).
  assert (Cu : Z.land (closed_flags (fs_flags st') mod 2^32) (32768 mod 2^32) mod 2^32 = 0).
  { rewrite (Z.mod_small _ _ Hclr). change (32768 mod 2^32) with 32768. rewrite closed_user_lock. reflexivity. }
  assert (Cl : has (closed_flags (fs_flags st')) io_linked = true).
  { unfold has, io_linked. rewrite closed_linked. exact Hlinked. }
  iPoseProof "Hs" as "((%Hgs & %Hsend) & #Hsl & #Hsb)".
  iDestruct "Hlk" as "(%Bl & Hll & [%L0 Hb0] & [%L4 Hb4] & Hbo)". destruct Bl as (Bla & Ble & Blr).
  iApply (wp_live_fit1 with "Hll"). iIntros ([? ?]) "Hll". iApply (wp_live_fit with "Hsl"). iIntros ([? ?]) "_".
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_rewrite Cu.
  step. load_s32 "Hl" "Hfl". step. step. branch_rewrite Cu.
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hll". step. check "Hll". load_s32 "Hll" "Hb4". step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hll". step. check "Hll". store "Hll" "Hbo".
  check "Hl". load "Hl" "Hlp" "Hll". check "Hll". store_int "Hll" "Hb0". step.
  rewrite (Z.mod_small k (2^32) Hkr). iApply (wp_fclose_wide_L8 Hff
    (wp_glibc__IO_un_link Hreg Hext) wp_glibc__IO_un_link_unlinked
    with "Hvt Hwv Hs Ht Hl [$Hfl //] Hlp [Hll Hb0 Hb4 Hbo] Hio Hlives Hfd Hmode Hvtp Hbb H80 H96 Hwd Hcv Hdata Hmb Hfw Hwr Hgl");
    try close_side; try (unfold has, io_user_lock; rewrite closed_user_lock; reflexivity).
  { iFrame. repeat iSplit; done. }
  iNext. iIntros "Ht Hio Hlives Hl Hfl Hlp Hlk Hvtp Hwd Hdata Hgl". rewrite stdout_closed_flags (Z.mod_small k _ Hkr).
  iApply ("HK" $! k with "[%] Ht Hio Hlives [-He HE Hgl] He HE Hgl"); [exact K|].
  iExists fb,freg,lb,lr,wd. iSplit; [done|]. rewrite /closed_wide /closed_wide_fields. by iFrame.
Qed.
End fclose.

(** Once a wide stream has tried to flush, close_it closes its descriptor
    even if the flush failed. The wide jump table uses the same close
    function as the narrow table. The stream keeps its wide orientation
    and its lock pointer when it drops its two buffers. *)

From Glibc Require Import Unit_io_close_nocancel_os Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_wgenops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry SysWrappers FileInv FileIdle LibioLogic
  LibioCloseSteps LibioGenLeaves LibioSetb
  LibioCloseItEnd LibioCloseItMid LibioCloseItShort LibioWIdle LibioWAllocSetb LibioWCloseItEnd Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

(** The closed FILE retains all fields that close_it does not write.
    In particular its wide jump table, codecvt and lock still point to
    the same objects when fclose unlocks and unlinks it. *)
Definition wclosed_state (st : fstate) : fstate :=
  mkFstate (closed_flags (fs_flags st)) (replicate 8 null ++ drop 8 (fs_ptrs st))
    (2^32-1) (wsetb_flags2 (fs_flags2 st) 0) (fs_old_offset st) (fs_column st) (fs_lock st)
    (2^64-1) (fs_codecvt st) (fs_wide st) (fs_freeres_list st) (fs_freeres_buf st)
    (fs_mode st) (fs_total st) (fs_vtable st).

Section close_it.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge)
  (Hfc : ge_fn ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close)
  `{Hcn : !Defines ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel}
  `{Hwsb : !Defines ge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb}
  `{Hsb : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{Hum : !Defines ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation objp b := (mkPtr b (Obj b)).

Local Definition buffer_to_drop fb fl ob : iProp Σ := LibioSetb.old_base fl ob ∨ short_base fb fl ob.

Local Lemma setb_drops_buffer : setb_spec_with w0 registry ge buffer_to_drop.
Proof using Hfree.
  intros fr fb freg fl ob oe nb ne a Φ Hfr Hfb Hal He Hr Ha.
  iIntros "Hl Hf Hb He [HB|HB] HK".
  - iApply (wp_glibc__IO_setb Hfree with "Hl Hf Hb He HB HK"); done.
  - iApply (short_setb_spec with "Hl Hf Hb He HB HK"); done.
Qed.

Local Lemma wide_narrow_buffer fb nb st : buf_ptrs_ok fb nb (fs_ptrs st) -> wshort_ok nb st ->
  buf_idle nb -∗ buffer_to_drop fb (fs_flags st) (fs_ptr st 6).
Proof using Type.
  intros Hp [_ Hs]. unfold buffer_to_drop, fs_ptr. destruct nb as [| |b sz|b].
  - iIntros "_". iLeft. iLeft. iPureIntro. rewrite <-(take_drop 8 (fs_ptrs st)), app_nth1, Hp; [reflexivity|rewrite Hp; simpl; lia].
  - iIntros "_". iRight. iPureIntro. split; [exact (proj1 Hp)|]. apply Z.eqb_neq, negb_true_iff. exact (proj1 Hs).
  - iIntros "(%r & %xs & %cs & %Hb & Hl & _)". iLeft. iRight. iExists b, r. iFrame.
    destruct Hb as (Hk & Hend & Hr & Hpos & Hal & Hsz & _). iPureIntro. split_and!; try assumption; try lia.
    + exact (proj1 Hp).
    + apply Z.eqb_eq, negb_false_iff. exact (proj1 Hs).
  - iIntros "[]".
Qed.

(** Both outcomes of the flush enter block L18. The close slot may
    return EOF as well. The rule returns both results according to
    glibc's priority and keeps the actual closed FILE for its caller. *)
Lemma wp_wclose_it_L18 e e' from p3 fb freg st nb vb vr eb wd w tw tm Φ :
  (forall b, find_block (TAtom "L18") (fn_blocks Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink) = Some b ->
    phis_env ge (b_phis b) (Some from) e = Some e') ->
  lookup (TAtom "v0") e' = Some (WPtr (objp fb)) -> lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (fb+off_fileno) (Obj fb))) ->
  lookup (TAtom "chk1") e' = Some (WPtr (objp fb)) -> lookup (TAtom "v2") e' = Some (WInt 0) ->
  lookup (TAtom "pr.3") e' = Some (WInt p3) -> 0 <= p3 < 2^32 ->
  0 < fb -> fb mod 8 = 0 -> fb+file_size <= r_end freg -> r_end freg <= 2^63 ->
  fs_mode st = 1 -> fs_vtable st = mkPtr (vb+vt_wfile) (Ro vb) -> fs_wide st = objp wd ->
  fs_ptr st 9 = null -> fs_ptr st 11 = null -> Z.land (fs_flags2 st) 32 = 0 ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> wshort_ok nb st -> wbuf_user_ok w (fs_flags2 st) ->
  ow_errno w0 = Some (objp eb) -> vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ errno_any eb -∗
  live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗ wide_data vb tw tm wd w -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2^32-1⌝ -∗ errno_any eb -∗ live fb freg -∗ file_fields fb (wclosed_state st) -∗
     wide_data vb tw tm wd WbNone -∗ Φ (Ret (WInt (if k =? 0 then p3 else k)))) -∗
  WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink e [] None (Enter (TAtom "L18") (Some from))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hphi Hv Hc Hc1 Hv2 Hp Hp3 Hfb Hal He Hr Hmode Hvtp Hwd E9 E11 Hnc Hbp Hshort Hu Herr.
  iIntros "#Hvt #Hwv Herr Hl HF Hb Hdata HK".
  iDestruct (wide_narrow_buffer with "Hb") as "HB"; [exact Hbp|exact Hshort|].
  iDestruct "HF" as "(%L & Hfl & Hps & Hfd & Hf2 & Ho & %Lc & Hcol & Hlk & Hoff & Hcv & Hwd & Hfr & Hbuf & Hmd & Hwt & Hvtp)".
  unfold fs_ptr in E9, E11. unfold fs_ptr. destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3' [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Eps; try discriminate L.
  cbn [nth] in E9, E11. subst p9 p11. cbn [nth]. rewrite Hmode Hvtp Hwd.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  iDestruct "Hf2" as "[%Hf2 Hf2]". iDestruct "Hfl" as "[%Hfl Hfl]".
  unfold file_size in He. iApply (wp_live_fit1 with "Hl"). iIntros ([? ?]) "Hl".
  iApply wp_enter; [reflexivity|apply Hphi; reflexivity|]. iNext. cbn [b_insts b_jump].
  destruct (unsave_spec_holds fb) as (frm & Hfrm & Hunsave).
  iApply wp_call_bind; [vx|exact Hum|exact Hfrm|]. iNext.
  iApply (Hunsave with "Hl P9 P11"); try close_side. iNext. iIntros "Hl P9 P11". resume.
  step. check "Hl". load_s32 "Hl" "Hf2". do 4 step. rewrite (flags2_mask _ 32 5); [|reflexivity|lia|exact Hf2]. rewrite Hnc. branch.
  iPoseProof (wvtables_slot ge vb slot_close "__GI__IO_file_close" with "Hwv") as "#Hsc"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "__GI__IO_file_close")) vr) as "Hcap".
  { rewrite (ge_fn_cap _ _ _ Hfc). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvr) & Hvl & _)". unfold io_vtables_size in Hvend.
  step. step. check "Hl". iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity|vx|left; reflexivity|a2|a2|cbn; unfold vt_wfile; lia|]. iNext. iIntros "Hl Hvtp _".
  step. step_global Hvg. do 3 step. unfold vt_wfile. norm. replace (vb+840-vb) with 840 by lia. branch. step. step.
  check_read_dq "Hvl" by a2. iNext. iIntros "_". iApply (wp_raw_load_pointer_dq with "Hvl Hsc Hcap");
    [reflexivity|vx|right; reflexivity|a2|a2|apply (ge_fn_addr _ _ _ Hfc)|]. iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx|apply (ge_fn_check _ _ _ Hfc)|]. iNext.
  iApply wp_raw_call_bind; [vx|apply (ge_fn_cap _ _ _ Hfc)|apply (ge_fn_check _ _ _ Hfc)|vx|
    apply (ge_fn_find _ _ _ Hfc)|reflexivity|reflexivity|]. iNext.
  iApply (short_close_spec Hreg Hext with "Hl Hfd Herr"); try close_side. iNext. iIntros (k Hk) "Hl Hfd Herr". resume.
  step. step. step. check "Hl". iDestruct "Hmd" as "[%Hmr Hmd]". load_s32 "Hl" "Hmd". step. branch.
  assert (Hkr : 0 <= k < 2^32) by (destruct Hk; lia). rewrite !(Z.mod_small k (2^32) Hkr).
  iApply (wp_wclose_it_L221 Hfree buffer_to_drop setb_drops_buffer
    with "Hl [$Hf2 //] Hwd Hdata [$Hfl //] Hfd Hoff P0 P1 P2 P3 P4 P5 P6 P7 HB"); try close_side.
  iNext. iIntros "Hl Hf2 Hwd Hdata Hfl Hfd Hoff P0 P1 P2 P3 P4 P5 P6 P7".
  iApply ("HK" $! k with "[%] Herr Hl [-Hdata] Hdata"); [exact Hk|].
  rewrite /file_fields /wclosed_state /= Eps Hmode Hwd Hvtp /=. by iFrame.
Qed.
End close_it.

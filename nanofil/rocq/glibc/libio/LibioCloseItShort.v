(** An empty short buffer can be closed without freeing its containing stream.
    This proof follows the actual close path with USER_BUF set and equal write
    pointers. Nonempty pending output and the surrounding fclose lock/list
    composition remain separate obligations. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Unit_io_close_nocancel_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics OsBlocks OsWorld OsRegistry
  SysWrappers LibioRead LibioDoWrite
  LibioGenLeaves FileInv LibioLogic LibioCloseSteps LibioCloseItEnd LibioCloseItMid
  LibioSetbShort LibioPutsInv.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld
  FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{Hcn : !Defines ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close)
  `{Hsetb : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{Hdwf : !Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The buffer resource is a pure description of an in-object pointer.
    Its lifetime is the stream lifetime already owned by the caller. *)
Definition short_base (fb fl : Z) (ob : ptr) : iProp Σ :=
  ⌜ob = mkPtr (fb + off_shortbuf) (Obj fb) /\ Z.land fl io_user_buf <> 0⌝.

Lemma short_setb_spec : LibioCloseItEnd.setb_spec_with w0 registry ge short_base.
Proof using Type.
  intros fr fb freg fl ob oe nb ne a Φ Hfr Hfb Hal Hend Hreg' Ha.
  iIntros "Hl Hfl Hb He [%Hob %Huser] HK". subst ob.
  iApply (wp_glibc__IO_setb_short with "Hl Hfl Hb He HK"); assumption.
Qed.

Lemma short_close_spec : LibioCloseItMid.close_spec w0 registry ge.
Proof using Hcn Hext Hreg.
  intros fr fb freg fd eb Φ Hfr Hfb Hal Hend Hreg' He.
  exact (LibioRead.wp_glibc__IO_file_close Hreg Hext fr fb freg fd eb Φ
    Hfr Hcn Hfb Hal Hend Hreg' He).
Qed.

(** Equal write pointers make the actual write call return zero without
    accessing the short byte. The descriptor close may still fail. Both
    results preserve the caller's frame E, including any short byte, auxiliary
    capabilities, cleanup resources and remaining stream ownership. *)
Lemma wp_glibc__IO_file_close_short_empty fr fb freg fl f2 fd off md rp re rb we be vb vreg eb
    (E : iProp Σ) Φ :
  let sb := mkPtr (fb + off_shortbuf) (Obj fb) in
  call_frame Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink [WPtr (mkPtr fb (Obj fb)); WInt 0] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= f2 < 2 ^ 32 -> Z.land f2 32 = 0 -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_no_writes = 0 ->
  Z.land fl io_currently_putting <> 0 -> Z.land fl io_user_buf <> 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗
  int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ icell fb off_offset off -∗
  int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ errno_any eb -∗
  pcell fb 8 rp -∗ pcell fb 16 re -∗ pcell fb 24 rb -∗ pcell fb 32 sb -∗ pcell fb 40 sb -∗
  pcell fb 48 we -∗ pcell fb off_buf_base sb -∗ pcell fb off_buf_end be -∗
  pcell fb 80 null -∗ pcell fb 96 null -∗ E -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗
     live fb freg -∗ int_cell fb off_flags (closed_flags fl) -∗ int_cell fb off_flags2 f2 -∗
     int_cell fb off_fileno (2 ^ 32 - 1) -∗ icell fb off_offset (2 ^ 64 - 1) -∗
     int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ errno_any eb -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     pcell fb 80 null -∗ pcell fb 96 null -∗ E -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros sb Hfr. injection Hfr as <-.
  intros Hfb Hfal Hfend Hfreg Hf2r Hf232 Hfdr Hfl Hnw Hcp Hub He Hmd.
  iIntros "#Hvt Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend H80 H96 HE HK".
  unfold file_size in Hfend. unfold sb. unfold io_no_writes in Hnw. unfold io_currently_putting in Hcp.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  assert (0 <= fd < 2 ^ 32) by lia.
  assert (0 <= Z.land fl 8 < 2 ^ 32) by (rewrite Hnw; lia).
  assert (0 <= Z.land fl 2048 < 2 ^ 32) by (apply land_lt32; lia).
  iDestruct "Hfd" as "[_ Hfd]". iDestruct "Hfl" as "[_ Hfl]". iDestruct "Hmode" as "[%Hmr Hmode]".
  step. step. check "Hl". load_s32 "Hl" "Hfd". step. branch_as true.
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. load_s32 "Hl" "Hfl". step. step. step. step. branch_as false.
  step. step. check "Hl". load_s32 "Hl" "Hmode". step.
  assert (Esx : (sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32) <=?
                sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32)) = true)
    by (destruct Hmd as [-> | ->]; reflexivity).
  rewrite Esx. clear Esx. branch.
  step. step. check "Hl".
  load_self_using (wp_raw_load_pointer_self) "Hl Hwb". step.
  load_self_using (wp_raw_load_pointer_self) "Hl Hwp".
  load_self_using (wp_raw_load_pointer_self) "Hl Hwb". step. step. step.
  rewrite Z.sub_diag. change (0 mod 2 ^ 64) with 0.
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  iAssert (int_cell fb off_fileno fd) with "[Hfd]" as "Hfd"; [iSplit; [done | iExact "Hfd"]|].
  iAssert (int_cell fb off_mode md) with "[Hmode]" as "Hmode"; [iSplit; [done | iExact "Hmode"]|].
  iApply wp_call_bind; [vx | exact Hdwf | reflexivity |]. iNext.
  iApply LibioDoWrite.wp_glibc__IO_new_do_write_zero; [reflexivity |]. iNext. resume. step.
  iApply (LibioCloseItMid.wp_close_it_L18_with Hfc short_close_spec short_base short_setb_spec
    Unit_libio_genops_os.fn___GI__IO_unsave_markers LibioGenLeaves.unsave_spec_holds
    with "Hvt Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend [] H80 H96");
    first [intros blk Hblk; vm_compute in Hblk; injection Hblk as <-; reflexivity | try close_side; try exact Hmd].
  { iPureIntro. split; [reflexivity | exact Hub]. }
  iNext. iIntros (k Hk) "Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96".
  assert (Ek : (if k =? 0 then 0 else k) = k) by (destruct Hk as [-> | ->]; reflexivity).
  rewrite Ek. iApply ("HK" $! k with "[%] Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr
    H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96 HE"). exact Hk.
Qed.
End rules.

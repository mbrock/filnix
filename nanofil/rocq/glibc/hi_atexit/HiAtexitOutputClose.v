(** Closing stdout needs its pending bytes and the original heap
    buffer. String output retains both, even when a write fails.
    This bridge supplies the close callback's concrete stream state
    without assuming that the operating system accepted the output. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioOverflowBase LibioDefaultXsputnBuf LibioXsputnBase HiAtexitBase HiAtexitGe
  HiAtexitFclose HiAtexitCloseStdout HiAtexitOutputState.
From Glibc Require FileInv LibioDefaultXsputnBuf LibioFcloseTail LibioLogic LibioOverflowBase LibioXsputnBase LibioXsputnSetp OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.
Import LibioOverflowBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Import LibioXsputnSetp.
Import LibioXsputnBase LibioDefaultXsputnBuf.
Import LibioFcloseTail.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** The callback uses the linked program and its OS registry. *)
Local Instance hi_output_close_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** The output state supplies all fields that closing reads. The
    caller supplies stdout's free lock, its list membership and the
    thread cleanup state; output does not own or invent those resources. *)
Lemma hi_output_close pre post fb freg bb sz wp we eb vb vreg
    lb lbreg sb sreg fcp pin so soreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "stdout") (ge_globals hge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals hge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals hge) = Some pin -> ptr_addr pin <> fb -> 0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals hge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> 0 < lb ->
  vtables_ro hge vb vreg -∗ single_ro hge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live so soreg -∗ pcell so 0 fp -∗ live fb freg -∗
  pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb (Some (bb, sz)) wp we -∗ xfields w0 eb fb (Some (bb, sz)) -∗
  pcell fb 72 null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv hge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ io_list_inv hge (pre ++ post) -∗
     ([∗ list] g ∈ pre ++ post, stream_life g) -∗ Φ RetVoid) -∗
  WP (ERun hi_close_frame : sexpr) {{ Φ }}.
Proof.
  intros fp Hgso Hsoal Hsoend Hgout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Heb Hlb.
  iIntros "Hvt Hs Htcb Hso Hsoc Hl Hvtp Hwb Hxf H72 H80 H96 Hlp Hlk Hio Hlives HK".
  iDestruct "Hxf" as (fl f2 fd tw off md (Happ & Hf22 & Hfd & Hmd & Hflags & Hfd31 & Hf2160))
    "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
  iDestruct (hi_wbuf_to_ovf with "Hwb Hfl Htw Hoff") as (breg xs cs k [Hb8 [Hheap Hlc]]) "[Hst Hcs]".
  iDestruct "Hst" as "(%Hp & Hbl & Hxs & Hfl & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
  destruct Hp as (Hb & Hend & Hregend & Hsz & Hk & Hlx & Hxs & Hwecap & Hweaddr).
  iDestruct "Hfl" as "[%Hflr Hfl]". iDestruct "Hfl2" as "[%Hf2r Hfl2]".
  assert (Hf232 : Z.land f2 32 = 0).
  { replace (Z.land f2 32) with (Z.land (Z.land f2 160) 32) by (rewrite -Z.land_assoc; reflexivity).
    rewrite Hf2160. reflexivity. }
  assert (Hnl : Z.land f2 io_need_lock = 0).
  { replace (Z.land f2 io_need_lock) with (Z.land (Z.land f2 160) io_need_lock)
      by (rewrite -Z.land_assoc; reflexivity). rewrite Hf2160. reflexivity. }
  pose proof (xs_flags_mask _ _ io_no_writes eq_refl Hflags) as Hnw.
  pose proof (xs_flags_mask _ _ io_user_buf eq_refl Hflags) as Hub.
  pose proof (xs_flags_mask _ _ io_user_lock eq_refl Hflags) as Hul.
  pose proof (xs_flags_mask _ _ io_linked eq_refl Hflags) as Hlinked.
  pose proof (xs_flags_mask _ _ io_is_filebuf eq_refl Hflags) as Hfile.
  assert (Htake : Z.of_nat (length (take (Z.to_nat k) xs)) = k).
  { rewrite length_take_le; lia. }
  iAssert (bytes bb 0 (take (Z.to_nat k) xs ++ drop (Z.to_nat k) xs)) with "[Hxs]" as "Hxs".
  { rewrite take_drop. iExact "Hxs". }
  iEval (rewrite bytes_app) in "Hxs".
  iDestruct "Hxs" as "[Hpending Hrest]".
  replace (mkPtr bb (Obj bb)) with (mkPtr (bb + 0) (Obj bb)) by (f_equal; lia).
  replace (mkPtr (bb + k) (Obj bb)) with (mkPtr (bb + 0 + Z.of_nat (length (take (Z.to_nat k) xs))) (Obj bb))
    by (f_equal; lia).
  iEval (rewrite Z.add_0_r) in "Hbase".
  iApply (wp_hi_close_stdout w0 pre post fb freg fl f2 fd tw off bb breg 0 (take (Z.to_nat k) xs)
    (mkPtr (bb + 0) (Obj bb)) (mkPtr (bb + 0) (Obj bb)) we (mkPtr (bb + sz) (Obj bb)) eb vb vreg
    lb lbreg sb sreg fcp pin md so soreg with
    "Hvt Hs Htcb Hso Hsoc Hl [$Hfl //] [$Hfl2 //] Hfdc Htw Hoff Hbl Hpending Herr
     Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives HK");
    try assumption.
  - exact (proj2 Hflags).
  - unfold has. rewrite Hul. reflexivity.
  - unfold has. rewrite Hlinked. reflexivity.
  - unfold has. rewrite Hfile. reflexivity.
  - lia.
  - lia.
  - apply Forall_take. exact Hxs.
  - cbn [ptr_addr]. lia.
  - reflexivity.
Qed.

End rules.

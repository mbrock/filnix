(** A successful allocation changes which idle-stream facts the next
    caller needs. A stream with no buffer was not writing; a stream
    with a heap buffer is writing, owns the allocation, and keeps its
    read and write bases at the start of that allocation. These facts
    also hold when the write reports an error. *)

From Stdlib Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import GlibcProgram FileInv FileIdle FileTidy LibioPutsInv PrintfStreamInv PrintfStreamHeap
  OsBlocks LibioSetb LibioOverflowBase LibioOverflowAllocSetg LibioOverflowHeapStart LibioOverflowHeapBuffer LibioDefaultXsputnBuf.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv.
Open Scope Z_scope.

(** Only an absent or heap-allocated buffer belongs to a buffered
    stream. The write-buffer predicate distinguishes these two cases
    by the presence of a base and a size. *)
Definition heap_kind (nb : option (Z * Z)) := match nb with None => NbNone | Some (b,s) => NbHeap b s end.

(** A flag outside the four bits the allocation and write may touch
    keeps its old value. *)
Lemma heap_flags_mask nb fl fl' m : heap_overflow_flags nb fl fl' ->
  Z.land 4294967294 m = m -> Z.land io_line_buf m = 0 -> Z.land 2048 m = 0 -> Z.land io_err_seen m = 0 ->
  Z.land fl' m = Z.land fl m.
Proof.
  destruct nb; cbn [heap_overflow_flags]; intros (v & Hv & [->| ->]) Hu Hl Hp He;
    try rewrite (land_lor_const _ _ _ He); destruct Hv as [H| ->];
    try destruct H as [-> _]; try subst v; repeat rewrite (land_lor_const _ _ _ Hp);
    rewrite ?(setb1_land _ _ Hu) ?(land_lor_const _ _ _ Hl); reflexivity.
Qed.

(** The first allocation clears USER_BUF even if it was set beforehand.
    A later write preserves that bit. Both paths leave PUTTING set. *)
Lemma heap_flags_owned nb fl fl' : heap_overflow_flags nb fl fl' ->
  (nb <> None -> has fl io_user_buf = false) -> has fl' io_user_buf = false /\ has fl' io_currently_putting = true.
Proof.
  destruct nb as [p|]; cbn [heap_overflow_flags]; intros (v & Hv & [->| ->]) Hu; unfold has in *;
    try rewrite (land_lor_const _ io_err_seen io_user_buf eq_refl);
    try rewrite (land_lor_const _ io_err_seen io_currently_putting eq_refl).
  1,2: destruct Hv as [[-> Hput]| ->]; split; try apply Hu; try discriminate;
    try (apply Bool.negb_true_iff, Z.eqb_neq; exact Hput);
    try (rewrite (land_lor_const _ 2048 io_user_buf eq_refl); apply Hu; discriminate).
  all: try split; try (rewrite (land_lor_const _ 2048 io_user_buf eq_refl); unfold setb_flags;
    cbn [Z.eqb]; rewrite -Z.land_assoc; change (Z.land 4294967294 io_user_buf) with 0; rewrite Z.land_0_r; reflexivity).
  all: apply Bool.negb_true_iff, Z.eqb_neq; rewrite Z.land_lor_distr_l;
    intro H; apply Z.lor_eq_0_iff in H; destruct H as [_ H]; discriminate.
Qed.

(** The result records the fields that changed and the exact heap
    allocation. The mode may already have changed in the outer wrapper;
    the jump-table entry itself preserves the mode it receives. *)
Lemma heap_after_idle st nb fd fb bb sz k we fl tw off mode :
  let st' := heap_file_state (fs_with_mode st mode) bb sz k we fl tw off in
  flags_ok st -> idle_ok fd (fs_with_flags2 st 0) -> short_idle (heap_kind nb) st ->
  has (fs_flags st) io_unbuffered = false -> has (fs_flags st) io_no_writes = false ->
  heap_overflow_flags nb (fs_flags st) fl -> 0 <= fl < 2^32 -> (mode = 0 \/ mode = 2^32-1) ->
  0 <= k <= sz -> LibioDefaultXsputnBuf.in_buf bb sz we ->
  flags_ok st' /\ idle_ok fd (fs_with_flags2 st' 0) /\ short_idle (NbHeap bb sz) st' /\ buf_ptrs_ok fb (NbHeap bb sz) (fs_ptrs st').
Proof.
  cbn zeta. intros Hok Hi Hshort Hu Hnw Hflags Hrange Hmd Hk [Hwec Hwea].
  pose proof (heap_flags_owned _ _ _ Hflags ltac:(destruct nb as [[b s]|]; [destruct Hshort as (_ & _ & _ & _ & Huser & _); auto|tauto])) as [Huser Hput].
  assert (E : forall m, Z.land 4294967294 m = m -> Z.land io_line_buf m = 0 -> Z.land 2048 m = 0 ->
    Z.land io_err_seen m = 0 -> has fl m = has (fs_flags st) m) by (intros; unfold has; rewrite (heap_flags_mask _ _ _ _ Hflags) //).
  assert (Hu' : has fl io_unbuffered = false) by (rewrite E; auto; reflexivity).
  assert (Hnw' : has fl io_no_writes = false) by (rewrite E; auto; reflexivity).
  unfold flags_ok, idle_ok, short_idle, heap_file_state, fs_with_flags2, fs_with_mode, fs_ptr in *.
  cbn [fs_flags fs_flags2 fs_ptrs fs_fileno fs_mode fs_lock fs_column nth] in *.
  decompose [and] Hi. decompose [and] Hok.
  split_and!; try solve [assumption | reflexivity | lia | rewrite E; auto; reflexivity |
    rewrite (heap_flags_mask _ _ _ _ Hflags); auto; reflexivity | congruence | intros; assumption].
  - cbn; lia.
  - clear - Hk Hwec Hwea. unfold buf_ptrs_ok. cbn [nth take]. split_and!; try reflexivity.
    repeat constructor; cbn; first [assumption | lia].
Qed.

Section fields.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Overflow borrows the buffer, counters and fixed fields. The caller
    keeps the rest of the stream, including the six bytes after the
    column counter. Returning the borrowed fields rebuilds the stream
    and accounts for every capability slot in its heap buffer. *)
Lemma heap_fields fb st nb vb eb :
  let fd := fs_fileno st in let fl := fs_flags st in let f2 := fs_flags2 st in
  flags_ok st -> idle_ok fd (fs_with_flags2 st 0) -> short_idle (heap_kind nb) st ->
  buf_ptrs_ok fb (heap_kind nb) (fs_ptrs st) -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  has fl io_unbuffered = false -> has fl io_no_writes = false ->
  file_fields fb st -∗ buf_idle (heap_kind nb) -∗ errno_any eb -∗
  wbuf fb nb (fs_ptr st 4) (fs_ptr st 5) ∗ ovf_fixed fb f2 fd eb (fs_mode st) vb ∗
  int_cell fb off_flags fl ∗ icell fb off_total_written (fs_total st) ∗ icell fb off_offset (fs_offset st) ∗
  (∀ bb sz k we fl' tw' off' m, let st' := heap_file_state (fs_with_mode st m) bb sz k we fl' tw' off' in
    ⌜heap_overflow_flags nb fl fl' /\ (m = 0 \/ m = 2^32-1)⌝ -∗
    wbuf fb (Some (bb,sz)) (mkPtr (bb+k) (Obj bb)) we -∗ ovf_fixed fb f2 fd eb m vb -∗
    int_cell fb off_flags fl' -∗ icell fb off_total_written tw' -∗ icell fb off_offset off' -∗
    ⌜flags_ok st' /\ idle_ok fd (fs_with_flags2 st' 0) /\ short_idle (NbHeap bb sz) st' /\ buf_ptrs_ok fb (NbHeap bb sz) (fs_ptrs st')⌝ ∗
    file_fields fb st' ∗ buf_idle (NbHeap bb sz) ∗ errno_any eb).
Proof using Type.
  cbn zeta. intros Hok Hi Hshort Hb Hvt Hu Hnw.
  iIntros "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htw & Hvt) Hb Herr".
  assert (Hcol : take 2 (fs_column st) = [0;0]) by (unfold idle_ok in Hi; tauto).
  assert (H01 : fs_ptr st 0 = fs_ptr st 1) by (unfold idle_ok in Hi; tauto).
  assert (H13 : fs_ptr st 1 = fs_ptr st 3) by (unfold idle_ok in Hi; tauto).
  pose proof (buf_ptrs_in _ _ _ 4 Hb Hlen ltac:(lia)) as H4. pose proof (buf_ptrs_in _ _ _ 5 Hb Hlen ltac:(lia)) as H5.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps; try discriminate Hlen.
  unfold fs_ptr in H01, H13 |- *. rewrite Hps in H01, H13 |- *. cbn [nth] in H01, H13, H4, H5 |- *.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  iSplitL "P0 P1 P2 P3 P4 P5 P6 P7 Hb".
  { destruct nb as [[bb sz]|]; cbn [heap_kind] in *.
    - destruct Hshort as (_ & _ & H26 & H36 & _). unfold fs_ptr in H26, H36. rewrite Hps in H26, H36. cbn [nth] in H26, H36.
      destruct Hb as (H6 & H7 & _). cbn [nth] in H6, H7. subst p0 p1 p2 p3 p6 p7.
      iDestruct "Hb" as (br xs cs (Hheap & Hend & Hr & Hbb & Hal & Hsz & Hlenx & Hxs & Hlenc)) "(Hl & Hxs & Hcs)".
      unfold wbuf, wcells. cbn [nb_base nb_end]. iFrame. iPureIntro. unfold room_ok. tauto.
    - injection Hb as -> -> -> -> -> -> -> ->. unfold wbuf, wcells. cbn [nb_base nb_end wroom].
      iFrame "P0 P1 P2 P3 P4 P5 P6 P7". done. }
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol bytes_app) in "Hcol". iDestruct "Hcol" as "[Hcol Htail]".
  iEval (rewrite Hvt) in "Hvt". iFrame "Hfl Htw Hoff Hfd Hf2 Herr Hcol Hmd Hvt".
  iIntros (bb sz k we fl' tw' off' m [Hflags Hm]) "((P0 & P1 & P2 & P3 & P6 & P7) & P4 & P5 & Hroom) (Hf2 & Hfd & $ & Hcol & Hmd & Hvt) [%Hrange Hfl] Htw Hoff".
  iDestruct "Hroom" as (br xs cs (Hbb & Hal & Hsz & Hend & Hr & Hlenx & Hlenc & Hxs & [_ Hk] & Hwe & Hheap)) "(Hl & Hxs & Hcs)".
  iSplit. { iPureIntro. eapply (heap_after_idle st nb); try assumption. cbn in Hk; lia. }
  iSplitR "Hl Hxs Hcs"; last first.
  { iExists br, xs, cs. iFrame. iPureIntro. tauto. }
  unfold heap_file_state, fs_with_mode, file_fields, fs_ptr. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
    fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable]. rewrite Hps Hvt. cbn [nth big_opL].
  iFrame "Hfd Hf2 Hold Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htw Hvt P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11".
  iSplit; [done|]. iSplitL "Hfl"; [iFrame; done|]. iSplit; [done|].
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol bytes_app). iFrame.
Qed.
End fields.

(** Printf may need to write a byte when its stream buffer is full.
    To send the buffered bytes safely, glibc needs a valid open descriptor
    and pointers within the same allocation. This file describes streams
    that have already begun writing into a heap buffer without append mode.

    The stream keeps its cancellation flags and recursive lock count across
    the call. This view separates fields that overflow changes from fields
    it leaves alone. It supports heap buffers only; it does not describe
    allocation or buffers stored inside FILE. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioOverflowBase PrintfStreamInv.
Import ListNotations.
Open Scope Z_scope.

(** The heap view shares the caller's runtime and memory interpretation. *)
Module PrintfStreamHeapOn (R : Runtime) (LG0 : LogicSig R).
Module PS := PrintfStreamInvOn R LG0.
Module OB := LibioOverflowBaseOn R LG0.
Import PS PS.PI PS.PI.CS.SW.FI PS.PI.CS.SW.FI.ML PS.PI.CS.SW.FI.LG PS.PI.CS.SW.FI.L.

(** Overflow changes the first eight pointers, flags, offset and byte count.
    The remaining fields keep their values from the surrounding stream. *)
Definition heap_file_state (st : fstate) (bb sz k : Z) (we : ptr) (fl tw off : Z) : fstate :=
  mkFstate fl
    [mkPtr bb (Obj bb); mkPtr bb (Obj bb); mkPtr bb (Obj bb); mkPtr bb (Obj bb);
     mkPtr (bb + k) (Obj bb); we; mkPtr bb (Obj bb); mkPtr (bb + sz) (Obj bb);
     fs_ptr st 8; fs_ptr st 9; fs_ptr st 10; fs_ptr st 11]
    (fs_fileno st) (fs_flags2 st) (fs_old_offset st) (fs_column st) (fs_lock st) off
    (fs_codecvt st) (fs_wide st) (fs_freeres_list st) (fs_freeres_buf st) (fs_mode st) tw
    (fs_vtable st).

(** Marking a write error changes none of the flags used by the stream invariant. *)
Lemma heap_file_flags_error st bb sz k we fl tw off :
  flags_ok (heap_file_state st bb sz k we fl tw off) ->
  flags_ok (heap_file_state st bb sz k we (Z.lor fl io_err_seen) tw off).
Proof.
  unfold flags_ok, heap_file_state. cbn [fs_flags fs_flags2].
  intros (Hfl & Hmagic & Hfile & Hbackup & Huser & Hneed & Hunbuf).
  split; [apply lor_lt32; [exact Hfl | unfold io_err_seen; lia]|].
  unfold has in *. rewrite !Z.land_lor_distr_l.
  change (Z.land io_err_seen 4294901760) with 0.
  change (Z.land io_err_seen io_is_filebuf) with 0.
  change (Z.land io_err_seen io_in_backup) with 0.
  change (Z.land io_err_seen io_user_lock) with 0.
  change (Z.land io_err_seen io_unbuffered) with 0.
  change (Z.land io_err_seen io_user_buf) with 0.
  rewrite !Z.lor_0_r. tauto.
Qed.

Section streams.
Context `{!gen_heapGS piece pval Σ}.

(** Overflow leaves these fields and the caller's exact lock state untouched.
    The first two column bytes belong to the write proof; the rest stay here. *)
Definition heap_file_tail (fb : Z) (self : ptr) (held : option Z) (st : fstate)
    (col : list Z) : iProp Σ :=
  pcell fb 72 (fs_ptr st 8) ∗ pcell fb 80 (fs_ptr st 9) ∗
  pcell fb 88 (fs_ptr st 10) ∗ pcell fb 96 (fs_ptr st 11) ∗
  icell fb off_old_offset (fs_old_offset st) ∗ bytes fb (off_column + 2) col ∗
  pcell fb off_lock (fs_lock st) ∗ lock_inv self (fs_lock st) held ∗
  pcell fb off_codecvt (fs_codecvt st) ∗ pcell fb off_wide (fs_wide st) ∗
  pcell fb off_freeres_list (fs_freeres_list st) ∗ pcell fb off_freeres_buf (fs_freeres_buf st).

(** An IO-ready heap stream owns all ordinary stream fields and buffer bytes.
    Its extra facts justify the already-writing, nonappend backend path.
    Errno remains separate because writes may change its value. *)
Definition printf_heap_stream (w0 : os_world) (vb : Z) (self fp : ptr)
    (mode flags2 : Z) (held : option Z) : iProp Σ :=
  ∃ fb freg st bb breg sz k we xs fl tw off col,
    ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\
      fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ r_kind breg = Heap /\
      fs_mode st = mode /\ (mode = 0 \/ mode = 2 ^ 32 - 1) /\ fs_flags2 st = flags2 /\
      fs_vtable st = mkPtr (vb + vt_file) (Ro vb) /\ fs_column st = [0; 0] ++ col /\
      length col = 6%nat /\ In (fs_fileno st) (ow_fds w0) /\
      Z.land fl io_is_appending = 0 /\ Z.land fl io_no_writes = 0 /\
      Z.land fl io_currently_putting <> 0 /\
      flags_ok (heap_file_state st bb sz k we fl tw off)⌝ ∗
    live fb freg ∗ OB.ovf_state fb bb breg sz k we xs fl tw off ∗
    int_cell fb off_flags2 flags2 ∗ int_cell fb off_fileno (fs_fileno st) ∗
    bytes fb off_column [0; 0] ∗ int_cell fb off_mode mode ∗
    pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗ heap_file_tail fb self held st col.

(** A caller can borrow the FILE lifetime for its checked pointer load.
    The closing wand requires the same token before any stream call proceeds. *)
Lemma printf_heap_stream_live w0 vb self fp mode flags2 held :
  printf_heap_stream w0 vb self fp mode flags2 held -∗
  ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗
    (live_capq dq (ptr_cap fp) reg -∗ printf_heap_stream w0 vb self fp mode flags2 held).
Proof.
  iIntros "(%fb & %freg & %st & %bb & %breg & %sz & %k & %we & %xs & %fl & %tw & %off & %col & %Hp & Hl & Hrest)".
  pose proof Hp as (Hfp & _). subst fp.
  iExists (DfracOwn 1%Qp), freg. iFrame "Hl". iIntros "Hl".
  iExists fb, freg, st, bb, breg, sz, k, we, xs, fl, tw, off, col. iFrame. done.
Qed.

(** The stronger heap view returns an ordinary diagnostic stream with the
    same mode, cancellation flags and held count. This implication does not
    promise that a write succeeds or that errno keeps its old value. *)
Lemma printf_heap_stream_forget w0 vb self fp mode flags2 held :
  printf_heap_stream w0 vb self fp mode flags2 held -∗
  printf_stream vb self fp mode flags2 held.
Proof.
  iIntros "(%fb & %freg & %st & %bb & %breg & %sz & %k & %we & %xs & %fl & %tw & %off & %col & %Hp &
    Hl & Hst & Hf2 & Hfd & Hcol0 & Hmd & Hvt & Htail)".
  destruct Hp as (Hfp & Hfb & Hal & Hend & Hreg & Hheap & Hmode & Hnarrow & Hflags2 & Hvt & Hcolumn &
    Hcol & Hfd & Happ & Hnw & Hput & Hok).
  iDestruct "Hst" as "(%Hb & Hbl & Hxs & Hfl & Htw & Hoff & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
  destruct Hb as (Hbb & Hbend & Hbreg & Hsz & Hk & Hxslen & Hbytes & Hwecap & Hweaddr).
  iDestruct "Htail" as "(H8 & H9 & H10 & H11 & Hold & Hcol1 & Hlp & Hlk & Hcv & Hwd & Hfrl & Hfrb)".
  iExists fb, freg, (heap_file_state st bb sz k we fl tw off), (NbHeap bb sz), vt_file.
  iSplitR.
  { iPureIntro. cbn [heap_file_state fs_flags fs_ptrs fs_fileno fs_flags2 fs_mode fs_vtable].
    split_and!; try assumption.
    - left. tauto.
    - unfold buf_ptrs_ok. cbn [nth take]. split; [reflexivity|]. split; [reflexivity|].
      repeat constructor; cbn [ptr_cap ptr_addr]; try assumption; lia. }
  iFrame "Hl Hlk".
  iSplitL "Hfl H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hfd Hf2 Hold Hcol0 Hcol1 Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htw Hvt".
  - unfold file_fields, heap_file_state.
    cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
      fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable big_opL length].
    rewrite Hmode Hflags2 Hvt Hcolumn.
    iFrame. iSplit; [done|]. iSplit; [iPureIntro; rewrite length_app; cbn; lia|].
    rewrite bytes_app. cbn [length]. iFrame.
  - iExists breg, xs. iFrame. iPureIntro. tauto.
Qed.

End streams.
End PrintfStreamHeapOn.

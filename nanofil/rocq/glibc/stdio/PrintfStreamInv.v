(** Diagnostic formatting temporarily changes a stream's cancellation flags and
    takes its recursive lock. Its caller needs both values back on return.
    This module retains the original flags alongside the mode and lock count
    already exposed by the stream's [[separation logic]] invariant.

    These ownership lemmas do not prove a formatting call or a cleanup call.
    In particular, forgetting the flags does not release a held lock. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv LibioPutsInv.
Import ListNotations.
Open Scope Z_scope.

(** The refinement uses the caller's existing runtime and heap interpretation. *)
Module PrintfStreamInvOn (R : Runtime) (LG0 : LogicSig R).
Module PI := LibioPutsInvOn R LG0.
Import PI PI.CS.SW.FI PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L.

(** Updating flags2 leaves the stream's orientation, buffer and lock pointer unchanged. *)
Definition fs_with_flags2 (st : fstate) (flags2 : Z) : fstate :=
  mkFstate (fs_flags st) (fs_ptrs st) (fs_fileno st) flags2 (fs_old_offset st) (fs_column st)
    (fs_lock st) (fs_offset st) (fs_codecvt st) (fs_wide st) (fs_freeres_list st) (fs_freeres_buf st)
    (fs_mode st) (fs_total st) (fs_vtable st).

Section streams.
Context `{!gen_heapGS piece pval Σ}.

(** A diagnostic stream records the exact flags2 value and recursive lock state.
    Its buffer and jump table satisfy the existing stream invariant unchanged. *)
Definition printf_stream (vb : Z) (self fp : ptr) (mode flags2 : Z)
    (held : option Z) : iProp Σ :=
  ∃ fb freg st nb vt_off, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\ fs_mode st = mode /\
     mode_vtable mode vt_off /\ fs_vtable st = mkPtr (vb + vt_off) (Ro vb) /\
     buf_ptrs_ok fb nb (fs_ptrs st) /\ fs_flags2 st = flags2⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) held ∗ buf_own nb.

(** Hiding the saved cancellation flags preserves the exact mode and held count. *)
Lemma printf_stream_forget vb self fp mode flags2 held :
  printf_stream vb self fp mode flags2 held -∗ file_at vb self fp mode held.
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  iExists fb, freg, st, nb, vt. iFrame. iPureIntro. tauto.
Qed.

(** Every existing stream has some flags2 value that this refinement can retain.
    Choosing that value does not add ownership or impose a new restriction. *)
Lemma file_at_printf_stream vb self fp mode held :
  file_at vb self fp mode held ⊣⊢ ∃ flags2, printf_stream vb self fp mode flags2 held.
Proof.
  iSplit.
  - iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
    iExists (fs_flags2 st), fb, freg, st, nb, vt. iFrame. iPureIntro. tauto.
  - iIntros "(%flags2 & Hf)". iApply (printf_stream_forget with "Hf").
Qed.

(** A lock operation can borrow the stream's lock while the caller keeps every
    other field. Closing this view records the resulting lock state exactly. *)
Lemma printf_stream_lock vb self fp mode flags2 held :
  printf_stream vb self fp mode flags2 held -∗
  ∃ lp, lock_inv self lp held ∗
    (∀ held', lock_inv self lp held' -∗ printf_stream vb self fp mode flags2 held').
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  iExists (fs_lock st). iFrame "Hk". iIntros (held') "Hk".
  iExists fb, freg, st, nb, vt. iFrame. done.
Qed.

(** A flags update borrows the exact four bytes and the stream's life token.
    It must retain the existing need-lock restriction; it cannot release the lock. *)
Lemma printf_stream_flags2 vb self fp mode flags2 held :
  printf_stream vb self fp mode flags2 held -∗
  ∃ fb freg, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
    fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
    live fb freg ∗ int_cell fb off_flags2 flags2 ∗
    (∀ flags2', ⌜Z.land flags2' io_need_lock = 0⌝ -∗ live fb freg -∗
      int_cell fb off_flags2 flags2' -∗ printf_stream vb self fp mode flags2' held).
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  destruct Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hok & Hm & Hmv & Hvt & Hbok & Hf2).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hflags2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd &
    Hfrl & Hfrb & Hmd & Htot & Hvtp)".
  iExists fb, freg. rewrite Hf2. iFrame "Hl Hflags2".
  iSplitR; [iPureIntro; tauto|]. iIntros (flags2' Hmask) "Hl Hflags2".
  iExists fb, freg, (fs_with_flags2 st flags2'), nb, vt.
  unfold fs_with_flags2, file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable].
  iSplitR; [iPureIntro; unfold flags_ok in *; cbn [fs_flags fs_flags2]; tauto|].
  iFrame. iSplit; done.
Qed.

(** Buffer selection reads FILE's write pointers without changing the stream.
    Two shares of its existing lifetime also cover storage inside FILE.
    The closing loan retains all bytes, including the inline byte at offset 131.
    Heap storage remains owned inside the loan; this rule lends no heap lifetime
    and does not establish a heap buffer's positivity or alignment. *)
Lemma printf_stream_selection vb self fp mode flags2 held :
  printf_stream vb self fp mode flags2 held -∗
  ∃ fb freg nb wp we, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
    fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\
    in_buf fb nb wp /\ in_buf fb nb we⌝ ∗
    liveq (DfracOwn (1 / 2)) fb freg ∗ liveq (DfracOwn (1 / 2)) fb freg ∗
    pcell fb off_write_ptr wp ∗ pcell fb off_write_end we ∗
    (liveq (DfracOwn (1 / 2)) fb freg -∗ liveq (DfracOwn (1 / 2)) fb freg -∗
      pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗
      printf_stream vb self fp mode flags2 held).
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  pose proof Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hok & Hm & Hmv & Hvt & Hbok & Hf2).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hflags2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd &
    Hfrl & Hfrb & Hmd & Htot & Hvtp)".
  destruct st as [fl ps fd f2 old col lk off cv wd frl frb md tot vtp]; cbn [fs_ptrs fs_column] in *.
  destruct ps as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]];
    try discriminate Hlen.
  pose proof (buf_ptrs_in fb nb _ 4 Hbok eq_refl ltac:(lia)) as Hw.
  pose proof (buf_ptrs_in fb nb _ 5 Hbok eq_refl ltac:(lia)) as He. cbn [nth] in Hw, He.
  iDestruct "Hps" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _)".
  iDestruct (live_halves with "Hl") as "[Hl1 Hl2]".
  iExists fb, freg, nb, p4, p5. iFrame "Hl1 Hl2 H4 H5".
  iSplitR; [iPureIntro; tauto|]. iIntros "Hl1 Hl2 H4 H5".
  iCombine "Hl1 Hl2" as "Hl". rewrite -live_halves.
  iExists fb, freg, (mkFstate fl [p0; p1; p2; p3; p4; p5; p6; p7; p8; p9; p10; p11]
    fd f2 old col lk off cv wd frl frb md tot vtp), nb, vt.
  iSplitR; [done|]. unfold file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable big_opL length].
  iFrame "Hl Hk Hb Hfl H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hfd Hflags2 Hold Hcol Hlp Hoff
    Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp". iSplit; done.
Qed.

End streams.
End PrintfStreamInvOn.

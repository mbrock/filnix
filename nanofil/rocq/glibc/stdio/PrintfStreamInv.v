(** Diagnostic formatting temporarily changes a stream's cancellation flags and
    takes its recursive lock. Its caller needs both values back on return.
    This module retains the original flags alongside the mode and lock count
    already exposed by the stream's [[separation logic]] invariant.

    These ownership lemmas do not prove a formatting call or a cleanup call.
    In particular, forgetting the flags does not release a held lock. *)
From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv LibioPutsInv.
From Glibc Require FileInv LibioPutsInv.
From Glibc Require Import Fix.
Open Scope Z_scope.


Import LibioPutsInv FileInv FileInv.ML FileInv.LG FileInv.L.

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
  iFrame "Hl Hk Hb Hfl Hps Hfd Hflags2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp". iSplit; done.
Qed.

End streams.

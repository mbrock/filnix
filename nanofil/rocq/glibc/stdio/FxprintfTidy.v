(** When getopt reports a bad option, glibc prints the message with
    `c: __fxprintf_nocancel`. That function locks the stream, checks
    that the stream is not wide, and then calls the formatter to write
    the text. Hello keeps its streams idle between calls, and the
    formatter's contract gives a stream back in a form that does not
    say whether it is narrow yet. This file adds that one fact to the
    stream, so that the proof of the locking function can check it, and
    it lends the few fields that the locking function touches. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import Fix FileInv FileIdle PrintfStreamInv FileTidy.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section fx_stream.
Context `{!gen_heapGS piece pval Σ}.

(** ## The stream as the wrapper sees it

    The wrapper's callers hold the stream as [file_tidy], which hides
    the stream's orientation. The wrapper reads that orientation, and a
    caller that prints twice may want to know it, so the predicate
    [fx_stream] names it as the parameter mode. Otherwise it owns the
    stream exactly as [file_tidy] does. *)
Definition fx_stream (vb : Z) (self fp : ptr) (fd mode flags2 : Z) (held : option Z) : iProp Σ :=
  ∃ fb freg st nb, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\
     idle_ok fd (fs_with_flags2 st 0) /\ fs_flags2 st = flags2 /\
     fs_vtable st = mkPtr (vb + vt_file) (Ro vb) /\ buf_ptrs_ok fb nb (fs_ptrs st) /\ fs_mode st = mode /\
     short_idle nb st⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) held ∗ buf_idle nb ∗
    wide_idle vb (fs_wide st) (fs_codecvt st).

(** A tidy stream is a stream of the wrapper's view at its current
    mode, and naming the mode loses nothing. *)
Lemma file_tidy_fx_stream vb self fp fd flags2 held :
  file_tidy vb self fp fd flags2 held ⊣⊢ ∃ mode, fx_stream vb self fp fd mode flags2 held.
Proof using Type.
  iSplit.
  - iIntros "(%fb & %freg & %st & %nb & %Hp & H)". iExists (fs_mode st), fb, freg, st, nb.
    iFrame "H". iPureIntro. tauto.
  - iIntros "(%mode & %fb & %freg & %st & %nb & %Hp & H)". iExists fb, freg, st, nb.
    iFrame "H". iPureIntro. tauto.
Qed.

(** The mode of such a stream is 0, no orientation yet, or -1 as a
    32-bit word, narrow. It is never wide. *)
Lemma fx_stream_mode vb self fp fd mode flags2 held :
  fx_stream vb self fp fd mode flags2 held ⊢ ⌜mode = 0 \/ mode = 2 ^ 32 - 1⌝.
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & _)". iPureIntro.
  destruct Hp as (_ & _ & _ & _ & _ & _ & (_ & _ & Hm & _) & _ & _ & _ & <- & _). exact Hm.
Qed.

(** The locking function reads the stream's flags and mode, sets and
    restores a bit in its second flags word, and takes and releases its
    lock. It needs only those cells and the stream's lifetime, so this
    lemma lends exactly them. When the caller gives them back, the
    second flags word and the lock may hold new values, and the rest of
    the stream is as it was. *)
Lemma fx_stream_fx vb self fp fd mode flags2 held :
  fx_stream vb self fp fd mode flags2 held -∗
  ∃ fb freg fl lp, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ 0 <= fl < 2 ^ 32 /\
     Z.land fl io_user_lock = 0 /\ Z.land flags2 io_need_lock = 0 /\ 0 <= flags2 < 2 ^ 32 /\
     0 <= mode < 2 ^ 32⌝ ∗
    live fb freg ∗ int_cell fb off_flags fl ∗ int_cell fb off_flags2 flags2 ∗ int_cell fb off_mode mode ∗
    pcell fb off_lock lp ∗ lock_inv self lp held ∗
    (∀ flags2' held', ⌜Z.land flags2' io_need_lock = 0⌝ -∗ live fb freg -∗ int_cell fb off_flags fl -∗
       int_cell fb off_flags2 flags2' -∗ int_cell fb off_mode mode -∗ pcell fb off_lock lp -∗
       lock_inv self lp held' -∗ fx_stream vb self fp fd mode flags2' held').
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hk & Hb & Hw)".
  destruct Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hok & Hi & Hf2 & Hvt & Hbok & Hm & Hshort).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hflags2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd &
    Hfrl & Hfrb & Hmd & Htot & Hvtp)".
  iDestruct "Hfl" as "[%Hflr Hfl]". iDestruct "Hflags2" as "[%Hf2r Hflags2]".
  iDestruct "Hmd" as "[%Hmdr Hmd]".
  pose proof Hok as (_ & _ & _ & _ & Hul & Hnl & _). unfold has in Hul.
  apply negb_false_iff, Z.eqb_eq in Hul.
  iExists fb, freg, (fs_flags st), (fs_lock st). rewrite -Hf2 -Hm.
  iFrame "Hl Hk Hlp". iSplitR; [iPureIntro; split_and!; tauto|].
  iSplitL "Hfl"; [iSplit; [done|iExact "Hfl"]|].
  iSplitL "Hflags2"; [iSplit; [done|iExact "Hflags2"]|].
  iSplitL "Hmd"; [iSplit; [done|iExact "Hmd"]|].
  iIntros (flags2' held' Hmask) "Hl Hfl Hflags2 Hmd Hlp Hk".
  iExists fb, freg, (fs_with_flags2 st flags2'), nb.
  apply (proj2 (short_idle_flags2 nb st flags2')) in Hshort. unfold fs_with_flags2 in Hshort.
  unfold fs_with_flags2, file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable].
  iSplitR; [iPureIntro; unfold flags_ok in *; cbn [fs_flags fs_flags2]; tauto|].
  iFrame "Hl Hk Hb Hw Hfl Hps Hfd Hflags2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp". iSplit; done.
Qed.

(** An idle stream is the wrapper's view with a free lock and the two
    bits of the second flags word clear that [idle_ok] names. A caller
    that keeps a stream idle between calls opens it this way for one
    call and closes it again afterwards. *)
Lemma file_idle_fx_stream vb self fp fd :
  file_idle vb self fp fd ⊣⊢
  ∃ mode flags2, ⌜Z.land flags2 2 = 0 /\ Z.land flags2 32 = 0⌝ ∗ fx_stream vb self fp fd mode flags2 None.
Proof using Type.
  rewrite file_idle_tidy. iSplit.
  - iIntros "(%flags2 & %Hb & Hs)". iDestruct (file_tidy_fx_stream with "Hs") as (mode) "Hs".
    iExists mode, flags2. iFrame "Hs". done.
  - iIntros "(%mode & %flags2 & %Hb & Hs)". iExists flags2. iSplit; [done|].
    iApply file_tidy_fx_stream. iExists mode. iExact "Hs".
Qed.

End fx_stream.

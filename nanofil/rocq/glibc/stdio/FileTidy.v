(** Glibc's formatter prints to a stream in two situations. A program
    calls `c: fprintf` on a stream that nobody has locked. The
    diagnostic functions behind `c: error` and `c: getopt` lock the
    stream first, set a bit in its second flags word, and then call the
    formatter. In both situations the caller needs the stream back in
    the idle state of [FileIdle](../libio/FileIdle.v), so that the next
    call can use it.

    The idle state fixes the lock as free and the cancellation bit of
    the second flags word as clear. This file states the same state
    with those two as parameters. The formatter's contract uses the
    predicate of this file, and an idle stream is the case where the
    lock is free and the bit is clear. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import Fix FileInv FileIdle PrintfStreamInv.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** The facts [idle_ok] say two things about the second flags word.
    The other facts do not mention that word. So the facts hold of a
    state exactly when they hold of the state with a zero second flags
    word and the word itself meets the two. *)
Lemma idle_ok_flags2 fd st :
  idle_ok fd st <->
  idle_ok fd (fs_with_flags2 st 0) /\ Z.land (fs_flags2 st) 2 = 0 /\ Z.land (fs_flags2 st) 32 = 0.
Proof. unfold idle_ok, fs_with_flags2. cbn. tauto. Qed.

(** The fact [short_idle] does not mention the second flags word
    either, so a new value of that word keeps it. *)
Lemma short_idle_flags2 nb st x : short_idle nb (fs_with_flags2 st x) <-> short_idle nb st.
Proof. unfold short_idle, fs_with_flags2. destruct nb; reflexivity. Qed.

Section tidy.
Context `{!gen_heapGS piece pval Σ}.

(** ## A tidy stream *)

(** The formatter may run while its caller holds the stream's lock,
    and its caller may have set bits in the stream's second flags word.
    A contract that covers both cases must say what the lock and that
    word are. The predicate [file_tidy] owns a stream as [file_idle]
    does and takes the two as parameters. The parameter flags2 is the
    value of the second flags word. The parameter held is None when
    the lock is free. It is Some c when the thread self has taken the
    lock c + 1 times. *)
Definition file_tidy (vb : Z) (self fp : ptr) (fd flags2 : Z) (held : option Z) : iProp Σ :=
  ∃ fb freg st nb, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\
     idle_ok fd (fs_with_flags2 st 0) /\ fs_flags2 st = flags2 /\
     fs_vtable st = mkPtr (vb + vt_file) (Ro vb) /\ buf_ptrs_ok fb nb (fs_ptrs st) /\
     short_idle nb st⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) held ∗ buf_idle nb ∗
    wide_idle vb (fs_wide st) (fs_codecvt st).

(** An idle stream is a tidy stream with a free lock whose second
    flags word has the two bits clear that [idle_ok] names. A caller
    of `c: fprintf` goes from left to right before the formatter runs
    and from right to left after it. *)
Lemma file_idle_tidy vb self fp fd :
  file_idle vb self fp fd ⊣⊢
  ∃ flags2, ⌜Z.land flags2 2 = 0 /\ Z.land flags2 32 = 0⌝ ∗ file_tidy vb self fp fd flags2 None.
Proof using Type.
  iSplit.
  - iIntros "(%fb & %freg & %st & %nb & %Hp & H)".
    destruct Hp as (? & ? & ? & ? & ? & ? & Hi & ? & ?). apply idle_ok_flags2 in Hi as (? & ? & ?).
    iExists (fs_flags2 st). iSplit; [done|]. iExists fb, freg, st, nb. iFrame "H". iPureIntro. tauto.
  - iIntros "(%flags2 & %Hb & %fb & %freg & %st & %nb & %Hp & H)".
    destruct Hp as (? & ? & ? & ? & ? & ? & Hi & <- & ? & ?).
    iExists fb, freg, st, nb. iFrame "H". iPureIntro. rewrite idle_ok_flags2. tauto.
Qed.

(** ## Borrowing parts of a tidy stream *)

(** A lock operation borrows the stream's lock, and the caller keeps
    every other part. Giving the lock back records its new state. *)
Lemma file_tidy_lock vb self fp fd flags2 held :
  file_tidy vb self fp fd flags2 held -∗
  ∃ lp, lock_inv self lp held ∗
    (∀ held', lock_inv self lp held' -∗ file_tidy vb self fp fd flags2 held').
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hk & Hb)".
  iExists (fs_lock st). iFrame "Hk". iIntros (held') "Hk".
  iExists fb, freg, st, nb. iFrame. done.
Qed.

(** A load of a pointer to the stream needs the stream's object to be
    alive. The caller borrows the stream's lifetime for the load and
    gives it back. The stream's address is positive and lies below
    2^63. *)
Lemma file_tidy_live vb self fp fd flags2 held :
  file_tidy vb self fp fd flags2 held -∗
  ∃ fb freg, ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb < 2 ^ 63⌝ ∗
    live fb freg ∗ (live fb freg -∗ file_tidy vb self fp fd flags2 held).
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & H)".
  iExists fb, freg. iFrame "Hl". iSplit.
  { iPureIntro. destruct Hp as (? & _ & ? & ? & ? & _). unfold file_size in *. split; [assumption | lia]. }
  iIntros "Hl". iExists fb, freg, st, nb. iFrame "Hl H". done.
Qed.

(** The diagnostic functions set a bit in the second flags word
    before they print, and they restore the word afterwards. Each of
    these writes needs the four bytes of the word and the stream's
    lifetime, so the lemma below lends both. The stream stays tidy for
    any new value in which the bit `c: _IO_FLAGS2_NEED_LOCK` is clear.
    That bit is clear in every stream that these proofs handle. *)
Lemma file_tidy_flags2 vb self fp fd flags2 held :
  file_tidy vb self fp fd flags2 held -∗
  ∃ fb freg, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
    fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
    live fb freg ∗ int_cell fb off_flags2 flags2 ∗
    (∀ flags2', ⌜Z.land flags2' io_need_lock = 0⌝ -∗ live fb freg -∗
      int_cell fb off_flags2 flags2' -∗ file_tidy vb self fp fd flags2' held).
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hk & Hb)".
  destruct Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hok & Hi & Hf2 & Hvt & Hbok & Hshort).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hflags2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd &
    Hfrl & Hfrb & Hmd & Htot & Hvtp)".
  iExists fb, freg. rewrite Hf2. iFrame "Hl Hflags2".
  iSplitR; [iPureIntro; tauto|]. iIntros (flags2' Hmask) "Hl Hflags2".
  iExists fb, freg, (fs_with_flags2 st flags2'), nb.
  apply (proj2 (short_idle_flags2 nb st flags2')) in Hshort. unfold fs_with_flags2 in Hshort.
  unfold fs_with_flags2, file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable].
  iSplitR; [iPureIntro; unfold flags_ok in *; cbn [fs_flags fs_flags2]; tauto|].
  iFrame "Hl Hk Hb Hfl Hps Hfd Hflags2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp". iSplit; done.
Qed.

(** The older proofs of the diagnostic functions ask for a stream in
    the form [printf_stream], which names the stream's mode. A tidy
    stream has every part that form needs, and its mode is 0 or -1.
    The conversion forgets the capability slots of the buffer, so it
    goes one way only. *)
Lemma file_tidy_stream vb self fp fd flags2 held :
  file_tidy vb self fp fd flags2 held ⊢
  ∃ mode, ⌜mode = 0 \/ mode = 2 ^ 32 - 1⌝ ∗ printf_stream vb self fp mode flags2 held.
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hlk & Hb & _)".
  destruct Hp as (? & ? & ? & ? & ? & ? & (_ & _ & Hm & _) & ? & ? & ? & _).
  iExists (fs_mode st). iSplit; [done|].
  iExists fb, freg, st, nb, vt_file. iFrame "Hl Hf Hlk". iSplit.
  { iPureIntro. unfold mode_vtable. eauto 20. }
  destruct nb; cbn; try done.
  iDestruct "Hb" as (breg xs cs (? & ? & ? & _ & _ & ? & ? & _ & _)) "(Hl & Hx & _)".
  iExists breg, xs. iFrame. done.
Qed.

End tidy.

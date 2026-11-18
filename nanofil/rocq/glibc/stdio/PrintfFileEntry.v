(** Before `c: __vfprintf_internal` formats anything, it looks at the
    stream. It reads the stream's orientation and makes an unoriented
    stream narrow. It reads the flags, and on a stream that cannot be
    written it sets the error flag and returns. It reads the second
    flags word to see whether the stream needs its lock. After the
    formatter has run, the function gives the stream back to its
    caller.

    This module has the two lemmas about the stream that these steps
    need. The first lends the three fields that the entry code reads
    and takes them back with the changes that the entry code may make.
    The second takes the stream out of the invariant of a file-backed
    buffer when the print is over. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle FileTidy PrintfStreamInv LibioLogic LibioFputsSpec
  AllocRo FormatterStringArg CStruct PrintfLayout PrintfOut PrintfSpec PrintfFileOut.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic StringVL.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** ## The entry code *)

(** The function [fs_entry] gives the state of a stream after stores
    to its flags and to its orientation. *)
Definition fs_entry (st : fstate) (fl md : Z) : fstate :=
  mkFstate fl (fs_ptrs st) (fs_fileno st) (fs_flags2 st) (fs_old_offset st)
    (fs_column st) (fs_lock st) (fs_offset st) (fs_codecvt st) (fs_wide st) (fs_freeres_list st)
    (fs_freeres_buf st) md (fs_total st) (fs_vtable st).

(** A caller holds the stream between calls under an invariant that
    lists facts about the stream's flags and its orientation. The
    entry code changes two things. It may set the error flag, and it
    may change an unoriented stream to a narrow one. This lemma shows
    that the invariant's facts still hold after either change. None of
    the facts reads the error flag, and the invariant allows both an
    unoriented and a narrow stream. *)
Lemma entry_ok fd fb nb st fl md :
  flags_ok st -> idle_ok fd (fs_with_flags2 st 0) -> short_idle nb st -> buf_ptrs_ok fb nb (fs_ptrs st) ->
  fl = fs_flags st \/ fl = Z.lor (fs_flags st) io_err_seen -> md = fs_mode st \/ md = 2 ^ 32 - 1 ->
  flags_ok (fs_entry st fl md) /\ idle_ok fd (fs_with_flags2 (fs_entry st fl md) 0) /\
  short_idle nb (fs_entry st fl md) /\ buf_ptrs_ok fb nb (fs_ptrs (fs_entry st fl md)).
Proof.
  intros Hfl Hidle Hsh Hbp Hf Hm. destruct st as [fl0 ps fno fl2 oo col lk off cv wd frl frb md0 tot vt].
  unfold fs_entry, flags_ok, idle_ok, short_idle, fs_with_flags2, fs_ptr in *.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable] in *.
  assert (Hhas : forall b, Z.land io_err_seen b = 0 -> has fl b = has fl0 b).
  { intros b Hb. destruct Hf as [-> | ->]; [reflexivity|]. unfold has. by rewrite Z.land_lor_distr_l Hb Z.lor_0_r. }
  rewrite !(Hhas io_is_filebuf eq_refl) !(Hhas io_in_backup eq_refl) !(Hhas io_user_lock eq_refl) !(Hhas io_unbuffered eq_refl)
    !(Hhas io_user_buf eq_refl) !(Hhas io_line_buf eq_refl) !(Hhas io_currently_putting eq_refl) !(Hhas io_no_writes eq_refl)
    !(Hhas io_is_appending eq_refl) !(Hhas io_linked eq_refl).
  assert (Hr : 0 <= fl < 2 ^ 32 /\ Z.land fl 4294901760 = io_magic).
  { destruct Hfl as (Hr & Hmagic & _). destruct Hf as [-> | ->]; [done|]. split; [apply lor_lt32; [exact Hr | unfold io_err_seen; lia]|].
    rewrite Z.land_lor_distr_l. change (Z.land io_err_seen 4294901760) with 0. by rewrite Z.lor_0_r. }
  assert (Hmd : md = 0 \/ md = 2 ^ 32 - 1) by (destruct Hidle as (_ & _ & Hmd & _); destruct Hm as [-> | ->]; [exact Hmd | by right]).
  split_and!; tauto.
Qed.

Section entry.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The entry code reads the stream's flags, its second flags word and
    its orientation. This lemma lends those three fields and the
    stream's lifetime out of a tidy stream. The stream comes back tidy
    when the flags are as they were or have the error flag set, and
    the orientation is as it was or narrow. *)
Lemma file_tidy_entry vb self fp fd flags2 held :
  file_tidy vb self fp fd flags2 held ⊢ ∃ fb freg fl md,
    ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\
     0 <= fl < 2 ^ 32 /\ (md = 0 \/ md = 2 ^ 32 - 1) /\ Z.land flags2 io_need_lock = 0 /\
     (fd <> 0 -> has fl io_no_writes = false)⌝ ∗
    live fb freg ∗ int_cell fb off_flags fl ∗ int_cell fb off_flags2 flags2 ∗ int_cell fb off_mode md ∗
    (∀ fl' md', ⌜(fl' = fl \/ fl' = Z.lor fl io_err_seen) /\ (md' = md \/ md' = 2 ^ 32 - 1)⌝ -∗
       live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 flags2 -∗ int_cell fb off_mode md' -∗
       file_tidy vb self fp fd flags2 held).
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %HP & Hl & Hf & Hlk & Hb & Hw)".
  destruct HP as (Hfp & A1 & A2 & A3 & A4 & Hfl & Hidle & A5 & A6 & Hbp & Hsh).
  iDestruct "Hf" as "(%Hlen & Hflg & Hps & Hfno & Hfl2 & Hoo & %Hcol & Hcolb & Hlock & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htot & Hvt)".
  iExists fb, freg, (fs_flags st), (fs_mode st). rewrite A5. iFrame "Hl Hflg Hfl2 Hmd". iSplit.
  { iPureIntro. pose proof Hfl as (F1 & _ & _ & _ & _ & F6 & _). pose proof Hidle as (_ & _ & I3 & _ & _ & _ & _ & _ & _ & _ & I11 & _).
    rewrite A5 in F6. unfold fs_with_flags2 in I3, I11. cbn [fs_mode fs_flags] in I3, I11. split_and!; first [assumption | lia]. }
  iIntros (fl' md' [Hf' Hm']) "Hl Hflg Hfl2 Hmd".
  destruct (entry_ok fd fb nb st fl' md' Hfl Hidle Hsh Hbp Hf' Hm') as (E1 & E2 & E3 & E4).
  iExists fb, freg, (fs_entry st fl' md'), nb. iFrame "Hl Hlk Hb Hw". iSplit; [iPureIntro; split_and!; assumption|].
  unfold file_fields, fs_entry. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable].
  rewrite A5. iFrame "Hflg Hps Hfno Hfl2 Hoo Hcolb Hlock Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvt". done.
Qed.

(** ## The stream of a call *)

(** A write to a stream can take the stream's lock, call the kernel
    and set errno. The proofs of those steps need to know which thread
    is running, where errno lives and whether the stream's descriptor
    is open. The buffer's invariant owns the stream but states none of
    this, so the predicate [fout_ok] states it for the stream of a.
    The stream's lock is taken, if at all, by the thread that is
    running. The object of errno is that thread's errno cell, and the
    global `c: __libc_errno` points to it. The stream's descriptor is
    open. The precondition of `c: __vfprintf_internal` implies all of
    these facts for its stream. *)
Definition fout_ok (a : fout) : Prop :=
  fo_self a = ow_self w0 /\
  ow_errno w0 = Some (mkPtr (fo_eb a) (Obj (fo_eb a))) /\
  In (fo_fd a) (ow_fds w0) /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (fo_eb a) (Obj (fo_eb a))).

(** ## A fresh buffer *)

(** The function keeps the buffer in a local variable, which is a new
    object of 176 zero bytes. Such an object is a file-backed buffer
    whose pointers are null and whose count and mode are zero, together
    with the bytes of its staging array. The function that sets the
    buffer up overwrites every field. *)
Lemma fresh_file_buffer bb :
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= 2 ^ 48 ->
  let br := mkRegion bb (bb + 176) Heap Live in
  live bb br ∗ bytes bb 0 (replicate 176 0) ∗ auxes bb 0 (replicate 176 CNone) ⊢
  pbuf_file_live bb br ∗ pbuf_file bb [("fp", VPtr null)] ∗
  pbuf bb [("write_base", VPtr null); ("write_ptr", VPtr null); ("write_end", VPtr null);
           ("written", VInt 0); ("mode", VInt 0)] ∗
  win_own bb (bb + stage_off) (bb + stage_end).
Proof using Type.
  intros Hb Hal Hend. cbn zeta. iIntros "(Hl & Hx & Hc)".
  change (replicate 176 0) with (replicate (8 + (8 + (8 + (8 + (4 + 4 + (8 + 128)))))) 0).
  change (replicate 176 CNone) with (replicate (8 + (8 + (8 + (8 + (8 + (8 + 128)))))) CNone).
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H0 & Hx & Hc)". iDestruct (zero_cell_prefix with "Hx Hc") as "(H8 & Hx & Hc)".
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H16 & Hx & Hc)". iDestruct (zero_cell_prefix with "Hx Hc") as "(H24 & Hx & Hc)".
  iEval (rewrite (replicate_add (4 + 4)) (replicate_add 4) !byte_ps_app !pts_app) in "Hx". iDestruct "Hx" as "[[H32 _] Hx]".
  iEval (rewrite (replicate_add 8) aux_ps_app pts_app) in "Hc". iDestruct "Hc" as "[_ Hc]".
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H40 & Hx & Hc)".
  iEval (rewrite /pcell /pts big_sepL_cons) in "H24". iDestruct "H24" as "[_ H24]".
  cbn [length replicate app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. cbn [Z.add Pos.add Pos.succ Pos.add_carry].
  iSplitL "Hl". { iEval (struct_sizes). iSplit; [iPureIntro; cbn [r_end]; lia | iExact "Hl"]. }
  iSplitL "H40"; [struct_close|].
  iSplitR "Hx Hc".
  - struct_close. iPureIntro. lia.
  - iExists (replicate 128 0), (replicate 128 CNone). unfold stage_off, stage_end. replace (bb + 48 - bb) with 48 by lia.
    iFrame "Hx Hc". iPureIntro. rewrite !length_replicate. split_and!; [lia | reflexivity | by apply Forall_replicate].
Qed.

(** ## The end of a print *)

(** When the print is over, the buffer's invariant still owns the
    stream. The buffer's window is the staging array, and the stream
    is whole, or the window is room in the stream's character buffer,
    and the room goes back to the stream. Either way the caller gets a
    tidy stream and errno. *)
Lemma file_out_close a bb :
  printf_out 4 (file_R a) bb ⊢
  file_tidy (fo_vb a) (fo_self a) (fo_fp a) (fo_fd a) (fo_flags2 a) (fo_held a) ∗ errno_any (fo_eb a).
Proof using Type.
  iIntros "(%breg & %w & %written & %mode & _ & Hbuf & HR)". iDestruct "Hbuf" as "(%Hw & _ & _ & Hwl & Hwin)".
  unfold file_R, pw_place, win_live. destruct (Z.eq_dec (pw_obj w) bb) as [Heq|Hne].
  - iDestruct "HR" as "(_ & _ & $ & _ & _ & _ & _ & $)".
  - destruct (numbers.Z.eq_dec (pw_obj w) bb); [contradiction|].
    iDestruct "HR" as "(_ & _ & $ & _ & _ & _ & _ & Hloan)".
    iApply (file_lent_tidy a (pw_obj w) (pw_reg w) (pw_lo w) (pw_base w) (pw_end w)). iFrame.
Qed.

End entry.

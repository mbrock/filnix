(** When a stream forbids writes, its overflow function reports a bad
    descriptor without touching the buffer. This applies both to a single
    character and to the flush that precedes a string write. The public
    overflow wrapper may also change an unoriented stream to narrow mode. *)

From Glibc Require Import Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle FileTidy PrintfStreamInv LibioFputsSpec
  LibioLogic LibioOverflowBase LibioOverflowGen DcigettextExit.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Section nowrite.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The error path returns EOF independently of the character. It sets
    the error bit on the stream and writes EBADF to the thread's errno. *)
Lemma wp_file_overflow_nowrite fr fb freg ch fl eb Φ :
  call_frame Unit_libio_fileops_os.fn__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb+file_size <= r_end freg -> r_end freg <= 2^63 ->
  has fl io_no_writes = true -> ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ errno_any eb -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (Z.lor fl io_err_seen) -∗ errno_own eb (le_bytes 9 4) -∗
     Φ (Ret (WInt (2^32-1)))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hrend Hnw He Hg. injection Hfr as <-. unfold file_size in Hend.
  unfold has, io_no_writes in Hnw. apply negb_true_iff, Z.eqb_neq in Hnw.
  iIntros "Hl [%Hfl Hflags] (%bs & %cs & [%Hbs %Hcs] & Hp) HK".
  iEval (rewrite pts_app) in "Hp". iDestruct "Hp" as "[Heb Hea]".
  assert (Hmask : 0 <= Z.land fl 8 < 2^32) by (apply land_lt32; lia).
  assert (Hset : 0 <= Z.lor fl 32 < 2^32) by (apply lor_lt32; lia).
  step. adv. load_s32 "Hl" "Hflags". adv. branch_as false. adv. load_s32 "Hl" "Hflags". adv.
  store_int_group "Hl Hflags". step_global Hg. iApply (wp_dci_errno_check eb He); [vx|]. iNext.
  iApply (wp_dci_errno_store eb He with "Heb"); [vx|vx|exact Hbs|]. iNext. iIntros "Heb".
  iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" with "Hl [Hflags] [Heb Hea]").
  - iSplit; [done|]. iEval (change (32 mod 2^32) with 32; unwrap2) in "Hflags". iExact "Hflags".
  - iExists cs. iSplit; [done|]. rewrite pts_app. iFrame.
Qed.

(** Only the error bit and the orientation can change. In particular,
    all facts about pending output depend on other flag bits and on
    pointers that neither error path writes. *)
Definition nowrite_after st mode :=
  mkFstate (Z.lor (fs_flags st) io_err_seen) (fs_ptrs st) (fs_fileno st) (fs_flags2 st) (fs_old_offset st)
    (fs_column st) (fs_lock st) (fs_offset st) (fs_codecvt st) (fs_wide st) (fs_freeres_list st)
    (fs_freeres_buf st) mode (fs_total st) (fs_vtable st).

Lemma nowrite_idle st nb fd mode :
  flags_ok st -> idle_ok fd (fs_with_flags2 st 0) -> short_idle nb st -> (mode = 0 \/ mode = 2^32-1) ->
  let st' := nowrite_after st mode in flags_ok st' /\ idle_ok fd (fs_with_flags2 st' 0) /\ short_idle nb st'.
Proof using Type.
  cbn zeta. destruct nb; unfold flags_ok, idle_ok, short_idle, fs_with_flags2, fs_ptr, nowrite_after, has;
    cbn [fs_flags fs_ptrs fs_flags2 fs_fileno fs_mode fs_column];
    repeat (rewrite land_lor_const; [|reflexivity]); intros (Hfl & ?) ? ? ?.
  all: split; [split; [apply lor_lt32; [done|unfold io_err_seen; lia]|tauto]|tauto].
Qed.

(** The wrapper and the file method borrow the flags, mode and jump
    table pointer. Putting them back does not require opening the buffer,
    moving a pointer or changing the lock state. *)
Lemma nowrite_fields fb st : file_fields fb st ⊢
  int_cell fb off_flags (fs_flags st) ∗ int_cell fb off_mode (fs_mode st) ∗ pcell fb off_vtable (fs_vtable st) ∗
  (∀ mode, int_cell fb off_flags (Z.lor (fs_flags st) io_err_seen) -∗ int_cell fb off_mode mode -∗
    pcell fb off_vtable (fs_vtable st) -∗ file_fields fb (nowrite_after st mode)).
Proof using Type.
  iIntros "(%Hlen & $ & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfl & Hfb & $ & Htw & $)".
  iIntros (mode) "Hflags Hmode Hvt". unfold file_fields, nowrite_after. cbn. iFrame. done.
Qed.

Context (Hov : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow).

(** On a stream that forbids writes, the public overflow wrapper returns
    EOF and leaves every idle-stream fact in force. It may orient the
    stream even though no byte was written. *)
Lemma wp_overflow_nowrite fr vb self fb freg st nb flags2 held ch eb Φ :
  let fp := mkPtr fb (Obj fb) in let fd := fs_fileno st in
  call_frame Unit_libio_genops_os.fn___GI___overflow [WPtr fp; WInt ch] = Some fr -> 0 <= ch < 256 ->
  fb mod 8 = 0 -> 0 < fb -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> flags_ok st ->
  idle_ok fd (fs_with_flags2 st 0) -> fs_flags2 st = flags2 -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st -> has (fs_flags st) io_no_writes = true ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  fputs_ro vb -∗ live fb freg -∗ file_fields fb st -∗ lock_inv self (fs_lock st) held -∗ buf_idle nb -∗
  wide_idle vb (fs_wide st) (fs_codecvt st) -∗ errno_any eb -∗
  ▷ (∀ r, ⌜r = ch \/ r = 2^32-1⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  cbn zeta. intros Hfr Hch Hal Hfb Hend Hrend Hok Hi Hf2 Hvt Hb Hshort Hnw He Hin Hg.
  iIntros "#Hro Hl Hf Hlk Hb Hw Herr HK". iDestruct "Hro" as (vr sb sr) "[#Hvt _]".
  iDestruct (nowrite_fields with "Hf") as "(Hfl & Hmd & Hvtp & Hclose)". iEval (rewrite Hvt) in "Hvtp".
  pose proof Hi as (_ & _ & Hmd & _). cbn [fs_with_flags2 fs_mode] in Hmd.
  iApply (wp_glibc___overflow Hov fr fb freg ch (fs_mode st) vb vr with "Hvt Hl Hmd Hvtp"); try first [assumption | lia].
  iNext. iIntros (fr' Hfr') "Hl Hmd Hvtp".
  iApply (wp_file_overflow_nowrite fr' fb freg ch (fs_flags st) eb with "Hl Hfl Herr"); try assumption.
  iNext. iIntros "Hl Hfl Herr". iExists (2^32-1). iSplit; [iPureIntro; intuition lia|].
  iApply ("HK" with "[%] [Hl Hfl Hmd Hvtp Hclose Hlk Hb Hw] [Herr]"); [auto| |iExists _; iExact "Herr"].
  iEval (rewrite -Hvt) in "Hvtp". iDestruct ("Hclose" with "Hfl Hmd Hvtp") as "Hf".
  iExists fb, freg, (nowrite_after st (2^32-1)), nb. iFrame "Hl Hf Hlk Hb Hw".
  iPureIntro. destruct (nowrite_idle st nb (fs_fileno st) (2^32-1) Hok Hi Hshort (or_intror eq_refl)) as (A & B & C). intuition.
Qed.
End nowrite.

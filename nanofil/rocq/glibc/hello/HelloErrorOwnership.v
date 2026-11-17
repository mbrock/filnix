(** Reporting a failed close needs access to stdout and stderr even
    though stdout is already closed. The close proof kept both objects
    alive. This exchange makes that existing memory available to error
    without claiming another copy of either stream. The caller must still
    supply error's private globals and evidence that errno remains alive.

    A separate exchange reconnects errno and stream-mode ownership after
    message printing. Which part owns those cells depends on the result. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic LibioCloseSteps LibioFcloseTail
  HelloClosedStdout HelloCloseStdout HelloCloseCallback HelloErrorClosed HelloErrorCall
  ErrorCall ErrorFailure ErrorMessage.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps LibioFcloseTail.
Open Scope Z_scope.

Section ownership.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
#[local] Hint Opaque live pcell int_cell errno_any closed_stdout_fields
  error_thread_ready error_va io_list_inv stderr_short_fields : typeclass_instances.

(** The callback API currently frames the pointer cells outside its loan.
    This exchange requires the caller to lend them explicitly. The sync
    slot remains separate from the unchanged vtable invariant. *)
Lemma error_retained_exchange rest fb freg vb lb lbreg rb ob oreg sc screg eb ap xs (D : iProp Σ) :
  close_diagnostic_loan rest rb vb
    (closed_stdout fb freg vb lb lbreg ∗
      pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") ∗ D)%I ∗
  (live ob oreg ∗ pcell ob 0 (mkPtr fb (Obj fb))) ∗
  (live sc screg ∗ pcell sc 0 (mkPtr rb (Obj rb))) ∗ errno_any eb ∗ error_va ap xs ⊢
  ∃ rreg, ⌜0 < rb /\ rb mod 8 = 0 /\ rb + file_size <= r_end rreg /\ r_end rreg <= 2 ^ 63⌝ ∗
    error_thread_ready 0 ∗ error_stdout_loan fb freg ob oreg ∗
    live sc screg ∗ pcell sc 0 (mkPtr rb (Obj rb)) ∗ live rb rreg ∗
    errno_any eb ∗ error_va ap xs ∗ closed_stdout_fields fb vb lb lbreg ∗
    pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") ∗
    io_list_inv ge (mkPtr rb (Obj rb) :: rest) ∗
    ([∗ list] g ∈ rest, stream_life g) ∗ stderr_short_fields rb vb ∗ D.
Proof using Type.
  iIntros "[(Ht & Hio & Hlives & Hfields & Hclosed & #Hslot & HD) ((Hol & Hop) & (Hsl & Hsp) & Herr & Hva)]".
  iDestruct "Hlives" as "[Hrl Hlives]".
  iDestruct "Hrl" as (b rreg [Heq Hbounds]) "Hrl".
  injection Heq as <-. iExists rreg. iSplit; [done |].
  iDestruct (error_cleanup_exchange with "Ht") as "Ht".
  iDestruct "Hclosed" as "[Hout Hclosed]". iFrame "Ht".
  iSplitL "Hol Hop Hout"; [unfold error_stdout_loan; iFrame |].
  iFrame "Hsl Hsp Hrl Herr Hva Hclosed Hslot Hio Hlives Hfields HD".
Qed.

(** Successful message printing keeps errno private. Failure exposes it
    for the actual load. Only ENOMEM also exposes the stream-mode field. *)
Definition error_message_residual fb eb ereg r en md : iProp Σ :=
  (if decide (2 ^ 31 <= r mod 2 ^ 32) then
    if decide (en = 12) then emp else int_cell fb 192 md
   else live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ int_cell fb 192 md)%I.

Lemma error_message_resources fb freg eb ereg r en md :
  error_message_returned fb freg eb ereg r en md ∗ error_message_residual fb eb ereg r en md ⊢
  live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ int_cell fb 192 md.
Proof using Type.
  unfold error_message_returned, error_message_residual, error_mode_own.
  destruct (decide (2 ^ 31 <= r mod 2 ^ 32)); [destruct (decide (en = 12)) |].
  - iIntros "[(_ & Hl & Hnow & _ & Hmode) _]". iFrame.
  - iIntros "[(_ & Hl & Hnow & _) Hmode]". iFrame.
  - iIntros "[_ H]". iExact "H".
Qed.
End ownership.

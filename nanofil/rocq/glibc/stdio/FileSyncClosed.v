(** Closing a static stream clears its read and write pointers. The actual
    file-sync function then has neither pending output nor a read-position
    adjustment. It resets the offset and returns zero without using the
    descriptor, errno, cancellation state or any external callee.

    Closing stdout leaves its static object in memory. To flush it safely,
    the caller must prove that this memory is still alive and that the
    pointer fields remain cleared. An address alone cannot prove either fact. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps FileSyncCode Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Section sync.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A closed stream has no saved input to restore and no pending output to
    write. The rule checks these conditions through the flags and four null
    pointers. It preserves all other owned memory, so cancellation may stay
    disabled while this function runs. *)
Lemma wp_file_sync_closed fr fb freg fl off (E : iProp Σ) Φ :
  call_frame glibc__IO_new_file_sync [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 152 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 256 = 0 ->
  live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
  icell fb 144 off -∗ E -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗
    pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
    icell fb 144 (2 ^ 64 - 1) -∗ E -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hreg Hbackup.
  iIntros "Hl Hfl H8 H16 H32 H40 Hoff HE HK".
  iDestruct "Hfl" as "[%Hfl Hfl]".
  cbn in Hfr. injection Hfr as <-.
  step. step. check "Hl". load_null "Hl" "H40".
  step. check "Hl". load_null "Hl" "H32". step. step. step. branch_as true.
  step. step. check "Hl". load_null "Hl" "H8".
  step. check "Hl". load_null "Hl" "H16". step. step. step.
  check "Hl". load_s32 "Hl" "Hfl". step. branch_as true.
  step. step. branch_as true. step. step. branch_as false.
  step. step. check "Hl". store_long "Hl" "Hoff". step. step.
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" with "Hl [Hfl] H8 H16 H32 H40 Hoff HE").
  iSplit; [done | iExact "Hfl"].
Qed.
End sync.

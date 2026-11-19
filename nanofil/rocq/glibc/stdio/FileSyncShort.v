(** An empty in-object short buffer needs no write or read-position
    adjustment. The actual sync function loads its four equal pointers
    using the stream's own lifetime, resets the offset and returns zero.
    It does not read the descriptor, errno or the short byte. *)
From Glibc Require Import Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps LibioPutsInv Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Section sync.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Equal read pointers exclude seeking, and equal write pointers exclude
    pending output. These cells own no second lifetime or short-buffer byte. *)
Definition short_sync_fields fb off : iProp Σ :=
  let buf := mkPtr (fb + 131) (Obj fb) in
  pcell fb 8 buf ∗ pcell fb 16 buf ∗ pcell fb 32 buf ∗ pcell fb 40 buf ∗ icell fb 144 off.

Lemma wp_file_sync_short_empty fr fb freg fl off (E : iProp Σ) Φ :
  call_frame Unit_libio_fileops_os.fn__IO_new_file_sync [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 152 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 256 = 0 ->
  live fb freg -∗ int_cell fb 0 fl -∗ short_sync_fields fb off -∗ E -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗ short_sync_fields fb (2 ^ 64 - 1) -∗
    E -∗ Φ (Ret (WInt 0))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hreg Hbackup.
  iIntros "Hl Hfl (H8 & H16 & H32 & H40 & Hoff) HE HK".
  iDestruct "Hfl" as "[%Hfl Hfl]".
  cbn in Hfr. injection Hfr as <-.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl H40".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl H32".
  step. step. step. branch_as true.
  step. step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl H8".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl H16".
  step. step. step.
  check "Hl". load_s32 "Hl" "Hfl". step. branch_as true.
  step. step. branch_as true. step. step. branch_as false.
  step. step. check "Hl". store_long "Hl" "Hoff". step. step.
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" with "Hl [Hfl] [$H8 $H16 $H32 $H40 $Hoff] HE").
  iSplit; [done | iExact "Hfl"].
Qed.
End sync.

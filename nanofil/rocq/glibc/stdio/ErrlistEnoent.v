(** The error table supplies the untranslated ENOENT message. This proof
    reads the actual length and pointer cells; their addresses alone do not
    supply permission to read them or the message. The caller retains all
    three lifetimes and both cells. *)
From Glibc Require Import Unit_stdioZ2dcommon_errlist_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic OsWorld.
Open Scope Z_scope.

Section lookup.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The table entry is index two, hence byte offset sixteen. The message
    lifetime is borrowed separately from the table and length objects. *)
Definition enoent_lookup_cells lb lr tb tr mid mr : iProp Σ :=
  live_capq DfracDiscarded (Ro lb) lr ∗ icellq DfracDiscarded lb 0 134 ∗
  live_capq DfracDiscarded (Ro tb) tr ∗ pcellq DfracDiscarded tb 16 mid ∗
  live_capq DfracDiscarded (ptr_cap mid) mr.

Lemma wp_get_errlist_enoent fr lb lr tb tr mid mr Φ :
  call_frame Unit_stdioZ2dcommon_errlist_os.fn___get_errlist [WInt 2] = Some fr ->
  lookup (TAtom "_sys_errlist_internal_len") (ge_globals ge) = Some (mkPtr lb (Ro lb)) ->
  lookup (TAtom "_sys_errlist_internal") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  0 < lb -> lb + 8 <= r_end lr -> r_end lr <= 2 ^ 48 ->
  0 < tb -> tb mod 8 = 0 -> tb + 24 <= r_end tr -> r_end tr <= 2 ^ 48 ->
  0 <= ptr_addr mid < 2 ^ 64 ->
  enoent_lookup_cells lb lr tb tr mid mr -∗
  ▷ (enoent_lookup_cells lb lr tb tr mid mr -∗ Φ (Ret (WPtr mid))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hlen Htable Hlb Hle Hlr Htb Hal Hte Htr Hmid.
  iIntros "(Hll & Hlen & Htl & Hentry & Hml) HK".
  cbn in Hfr. injection Hfr as <-.
  step. step.
  change (if sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) <=?
    sign_extension (2 ^ 32) (2 ^ 31) (2 mod 2 ^ 32) then 1 else 0) with 1.
  branch_as false. step. step_global Hlen.
  check_read_dq "Hll" by ar.
  iNext. iIntros "Hll".
  iApply (wp_raw_load_read_dq with "Hll Hlen");
    [reflexivity | vx | right; reflexivity | ar |].
  iNext. iIntros "Hll Hlen".
  step. step. step. step. branch_as false. step. step_global Htable. step. step. step.
  change (sign_extension (2 ^ 32) (2 ^ 31) (2 mod 2 ^ 32)) with 2.
  change (((2 mod 2 ^ 64) mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64) with 16.
  check_read_dq "Htl" by ar.
  iNext. iIntros "Htl".
  iApply (wp_raw_load_pointer_dq with "Htl Hentry Hml");
    [reflexivity | vx | right; reflexivity | ar | ar | exact Hmid |].
  iNext. iIntros "Htl Hentry Hml".
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" with "[$Hll $Hlen $Htl $Hentry $Hml]").
Qed.
End lookup.

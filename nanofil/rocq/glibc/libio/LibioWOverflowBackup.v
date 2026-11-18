(** When overflow allocates a wide buffer, it also discards the old
    backup area. An idle stream has no such area: glibc calls free on
    null, then writes null back to each of the three backup pointers. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude HelloImageCode145 Fix OsWorld FileInv LibioLogic LibioCloseSteps
  AllocLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation obj b := (mkPtr b (Obj b)).

Definition wfree_backup_fn := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_145])) "__GI__IO_free_wbackup_area".

Section backup.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context `{!Defines ge "free" free_fn} (Hfree : frees_heap (ge_free ge))
  (Hfn : find_fn ge zgc_free_name = None) (Hsym : lookup zgc_free_name (ge_globals ge) = None).

Lemma wp_wfree_backup frame fb fr fl wd wr Φ :
  call_frame wfree_backup_fn [WPtr (obj fb)] = Some frame ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> Z.land fl 256 = 0 ->
  live fb fr -∗ int_cell fb off_flags fl -∗ pcell fb off_wide (obj wd) -∗ live wd wr -∗
  pcell wd 64 null -∗ pcell wd 72 null -∗ pcell wd 80 null -∗
  ▷ (live fb fr -∗ int_cell fb off_flags fl -∗ pcell fb off_wide (obj wd) -∗ live wd wr -∗
     pcell wd 64 null -∗ pcell wd 72 null -∗ pcell wd 80 null -∗ Φ RetVoid) -∗ WP (ERun frame : sexpr) {{ Φ }}.
Proof using Type*.
  intros C Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B. injection C as <-.
  iIntros "Hf [%F Hfl] Hwd Hl Hsave Hback Hend HK". step. check "Hf". load_s32 "Hf" "Hfl". step. norm.
  rewrite B. branch. step. step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". load_null "Hl" "Hsave".
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (AllocLogic.wp_glibc_free_null registry (os_wi w0) ge); [done|done|done|]. resume.
  check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". store "Hl" "Hsave".
  check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". store "Hl" "Hend".
  check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". store "Hl" "Hback".
  iApply wp_ret_void. iNext. iApply ("HK" with "Hf [$Hfl //] Hwd Hl Hsave Hback Hend").
Qed.
End backup.

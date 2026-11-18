(** When fclose releases a C locale conversion step, it finds no shared
    library to unload. Glibc still checks the step's finalizer: a
    built-in step with a finalizer would fail an assertion. Both Hello
    steps have a null finalizer as well as a null library handle. *)

From Glibc Require Import HelloImageTypedGC.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude OsWorld FileInv LibioLogic Fix.
From Glibc Require MemchrLast.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Definition glibc_gconv_release_step := hello_image_fn___gconv_release_step.

Section release.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Notation dq := DfracDiscarded.

(** A read-only step needs no reference count when its library handle
    is null. Glibc reads the handle twice and checks the finalizer but
    changes neither the step nor the caller's lock. *)
Lemma wp_gconv_release_static fr b reg Φ :
  call_frame glibc_gconv_release_step [WPtr (mkPtr b (Ro b))] = Some fr ->
  0 < b -> b mod 8 = 0 -> b + 72 <= r_end reg -> r_end reg <= 2^63 ->
  liveq dq b reg -∗ pcellq dq b 0 null -∗ pcellq dq b 64 null -∗
  ▷ Φ RetVoid -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hb Ha He Hr. injection Hfr as <-. iIntros "#Hl #H0 #H64 HK".
  Local Ltac load_null o H :=
    iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o null (mkRegion 0 0 Heap Live) dq dq dq with H);
    [reflexivity|vx|right; reflexivity|a2|a2|change (0 <= 0 < 2^64); lia|done|]; iNext; iIntros "_ _ _".
  step. check_read_dq "Hl" by a2. iNext. iIntros "_". load_null 0 "Hl H0 []".
  do 3 step. branch. step. branch. step. load_null 0 "Hl H0 []". do 2 step. branch. step. step.
  iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
    [reflexivity|vx|reflexivity|right; reflexivity|a2|a2|lia|a2|a2|]. iNext. iIntros "_".
  load_null 64 "Hl H64 []". do 2 step. branch. step. iApply wp_ret_void. by iNext.
Qed.
End release.

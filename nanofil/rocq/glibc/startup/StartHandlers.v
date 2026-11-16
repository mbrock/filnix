(** `c: __libc_start_main` registers two handlers with the runtime. The
    runtime calls the errno handler when a system call fails, to store
    the error number in `c: errno`, and it calls the dlerror handler to
    publish a `c: dlerror` message. This module proves both handlers over
    their compiled bodies, so that a proof can rely on what a handler
    does when the runtime calls it.

    ## What the handlers do

    Each handler is one store. The errno handler writes its argument to
    the four bytes of `c: __libc_errno`, and the dlerror handler writes
    its pointer argument to `c: __libc_dlerror_result_string`. The
    contracts for failing system calls already write the errno cell
    themselves, which the first rule shows is what the handler does. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsStartCalls FileInv LibioLogic LibioCloseSteps StartCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

(** ## The two rules

    Both rules hold in any world, because neither handler calls the
    runtime. They need only ownership of the variable that the handler
    writes. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Calling the errno handler with v stores the low 32 bits of v in
    `c: errno`. *)
Lemma wp_errno_handler fr v eb reg xs Φ :
  call_frame errno_handler_fn [WInt v] = Some fr ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  eb + 4 <= r_end reg -> length xs = 4%nat ->
  live eb reg -∗ bytes eb 0 xs -∗
  ▷ (live eb reg -∗ bytes eb 0 (le_bytes (v mod 2 ^ 32) 4) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Heb Hend Hlen. injection Hfr as <-. iIntros "Hl Hx HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  step. step_global Heb. check "Hl". store_word "Hl Hx" by (a2) preserving (wi_store). iNext. iIntros "Hl Hx".
  iApply wp_ret_void. iNext. iApply ("HK" with "Hl Hx").
Qed.

(** Calling the dlerror handler with p stores p in
    `c: __libc_dlerror_result_string`. *)
Lemma wp_dlerror_handler fr p db reg x Φ :
  call_frame start_dlerror_handler_fn [WPtr p] = Some fr ->
  lookup (TAtom "__libc_dlerror_result_string") (ge_globals ge) = Some (mkPtr db (Obj db)) ->
  db mod 8 = 0 -> db + 8 <= r_end reg ->
  live db reg -∗ pcell db 0 x -∗
  ▷ (live db reg -∗ pcell db 0 p -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hdb Hal Hend. injection Hfr as <-. iIntros "Hl Hx HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  step. step_global Hdb. check "Hl". store "Hl" "Hx".
  iApply wp_ret_void. iNext. iApply ("HK" with "Hl Hx").
Qed.

End rules.

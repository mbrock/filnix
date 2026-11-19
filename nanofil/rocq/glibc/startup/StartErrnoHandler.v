(** This module proves the contract of the errno handler, stated in
    [StartErrnoHandlerSpec](StartErrnoHandlerSpec.v), over the handler's
    compiled body. The body checks that four bytes of `c: __libc_errno`
    are writable and stores its argument there.

    ## Why the world does not matter

    The handler makes no runtime call, so nothing it does depends on
    the OS world. The proof holds in any world and needs only ownership
    of the errno variable. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics OsTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsStartCalls FileInv LibioLogic LibioCloseSteps StartErrnoHandlerSpec.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

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
Proof using Type.
  intros Hfr Heb Hend Hlen. injection Hfr as <-. iIntros "Hl Hx HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  step. step_global Heb. check "Hl". store_word "Hl Hx" by (a2) preserving (wi_store). iNext. iIntros "Hl Hx".
  iApply wp_ret_void. iNext. iApply ("HK" with "Hl Hx").
Qed.

(** Any program whose image defines the errno handler with this body
    meets the handler's contract. *)
#[global] Instance errno_handler_has_spec `{!Defines ge "glibc_libc_start#errno_handler" errno_handler_fn} :
  HasSpec registry (os_wi w0) ge errno_handler_name (errno_handler_spec ge).
Proof using Type.
  intros [[[v eb] reg] xs]. exists errno_handler_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args errno_handler_spec].
  iIntros "(%H & Hl & Hx) HK". destruct H as (Heb & Hend & Hlen).
  iApply (wp_errno_handler with "Hl Hx"); [exact Hfr | eassumption..|].
  iNext. iIntros "Hl Hx". iApply "HK". iFrame. done.
Qed.

End rules.

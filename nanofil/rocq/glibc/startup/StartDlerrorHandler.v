(** This module proves the contract of the dlerror handler, stated in
    [StartDlerrorHandlerSpec](StartDlerrorHandlerSpec.v), over the
    handler's compiled body. The body stores its pointer argument in
    `c: __libc_dlerror_result_string`.

    ## Why the world does not matter

    The handler makes no runtime call, so nothing it does depends on
    the OS world. The proof holds in any world and needs only ownership
    of the variable that it writes. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsStartCalls FileInv LibioLogic LibioCloseSteps StartCode StartDlerrorHandlerSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Calling the dlerror handler with p stores p in
    `c: __libc_dlerror_result_string`. *)
Lemma wp_dlerror_handler fr p db reg x Φ :
  call_frame start_dlerror_handler_fn [WPtr p] = Some fr ->
  lookup (TAtom "__libc_dlerror_result_string") (ge_globals ge) = Some (mkPtr db (Obj db)) ->
  db mod 8 = 0 -> db + 8 <= r_end reg ->
  live db reg -∗ pcell db 0 x -∗
  ▷ (live db reg -∗ pcell db 0 p -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hdb Hal Hend. injection Hfr as <-. iIntros "Hl Hx HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  step. step_global Hdb. check "Hl". store "Hl" "Hx".
  iApply wp_ret_void. iNext. iApply ("HK" with "Hl Hx").
Qed.

(** Any program whose image defines the dlerror handler with this body
    meets the handler's contract. *)
#[global] Instance dlerror_handler_has_spec
    `{!Defines ge "glibc_libc_start#dlerror_handler" start_dlerror_handler_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_libc_start#dlerror_handler") (dlerror_handler_spec ge).
Proof using Type.
  intros [[[p db] reg] x]. exists start_dlerror_handler_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args dlerror_handler_spec].
  iIntros "(%H & Hl & Hx) HK". destruct H as (Hdb & Hal & Hend).
  iApply (wp_dlerror_handler with "Hl Hx"); [exact Hfr | eassumption..|].
  iNext. iIntros "Hl Hx". iApply "HK". iFrame. done.
Qed.

End rules.

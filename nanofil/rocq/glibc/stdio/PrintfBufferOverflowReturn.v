From Glibc Require Import GlibcProgram.
(** When the stream's overflow call returns EOF, printf marks its buffer
    failed and returns without selecting another buffer. The caller keeps
    the stream, staging byte and accumulated count unchanged by this suffix.

    This proof starts after the call in the captured flush body. It proves
    the caller's error handling, not the overflow call that precedes it. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** The captured block places the result comparison immediately after its call. *)
Definition printf_overflow_block : block := Eval vm_compute in
  match find_block (TAtom "L74") (fn_blocks glibc___printf_buffer_flush_to_file) with
  | Some b => b | None => mkBlock (TAtom "L74") [] [] JRetVoid end.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Canonical EOF follows the failure edge and stores mode zero. No stream
    ownership is needed here because the suffix makes no further call. *)
Lemma wp_printf_overflow_eof e bb breg mode Φ :
  0 < bb -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  lookup (TAtom "v96") e = Some (WInt 4294967295) ->
  live bb breg -∗ int_cell bb 32 mode -∗
  ▷ (live bb breg -∗ int_cell bb 32 0 -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "L74") (skipn 8 (b_insts printf_overflow_block))
      (b_jump printf_overflow_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hbe Hbr Hv0 Hchk Hr. iIntros "Hb [%Hm Hm] HK".
  cbn [printf_overflow_block b_insts b_jump skipn].
  step. branch_as false. step. step. check "Hb". store_int "Hb" "Hm".
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb [Hm]"). iSplit; [iPureIntro; lia | iExact "Hm"].
Qed.

(** A result other than EOF sends printf to its buffer-selection call.
    The caller must separately prove the code starting at that call;
    this rule only establishes which branch the comparison takes. *)
Lemma wp_printf_overflow_continue e r Φ :
  0 <= r < 2 ^ 32 -> r <> 4294967295 ->
  lookup (TAtom "v96") e = Some (WInt r) ->
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file
    (put (TAtom "v98") (WInt 0) e) [] None
    (Enter (TAtom "L88") (Some (TAtom "L74")))) : sexpr) {{ Φ }} -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "L74") (skipn 8 (b_insts printf_overflow_block))
      (b_jump printf_overflow_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hr Hnot Hlookup. iIntros "HK".
  cbn [printf_overflow_block b_insts b_jump skipn].
  step. branch_as true. norm.
  assert (Heof : (r =? 4294967295) = false) by (apply Z.eqb_neq; exact Hnot).
  rewrite Heof. iExact "HK".
Qed.

End rules.

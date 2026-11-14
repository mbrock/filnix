(** Printf checks how many staged bytes the stream accepted. A short result
    marks the printf buffer failed and returns. Only an exact count reaches
    the buffer-selection call.

    These rules begin after the stream call. They preserve the caller's
    resources without assuming that the requested bytes were all accepted. *)
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

(** The captured indirect call is followed immediately by its count comparison. *)
Definition printf_xsputn_block : block := Eval vm_compute in
  match find_block (TAtom "iw_1.join") (fn_blocks glibc___printf_buffer_flush_to_file) with
  | Some b => b | None => mkBlock (TAtom "iw_1.join") [] [] JRetVoid end.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Updating the printf error flag leaves stream and OS resources untouched. *)
Local Instance return_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Any count mismatch takes the failure edge, including partial acceptance
    and zero accepted bytes for a nonempty request. *)
Lemma wp_printf_xsputn_mismatch e bb breg mode r n Φ :
  0 < bb -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 <= r < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> r <> n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  lookup (TAtom "v55") e = Some (WInt r) ->
  lookup (TAtom "v37") e = Some (WInt n) ->
  live bb breg -∗ int_cell bb 32 mode -∗
  ▷ (live bb breg -∗ int_cell bb 32 0 -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "iw_1.join") (skipn 9 (b_insts printf_xsputn_block))
      (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hbe Hbr Hr Hn Hneq Hv0 Hchk Hret Hcount.
  iIntros "Hb [%Hm Hm] HK".
  cbn [printf_xsputn_block b_insts b_jump skipn].
  step. branch_as false. step. step. check "Hb". store_int "Hb" "Hm".
  iApply wp_ret_void. iNext. norm.
  iApply ("HK" with "Hb [Hm]"). iSplit; [iPureIntro; lia | iExact "Hm"].
Qed.

(** When the counts match, printf selects its next buffer without marking
    an error. This rule proves the branch; the caller must prove the selection. *)
Lemma wp_printf_xsputn_complete e n Φ :
  0 <= n < 2 ^ 64 ->
  lookup (TAtom "v55") e = Some (WInt n) ->
  lookup (TAtom "v37") e = Some (WInt n) ->
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file
    (put (TAtom "v57") (WInt 0) e) [] None
    (Enter (TAtom "L40") (Some (TAtom "iw_1.join")))) : sexpr) {{ Φ }} -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "iw_1.join") (skipn 9 (b_insts printf_xsputn_block))
      (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hn Hret Hcount. iIntros "HK".
  cbn [printf_xsputn_block b_insts b_jump skipn].
  step. branch_as true. norm. rewrite Z.eqb_refl. iExact "HK".
Qed.

End rules.

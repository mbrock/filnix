(** Printf must locate its output stream before passing a character to it.
    It reads the FILE pointer stored in its buffer header without changing
    either allocation.

    The rule covers the first three instructions of the captured overflow
    block. It requires no stream backend contract and preserves every field. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode PrintfBufferOverflowReturn.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Reading the pointer leaves OS resources unchanged. *)
Local Instance prelude_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Reading the FILE pointer does not consume ownership of either allocation.
    The caller receives the pointer and recovers the resources it lent. *)
Lemma wp_printf_overflow_prelude e from bb breg fb freg dqf Φ :
  0 < bb -> bb mod 8 = 0 -> bb + 48 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb < 2 ^ 64 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ liveq dqf fb freg -∗
  (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb))) /\
       lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (bb + 24) (Obj bb))) /\
       lookup (TAtom "v91") e' = Some (WPtr (mkPtr fb (Obj fb)))⌝ -∗
     live bb breg -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ liveq dqf fb freg -∗
     WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
       (Exec (TAtom "L74") (skipn 3 (b_insts printf_overflow_block))
         (b_jump printf_overflow_block))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L74") from)) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hba Hbe Hbr Hfb Hfr Hv0 Hchk. iIntros "Hb Hfp Hf HK".
  iApply wp_enter; [reflexivity | destruct from; reflexivity |].
  iNext. cbn [b_insts b_jump]. step. check "Hb".
  iApply (wp_raw_load_pointer_dq with "Hb Hfp Hf");
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |].
  iNext. iIntros "Hb Hfp Hf".
  iApply ("HK" $! _ with "[%] Hb Hfp Hf").
  split_and!; lookups; reflexivity.
Qed.

End rules.

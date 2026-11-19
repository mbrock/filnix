(** When glibc rejects a byte, gnulib asks for the name of the current
    character locale. It calls `c: setlocale(LC_CTYPE, NULL)`, which
    reads the first name pointer in `c: _nl_global_locale` without
    taking the locale lock. *)

From Glibc Require Import Unit_locale_setlocale_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsMemLogic.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsMemLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section query.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The query returns the name pointer at offset 128. The caller may
    lend different [[separation-logic|shares]] of the two objects' lifetime
    tokens and of the cell that holds the pointer. *)
Lemma wp_setlocale_ctype_query fr gb greg dql dqc cn treg dqt Φ :
  call_frame Unit_locale_setlocale_os.fn___GI_setlocale [WInt 0; WPtr null] = Some fr ->
  lookup (TAtom "_nl_global_locale") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 136 <= r_end greg -> r_end greg <= 2 ^ 48 -> 0 <= ptr_addr cn < 2 ^ 64 ->
  liveq dql gb greg -∗ pcellq dqc gb 128 cn -∗ live_capq dqt (ptr_cap cn) treg -∗
  ▷ (liveq dql gb greg -∗ pcellq dqc gb 128 cn -∗ live_capq dqt (ptr_cap cn) treg -∗ Φ (Ret (WPtr cn))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hgl Hgb Hal Hend Hmax Hcn. injection Hfr as <-.
  iIntros "Hl Hc Ht HK".
  step.
  do 5 (iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
    iNext; iIntros (? _) "_").
  step. closed_ints. step. branch. step. step. step. step. branch. step.
  step. step. step. branch. step.
  step_global Hgl. step. step. closed_ints. step.
  check_read_dq "Hl" by a2. iNext. iIntros "Hl".
  load_pointer_dq "Hl Hc Ht" by a2. iNext. iIntros "Hl Hc Ht".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "Hl Hc Ht").
Qed.

End query.

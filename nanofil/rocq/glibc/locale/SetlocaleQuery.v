(** GNU Hello asks `c: setlocale(LC_MESSAGES, NULL)` for the name of
    the current message locale. glibc answers such a query without
    taking its lock: `c: setlocale` checks the category, sees the null
    name and returns the pointer stored in `c: _nl_global_locale`'s
    array of names. This module proves that route of the compiled
    function.

    To answer the query, the function reads one pointer out of glibc's
    global locale object, so the caller must let it read that object. In
    Fil-C, reading a pointer also checks that the object it points to is
    still alive, so the caller must show that as well. The function first
    allocates five local objects for its other routes, and this route
    never touches them. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv LibioLogic SetlocaleCode.
From Glibc Require FileInv LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section query.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A caller who asks for the name of category 5 gets the pointer that
    glibc keeps for that category, and it gets back every share it lent.
    The pointer sits 168 bytes into `c: _nl_global_locale`. The caller
    may lend the object's lifetime and the name's cell at different
    fractions, because the function only reads them. *)
Lemma wp_setlocale_query fr gb greg dql dqc cn treg dqt Φ :
  call_frame glibc_setlocale [WInt 5; WPtr null] = Some fr ->
  lookup (TAtom "_nl_global_locale") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 232 <= r_end greg -> r_end greg <= 2 ^ 48 -> 0 <= ptr_addr cn < 2 ^ 64 ->
  liveq dql gb greg -∗ pcellq dqc gb 168 cn -∗ live_capq dqt (ptr_cap cn) treg -∗
  ▷ (liveq dql gb greg -∗ pcellq dqc gb 168 cn -∗ live_capq dqt (ptr_cap cn) treg -∗ Φ (Ret (WPtr cn))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hgl Hgb Hal Hend Hmax Hcn. injection Hfr as <-.
  iIntros "Hl Hc Ht HK".
  step.
  do 5 (iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
    iNext; iIntros (? _) "_").
  (* The category is in range and the name is null. *)
  step. closed_ints. step. branch. step. step. step. step. branch. step.
  step. step. step. branch. step.
  (* Load the name of the category. *)
  step_global Hgl. step. step. closed_ints. step.
  check_read_dq "Hl" by a2. iNext. iIntros "Hl".
  load_pointer_dq "Hl Hc Ht" by a2. iNext. iIntros "Hl Hc Ht".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "Hl Hc Ht").
Qed.

End query.

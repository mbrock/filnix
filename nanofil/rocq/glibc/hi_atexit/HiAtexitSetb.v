(** When a stream is closed, `c: _IO_setb` gives its buffer back to
    the allocator by calling `c: free`. In hi_atexit.c that call runs
    glibc's own `c: free`, linked from malloc/malloc.os, so the proof
    of `c: _IO_setb` has to work with that function. LibioSetb.v
    assumes the call as a rule; this file proves the rule from the
    triple of glibc's `c: free` in AllocLogic.v, which gives up the
    heap object's life and returns.

    What remains assumed is a fact about the genv: its `c: free` is
    glibc's, the runtime frees heap objects, and `c: zgc_free` is the
    model's. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  LeavesLogic AllocLogic LibioSetb HiAtexitBase.
From Glibc Require AllocLogic FileInv LibioLogic LibioSetb OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** glibc's `c: malloc` and `c: free`, at [HLG]. *)
(** `c: _IO_setb`, at [HLG]. *)
Import LibioSetb SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hfree_fn : find_fn ge (TAtom "free") = Some (Defined free_fn)) (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance hi_setb_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [free_rule] with glibc's `c: free`: the call enters `free_fn`,
    [wp_glibc_free] gives up b's life, and the call returns to the rest
    of the block. *)
Lemma hi_free_rule : LibioSetb.free_rule w0 registry ge.
Proof.
  intros f e ls l v rest j b reg Φ Hx Hk Hb. iIntros "Hbl HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | exact Hfree_fn | reflexivity |]. iNext.
  iApply (AllocLogic.wp_glibc_free registry (os_wi w0) ge b reg with "Hbl [HK]");
    [exact Hfh | exact Hzf | exact Hzg | exact Hk | lia | |].
  - intros m wd h rs Hh Hrs Hw. exact (os_wi_free w0 m wd h b reg rs Hk Hh Hrs Hw).
  - iExists _. iSplit; [iPureIntro; reflexivity|]. iExact "HK".
Qed.

(** LibioSetb.v's [wp_glibc__IO_setb] with glibc's `c: free`. *)
Definition hi_setb := LibioSetb.wp_glibc__IO_setb w0 registry ge hi_free_rule.

End rules.

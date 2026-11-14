(** The first write to stdout allocates its buffer with glibc's
    `c: malloc`. This file proves the allocation rule used by the
    buffer proofs from AllocLogic.v's triple. The allocator keeps its
    thread cache idle and returns a fresh heap object. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  AllocLogic HiAtexitBase HiAtexitSetb.
From Glibc Require AllocLogic FileInv LibioLogic OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hmalloc_fn : find_fn ge (TAtom "malloc") = Some (Defined malloc_fn))
  (Hmalloc2 : find_fn ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn)).
Context (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).

(** The program logic uses the OS world for this allocation rule. *)
Local Instance hi_alloc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Buffer allocation preserves the idle thread cache. *)
Definition hi_malloc_state : iProp Σ := AllocLogic.tcache_idle dq mp tc dummy mpr tcr dr.

(** A call of glibc's `c: malloc` in a buffer-allocation block returns
    a fresh object and preserves the idle thread cache. *)
Lemma hi_malloc_rule f e ls lab d v rest j n Φ :
  arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  hi_malloc_state -∗
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
       obj base (heap_req 16 n) -∗ hi_malloc_state -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j))
             : language.expr (nanofil_lang registry ge)) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j))
        : language.expr (nanofil_lang registry ge)) {{ Φ }}.
Proof.
  intros Hx Hn. iIntros "HM HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | exact Hmalloc_fn | reflexivity |].
  iNext.
  iApply (AllocLogic.wp_glibc_malloc registry (os_wi w0) ge n dq mp tc dummy mpr tcr dr with "HM [HK]");
    [exact Hn | | exact Hmp | exact Htc | exact Hmalloc2 |].
  - intros m wd h base Hfresh Hw. exact (os_wi_alloc w0 m wd h (heap_req 16 n) base Hfresh Hw).
  - iIntros (base Hb) "Ho HM". iExists _. iSplit; [iPureIntro; reflexivity|].
    iApply ("HK" with "[%] Ho HM"). exact Hb.
Qed.

End rules.

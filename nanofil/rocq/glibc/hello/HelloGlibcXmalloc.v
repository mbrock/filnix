(** This file proves GNU Hello's `xmalloc` when it is linked with
    glibc's own `malloc`, with no premise about either function.

    HelloJoin.v proves `xmalloc` from a contract for `malloc` that has
    no null return. Here `malloc` is glibc's compiled code, and
    AllocLogic.v's [wp_glibc_malloc] proves that it returns a fresh
    16-aligned heap object at a positive base while the tcache prelude
    stays idle ([tcache_idle]). When the runtime refuses an allocation,
    the run stops cleanly as a resource ending before `malloc` returns,
    so `xmalloc` never sees a null pointer and its call of `xalloc_die`
    is unreachable.

    Allocation preserves the concrete OS world interpretation.
    The triple therefore requires no additional preservation premise. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic MemLogic HelloModule HelloLeaf HelloJoin.
From Glibc Require Import OsWorld LeavesLogic AllocLogic.
From Glibc Require AllocLogic OsWorld.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** A call of xmalloc starts with the requested size n. *)
Lemma xmalloc_frame n :
  call_frame xmalloc_fn [WInt n] =
  Some (mkFrame xmalloc_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.


(** The allocator module supplies the concrete malloc and free proofs. *)
(** The OS module supplies the concrete preservation rules. *)
(** The proof uses the caller's logic instance. *)
Module LG := LG0.
(** The linked language uses that same logic instance. *)
Module L := LG.L.
Import L LG.

Section xmalloc.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance xm_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the chosen registry and concrete world interpretation. *)
Local Instance xm_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic supplies the safepoint instance left by a step rule. *)
Local Ltac wpm := first [ reflexivity | compute_premise ].

(** The linked allocator returns ownership of a fresh, sixteen-aligned
    object at a positive base. The null branch is therefore unreachable,
    and the caller receives both the object and the idle allocator state. *)
Lemma wp_hello_xmalloc n dq mp_b tc_b dummy_b mp_reg tc_reg dummy_reg Φ :
  0 <= n < 2 ^ 64 ->
  find_fn ge (TAtom "malloc") = Some (Defined malloc_fn) ->
  lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr mp_b (Obj mp_b)) ->
  lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc_b (Obj tc_b)) ->
  find_fn ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn) ->
  AllocLogic.tcache_idle dq mp_b tc_b dummy_b mp_reg tc_reg dummy_reg -∗
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
       obj base (heap_req 16 n) -∗ AllocLogic.tcache_idle dq mp_b tc_b dummy_b mp_reg tc_reg dummy_reg -∗
       Φ (Ret (WPtr (mkPtr base (Obj base))))) -∗
  WP (ERun (mkFrame xmalloc_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)) : gexpr)
    {{ Φ }}.
Proof.
  intros Hn Hm Hmp Htc Hm2. iIntros "Hidle HK".
  iApply (wp_enter _ _ _ _ _ _ _ _ (hblk xmalloc_fn "start")); [vm_compute; reflexivity | wpm |]. iNext.
  cbn [b_insts b_jump hblk].
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ [WInt n]);
    [cbn; rewrite Z.mod_small; [reflexivity | exact Hn] | exact Hm | reflexivity |].
  iNext.
  iApply (AllocLogic.wp_glibc_malloc registry (os_wi w0) ge n with "Hidle");
    [exact Hn | intros m wd h base Hf Hw; exact (os_wi_alloc w0 m wd h _ base Hf Hw) |
     exact Hmp | exact Htc | exact Hm2 |].
  iIntros (base (Hb0 & Hb16 & Hbend)) "Hobj Hidle".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_let; [reflexivity | reflexivity | wpm | intros ?m; wpm |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | wpm | intros ?m; wpm |]. iNext.
  assert (Hq : 0 <= req_extent (heap_req 16 n)).
  { cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos |]; lia. }
  assert (Eb : (base mod 2 ^ 64 =? 0 mod 2 ^ 64) = false).
  { apply Z.eqb_neq. rewrite Zmod_0_l. rewrite (Z.mod_small base); lia. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [cbn; rewrite Eb; reflexivity |]. iNext.
  cbn [Z.eqb edge_label].
  iApply (wp_enter _ _ _ _ _ _ _ _ (hblk xmalloc_fn "iw_1.join")); [vm_compute; reflexivity | wpm |]. iNext.
  cbn [b_insts b_jump hblk].
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "[%] Hobj Hidle"). auto.
Qed.

End xmalloc.

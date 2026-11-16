From Glibc Require Import GlibcProgram.
(** The parser in glibc's getopt_long calls free, malloc and memset when
    it collects the candidates for an ambiguous long option. The parser's
    proof takes a rule for each of those calls as an assumption. Hello
    links glibc's own allocator and memset, and their proofs already
    exist, so this file proves the three rules from those proofs. Hello's
    safety theorem in HelloNeverPanics.v uses them.

    A caller of the theorem should not have to lend the parser memory
    that Hello already shares. Malloc only reads a cache that Hello holds
    a read-only share of, so that share comes from Hello itself. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv StrchrCode StrcmpCode StrncmpCode StrlenLogic
  MemFwdCode MemFwdLogic AllocLogic StdlibCode
  GetoptModule GetoptState GetoptInitialize GetoptDiag GetoptLongExact GetoptLongStore GetoptLongDiag
  GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptWrapParse GetoptLongStr GetoptInitial
  AtexitLogic HelloGlibcLibsT HelloGetoptTable HelloGetoptState HelloGlibcDebts.
From Glibc Require FileInv AllocLogic MemFwdLogic HelloGlibcDebts.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L HelloGlibcDebts.

Section backend.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hk : hello_link ge o).
(** The OS interpretation survives the allocator's safepoints. *)
Local Instance backend_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** These calls run with the concrete glibc OS registry. *)
Local Instance backend_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** ## free and malloc

    Hello links glibc's free and malloc. Freeing hands back a live heap
    object, and allocation reads the idle thread cache and returns a
    fresh object. *)

(** This is Hello's share of the allocator's idle thread cache. *)
Definition hello_tcache : iProp Σ :=
  AL.tcache_idle DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o).

(** Hello's read-only promise includes that share. *)
Lemma hello_ro_tcache : hello_ro ge o ⊢ hello_tcache.
Proof. iIntros "(_ & _ & _ & _ & _ & _ & _ & Htc & _)". iExact "Htc". Qed.

(** glibc's free meets the parser's rule for free. *)
Lemma hello_free_rule : getopt_free_rule w0 glibc_os_registry ge.
Proof.
  intros f e ls l v rest j b reg Φ Hx Hheap Hb. iIntros "Hl HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | exact (hk_free _ _ Hk) | reflexivity |].
  iNext. destruct (hk_frees _ _ Hk) as (Hfree & Hfn & Hglobal).
  iApply (AllocLogic.wp_glibc_free glibc_os_registry (os_wi w0) ge with "Hl");
    [exact Hfree | exact Hfn | exact Hglobal | exact Hheap | lia |
     intros m wd h rs Hlive Hrs Hw; exact (os_wi_free w0 m wd h b reg rs Hheap Hlive Hrs Hw) |].
  iExists _. iSplit; [iPureIntro; reflexivity | iExact "HK"].
Qed.

(** glibc's malloc meets the parser's rule for malloc with Hello's share
    of the thread cache. *)
Lemma hello_malloc_rule : getopt_malloc_rule w0 glibc_os_registry ge hello_tcache.
Proof.
  intros f e ls l d v rest j n Φ Hx Hn. iIntros "HM HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | exact (hk_malloc _ _ Hk) | reflexivity |].
  iNext.
  iApply (AllocLogic.wp_glibc_malloc glibc_os_registry (os_wi w0) ge n with "HM [HK]");
    [exact Hn | | exact (hk_mp _ _ Hk) | exact (hk_tc _ _ Hk) | exact (hk_malloc2 _ _ Hk) |].
  - intros m wd h base Hfresh Hw. exact (os_wi_alloc w0 m wd h (heap_req 16 n) base Hfresh Hw).
  - iIntros (base Hb) "Ho HM". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    iApply ("HK" with "HM"). iRight. iExists base. iSplit; [iPureIntro; split_and!; (reflexivity || lia) | iExact "Ho"].
Qed.

(** ## memset

    The parser clears its candidate buffer through glibc's internal name
    __GI_memset. Hello's link facts name only the public memset, so the
    internal name is a premise here. *)

(** glibc's memset meets the parser's rule for memset. *)
Lemma hello_memset_rule : find_fn ge (TAtom "__GI_memset") = Some (Defined glibc_memset) ->
  getopt_memset_rule w0 glibc_os_registry ge.
Proof.
  intros Hgm f e ls l d args rest j b reg xs cs nz Φ Hx -> Hn Hb8 Hend Hlen. iIntros "Hl Hx Hcs HK".
  destruct (hk_zmemset _ _ Hk) as [Hzf Hzs].
  replace (mkPtr b (Obj b)) with (mkPtr (b + 0) (Obj b)) in Hx by (rewrite Z.add_0_r; reflexivity).
  iApply (wp_call_glibc_memset (glibc_program := program_of w0 glibc_os_registry ge) ltac:(reflexivity) Hzf Hzs
    f e ls l (CResult d P) (TAtom "__GI_memset") args rest j b reg 0 xs cs 0
    (mkFrame f (put d (WPtr (mkPtr b (Obj b))) e) ls None (Exec l rest j)) Φ
    Hx Hgm ltac:(rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia) Hb8 ltac:(reflexivity) ltac:(lia)
    ltac:(lia) Hlen with "Hl Hx Hcs").
  iNext. iIntros "Hl Hx Hcs". change (0 mod 256) with 0. iApply ("HK" with "Hl Hx Hcs").
Qed.

End backend.

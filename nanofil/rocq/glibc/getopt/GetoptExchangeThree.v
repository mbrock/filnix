From Glibc Require Import GlibcProgram.
(** Glibc's scanner inlines its exchange routine twice. This file
    proves the outer loop of the second copy with the script that proves
    the first. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange
  GetoptSwap2Lower GetoptSwap2Upper GetoptExchangeTwo GetoptSwap3Lower GetoptSwap3Upper.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptExchangeTwo GetoptInitialize GetoptState GetoptSwap3Lower GetoptSwap3Upper LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The first copy's module supplies the outer-loop script. *)
(** This module proves the lower swap loop of the second copy. *)
(** This module proves the upper swap loop of the second copy. *)
Import GetoptExchangeTwo GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section exchange.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance xchg_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The outer loop keeps 0 <= bot <= mid <= top <= n: each swap run
    shrinks the longer block by the length of the shorter one. *)
Lemma wp_x3_loop ks e bot mid top av ar n ps Φ :
  avoids ks x3_outer = true ->
  lookup (TAtom "iw_3.pr.1") e = Some (WInt bot) -> lookup (TAtom "iw_3.pr.3") e = Some (WInt top) ->
  lookup (TAtom "iw_3.v11") e = Some (WInt mid) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  0 <= bot <= mid -> mid <= top -> top <= n < 2 ^ 31 ->
  Z.of_nat (List.length ps) = n ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps', ⌜Permutation ps ps' /\ keeps ks e e'⌝ -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "iw_3.L18") (Some (TAtom "iw_3.L23")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "iw_3.L16") (b_insts x3_blk16) (b_jump x3_blk16))) : gexpr) {{ Φ }}.
Proof. x_outer (GetoptSwap3Lower.wp_x3_lower) (GetoptSwap3Upper.wp_x3_upper)
  (TAtom "iw_3.pr.1") (TAtom "iw_3.pr.3") (TAtom "iw_3.v11") ks e bot mid top av ar n ps. Qed.

End exchange.

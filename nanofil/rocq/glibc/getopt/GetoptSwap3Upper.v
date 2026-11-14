From Glibc Require Import GlibcProgram.
(** Glibc's scanner inlines its exchange routine twice. This file proves
    the upper swap loop of the second copy, which moves the shorter upper
    block of options below the skipped nonoptions. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The exchange module supplies the swap scripts. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section exchange.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance xchg_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The second loop swaps the lower block with the entries just above
    mid, for the length top - mid of the upper block. It runs when the
    upper block is not longer, so the two runs never overlap. *)
Lemma wp_x3_upper ks e fr i bot mid top av ar n ps Φ :
  avoids ks x3_inner = true ->
  phis_env ge (b_phis x3_blk100) (Some fr) e = Some (put (TAtom "iw_3.pr.6") (WInt i) e) ->
  lookup (TAtom "iw_3.pr.1") e = Some (WInt bot) -> lookup (TAtom "iw_3.v11") e = Some (WInt mid) ->
  lookup (TAtom "iw_3.v34") e = Some (WInt (top - mid)) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  0 <= bot -> 0 <= i <= top - mid -> top - mid <= mid - bot -> top <= n < 2 ^ 31 ->
  Z.of_nat (List.length ps) = n ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps', ⌜Permutation ps ps' /\ keeps ks e e' /\ lookup (TAtom "iw_3.v142") e' = Some (WInt (bot + (top - mid)))⌝ -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "iw_3.L16") (Some (TAtom "iw_3.L103")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "iw_3.L100") (Some fr))) : gexpr) {{ Φ }}.
Proof. x_upper e fr i ps bot mid top av. Qed.

End exchange.

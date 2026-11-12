(** Glibc's scanner inlines its exchange routine twice. This file proves
    the lower swap loop of the first copy, which moves the shorter lower
    block of skipped nonoptions to the top of the window. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptSwap2LowerOn (R : Runtime) (LG0 : LogicSig R).
(** The exchange module supplies the swap scripts. *)
Module X := GetoptExchangeOn R LG0.
Import X X.I X.I.S X.I.S.FI X.I.S.FI.ML X.I.S.FI.LG X.I.S.FI.L X.I.ST X.I.GB X.A.

Section exchange.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance xchg_stable : SafepointStable (os_wi w0) := I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance xchg_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The first loop swaps the lower block, of length mid - bot, with the
    same number of entries at the top. It runs when the upper block is
    longer, so the two runs never overlap. *)
Lemma wp_x2_lower ks e fr i bot mid top av ar n ps Φ :
  avoids ks x2_inner = true ->
  phis_env ge (b_phis x2_blk44) (Some fr) e = Some (put (TAtom "iw_2.pr.5") (WInt i) e) ->
  lookup (TAtom "iw_2.pr.1") e = Some (WInt bot) -> lookup (TAtom "iw_2.pr.3") e = Some (WInt top) ->
  lookup (TAtom "iw_2.v37") e = Some (WInt (mid - bot)) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  0 <= bot -> 0 <= i <= mid - bot -> mid - bot < top - mid -> top <= n < 2 ^ 31 ->
  Z.of_nat (List.length ps) = n ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps', ⌜Permutation ps ps' /\ keeps ks e e' /\ lookup (TAtom "iw_2.v94") e' = Some (WInt (top - (mid - bot)))⌝ -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "iw_2.L16") (Some (TAtom "iw_2.L47")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "iw_2.L44") (Some fr))) : gexpr) {{ Φ }}.
Proof. x_lower e fr i ps bot mid top av. Qed.

End exchange.
End GetoptSwap2LowerOn.

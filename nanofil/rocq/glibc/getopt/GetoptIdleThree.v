(** When the scanner meets the argument "--", it steps past it and moves
    the nonoptions it skipped behind the options that followed them. This
    is the second inlined copy of glibc's exchange. This file proves it
    safe, including the blocks that load the endpoints before the outer
    loop and update them after it. *)

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
  GetoptSwap2Lower GetoptSwap2Upper GetoptExchangeTwo GetoptSwap3Lower GetoptSwap3Upper GetoptExchangeThree.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptExchangeThree GetoptExchangeTwo GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The blocks around the second exchange's loop assign these names. *)
Definition x3_edges : list name := Eval vm_compute in
  List.map (fun s => TAtom ("iw_3" ++ s)%string)
    [".v6"; ".v7"; ".v10"; ".v11"; ".v14"; ".v144"; ".v145"; ".v147"; ".v149"; ".v150"; ".v151";
     ".v152"; ".v156"]%string ++ List.map TAtom ["chk88"; "chk89"; "chk90"; "chk91"]%string.


(** This module proves the second exchange's outer loop. *)
Import GetoptExchangeThree GetoptExchangeTwo GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic loads an owned private integer field as a signed 32-bit value. *)


(** This tactic rebuilds an integer field from its rewritten bytes. *)
Ltac icell := iSplit; [iPureIntro; lia | iAssumption].

Section idle3.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance idle3_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance idle3_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A stored integer in range rebuilds its field. *)
Lemma cell_mod3 b o x : 0 <= x < 2 ^ 32 -> bytes b o (le_bytes (x mod 2 ^ 32) 4) ⊢ int_cell b o x.
Proof. intros Hx. rewrite Z.mod_small; [|lia]. iIntros "H". by iSplit. Qed.

(** The second exchange runs after the scanner stepped past "--" to the
    public index i. It moves the pending nonoptions, from first up to
    last, behind the options from last up to i, and then records that the
    nonoptions end at i and start at first + (i - last). *)
Lemma wp_x3_exchange ks e fr f l i b r av ar n ps Φ :
  avoids ks (x3_outer ++ x3_edges) = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  lookup (TAtom "chk72") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk73") e = Some (WPtr (mkPtr (b + 44) (Obj b))) ->
  lookup (TAtom "chk74") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  0 <= f <= l -> l <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps', ⌜Permutation ps ps' /\ keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 44 (f + (i - l)) -∗ int_cell b 48 i -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L227") (Some (TAtom "iw_3.L18")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "iw_3.start") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv2 Hv12 Hc2 Hc23 Hc72 Hc73 Hc74 Hfl Hli Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  pose proof (avoids_app _ _ _ Hks) as [Hko Hke].
  iIntros "Hl [%Hi Hib] [%Hf Hfb] [%Hla Hlab] Ha Hc #Hs HK".
  step. step. norm. load_s32_using ltac:(arith) "Hl Hfb". step. norm. load_s32_using ltac:(arith) "Hl Hlab". load_s32_using ltac:(arith) "Hl Hib". step.
  iApply wp_enter; [reflexivity | vxn | iNext].
  set (ks' := (ks ++ [TAtom "v12"; TAtom "chk2"; TAtom "chk23"; TAtom "chk73"])%list).
  iApply (GetoptExchangeThree.wp_x3_loop w0 registry ge ks' _ f l i av ar n ps with "Ha Hc Hs");
    [ apply avoids_app_r; [exact Hko | vm_compute; reflexivity]
    | lk_prove | lk_prove | lk_prove | lk_prove | lia | lia | lia | assumption | lia | lia | lia | lia |].
  iIntros (e1 ps1 (Hp1 & Hk1)) "Ha Hc Hs1".
  apply keeps_app in Hk1 as [Hk1 Hk1'].
  eassert (K12 : lookup (TAtom "v12") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  eassert (K73 : lookup (TAtom "chk73") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  eassert (K2 : lookup (TAtom "chk2") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  eassert (K23 : lookup (TAtom "chk23") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  step. step. check "Hl". load_s32_using ltac:(arith) "Hl Hfb". check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. check "Hl". load_s32_using ltac:(arith) "Hl Hlab".
  step. step. norm. check "Hl".
  iApply (wp_raw_store_w with "Hl Hfb"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hfb". load_s32_using ltac:(arith) "Hl Hib".
  iApply (wp_raw_store_w with "Hl Hlab"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hlab". step.
  iApply ("HK" with "[%] Hl [Hib] [Hfb] [Hlab] Ha Hc Hs1"); [| icell | (iApply cell_mod3; [lia | iAssumption]) | (iApply cell_mod3; [lia | iAssumption])].
  assert (Hke1 : keeps ks e e1) by (eapply keeps_trans; [|exact Hk1]; xkeep).
  split; [done|]. xkeep.
Qed.

End idle3.

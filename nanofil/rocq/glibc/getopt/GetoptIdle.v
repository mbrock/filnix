(** When no short-option cluster is pending, glibc's scanner first clamps
    its two nonoption endpoints to the public index. In permuting mode it
    then moves the nonoptions it skipped behind the options that followed
    them. This file proves that first exchange safe, including the blocks
    that load the endpoints before the outer loop and update them after
    it. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange
  GetoptSwap2Lower GetoptSwap2Upper GetoptExchangeTwo.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The blocks around the first exchange's loop assign these names. *)
Definition x2_edges : list name := Eval vm_compute in
  List.map (fun s => TAtom ("iw_2" ++ s)%string)
    [".v6"; ".v7"; ".v10"; ".v11"; ".v14"; ".v144"; ".v145"; ".v147"; ".v149"; ".v150"; ".v151";
     ".v152"; ".v156"]%string ++ List.map TAtom ["chk47"; "chk48"; "chk49"; "chk50"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptIdleOn (R : Runtime) (LG0 : LogicSig R).
(** This module proves the first exchange's outer loop. *)
Module O := GetoptExchange2On R LG0.
Import O O.SL.X O.SL.X.I O.SL.X.I.S O.SL.X.I.S.FI O.SL.X.I.S.FI.ML O.SL.X.I.S.FI.LG O.SL.X.I.S.FI.L
  O.SL.X.I.ST O.SL.X.I.GB O.SL.X.A.

(** This tactic loads an owned private integer field as a signed 32-bit value. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | arith |];
  iNext; iIntros H.

(** This tactic rebuilds an integer field from its rewritten bytes. *)
Ltac icell := iSplit; [iPureIntro; lia | iAssumption].

Section idle.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance idle_stable : SafepointStable (os_wi w0) := O.SL.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance idle_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A stored integer in range rebuilds its field. *)
Lemma cell_mod b o x : 0 <= x < 2 ^ 32 -> bytes b o (le_bytes (x mod 2 ^ 32) 4) ⊢ int_cell b o x.
Proof. intros Hx. rewrite Z.mod_small; [|lia]. iIntros "H". by iSplit. Qed.

(** The first exchange takes the pending nonoptions, from first up to
    last, and moves them behind the options from last up to the public
    index i. It then records that the nonoptions end at i and start at
    first + (i - last). *)
Lemma wp_x2_exchange ks e fr f l i b r av ar n ps Φ :
  avoids ks (x2_outer ++ x2_edges) = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  lookup (TAtom "chk24") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= f <= l -> l <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps', ⌜Permutation ps ps' /\ keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 44 (f + (i - l)) -∗ int_cell b 48 i -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L159") (Some (TAtom "iw_2.L18")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "iw_2.start") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv2 Hv12 Hc0 Hc2 Hc23 Hc24 Hfl Hli Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  pose proof (avoids_app _ _ _ Hks) as [Hko Hke].
  iIntros "Hl [%Hi Hib] [%Hf Hfb] [%Hla Hlab] Ha Hc #Hs HK".
  en. st. load_int "Hl Hfb". st. load_int "Hl Hlab". load_int "Hl Hib". st.
  iApply wp_enter; [reflexivity | vxn | iNext].
  set (ks' := (ks ++ [TAtom "v12"; TAtom "chk0"; TAtom "chk2"; TAtom "chk23"])%list).
  iApply (O.wp_x2_loop w0 registry ge ks' _ f l i av ar n ps with "Ha Hc Hs");
    [ apply avoids_app_r; [exact Hko | vm_compute; reflexivity]
    | lk_prove | lk_prove | lk_prove | lk_prove | lia | lia | lia | assumption | lia | lia | lia | lia |].
  iIntros (e1 ps1 (Hp1 & Hk1)) "Ha Hc Hs1".
  apply keeps_app in Hk1 as [Hk1 Hk1'].
  eassert (K12 : lookup (TAtom "v12") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  eassert (K0 : lookup (TAtom "chk0") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  eassert (K2 : lookup (TAtom "chk2") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  eassert (K23 : lookup (TAtom "chk23") e1 = Some _) by (rewrite (keeps_in _ _ _ _ Hk1'); [lk_prove | cbn; tauto]).
  en. st. chk "Hl". load_int "Hl Hfb". chk "Hl". load_int "Hl Hib". st. chk "Hl". load_int "Hl Hlab".
  st. st. norm. chk "Hl".
  iApply (wp_raw_store_w with "Hl Hfb"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hfb". load_int "Hl Hib".
  iApply (wp_raw_store_w with "Hl Hlab"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hlab". st.
  iApply ("HK" with "[%] Hl [Hib] [Hfb] [Hlab] Ha Hc Hs1"); [| icell | (iApply cell_mod; [lia | iAssumption]) | (iApply cell_mod; [lia | iAssumption])].
  assert (Hke1 : keeps ks e e1) by (eapply keeps_trans; [|exact Hk1]; xkeep).
  split; [done|]. xkeep.
Qed.

End idle.
End GetoptIdleOn.

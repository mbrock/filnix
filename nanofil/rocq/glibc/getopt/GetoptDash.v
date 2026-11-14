(** The argument "--" ends the options. When glibc's scanner meets it,
    the scanner steps past it, moves the pending nonoptions behind the
    options before it, and makes every remaining argument a nonoption by
    setting both the public index and the end of the nonoption block to
    the argument count. This file proves those blocks safe. *)

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
  GetoptSwap2Lower GetoptSwap2Upper GetoptExchangeTwo GetoptSwap3Lower GetoptSwap3Upper GetoptExchangeThree
  GetoptIdleThree.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptExchangeThree GetoptExchangeTwo GetoptIdleThree GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The blocks after "--" assign these names. *)
Definition dash_names : list name := Eval vm_compute in
  List.map TAtom ["chk71"; "v223"; "v224"; "chk72"; "v229"; "chk73"; "v230"; "v232"; "chk74"; "v233";
    "v234"; "v238"; "v239"; "v241"; "v242"; "v244"; "v251"; "v252"; "v254"; "v255"; "v256"; "v258";
    "v260"; "v262"; "chk98"; "chk99"]%string.

(** The end-of-scan test starts here. *)
Definition getopt_blk203 : block := Eval vm_compute in x_blk "L203".


(** This module proves the second exchange. *)
Import GetoptIdleThree GetoptExchangeThree GetoptExchangeTwo GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section dash.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance dash_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance dash_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** After "--", every argument that is left counts as a nonoption. This
    lemma starts where the scanner has found "--" at the public index i,
    below the argument count n, and the pending nonoptions lie between
    first and last, both at most i. The scanner then reaches the
    end-of-scan test with a permuted argument vector, with the index and
    the end of the nonoption block both at n, and with first between 0
    and n. *)
Lemma wp_getopt_dash ks e i n f l b r av ar ps Φ :
  avoids ks (x3_outer ++ x3_edges) = true -> avoids ks dash_names = true ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  0 <= f <= l -> l <= i -> i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps' f', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= n⌝ -∗
     live b r -∗ int_cell b 0 n -∗ int_cell b 44 f' -∗ int_cell b 48 n -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                 (Exec (TAtom "L203") (b_insts getopt_blk203) (b_jump getopt_blk203))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L201") (Some (TAtom "L209")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hkx Hkd Hv0 Hv2 Hv12 Hc0 Hc2 Hc23 Hfl Hli Hin Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi Hib] [%Hf Hfb] [%Hla Hlab] Ha Hc #Hs HK".
  assert (Hi1 : 0 <= i + 1 < 2 ^ 32) by lia.
  iAssert (∀ e2 fr i' f' l' ps', ⌜Permutation ps ps' /\ keeps ks e e2 /\ 0 <= f' <= n /\
      lookup (TAtom "v0") e2 = Some (WInt n) /\ lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk2") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk23") e2 = Some (WPtr (mkPtr (b + 48) (Obj b)))⌝ -∗
    live b r -∗ int_cell b 0 i' -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
    live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L227") (Some fr))) : gexpr) {{ Φ }})%I
    with "[HK]" as "HL227".
  { iIntros (e2 fr i' f' l' ps' (Hp & Hk & Hf' & H0 & H12 & H2 & H23)) "Hl [%Hi' Hib] Hfb [%Hl' Hlab] Ha Hc Hs'".
    step. step. norm. check "Hl".
    iApply (wp_raw_store_w with "Hl Hlab"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hlab". check "Hl".
    iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hib". step. step.
    iApply ("HK" with "[%] Hl [Hib] Hfb [Hlab] Ha Hc Hs'");
      [| (iApply cell_mod3; [lia | iAssumption]) | (iApply cell_mod3; [lia | iAssumption])].
    split; [done|]. split; [xkeep | lia]. }
  step. check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
  iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hib". step. norm. check "Hl". load_s32_using ltac:(arith) "Hl Hfb". step. norm. check "Hl". load_s32_using ltac:(arith) "Hl Hlab". step.
  rewrite (Z.mod_small f (2 ^ 32)); [|lia]. rewrite (Z.mod_small l (2 ^ 32)); [|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec f l) as [Efl | Efl]; close_br.
  - subst l. step. brz. step. step. norm. load_s32_using ltac:(arith) "Hl Hfb". step. norm. load_s32_using ltac:(arith) "Hl Hlab". step.
    rewrite (Z.mod_small f (2 ^ 32)); [|lia]. rewrite Z.eqb_refl. brz.
    step. step. norm. load_s32_using ltac:(arith) "Hl Hib".
    iApply (wp_raw_store_w with "Hl Hfb"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hfb". step.
    iApply ("HL227" $! _ _ (i + 1) (i + 1) f ps with "[%] Hl [Hib] [Hfb] [Hlab] Ha Hc Hs");
      [| icell | (iApply cell_mod3; [lia | iAssumption]) | icell].
    split; [done|]. split; [xkeep|]. split; [lia|]. repeat split; lk_prove.
  - step. step. norm. load_s32_using ltac:(arith) "Hl Hlab". load_s32_using ltac:(arith) "Hl Hib". step. step. step.
    rewrite (Z.mod_small l (2 ^ 32)); [|lia]. rewrite (Z.mod_small (i + 1) (2 ^ 32)); [|lia].
    iApply wp_branch; [vx | iNext]. rewrite (proj2 (Z.eqb_neq l (i + 1))); [|lia]. close_br.
    iApply (wp_x3_exchange w0 registry ge (ks ++ [TAtom "v0"; TAtom "v12"; TAtom "chk2"; TAtom "chk23"])%list
      _ _ f l (i + 1) b r av ar n ps with "Hl [Hib] [Hfb] [Hlab] Ha Hc Hs [HL227]");
      [ apply avoids_app_r; [exact Hkx | vm_compute; reflexivity]
      | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove
      | lia | lia | lia | assumption | lia | lia | lia | lia | lia | lia | lia | lia
      | icell | icell | icell | ].
    iIntros (e4 ps4 (Hp4 & Hk4)) "Hl Hib Hfb Hlab Ha Hc Hs4".
    apply keeps_app in Hk4 as [Hk4 Hk4'].
    iApply ("HL227" with "[%] Hl Hib Hfb Hlab Ha Hc Hs4").
    split; [done|]. split; [eapply keeps_trans; [|exact Hk4]; xkeep|]. split; [lia|].
    repeat split; (rewrite (keeps_in _ _ _ _ Hk4'); [lk_prove | cbn; tauto]).
Qed.

End dash.

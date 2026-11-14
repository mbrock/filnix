From Glibc Require Import GlibcProgram.
(** When no short-option cluster is pending, glibc's scanner first clamps
    its two nonoption endpoints to the public index i. In permuting mode
    it then either exchanges the skipped nonoptions with the options that
    followed them, or restarts the nonoption block at i. This file proves
    those blocks safe and tracks the endpoints they leave. *)

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
  GetoptSwap2Lower GetoptSwap2Upper GetoptExchangeTwo GetoptIdle GetoptPermute.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptExchangeTwo GetoptIdle GetoptInitialize GetoptPermute GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** An unsigned 32-bit load of an int's bytes, at class [W], is its bits. *)
Lemma load_uw_int x : 0 <= x < 2 ^ 32 -> extended Uw W (of_bytes (le_bytes x 4)) = Some (WInt x).
Proof. intros Hx. rewrite of_bytes_int; [|exact Hx]. cbn. by rewrite !(Z.mod_small x (2 ^ 32)). Qed.


(** The permuting branch. *)
Import GetoptPermute GetoptIdle GetoptExchangeTwo GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section clamp.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance clamp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A caller may rewind the public index between calls, so the scanner
    first lowers both endpoints to it. The session supplies endpoints with
    0 <= first <= last <= n and first <= i. In permuting mode, ordering 1,
    the scanner then reaches the skip loop with first between 0 and i. In
    the other modes it reaches the "--" test with first <= last <= i and
    leaves the argument vector untouched. *)
Lemma wp_getopt_clamp ks e fr0 n i o f l b r av ar ps Φ :
  avoids ks (x2_outer ++ x2_edges) = true -> avoids ks clamp_names = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= f <= l -> l <= n -> f <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 40 o -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ e' ps' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ o = 1 /\ 0 <= f' <= i /\
       lookup (TAtom "chk23") e' = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
       lookup (TAtom "chk24") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 40 o -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                 (Exec (TAtom "L159") (b_insts getopt_blk159) (b_jump getopt_blk159))) : gexpr) {{ Φ }}) ∧
   (∀ e' l', ⌜keeps ks e e' /\ o <> 1 /\ f <= l' <= i /\
       lookup (TAtom "chk23") e' = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
       lookup (TAtom "chk24") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 40 o -∗ int_cell b 44 f -∗ int_cell b 48 l' -∗
     live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                 (Exec (TAtom "L119") (b_insts getopt_blk119) (b_jump getopt_blk119))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L73") (Some fr0))) : gexpr) {{ Φ }}.
Proof.
  intros Hkx Hkc Hv2 Hv12 Hc0 Hc2 Hfl Hln Hfi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi Hib] [%Ho Hob] [%Hf Hfb] [%Hla Hlab] Ha Hc #Hs HK".
  step. step. norm. check "Hl". load_s32_using ltac:(arith) "Hl Hlab". check "Hl". load_s32_using ltac:(arith) "Hl Hib". step.
  iAssert (∀ e2 l1 fr, ⌜keeps ks e e2 /\ f <= l1 <= i /\
      lookup (TAtom "v2") e2 = Some (WPtr (mkPtr av (Obj av))) /\
      lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk0") e2 = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
      lookup (TAtom "chk2") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk23") e2 = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
      lookup (TAtom "chk24") e2 = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
    live b r -∗ int_cell b 0 i -∗ int_cell b 48 l1 -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L93") (Some fr))) : gexpr) {{ Φ }})%I
    with "[Hob Hfb Ha Hc HK]" as "HL93".
  { iIntros (e2 l1 fr (Hk & Hl1 & H2 & H12 & H0 & H2' & H23 & H24)) "Hl [%Hi' Hib] [%Hl1' Hlab]".
    step. step. norm. load_s32_using ltac:(arith) "Hl Hfb". load_s32_using ltac:(arith) "Hl Hib". step. brz. step. step. norm.
    iApply (wp_raw_load_sub_bytes_dq with "Hl Hob");
      [reflexivity | vx | reflexivity | apply load_uw_int; assumption | left; reflexivity | arith |].
    iNext. iIntros "Hl Hob". step.
    rewrite (Z.mod_small o (2 ^ 32)); [|lia]. change (1 mod 2 ^ 32) with 1. iApply wp_branch; [vx | iNext].
    destruct (Z.eqb_spec o 1) as [-> | Ho1]; close_br.
    2:{ step. iDestruct "HK" as "[_ HK]".
        iApply ("HK" $! _ l1 with "[%] Hl [Hib] [Hob] [Hfb] [Hlab] Ha Hc Hs"); [| icell | icell | icell | icell].
        split; [xkeep|]. split; [done|]. split; [lia|]. split; lk_prove. }
    iDestruct "HK" as "[HK _]".
    iApply (GetoptPermute.wp_getopt_permute ks _ _ f l1 i b r av ar n ps
      with "Hl [Hib] [Hob] [Hfb] [Hlab] Ha Hc Hs [HK]");
      [ exact Hkx | exact Hkc | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove
      | lia | lia | lia | assumption | lia | lia | lia | lia | lia | lia | lia | lia
      | icell | icell | icell | icell | ].
    iIntros (e' ps' f' l' (Hp & Hk' & Hf' & H23' & H24')) "Hl Hib Hob Hfb Hlab Ha Hc Hs'".
    iApply ("HK" with "[%] Hl Hib Hob Hfb Hlab Ha Hc Hs'").
    split; [done|]. split; [eapply keeps_trans; [|exact Hk']; xkeep|]. split; [done|]. split; [lia|]. split; assumption. }
  iApply wp_branch; [vx | iNext]. sx.
  destruct (Z.ltb_spec i l) as [Hgt | Hle]; close_br.
  - step. step. norm. load_s32_using ltac:(arith) "Hl Hib". check "Hl".
    store_word "Hl Hlab" by (arith) preserving wi_store.
    iNext. iIntros "Hl Hlab". step.
    iApply ("HL93" $! _ i with "[%] Hl [Hib] [Hlab]"); [| icell | (iApply cell_mod; [lia | iAssumption])].
    split; [xkeep|]. split; [lia|]. repeat split; lk_prove.
  - iApply ("HL93" $! _ l with "[%] Hl [Hib] [Hlab]"); [| icell | icell].
    split; [xkeep|]. split; [lia|]. repeat split; lk_prove.
Qed.

End clamp.

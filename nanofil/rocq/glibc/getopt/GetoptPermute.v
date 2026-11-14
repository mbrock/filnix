From Glibc Require Import GlibcProgram.
(** In permuting mode, after clamping its nonoption endpoints to the
    public index i, glibc's scanner either exchanges the skipped
    nonoptions with the options that followed them, or restarts the
    nonoption block at i. This file proves those blocks safe and tracks
    the endpoints they leave. *)

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
  GetoptSwap2Lower GetoptSwap2Upper GetoptExchangeTwo GetoptIdle.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptExchangeTwo GetoptIdle GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The clamp and the choice of exchange assign these names. *)
Definition clamp_names : list name := Eval vm_compute in
  List.map TAtom ["v95"; "chk23"; "v96"; "chk24"; "v98"; "v99"; "v101"; "v103"; "chk26"; "v108"; "v109";
    "v111"; "v112"; "v114"; "v116"; "chk30"; "v121"; "v122"; "v123"; "v128"; "v129"; "v131"; "v132";
    "v133"; "v137"; "v138"; "v140"; "v141"; "v143"; "v150"; "v151"; "v153"; "v154"; "v156"; "v158";
    "chk56"]%string.

(** The skip loop over nonoptions starts here. *)
Definition getopt_blk159 : block := Eval vm_compute in x_blk "L159".
(** The test for the "--" argument starts here. *)
Definition getopt_blk119 : block := Eval vm_compute in x_blk "L119".


(** The first exchange. *)
Import GetoptIdle GetoptExchangeTwo GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section permute.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance permute_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** In permuting mode the scanner may move skipped nonoptions behind
    the options after them. The branch starts with 0 <= first <= last <= i
    and reaches the skip loop with first between 0 and i. The argument
    vector it leaves is a permutation of the one it received. *)
Lemma wp_getopt_permute ks e fr f l1 i b r av ar n ps Φ :
  avoids ks (x2_outer ++ x2_edges) = true -> avoids ks clamp_names = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  lookup (TAtom "chk24") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= f <= l1 -> l1 <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 40 1 -∗ int_cell b 44 f -∗ int_cell b 48 l1 -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= i /\
       lookup (TAtom "chk23") e' = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
       lookup (TAtom "chk24") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 40 1 -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                 (Exec (TAtom "L159") (b_insts getopt_blk159) (b_jump getopt_blk159))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L117") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hkx Hkc Hv2 Hv12 Hc0 Hc2 Hc23 Hc24 Hfl Hli Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi Hib] [%Ho Hob] [%Hf Hfb] [%Hla Hlab] Ha Hc #Hs HK".
  step. step. norm. load_s32_using ltac:(arith) "Hl Hfb". step. norm. load_s32_using ltac:(arith) "Hl Hlab". step.
  rewrite (Z.mod_small f (2 ^ 32)); [|lia]. rewrite (Z.mod_small l1 (2 ^ 32)); [|lia].
  destruct (decide (f = l1 \/ l1 = i)) as [Hrs | Hx].
  + iAssert (∀ e3 fr', ⌜keeps ks e e3 /\
        lookup (TAtom "v12") e3 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "chk0") e3 = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
        lookup (TAtom "chk2") e3 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "chk23") e3 = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
        lookup (TAtom "chk24") e3 = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 44 f -∗ int_cell b 48 l1 -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None (Enter (TAtom "L125") (Some fr'))) : gexpr) {{ Φ }})%I
      with "[HK Hob Ha Hc]" as "HL125".
    { iIntros (e3 fr' (Hk3 & H12' & H0' & H2'' & H23' & H24')) "Hl [%Hi3 Hib] [%Hf3 Hfb] [%Hl3 Hlab]".
      step. step. norm. load_s32_using ltac:(arith) "Hl Hlab". load_s32_using ltac:(arith) "Hl Hib". step.
      rewrite (Z.mod_small i (2 ^ 32)); [|lia]. rewrite (Z.mod_small l1 (2 ^ 32)); [|lia].
      iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec l1 i) as [Eli | Eli]; close_br.
      - step. iApply ("HK" $! _ ps f l1 with "[%] Hl [Hib] [Hob] [Hfb] [Hlab] Ha Hc Hs"); [| icell | icell | icell | icell].
        split; [done|]. split; [xkeep|]. split; [lia|]. split; lk_prove.
      - step. step. norm. load_s32_using ltac:(arith) "Hl Hib". check "Hl".
        store_word "Hl Hfb" by (arith) preserving wi_store.
        iNext. iIntros "Hl Hfb". step. step.
        iApply ("HK" $! _ ps i l1 with "[%] Hl [Hib] [Hob] [Hfb] [Hlab] Ha Hc Hs");
          [| icell | icell | (iApply cell_mod; [lia | iAssumption]) | icell].
        split; [done|]. split; [xkeep|]. split; [lia|]. split; lk_prove. }
    iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec f l1) as [Efl | Efl]; close_br.
    * step. brz. iApply ("HL125" with "[%] Hl [Hib] [Hfb] [Hlab]"); [| icell | icell | icell].
      split; [xkeep|]. repeat split; lk_prove.
    * assert (Eli : l1 = i) by lia. subst l1.
      step. step. norm. load_s32_using ltac:(arith) "Hl Hlab". load_s32_using ltac:(arith) "Hl Hib". step. step. step.
      rewrite (Z.mod_small i (2 ^ 32)); [|lia]. rewrite (Z.eqb_refl i). brz. iApply ("HL125" with "[%] Hl [Hib] [Hfb] [Hlab]"); [| icell | icell | icell].
      split; [xkeep|]. repeat split; lk_prove.
  + iApply wp_branch; [vx | iNext]. rewrite (proj2 (Z.eqb_neq f l1)); [|lia]. close_br.
    step. step. norm. load_s32_using ltac:(arith) "Hl Hlab". load_s32_using ltac:(arith) "Hl Hib". step. step. step.
    rewrite (Z.mod_small i (2 ^ 32)); [|lia]. rewrite (Z.mod_small l1 (2 ^ 32)); [|lia].
    iApply wp_branch; [vx | iNext]. rewrite (proj2 (Z.eqb_neq l1 i)); [|lia]. close_br.
    iApply (GetoptIdle.wp_x2_exchange (ks ++ [TAtom "chk23"; TAtom "chk24"])%list _ _ f l1 i b r av ar n ps
      with "Hl [Hib] [Hfb] [Hlab] Ha Hc Hs [HK Hob]");
      [ apply avoids_app_r; [exact Hkx | vm_compute; reflexivity]
      | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove
      | lia | lia | lia | assumption | lia | lia | lia | lia | lia | lia | lia | lia
      | icell | icell | icell | ].
    iIntros (e4 ps4 (Hp4 & Hk4)) "Hl Hib Hfb Hlab Ha Hc Hs4".
    apply keeps_app in Hk4 as [Hk4 Hk4']. step.
    iApply ("HK" $! _ ps4 (f + (i - l1)) i with "[%] Hl Hib [Hob] Hfb Hlab Ha Hc Hs4"); [| icell].
    split; [done|]. split; [eapply keeps_trans; [|exact Hk4]; xkeep|]. split; [lia|].
    split; (rewrite (keeps_in _ _ _ _ Hk4'); [lk_prove | cbn; tauto]).
Qed.

End permute.

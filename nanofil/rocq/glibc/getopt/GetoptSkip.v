(** In permuting mode, glibc's scanner skips the nonoptions that follow
    the public index before it looks for an option. An argument is a
    nonoption when its first character is not a dash, or when it is the
    single dash. This file proves that loop safe: each test reads only
    the argument's terminated string, and the loop stores the index it
    stops at as the new end of the nonoption block. *)

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
  GetoptPermute GetoptExchangeTwo GetoptSkipTest.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptSkipTest GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The skip loop assigns these names. *)
Definition skip_names : list name :=
  List.map TAtom ["chk57"; "v163"; "v165"; "v195"; "v196"; "chk65"; "v198"; "v200"; "chk67"]%string ++ test_names.


(** This module proves the nonoption test, and its exchange module supplies the argument vector. *)
Import GetoptSkipTest GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section skip.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance skip_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance skip_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A stored integer in range rebuilds its field. *)
Lemma skip_cell b o x : 0 <= x < 2 ^ 32 -> bytes b o (le_bytes (x mod 2 ^ 32) 4) ⊢ int_cell b o x.
Proof. intros Hx. rewrite Z.mod_small; [|lia]. iIntros "H". by iSplit. Qed.


(** The loop starts at the public index i and stops at some i' between
    i and n. It writes i' to both the index and the end of the nonoption
    block, and leaves the argument vector unchanged. *)
Lemma wp_getopt_skip ks e i n l b r av ar ps Φ :
  avoids ks skip_names = true ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  0 <= i <= n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 48 l -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' i', ⌜keeps ks e e' /\ i <= i' <= n⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 48 i' -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                 (Exec (TAtom "L119") (b_insts getopt_blk119) (b_jump getopt_blk119))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "L159") (b_insts getopt_blk159) (b_jump getopt_blk159))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv0 Hv2 Hv12 Hc2 Hc23 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  remember (Z.to_nat (n - i)) as m eqn:Hms. revert e i Hv0 Hv2 Hv12 Hc2 Hc23 Hi Hms.
  induction m as [m IH] using (well_founded_induction lt_wf). intros e i Hv0 Hv2 Hv12 Hc2 Hc23 Hi Hms.
  iIntros "Hl [%Hi0 Hib] [%Hla Hlab] Ha Hc #Hs HK".
  cbn [b_insts b_jump getopt_blk159].
  check "Hl". load_s32_using ltac:(arith) "Hl Hib". step.
  iAssert ((∀ e2 fr, ⌜keeps ks e e2 /\ lookup (TAtom "chk57") e2 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\ lookup (TAtom "chk23") e2 = Some (WPtr (mkPtr (b + 48) (Obj b)))⌝ -∗
      live b r -∗ bytes b 0 (int_bytes i) -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L161") (Some fr))) : gexpr) {{ Φ }}) ∧
    (∀ e2 fr, ⌜keeps ks e e2 /\ i < n /\ lookup (TAtom "chk57") e2 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "v0") e2 = Some (WInt n) /\ lookup (TAtom "v2") e2 = Some (WPtr (mkPtr av (Obj av))) /\
        lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "chk2") e2 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "chk23") e2 = Some (WPtr (mkPtr (b + 48) (Obj b)))⌝ -∗
      live b r -∗ bytes b 0 (int_bytes i) -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L160") (Some fr))) : gexpr) {{ Φ }}))%I
    with "[HK Hlab]" as "HLs".
  { iSplit.
    - iIntros (e2 fr (Hk & H57 & H12 & H23)) "Hl Hib Ha Hc".
      step. step. norm. load_s32_using ltac:(arith) "Hl Hib". check "Hl".
      iApply (wp_raw_store_w with "Hl Hlab"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
      iNext. iIntros "Hl Hlab". step. step.
      iApply ("HK" $! _ i with "[%] Hl [Hib] [Hlab] Ha Hc Hs"); [| icell | (iApply skip_cell; [lia | iAssumption])].
      split; [xkeep | lia].
    - iIntros (e2 fr (Hk & Hin & H57 & H0 & H2 & H12 & H2' & H23)) "Hl Hib Ha Hc".
      step. load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
      iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
      iNext. iIntros "Hl Hib". step. step.
      iApply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) _ (i + 1) with "Hl [Hib] [Hlab] Ha Hc Hs [HK]");
        [ lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lia | reflexivity
        | (iApply skip_cell; [lia | iAssumption]) | icell | ].
      iIntros (e' i' (Hk' & Hi')) "Hl Hib Hlab Ha Hc Hs'". iApply ("HK" with "[%] Hl Hib Hlab Ha Hc Hs'").
      split; [|lia]. eapply keeps_trans; [|exact Hk']. xkeep. }
  iApply wp_branch; [vx | iNext]. sx.
  destruct (Z.ltb_spec i n) as [Hlt | Hge]; close_br.
  2:{ step. brz. iDestruct "HLs" as "[HL _]". iApply ("HL" with "[%] Hl Hib Ha Hc").
      split; [xkeep|]. repeat split; lk_prove. }
  pose proof (avoids_app _ _ _ Hks) as [_ Hkt].
  iApply (wp_skip_test w0 registry ge (ks ++ List.map TAtom ["v0"; "v2"; "v12"; "chk2"; "chk23"; "chk57"]%string)%list
    _ i n b r av ar ps with "Hl Hib Ha Hc Hs [HLs]");
    [ apply avoids_app_r; [exact Hkt | vm_compute; reflexivity] | lk_prove | lk_prove
    | lia | lia | assumption | lia | lia | lia | lia | lia | lia | lia | lia |].
  iSplit.
  - iIntros (e2 fr Hk2) "Hl Hib Ha Hc". apply keeps_app in Hk2 as [Hk2 Hk2'].
    iDestruct "HLs" as "[HL _]". iApply ("HL" with "[%] Hl Hib Ha Hc").
    split; [eapply keeps_trans; [|exact Hk2]; xkeep|].
    repeat split; (rewrite (keeps_in _ _ _ _ Hk2'); [lk_prove | cbn; tauto]).
  - iIntros (e2 fr Hk2) "Hl Hib Ha Hc". apply keeps_app in Hk2 as [Hk2 Hk2'].
    iDestruct "HLs" as "[_ HL]". iApply ("HL" with "[%] Hl Hib Ha Hc").
    split; [eapply keeps_trans; [|exact Hk2]; xkeep|]. split; [lia|].
    repeat split; (rewrite (keeps_in _ _ _ _ Hk2'); [lk_prove | cbn; tauto]).
Qed.

End skip.

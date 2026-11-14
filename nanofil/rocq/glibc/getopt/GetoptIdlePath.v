From Glibc Require Import GlibcProgram.
(** Before it looks for an option, glibc's permuting scanner tidies the
    argument vector. It clamps the ends of the pending nonoption block to
    the public index, moves pending nonoptions behind the options that
    follow them, skips the nonoptions at the index, and handles "--".
    This file joins the proofs of those steps into one lemma for the
    whole path, from the clamp to the end-of-scan test. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrcmpCode
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange
  GetoptExchangeTwo GetoptExchangeThree GetoptIdle GetoptIdleThree GetoptPermute GetoptClamp
  GetoptSkipTest GetoptSkip GetoptDash GetoptDashTest.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptClamp GetoptDashTest GetoptExchange GetoptInitialize GetoptSkip GetoptSkipTest GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** The path assigns these names, and the caller's kept names avoid them. *)
Definition idle_names : list name :=
  (x2_outer ++ x2_edges) ++ clamp_names ++ skip_names ++ (x3_outer ++ x3_edges) ++ dash_names ++ dash_test_names.

(** These names hold what the steps after the clamp read. *)
Definition clamp_keys : list name := List.map TAtom ["v0"; "v2"; "v12"; "chk0"; "chk2"]%string.


(** The clamp module proves the clamp and the first exchange. *)
(** The skip module proves the nonoption skip loop. *)
(** The "--" test module proves the test and the second exchange. *)
Import GetoptSkipTest GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section path.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance path_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic proves a lookup that the kept names Hk carry over. *)
Ltac kin Hk H := rewrite (keeps_in _ _ _ _ Hk); [exact H | cbn; tauto].
(** This tactic carries a lookup over two runs of kept names. *)
Ltac kin2 Hk Hk' H := rewrite (keeps_in _ _ _ _ Hk); [kin Hk' H | cbn; tauto].

(** Whatever the arguments are, the path must not read or write outside
    the argument vector. This lemma proves the path safe and says where
    its positions end up. The pending nonoptions still lie between first
    and last, last is at most the new index, and the index has not moved
    back or past the argument count. The vector holds the same arguments
    in another order. *)
Lemma wp_getopt_idle ks e fr0 n i o f l b r av ar ps pdd sdd Φ :
  avoids ks idle_names = true ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= f <= l -> l <= n -> f <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 40 o -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  (∀ e' ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' <= n /\ i <= i' /\
       lookup (TAtom "chk23") e' = Some (WPtr (mkPtr (b + 48) (Obj b)))⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 40 o -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                 (Exec (TAtom "L203") (b_insts getopt_blk203) (b_jump getopt_blk203))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L73") (Some fr0))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hg Hdd Hv0 Hv2 Hv12 Hc0 Hc2 Hfl Hln Hfi Hin Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  unfold idle_names in Hks.
  apply avoids_app in Hks as [Hkx2 Hks]. apply avoids_app in Hks as [Hkc Hks].
  apply avoids_app in Hks as [Hksk Hks]. apply avoids_app in Hks as [Hkx3 Hks].
  apply avoids_app in Hks as [Hkd Hkt].
  iIntros "Hl Hi Ho Hf Hla Ha Hc #Hs #Hdd HK".
  iApply (GetoptClamp.wp_getopt_clamp (ks ++ clamp_keys) e fr0 n i o f l b r av ar ps
            with "Hl Hi Ho Hf Hla Ha Hc Hs [HK]");
    [ apply avoids_app_r; [exact Hkx2 | vm_compute; reflexivity]
    | apply avoids_app_r; [exact Hkc | vm_compute; reflexivity]
    | exact Hv2 | exact Hv12 | exact Hc0 | exact Hc2
    | lia | lia | lia | lia | exact Hlen | lia | lia | lia | lia | lia | lia | lia | lia |].
  iSplit.
  - iIntros (e1 ps1 f1 l1 (Hp1 & Hk1 & _ & Hf1 & H23 & _)) "Hl Hi Ho Hf Hla Ha Hc #Hs1".
    apply keeps_app in Hk1 as [Hk1 Hk1'].
    assert (Hlen1 : Z.of_nat (List.length ps1) = n) by (rewrite -(Permutation_length Hp1); exact Hlen).
    iApply (GetoptSkip.wp_getopt_skip (ks ++ GetoptDashTest.dash_keys) e1 i n l1 b r av ar ps1
              with "Hl Hi Hla Ha Hc Hs1 [Ho Hf HK]");
      [ apply avoids_app_r; [exact Hksk | vm_compute; reflexivity]
      | kin Hk1' Hv0 | kin Hk1' Hv2 | kin Hk1' Hv12 | kin Hk1' Hc2 | exact H23
      | lia | lia | exact Hlen1 | lia | lia | lia | lia | lia | lia | lia | lia |].
    iIntros (e2 i2 (Hk2 & Hi2)) "Hl Hi Hla Ha Hc #Hs2". apply keeps_app in Hk2 as [Hk2 Hk2'].
    iApply (GetoptDashTest.wp_getopt_dash_end (ks ++ [TAtom "chk23"]) e2 i2 n f1 i2 b r av ar ps1 pdd sdd
              with "Hl Hi Hf Hla Ha Hc Hs2 Hdd [Ho HK]");
      [ apply avoids_app_r; [exact Hkx3 | vm_compute; reflexivity]
      | apply avoids_app_r; [exact Hkd | vm_compute; reflexivity]
      | apply avoids_app_r; [exact Hkt | vm_compute; reflexivity] | exact Hg | exact Hdd
      | kin2 Hk2' Hk1' Hv0 | kin2 Hk2' Hk1' Hv2 | kin2 Hk2' Hk1' Hv12 | kin2 Hk2' Hk1' Hc0
      | kin2 Hk2' Hk1' Hc2 | kin Hk2' H23
      | lia | lia | lia | lia | exact Hlen1 | lia | lia | lia | lia | lia | lia | lia | lia |].
    iIntros (e3 ps3 i3 f3 l3 (Hp3 & Hk3 & Hord)) "Hl Hi Hf Hla Ha Hc Hs3".
    apply keeps_app in Hk3 as [Hk3 Hk3'].
    iApply ("HK" with "[%] Hl Hi Ho Hf Hla Ha Hc Hs3").
    split; [by rewrite Hp1|]. split; [eapply keeps_trans; [eapply keeps_trans; [exact Hk1 | exact Hk2] | exact Hk3]|].
    split; [lia|]. split; [lia|]. split; [lia|]. kin2 Hk3' Hk2' H23.
  - iIntros (e1 l1 (Hk1 & _ & Hl1 & H23 & _)) "Hl Hi Ho Hf Hla Ha Hc #Hs1".
    apply keeps_app in Hk1 as [Hk1 Hk1'].
    iApply (GetoptDashTest.wp_getopt_dash_end (ks ++ [TAtom "chk23"]) e1 i n f l1 b r av ar ps pdd sdd
              with "Hl Hi Hf Hla Ha Hc Hs1 Hdd [Ho HK]");
      [ apply avoids_app_r; [exact Hkx3 | vm_compute; reflexivity]
      | apply avoids_app_r; [exact Hkd | vm_compute; reflexivity]
      | apply avoids_app_r; [exact Hkt | vm_compute; reflexivity] | exact Hg | exact Hdd
      | kin Hk1' Hv0 | kin Hk1' Hv2 | kin Hk1' Hv12 | kin Hk1' Hc0 | kin Hk1' Hc2 | exact H23
      | lia | lia | lia | lia | exact Hlen | lia | lia | lia | lia | lia | lia | lia | lia |].
    iIntros (e3 ps3 i3 f3 l3 (Hp3 & Hk3 & Hord)) "Hl Hi Hf Hla Ha Hc Hs3".
    apply keeps_app in Hk3 as [Hk3 Hk3'].
    iApply ("HK" with "[%] Hl Hi Ho Hf Hla Ha Hc Hs3").
    split; [exact Hp3|]. split; [eapply keeps_trans; [exact Hk1 | exact Hk3]|].
    split; [lia|]. split; [lia|]. split; [lia|]. kin Hk3' H23.
Qed.

End path.

From Glibc Require Import GlibcProgram.
(** In permuting mode, glibc's scanner skips nonoptions and then asks
    whether the argument at the public index is "--", which ends the
    options. It compares the argument with glibc's own strcmp. This file
    proves that test safe: it reads the argument only below the argument
    count, and it compares two terminated strings that the scanner may
    read. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrcmpCode StrcmpBits StrcmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange
  GetoptPermute GetoptExchangeTwo GetoptExchangeThree GetoptIdleThree GetoptDash.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDash GetoptExchange GetoptExchangeThree GetoptExchangeTwo GetoptIdleThree GetoptInitialize GetoptState LibioLogic OsWorld StrcmpLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The "--" test assigns these names. *)
Definition dash_test_names : list name := Eval vm_compute in
  List.map TAtom ["chk68"; "v205"; "v207"; "v212"; "v213"; "v214"; "v215"; "chk70"; "v216"; "v217";
    "v218"; "v219"; "v221"]%string.


(** When the argument is "--", the scanner runs the blocks that GetoptDash.v proves. *)
Import GetoptDash GetoptIdleThree GetoptExchangeThree GetoptExchangeTwo GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.
(** The strcmp module proves glibc's own strcmp. *)

(** This tactic enters a block and evaluates its phi assignments. *)


(** This tactic loads an owned private integer field as a signed 32-bit value. *)


Import ProgramAbbreviations.
Section test_values.
Definition dash_keys : list name := List.map TAtom ["v0"; "v2"; "v12"; "chk0"; "chk2"; "chk23"]%string.
End test_values.
Section test.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance dash_test_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The scanner must not read past the last argument, and it may only
    compare strings it can read. Here the public index i is at most the
    argument count n, and the scanner reads argument i only when i is
    below n. The caller supplies two facts about the linked program: the
    name __GI_strcmp is glibc's strcmp, and the global str.146 is a
    shared terminated string. A match leads to the "--" blocks with i
    below n, and any other result leads to the end-of-scan test. Both
    paths keep the index field and the argument vector. *)
Lemma wp_dash_test ks e i n b r av ar ps pdd sdd Φ :
  avoids ks dash_test_names = true ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= i <= n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  word_string DfracDiscarded pdd sdd -∗
  ((∀ e', ⌜keeps ks e e'⌝ -∗ live b r -∗ int_cell b 0 i -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                  (Exec (TAtom "L203") (b_insts getopt_blk203) (b_jump getopt_blk203))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ i < n⌝ -∗ live b r -∗ int_cell b 0 i -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L201") (Some (TAtom "L209")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "L119") (b_insts getopt_blk119) (b_jump getopt_blk119))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hg Hdd Hv0 Hv2 Hv12 Hc2 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi0 Hib] Ha Hc #Hs #Hdd HK".
  cbn [b_insts b_jump getopt_blk119].
  check "Hl". load_s32_using ltac:(arith) "Hl Hib". step.
  rewrite (Z.mod_small i (2 ^ 32)); [|lia]. rewrite (Z.mod_small n (2 ^ 32)); [|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec i n) as [Ein | Ein]; close_br.
  { step. iApply wp_branch; [vx | iNext]. close_br. step. iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[%] Hl [Hib] Ha Hc"); [xkeep | by iSplit]. }
  step. load_s32_using ltac:(arith) "Hl Hib". step. step. step. idx i. check "Ha".
  set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iDestruct (big_sepL_lookup with "Hs") as (s) "#Hws"; [exact Hq|].
  iDestruct (argv_str_cap with "Hws") as (rq) "[Hcapq %Hq0]".
  load_pointer_dq "Ha Hcj Hcapq" by arith.
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). step.
  iApply (StrcmpLogic.wp_call_glibc_strcmp registry (os_wi w0) ge with "Hws Hdd"); [reflexivity | exact Hg | reflexivity |].
  iNext. iIntros "_ _". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step. step. step.
  destruct (Z.eqb ((strcmp_res s sdd mod 2 ^ 32) mod 2 ^ 32) (0 mod 2 ^ 32));
    iApply wp_branch; [vx | iNext | vx | iNext]; close_br.
  - iDestruct "HK" as "[_ HK]". iApply ("HK" with "[%] Hl [Hib] Ha Hc"); [split; [xkeep | lia] | by iSplit].
  - step. iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl [Hib] Ha Hc"); [xkeep | by iSplit].
Qed.

(** These names hold what the "--" blocks read. *)

(** The end-of-scan test needs the scanner's positions in order, so this
    lemma joins the "--" test with the blocks that follow it. It starts
    after the skip loop, with first <= last <= i <= n. The scanner then
    reaches the end-of-scan test with the same order among the new
    positions, an index that has not decreased, and a permuted argument
    vector. The facts about strcmp and str.146 stay premises. *)
Lemma wp_getopt_dash_end ks e i n f l b r av ar ps pdd sdd Φ :
  avoids ks (x3_outer ++ x3_edges) = true -> avoids ks dash_names = true ->
  avoids ks dash_test_names = true ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  0 <= f <= l -> l <= i -> i <= n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  (∀ e' ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' <= n /\ i <= i'⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None
                 (Exec (TAtom "L203") (b_insts getopt_blk203) (b_jump getopt_blk203))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "L119") (b_insts getopt_blk119) (b_jump getopt_blk119))) : gexpr) {{ Φ }}.
Proof.
  intros Hkx Hkd Hkt Hg Hdd Hv0 Hv2 Hv12 Hc0 Hc2 Hc23 Hfl Hli Hin Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl Hi Hf Hla Ha Hc #Hs #Hdd HK".
  iApply (wp_dash_test (ks ++ dash_keys) e i n b r av ar ps pdd sdd with "Hl Hi Ha Hc Hs Hdd [Hf Hla HK]");
    [ apply avoids_app_r; [exact Hkt | vm_compute; reflexivity] | exact Hg | exact Hdd
    | exact Hv0 | exact Hv2 | exact Hv12 | exact Hc2 | lia | lia | exact Hlen
    | lia | lia | lia | lia | lia | lia | lia | lia |].
  iSplit.
  - iIntros (e' Hk) "Hl Hi Ha Hc". apply keeps_app in Hk as [Hk _].
    iApply ("HK" with "[%] Hl Hi Hf Hla Ha Hc Hs"). split; [done|]. split; [exact Hk | lia].
  - iIntros (e' (Hk & Hlt)) "Hl Hi Ha Hc". apply keeps_app in Hk as [Hk Hk'].
    iApply (wp_getopt_dash ks e' i n f l b r av ar ps with "Hl Hi Hf Hla Ha Hc Hs [HK]");
      [ exact Hkx | exact Hkd
      | rewrite (keeps_in _ _ _ _ Hk'); [exact Hv0 | cbn; tauto]
      | rewrite (keeps_in _ _ _ _ Hk'); [exact Hv2 | cbn; tauto]
      | rewrite (keeps_in _ _ _ _ Hk'); [exact Hv12 | cbn; tauto]
      | rewrite (keeps_in _ _ _ _ Hk'); [exact Hc0 | cbn; tauto]
      | rewrite (keeps_in _ _ _ _ Hk'); [exact Hc2 | cbn; tauto]
      | rewrite (keeps_in _ _ _ _ Hk'); [exact Hc23 | cbn; tauto]
      | lia | lia | lia | lia | exact Hlen | lia | lia | lia | lia | lia | lia | lia | lia |].
    iIntros (e2 ps2 f2 (Hp & Hk2 & Hf2)) "Hl Hi Hf Hla Ha Hc Hs2".
    iApply ("HK" with "[%] Hl Hi Hf Hla Ha Hc Hs2").
    split; [exact Hp|]. split; [eapply keeps_trans; [exact Hk | exact Hk2] | lia].
Qed.

End test.

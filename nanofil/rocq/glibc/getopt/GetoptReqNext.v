From Glibc Require Import GlibcProgram.
(** A short option with a required argument takes the rest of its
    cluster as the argument, or else the next argument of the vector
    when one is left. glibc's scanner
    steps the public index past it and stores it as the private option
    argument. This file proves that step safe: the scanner reads the
    vector only below the argument count and writes only the fields of
    its own state. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The tail module supplies the report rule, the argument vector and its tactics. *)
Import GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section next.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance next_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The cluster stood at index i, and the character step moved the
    index to i + 1, which is still below the argument count n. The
    argument there becomes the option argument, the index becomes i + 2,
    and the cursor x becomes null. The answer is the option character c.
    The names ks keep their values from the caller's environment e0. *)
Lemma wp_getopt_reqnext ks e0 e fr i n c a x b r av ar ps Φ :
  avoids ks req_names = true -> keeps ks e0 e ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk177") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= i -> i + 1 < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> 0 <= c < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 a -∗ pcell b 32 x -∗ live av ar -∗ argv_cells av ps -∗
  argv_strs ps -∗
  (∀ e', ⌜keeps ks e0 e' /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
     live b r -∗ int_cell b 0 (i + 2) -∗ pcell b 16 (nth (Z.to_nat (i + 1)) ps null) -∗ pcell b 32 null -∗
     live av ar -∗ argv_cells av ps -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L654") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H2 H12 H455 Hc1 Hc2 Hc20 Hc177 Hi Hin Hn Hlen Hc Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi0 Hib] Hab Hcur Ha Hcl #Hs HK".
  set (j := Z.to_nat (i + 1)). assert (Hj : Z.of_nat j = i + 1) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  iDestruct (big_sepL_lookup with "Hs") as (s1) "#Hws1"; [exact Hq|].
  iDestruct (argv_str_cap with "Hws1") as (rq1) "[#Hcapq1 %Hq1]".
  step. step. norm. load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
  store_word "Hl Hib" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hib". step. step. step. idx (i + 1). check "Ha".
  iDestruct (big_sepL_lookup_acc with "Hcl") as "[Hcj Hcl]"; [exact Hq|].
  load_pointer_dq "Ha Hcj Hcapq1" by arith.
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hcl" with "Hcj"). check "Hl".
  store_pointer "Hl Hab" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hab". step. step. rewrite ?(Z.mod_small c (2 ^ 32)); [|lia]. step. check "Hl".
  store_pointer "Hl Hcur" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hcur". step.
  iApply ("HK" with "[%] Hl [Hib] [Hab] Hcur Ha Hcl");
    [split; [xkeep | lk_prove] | | unfold j in Hq; by rewrite (nth_lookup_Some _ _ _ _ Hq)].
  iSplit; [iPureIntro; lia|]. by replace (i + 2) with (i + 1 + 1) by lia.
Qed.

(** A cluster with more characters after the option gives them as the
    argument. The rest of the cluster becomes the option argument, the
    index steps from the cluster's position i past it, and the cursor
    becomes null. The answer is the option character c. *)
Lemma wp_getopt_reqrest ks e0 e fr i c cur t a b r Φ :
  avoids ks req_names = true -> keeps ks e0 e ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < 2 ^ 31 - 1 -> 0 <= c < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗
  live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ pcell b 32 (ptr_add cur 1) -∗
  (∀ e', ⌜keeps ks e0 e' /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
     live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 (ptr_add cur 1) -∗ pcell b 32 null -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L637") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H12 H455 Hc1 Hc2 Hc20 H137 Hi Hc Hb Hal Hend Hr.
  iIntros "#Hws Hl [%Hi0 Hib] Hab Hcur HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  step. step. step.
  iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapq");
    [reflexivity | vx | left; reflexivity | arith | arith | unfold ptr_add; cbn [ptr_addr]; lia |].
  iNext. iIntros "Hl Hcur _". check "Hl".
  store_pointer "Hl Hab" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hab". check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
  store_word "Hl Hib" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hib". step. step. rewrite ?(Z.mod_small c (2 ^ 32)); [|lia]. step. check "Hl".
  store_pointer "Hl Hcur" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hcur". step.
  iApply ("HK" with "[%] Hl [Hib] Hab Hcur"); [split; [xkeep | lk_prove]|].
  iSplit; [iPureIntro; lia|]. rewrite (Z.mod_small (i + 1) (2 ^ 32)); [iAssumption | lia].
Qed.

End next.

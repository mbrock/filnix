(** A long option written without an equals sign may still require an
    argument. This file proves the two ends of that path in glibc's
    long-option parser. When another element of the argument vector is
    left, the parser takes it as the argument and steps the index past
    it. When none is left, the parser stores the option's value as the
    bad option and answers ':' or '?' as the option string asks. Both
    ends write only the parser's own private fields. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongExact GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The required-argument path assigns these names. *)
Definition lreq_names : list name := Eval vm_compute in
  List.map TAtom ["v436"; "chk58"; "v437"; "v438"; "chk59"; "v443"; "v445"; "v447"; "v450"; "v451"; "chk61";
    "v452"; "v453"; "v454"; "chk62"; "v455"; "chk63"; "v473"; "v475"; "chk67"; "v476"; "chk68"; "chk69";
    "v482"; "v483"; "v484"]%string.


(** The store module supplies the option table, the report rule and the tactics. *)
Import GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section tail.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance tail_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance tail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The index has stepped to i + 1, and the element at i + 1 is below the
    count n. It becomes the argument, and the index steps to i + 2. *)
Lemma wp_long_next ks e fr i n a b r av ar ps Φ :
  avoids ks lreq_names = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk47") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk59") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= i -> i + 1 < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 a -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 (i + 2) -∗ pcell b 16 (nth (Z.to_nat (i + 1)) ps null) -∗ live av ar -∗
     argv_cells av ps -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L398") (Some (TAtom "L439"))))
       : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L439") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks H2 H12 Hc0 Hc47 Hc59 Hi Hlt Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi0 Hib] Hab Ha Hcl #Hs HK".
  set (k := Z.to_nat (i + 1)). assert (Hkk : Z.of_nat k = i + 1) by (unfold k; lia).
  destruct (lookup_lt_is_Some_2 ps k) as [q Hq]; [lia|].
  iDestruct (big_sepL_lookup with "Hs") as (s1) "#Hws1"; [exact Hq|].
  iDestruct (argv_str_cap with "Hws1") as (rq1) "[#Hcapq1 %Hq1]".
  step. step. load_s32_using ltac:(arith) "Hl Hib". step. check "Hl".
  iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | StrlenLoop.arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hib". step. step. step. idx (i + 1). check "Ha".
  iDestruct (big_sepL_lookup_acc with "Hcl") as "[Hcj Hcl]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq1"); [reflexivity | vx | left; reflexivity | StrlenLoop.arith | StrlenLoop.arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hcl" with "Hcj"). check "Hl".
  iApply (wp_raw_store_pointer with "Hl Hab"); [vx | vx | reflexivity | StrlenLoop.arith | StrlenLoop.arith | wi_store |].
  iNext. iIntros "Hl Hab". step.
  iApply ("HK" with "[%] Hl [Hib] [Hab] Ha Hcl"); [xkeep | | unfold k in Hq; by rewrite (nth_lookup_Some _ _ _ _ Hq)].
  iSplit; [iPureIntro; lia|]. by replace (i + 2) with (i + 1 + 1) by lia.
Qed.

(** No element is left for the argument of the found entry x. The bad
    option becomes the value of x, and the answer v484 is ':' when the
    option string po starts with a colon and '?' otherwise. *)
Lemma wp_long_miss_tail ks e fr lo os j x p1 po so oo b r Φ :
  avoids ks lreq_names = true ->
  lookup (TAtom "v4") e = Some (WPtr po) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk58") e = Some (WPtr p1) -> ptr_cap p1 = ptr_cap lo ->
  os !! j = Some x -> 0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded po so -∗ live b r -∗ int_cell b 8 oo -∗
  (∀ e', ⌜keeps ks e e' /\ lookup (TAtom "v484") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
     live b r -∗ int_cell b 8 (lo_val x) -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L479") [] (JRet (Tmp (TAtom "v484")))))
       : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L458") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks H4 H12 H7 Hc0 Hc58 Hp1 Hx Hb Hal Hend Hr. pose proof (lookup_lt_Some _ _ _ Hx) as Hjl.
  iIntros "#Ht #Hpo Hl [%Hoo Hoob] HK".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(_ & _ & _ & _ & #Hvl)"; [exact Hx|].
  iDestruct "Hvl" as "[%Hv0 Hvb]".
  iDestruct (ws_shape with "Hpo") as %(Hcho & Hpop & Hpoe).
  pose proof (sbyte_range so 0 Hcho) as Hs0r.
  step. step. step.
  iApply (wp_half_check_read_dq w0 registry ge with "Htl");
    [reflexivity | vx | cbn; rewrite Hp1; reflexivity | exact Htc | al8 | al8 | lia | lia | apply Z.mod_1_r |].
  iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Htl Hvb");
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | exact Htc | rawa |].
  iNext; iIntros "_ _". check "Hl".
  iApply (wp_raw_store_w with "Hl Hoob"); [vx | vx | reflexivity | StrlenLoop.arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hoob". rewrite (Z.mod_small (lo_val x) (2 ^ 32)); [|lia].
  iDestruct (ws_byte po so 0 with "Hpo") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | rawa | rawa | apply Z.mod_1_r |]; iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | rawa |].
  iNext; iIntros "_ _". iClear "Hbl Hbt". step. rewrite chr_cmp; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte so 0) 58) as [E58 | E58]; close_br.
  - step. iApply ("HK" with "[%] Hl [Hoob]"); [split; [xkeep | lk_prove] | by iSplit].
  - step. step. step. iApply ("HK" with "[%] Hl [Hoob]"); [split; [xkeep | lk_prove] | by iSplit].
Qed.

End tail.

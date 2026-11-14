(** A short option with a required argument and nothing left to take
    has no argument. glibc's scanner then records the option character
    as the bad option, reports it on stderr if the caller lets it print
    errors, and answers ':' or '?' as the option string asks. This file
    proves that tail safe: the scanner reads the option string only at
    its first byte and writes only the fields of its own state, and the
    report goes through the caller's rule. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The required-argument blocks assign these names. *)
Definition req_names : list name := Eval vm_compute in
  List.map TAtom ["v641"; "v642"; "chk172"; "v643"; "v644"; "v646"; "v648"; "v649"; "chk174"; "chk175";
    "v651"; "v652"; "chk176"; "chk177"; "v657"; "v659"; "v675"; "chk180"; "chk181"; "v682"; "v683"; "v685";
    "v688"; "v689"; "chk183"; "v690"; "v691"; "v692"; "chk184"; "v693"; "chk185"; "pr.7"; "v695";
    "chk186"]%string.


(** The report module supplies the diagnostic rule, the argument vector and its tactics. *)
Import GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic loads an owned private integer field as a signed 32-bit value. *)


(** This tactic reads a lookup through names that a report keeps. *)
Ltac viakeep H := erewrite (keeps_in _ _ _ _ H); [lk_prove | cbn; tauto].

(** This tactic closes a bound on a raw address inside a shared string. *)
Ltac rawa := unfold raw_address, ptr_add; cbn [ptr_addr]; rewrite ?(Z.mod_small _ (2 ^ 64)); lia.

(** The missing-argument tail reads these names from the scanner's environment. *)
Definition tail_keys : list name := Eval vm_compute in
  List.map TAtom ["v12"; "v455"; "chk0"; "chk19"; "pr.1"; "chk20"]%string.

(** Names avoid a list after other names exactly when both lists avoid it. *)
Lemma avoids_app_l xs ks W : avoids (xs ++ ks) W = avoids xs W && avoids ks W.
Proof. unfold avoids. apply forallb_app. Qed.

Section tail.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance tail_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance tail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A renewed read of a pointer into a shared object needs only a share
    of that object's lifetime. *)
Lemma wp_renew_read_dq f e ls l d lo hi al args rest j classes p1 p b reg dq Φ :
  op_arg_classes (Renew lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Renew lo hi Read al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp1 Hp H1 H2 H3. apply (wp_read_dq registry (os_wi w0) ge dq _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_renew; [exact Hp1|]. eapply access_read; eauto.
Qed.

(** When no argument is left, the scanner stores the option character c
    as the bad option, and answers ':' when the option string so starts
    with a colon and '?' otherwise. The cursor x becomes null. *)
Lemma wp_getopt_miss_tail ks e0 e fr c po so oo x b r Φ :
  avoids ks req_names = true -> keeps ks e0 e ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= c < 2 ^ 32 -> 0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded po so -∗ live b r -∗ int_cell b 8 oo -∗ pcell b 32 x -∗
  (∀ e', ⌜keeps ks e0 e' /\ lookup (TAtom "pr.7") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
     live b r -∗ int_cell b 8 c -∗ pcell b 32 null -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L662") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H12 H455 Hc0 Hc19 Hpo Hc20 Hc Hb Hal Hend Hr.
  iIntros "#Hpo Hl [%Hoo Hoob] Hcur HK".
  iDestruct (ws_shape with "Hpo") as %(Hcho & Hpop & Hpoe).
  pose proof (sbyte_range so 0 Hcho) as Hs0r.
  step. step. check "Hl".
  iApply (wp_raw_store_w with "Hl Hoob"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hoob".
  iDestruct (ws_byte po so 0 with "Hpo") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  iApply (wp_renew_read_dq with "Hbl"); [reflexivity | vx | reflexivity | exact Hcap | rawa | rawa | apply Z.mod_1_r |].
  iNext. iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | rawa |].
  iNext; iIntros "_ _". iClear "Hbl Hbt". step. rewrite chr_cmp; [|lia|lia].
  rewrite (Z.mod_small c (2 ^ 32)); [|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte so 0) 58) as [E58 | E58]; close_br.
  - step. step. check "Hl".
    iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hcur". step.
    iApply ("HK" with "[%] Hl [Hoob] Hcur"); [split; [xkeep | lk_prove] | by iSplit].
  - step. step. step. step. check "Hl".
    iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hcur". step.
    iApply ("HK" with "[%] Hl [Hoob] Hcur"); [split; [xkeep | lk_prove] | by iSplit].
Qed.

(** When the cluster ends at the last argument, nothing is left for the
    required argument. If the caller lets the scanner print errors, its
    rule for the report keeps G. The tail then records the bad option
    and answers. *)
Lemma wp_getopt_reqmiss ks e0 e fr c pe po so oo x b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
  avoids ks req_names = true -> avoids ks diag_names = true -> keeps ks e0 e ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded po so -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 8 oo -∗ pcell b 32 x -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e0 e' /\ lookup (TAtom "pr.7") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
     live b r -∗ int_cell b 8 c -∗ pcell b 32 null -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L653") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksd Hk0 Hrule Hse Hmid H2 H12 H455 Hpo Hpe Hc0 Hc19 Hc20 Hc Hper Hb Hal Hend Hr Hav Hala Hda Hra Hps
    Hse0 Hsea Hsee Hser.
  iIntros "#Hpo #Hsl #Hsc Hl Hoo Hcur Ha Hcl #Hs HG HK".
  step. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small pe (2 ^ 32)); [|lia].
  destruct (Z.eqb_spec pe 0) as [Ep | Ep]; cbn [edge_label].
  - iApply (wp_getopt_miss_tail ks e0 with "Hpo Hl Hoo Hcur");
      [exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | exact Hc | exact Hb
      | exact Hal | exact Hend | exact Hr |].
    iIntros (e2) "Hk Hl Hoo Hcur". iApply ("HK" with "Hk Hl Hoo Hcur Ha Hcl HG").
  - iApply (wp_getopt_diag_missing w0 registry ge (tail_keys ++ ks) with "Hsl Hsc Ha Hcl Hs HG [Hl Hoo Hcur HK]");
      [rewrite avoids_app_l; rewrite Hksd; vm_compute; reflexivity | exact Hrule | exact Hse | exact Hmid | lk_prove
      | lk_prove | exact Hc | exact Hse0 | exact Hsea | exact Hsee | exact Hser | exact Hav | exact Hala | exact Hda
      | exact Hra | exact Hps |].
    iIntros (e1) "%Hk1 Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
    iApply (wp_getopt_miss_tail ks e0 with "Hpo Hl Hoo Hcur");
      [ exact Hks | (eapply keeps_trans; [|exact Hk1]; xkeep) | viakeep Hkt | viakeep Hkt | viakeep Hkt
      | viakeep Hkt | viakeep Hkt | viakeep Hkt | exact Hc | exact Hb | exact Hal | exact Hend | exact Hr |].
    iIntros (e2) "Hk Hl Hoo Hcur". iApply ("HK" with "Hk Hl Hoo Hcur Ha Hcl HG").
Qed.

End tail.

From Glibc Require Import GlibcProgram.
(** A long option may carry its argument after an equals sign, as in
    "--name=value". glibc's long-option parser then makes the rest of the
    word after the equals sign the argument when the option takes one.
    When the option takes none, the parser reports the misuse, stores the
    option's value as the bad option, and answers '?'. This file proves
    that part of the parser safe: it reads only the found table entry
    and writes only the parser's own private fields. *)

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
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongExact GetoptLongReq GetoptLongScan GetoptLongStore GetoptLongTail GetoptReqTail GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The equals-sign path assigns these names. *)
Definition leq_names : list name := Eval vm_compute in
  List.map TAtom ["v405"; "chk51"; "v406"; "v408"; "v410"; "chk52"; "v428"; "v430"; "chk56"; "v431"; "chk57"]%string.

(** The report keeps these names for the block after it. *)
Definition leq_keys : list name := Eval vm_compute in
  List.map TAtom ["v12"; "pr.7"; "chk0"; "chk51"]%string.


(** The required-argument module supplies the option table, the report rule and the tactics. *)
Import GetoptLongReq GetoptLongTail GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section eq.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance eq_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser has found the entry x at index j of the table lo, and the
    name at the cursor cur ends with an equals sign at pr.1. When x takes
    an argument, the rest of the word after the equals sign becomes the
    argument. Otherwise the report rule keeps G, the bad option becomes
    the value of x, and the parser answers '?'. *)
Lemma wp_long_eq ks e fr (G : iProp Σ) T fp dom se sereg mid av ar ps lo os j x pfx sp cur s pe oo a b r Φ :
  avoids ks leq_names = true -> avoids ks ldiag_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "pr.1") e = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  os !! j = Some x -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx sp -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  ((∀ e', ⌜keeps ks e e' /\ lo_has x <> 0⌝ -∗
      live b r -∗ int_cell b 8 oo -∗ pcell b 16 (ptr_add cur (Z.of_nat (eq_len s) + 1)) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L398") (Some (TAtom "L401"))))
        : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ lo_has x = 0⌝ -∗
      live b r -∗ int_cell b 8 (lo_val x) -∗ pcell b 16 a -∗ live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L413") [] (JRet (Const 63)))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L396") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksd Hrule Hse Hmid H2 H12 H14 H16 H7 Hp1 Hc0 Hx Hpe
    Hb Hal Hend Hr Hav Hala Hda Hra Hps Hse0 Hsea Hsee Hser.
  pose proof (lookup_lt_Some _ _ _ Hx) as Hjl.
  iIntros "#Ht #Hpfx #Hws #Hsl #Hsc Hl [%Hoo Hoob] Hab Ha Hcl #Hs HG HK".
  iPoseProof "Ht" as "Ht0".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(_ & _ & #Hhl & _ & #Hvl)"; [exact Hx|].
  iDestruct "Hhl" as "[%Hh0 Hhb]". iDestruct "Hvl" as "[%Hv0 Hvb]".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe). pose proof (eq_len_le s) as Hle.
  step. step.
  check_read_dq "Htl" by rawa; iNext; iIntros "_".
  load_bytes_dq "Htl Hhb" decode (apply load_sw_int; assumption) by rawa.
  iNext; iIntros "_ _".
  iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small (lo_has x) (2 ^ 32)); [|lia].
  destruct (Z.eqb_spec (lo_has x) 0) as [E0 | E0]; cbn [edge_label].
  2: { iDestruct "HK" as "[HK _]". step. step. step. check "Hl".
       store_pointer "Hl Hab" by (StrlenLoop.arith) preserving wi_store.
       iNext. iIntros "Hl Hab". step.
       match goal with |- context [pcell b 16 ?X] =>
         replace X with (ptr_add cur (Z.of_nat (eq_len s) + 1)) by
           (unfold ptr_add; cbn [ptr_addr ptr_cap]; f_equal; rewrite (Z.mod_small 1 (2 ^ 64)); [|lia];
            rewrite (Z.mod_small (ptr_addr cur + _) (2 ^ 64)); [|lia]; rewrite Z.mod_small; lia) end.
       iApply ("HK" with "[%] Hl [Hoob] Hab Ha Hcl HG"); [split; [xkeep | exact E0] | by iSplit]. }
  iDestruct "HK" as "[_ HK]".
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "pr.7") e1 = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) /\
      lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
      lookup (TAtom "chk51") e1 = Some (WPtr (mkPtr ((ptr_addr (ptr_add lo (32 * Z.of_nat j)) mod 2 ^ 64 + 8 mod 2 ^ 64)
        mod 2 ^ 64) (ptr_cap (ptr_add lo (32 * Z.of_nat j)))))⌝ -∗
    live av ar -∗ argv_cells av ps -∗ G -∗
    WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L413") (Some fr1))) : gexpr) {{ Φ }})%I
    with "[Hl Hoob Hab HK]" as "HL413".
  { iIntros (e1 fr1 (Hk1 & H12' & H7' & Hc0' & Hc51')) "Ha Hcl HG".
    step. step. step.
    iApply (wp_half_check_read_dq with "Htl");
      [reflexivity | vx | reflexivity | exact Htc | al8 | al8 | lia | lia | apply Z.mod_1_r |].
    iNext; iIntros "_".
    load_bytes_dq "Htl Hvb" decode (apply load_sw_int; assumption) by rawa.
    iNext; iIntros "_ _". check "Hl".
    store_word "Hl Hoob" by (StrlenLoop.arith) preserving wi_store.
    iNext. iIntros "Hl Hoob". rewrite (Z.mod_small (lo_val x) (2 ^ 32)); [|lia].
    iApply ("HK" with "[%] Hl [Hoob] Hab Ha Hcl HG"); [split; [eapply keeps_trans; [exact Hk1|]; xkeep | exact E0] | by iSplit]. }
  step. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small pe (2 ^ 32)); [|lia].
  destruct (Z.eqb_spec pe 0) as [Ep | Ep]; cbn [edge_label].
  - iApply ("HL413" with "[%] Ha Hcl HG"). split; [xkeep|]. repeat split; lk_prove.
  - iApply (wp_getopt_ldiag_noarg (leq_keys ++ ks) with "Ht0 Hpfx Hsl Hsc Ha Hcl Hs HG [HL413]");
      [rewrite avoids_app_l; rewrite Hksd; vm_compute; reflexivity | exact Hrule | exact Hse | exact Hmid | lk_prove
      | lk_prove | lk_prove | lk_prove | reflexivity | exact Hx | exact Hse0 | exact Hsea | exact Hsee | exact Hser
      | exact Hav | exact Hala | exact Hda | exact Hra | exact Hps |].
    iIntros (e1) "%Hk1 Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
    iApply ("HL413" with "[%] Ha Hcl HG"). split; [(eapply keeps_trans; [|exact Hk1]; xkeep)|].
    repeat split; viakeep Hkt.
Qed.

End eq.

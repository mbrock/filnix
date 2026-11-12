(** In long-only mode, the scanner tries a single-dash argument as a
    long option unless the argument is one character that the short
    option string names. This file proves that test safe: the scanner
    reads the argument's third byte only when its second byte is not the
    terminator, and it looks the second byte up in the short option
    string with glibc's own strchr. When the long-option parser is to
    run, the scanner first stores the private cursor one byte into the
    argument. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The long-only test assigns these names. *)
Definition long_only_names : list name :=
  List.map TAtom ["v384"; "v385"; "v386"; "v387"; "chk123"; "v388"; "v389"; "chk124"; "v390"; "v396"; "v397";
    "v398"; "v399"; "chk126"; "v400"; "v401"; "chk127"; "v402"; "v403"; "v404"; "v406"; "v410"]%string
  ++ long_cursor_names.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongOnlyOn (R : Runtime) (LG0 : LogicSig R).
(** The cursor module stores the cursor before the long-option parser. *)
Module CU := GetoptCursorOn R LG0.
Import CU CU.X CU.X.I CU.X.I.S CU.X.I.S.FI CU.X.I.S.FI.ML CU.X.I.S.FI.LG CU.X.I.S.FI.L CU.X.I.ST CU.X.I.GB CU.X.A.
(** The strchr module proves glibc's own strchr. *)
Module SC := StrchrnulLogicOn R LG0.

(** This tactic enters a block and evaluates its phi assignments. *)
Ltac en := iApply wp_enter; [reflexivity | reflexivity | iNext]; cbn [b_insts b_jump].

(** This tactic loads an owned private integer field as a signed 32-bit value. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | arith |];
  iNext; iIntros H.

Section long_only.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance long_only_stable : SafepointStable (os_wi w0) := CU.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance long_only_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic checks and loads byte k, which lies inside the shared string s at q, as a signed byte. *)
Ltac rdin q s k :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  let Hcap := fresh "Hcap" in
  iDestruct (ws_byte q s k with "Hws") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|];
  destruct Hbb as (Hcap & ? & ? & ? & ?);
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | arith | cbn [ptr_addr]; unfold raw_address; rewrite Z.mod_small; lia | arith |];
  iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |];
  iNext; iIntros "_ _"; iClear "Hbl Hbt".

(** The test runs at an option in argument i, below the argument count
    n. The argument is a shared string s that starts with a dash, has a
    second character, and does not start with two dashes. The caller
    supplies the short option string po and the facts that the linked
    names __GI_strchr and __GI___strchrnul are glibc's functions. Outside
    long-only mode, and for a named single character, the scanner turns
    to the short options without any write. Otherwise it reaches the
    long-option parser with the cursor one byte into the argument. *)
Lemma wp_getopt_long_only ks e i n c lonly po so b r av ar ps s Φ :
  avoids ks long_only_names = true ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk100") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  sbyte s 0 = 45 -> sbyte s 1 <> 0 -> sbyte s 1 <> 45 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  word_string DfracDiscarded (nth (Z.to_nat i) ps null) s -∗ word_string DfracDiscarded po so -∗
  live b r -∗ int_cell b 0 i -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ e' fr, ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L338") (Some fr))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ lonly mod 2 ^ 32 <> 0⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add (nth (Z.to_nat i) ps null) 1) -∗
      live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L376") long_only_call long_only_jump))
            : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L344") (Some (TAtom "L336")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks Hg Hgn Hv2 Hv10 Hv12 Hpo Hc2 Hc20 Hc100 Hi Hn Hlen Hs0 Hs1 Hs45 Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "#Hws #Hpo Hl [%Hi0 Hib] Hcur Ha Hc #Hs HK".
  set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  assert (Hnq : nth j ps null = q) by (by rewrite (nth_lookup_Some _ _ _ _ Hq)).
  fold j. rewrite Hnq.
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  pose proof (sbyte_in_len s 1 Hs1) as Hl1.
  iAssert ((∀ e2 fr, ⌜keeps ks e e2 /\ lonly mod 2 ^ 32 <> 0 /\
      lookup (TAtom "v2") e2 = Some (WPtr (mkPtr av (Obj av))) /\
      lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk2") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk20") e2 = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
    live b r -∗ bytes b 0 (int_bytes i) -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L376") (Some fr))) : gexpr) {{ Φ }}) ∧
    (∀ e' fr, ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L338") (Some fr))) : gexpr) {{ Φ }}))%I
    with "[HK]" as "HL".
  { iSplit; [|iDestruct "HK" as "[HK _]"; iExact "HK"].
    iIntros (e2 fr (Hk & El & H2 & H12 & H2' & H20)) "Hl Hib Hcur Ha Hc".
    pose proof (avoids_app _ _ _ Hks) as [_ Hkc].
    iApply (wp_getopt_long_cursor w0 registry ge ks e2 fr i n c b r av ar ps with "Hl [Hib] Hcur Ha Hc Hs [HK]");
      [ exact Hkc | exact H2 | exact H12 | exact H2' | exact H20 | lia | lia | exact Hlen
      | lia | lia | lia | lia | lia | lia | lia | lia | by iSplit |].
    iIntros (e' Hk') "Hl Hi Hcur Ha Hc". iDestruct "HK" as "[_ HK]". fold j. rewrite Hnq.
    iApply ("HK" with "[%] Hl Hi Hcur Ha Hc"). split; [eapply keeps_trans; [exact Hk | exact Hk'] | exact El]. }
  en. iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (lonly mod 2 ^ 32) 0) as [El | El]; cbn [edge_label].
  { en. iApply wp_branch; [vx | iNext]. close_br. iDestruct "HL" as "[_ HL]".
    iApply ("HL" with "[%] Hl [Hib] Hcur Ha Hc"); [xkeep | by iSplit]. }
  en. load_int "Hl Hib". st. st. st. idx i. chk "Ha".
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq");
    [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). st. norm.
  rdin q s 2%nat. iApply wp_branch; [vx | iNext].
  pose proof (sbyte_range s 2 Hch) as Hs2r.
  rewrite (Z.mod_small (chr_w (sbyte s 2)) (2 ^ 32)); [|apply chr_w_range].
  rewrite chr_w_eqb; [|lia|lia].
  destruct (Z.eqb_spec (sbyte s 2) 0) as [E2 | E2]; cbn [edge_label].
  2:{ en. iApply wp_branch; [vx | iNext]. close_br. iDestruct "HL" as "[HL _]".
      iApply ("HL" with "[%] Hl Hib Hcur Ha Hc"). split; [xkeep|]. split; [exact El|]. repeat split; lk_prove. }
  en. load_int "Hl Hib". st. st. st. idx i. chk "Ha".
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq");
    [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). st. norm.
  rdin q s 1%nat.
  iApply (SC.wp_call_glibc_strchr registry (os_wi w0) ge with "Hpo");
    [vx | apply Z.mod_pos_bound; lia | exact Hg | exact Hgn | reflexivity |].
  iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. st. st. st. en.
  iApply wp_branch; [vx | iNext].
  match goal with |- context [edge_label (if ?c then _ else _)] => destruct c end; cbn [edge_label].
  - iDestruct "HL" as "[_ HL]". iApply ("HL" with "[%] Hl [Hib] Hcur Ha Hc"); [xkeep | by iSplit].
  - iDestruct "HL" as "[HL _]".
    iApply ("HL" with "[%] Hl Hib Hcur Ha Hc"). split; [xkeep|]. split; [exact El|]. repeat split; lk_prove.
Qed.

End long_only.
End GetoptLongOnlyOn.

(** In permuting mode, glibc's scanner skips the nonoptions that follow
    the public index before it looks for an option. An argument is a
    nonoption when its first character is not a dash, or when it is the
    single dash. This file proves that test safe: it reads only the
    argument's terminated string, and its second byte only after the
    first byte showed that the string is not empty. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange
  GetoptPermute.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The nonoption test assigns these names. *)
Definition test_names : list name := Eval vm_compute in
  List.map TAtom ["v170"; "v171"; "v172"; "v173"; "chk59"; "v174"; "chk60"; "v176"; "v177"; "v182";
    "v183"; "v184"; "v185"; "chk62"; "v186"; "v187"; "chk63"; "v188"; "v189"; "v193"]%string.

(** A string whose first character is a dash has a second byte. *)
Lemma dash_len (s : list Z) : sbyte s 0 = 45 -> (1 <= List.length s)%nat.
Proof. destruct s; [discriminate | cbn; lia]. Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptSkipTestOn (R : Runtime) (LG0 : LogicSig R).
(** The exchange module supplies the argument vector and its tactics. *)
Module X := GetoptExchangeOn R LG0.
Import X X.I X.I.S X.I.S.FI X.I.S.FI.ML X.I.S.FI.LG X.I.S.FI.L X.I.ST X.I.GB X.A.

(** This tactic enters a block and evaluates its phi assignments. *)
Ltac en := iApply wp_enter; [reflexivity | reflexivity | iNext]; cbn [b_insts b_jump].

(** This tactic loads an owned private integer field as a signed 32-bit value. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | arith |];
  iNext; iIntros H.

(** This tactic rebuilds an integer field from its rewritten bytes. *)
Ltac icell := iSplit; [iPureIntro; lia | iAssumption].

Section test.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance test_stable : SafepointStable (os_wi w0) := X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic checks and loads byte k of the shared string H at q as a signed byte. *)
Ltac rdchr H q s k :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  iDestruct (ws_byte q s k with H) as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|];
  destruct Hbb as (Hcap & Hb0' & Hbq & Hbe & Hbr);
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | arith | arith | arith |]; iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |];
  iNext; iIntros "_ _".

(** The test reads argument i, which lies below n. A nonoption
    reaches the loop's increment and an option reaches its exit; both
    keep the private index field and the argument vector. *)
Lemma wp_skip_test ks e i n b r av ar ps Φ :
  avoids ks test_names = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "chk57") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ bytes b 0 (int_bytes i) -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ e2 fr, ⌜keeps ks e e2⌝ -∗ live b r -∗ bytes b 0 (int_bytes i) -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L161") (Some fr))) : gexpr) {{ Φ }}) ∧
   (∀ e2 fr, ⌜keeps ks e e2⌝ -∗ live b r -∗ bytes b 0 (int_bytes i) -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L160") (Some fr))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L166") (Some (TAtom "L159")))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv2 Hc57 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl Hib Ha Hc #Hs HLs".
  assert (Hi0 : 0 <= i < 2 ^ 32) by lia.
  en. load_int "Hl Hib". st. st. st. idx i. chk "Ha".
  set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iDestruct (big_sepL_lookup with "Hs") as (s) "#Hws"; [exact Hq|].
  iDestruct (argv_str_cap with "Hws") as (rq) "[Hcapq %Hq0]".
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj").
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  rdchr "Hws" q s 0%nat. st.
  pose proof (sbyte_range s 0 Hch) as Hs0.
  rewrite (Z.mod_small (chr_w (sbyte s 0)) (2 ^ 32)); [|apply chr_w_range].
  change (45 mod 2 ^ 32) with 45. rewrite chr_w_eqb; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte s 0) 45) as [E45 | E45]; close_br.
  2:{ en. brz. iDestruct "HLs" as "[_ HL]". iApply ("HL" with "[%] Hl Hib Ha Hc"). xkeep. }
  pose proof (dash_len s E45) as Hs1.
  en. load_int "Hl Hib". st. st. st. idx i. chk "Ha".
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj").
  st. norm. iClear "Hbl Hbt". clear Hcap Hb0' Hbq Hbe Hbr.
  iDestruct (ws_byte q s 1 with "Hws") as (bb1 breg1) "(%Hbb1 & #Hbl & #Hbt)"; [lia|].
  destruct Hbb1 as (Hcap & Hb0' & Hbq & Hbe & Hbr).
  assert (Hlen1 : 1 <= Z.of_nat (List.length s)) by lia.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | arith | cbn [ptr_addr]; unfold raw_address; rewrite Z.mod_small; lia | arith |]; iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |].
  iNext; iIntros "_ _". st. st. en.
  pose proof (sbyte_range s 1 Hch) as Hs1'. rewrite chr_cmp; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte s 1) 0) as [E0 | E0]; close_br.
  - iDestruct "HLs" as "[_ HL]". iApply ("HL" with "[%] Hl Hib Ha Hc"). xkeep.
  - iDestruct "HLs" as "[HL _]". iApply ("HL" with "[%] Hl Hib Ha Hc"). xkeep.
Qed.

End test.
End GetoptSkipTestOn.

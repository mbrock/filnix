(** A short option with an optional argument takes the rest of its
    cluster as that argument. glibc's scanner reads the byte at its
    private cursor. When that byte is not the terminator, the private
    option argument becomes the cursor, and the public index steps past
    the cluster. At the end of the cluster the option argument becomes
    null, and the index had already stepped past it. Either way the
    cursor becomes null. This file proves that step safe: the scanner
    reads only the cursor's string and writes only its own fields. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic GetoptModule
  GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptShort.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The option blocks after the strchr lookup assign these names. *)
Definition opt_names : list name := Eval vm_compute in
  List.map TAtom ["chk144"; "v513"; "v514"; "v518"; "chk145"; "v519"; "v520"; "v522"; "v526"; "v528"; "v530";
    "v607"; "chk161"; "v608"; "v609"; "v614"; "chk162"; "v615"; "v616"; "v621"; "v622"; "chk164"; "v623";
    "v624"; "v626"; "v628"; "v629"; "chk166"; "chk167"; "v631"; "v632"; "chk168"; "v634"; "chk169"; "v636";
    "chk170"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptOptArgOn (R : Runtime) (LG0 : LogicSig R).
(** The character module supplies the argument vector and its tactics. *)
Module SH := GetoptShortOn R LG0.
Import SH SH.X SH.X.I SH.X.I.S SH.X.I.S.FI SH.X.I.S.FI.ML SH.X.I.S.FI.LG SH.X.I.S.FI.L SH.X.I.ST SH.X.I.GB SH.X.A.

(** This tactic enters a block and evaluates its phi assignments. *)
Ltac en := iApply wp_enter; [reflexivity | reflexivity | iNext]; cbn [b_insts b_jump].

(** This tactic loads an owned private integer field as a signed 32-bit value. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | arith |];
  iNext; iIntros H.

(** This tactic closes a bound on a raw address inside a shared string. *)
Ltac rawa := unfold raw_address, ptr_add; cbn [ptr_addr]; rewrite ?(Z.mod_small _ (2 ^ 64)); lia.

Section optarg.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance optarg_stable : SafepointStable (os_wi w0) := SH.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance optarg_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The scanner has just stepped over an option character in the
    cluster t, and that option takes an optional argument. The private
    option argument becomes the rest of the cluster, or null when nothing
    is left of it. The public index ends one past the cluster's position
    i in both cases, and the cursor becomes null. The names ks keep their
    values from the caller's environment e0. *)
Lemma wp_getopt_optarg ks e0 e fr i cur t a b r Φ :
  avoids ks opt_names = true -> keeps ks e0 e ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < 2 ^ 31 - 1 -> sbyte t 0 <> 0 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗
  live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗ pcell b 32 (ptr_add cur 1) -∗
  (∀ e', ⌜keeps ks e0 e'⌝ -∗
     live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗
     pcell b 32 null -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L619")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L610") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H12 Hc1 Hc2 Hc20 H137 Hi Ht0 Hb Hal Hend Hr.
  iIntros "#Hws Hl Hib Hab Hcur HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  pose proof (sbyte_in_len t 0 Ht0) as Hlt. pose proof (sbyte_range t 1 Hch) as Ht1r.
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  en. st.
  iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapq");
    [reflexivity | vx | left; reflexivity | arith | arith | unfold ptr_add; cbn [ptr_addr]; lia |].
  iNext. iIntros "Hl Hcur _".
  iDestruct (ws_byte cur t 1 with "Hws") as (bb1 breg1) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap' & ? & ? & ? & ?).
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap' | rawa | rawa | apply Z.mod_1_r |]; iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap' | rawa |].
  iNext; iIntros "_ _". iClear "Hbl Hbt". st.
  rewrite (Z.mod_small (chr_w (sbyte t 1)) (2 ^ 32)); [|apply chr_w_range].
  change (0 mod 2 ^ 32) with 0. rewrite chr_w_eqb; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte t 1) 0) as [E1 | E1]; close_br.
  - en. st. chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hab"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hab". st. en. st. chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hcur". st.
    iApply ("HK" with "[%] Hl Hib Hab Hcur"). xkeep.
  - iDestruct "Hib" as "[%Hi0 Hib]".
    en. st. st.
    iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapq");
      [reflexivity | vx | left; reflexivity | arith | arith | unfold ptr_add; cbn [ptr_addr]; lia |].
    iNext. iIntros "Hl Hcur _". chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hab"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hab". chk "Hl". load_int "Hl Hib". st. norm. chk "Hl".
    iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hib". st. en. st. chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hcur". st.
    iApply ("HK" with "[%] Hl [Hib] Hab Hcur"); [xkeep|].
    iSplit; [iPureIntro; lia|]. rewrite (Z.mod_small (i + 1) (2 ^ 32)); [iAssumption | lia].
Qed.

End optarg.
End GetoptOptArgOn.

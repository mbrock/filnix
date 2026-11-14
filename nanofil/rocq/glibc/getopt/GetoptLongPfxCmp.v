From Glibc Require Import GlibcProgram.
(** When glibc's long-option parser finds no entry whose name equals the
    word's name, it looks for entries whose names start with it. A
    second such entry makes the word ambiguous unless it means the same
    as the first: the same argument rule, the same flag pointer and the
    same value. In long-only mode every second entry counts as
    ambiguous. This file proves that comparison safe. The parser reads
    each field of the two entries inside the caller's table. It reads
    a flag pointer only while it holds the flag target's lifetime, which
    the caller lends it from the targets that it owns. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly
  GetoptLongMiss.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongExact GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The comparison assigns these names. *)
Definition pcmp_names : list name := Eval vm_compute in
  List.map TAtom ["v133"; "chk11"; "v134"; "v136"; "chk12"; "v137"; "v138"; "v140"; "v144"; "chk13"; "v145";
    "v147"; "chk14"; "v148"; "v149"; "v150"; "v151"; "v153"; "v157"; "chk15"; "v158"; "v160"; "chk16"; "v161";
    "v162"; "v164"]%string.

(** The flag test starts in this block. *)
Definition plo_blk131 : block := Eval vm_compute in plo_blk "L131".
(** The value test starts in this block. *)
Definition plo_blk142 : block := Eval vm_compute in plo_blk "L142".
(** The comparison decides in this block. *)
Definition plo_blk155 : block := Eval vm_compute in plo_blk "L155".


(** The not-found module supplies the option table, the targets and the tactics. *)
Import GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic hands the comparison's outcome to the caller. *)
Ltac pcmp_fin := first
  [ iDestruct "HK" as "[HK _]"; iApply ("HK" with "[%] HF"); xkeep
  | iDestruct "HK" as "[_ HK]"; iApply ("HK" with "[%] HF"); xkeep ].

(** This tactic folds the entered block L back into its definition B. *)
Ltac pcmp_fold L B := cbn [edge_label]; lazymatch goal with |- environments.envs_entails _ ?P =>
  lazymatch P with context [Exec (TAtom L) ?i ?j] =>
    change (Exec (TAtom L) i j) with (Exec (TAtom L) (b_insts B) (b_jump B)) end end.

(** This tactic decides a branch whose condition the proof leaves open. *)
Ltac pcmp_br := iApply wp_branch; [vx | iNext];
  match goal with |- context [edge_label (if ?c then _ else _)] => destruct c end; cbn [edge_label].

Import ProgramAbbreviations.
Section cmp_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
Lemma flag_capq F f :
  f = null \/ f ∈ F ->
  flags_own F ⊢ ∃ reg, ⌜0 <= ptr_addr f < 2 ^ 64⌝ ∗ live_capq (DfracOwn 1) (ptr_cap f) reg ∗
    (live_capq (DfracOwn 1) (ptr_cap f) reg -∗ flags_own F).
Proof.
  intros [-> | Hin]; iIntros "HF".
  - iExists (mkRegion 0 0 Heap Live). iSplit; [iPureIntro; cbn; lia|]. unfold live_capq; cbn.
    iSplit; [done|]. iIntros "_". iExact "HF".
  - iDestruct "HF" as "[%Hnd HF]". apply list_elem_of_lookup_1 in Hin as [k Hk].
    iDestruct (big_sepL_lookup_acc with "HF") as "[Hfc HF]"; [exact Hk|].
    iDestruct "Hfc" as (fv fb freg) "(%Hfp & Hfll & Hfcell)". pose proof Hfp as (Hfc0 & Hfb & Hfa & Hfe & Hfr).
    iExists freg. iSplit; [iPureIntro; lia|]. rewrite Hfc0. iFrame "Hfll".
    iIntros "Hfll". iSplit; [done|]. iApply "HF". iExists fv, fb, freg. iFrame. done.
Qed.
End cmp_values.
Section cmp.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance cmp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** To read a flag pointer, the parser needs a share of the lifetime of
    the integer it points at. The caller owns each flag target in F.
    One target can lend its lifetime for the read and take it back
    afterwards. A null flag needs no lifetime. *)

(** The parser has found a second entry y at index k whose name starts
    with the word's name, after the first such entry x at index j. In
    long-only mode it goes on as for an ambiguous word. Otherwise it
    compares the argument rules, the flag pointers and the values of x
    and y. It goes on as for an ambiguous word when one of them differs,
    and to the next entry when they agree. *)
Lemma wp_long_pfx_cmp ks e lo os j x k y lonly F Φ :
  avoids ks pcmp_names = true ->
  lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "pr.8") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "pr.3") e = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) ->
  lookup (TAtom "chk8") e = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) ->
  os !! j = Some x -> os !! k = Some y -> (List.length os < 2 ^ 31)%Z ->
  lo_flag x = null \/ lo_flag x ∈ F -> lo_flag y = null \/ lo_flag y ∈ F ->
  opt_table lo os -∗ flags_own F -∗
  ((∀ e', ⌜keeps ks e e'⌝ -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L126") (Some (TAtom "L155")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e'⌝ -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L108") (Some (TAtom "L155")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L118") (Some (TAtom "L106")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks H10 H8 H3 Hc8 Hx Hy Hos Hfx Hfy.
  pose proof (lookup_lt_Some _ _ _ Hx) as Hjl. pose proof (lookup_lt_Some _ _ _ Hy) as Hkl.
  iIntros "#Ht HF HK".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(_ & _ & #Hhx & #Hfxl & #Hvx)"; [exact Hx|].
  iDestruct (big_sepL_lookup with "Hes") as "(_ & _ & #Hhy & #Hfyl & #Hvy)"; [exact Hy|].
  iDestruct "Hhx" as "[%Hhx0 Hhxb]". iDestruct "Hhy" as "[%Hhy0 Hhyb]".
  iDestruct "Hvx" as "[%Hvx0 Hvxb]". iDestruct "Hvy" as "[%Hvy0 Hvyb]".
  iAssert (∀ e2, ⌜keeps ks e e2 /\ exists c, lookup (TAtom "v164") e2 = Some (WInt c)⌝ -∗ flags_own F -∗
    WP (ERun (mkFrame glibc_process_long_option e2 [] None
      (Exec (TAtom "L155") (b_insts plo_blk155) (b_jump plo_blk155))) : gexpr) {{ Φ }})%I with "[HK]" as "H155".
  { iIntros (e2 (Hk2 & c & Hc)) "HF". cbn [b_insts b_jump plo_blk155]. pcmp_br; pcmp_fin. }
  iAssert (∀ e2, ⌜keeps ks e e2 /\ lookup (TAtom "pr.8") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) /\
      lookup (TAtom "pr.3") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) /\
      lookup (TAtom "chk8") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) /\
      exists c, lookup (TAtom "v153") e2 = Some (WInt c)⌝ -∗ flags_own F -∗
    WP (ERun (mkFrame glibc_process_long_option e2 [] None
      (Exec (TAtom "L142") (b_insts plo_blk142) (b_jump plo_blk142))) : gexpr) {{ Φ }})%I with "[H155]" as "H142".
  { iIntros (e2 (Hk2 & H82 & H32 & Hc82 & c & Hc)) "HF". cbn [b_insts b_jump plo_blk142]. pcmp_br.
    - step. step.
      check_read_dq "Htl" by rawa; iNext; iIntros "_".
      load_bytes_dq "Htl Hvxb" decode (apply load_sw_int; assumption) by rawa.
      iNext; iIntros "_ _". step.
      iApply (wp_half_check_read_dq with "Htl");
        [reflexivity | vx | reflexivity | exact Htc | al8 | al8 | lia | lia | apply Z.mod_1_r |].
      iNext; iIntros "_".
      load_bytes_dq "Htl Hvyb" decode (apply load_sw_int; assumption) by rawa.
      iNext; iIntros "_ _". step. step. step.
      pcmp_fold "L155" plo_blk155. iApply ("H155" with "[%] HF"). split; [xkeep | eexists; lk_prove].
    - step. pcmp_fold "L155" plo_blk155. iApply ("H155" with "[%] HF"). split; [xkeep | eexists; lk_prove]. }
  iAssert (∀ e2, ⌜keeps ks e e2 /\ lookup (TAtom "pr.8") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) /\
      lookup (TAtom "pr.3") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) /\
      lookup (TAtom "chk8") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) /\
      exists c, lookup (TAtom "v140") e2 = Some (WInt c)⌝ -∗ flags_own F -∗
    WP (ERun (mkFrame glibc_process_long_option e2 [] None
      (Exec (TAtom "L131") (b_insts plo_blk131) (b_jump plo_blk131))) : gexpr) {{ Φ }})%I with "[H142]" as "H131".
  { iIntros (e2 (Hk2 & H82 & H32 & Hc82 & c & Hc)) "HF". cbn [b_insts b_jump plo_blk131]. pcmp_br.
    - step. step.
      check_read_dq "Htl" by first [rawa | al8]; iNext; iIntros "_".
      iDestruct (flag_capq with "HF") as (fr) "(%Hfr & Hcap & HF)"; [exact Hfx|].
      load_pointer_dq "Htl Hfxl Hcap" by first [rawa | al8].
      iNext. iIntros "_ _ Hcap". iSpecialize ("HF" with "Hcap"). step.
      iApply (wp_half_check_read_dq with "Htl");
        [reflexivity | vx | reflexivity | exact Htc | al8 | al8 | lia | lia | al8 |].
      iNext; iIntros "_".
      iDestruct (flag_capq with "HF") as (fr') "(%Hfr' & Hcap & HF)"; [exact Hfy|].
      load_pointer_dq "Htl Hfyl Hcap" by first [rawa | al8].
      iNext. iIntros "_ _ Hcap". iSpecialize ("HF" with "Hcap"). step. step. step. step. step. pcmp_fold "L142" plo_blk142.
      iApply ("H142" with "[%] HF"). split; [xkeep|]. repeat split; [lk_prove | lk_prove | lk_prove | eexists; lk_prove].
    - step. pcmp_fold "L142" plo_blk142. iApply ("H142" with "[%] HF"). split; [xkeep|]. repeat split; [lk_prove | lk_prove | lk_prove | eexists; lk_prove]. }
  step. pcmp_br.
  - step. step.
    check_read_dq "Htl" by rawa; iNext; iIntros "_".
    load_bytes_dq "Htl Hhxb" decode (apply load_sw_int; assumption) by rawa.
    iNext; iIntros "_ _". step.
    iApply (wp_half_check_read_dq with "Htl");
      [reflexivity | vx | reflexivity | exact Htc | al8 | al8 | lia | lia | apply Z.mod_1_r |].
    iNext; iIntros "_".
    load_bytes_dq "Htl Hhyb" decode (apply load_sw_int; assumption) by rawa.
    iNext; iIntros "_ _". step. step. step.
    pcmp_fold "L131" plo_blk131. iApply ("H131" with "[%] HF"). split; [xkeep|]. repeat split; [lk_prove | lk_prove | lk_prove | eexists; lk_prove].
  - step. pcmp_fold "L131" plo_blk131. iApply ("H131" with "[%] HF"). split; [xkeep|]. repeat split; [lk_prove | lk_prove | lk_prove | eexists; lk_prove].
Qed.

End cmp.

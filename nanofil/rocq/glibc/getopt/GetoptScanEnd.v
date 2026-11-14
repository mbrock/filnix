From Glibc Require Import GlibcProgram.
(** After it tidies the argument vector, glibc's scanner decides what the
    argument at the public index is. It may find no argument left, a
    nonoption, or an option. An argument is a nonoption when it does not
    start with a dash, or when it is the single dash. This file proves
    the decision safe: the scanner reads the argument only below the
    argument count, and its second byte only after the first byte showed
    a dash. The decision then reaches the returns that GetoptReturn.v
    proves, or the option parser. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptClamp GetoptSkipTest GetoptDash GetoptReturn.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptReturn GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The decision assigns these names. *)
Definition scan_names : list name := Eval vm_compute in
  List.map TAtom ["chk100"; "v270"; "v272"; "v294"; "v295"; "v296"; "v297"; "chk106"; "v298"; "chk107"; "v300";
    "v301"; "v306"; "v307"; "v308"; "v309"; "chk109"; "v310"; "v311"; "chk110"; "v312"; "v313";
    "v315"]%string.

(** The decision and the nonoption returns assign these names. *)
Definition scan_end_names : list name := scan_names ++ return_names.


(** The return module proves the returns that end the call early. *)
Import GetoptReturn GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic enters a block and evaluates its phi assignments. *)


(** This tactic loads an owned private integer field as a signed 32-bit value. *)


Import ProgramAbbreviations.
Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance scan_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
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

(** The scanner must read only arguments below the argument count n and
    write only the fields it owns. Here the decision starts with the
    pending nonoptions between first and last, and last at most the
    public index i, which is at most n. Each outcome keeps the caller's
    names and every resource. With no argument left, the index becomes
    first when the pending block is not empty. A nonoption in strict
    order changes nothing. A nonoption in any other order becomes the
    private option argument, with the index stepped past it. An option
    starts with a dash and has a second character, which the option
    parser reads next. *)
Lemma wp_getopt_scan_end ks e i n o f l a b r av ar ps Φ :
  avoids ks scan_end_names = true ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  0 <= f <= l -> l <= i -> i <= n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ int_cell b 40 o -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ e' fr, ⌜keeps ks e e' /\ i = n⌝ -∗
      live b r -∗ int_cell b 0 (if f =? l then i else f) -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f -∗ int_cell b 48 l -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L275") (Some fr))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ i < n /\ o = 0⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f -∗ int_cell b 48 l -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L316") (Some (TAtom "L289")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ i < n /\ o <> 0⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 (nth (Z.to_nat i) ps null) -∗ int_cell b 40 o -∗
      int_cell b 44 f -∗ int_cell b 48 l -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L318") [] (b_jump getopt_blk318))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' s, ⌜keeps ks e e' /\ i < n /\ sbyte s 0 = 45 /\ sbyte s 1 <> 0 /\
        lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i) ps null) s -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f -∗ int_cell b 48 l -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L291") (Some (TAtom "L303")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "L203") (b_insts getopt_blk203) (b_jump getopt_blk203))) : gexpr) {{ Φ }}.
Proof.
  intros Hks0 Hv0 Hv2 Hv12 Hc0 Hc1 Hc2 Hc23 Hfl Hli Hin Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi0 Hib] Hab [%Ho Hob] [%Hf Hfb] [%Hla Hlab] Ha Hc #Hs HK".
  pose proof (avoids_app _ _ _ Hks0) as [Hks Hkn].
  cbn [b_insts b_jump getopt_blk203].
  check "Hl". load_s32_using ltac:(arith) "Hl Hib". step.
  rewrite (Z.mod_small i (2 ^ 32)); [|lia]. rewrite (Z.mod_small n (2 ^ 32)); [|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec i n) as [Ein | Ein]; close_br.
  - iApply (wp_getopt_argv_end ks _ _ i f l b r with "Hl [Hib] [Hfb] [Hlab] [Hab Hob Ha Hc HK]");
      [exact Hkn | lk_prove | lk_prove | lk_prove | lk_prove | lia | lia | lia | lia | by iSplit | by iSplit | by iSplit |].
    iIntros (e' fr Hk') "Hl Hi Hf Hla". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[%] Hl Hi Hab [Hob] Hf Hla Ha Hc"); [| by iSplit].
    split; [eapply keeps_trans; [|exact Hk']; xkeep | exact Ein].
  - set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
    destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
    iDestruct (big_sepL_lookup with "Hs") as (s) "#Hws"; [exact Hq|].
    iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
    iAssert ((∀ e2 fr, ⌜keeps ks e e2 /\ lookup (TAtom "v2") e2 = Some (WPtr (mkPtr av (Obj av))) /\
        lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "chk0") e2 = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
        lookup (TAtom "chk1") e2 = Some (WPtr (mkPtr (b + 16) (Obj b))) /\
        lookup (TAtom "chk2") e2 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "chk100") e2 = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
      live b r -∗ bytes b 0 (int_bytes i) -∗ pcell b 16 a -∗ bytes b 40 (int_bytes o) -∗
      bytes b 44 (int_bytes f) -∗ bytes b 48 (int_bytes l) -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L289") (Some fr))) : gexpr) {{ Φ }}) ∧
      (∀ e' s, ⌜keeps ks e e' /\ i < n /\ sbyte s 0 = 45 /\ sbyte s 1 <> 0 /\
          lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
        word_string DfracDiscarded (nth (Z.to_nat i) ps null) s -∗
        live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ int_cell b 40 o -∗
        int_cell b 44 f -∗ int_cell b 48 l -∗ live av ar -∗ argv_cells av ps -∗
        WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L291") (Some (TAtom "L303")))) : gexpr)
          {{ Φ }}))%I
      with "[HK]" as "HL".
    { iSplit; [|iDestruct "HK" as "(_ & _ & _ & HK)"; iExact "HK"].
      iIntros (e2 fr (Hk & H2 & H12 & H0 & H1 & H2' & H100)) "Hl Hib Hab Hob Hfb Hlab Ha Hc".
      iApply (wp_getopt_nonopt ks e2 fr i n o a b r av ar ps
                with "Hl [Hib] Hab [Hob] Ha Hc Hs [HK Hfb Hlab]");
        [ exact Hkn | exact H2 | exact H12 | exact H0 | exact H1 | exact H2' | exact H100 | lia | lia
        | exact Hlen | lia | lia | lia | lia | lia | lia | lia | lia | by iSplit | by iSplit |].
      iSplit.
      - iIntros (e' (Hk' & Ho0)) "Hl Hi Hab Ho Ha Hc". iDestruct "HK" as "(_ & HK & _)".
        iApply ("HK" with "[%] Hl Hi Hab Ho [Hfb] [Hlab] Ha Hc");
          [split; [eapply keeps_trans; [exact Hk | exact Hk'] | lia] | by iSplit | by iSplit].
      - iIntros (e' (Hk' & Ho0)) "Hl Hi Hab Ho Ha Hc". iDestruct "HK" as "(_ & _ & HK & _)".
        iApply ("HK" with "[%] Hl Hi Hab Ho [Hfb] [Hlab] Ha Hc");
          [split; [eapply keeps_trans; [exact Hk | exact Hk'] | lia] | by iSplit | by iSplit]. }
    step. load_s32_using ltac:(arith) "Hl Hib". step. step. step. idx i. check "Ha".
    iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
    load_pointer_dq "Ha Hcj Hcapq" by arith.
    iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj").
    iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
    rdchr "Hws" q s 0%nat. step.
    pose proof (sbyte_range s 0 Hch) as Hs0.
    rewrite (Z.mod_small (chr_w (sbyte s 0)) (2 ^ 32)); [|apply chr_w_range].
    change (45 mod 2 ^ 32) with 45. rewrite chr_w_eqb; [|lia|lia].
    iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte s 0) 45) as [E45 | E45]; close_br.
    2:{ step. iApply wp_branch; [vx | iNext]. close_br.
        iDestruct "HL" as "[HL289 _]". iApply ("HL289" with "[%] Hl Hib Hab Hob Hfb Hlab Ha Hc"). split; [xkeep|]. repeat split; lk_prove. }
    pose proof (dash_len s E45) as Hs1.
    step. load_s32_using ltac:(arith) "Hl Hib". step. step. step. idx i. check "Ha".
    iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
    load_pointer_dq "Ha Hcj Hcapq" by arith.
    iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj").
    step. norm. iClear "Hbl Hbt". clear Hcap Hb0' Hbq Hbe Hbr.
    iDestruct (ws_byte q s 1 with "Hws") as (bb1 breg1) "(%Hbb1 & #Hbl & #Hbt)"; [lia|].
    destruct Hbb1 as (Hcap & Hb0' & Hbq & Hbe & Hbr).
    assert (Hlen1 : 1 <= Z.of_nat (List.length s)) by lia.
    iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
      [reflexivity | vx | exact Hcap | arith | cbn [ptr_addr]; unfold raw_address; rewrite Z.mod_small; lia | arith |].
    iNext; iIntros "_".
    load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by arith.
    iNext; iIntros "_ _". step. step. step.
    pose proof (sbyte_range s 1 Hch) as Hs1'. rewrite chr_cmp; [|lia|lia].
    iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte s 1) 0) as [E0 | E0]; close_br.
    + iDestruct "HL" as "[HL289 _]". iApply ("HL289" with "[%] Hl Hib Hab Hob Hfb Hlab Ha Hc"). split; [xkeep|]. repeat split; lk_prove.
    + iDestruct "HL" as "[_ HK]". unfold j in Hq. rewrite (nth_lookup_Some _ _ _ _ Hq).
      iApply ("HK" with "[%] Hws Hl [Hib] Hab [Hob] [Hfb] [Hlab] Ha Hc");
        [ split; [xkeep|]; split; [lia|]; split; [exact E45|]; split; [exact E0 | lk_prove]
        | by iSplit | by iSplit | by iSplit | by iSplit].
Qed.

End scan.

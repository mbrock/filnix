From Glibc Require Import GlibcProgram.
(** Some arguments end one call of glibc's scanner before it parses an
    option. When no argument is left, the scanner points the public
    index at the first pending nonoption and returns -1. A nonoption at
    the index makes it return -1 in strict order. In any other order it
    returns 1, makes the argument the private option argument, and steps
    the index past it. This file proves these returns safe: the scanner
    reads an argument pointer only below the argument count, and it
    writes only the fields of its own state. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptClamp.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The returns assign these names. *)
Definition return_names : list name := Eval vm_compute in
  List.map TAtom ["v277"; "chk101"; "v278"; "v280"; "chk102"; "v281"; "v282"; "v285"; "v286"; "chk104";
    "v320"; "chk111"; "v321"; "v322"; "v326"; "v329"; "v330"; "chk113"; "v331"; "v332";
    "v333"; "chk114"; "v334"; "chk115"]%string.

(** The nonoption return of 1 ends in this block. *)
Definition getopt_blk318 : block := Eval vm_compute in x_blk "L318".


(** The exchange module supplies the argument vector and its tactics. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic enters a block and evaluates its phi assignments. *)


(** This tactic loads an owned private integer field as a signed 32-bit value. *)


Import ProgramAbbreviations.
Section returns.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance return_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** No argument is left when the public index i equals the argument
    count. The pending nonoptions lie between first and last. When that
    block is not empty, the index becomes first, so that the caller sees
    the nonoptions after the options. *)
Lemma wp_getopt_argv_end ks e fr i f l b r Φ :
  avoids ks return_names = true ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk23") e = Some (WPtr (mkPtr (b + 48) (Obj b))) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  (∀ e' fr', ⌜keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 (if f =? l then i else f) -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L275") (Some fr'))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L266") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks H12 H0 H2 H23 Hb Hal Hend Hr.
  iIntros "Hl [%Hi0 Hib] [%Hf Hfb] [%Hla Hlab] HK".
  step. step. norm. check "Hl". load_s32_using ltac:(arith) "Hl Hfb". step. norm. check "Hl". load_s32_using ltac:(arith) "Hl Hlab". step.
  rewrite (Z.mod_small f (2 ^ 32)); [|lia]. rewrite (Z.mod_small l (2 ^ 32)); [|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec f l) as [Efl | Efl]; close_br.
  - iApply ("HK" with "[%] Hl [Hib] [Hfb] [Hlab]"); [xkeep | by iSplit | by iSplit | by iSplit].
  - step. step. norm. load_s32_using ltac:(arith) "Hl Hfb". check "Hl".
    store_word "Hl Hib" by (arith) preserving wi_store.
    iNext. iIntros "Hl Hib". step.
    iApply ("HK" with "[%] Hl [Hib] [Hfb] [Hlab]"); [xkeep | | by iSplit | by iSplit].
    iSplit; [iPureIntro; lia|]. rewrite (Z.mod_small f (2 ^ 32)); [|lia]. iAssumption.
Qed.

(** The argument at the public index i, below the argument count n, is
    a nonoption. The ordering field o decides the return. In strict
    order, which is o = 0, nothing changes. Otherwise the private option
    argument becomes argument i and the index becomes i + 1. Both keep
    the caller's names and the argument vector. *)
Lemma wp_getopt_nonopt ks e fr i n o a b r av ar ps Φ :
  avoids ks return_names = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk100") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ int_cell b 40 o -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ e', ⌜keeps ks e e' /\ o = 0⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ int_cell b 40 o -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L316") (Some (TAtom "L289")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ o <> 0⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 (nth (Z.to_nat i) ps null) -∗ int_cell b 40 o -∗
      live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L318") [] (b_jump getopt_blk318))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L289") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks H2 H12 H0 H1 H2' H100 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi0 Hib] Hab [%Ho Hob] Ha Hc #Hs HK".
  set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  iDestruct (big_sepL_lookup with "Hs") as (s) "#Hws"; [exact Hq|].
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  step. step. norm. check "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hob");
    [reflexivity | vx | reflexivity | apply load_uw_int; assumption | left; reflexivity | arith |].
  iNext. iIntros "Hl Hob". step. rewrite (Z.mod_small o (2 ^ 32)); [|lia]. change (0 mod 2 ^ 32) with 0.
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec o 0) as [Eo | Eo]; close_br.
  - iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[%] Hl [Hib] Hab [Hob] Ha Hc"); [split; [xkeep | lia] | by iSplit | by iSplit].
  - step. step. norm. load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
    store_word "Hl Hib" by (arith) preserving wi_store.
    iNext. iIntros "Hl Hib". step. step. step. idx i. check "Ha".
    iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
    load_pointer_dq "Ha Hcj Hcapq" by arith.
    iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). check "Hl".
    store_pointer "Hl Hab" by (arith) preserving wi_store.
    iNext. iIntros "Hl Hab". iDestruct "HK" as "[_ HK]".
    iApply ("HK" with "[%] Hl [Hib] [Hab] [Hob] Ha Hc");
      [ split; [xkeep | lia] | iSplit; [iPureIntro; lia | iAssumption]
      | unfold j in Hq; by rewrite (nth_lookup_Some _ _ _ _ Hq) | by iSplit].
Qed.

End returns.

(** When no short-option cluster is pending, glibc's scanner first clamps
    its two nonoption endpoints to the public index i. In permuting mode
    it then either exchanges the skipped nonoptions with the options that
    followed them, or restarts the nonoption block at i. This file proves
    those blocks safe and tracks the endpoints they leave. *)

From Glibc Require Import OsMemLogic GetoptTactics GlibcProgram GlibcTactics OsTactics GlibcEnv GlibcSym.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic FrameNotation.
From Glibc Require Import OsWorld WordString GetoptModule
    GetoptArgv GetoptExchange
  GetoptIdle GetoptPermute GetoptNames GetoptLayout CStruct.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** An unsigned 32-bit load of an int's bytes, at class [W], is its bits. *)
Lemma load_uw_int x : 0 <= x < 2 ^ 32 -> extended Uw W (of_bytes (le_bytes x 4)) = Some (WInt x).
Proof. intros Hx. rewrite of_bytes_int; [|exact Hx]. cbn. by rewrite !(Z.mod_small x (2 ^ 32)). Qed.

Import GetoptPermute GetoptIdle GetoptExchange Fix.ML0 Fix.LG0 Fix.LG0.L GetoptArgv.

Import ProgramAbbreviations.
Import GetoptNames.fn__getopt_internal_r Fix.LG0.L.RunNotation.

(** Both indices fit in a signed C int, so the compiled greater-than
    comparison agrees with the comparison of their mathematical values. *)
Local Lemma index_gt x y : 0 <= x < 2^31 -> 0 <= y < 2^31 ->
  cond_bit Sgt W x y = Some (if y <? x then 1 else 0).
Proof.
  intros Hx Hy. cbn [cond_bit signed modulus half_modulus].
  by rewrite (sx_nonneg x Hx) (sx_nonneg y Hy).
Qed.

(** A call lends the scanner its public index, ordering mode, and two
    nonoption endpoints. The layout of the captured C structure locates
    each field and supplies its width. *)
Definition clamp_fields `{!gen_heapGS piece pval Σ} b i ordering first last : iProp Σ :=
  struct_at GetoptLayout.fields "struct _getopt_data" b
    [("optind", VInt i); ("__ordering", VInt ordering);
     ("__first_nonopt", VInt first); ("__last_nonopt", VInt last)].

#[global] Hint Unfold clamp_fields : structs.

(** The scanner carries argv and its private state into the clamp. Earlier
    checks also leave pointers to the state and its opterr field. *)
Definition clamp_inputs (e : env) av b :=
  e.[‹argv›] = Some (WPtr (mkPtr av (Obj av))) /\
  e.[‹d›] = Some (WPtr (mkPtr b (Obj b))) /\
  e.[‹chk(d+4)›] = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
  e.[‹chk(d)›] = Some (WPtr (mkPtr b (Obj b))).

(** Comparing the last nonoption with optind checks both field addresses.
    The ordering test and the skip loop reuse those checked pointers. *)
Definition clamp_checks (e : env) b :=
  e.[‹chk(d+48)@L73›] = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
  e.[‹chk(d)@L73›] = Some (WPtr (mkPtr b (Obj b))).

Local Abbreviation skip_nonoptions :=
  (Exec (b_label getopt_blk159) (b_insts getopt_blk159) (b_jump getopt_blk159)).
Local Abbreviation test_double_dash :=
  (Exec (b_label getopt_blk119) (b_insts getopt_blk119) (b_jump getopt_blk119)).

Section clamp.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Existing Instance program_irisGS.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance clamp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.

(** When a caller rewinds optind, the scanner lowers the saved last
    nonoption to that index. Both branches reach the next comparison
    with the smaller of the two values in the field. *)
Local Lemma wp_clamp_last ks e from av b r i last Φ :
  avoids ks clamp_names = true -> clamp_inputs e av b ->
  0 <= i < 2^31 -> 0 <= last < 2^31 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2^48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 48 last -∗
  (∀ e' pred, ⌜keeps ks e e' /\ clamp_inputs e' av b /\ clamp_checks e' b⌝ -∗
    live b r -∗ int_cell b 0 i -∗ int_cell b 48 (Z.min last i) -∗
    WP run{ glibc_getopt_internal_r env: e' | enter: @"L93" from: pred } {{ Φ }}) -∗
  WP run{ glibc_getopt_internal_r env: e | enter: @"L73" from: from } {{ Φ }}.
Proof using Type.
  intros Havoid (Hargv & Hdata & Hopterr & Hindex) Hi Hlast Hb Hal Hfit Hr.
  iIntros "Hl [%Hi32 Hib] [%Hlast32 Hlab] Hclamped".
  step. sym_run "Hl Hlab Hib".
  rewrite (index_gt last i ltac:(lia) ltac:(lia)).
  destruct (Z.ltb_spec i last) as [Hgt | Hle]; close_br.
  - rewrite Z.min_r; last lia. step. sym_run "Hl Hib Hlab".
    store_word "Hl Hlab" by (arith) preserving wi_store.
    iNext. iIntros "Hl Hlab". step.
    iApply ("Hclamped" $! _ with "[%] Hl [Hib] [Hlab]"); [| icell | (iApply cell_mod; [lia | iAssumption])].
    split; [xkeep|]. repeat split; lk_prove.
  - rewrite Z.min_l; last lia. iApply ("Hclamped" $! _ with "[%] Hl [Hib] [Hlab]"); [| icell | icell].
    split; [xkeep|]. repeat split; lk_prove.
Qed.

(** A caller may rewind the public index between calls, so the scanner
    first lowers both endpoints to it. The session supplies endpoints with
    0 <= first <= last <= n and first <= i. In permuting mode, ordering 1,
    the scanner then reaches the skip loop with first between 0 and i. In
    the other modes it reaches the "--" test with first <= last <= i and
    leaves the argument vector untouched. *)
Lemma wp_getopt_clamp ks e fr0 n i o f l b r av ar ps Φ :
  avoids ks (x2_outer ++ x2_edges) = true -> avoids ks clamp_names = true ->
  clamp_inputs e av b ->
  0 <= f <= l -> l <= n -> f <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ clamp_fields b i o f l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ e' ps' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ o = 1 /\ 0 <= f' <= i /\
       clamp_checks e' b⌝ -∗
     live b r -∗ clamp_fields b i o f' l' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP run{ glibc_getopt_internal_r env: e' | pc: skip_nonoptions } {{ Φ }}) ∧
   (∀ e' l', ⌜keeps ks e e' /\ o <> 1 /\ f <= l' <= i /\
       clamp_checks e' b⌝ -∗
     live b r -∗ clamp_fields b i o f l' -∗
     live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
     WP run{ glibc_getopt_internal_r env: e' | pc: test_double_dash } {{ Φ }})) -∗
  WP run{ glibc_getopt_internal_r env: e | enter: @"L73" from: fr0 } {{ Φ }}.
Proof using Type.
  intros Hkx Hkc Hinputs Hfl Hln Hfi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl Hfields Ha Hc #Hs HK".
  struct_open "Hfields" as "(Hindex & [%Ho Hob] & [%Hf Hfb] & Hlast & _)".
  iApply (wp_clamp_last ks e fr0 av b r i l with "Hl Hindex Hlast [-]");
    try (first [exact Hkc | exact Hinputs | lia]).
  iIntros (e2 pred (Hk & (Hargv & Hdata & Hopterr & Hindex) & Hlast & Hchecked))
    "Hl [%Hi Hib] [%Hla Hlab]".
  step. sym_run "Hl Hfb Hib".
  rewrite (index_gt f i ltac:(lia) ltac:(lia)).
  rewrite (proj2 (Z.ltb_ge i f) Hfi). close_br. step.
  sym_run "Hl Hob".
  cbn [cond_bit].
  destruct (Z.eqb_spec o 1) as [-> | Ho1]; close_br.
  2:{ step. iDestruct "HK" as "[_ HK]".
      iApply ("HK" $! _ (Z.min l i) with "[%] Hl [Hib Hob Hfb Hlab] Ha Hc Hs"); last first.
      { struct_close; repeat (iSplit; [icell|]); done. }
      split; [xkeep|]. split; [done|]. split; [lia|]. split; lk_prove. }
  iDestruct "HK" as "[HK _]".
  iApply (GetoptPermute.wp_getopt_permute ks _ _ f (Z.min l i) i b r av ar n ps
    with "Hl [Hib] [Hob] [Hfb] [Hlab] Ha Hc Hs [HK]");
    try solve [assumption | lk_prove | lia | icell].
  iIntros (e' ps' f' l' (Hp & Hk' & Hf' & H23' & H24')) "Hl Hib Hob Hfb Hlab Ha Hc Hs'".
  iApply ("HK" with "[%] Hl [Hib Hob Hfb Hlab] Ha Hc Hs'"); [|struct_close].
  split; [done|]. split; [eapply keeps_trans; [|exact Hk']; xkeep|]. split; [done|]. split; [lia|]. split; assumption.
Qed.

End clamp.

(** Calling `c: strlen` on a shared, borrowed, or read-only string
    requires a [[weakest-precondition]] specification that preserves any
    fractional or persistent ownership share. This module proves
    [wp_glibc_strlen_ws] for a call [[frame]] of glibc's `__strlen` over
    a [word_string], and [wp_call_glibc_strlen] for any caller invoking
    it through a module's global function table.

    A caller may borrow a string, share it read-only, or hold a
    persistent copy, so every memory read must work at any ownership
    fraction. This proof adapts the full-ownership argument from
    [StrlenLogic] to use fractional read rules. It verifies the entry
    block in [wp_glibc_strlen_dq] and hands off the remaining words to
    [StrlenLoop]'s [loop_spec_dq]. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop.
From Glibc Require StrlenLoop WordString.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.


Module LG := LG0.
Module L := LG.L.
Import L LG WordString.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** To step through IR instructions in [[separation-logic|separation logic]],
    [rules_irisGS] connects the contract registry and world invariant `wi`
    to the Iris program logic. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** This shorthand names the expression type of the instantiated
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Tactic [st] advances the symbolic execution by one pure `let`,
    `flight`, block entry, or `goto` step whose premises reduce by
    computation. *)


(** Given fractional ownership of an 8-aligned object b and the words ws
    starting from the word that contains byte p, `__strlen` locates the
    first zero byte n bytes past p, returns n, and hands back the live
    [[region]] and word pieces. *)
Lemma wp_glibc_strlen_dq dq p b reg ws n Φ :
  (ptr_cap p = Obj b \/ ptr_cap p = Ro b) -> 0 < b -> b mod 8 = 0 -> b <= ptr_addr p ->
  ptr_addr p - ptr_addr p mod 8 + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws ->
  first_zero (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) n ->
  liveq dq b reg -∗ ptsq dq (words_ps b (ptr_addr p - ptr_addr p mod 8 - b) ws) -∗
  (liveq dq b reg -∗ ptsq dq (words_ps b (ptr_addr p - ptr_addr p mod 8 - b) ws) -∗ Φ (Ret (WInt (Z.of_nat n)))) -∗
  WP (ERun (mkFrame glibc_strlen [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)) : gexpr)
    {{ Φ }}.
Proof.
  destruct p as [a c]. cbn [ptr_addr ptr_cap]. intros Hc Hb0 Hb8 Hba Hend Hreg Hr Hz.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hk.
  assert (Hal : b <= a - a mod 8) by (pose proof (Z.div_mod a 8 ltac:(lia)); pose proof (Z.div_mod b 8 ltac:(lia)); nia).
  destruct ws as [|w ws].
  { destruct Hz as [Hz _]. rewrite drop_nil in Hz. discriminate. }
  cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  apply Forall_cons_1 in Hr as [Hw0 Hr].
  iIntros "Hl Hps HK". cbn [words_ps]. rewrite ptsq_app. iDestruct "Hps" as "[Hw Hps]".
  do 5 step.
  match goal with |- context [put (TAtom "v10") (WPtr (mkPtr ?X _)) _] =>
    replace X with (a - a mod 8) by
      (cbn [ptr_addr]; rewrite (Z.mod_small a (2 ^ 64)); [rewrite land_align; [arith | lia] | lia]) end.
  iApply (wp_check_read_dq with "Hl"); [reflexivity | reflexivity | exact Hc | arith | arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_read_dq with "Hl Hw"); [reflexivity | reflexivity | exact Hc | arith |].
  iNext. iIntros "Hl Hw". rewrite (Z.mod_small w (2 ^ 64) Hw0).
  do 8 step. set_int "iw_2.v12" (first_shift w a).
  step. iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (first_shift w a) (2 ^ 64) (first_shift_range w a)) Zmod_0_l.
  assert (Hfs : forall i, 0 <= i -> byte_of (first_shift w a) i =
            if i + a mod 8 <? 8 then (if byte_of w (i + a mod 8) =? 0 then 128 else 0) else 0)
    by (intros i Hi; apply first_shift_byte; lia).
  assert (Hk8 : (Z.to_nat (a mod 8) < 8)%nat) by (change 8%nat with (Z.to_nat 8); apply Z2Nat.inj_lt; lia).
  destruct (Nat.lt_ge_cases (Z.to_nat (a mod 8) + n) 8) as [Hn|Hn].
  - (* The NUL is in the first word. *)
    destruct (first_zero_in w ws _ n Hk8 Hz Hn) as [Hzn Hnz].
    rewrite Nat2Z.inj_add Z2Nat.id in Hzn; [|lia].
    assert (Hat : byte_of (first_shift w a) (Z.of_nat n) = 128).
    { rewrite Hfs; [|lia]. replace (Z.of_nat n + a mod 8 <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite (Z.add_comm (Z.of_nat n)) Hzn. reflexivity. }
    assert (Hlow : forall i, 0 <= i < Z.of_nat n -> byte_of (first_shift w a) i = 0).
    { intros i Hi. rewrite Hfs; [|lia]. replace (i + a mod 8 <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      specialize (Hnz (Z.to_nat (i + a mod 8)) ltac:(lia)). rewrite Z2Nat.id in Hnz; [|lia].
      apply Z.eqb_neq in Hnz. rewrite Hnz. reflexivity. }
    assert (H01 : forall i, 0 <= i < 8 -> byte_of (first_shift w a) i = 0 \/ byte_of (first_shift w a) i = 128).
    { intros i Hi. rewrite Hfs; [|lia]. destruct (_ <? 8); [destruct (_ =? 0)|]; auto. }
    assert (Hnz0 : (first_shift w a =? 0) = false).
    { apply Z.eqb_neq. intros E. rewrite E in Hat. unfold byte_of in Hat. rewrite Z.div_0_l in Hat; [discriminate|].
      apply Z.pow_nonzero; lia. }
    rewrite Hnz0. close_if.
    step. step. iApply wp_branch; [reflexivity|]. iNext.
    rewrite (Z.mod_small (first_shift w a) (2 ^ 64) (first_shift_range w a)) Zmod_0_l Hnz0. close_if.
    do 16 (step; gen_top).
    set_tail "iw_3.iw_1.iw_1.v22" (first_shift w a).
    rewrite (tail_first (first_shift w a) (Z.of_nat n) (first_shift_range w a) H01 ltac:(lia) Hat Hlow).
    step. step. set_int "iw_3.iw_1.iw_1.v23" (8 * Z.of_nat n + 7).
    step. set_int "iw_3.iw_1.v27" (Z.of_nat n).
    step. set_int "v26" (Z.of_nat n).
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) => replace X with (Z.of_nat n) by arith end.
    iApply ("HK" with "Hl [$Hw $Hps]").
  - (* The NUL is in a later word: the loop. *)
    destruct (first_zero_past w ws _ n Hk8 Hz Hn) as [Hnz Hz'].
    assert (H0 : first_shift w a = 0).
    { apply zero_word; [apply first_shift_range|]. intros i Hi. rewrite Hfs; [|lia].
      destruct (i + a mod 8 <? 8) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
      specialize (Hnz (Z.to_nat (i + a mod 8)) ltac:(lia)). rewrite Z2Nat.id in Hnz; [|lia].
      apply Z.eqb_neq in Hnz. rewrite Hnz. reflexivity. }
    rewrite H0. close_if.
    iApply (StrlenLoop.loop_spec_dq registry wi ge dq b reg c a ws (a - a mod 8 - b + 8) _ (Some (TAtom "start"))
              (Z.to_nat (a mod 8) + n - 8)%nat (mkPtr (a - a mod 8) c) with "Hl Hps [Hw HK]").
    + exact Hc.
    + lia.
    + lia.
    + replace (b + (a - a mod 8 - b + 8)) with (8 * (a / 8 + 1)) by (pose proof (Z.div_mod a 8); lia).
      rewrite Z.mul_comm Z_mod_mult. reflexivity.
    + lia.
    + lia.
    + exact Hreg.
    + exact Hr.
    + exact Hz'.
    + cbn. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + iIntros "Hl Hps".
      replace (b + (a - a mod 8 - b + 8) + Z.of_nat (Z.to_nat (a mod 8) + n - 8) - a) with (Z.of_nat n) by lia.
      iApply ("HK" with "Hl [$Hw $Hps]").
Qed.

(** Executing a frame of [glibc_strlen] on a [word_string] at any share
    returns the string's length and restores the [word_string]
    resource. *)
Lemma wp_glibc_strlen_ws dq p s Φ :
  word_string dq p s -∗ (word_string dq p s -∗ Φ (Ret (WInt (Z.of_nat (List.length s))))) -∗
  WP (ERun (mkFrame glibc_strlen [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)) : gexpr)
    {{ Φ }}.
Proof.
  iIntros "(%b & %reg & %ws & %Hs & Hl & Hw) HK".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp _ Hr _ _].
  iApply (wp_glibc_strlen_dq dq p b reg ws (List.length s) with "Hl Hw");
    [exact Hc | exact Hb0 | exact Hb8 | exact Hst | exact Hf | exact Hsp | exact Hr
    | exact (str_shape_first_zero _ _ _ _ _ Hs) |].
  iIntros "Hl Hw". iApply "HK". iExists b, reg, ws. by iFrame.
Qed.

(** Calling a global function g bound to [glibc_strlen] on a
    [word_string] at any share resumes the caller with the string's
    length and restores the [word_string]. *)
Lemma wp_call_glibc_strlen f e ls l r g args rest j dq p s cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p] -> find_fn ge g = Some (Defined glibc_strlen) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WInt (Z.of_nat (List.length s)))) = Some cf' ->
  word_string dq p s -∗ ▷ (word_string dq p s -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hg Hr. iIntros "Hs HK".
  iApply (wp_call_bind with "[Hs HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_strlen_ws with "Hs"). iIntros "Hs". iExists cf'. iSplit; [done|]. iNext.
  iApply ("HK" with "Hs").
Qed.

End rules.

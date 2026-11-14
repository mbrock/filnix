(** Glibc's `__memchr` implements `c: memchr(p, c, n)` by returning null
    immediately when `n` is zero and otherwise computing a saturated end
    address `memchr_end` so pointer arithmetic cannot wrap past the top
    of memory. It then loads the 8-byte [[word]] containing `p`, shifts
    away any bytes before `p`, and delegates to [MemchrFirst] and
    [MemchrLoop].

    This module proves [wp_glibc_memchr_dq] for a call [[frame]] of
    `__memchr` at any ownership share of the object it reads. Because
    the specification works for fractional and persistent shares alike,
    higher-level proofs such as [StrnlenLogic] can invoke `__memchr` on
    borrowed or shared strings. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrchrCode MemchrLast MemchrLoop
  MemchrFirst.
From Glibc Require MemchrFirst MemchrLast MemchrLoop WordString.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** Function [memchr_end] computes the inclusive end address of a
    search of n bytes from address a, saturating at `2 ^ 64 - 1`. *)
Definition memchr_end (a n : Z) : Z := Z.min (a + n - 1) (2 ^ 64 - 1).

(** Multiplying the zero-extended low byte of c by `0x0101010101010101`
    produces `[rep] c` in the IR. *)
Lemma rep_ext c : 0 <= c < 2 ^ 32 ->
  ((extension Uw ((extension Ub (c mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64) mod 2 ^ 64
   * (72340172838076673 mod 2 ^ 64)) mod 2 ^ 64 = rep c.
Proof.
  intros Hc. cbn [extension]. rewrite (Z.mod_small c (2 ^ 32) Hc). unfold rep, lows.
  pose proof (Z.mod_pos_bound c 256 ltac:(lia)).
  rewrite !(Z.mod_small (c mod 256) (2 ^ 32)); [|lia|lia|lia].
  rewrite (Z.mod_small (c mod 256) (2 ^ 64)); [|lia]. rewrite (Z.mod_small (c mod 256) (2 ^ 64)); [reflexivity|lia].
Qed.


Module LG := LG0.
Module L := LG.L.
Import L LG WordString MemchrLast MemchrLoop MemchrFirst.

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

(** To step past pure instructions without manual boilerplate, [st]
    advances one pure `let`, [[flight]], block entry, or `goto` step
    whose premises reduce. *)


(** Block `iw_2.L6` receives the saturated end address E, aligns it to an
    8-byte boundary, and tests the first word starting at byte offset k. *)
Definition memchr_blk_end : block := Eval vm_compute in
  match find_block (TAtom "iw_2.L6") (fn_blocks glibc_memchr) with
  | Some b => b | None => mkBlock (TAtom "iw_2.L6") [] [] JUnreachable end.


(** Entering `iw_2.L6` with end address E in `iw_2.v14`, [memchr_first]
    computes the match mask for the first word w, shifts past its k
    leading bytes, and branches to [memchr_hit] or [memchr_next]. *)
Lemma memchr_first dq b reg w ws a c0 (k : nat) e from c E r Φ :
  (c0 = Obj b \/ c0 = Ro b) -> 0 < b -> b mod 8 = 0 -> b <= a - Z.of_nat k -> a mod 8 = Z.of_nat k ->
  a - Z.of_nat k + 8 * Z.of_nat (List.length (w :: ws)) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) (w :: ws) -> a <= E < 2 ^ 64 ->
  phis_env ge (b_phis memchr_blk_end) from e = Some (put (TAtom "iw_2.v14") (WInt E) e) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr a c0)) -> lookup (TAtom "v16") e = Some (WInt a) ->
  lookup (TAtom "v25") e = Some (WInt w) -> lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)) ->
  lookup (TAtom "v19") e = Some (WPtr (mkPtr (a - Z.of_nat k) c0)) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (a - Z.of_nat k) c0)) ->
  loop_hit (drop k (wbytes (w :: ws))) (c mod 256) a E r ->
  liveq dq b reg -∗ ptsq dq (words_ps b (a - Z.of_nat k - b) (w :: ws)) -∗
  (liveq dq b reg -∗ ptsq dq (words_ps b (a - Z.of_nat k - b) (w :: ws)) -∗ Φ (Ret (WPtr (hit_ptr (mkPtr a c0) r)))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "iw_2.L6") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hb0 Hb8 Hba Hk Hend Hreg Hr HE Hphi H0 H16 H25 H7 H19 Hchk Hhit. iIntros "Hl Hps HK".
  apply Forall_cons_1 in Hr as [Hw0 Hr]. cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  pose proof (Nat2Z.is_nonneg (List.length ws)) as Hws.
  pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as HE8.
  iApply wp_enter; [reflexivity | exact Hphi |]. iNext. cbn [b_insts b_jump memchr_blk_end].
  do 5 step. cbn [ptr_addr ptr_cap]. sp "iw_3.v12" E. si "v40" E.
  step. rewrite (Z.mod_small E (2 ^ 64)); [|zl]. rewrite land_align; [|zl].
  step. step. sp "v43" (E - E mod 8).
  do 6 step. rewrite !(Z.mod_small w (2 ^ 64) Hw0) rep_mod.
  si "iw_4.iw_1.v13" (first_mask (Z.lxor w (rep c))).
  do 3 step. si "iw_5.v12" (first_shift (Z.lxor w (rep c)) a).
  step. iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (first_shift _ _) (2 ^ 64) (first_shift_range _ _)) Zmod_0_l.
  set (m := first_shift (Z.lxor w (rep c)) a).
  assert (Hm : forall i, 0 <= i -> byte_of m i =
            if i + Z.of_nat k <? 8 then (if byte_of w (i + Z.of_nat k) =? c mod 256 then 128 else 0) else 0).
  { intros i Hi. unfold m. rewrite first_hit_byte; [rewrite Hk; reflexivity | lia | exact Hi]. }
  assert (Hk8 : (k < 8)%nat) by (pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia).
  destruct (hit_first w ws (c mod 256) k a E r Hk8 ltac:(lia) Hhit)
    as [(j & Hj0 & Hj8 & Hcj & Hlj & ->) | (Hn & Hlast & Hnext)].
  - (* A match in the first word. *)
    assert (Hb : byte_of m j = 128).
    { rewrite Hm; [|lia]. replace (j + Z.of_nat k <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Hcj Z.eqb_refl. reflexivity. }
    assert (Hlow : forall i, 0 <= i < j -> byte_of m i = 0).
    { intros i Hi. rewrite Hm; [|lia]. replace (i + Z.of_nat k <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (Z.eqb_spec (byte_of w (i + Z.of_nat k)) (c mod 256)) as [E'|E']; [|reflexivity].
      exfalso. exact (Hlj i Hi E'). }
    assert (H01 : forall i, 0 <= i < 8 -> byte_of m i = 0 \/ byte_of m i = 128).
    { intros i Hi. rewrite Hm; [|lia]. destruct (_ <? 8); [destruct (_ =? _)|]; auto. }
    assert (Hm0 : (m =? 0) = false).
    { apply Z.eqb_neq. intros E'. rewrite E' in Hb. unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate|].
      apply Z.pow_nonzero; lia. }
    rewrite Hm0. close_if.
    iApply (memchr_hit _ _ _ _ _ m j a c0 E with "[Hl Hps HK]").
    + apply first_shift_range.
    + exact H01.
    + lia.
    + exact Hb.
    + exact Hlow.
    + lia.
    + lia.
    + lk H7.
    + lk H0.
    + lk H7.
    + iApply ("HK" with "Hl Hps").
  - (* No match in the first word. *)
    assert (Hm0 : m = 0).
    { apply zero_word; [apply first_shift_range|]. intros i Hi. rewrite Hm; [|lia].
      destruct (Z.ltb_spec (i + Z.of_nat k) 8); [|reflexivity].
      destruct (Z.eqb_spec (byte_of w (i + Z.of_nat k)) (c mod 256)) as [E'|E']; [|reflexivity].
      exfalso. exact (Hn (i + Z.of_nat k) ltac:(lia) E'). }
    rewrite Hm0. close_if.
    assert (Hal : (a - Z.of_nat k) mod 8 = 0).
    { rewrite <- Hk. rewrite Zminus_mod Z.mod_mod; [|lia]. rewrite Z.sub_diag. reflexivity. }
    iApply (memchr_next _ _ _ dq b reg w ws (a - Z.of_nat k) c0 _ _ _ c E (option_map (fun t => t - (8 - k))%nat r)
              with "Hl Hps [HK]").
    + exact Hc.
    + exact Hb0.
    + exact Hba.
    + exact Hal.
    + cbn [List.length]. lia.
    + exact Hreg.
    + exact Hr.
    + lia.
    + lk H19.
    + lk Hchk.
    + lk H7.
    + lk H7.
    + lk H7.
    + intros HL. rewrite Hlast; [reflexivity | lia].
    + intros HL. destruct (Hnext HL) as (? & _ & ?). split; assumption.
    + iIntros "Hl Hps".
      replace (hit_ptr (mkPtr (a - Z.of_nat k + 8) c0) (option_map (fun t => t - (8 - k))%nat r))
        with (hit_ptr (mkPtr a c0) r); [iApply ("HK" with "Hl Hps")|].
      destruct r as [t|]; [|reflexivity].
      destruct (Z_lt_le_dec E (a - Z.of_nat k + 8)) as [HL|HL]; [discriminate (Hlast HL)|].
      destruct (Hnext HL) as (_ & H8 & _). specialize (H8 t eq_refl). cbn [hit_ptr option_map ptr_addr ptr_cap].
      rewrite Nat2Z.inj_sub; [|exact H8]. f_equal. lia.
Qed.


(** To verify `c: memchr` at any ownership share, [wp_glibc_memchr_dq]
    steps through [glibc_memchr] on n bytes starting at p. It returns
    the earliest matching pointer or null, and restores the live
    [[region]] and word pieces. *)
Lemma wp_glibc_memchr_dq dq p c n b reg ws r e Φ :
  (ptr_cap p = Obj b \/ ptr_cap p = Ro b) -> 0 < b -> b mod 8 = 0 -> b <= ptr_addr p ->
  wstart p + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws -> 0 <= c < 2 ^ 32 -> 0 <= n < 2 ^ 64 ->
  loop_hit (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) (c mod 256) (ptr_addr p)
    (memchr_end (ptr_addr p) n) r ->
  lookup (TAtom "v0") e = Some (WPtr p) -> lookup (TAtom "v2") e = Some (WInt c) ->
  lookup (TAtom "v4") e = Some (WInt n) ->
  liveq dq b reg -∗ ptsq dq (words_ps b (wstart p - b) ws) -∗
  (liveq dq b reg -∗ ptsq dq (words_ps b (wstart p - b) ws) -∗ Φ (Ret (WPtr (hit_ptr p r)))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct p as [a c0]. unfold wstart. cbn [ptr_addr ptr_cap]. intros Hc Hb0 Hb8 Hba Hend Hreg Hr Hcr Hn Hhit H0 H2 H4.
  iIntros "Hl Hps HK".
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hk.
  assert (Hal : b <= a - a mod 8) by (pose proof (Z.div_mod a 8 ltac:(lia)); pose proof (Z.div_mod b 8 ltac:(lia)); nia).
  step. step. iApply wp_branch; [reflexivity|]. iNext. rewrite (Z.mod_small n (2 ^ 64) Hn).
  destruct (Z.eqb_spec n 0) as [->|Hn0].
  { (* No bytes: null. *)
    close_if. step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    destruct r as [t|]; [|iApply ("HK" with "Hl Hps")].
    exfalso. destruct Hhit as [Ht _]. unfold memchr_end in Ht. lia. }
  rewrite (proj2 (Z.eqb_neq _ _) Hn0). close_if.
  assert (HE : a <= memchr_end a n < 2 ^ 64) by (unfold memchr_end; lia).
  destruct ws as [|w ws].
  { exfalso. rewrite drop_nil in Hhit. destruct r as [t|]; cbn in Hhit; [|lia].
    destruct Hhit as [_ [Ht _]]. rewrite lookup_nil in Ht. discriminate. }
  cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  apply Forall_cons_1 in Hr as [Hw0 Hr'].
  cbn [words_ps]. rewrite ptsq_app. iDestruct "Hps" as "[Hw Hps]".
  do 5 step. cbn [ptr_addr ptr_cap]. rewrite (Z.mod_small a (2 ^ 64)); [|zl]. rewrite land_align; [|zl].
  sp "v19" (a - a mod 8).
  iApply (wp_check_read_dq with "Hl"); [reflexivity | vx | exact Hc | ar | ar | apply Z.mod_1_r |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_read_dq with "Hl Hw"); [reflexivity | reflexivity | exact Hc | ar |].
  iNext. iIntros "Hl Hw". rewrite (Z.mod_small w (2 ^ 64) Hw0).
  do 6 step. rewrite (rep_ext c Hcr). si "v34" (n - 1). si "iw_2.v9" (2 ^ 64 - 1 - a).
  iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (2 ^ 64 - 1 - a) (2 ^ 64)); [|zl]. rewrite (Z.mod_small (n - 1) (2 ^ 64)); [|zl].
  set (k := Z.to_nat (a mod 8)) in Hhit.
  assert (Hk8 : a mod 8 = Z.of_nat k) by (unfold k; rewrite Z2Nat.id; lia).
  rewrite Hk8. rewrite Hk8 in Hal.
  destruct (Z.ltb_spec (2 ^ 64 - 1 - a) (n - 1)) as [Hs|Hs].
  - (* The end saturates. *)
    change ((if true then 1 else 0) mod 2 ^ 32 =? 0) with false. cbn [edge_label].
    replace (memchr_end a n) with 18446744073709551615 in Hhit by (unfold memchr_end; lia).
    iApply (memchr_first dq b reg w ws a c0 k _ _ c 18446744073709551615 r with "Hl [Hw Hps] [HK]").
    + exact Hc.
    + exact Hb0.
    + exact Hb8.
    + exact Hal.
    + exact Hk8.
    + cbn [List.length]. lia.
    + exact Hreg.
    + constructor; [exact Hw0 | exact Hr'].
    + zl.
    + reflexivity.
    + lk H0.
    + lk H0.
    + lk H0.
    + lk H0.
    + lk H0.
    + lk H0.
    + exact Hhit.
    + cbn [words_ps]. rewrite ptsq_app. iFrame.
    + iIntros "Hl Hps". cbn [words_ps]. rewrite ptsq_app. iApply ("HK" with "Hl Hps").
  - change ((if false then 1 else 0) mod 2 ^ 32 =? 0) with true. cbn [edge_label].
    do 2 step. si "iw_2.v13" (a + n - 1). step.
    replace (memchr_end a n) with (a + n - 1) in Hhit by (unfold memchr_end; lia).
    iApply (memchr_first dq b reg w ws a c0 k _ _ c (a + n - 1) r with "Hl [Hw Hps] [HK]").
    + exact Hc.
    + exact Hb0.
    + exact Hb8.
    + exact Hal.
    + exact Hk8.
    + cbn [List.length]. lia.
    + exact Hreg.
    + constructor; [exact Hw0 | exact Hr'].
    + zl.
    + cbn. rewrite Zmod_0_l. cbn. rewrite (Z.mod_small (a + n - 1) (2 ^ 64)); [reflexivity | zl].
    + lk H0.
    + lk H0.
    + lk H0.
    + lk H0.
    + lk H0.
    + lk H0.
    + exact Hhit.
    + cbn [words_ps]. rewrite ptsq_app. iFrame.
    + iIntros "Hl Hps". cbn [words_ps]. rewrite ptsq_app. iApply ("HK" with "Hl Hps").
Qed.

End rules.

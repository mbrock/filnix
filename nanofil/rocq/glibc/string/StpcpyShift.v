From Glibc Require Import GlibcProgram.
(** When glibc's `c: stpcpy` has aligned the destination but the source
    is still misaligned by v bytes, it cannot copy whole source words.
    Instead it loads aligned source words and shifts each pair of
    neighbours together, so that every merged word holds the next eight
    bytes of the string. This module proves that loop.

    Each turn of the loop loads the next aligned word of the source,
    merges it with the previous one, and stores the merged word into the
    destination unless it holds the terminator. The proof reads every
    source word from the string's window, so a load never leaves the
    words that the string occupies. When a word holds the terminator,
    the loop hands the last bytes to the byte tail of StpcpyTail.v. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld FileInv LibioLogic StrlenBits GetoptBytes WordString StrcmpBits StrcmpLoop.
From Glibc Require Import StpcpyCode StpcpyBytes StpcpyTail .
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** ## Shifts and masks *)

(** The compiled code computes the shift amount 8 * v with a shift by 3. *)
Lemma sh_amt v : 0 <= v < 8 -> (v mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64 = 8 * v.
Proof. intros H. change ((3 mod 2 ^ 32) mod 64) with 3. change (2 ^ 3) with 8. rewrite (Z.mod_small v); [|lia]. rewrite Z.mod_small; lia. Qed.
(** A logical shift right in the IR is [shd] from StrcmpBits.v. *)
Lemma sh_down w v : w mod 2 ^ 64 / 2 ^ (((8 * v) mod 2 ^ 32) mod 64) = shd w v.
Proof.
  unfold shd. symmetry. apply Z.mod_small. pose proof (Z.mod_pos_bound w (2 ^ 64) ltac:(lia)).
  assert (0 < 2 ^ (((8 * v) mod 2 ^ 32) mod 64)) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia].
Qed.
(** The shift left that brings in the next word's bytes is [shu] from StrcmpBits.v. *)
Lemma sh_up w v : (w mod 2 ^ 64 * 2 ^ (((64 - 8 * v) mod 2 ^ 32) mod 64)) mod 2 ^ 64 = shu w v.
Proof. unfold shu. rewrite Zmod_mod. reflexivity. Qed.
(** A value of [shu] is already reduced. *)
Lemma shu_mod w v : shu w v mod 2 ^ 64 = shu w v.
Proof. unfold shu. rewrite !Zmod_mod. reflexivity. Qed.
(** Every byte of the all-ones word is 255. *)
Lemma byte_ones u : 0 <= u < 8 -> byte_of 18446744073709551615 u = 255.
Proof. intros H. assert (u = 0 \/ u = 1 \/ u = 2 \/ u = 3 \/ u = 4 \/ u = 5 \/ u = 6 \/ u = 7) as Hu by lia.
  destruct_or! Hu; subst u; vm_compute; reflexivity. Qed.

(** A word whose first m bytes are string bytes from index base on, and
    whose other bytes are not zero, has no zero byte exactly when the
    string goes on past those m bytes. *)
Lemma mask_len y S n base m :
  0 <= y < 2 ^ 64 -> 0 <= base <= n -> 0 <= m <= 8 ->
  (forall t, 0 <= t < m -> base + t <= n -> byte_of y t = nth (Z.to_nat (base + t)) S 0) ->
  (forall t, m <= t < 8 -> byte_of y t <> 0) ->
  (forall j, 0 <= j < n -> nth (Z.to_nat j) S 0 <> 0) -> nth (Z.to_nat n) S 0 = 0 ->
  (loop_mask y = 0 -> base + m <= n) /\ (loop_mask y <> 0 -> n < base + m).
Proof.
  intros Hy Hb Hm Hagree Hhi Hnz H0. split.
  - intros Hz. destruct (Z_le_gt_dec (base + m) n) as [|Hlt]; [assumption|]. exfalso.
    apply (proj1 (loop_mask_zero y Hy) Hz (n - base)); [lia|].
    rewrite Hagree; [|lia|lia]. replace (base + (n - base)) with n by lia. exact H0.
  - intros Hz. destruct (loop_mask_has_zero y Hy Hz) as (j & Hj & Hyj).
    destruct (Z_lt_le_dec j m) as [Hjm|Hjm]; [|exfalso; exact (Hhi j ltac:(lia) Hyj)].
    destruct (Z_le_gt_dec (base + j) n) as [Hle|]; [|lia].
    rewrite Hagree in Hyj; [|lia|lia]. destruct (Z.eq_dec (base + j) n); [lia|].
    exfalso. exact (Hnz (base + j) ltac:(lia) Hyj).
Qed.

(** This definition names the loop head of the unaligned word loop. *)
Definition blk_34 : block := Eval vm_compute in sblk "iw_2.L34".

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance stp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The unaligned word loop

    The loop holds the source word Q, which contains string bytes d - v
    onwards, and the address of the destination byte at offset d. Every
    string byte up to d + 8 - v is known to be nonzero, so the next
    source word still lies in the window. The loop stops at the first
    merged or loaded word that contains a zero byte, and the byte tail
    then copies the rest of the string with its terminator. *)

Lemma stp_shift_loop e bd rd xs o q b reg ws dq s d v Q Φ :
  str_shape q b reg ws s ->
  lookup (TAtom "iw_2.pr.6") e = Some (WInt (wrd ws Q)) ->
  lookup (TAtom "iw_2.pr.5") e = Some (WPtr (mkPtr (wstart q + 8 * (Q + 1)) (ptr_cap q))) ->
  lookup (TAtom "iw_2.pr.2") e = Some (WPtr (mkPtr (bd + o + d) (Obj bd))) ->
  lookup (TAtom "iw_2.v12") e = Some (WInt (8 * v)) -> lookup (TAtom "iw_2.v16") e = Some (WInt (64 - 8 * v)) ->
  ptr_addr q mod 8 + d = 8 * Q + v -> 0 < v < 8 -> 0 <= d -> d + 8 - v <= Z.of_nat (length s) ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> 0 <= bd -> bd + Z.of_nat (length xs) <= r_end rd ->
  r_end rd <= 2 ^ 48 ->
  live bd rd -∗ bytes bd 0 (stp_dst xs o d (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
  (live bd rd -∗ bytes bd 0 (stp_dst xs o (Z.of_nat (length s) + 1) (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
     Φ (Ret (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))))) -∗
  WP (ERun (mkFrame glibc_stpcpy e [] None (Exec (TAtom "iw_2.L34") (b_insts blk_34) (b_jump blk_34))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hs. destruct (shape_facts _ _ _ _ _ Hs) as (B & S1 & M & P & K & E & R & N & C).
  pose proof (ss_words _ _ _ _ _ Hs) as F. pose proof (ss_chars _ _ _ _ _ Hs) as Hch. pose proof (sbyte_agree _ _ _ _ _ Hs) as A.
  set (n := Z.of_nat (length s)) in *. set (S := (s ++ [0])%list) in *.
  assert (HSn : forall j, 0 <= j < n -> 0 < nth (Z.to_nat j) S 0 < 256).
  { intros j Hj. unfold S. rewrite app_nth1; [|lia]. apply (Forall_nth (fun c => 0 < c < 256)); [exact Hch | lia]. }
  assert (HS : Z.of_nat (length S) = n + 1) by (unfold S, n; rewrite length_app; cbn; lia).
  assert (HSz : forall j, 0 <= j < n -> nth (Z.to_nat j) S 0 <> 0) by (intros j Hj; pose proof (HSn j Hj); lia).
  assert (HS0 : nth (Z.to_nat n) S 0 = 0) by (unfold S, n; rewrite app_nth2; [|lia]; rewrite Nat2Z.id Nat.sub_diag; reflexivity).
  intros Hp6 Hp5 Hp2 H12 H16 HQ Hv Hd Hdn Ho Hox Hbd Hend Hreg.
  remember (Z.to_nat (n - d)) as r eqn:Hr.
  revert d Q e Hp6 Hp5 Hp2 H12 H16 HQ Hd Hdn Hr. induction r as [r IH] using lt_wf_ind.
  intros d Q e Hp6 Hp5 Hp2 H12 H16 HQ Hd Hdn Hr. iIntros "Hl Hb Hw HK". cbn [blk_34 b_insts b_jump].
  step.
  iApply (wp_win_word registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ _ dq b reg (wstart q - b) ws (Q + 1) with "Hw");
    [vx | exact C | cbn; lia | lia | lia | lia | lia | lia | exact F |]. iIntros "Hw".
  set (w := wrd ws Q). set (y := wrd ws (Q + 1)).
  pose proof (wrd_range ws Q F) as X. pose proof (wrd_range ws (Q + 1) F) as Y.
  step_symbolic. normz "iw_2.v42" (shd w v) ltac:(symmetry; apply sh_down).
  step_symbolic. normz "iw_2.v45" (shu y v) ltac:(symmetry; apply sh_up).
  step_symbolic. normz "iw_2.v46" (merge w y v) ltac:(rewrite shd_mod shu_mod; reflexivity).
  set (z := merge w y v). pose proof (merge_range w y v) as Z0.
  assert (Hz : forall t, 0 <= t < 8 -> d + t <= n -> byte_of z t = nth (Z.to_nat (d + t)) S 0).
  { intros t Ht Htn. unfold z, w, y. rewrite -(bt_merge ws (ptr_addr q mod 8) d Q v t); [|lia|lia|lia|lia]. apply (A (d + t)). lia. }
  do 4 step_symbolic. normt (loop_mask z) ltac:(reflexivity). step_symbolic. branch_symbolic.
  rewrite (Z.mod_small (loop_mask z)); [|apply loop_mask_range]. change (0 mod 2 ^ 64) with 0.
  destruct (mask_len z S n d 8 Z0 ltac:(lia) ltac:(lia) Hz ltac:(intros; lia) HSz HS0) as [Mz Mnz].
  destruct (Z.eq_dec (loop_mask z) 0) as [Ez|Ez].
  - rewrite Ez. close_edge. pose proof (Mz Ez) as Hd8.
    step. step. check "Hl".
    pose proof (length_stp_dst xs o d S Ho ltac:(lia) ltac:(lia)) as Hlen.
    iDestruct (bytes_splice bd _ (Z.to_nat (o + d)) 8 with "Hb") as "[Hx Hb]"; [lia|].
    rewrite Z2Nat.id; [|lia].
    iApply (wp_raw_store_l_bytes with "Hl Hx"); [vx | vx | reflexivity | a2 | rewrite length_take length_drop; lia | wi_store |].
    iNext. iIntros "Hl Hx". rewrite (Z.mod_small z); [|lia].
    rewrite (le_bytes_word z S (Z.to_nat d)); [|lia|].
    2:{ intros t Ht. rewrite Hz; [|lia|lia]. f_equal. lia. }
    iDestruct ("Hb" with "[%] Hx") as "Hb"; [rewrite length_take length_drop; lia|].
    iEval (rewrite stp_dst_word; [|lia|lia|lia|lia]) in "Hb".
    assert (Hy : forall t, 0 <= t < 8 -> (d + 8 - v) + t <= n -> byte_of y t = nth (Z.to_nat ((d + 8 - v) + t)) S 0).
    { intros t Ht Htn. unfold y. rewrite -(bt_at ws (ptr_addr q mod 8) (d + 8 - v) (Q + 1) t); [|lia|lia|lia]. apply (A _). lia. }
    destruct (mask_len y S n (d + 8 - v) 8 Y ltac:(lia) ltac:(lia) Hy ltac:(intros; lia) HSz HS0) as [My Mny].
    do 4 step_symbolic. normt (loop_mask y) ltac:(reflexivity). step_symbolic. branch_symbolic.
    rewrite (Z.mod_small (loop_mask y)); [|apply loop_mask_range]. change (0 mod 2 ^ 64) with 0.
    destruct (Z.eq_dec (loop_mask y) 0) as [Ey|Ey].
    + rewrite Ey. close_edge. pose proof (My Ey) as Hd16.
      step. cbn [ptr_addr ptr_cap].
      normp "iw_2.pr.5" (wstart q + 8 * (Q + 1 + 1)). normp "iw_2.pr.2" (bd + o + (d + 8)).
      normz "iw_2.pr.6" y ltac:(rewrite Z.mod_small; lia).
      iApply (IH (Z.to_nat (n - (d + 8))) ltac:(lia) (d + 8) (Q + 1) _ with "Hl Hb Hw HK"); try lk_prove; lia.
    + replace (loop_mask y =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ey). close_edge.
      pose proof (Mny Ey) as Hn16.
      step. step_symbolic. normz "iw_2.v68" (shd y v) ltac:(symmetry; apply sh_down).
      step_symbolic. normz "iw_2.v70" 0 ltac:(change (0 mod 2 ^ 32) with 0; rewrite Z.mul_0_l; reflexivity).
      step_symbolic. normz "iw_2.v71" 0 ltac:(reflexivity).
      step_symbolic. normz "iw_2.v72" (shd y v) ltac:(rewrite shd_mod Zmod_0_l Z.lor_0_r; reflexivity).
      step. step. step. step. change (0 mod 2 ^ 64) with 0.
      pose proof (shd_mod y v) as Hm. pose proof (Z.mod_pos_bound (shd y v) (2 ^ 64) ltac:(lia)) as Hr64. rewrite Hm in Hr64.
      cbn [ptr_addr ptr_cap]. normp "iw_2.iw_4.pr.1" (bd + o + (d + 8) + 0).
      normz "iw_2.pr.8" (shd y v) ltac:(symmetry; apply shd_mod).
      iApply (stp_tail2 _ bd rd xs o s (d + 8) 0 (shd y v) with "Hl [Hb] [HK Hw]"); try lk_prove; try lia.
      * intros t Ht Htn. rewrite shd_byte; [|lia|lia]. replace (t + v <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite Hy; [|lia|lia]. f_equal. f_equal. lia.
      * rewrite Z.add_0_r. iExact "Hb".
      * iIntros "Hl Hb". iApply ("HK" with "Hl Hb Hw").
  - replace (loop_mask z =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ez). close_edge.
    pose proof (Mnz Ez) as Hn8.
    step. step. step. change (0 mod 2 ^ 64) with 0.
    normp "iw_2.iw_4.pr.1" (bd + o + d + 0). normz "iw_2.pr.8" z ltac:(rewrite Z.mod_small; lia).
    iApply (stp_tail2 _ bd rd xs o s d 0 z with "Hl [Hb] [HK Hw]"); try lk_prove; try lia.
    + rewrite Z.add_0_r. iExact "Hb".
    + iIntros "Hl Hb". iApply ("HK" with "Hl Hb Hw").
Qed.
End rules.

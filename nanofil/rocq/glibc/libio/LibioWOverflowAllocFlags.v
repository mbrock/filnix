(** The first write can allocate a narrow buffer, change stdout to
    line buffering, and allocate a wide buffer. Those changes affect
    different flags. They preserve the bits that the next write or
    close tests to identify the stream and decide whether to lock it. *)

From Stdlib Require Import List ZArith Lia.
From iris.proofmode Require Import proofmode.
From Nanofil Require Import Syntax Values Memory Runtime Pieces.
From Glibc Require Import FileInv LibioLogic LibioWIdle LibioWXsputnWindow LibioWOverflowState
  LibioWOverflowAllocated LibioWAllocSetb LibioSetb LibioOverflowBase.
Import FileInv LibioLogic.
Open Scope Z_scope.

Lemma wo_f2_mask f2 a m : m = 2 \/ m = 32 \/ m = io_need_lock -> Z.land (wsetb_flags2 f2 a) m = Z.land f2 m.
Proof. intros [-> | [-> | ->]]; unfold wsetb_flags2; destruct (a =? 0);
  first [apply land_lor_const; reflexivity | rewrite -Z.land_assoc; reflexivity]. Qed.

(** A fresh narrow heap buffer belongs to the stream. Clearing the
    user-buffer bit leaves every other bit alone; the terminal test may
    have set the line-buffered bit just before that. *)
Lemma wo_nflags fl fl1 : 0 <= fl < 2^32 -> (fl1 = fl \/ fl1 = Z.lor fl io_line_buf) ->
  0 <= setb_flags fl1 1 < 2^32 /\ has (setb_flags fl1 1) io_user_buf = false /\
  (forall m, Z.land 513 m = 0 -> Z.land (setb_flags fl1 1) m = Z.land fl m).
Proof.
  intros F E. assert (F1 : 0 <= fl1 < 2^32) by (destruct E as [-> | ->]; [done|apply lor_lt32; unfold io_line_buf; lia]).
  split; [apply setb_flags_range; done|]. unfold has, setb_flags. change (1 =? 0) with false. cbn iota.
  split; [rewrite -Z.land_assoc; change (Z.land 4294967294 io_user_buf) with 0; rewrite Z.land_0_r; done|].
  intros m H. change 513 with (Z.lor 1 io_line_buf) in H. rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [One Line].
  assert (Split : Z.lor (Z.land fl1 4294967294) (Z.land fl1 1) = fl1).
  { rewrite -Z.land_lor_distr_r. change (Z.lor 4294967294 1) with (Z.ones 32). rewrite Z.land_ones; [apply Z.mod_small|]; lia. }
  assert (Same := f_equal (fun x => Z.land x m) Split). cbn beta in Same. rewrite Z.land_lor_distr_l -(Z.land_assoc fl1 1 m) One Z.land_0_r Z.lor_0_r in Same.
  rewrite Same. destruct E as [-> | ->]; [reflexivity|by apply land_lor_const].
Qed.

Lemma wo_fresh_ok fb st f2 fl1 bb sz p : 0 <= fs_flags st < 2^32 ->
  (fl1 = fs_flags st \/ fl1 = Z.lor (fs_flags st) io_line_buf) -> 0 < sz -> 0 < p -> p+4*sz <= 2^48 ->
  (forall m, (m = 2 \/ m = 32 \/ m = io_need_lock) -> Z.land f2 m = Z.land (fs_flags2 st) m) ->
  wo_alloc_ok fb st (NbHeap bb sz) (setb_flags fl1 1) (wsetb_flags2 f2 1) (WbHeap p (4*sz)) (mkPtr bb (Obj bb)) (mkPtr (bb+sz) (Obj bb)).
Proof. intros F Flag S P End B2. destruct (wo_nflags _ _ F Flag) as (R & User & Bits).
  unfold wo_alloc_ok, wo_storage, wbuf_user_ok, window_bound, window_size. rewrite wsetb_flags2_bit (Z.mul_comm 4 sz) Z.mod_mul;
    try lia. split_and!; try reflexivity; try assumption; try lia.
  - intros m M. rewrite wo_f2_mask; auto.
  - rewrite Z.div_mul; lia.
Qed.

Lemma wo_backup_clear st fl : wflags_ok st ->
  (forall m, Z.land 513 m = 0 -> Z.land fl m = Z.land (fs_flags st) m) -> Z.land fl 256 = 0.
Proof. intros (_ & _ & _ & F & _) Bits. apply Bool.negb_false_iff, Z.eqb_eq in F. rewrite Bits; [done|reflexivity]. Qed.

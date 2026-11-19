(** The stream stores its secondary flags in a signed 24-bit field.
    These rules describe the shifts and masks that update that field. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Values Ops.
From Glibc Require Import FileInv LibioLogic.
Open Scope Z_scope.

(** ## The flags2 bitfield

    The wrapper reads `c: _flags2` as a 24-bit signed bitfield of a 32-bit
    word whose top byte belongs to the next field. Shifting left by 8 and
    arithmetically right by 8 recovers the bitfield's value. Only its low
    24 bits reach memory again, so these lemmas reduce the stores to
    ordinary bit operations on the whole word. *)

(** The wrapper saves this signed value of the bitfield. *)
Definition fx_field (x : Z) : Z :=
  (sign_extension (2 ^ 32) (2 ^ 31) ((x * 2 ^ 8) mod 2 ^ 32) / 2 ^ 8) mod 2 ^ 32.

(** Sign extension keeps the bitfield's low 24 bits. *)
Lemma fx_field_low x : 0 <= x < 2 ^ 32 -> Z.land (fx_field x) 16777215 = Z.land x 16777215.
Proof.
  intros Hx. change 16777215 with (Z.ones 24).
  rewrite (Z.land_ones _ 24); [|lia]. rewrite (Z.land_ones _ 24); [|lia].
  unfold fx_field, sign_extension.
  pose proof (Z.mod_pos_bound x (2 ^ 24)) as Hb.
  assert (Hr : (x * 2 ^ 8) mod 2 ^ 32 = (x mod 2 ^ 24) * 2 ^ 8).
  { change (2 ^ 32) with (2 ^ 24 * 2 ^ 8). rewrite Z.mul_mod_distr_r; lia. }
  rewrite Hr. rewrite (Z.mod_small (x mod 2 ^ 24 * 2 ^ 8)); [|lia].
  destruct (Z.leb_spec (2 ^ 31) (x mod 2 ^ 24 * 2 ^ 8)).
  - replace (x mod 2 ^ 24 * 2 ^ 8 - 2 ^ 32) with ((x mod 2 ^ 24 - 2 ^ 24) * 2 ^ 8) by lia.
    rewrite Z.div_mul; [|lia].
    rewrite <- (Z.mod_unique (x mod 2 ^ 24 - 2 ^ 24) (2 ^ 32) (-1) (x mod 2 ^ 24 - 2 ^ 24 + 2 ^ 32));
      [|lia|lia].
    symmetry. apply (Z.mod_unique _ _ 255); lia.
  - rewrite Z.div_mul; [|lia]. rewrite (Z.mod_small (x mod 2 ^ 24)); [|lia].
    rewrite Z.mod_mod; lia.
Qed.

(** Both 32-bit words are equal when their high byte and low 24 bits are. *)
Lemma fx_split x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land x 4278190080) (Z.land x 16777215) = x.
Proof.
  intros Hx. rewrite <- Z.land_lor_distr_r. change (Z.lor 4278190080 16777215) with (Z.ones 32).
  rewrite Z.land_ones; [|lia]. apply Z.mod_small. lia.
Qed.

(** The temporary store sets bit 2 of the bitfield and keeps the high byte. *)
Lemma fx_set x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land x 4278190080) (Z.land (Z.lor (fx_field x) 2) 16777215) = Z.lor x 2.
Proof.
  intros Hx. rewrite Z.land_lor_distr_l (fx_field_low x Hx).
  change (Z.land 2 16777215) with 2. rewrite Z.lor_assoc (fx_split x Hx). reflexivity.
Qed.

(** The restoring store puts back the saved bitfield under the current high
    byte, which the formatter leaves as it found it. *)
Lemma fx_restore x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land (Z.lor x 2) 4278190080) (Z.land (fx_field x) 16777215) = x.
Proof.
  intros Hx. rewrite Z.land_lor_distr_l (fx_field_low x Hx).
  change (Z.land 2 4278190080) with 0. rewrite Z.lor_0_r. apply fx_split. exact Hx.
Qed.

(** Bit 2 is not the need-lock bit, so the temporary flags keep the stream's restriction. *)
Lemma fx_need_lock x : Z.land x io_need_lock = 0 -> Z.land (Z.lor x 2) io_need_lock = 0.
Proof. intros H. rewrite Z.land_lor_distr_l H. reflexivity. Qed.

(** The wrapper computes the bitfield with a left shift and an arithmetic
    right shift, each reduced to 32 bits. The result is [fx_field]. *)
Lemma fx_shift_field x y z : 0 <= x < 2 ^ 32 ->
  y = (x mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  z = (sign_extension (2 ^ 32) (2 ^ 31) (y mod 2 ^ 32) / 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  z = fx_field x.
Proof.
  intros Hx -> ->. unfold fx_field. change ((8 mod 2 ^ 32) mod 32) with 8.
  rewrite (Z.mod_small x); [|lia]. rewrite Z.mod_mod; [reflexivity|lia].
Qed.

(** A bitwise and with a mask below 2^32 stays below 2^32. *)
Lemma fx_land_lt32 a b : 0 <= a -> 0 <= b < 2 ^ 32 -> 0 <= Z.land a b < 2 ^ 32.
Proof.
  intros Ha Hb. split; [apply Z.land_nonneg; lia|].
  rewrite Z.land_comm. rewrite <- (Z.mod_small b (2 ^ 32)) at 1; [|lia].
  rewrite <- (Z.land_ones b 32); [|lia].
  rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 32) a), Z.land_assoc.
  rewrite Z.land_ones; [|lia]. apply Z.mod_pos_bound. lia.
Qed.

(** The field value is a 32-bit word. *)
Lemma fx_field_range x : 0 <= fx_field x < 2 ^ 32.
Proof. unfold fx_field. apply Z.mod_pos_bound. lia. Qed.

(** The four operations of the temporary store produce flags2 with bit 2 set. *)
Lemma fx_set_ops x f a b c d : 0 <= x < 2 ^ 32 -> f = fx_field x ->
  a = Z.lor (f mod 2 ^ 32) (2 mod 2 ^ 32) ->
  b = Z.land (x mod 2 ^ 32) (4278190080 mod 2 ^ 32) ->
  c = Z.land (a mod 2 ^ 32) (16777215 mod 2 ^ 32) ->
  d = Z.lor (b mod 2 ^ 32) (c mod 2 ^ 32) -> d = Z.lor x 2.
Proof.
  intros Hx -> -> -> -> ->. pose proof (fx_field_range x) as Hf.
  change (2 mod 2 ^ 32) with 2. change (4278190080 mod 2 ^ 32) with 4278190080.
  change (16777215 mod 2 ^ 32) with 16777215.
  rewrite (Z.mod_small (fx_field x)); [|lia]. rewrite (Z.mod_small x); [|lia].
  assert (Ha : 0 <= Z.lor (fx_field x) 2 < 2 ^ 32) by (apply lor_lt32; lia).
  rewrite (Z.mod_small (Z.lor (fx_field x) 2)); [|lia].
  rewrite (Z.mod_small (Z.land x 4278190080)); [|apply fx_land_lt32; lia].
  rewrite (Z.mod_small (Z.land (Z.lor (fx_field x) 2) 16777215)); [|apply fx_land_lt32; lia].
  apply fx_set. exact Hx.
Qed.

(** The three operations of the restoring store give back the saved flags2. *)
Lemma fx_restore_ops x f b c d : 0 <= x < 2 ^ 32 -> f = fx_field x ->
  b = Z.land (Z.lor x 2 mod 2 ^ 32) (4278190080 mod 2 ^ 32) ->
  c = Z.land (f mod 2 ^ 32) (16777215 mod 2 ^ 32) ->
  d = Z.lor (b mod 2 ^ 32) (c mod 2 ^ 32) -> d = x.
Proof.
  intros Hx -> -> -> ->. pose proof (fx_field_range x) as Hf.
  assert (Ho : 0 <= Z.lor x 2 < 2 ^ 32) by (apply lor_lt32; lia).
  change (4278190080 mod 2 ^ 32) with 4278190080. change (16777215 mod 2 ^ 32) with 16777215.
  rewrite (Z.mod_small (fx_field x)); [|lia]. rewrite (Z.mod_small (Z.lor x 2)); [|lia].
  rewrite (Z.mod_small (Z.land (Z.lor x 2) 4278190080)); [|apply fx_land_lt32; lia].
  rewrite (Z.mod_small (Z.land (fx_field x) 16777215)); [|apply fx_land_lt32; lia].
  apply fx_restore. exact Hx.
Qed.

(** These values separate the real bitfield arithmetic from plausible
    mistakes. The word 8388609 has bit 23, the bitfield's sign bit, set, so
    its saved value is negative and sign-extends into the high byte. The
    restoring store must mask it; restoring the saved value whole would
    give 4286578689. The word 4278190208 has a nonzero high byte that both
    stores must keep, and its need-lock bit is set. *)
Example fx_controls :
  fx_field 8388609 = 4286578689 /\
  Z.lor (Z.land 8388609 4278190080) (Z.land (Z.lor (fx_field 8388609) 2) 16777215) = 8388611 /\
  Z.lor (Z.land 8388611 4278190080) (Z.land (fx_field 8388609) 16777215) = 8388609 /\
  Z.lor (Z.land 8388611 4278190080) (fx_field 8388609) <> 8388609 /\
  fx_field 4278190208 = 128 /\
  Z.lor (Z.land 4278190208 4278190080) (Z.land (Z.lor (fx_field 4278190208) 2) 16777215) = 4278190210 /\
  Z.land 4278190208 io_need_lock <> 0.
Proof. vm_compute. repeat split; discriminate || reflexivity. Qed.

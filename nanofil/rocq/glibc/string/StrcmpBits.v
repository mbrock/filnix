(** Pure byte-string comparison [strcmp_res] and word-level bitmask
    facts for glibc's `__GI_strcmp` (StrcmpLogic.v). *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Syntax Values Memory Ops.
From Glibc Require Import StrlenBits StrlenLogic WordString.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Pure byte-list comparison *)

(** The 32-bit unsigned-byte difference of the C strings s1 and s2 at their first mismatch, or 0 when equal. *)
Fixpoint strcmp_res (s1 s2 : list Z) : Z :=
  match s1, s2 with
  | [], [] => 0 | [], c2 :: _ => (0 - c2) mod 2 ^ 32 | c1 :: _, [] => (c1 - 0) mod 2 ^ 32
  | c1 :: s1', c2 :: s2' => if c1 =? c2 then strcmp_res s1' s2' else (c1 - c2) mod 2 ^ 32
  end.

(** A shared prefix does not change [strcmp_res]. *)
Lemma strcmp_res_app p s1 s2 : strcmp_res (p ++ s1) (p ++ s2) = strcmp_res s1 s2.
Proof. induction p as [|c p IH]; [reflexivity|]. cbn. rewrite Z.eqb_refl. exact IH. Qed.

(** Two bytes with zero 32-bit difference are equal. *)
Lemma sub32_eq_0 c1 c2 : 0 <= c1 < 256 -> 0 <= c2 < 256 -> (c1 - c2) mod 2 ^ 32 = 0 <-> c1 = c2.
Proof. intros H1 H2. split; [intros H; Z.div_mod_to_equations; lia | intros ->; by rewrite Z.sub_diag]. Qed.

(** [strcmp_res] is 0 if and only if the two C strings are equal. *)
Lemma strcmp_res_eq_0 s1 s2 :
  Forall (fun c => 0 < c < 256) s1 -> Forall (fun c => 0 < c < 256) s2 -> (strcmp_res s1 s2 = 0 <-> s1 = s2).
Proof.
  revert s2. induction s1 as [|c1 s1 IH]; intros [|c2 s2] H1 H2; cbn [strcmp_res]; [tauto| | |].
  - apply Forall_cons_1 in H2 as [Hc2 _]. split; [intros H; Z.div_mod_to_equations; lia | discriminate].
  - apply Forall_cons_1 in H1 as [Hc1 _]. split; [intros H; Z.div_mod_to_equations; lia | discriminate].
  - apply Forall_cons_1 in H1 as [Hc1 H1]. apply Forall_cons_1 in H2 as [Hc2 H2].
    destruct (Z.eqb_spec c1 c2) as [->|Hne]; [rewrite (IH s2 H1 H2); split; congruence|].
    split; [intros H; Z.div_mod_to_equations; lia | intros [= ->]; contradiction].
Qed.

(** At the first index j where c1 is 0 or differs from c2, [strcmp_res] is `(c1 - c2) mod 2 ^ 32`. *)
Lemma strcmp_res_at s1 s2 (j : nat) c1 c2 :
  Forall (fun c => 0 < c < 256) s1 -> Forall (fun c => 0 < c < 256) s2 ->
  (forall k : nat, (k < j)%nat -> (s1 ++ [0]) !! k = (s2 ++ [0]) !! k) ->
  (s1 ++ [0]) !! j = Some c1 -> (s2 ++ [0]) !! j = Some c2 -> (c1 = 0 \/ c1 <> c2) ->
  strcmp_res s1 s2 = (c1 - c2) mod 2 ^ 32.
Proof.
  revert s1 s2. induction j as [|j IH]; intros s1 s2 H1 H2 Hprev Hj1 Hj2 Hstop.
  - destruct s1 as [|a1 s1], s2 as [|a2 s2]; cbn in Hj1, Hj2 |- *; injection Hj1 as <-; injection Hj2 as <-;
      try reflexivity.
    apply Forall_cons_1 in H1 as [Ha1 _]. destruct (Z.eqb_spec a1 a2) as [->|]; [lia | reflexivity].
  - destruct s1 as [|a1 s1]; [cbn in Hj1; rewrite lookup_nil in Hj1; discriminate|].
    destruct s2 as [|a2 s2]; [cbn in Hj2; rewrite lookup_nil in Hj2; discriminate|].
    pose proof (Hprev 0%nat ltac:(lia)) as H0. cbn in H0. injection H0 as <-.
    apply Forall_cons_1 in H1 as [_ H1]. apply Forall_cons_1 in H2 as [_ H2]. cbn [strcmp_res]. rewrite Z.eqb_refl.
    apply (IH s1 s2 H1 H2); [intros k Hk; exact (Hprev (S k) ltac:(lia)) | exact Hj1 | exact Hj2 | exact Hstop].
Qed.

(** ## Byte and alignment arithmetic *)

(** Sign-extending a byte to 32 bits and zero-extending its low byte gives the byte back. *)
Lemma ext_ub_sb c : 0 <= c < 256 -> (extension Sb c mod 2 ^ 32 mod 2 ^ 32) mod 256 mod 2 ^ 32 = c.
Proof.
  intros Hc. apply Z.eqb_eq.
  exact (all_bytes (fun c => ((extension Sb c mod 2 ^ 32 mod 2 ^ 32) mod 256 mod 2 ^ 32 =? c))
           ltac:(vm_compute; reflexivity) c Hc).
Qed.

(** Shifting right by 8j bits and zero-extending the low byte to 32 bits extracts byte j. *)
Lemma shr_ext_ub x j : 0 <= j < 8 -> extension Ub ((x / 2 ^ (8 * j)) mod 2 ^ 32) mod 2 ^ 32 = byte_of x j.
Proof. intros Hj. unfold extension, byte_of. Z.div_mod_to_equations. lia. Qed.

(** A 64-bit word shifted right by 8k bits stays in 64-bit range. *)
Lemma div_pow8_range u k : 0 <= u < 2 ^ 64 -> 0 <= k -> 0 <= u / 2 ^ (8 * k) < 2 ^ 64.
Proof.
  intros Hu Hk. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply (Z.le_lt_trans _ u); [|lia]. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  pose proof (Z.pow_pos_nonneg 2 (8 * k) ltac:(lia)). nia.
Qed.

(** The negated address masked with 7 is `(- a) mod 8`. *)
Lemma align_rem a : Z.land ((- (a mod 2 ^ 64)) mod 2 ^ 64 mod 2 ^ 64) (7 mod 2 ^ 64) = (- a) mod 8.
Proof.
  change (7 mod 2 ^ 64) with (Z.ones 3). rewrite Z.land_ones; [|lia]. change (2 ^ 3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

(** An address masked with 7 is its offset in its 8-byte word. *)
Lemma mod8_land a : 0 <= a -> Z.land (a mod 2 ^ 64) (7 mod 2 ^ 64) = a mod 8.
Proof.
  intros Ha. change (7 mod 2 ^ 64) with (Z.ones 3). rewrite Z.land_ones; [|lia]. change (2 ^ 3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

(** Shifting left by m whole bytes puts 0 in the low m bytes and moves byte i - m to byte i. *)
Lemma byte_of_mul z m i : 0 <= m -> 0 <= i ->
  byte_of (z * 2 ^ (8 * m)) i = if i <? m then 0 else byte_of z (i - m).
Proof.
  intros Hm Hi. apply Z.bits_inj'. intros n Hn.
  rewrite -Z.shiftl_mul_pow2; [|lia]. rewrite byte_of_bits; [|lia|lia].
  destruct (i <? m) eqn:Ei.
  - apply Z.ltb_lt in Ei. rewrite Z.bits_0. destruct (n <? 8) eqn:En; [|reflexivity].
    apply Z.ltb_lt in En. rewrite Z.shiftl_spec_low; [reflexivity | lia].
  - apply Z.ltb_ge in Ei. rewrite byte_of_bits; [|lia|lia].
    destruct (n <? 8) eqn:En; [|reflexivity]. apply Z.ltb_lt in En.
    rewrite Z.shiftl_spec_high; [|lia|lia]. do 2 f_equal. lia.
Qed.

(** An or of words in range is in range. *)
Lemma lor_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.lor a b mod 2 ^ 64 = Z.lor a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2; [|lia]. rewrite Z.lor_spec.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
    rewrite (bits64 a n Ha E) (bits64 b n Hb E). reflexivity. }
  rewrite -E. apply Z.mod_pos_bound. lia.
Qed.

(** ## The comparison mask *)

(** glibc's `find_zero_ne_all` (string-fza.h) on two words x and y: 128 in
    each byte where x is 0 or x and y differ, 0 in each other. *)
Definition cmp_mask (x y : Z) : Z :=
  let v9 := Z.lxor (x mod 2 ^ 64) (y mod 2 ^ 64) in let v13 := Z.land (x mod 2 ^ 64) ones7 in
  let v15 := (v13 mod 2 ^ 64 + ones7) mod 2 ^ 64 in let v17 := Z.lor (v15 mod 2 ^ 64) (x mod 2 ^ 64) in
  let v21 := Z.land (v9 mod 2 ^ 64) ones7 in let v23 := (v21 mod 2 ^ 64 + ones7) mod 2 ^ 64 in
  let v25 := Z.lor (v23 mod 2 ^ 64) (v9 mod 2 ^ 64) in let v28 := Z.lxor (v17 mod 2 ^ 64) all64 in
  let v29 := Z.lor (v25 mod 2 ^ 64) (v28 mod 2 ^ 64) in Z.land (v29 mod 2 ^ 64) highs.

(** The ten-instruction chain that computes [cmp_mask] x y. *)
Lemma cmp_mask_chain x y v9 v13 v15 v17 v21 v23 v25 v28 v29 v32 :
  v9 = Z.lxor (x mod 2 ^ 64) (y mod 2 ^ 64) -> v13 = Z.land (x mod 2 ^ 64) (9187201950435737471 mod 2 ^ 64) ->
  v15 = (v13 mod 2 ^ 64 + 9187201950435737471 mod 2 ^ 64) mod 2 ^ 64 -> v17 = Z.lor (v15 mod 2 ^ 64) (x mod 2 ^ 64) ->
  v21 = Z.land (v9 mod 2 ^ 64) (9187201950435737471 mod 2 ^ 64) ->
  v23 = (v21 mod 2 ^ 64 + 9187201950435737471 mod 2 ^ 64) mod 2 ^ 64 -> v25 = Z.lor (v23 mod 2 ^ 64) (v9 mod 2 ^ 64) ->
  v28 = Z.lxor (v17 mod 2 ^ 64) ((-1) mod 2 ^ 64) -> v29 = Z.lor (v25 mod 2 ^ 64) (v28 mod 2 ^ 64) ->
  v32 = Z.land (v29 mod 2 ^ 64) (9259542123273814144 mod 2 ^ 64) -> v32 = cmp_mask x y.
Proof.
  intros -> -> -> -> -> -> -> -> -> ->. unfold cmp_mask.
  change (9187201950435737471 mod 2 ^ 64) with ones7. change ((-1) mod 2 ^ 64) with all64.
  change (9259542123273814144 mod 2 ^ 64) with highs. reflexivity.
Qed.

(** [cmp_mask] is a 64-bit word. *)
Lemma cmp_mask_range x y : 0 <= cmp_mask x y < 2 ^ 64.
Proof. unfold cmp_mask. apply land_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** High-bit detection on a single byte for zero and nonzero tests. *)
Lemma cmp_byte_bits b : 0 <= b < 256 ->
  Z.land (Z.lxor (Z.lor (Z.land b 127 + 127) b) 255) 128 = (if b =? 0 then 128 else 0) /\
  Z.land (Z.lor (Z.land b 127 + 127) b) 128 = (if b =? 0 then 0 else 128).
Proof.
  intros Hb. split; apply Z.eqb_eq; revert b Hb; apply all_bytes; vm_compute; reflexivity.
Qed.

(** Byte i of [cmp_mask] x y is 128 if byte i of x is 0 or differs from byte i of y, else 0. *)
Lemma cmp_mask_byte x y i : 0 <= i < 8 ->
  byte_of (cmp_mask x y) i =
    if (byte_of x i =? 0) || negb (byte_of x i =? byte_of y i) then 128 else 0.
Proof.
  intros Hi. unfold cmp_mask.
  assert (Hadd : forall u, 0 <= i < 8 ->
    byte_of ((Z.land (u mod 2 ^ 64) ones7 mod 2 ^ 64 + ones7) mod 2 ^ 64) i = Z.land (byte_of u i) 127 + 127).
  { intros u _. rewrite byte_of_mod64; [|lia]. rewrite byte_of_add; [| |lia].
    - rewrite byte_of_mod64; [|lia]. rewrite byte_of_land; [|lia].
      rewrite byte_of_mod64; [|lia]. rewrite !byte_ones7; [reflexivity | lia].
    - intros j Hj. rewrite byte_of_mod64; [|lia]. rewrite byte_of_land; [|lia].
      rewrite byte_of_mod64; [|lia]. rewrite !byte_ones7; [|lia].
      pose proof (land127 (byte_of u j) (byte_of_range u j)). lia. }
  repeat (first
    [ rewrite (Hadd _ Hi) | rewrite byte_of_mod64; [|lia] | rewrite byte_of_land; [|lia]
    | rewrite byte_of_lor; [|lia] | rewrite byte_of_lxor; [|lia]
    | rewrite byte_highs; [|lia] | rewrite byte_all64; [|lia] | rewrite byte_ones7; [|lia] ]).
  rewrite -(byte_of_lxor x y i); [|lia]. rewrite Z.land_lor_distr_l.
  rewrite (proj2 (cmp_byte_bits _ (byte_of_range _ _))) (proj1 (cmp_byte_bits _ (byte_of_range _ _))).
  rewrite byte_of_lxor; [|lia].
  destruct (byte_of x i =? 0), (Z.eqb_spec (Z.lxor (byte_of x i) (byte_of y i)) 0) as [H|H],
    (Z.eqb_spec (byte_of x i) (byte_of y i)) as [E|E];
    try (exfalso; apply E, Z.lxor_eq_0_iff, H); try (exfalso; apply H, Z.lxor_eq_0_iff, E); reflexivity.
Qed.

(** Every byte of [cmp_mask] x y is 0 or 128. *)
Lemma cmp_mask_01 x y i : 0 <= i < 8 -> byte_of (cmp_mask x y) i = 0 \/ byte_of (cmp_mask x y) i = 128.
Proof.
  intros Hi. rewrite cmp_mask_byte; [|lia].
  destruct ((byte_of x i =? 0) || negb (byte_of x i =? byte_of y i)); auto.
Qed.

(** A 64-bit word with a 128 at byte j is nonzero. *)
Lemma mask_nz m j : 0 <= m < 2 ^ 64 -> 0 <= j < 8 -> byte_of m j = 128 -> (m mod 2 ^ 64 =? 0) = false.
Proof.
  intros Hm Hj Hb. rewrite (Z.mod_small m (2 ^ 64) Hm). apply Z.eqb_neq. intros ->.
  unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate | apply Z.pow_nonzero; lia].
Qed.

(** ## Unaligned words and loop masks *)

(** Merging two consecutive words u0 and u1 of an unaligned second
    string at offset k in its word: `(u0 >> 8k) | (u1 << (64 - 8k))`.
    With `u1 = all64`, this pads the high k bytes with 0xff (`L58`). *)
Definition merge_words (u0 u1 k : Z) : Z := Z.lor (u0 / 2 ^ (8 * k)) ((u1 * 2 ^ (64 - 8 * k)) mod 2 ^ 64).

(** [merge_words] is a 64-bit word. *)
Lemma merge_words_range u0 u1 k :
  0 <= u0 < 2 ^ 64 -> 0 <= u1 < 2 ^ 64 -> 1 <= k < 8 -> 0 <= merge_words u0 u1 k < 2 ^ 64.
Proof. intros Hu0 _ Hk. apply lor_range; [apply div_pow8_range; lia | apply Z.mod_pos_bound; lia]. Qed.

(** Byte i of [merge_words] u0 u1 k is byte i + k of u0 for i < 8 - k,
    and byte i - (8 - k) of u1 for i >= 8 - k. *)
Lemma byte_of_merge_words u0 u1 k i :
  0 <= u0 < 2 ^ 64 -> 0 <= u1 < 2 ^ 64 -> 1 <= k < 8 -> 0 <= i < 8 ->
  byte_of (merge_words u0 u1 k) i =
    if i <? 8 - k then byte_of u0 (i + k) else byte_of u1 (i - (8 - k)).
Proof.
  intros Hu0 Hu1 Hk Hi. unfold merge_words. rewrite byte_of_lor; [|lia]. rewrite byte_of_div; [|lia|lia].
  rewrite byte_of_mod64; [|lia]. replace (64 - 8 * k) with (8 * (8 - k)) by lia.
  rewrite byte_of_mul; [|lia|lia]. destruct (i <? 8 - k) eqn:Ei; [by rewrite Z.lor_0_r|].
  apply Z.ltb_ge in Ei. rewrite (byte_of_high u0 (i + k)); [|exact Hu0|lia]. by rewrite Z.lor_0_l.
Qed.

(** Byte k + i of `wbytes (u0 :: u1 :: ws)` is byte i of [merge_words] u0 u1 k. *)
Lemma wbytes_merge u0 u1 ws (k i : nat) :
  0 <= u0 < 2 ^ 64 -> 0 <= u1 < 2 ^ 64 -> (1 <= k < 8)%nat -> (i < 8)%nat ->
  wbytes (u0 :: u1 :: ws) !! (k + i)%nat = Some (byte_of (merge_words u0 u1 (Z.of_nat k)) (Z.of_nat i)).
Proof.
  intros Hu0 Hu1 Hk Hi. rewrite byte_of_merge_words; [|exact Hu0|exact Hu1|lia|lia].
  destruct (Z.of_nat i <? 8 - Z.of_nat k) eqn:E.
  - apply Z.ltb_lt in E. rewrite wbytes_head; [|lia]. do 2 f_equal. lia.
  - apply Z.ltb_ge in E. replace (k + i)%nat with (8 + (k + i - 8))%nat by lia.
    rewrite wbytes_tail wbytes_head; [|lia]. do 2 f_equal. lia.
Qed.

(** The IR expression in `iw_2.L36` and `L58` computes [merge_words] u0 u1 k. *)
Lemma merge_words_ir u0 u1 k :
  0 <= u0 < 2 ^ 64 -> 0 <= u1 < 2 ^ 64 -> 1 <= k < 8 ->
  Z.lor ((u0 mod 2 ^ 64 / 2 ^ (((8 * k) mod 2 ^ 32) mod 64)) mod 2 ^ 64)
        (((u1 mod 2 ^ 64 * 2 ^ (((64 - 8 * k) mod 2 ^ 32) mod 64)) mod 2 ^ 64) mod 2 ^ 64) =
  merge_words u0 u1 k.
Proof.
  intros Hu0 Hu1 Hk. unfold merge_words.
  rewrite (Z.mod_small u0 (2 ^ 64) Hu0) (Z.mod_small u1 (2 ^ 64) Hu1).
  rewrite (Z.mod_small (8 * k) (2 ^ 32) ltac:(lia)) (Z.mod_small (8 * k) 64 ltac:(lia)).
  rewrite (Z.mod_small (64 - 8 * k) (2 ^ 32) ltac:(lia)) (Z.mod_small (64 - 8 * k) 64 ltac:(lia)).
  rewrite !Z.mod_mod; [|lia]. rewrite (Z.mod_small _ (2 ^ 64) (div_pow8_range u0 k Hu0 ltac:(lia))). reflexivity.
Qed.

(** The IR expression in `iw_2.L72` computes `u1 / 2 ^ (8 * k)`. *)
Lemma tail_shift_ir u1 k :
  0 <= u1 < 2 ^ 64 -> 1 <= k < 8 ->
  Z.lor ((u1 mod 2 ^ 64 / 2 ^ (((8 * k) mod 2 ^ 32) mod 64)) mod 2 ^ 64)
        ((extension Sw (((0 * 2 ^ (((64 - 8 * k) mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64) mod 2 ^ 64) =
  u1 / 2 ^ (8 * k) /\ 0 <= u1 / 2 ^ (8 * k) < 2 ^ 64.
Proof.
  intros Hu1 Hk. pose proof (div_pow8_range u1 k Hu1 ltac:(lia)) as Hdiv. split; [|exact Hdiv].
  rewrite (Z.mod_small u1 (2 ^ 64) Hu1) (Z.mod_small (8 * k) (2 ^ 32) ltac:(lia)) (Z.mod_small (8 * k) 64 ltac:(lia)).
  rewrite (Z.mod_small _ (2 ^ 64) Hdiv) Z.mul_0_l.
  change (((extension Sw ((0 mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64) mod 2 ^ 64)) with 0. apply Z.lor_0_r.
Qed.

(** If all bytes of [loop_mask] x below n are 0, then all bytes of x below n are nonzero. *)
Lemma loop_mask_zero_prefix x n :
  0 <= n <= 8 -> (forall i, 0 <= i < n -> byte_of (loop_mask x) i = 0) ->
  forall i, 0 <= i < n -> byte_of x i <> 0.
Proof.
  intros [H0 H8]. revert H8. pattern n. apply natlike_ind; [intros _ _ i Hi; lia | | exact H0].
  intros k Hk IH Hk8 Hm i Hi. unfold Z.succ in *.
  assert (Hprev : forall j, 0 <= j < k -> byte_of x j <> 0) by (apply (IH ltac:(lia)); intros; apply Hm; lia).
  destruct (Z.lt_ge_cases i k) as [Hlt|Hge]; [apply Hprev; lia|].
  assert (i = k) as -> by lia. intros Hz.
  pose proof (loop_mask_at x k ltac:(lia) Hprev Hz). pose proof (Hm k ltac:(lia)). lia.
Qed.

(** [loop_mask] x is 0 if and only if all eight bytes of x are nonzero. *)
Lemma loop_mask_eq_0 x : loop_mask x = 0 <-> forall i, 0 <= i < 8 -> byte_of x i <> 0.
Proof.
  split.
  - intros Hm. apply (loop_mask_zero_prefix x 8 ltac:(lia)). intros i Hi. by rewrite Hm.
  - intros Hnz. apply zero_word; [apply loop_mask_range | intros i Hi; apply (loop_mask_below x 8 i ltac:(lia) Hnz Hi)].
Qed.

(** If the 8 - k bytes of u0 from k are nonzero and [loop_mask] u1 is 0,
    then [loop_mask] of [merge_words] u0 u1 k is 0. *)
Lemma merge_words_mask_0 u0 u1 k :
  0 <= u0 < 2 ^ 64 -> 0 <= u1 < 2 ^ 64 -> 1 <= k < 8 ->
  (forall i, 0 <= i < 8 - k -> byte_of u0 (i + k) <> 0) -> loop_mask u1 = 0 ->
  loop_mask (merge_words u0 u1 k) = 0.
Proof.
  intros Hu0 Hu1 Hk Hnz0 Hm1. apply loop_mask_eq_0. intros i Hi.
  rewrite (byte_of_merge_words u0 u1 k i Hu0 Hu1 Hk Hi).
  destruct (i <? 8 - k) eqn:E; [apply Z.ltb_lt in E; apply Hnz0; lia | apply Z.ltb_ge in E; apply (proj1 (loop_mask_eq_0 u1) Hm1); lia].
Qed.

(** The least natural number at most k satisfying P, when k satisfies P. *)
Lemma find_first_nat (P : Z -> bool) (k : nat) :
  P (Z.of_nat k) = true ->
  exists j : nat, (j <= k)%nat /\ P (Z.of_nat j) = true /\ forall i, 0 <= i < Z.of_nat j -> P i = false.
Proof.
  revert P. induction k as [|k IH]; intros P Hk; [exists 0%nat; split; [lia | split; [exact Hk | intros; lia]]|].
  destruct (P 0) eqn:E0; [exists 0%nat; split; [lia | split; [exact E0 | intros; lia]]|].
  rewrite Nat2Z.inj_succ in Hk. unfold Z.succ in Hk.
  destruct (IH (fun z => P (z + 1)) Hk) as (j & Hj & HPj & Hlow).
  exists (S j). split; [lia|]. rewrite Nat2Z.inj_succ. unfold Z.succ.
  split; [exact HPj|]. intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne]; [exact E0|].
  replace i with ((i - 1) + 1) by lia. apply Hlow. lia.
Qed.

(** ## String shapes and word steps *)

(** A [str_shape] always has at least one word in its window. *)
Lemma str_shape_nonempty p b reg ws s : str_shape p b reg ws s -> ws <> [].
Proof.
  intros Hs ->. pose proof (ss_len _ _ _ _ _ Hs) as Hl.
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). cbn in Hl.
  assert (0 < (ptr_addr p mod 8 + Z.of_nat (length s) + 8) / 8) by (apply Z.div_str_pos; lia). lia.
Qed.

(** Bounds on `wstart p` and `ptr_addr p` from [str_shape]. *)
Lemma str_shape_addr_bound p b reg ws s :
  str_shape p b reg ws s ->
  1 <= b /\ b <= wstart p /\ wstart p <= ptr_addr p /\ ptr_addr p + 1 <= wstart p + 8 /\
  wstart p + 8 <= wstart p + 8 * Z.of_nat (length ws) /\ wstart p + 8 * Z.of_nat (length ws) <= 2 ^ 48.
Proof.
  intros Hs. pose proof (ss_base _ _ _ _ _ Hs). pose proof (ss_align _ _ _ _ _ Hs).
  pose proof (ss_start _ _ _ _ _ Hs). pose proof (ss_fit _ _ _ _ _ Hs).
  pose proof (ss_space _ _ _ _ _ Hs). pose proof (str_shape_nonempty _ _ _ _ _ Hs).
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). unfold wstart in *.
  assert (b <= ptr_addr p - ptr_addr p mod 8) by
    (pose proof (Z.div_mod (ptr_addr p) 8 ltac:(lia)); pose proof (Z.div_mod b 8 ltac:(lia)); nia).
  destruct ws; [contradiction | cbn [length] in *; lia].
Qed.

(** Byte i <= length s of an 8-aligned [str_shape] (w :: ws) is byte i of w, for i < 8. *)
Lemma str_shape_aligned_byte p b reg w ws s (i : nat) :
  str_shape p b reg (w :: ws) s -> ptr_addr p mod 8 = 0 -> (i <= length s)%nat -> (i < 8)%nat ->
  (s ++ [0]) !! i = Some (byte_of w (Z.of_nat i)).
Proof.
  intros Hs Ha Hi H8. rewrite -(str_shape_byte p b reg (w :: ws) s i Hs Hi); rewrite Ha.
  cbn [Z.to_nat Nat.add]. exact (wbytes_head w ws i H8).
Qed.

(** Byte i <= length s2 of an unaligned string `u0 :: u1 :: ws2` for i < 8 is byte i of [merge_words]. *)
Lemma str_shape_merge_byte p2 b2 reg2 u0 u1 ws2 s2 (i : nat) :
  str_shape p2 b2 reg2 (u0 :: u1 :: ws2) s2 -> 1 <= ptr_addr p2 mod 8 < 8 ->
  (i <= length s2)%nat -> (i < 8)%nat ->
  (s2 ++ [0]) !! i = Some (byte_of (merge_words u0 u1 (ptr_addr p2 mod 8)) (Z.of_nat i)).
Proof.
  intros Hs2 Hk2 Hi H8. pose proof (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs2)) as [Hu0 Hws2].
  pose proof (proj1 (Forall_cons_1 _ _ _ Hws2)) as Hu1.
  rewrite -(str_shape_byte p2 b2 reg2 (u0 :: u1 :: ws2) s2 i Hs2 Hi).
  rewrite (wbytes_merge u0 u1 ws2 (Z.to_nat (ptr_addr p2 mod 8)) i Hu0 Hu1 ltac:(lia) H8).
  rewrite Z2Nat.id; [reflexivity | lia].
Qed.

(** The first byte of (s ++ [0]) is [hd] 0 s, in [0, 256). *)
Lemma str_shape_hd_range p b reg ws s :
  str_shape p b reg ws s -> 0 <= hd 0 s < 256 /\ (s ++ [0]) !! 0%nat = Some (hd 0 s).
Proof.
  intros Hs. pose proof (ss_chars _ _ _ _ _ Hs) as Hc.
  destruct s as [|c s]; [cbn; split; [lia | reflexivity]|].
  apply Forall_cons_1 in Hc as [Hc _]. cbn. split; [lia | reflexivity].
Qed.

(** If the first n bytes from p in ws are nonzero, then n <= length s. *)
Lemma str_shape_nonzero_len n p b reg ws s :
  str_shape p b reg ws s ->
  (forall k : nat, (k < n)%nat -> exists c, c <> 0 /\ wbytes ws !! (Z.to_nat (ptr_addr p mod 8) + k)%nat = Some c) ->
  (n <= length s)%nat.
Proof.
  intros Hs Hnz. destruct (Nat.le_gt_cases n (length s)) as [Hle|Hgt]; [exact Hle|exfalso].
  destruct (Hnz (length s) Hgt) as (c & Hc & E).
  rewrite (str_shape_byte p b reg ws s (length s) Hs (le_n _)) lookup_app_r in E; [|lia].
  rewrite Nat.sub_diag in E. injection E as <-. exact (Hc eq_refl).
Qed.

(** Advancing two strings past n equal nonzero bytes preserves [strcmp_res] and steps both [str_shape]s. *)
Lemma strcmp_advance n p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 ->
  (forall k : nat, (k < n)%nat ->
     exists c, c <> 0 /\ wbytes ws1 !! (Z.to_nat (ptr_addr p1 mod 8) + k)%nat = Some c /\
                         wbytes ws2 !! (Z.to_nat (ptr_addr p2 mod 8) + k)%nat = Some c) ->
  let j1 := Z.to_nat ((ptr_addr p1 mod 8 + Z.of_nat n) / 8) in
  let j2 := Z.to_nat ((ptr_addr p2 mod 8 + Z.of_nat n) / 8) in
  (n <= length s1)%nat /\ (n <= length s2)%nat /\ (j1 <= length ws1)%nat /\ (j2 <= length ws2)%nat /\
  strcmp_res s1 s2 = strcmp_res (drop n s1) (drop n s2) /\
  str_shape (ptr_add p1 (Z.of_nat n)) b1 reg1 (drop j1 ws1) (drop n s1) /\
  wstart (ptr_add p1 (Z.of_nat n)) - b1 = wstart p1 - b1 + 8 * Z.of_nat j1 /\
  str_shape (ptr_add p2 (Z.of_nat n)) b2 reg2 (drop j2 ws2) (drop n s2) /\
  wstart (ptr_add p2 (Z.of_nat n)) - b2 = wstart p2 - b2 + 8 * Z.of_nat j2.
Proof.
  intros Hs1 Hs2 Hnz j1 j2.
  assert (Hl1 : (n <= length s1)%nat) by
    (apply (str_shape_nonzero_len n p1 b1 reg1 ws1 s1 Hs1); intros k Hk; destruct (Hnz k Hk) as (c & ? & ? & _); eauto).
  assert (Hl2 : (n <= length s2)%nat) by
    (apply (str_shape_nonzero_len n p2 b2 reg2 ws2 s2 Hs2); intros k Hk; destruct (Hnz k Hk) as (c & ? & _ & ?); eauto).
  assert (Htk : take n s1 = take n s2).
  { apply list_eq. intros k. destruct (Nat.lt_ge_cases k n) as [Hk|Hk]; [|by rewrite !lookup_take_ge].
    rewrite !lookup_take_lt; [|exact Hk|exact Hk].
    rewrite -(lookup_app_l s1 [0]); [|lia]. rewrite -(lookup_app_l s2 [0]); [|lia].
    rewrite -(str_shape_byte p1 b1 reg1 ws1 s1 k Hs1 ltac:(lia));
      rewrite -(str_shape_byte p2 b2 reg2 ws2 s2 k Hs2 ltac:(lia)).
    destruct (Hnz k Hk) as (c & _ & -> & ->). reflexivity. }
  assert (Hres : strcmp_res s1 s2 = strcmp_res (drop n s1) (drop n s2)) by
    (rewrite -{1}(take_drop n s1); rewrite -{1}(take_drop n s2); rewrite Htk; apply strcmp_res_app).
  pose proof Hs1 as Hs1'. rewrite -(take_drop n s1) in Hs1'.
  destruct (str_shape_suffix p1 b1 reg1 ws1 (take n s1) (drop n s1) Hs1') as [Hsh1 Ho1].
  rewrite (length_take_le _ _ Hl1) in Hsh1, Ho1. fold j1 in Hsh1, Ho1.
  pose proof Hs2 as Hs2'. rewrite -(take_drop n s2) in Hs2'.
  destruct (str_shape_suffix p2 b2 reg2 ws2 (take n s2) (drop n s2) Hs2') as [Hsh2 Ho2].
  rewrite (length_take_le _ _ Hl2) in Hsh2, Ho2. fold j2 in Hsh2, Ho2.
  assert (Hj1 : (j1 <= length ws1)%nat) by
    (apply Nat2Z.inj_le; unfold j1; pose proof (Z.mod_pos_bound (ptr_addr p1) 8 ltac:(lia));
     rewrite Z2Nat.id; [rewrite (ss_len _ _ _ _ _ Hs1); apply Z.div_le_mono; lia | apply Z.div_pos; lia]).
  assert (Hj2 : (j2 <= length ws2)%nat) by
    (apply Nat2Z.inj_le; unfold j2; pose proof (Z.mod_pos_bound (ptr_addr p2) 8 ltac:(lia));
     rewrite Z2Nat.id; [rewrite (ss_len _ _ _ _ _ Hs2); apply Z.div_le_mono; lia | apply Z.div_pos; lia]).
  auto 10.
Qed.

(** Advancing an 8-aligned string and a second string past 8 equal nonzero bytes. *)
Lemma word_eq_advance p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 u0 ws2 s2 :
  str_shape p1 b1 reg1 (w1 :: ws1) s1 -> ptr_addr p1 mod 8 = 0 ->
  str_shape p2 b2 reg2 (u0 :: ws2) s2 -> loop_mask w1 = 0 ->
  (forall k : nat, (k < 8)%nat ->
     wbytes (u0 :: ws2) !! (Z.to_nat (ptr_addr p2 mod 8) + k)%nat = Some (byte_of w1 (Z.of_nat k))) ->
  (1 <= length (w1 :: ws1))%nat /\ (1 <= length (u0 :: ws2))%nat /\
  strcmp_res s1 s2 = strcmp_res (drop 8 s1) (drop 8 s2) /\
  str_shape (ptr_add p1 8) b1 reg1 ws1 (drop 8 s1) /\
  wstart (ptr_add p1 8) - b1 = wstart p1 - b1 + 8 * Z.of_nat 1 /\
  str_shape (ptr_add p2 8) b2 reg2 ws2 (drop 8 s2) /\
  wstart (ptr_add p2 8) - b2 = wstart p2 - b2 + 8 * Z.of_nat 1 /\
  ptr_addr (ptr_add p1 8) mod 8 = 0 /\ ptr_addr (ptr_add p2 8) mod 8 = ptr_addr p2 mod 8.
Proof.
  intros Hs1 Ha1 Hs2 Hm0 Hw2. pose proof (Z.mod_pos_bound (ptr_addr p2) 8 ltac:(lia)).
  assert (Hadv : forall k : nat, (k < 8)%nat ->
    exists c, c <> 0 /\ wbytes (w1 :: ws1) !! (Z.to_nat (ptr_addr p1 mod 8) + k)%nat = Some c /\
                        wbytes (u0 :: ws2) !! (Z.to_nat (ptr_addr p2 mod 8) + k)%nat = Some c).
  { intros k Hk. rewrite Ha1. cbn [Z.to_nat Nat.add].
    exists (byte_of w1 (Z.of_nat k)). split; [apply (proj1 (loop_mask_eq_0 w1) Hm0); lia|].
    split; [exact (wbytes_head w1 ws1 k Hk) | exact (Hw2 k Hk)]. }
  destruct (strcmp_advance 8 p1 b1 reg1 (w1 :: ws1) s1 p2 b2 reg2 (u0 :: ws2) s2 Hs1 Hs2 Hadv)
    as (_ & _ & Hj1 & Hj2 & Hres & Hsh1 & Ho1 & Hsh2 & Ho2).
  rewrite Ha1 in Hj1, Hsh1, Ho1.
  assert (Ej2 : Z.to_nat ((ptr_addr p2 mod 8 + Z.of_nat 8) / 8) = 1%nat) by
    (change (Z.of_nat 8) with 8; replace ((ptr_addr p2 mod 8 + 8) / 8) with 1 by (Z.div_mod_to_equations; lia); reflexivity).
  rewrite Ej2 in Hj2, Hsh2, Ho2. cbn [Z.of_nat Z.add Z.div Z.to_nat drop ptr_addr ptr_add] in *.
  replace (ptr_addr p1 + 8) with (ptr_addr p1 + 1 * 8) by lia.
  replace (ptr_addr p2 + 8) with (ptr_addr p2 + 1 * 8) by lia. rewrite !Z_mod_plus_full Ha1. auto 10.
Qed.

(** Advancing two strings past 1 equal nonzero head byte. *)
Lemma byte_eq_advance p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> hd 0 s1 <> 0 -> hd 0 s1 = hd 0 s2 ->
  let j1 := Z.to_nat ((ptr_addr p1 mod 8 + 1) / 8) in let j2 := Z.to_nat ((ptr_addr p2 mod 8 + 1) / 8) in
  (j1 <= length ws1)%nat /\ (j2 <= length ws2)%nat /\ strcmp_res s1 s2 = strcmp_res (drop 1 s1) (drop 1 s2) /\
  str_shape (ptr_add p1 1) b1 reg1 (drop j1 ws1) (drop 1 s1) /\
  wstart (ptr_add p1 1) - b1 = wstart p1 - b1 + 8 * Z.of_nat j1 /\
  str_shape (ptr_add p2 1) b2 reg2 (drop j2 ws2) (drop 1 s2) /\
  wstart (ptr_add p2 1) - b2 = wstart p2 - b2 + 8 * Z.of_nat j2.
Proof.
  intros Hs1 Hs2 Hnz Heq.
  assert (Hadv : forall k : nat, (k < 1)%nat ->
    exists c, c <> 0 /\ wbytes ws1 !! (Z.to_nat (ptr_addr p1 mod 8) + k)%nat = Some c /\
                        wbytes ws2 !! (Z.to_nat (ptr_addr p2 mod 8) + k)%nat = Some c).
  { intros k Hk. assert (k = 0%nat) as -> by lia. exists (hd 0 s1). split; [exact Hnz|].
    rewrite (str_shape_byte p1 b1 reg1 ws1 s1 0 Hs1 ltac:(lia)) (str_shape_byte p2 b2 reg2 ws2 s2 0 Hs2 ltac:(lia)).
    destruct (str_shape_hd_range p1 b1 reg1 ws1 s1 Hs1) as [_ ->].
    destruct (str_shape_hd_range p2 b2 reg2 ws2 s2 Hs2) as [_ ->]. rewrite Heq. auto. }
  destruct (strcmp_advance 1 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 Hs1 Hs2 Hadv)
    as (_ & _ & Hj1 & Hj2 & Hres & Hsh1 & Ho1 & Hsh2 & Ho2).
  change (Z.of_nat 1) with 1 in *. auto 10.
Qed.

(** Distinct 64-bit words differ at some byte below 8. *)
Lemma word_neq_diff_byte x y :
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  exists k : nat, (k < 8)%nat /\ byte_of x (Z.of_nat k) <> byte_of y (Z.of_nat k).
Proof.
  intros Hx Hy Hne.
  destruct (Z.eq_dec (byte_of x 0) (byte_of y 0)); [|exists 0%nat; split; [lia | assumption]];
  destruct (Z.eq_dec (byte_of x 1) (byte_of y 1)); [|exists 1%nat; split; [lia | assumption]];
  destruct (Z.eq_dec (byte_of x 2) (byte_of y 2)); [|exists 2%nat; split; [lia | assumption]];
  destruct (Z.eq_dec (byte_of x 3) (byte_of y 3)); [|exists 3%nat; split; [lia | assumption]].
  destruct (Z.eq_dec (byte_of x 4) (byte_of y 4)); [|exists 4%nat; split; [lia | assumption]];
  destruct (Z.eq_dec (byte_of x 5) (byte_of y 5)); [|exists 5%nat; split; [lia | assumption]];
  destruct (Z.eq_dec (byte_of x 6) (byte_of y 6)); [|exists 6%nat; split; [lia | assumption]];
  destruct (Z.eq_dec (byte_of x 7) (byte_of y 7)); [|exists 7%nat; split; [lia | assumption]].
  exfalso. apply Hne. rewrite -(of_bytes_byte_of x Hx); rewrite -(of_bytes_byte_of y Hy). cbn [map idx8]. congruence.
Qed.

(** When [loop_mask] x is nonzero, x has a zero byte below 8. *)
Lemma loop_mask_nz_byte x : loop_mask x <> 0 -> exists i : nat, (i < 8)%nat /\ byte_of x (Z.of_nat i) = 0.
Proof.
  intros Hm.
  destruct (Z.eq_dec (byte_of x 0) 0); [exists 0%nat; split; [lia | assumption]|];
  destruct (Z.eq_dec (byte_of x 1) 0); [exists 1%nat; split; [lia | assumption]|];
  destruct (Z.eq_dec (byte_of x 2) 0); [exists 2%nat; split; [lia | assumption]|];
  destruct (Z.eq_dec (byte_of x 3) 0); [exists 3%nat; split; [lia | assumption]|].
  destruct (Z.eq_dec (byte_of x 4) 0); [exists 4%nat; split; [lia | assumption]|];
  destruct (Z.eq_dec (byte_of x 5) 0); [exists 5%nat; split; [lia | assumption]|];
  destruct (Z.eq_dec (byte_of x 6) 0); [exists 6%nat; split; [lia | assumption]|];
  destruct (Z.eq_dec (byte_of x 7) 0); [exists 7%nat; split; [lia | assumption]|].
  exfalso. apply Hm, loop_mask_eq_0. intros i Hi. byte_cases i; assumption.
Qed.

(** First mismatch or NUL byte j < 8 in [cmp_mask] x y gives [strcmp_res] s1 s2. *)
Lemma word_mismatch_strcmp p1 b1 reg1 x ws1 s1 p2 b2 reg2 ws2 s2 y :
  0 <= y < 2 ^ 64 -> str_shape p1 b1 reg1 (x :: ws1) s1 -> ptr_addr p1 mod 8 = 0 -> str_shape p2 b2 reg2 ws2 s2 ->
  (forall i : nat, (i <= length s2)%nat -> (i < 8)%nat -> (s2 ++ [0]) !! i = Some (byte_of y (Z.of_nat i))) ->
  (x <> y \/ (length s2 < 8)%nat \/ loop_mask x <> 0) ->
  exists j : nat, (j < 8)%nat /\ byte_of (cmp_mask x y) (Z.of_nat j) = 128 /\
    (forall i, 0 <= i < Z.of_nat j -> byte_of (cmp_mask x y) i = 0) /\
    (byte_of x (Z.of_nat j) - byte_of y (Z.of_nat j)) mod 2 ^ 32 = strcmp_res s1 s2.
Proof.
  intros Hy_rng Hs1 Ha1 Hs2 Hy Hdiff.
  pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hx_rng.
  set (P := fun i : Z => (byte_of x i =? 0) || negb (byte_of x i =? byte_of y i)).
  assert (Hex : exists k : nat, (k < 8)%nat /\ P (Z.of_nat k) = true).
  { destruct Hdiff as [Hne|[Hlt8|Hm]].
    - destruct (word_neq_diff_byte x y Hx_rng Hy_rng Hne) as (k & Hk & Hne_k).
      exists k. split; [exact Hk|]. unfold P. apply orb_true_iff. right. by apply negb_true_iff, Z.eqb_neq.
    - exists (length s2). split; [exact Hlt8|]. unfold P.
      pose proof (Hy (length s2) (le_n _) Hlt8) as E.
      rewrite lookup_app_r in E; [|lia]. rewrite Nat.sub_diag in E. injection E as E.
      rewrite -E. destruct (byte_of x (Z.of_nat (length s2)) =? 0); reflexivity.
    - destruct (loop_mask_nz_byte x Hm) as (k & Hk & Hz). exists k. split; [exact Hk|]. unfold P. by rewrite Hz. }
  destruct Hex as (k & Hk8 & HPk). destruct (find_first_nat P k HPk) as (j & Hjk & HPj & Hlow).
  assert (Hj8 : (j < 8)%nat) by lia.
  assert (Hprev : forall u : nat, (u < j)%nat ->
    byte_of x (Z.of_nat u) <> 0 /\ byte_of x (Z.of_nat u) = byte_of y (Z.of_nat u)).
  { intros u Hu. pose proof (Hlow (Z.of_nat u) ltac:(lia)) as H0.
    apply orb_false_iff in H0 as [H1 H2]. apply Z.eqb_neq in H1. apply negb_false_iff, Z.eqb_eq in H2. auto. }
  assert (Hle1 : (j <= length s1)%nat).
  { destruct (Nat.le_gt_cases j (length s1)) as [Hle|Hgt]; [exact Hle|exfalso].
    pose proof (str_shape_aligned_byte p1 b1 reg1 x ws1 s1 (length s1) Hs1 Ha1 (le_n _) ltac:(lia)) as E.
    rewrite lookup_app_r in E; [|lia]. rewrite Nat.sub_diag in E. injection E as E.
    exact (proj1 (Hprev (length s1) Hgt) (symmetry E)). }
  assert (Hle2 : (j <= length s2)%nat).
  { destruct (Nat.le_gt_cases j (length s2)) as [Hle|Hgt]; [exact Hle|exfalso].
    pose proof (Hy (length s2) (le_n _) ltac:(lia)) as E.
    rewrite lookup_app_r in E; [|lia]. rewrite Nat.sub_diag in E. injection E as E.
    destruct (Hprev (length s2) Hgt) as [Hnz Heq]. lia. }
  exists j. split; [exact Hj8|]. split; [|split].
  - rewrite cmp_mask_byte; [|lia]. unfold P in HPj. by rewrite HPj.
  - intros i Hi. rewrite cmp_mask_byte; [|lia]. pose proof (Hlow i Hi) as H0. unfold P in H0. by rewrite H0.
  - symmetry. apply (strcmp_res_at s1 s2 j (byte_of x (Z.of_nat j)) (byte_of y (Z.of_nat j))
                       (ss_chars _ _ _ _ _ Hs1) (ss_chars _ _ _ _ _ Hs2)).
    + intros u Hu. rewrite (str_shape_aligned_byte p1 b1 reg1 x ws1 s1 u Hs1 Ha1 ltac:(lia) ltac:(lia)).
      rewrite (Hy u ltac:(lia) ltac:(lia)). f_equal. exact (proj2 (Hprev u Hu)).
    + exact (str_shape_aligned_byte p1 b1 reg1 x ws1 s1 j Hs1 Ha1 Hle1 Hj8).
    + exact (Hy j Hle2 Hj8).
    + unfold P in HPj. apply orb_true_iff in HPj as [H1|H2]; [left; by apply Z.eqb_eq | right; by apply negb_true_iff, Z.eqb_neq in H2].
Qed.

(** Equal words with a zero byte give [strcmp_res] s1 s2 = 0. *)
Lemma word_eq_zero_strcmp p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 ws2 s2 :
  str_shape p1 b1 reg1 (w1 :: ws1) s1 -> ptr_addr p1 mod 8 = 0 -> str_shape p2 b2 reg2 ws2 s2 ->
  (forall i : nat, (i <= length s2)%nat -> (i < 8)%nat -> (s2 ++ [0]) !! i = Some (byte_of w1 (Z.of_nat i))) ->
  loop_mask w1 <> 0 -> strcmp_res s1 s2 = 0.
Proof.
  intros Hs1 Ha1 Hs2 Hy Hm. pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hw1.
  destruct (word_mismatch_strcmp p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 ws2 s2 w1 Hw1 Hs1 Ha1 Hs2 Hy (or_intror (or_intror Hm)))
    as (j & _ & _ & _ & <-).
  by rewrite Z.sub_diag.
Qed.

(** A zero byte at i + k < 8 in the first word u of s2 bounds length s2. *)
Lemma unaligned_short_str p2 b2 reg2 u ws2 s2 (i : nat) :
  str_shape p2 b2 reg2 (u :: ws2) s2 -> (Z.to_nat (ptr_addr p2 mod 8) + i < 8)%nat ->
  byte_of u (Z.of_nat i + ptr_addr p2 mod 8) = 0 ->
  (length s2 < 8 - Z.to_nat (ptr_addr p2 mod 8))%nat /\
  forall j : nat, (j <= length s2)%nat -> (s2 ++ [0]) !! j = Some (byte_of u (Z.of_nat j + ptr_addr p2 mod 8)).
Proof.
  intros Hs2 Hi Hz. pose proof (Z.mod_pos_bound (ptr_addr p2) 8 ltac:(lia)) as Hk.
  set (k := ptr_addr p2 mod 8) in *.
  assert (Hbyte : forall j : nat, (j <= length s2)%nat -> (Z.to_nat k + j < 8)%nat ->
    (s2 ++ [0]) !! j = Some (byte_of u (Z.of_nat j + k))).
  { intros j Hj Hj8. rewrite -(str_shape_byte p2 b2 reg2 (u :: ws2) s2 j Hs2 Hj).
    rewrite wbytes_head; [|exact Hj8]. do 2 f_equal. lia. }
  assert (Hlt : (length s2 < 8 - Z.to_nat k)%nat).
  { destruct (Nat.le_gt_cases (length s2) i) as [Hle|Hgt]; [lia|exfalso].
    pose proof (Hbyte i ltac:(lia) Hi) as E. rewrite Hz in E. rewrite lookup_app_l in E; [|exact Hgt].
    pose proof (Forall_lookup_1 _ _ _ _ (ss_chars _ _ _ _ _ Hs2) E) as Hc. cbn in Hc. lia. }
  split; [exact Hlt|]. intros j Hj. apply (Hbyte j Hj). lia.
Qed.

(** If the 8 - k bytes of u0 from k are nonzero, then (u0 :: ws2) has at least one more word. *)
Lemma unaligned_has_next_word p2 b2 reg2 u0 ws2 s2 :
  str_shape p2 b2 reg2 (u0 :: ws2) s2 ->
  (forall i, 0 <= i < 8 - ptr_addr p2 mod 8 -> byte_of u0 (i + ptr_addr p2 mod 8) <> 0) -> ws2 <> [].
Proof.
  intros Hs2 Hnz. pose proof (Z.mod_pos_bound (ptr_addr p2) 8 ltac:(lia)) as Hk.
  pose proof (ss_len _ _ _ _ _ Hs2) as Hl. set (k := ptr_addr p2 mod 8) in *.
  assert (Hlen : (8 - Z.to_nat k <= length s2)%nat).
  { apply (str_shape_nonzero_len (8 - Z.to_nat k) p2 b2 reg2 (u0 :: ws2) s2 Hs2).
    intros j Hj. exists (byte_of u0 (Z.of_nat j + k)). split; [apply Hnz; lia|].
    rewrite wbytes_head; [|lia]. do 2 f_equal. lia. }
  intros ->. cbn [length] in Hl.
  pose proof (Z.div_le_mono 16 (k + Z.of_nat (length s2) + 8) 8 ltac:(lia) ltac:(lia)) as Hd.
  change (16 / 8) with 2 in Hd. lia.
Qed.

(** Nonzero [loop_mask] of `merge_words u0 all64 k` means s2 ends in u0. *)
Lemma head_pad_zero_str p2 b2 reg2 u0 ws2 s2 :
  str_shape p2 b2 reg2 (u0 :: ws2) s2 -> 1 <= ptr_addr p2 mod 8 < 8 ->
  loop_mask (merge_words u0 all64 (ptr_addr p2 mod 8)) <> 0 -> (length s2 < 8)%nat /\
  forall j : nat, (j <= length s2)%nat -> (j < 8)%nat ->
    (s2 ++ [0]) !! j = Some (byte_of (merge_words u0 all64 (ptr_addr p2 mod 8)) (Z.of_nat j)).
Proof.
  intros Hs2 Hk Hm. pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs2))) as Hu0.
  assert (Hall : 0 <= all64 < 2 ^ 64) by (vm_compute; split; congruence).
  set (k := ptr_addr p2 mod 8) in *. destruct (loop_mask_nz_byte _ Hm) as (i & Hi8 & Hz).
  rewrite (byte_of_merge_words u0 all64 k (Z.of_nat i) Hu0 Hall Hk ltac:(lia)) in Hz.
  destruct (Z.of_nat i <? 8 - k) eqn:E;
    [|apply Z.ltb_ge in E; rewrite byte_all64 in Hz; [discriminate | lia]].
  apply Z.ltb_lt in E. destruct (unaligned_short_str p2 b2 reg2 u0 ws2 s2 i Hs2 ltac:(lia) Hz) as [Hlt Hby].
  split; [lia|]. intros j Hj Hj8. rewrite (Hby j Hj) (byte_of_merge_words u0 all64 k (Z.of_nat j) Hu0 Hall Hk ltac:(lia)).
  replace (Z.of_nat j <? 8 - k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** When [merge_words] u0 u1 k has no zero byte but u1 has a zero byte, `drop 8 s2` ends in `u1 >> 8k`. *)
Lemma unaligned_tail_zero_str p2 b2 reg2 u0 u1 ws2 s2 :
  0 <= u0 < 2 ^ 64 -> str_shape (ptr_add p2 8) b2 reg2 (u1 :: ws2) (drop 8 s2) ->
  1 <= ptr_addr p2 mod 8 < 8 -> loop_mask (merge_words u0 u1 (ptr_addr p2 mod 8)) = 0 ->
  loop_mask u1 <> 0 -> (length (drop 8 s2) < 8)%nat /\
  forall j : nat, (j <= length (drop 8 s2))%nat -> (j < 8)%nat ->
    (drop 8 s2 ++ [0]) !! j = Some (byte_of (u1 / 2 ^ (8 * (ptr_addr p2 mod 8))) (Z.of_nat j)).
Proof.
  intros Hu0 Hs2' Hk Hm0 Hm1. pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs2'))) as Hu1.
  assert (Hk' : ptr_addr (ptr_add p2 8) mod 8 = ptr_addr p2 mod 8) by
    (cbn [ptr_addr ptr_add]; replace (ptr_addr p2 + 8) with (ptr_addr p2 + 1 * 8) by lia; apply Z_mod_plus_full).
  remember (ptr_addr p2 mod 8) as k eqn:Ek. pose proof (Z2Nat.id k ltac:(lia)).
  destruct (loop_mask_nz_byte _ Hm1) as (m & Hm8 & Hz).
  assert (Hge : k <= Z.of_nat m).
  { destruct (Z.le_gt_cases k (Z.of_nat m)) as [Hle|Hgt]; [exact Hle|exfalso].
    pose proof (proj1 (loop_mask_eq_0 _) Hm0 (Z.of_nat m + (8 - k)) ltac:(lia)) as Hnz.
    rewrite byte_of_merge_words in Hnz; [|exact Hu0|exact Hu1|exact Hk|lia].
    replace (Z.of_nat m + (8 - k) <? 8 - k) with false in Hnz by (symmetry; apply Z.ltb_ge; lia).
    replace (Z.of_nat m + (8 - k) - (8 - k)) with (Z.of_nat m) in Hnz by lia. exact (Hnz Hz). }
  assert (Hz' : byte_of u1 (Z.of_nat (m - Z.to_nat k) + ptr_addr (ptr_add p2 8) mod 8) = 0) by
    (rewrite Hk'; replace (Z.of_nat (m - Z.to_nat k) + k) with (Z.of_nat m) by lia; exact Hz).
  destruct (unaligned_short_str (ptr_add p2 8) b2 reg2 u1 ws2 (drop 8 s2) (m - Z.to_nat k)
              Hs2' ltac:(rewrite Hk'; lia) Hz') as [Hlt Hby].
  rewrite Hk' in Hlt, Hby. split; [lia|]. intros j Hj Hj8. rewrite (Hby j Hj) byte_of_div; [reflexivity | lia | lia].
Qed.

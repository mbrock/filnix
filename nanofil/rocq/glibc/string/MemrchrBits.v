(** The bit and byte facts glibc's own `__memrchr` (MemrchrCode.v's
    [glibc_memrchr]) rests on, for MemrchrLoop.v and MemrchrLogic.v.

    glibc's memrchr reads whole words from the one that holds the last
    of its n bytes down to the one that holds the first. In each word it
    marks the bytes equal to c's low byte with string-fza.h's
    `find_eq_all` (StrlenBits.v's [first_mask] of the word xor'd with
    MemchrLast.v's [rep] c), or tests for one with `has_eq`
    ([loop_mask]); in the last word it keeps only the bytes below the
    end ([low_mask]); and it takes the index of the highest marked byte
    from the count of leading zero bits ([head], [head_last]).

    The answer is StrrchrLogic.v's [last_byte] of the n bytes, which
    [last_hit] characterizes: the byte at its index is c, and no later
    one is ([last_byte_hit], [last_hit_unique]). *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Memory.
From Glibc Require Import StrlenBits StrlenLogic StrcmpBits StrrchrLogic MemchrLast.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The last byte c *)

(** r is the index of the last byte c of bs, or none is c. *)
Definition last_hit (bs : list Z) (c : Z) (r : option nat) : Prop :=
  match r with
  | Some t => bs !! t = Some c /\ forall u, (t < u)%nat -> bs !! u <> Some c
  | None => forall u, bs !! u <> Some c
  end.

(** [last_from] from i after acc is the last byte c of bs moved up by
    i, or acc when bs has none. *)
Lemma last_from_shift c i bs acc :
  last_from c i bs acc = match last_byte c bs with Some t => Some (i + t)%nat | None => acc end.
Proof.
  unfold last_byte. revert i acc. induction bs as [|x bs IH]; intros i acc; [reflexivity|].
  cbn [last_from]. rewrite (IH (S i)) (IH 1%nat).
  destruct (last_from c 0 bs None) as [t|]; [f_equal; lia|].
  destruct (x =? c)%Z; [f_equal; lia | reflexivity].
Qed.

(** The last byte c of x :: bs: bs's, one up, or x when c. *)
Lemma last_byte_cons c x bs :
  last_byte c (x :: bs) = match last_byte c bs with Some t => Some (S t) | None => if (x =? c)%Z then Some 0%nat else None end.
Proof. unfold last_byte at 1. cbn [last_from]. rewrite last_from_shift. reflexivity. Qed.

(** [last_byte] is the last byte c. *)
Lemma last_byte_hit c bs : last_hit bs c (last_byte c bs).
Proof.
  induction bs as [|x bs IH]; [intros u; rewrite lookup_nil; discriminate|].
  rewrite last_byte_cons. destruct (last_byte c bs) as [t|]; cbn in IH |- *.
  - destruct IH as [Ht Hu]. split; [exact Ht|]. intros [|u] Hlt; [lia|]. apply Hu. lia.
  - destruct (Z.eqb_spec x c) as [->|Hne]; cbn.
    + split; [reflexivity|]. intros [|u] Hlt; [lia|]. apply IH.
    + intros [|u]; [cbn; intros [= E]; exact (Hne E) | apply IH].
Qed.

(** One list has one last byte c. *)
Lemma last_hit_unique bs c r1 r2 : last_hit bs c r1 -> last_hit bs c r2 -> r1 = r2.
Proof.
  destruct r1 as [t1|], r2 as [t2|]; cbn; intros H1 H2.
  - destruct H1 as [E1 U1], H2 as [E2 U2]. f_equal.
    destruct (Nat.lt_total t1 t2) as [Hl|[Hl|Hl]]; [exfalso; exact (U1 _ Hl E2) | exact Hl | exfalso; exact (U2 _ Hl E1)].
  - exfalso. exact (H2 t1 (proj1 H1)).
  - exfalso. exact (H1 t2 (proj1 H2)).
  - reflexivity.
Qed.

(** Byte u of the n bytes from k of bs, n + k at most bs's length. *)
Lemma window_lookup (bs : list Z) k n u : (k + n <= length bs)%nat ->
  take n (drop k bs) !! u = if (u <? n)%nat then bs !! (k + u)%nat else None.
Proof.
  intros H. destruct (Nat.ltb_spec u n) as [Hl|Hl].
  - rewrite lookup_take_lt; [|exact Hl]. apply lookup_drop.
  - apply lookup_take_ge. exact Hl.
Qed.

(** ## The highest marked byte *)

(** glibc's `index_last` (string-fzi.h) as nanofil inlines it on the
    mask r: the count of r's leading zero bits, 64 less the population
    count of r with every bit below its highest set, every read
    wrapped. *)
Definition head (r : Z) : Z :=
  let x := r mod 2 ^ 64 / 2 ^ ((1 mod 2 ^ 32) mod 64) in
  let x0 := Z.lor (r mod 2 ^ 64) (x mod 2 ^ 64) in
  let x1 := x0 mod 2 ^ 64 / 2 ^ ((2 mod 2 ^ 32) mod 64) in
  let x2 := Z.lor (x0 mod 2 ^ 64) (x1 mod 2 ^ 64) in
  let x3 := x2 mod 2 ^ 64 / 2 ^ ((4 mod 2 ^ 32) mod 64) in
  let x4 := Z.lor (x2 mod 2 ^ 64) (x3 mod 2 ^ 64) in
  let x5 := x4 mod 2 ^ 64 / 2 ^ ((8 mod 2 ^ 32) mod 64) in
  let x6 := Z.lor (x4 mod 2 ^ 64) (x5 mod 2 ^ 64) in
  let x7 := x6 mod 2 ^ 64 / 2 ^ ((16 mod 2 ^ 32) mod 64) in
  let x8 := Z.lor (x6 mod 2 ^ 64) (x7 mod 2 ^ 64) in
  let x9 := x8 mod 2 ^ 64 / 2 ^ ((32 mod 2 ^ 32) mod 64) in
  let x10 := Z.lor (x8 mod 2 ^ 64) (x9 mod 2 ^ 64) in
  let x11 := x10 mod 2 ^ 64 / 2 ^ ((1 mod 2 ^ 32) mod 64) in
  let x12 := Z.land (x11 mod 2 ^ 64) (6148914691236517205 mod 2 ^ 64) in
  let x13 := (x10 mod 2 ^ 64 - x12 mod 2 ^ 64) mod 2 ^ 64 in
  let x14 := Z.land (x13 mod 2 ^ 64) (3689348814741910323 mod 2 ^ 64) in
  let x15 := x13 mod 2 ^ 64 / 2 ^ ((2 mod 2 ^ 32) mod 64) in
  let x16 := Z.land (x15 mod 2 ^ 64) (3689348814741910323 mod 2 ^ 64) in
  let x17 := (x14 mod 2 ^ 64 + x16 mod 2 ^ 64) mod 2 ^ 64 in
  let x18 := x17 mod 2 ^ 64 / 2 ^ ((4 mod 2 ^ 32) mod 64) in
  let x19 := (x17 mod 2 ^ 64 + x18 mod 2 ^ 64) mod 2 ^ 64 in
  let x20 := Z.land (x19 mod 2 ^ 64) (1085102592571150095 mod 2 ^ 64) in
  let x21 := (x20 mod 2 ^ 64 * (72340172838076673 mod 2 ^ 64)) mod 2 ^ 64 in
  let x22 := x21 mod 2 ^ 64 / 2 ^ ((56 mod 2 ^ 32) mod 64) in
  let x23 := (x22 mod 2 ^ 64 - 64 mod 2 ^ 64) mod 2 ^ 64 in
  - (x23 mod 2 ^ 64) mod 2 ^ 64.

(** The count as the chain of the twenty-five values the IR names: its
    last value is [head] r. *)
Lemma head_chain r x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 :
  x = r mod 2 ^ 64 / 2 ^ ((1 mod 2 ^ 32) mod 64) -> x0 = Z.lor (r mod 2 ^ 64) (x mod 2 ^ 64) ->
  x1 = x0 mod 2 ^ 64 / 2 ^ ((2 mod 2 ^ 32) mod 64) -> x2 = Z.lor (x0 mod 2 ^ 64) (x1 mod 2 ^ 64) ->
  x3 = x2 mod 2 ^ 64 / 2 ^ ((4 mod 2 ^ 32) mod 64) -> x4 = Z.lor (x2 mod 2 ^ 64) (x3 mod 2 ^ 64) ->
  x5 = x4 mod 2 ^ 64 / 2 ^ ((8 mod 2 ^ 32) mod 64) -> x6 = Z.lor (x4 mod 2 ^ 64) (x5 mod 2 ^ 64) ->
  x7 = x6 mod 2 ^ 64 / 2 ^ ((16 mod 2 ^ 32) mod 64) -> x8 = Z.lor (x6 mod 2 ^ 64) (x7 mod 2 ^ 64) ->
  x9 = x8 mod 2 ^ 64 / 2 ^ ((32 mod 2 ^ 32) mod 64) -> x10 = Z.lor (x8 mod 2 ^ 64) (x9 mod 2 ^ 64) ->
  x11 = x10 mod 2 ^ 64 / 2 ^ ((1 mod 2 ^ 32) mod 64) ->
  x12 = Z.land (x11 mod 2 ^ 64) (6148914691236517205 mod 2 ^ 64) ->
  x13 = (x10 mod 2 ^ 64 - x12 mod 2 ^ 64) mod 2 ^ 64 ->
  x14 = Z.land (x13 mod 2 ^ 64) (3689348814741910323 mod 2 ^ 64) ->
  x15 = x13 mod 2 ^ 64 / 2 ^ ((2 mod 2 ^ 32) mod 64) ->
  x16 = Z.land (x15 mod 2 ^ 64) (3689348814741910323 mod 2 ^ 64) ->
  x17 = (x14 mod 2 ^ 64 + x16 mod 2 ^ 64) mod 2 ^ 64 -> x18 = x17 mod 2 ^ 64 / 2 ^ ((4 mod 2 ^ 32) mod 64) ->
  x19 = (x17 mod 2 ^ 64 + x18 mod 2 ^ 64) mod 2 ^ 64 ->
  x20 = Z.land (x19 mod 2 ^ 64) (1085102592571150095 mod 2 ^ 64) ->
  x21 = (x20 mod 2 ^ 64 * (72340172838076673 mod 2 ^ 64)) mod 2 ^ 64 ->
  x22 = x21 mod 2 ^ 64 / 2 ^ ((56 mod 2 ^ 32) mod 64) -> x23 = (x22 mod 2 ^ 64 - 64 mod 2 ^ 64) mod 2 ^ 64 ->
  x24 = - (x23 mod 2 ^ 64) mod 2 ^ 64 -> x24 = head r.
Proof.
  intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->. unfold head. cbv zeta. reflexivity.
Qed.

(** On a mask in range whose bytes are 0 or 128, with the last 128 at
    byte j: the count of leading zeros is 56 - 8j. Each of the 255
    masks with a last 128 at some byte is computed. *)
Lemma head_last r j : 0 <= r < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> byte_of r i = 0 \/ byte_of r i = 128) ->
  0 <= j < 8 -> byte_of r j = 128 -> (forall i, j < i < 8 -> byte_of r i = 0) ->
  head r = 56 - 8 * j.
Proof.
  intros Hr H01 Hj Hjb Hhigh. rewrite <- (of_bytes_byte_of r Hr). cbn [List.map idx8].
  byte_cases j;
    repeat match goal with
      | |- context [byte_of r ?i] =>
          first [ rewrite (Hhigh i); [|lia] | rewrite Hjb
                | let E := fresh in destruct (H01 i ltac:(lia)) as [E|E]; rewrite E ]
      end;
    vm_compute; reflexivity.
Qed.

(** ## Words and their marks *)

(** An xor of words in range is in range. *)
Lemma lxor_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.lxor a b mod 2 ^ 64 = Z.lxor a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2; [|lia]. rewrite Z.lxor_spec.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
    rewrite (bits64 a n Ha E) (bits64 b n Hb E). reflexivity. }
  rewrite -E. apply Z.mod_pos_bound. lia.
Qed.

(** [rep] c is a word. *)
Lemma rep_range c : 0 <= rep c < 2 ^ 64.
Proof. unfold rep. apply Z.mod_pos_bound. lia. Qed.

(** The marks of the word w for c, [first_mask] of w xor [rep] c, are
    in range. *)
Lemma marks_range w c : 0 <= first_mask (Z.lxor w (rep c)) < 2 ^ 64.
Proof.
  unfold first_mask. apply lxor_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence].
Qed.

(** Byte i of the marks of w for c: 128 if w's byte i is c's low byte,
    else 0. *)
Lemma marks_byte w c i : 0 <= i < 8 ->
  byte_of (first_mask (Z.lxor w (rep c))) i = if byte_of w i =? c mod 256 then 128 else 0.
Proof.
  intros Hi. rewrite first_mask_byte; [|exact Hi].
  destruct (Z.eqb_spec (byte_of (Z.lxor w (rep c)) i) 0) as [E|E];
    destruct (Z.eqb_spec (byte_of w i) (c mod 256)) as [E'|E']; try reflexivity.
  - exfalso. apply E'. apply xor_zero; [exact Hi | exact E].
  - exfalso. apply E. apply xor_zero; [exact Hi | exact E'].
Qed.

(** `has_eq` of the word w in range for c: [loop_mask] of w xor [rep]
    c is 0 just when no byte of w is c's low byte. *)
Lemma has_eq_zero w c : 0 <= w < 2 ^ 64 ->
  loop_mask (Z.lxor w (rep c)) = 0 <-> forall i, 0 <= i < 8 -> byte_of w i <> c mod 256.
Proof.
  intros Hw. rewrite (loop_mask_zero _ (lxor_range _ _ Hw (rep_range c))). split.
  - intros H i Hi E. apply (H i Hi). apply xor_zero; [exact Hi | exact E].
  - intros H i Hi E. apply (H i Hi). apply xor_zero; [exact Hi | exact E].
Qed.

(** Below n, a decidable property holds last at some j, or nowhere. *)
Lemma greatest_below (P : nat -> Prop) (dec : forall i, {P i} + {~ P i}) n :
  (exists j, (j < n)%nat /\ P j /\ forall i, (j < i < n)%nat -> ~ P i) \/ (forall i, (i < n)%nat -> ~ P i).
Proof.
  induction n as [|n IH]; [right; lia|].
  destruct (dec n) as [Hp|Hp]; [left; exists n; split; [lia | split; [exact Hp | lia]]|].
  destruct IH as [(j & Hj & Hpj & Hl) | Hn]; [left; exists j; split; [lia | split; [exact Hpj|]] | right].
  - intros i Hi. destruct (Nat.eq_dec i n) as [->|]; [exact Hp | apply Hl; lia].
  - intros i Hi. destruct (Nat.eq_dec i n) as [->|]; [exact Hp | apply Hn; lia].
Qed.

(** The word w holds c last at byte j, or nowhere. *)
Lemma word_last w c :
  (exists j, 0 <= j < 8 /\ byte_of w j = c /\ forall i, j < i < 8 -> byte_of w i <> c) \/
  (forall i, 0 <= i < 8 -> byte_of w i <> c).
Proof.
  destruct (greatest_below (fun i => byte_of w (Z.of_nat i) = c) (fun i => Z.eq_dec _ _) 8)
    as [(j & Hj & Hp & Hl) | Hn].
  - left. exists (Z.of_nat j). split; [lia|]. split; [exact Hp|]. intros i Hi.
    specialize (Hl (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hl; [exact Hl | lia].
  - right. intros i Hi. specialize (Hn (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hn; [exact Hn | lia].
Qed.

(** The marks of w for c whose last c is at byte j: their count of
    leading zeros is 56 - 8j. *)
Lemma head_marks w c j : 0 <= j < 8 -> byte_of w j = c mod 256 ->
  (forall i, j < i < 8 -> byte_of w i <> c mod 256) -> head (first_mask (Z.lxor w (rep c))) = 56 - 8 * j.
Proof.
  intros Hj Hc Hl. apply head_last; [apply marks_range | | exact Hj | | ].
  - intros i Hi. rewrite marks_byte; [|exact Hi]. destruct (_ =? _); auto.
  - rewrite marks_byte; [|exact Hj]. rewrite Hc Z.eqb_refl. reflexivity.
  - intros i Hi. rewrite marks_byte; [|lia]. destruct (Z.eqb_spec (byte_of w i) (c mod 256)) as [E|E];
      [exfalso; exact (Hl i Hi E) | reflexivity].
Qed.

(** ## The bytes of a window *)

(** No byte of bs from lo to below hi is c. *)
Definition none_in (bs : list Z) (c : Z) (lo hi : nat) : Prop :=
  forall u, (lo <= u < hi)%nat -> bs !! u <> Some c.

(** Byte j of word i of ws, inside ws. *)
Lemma wbytes_at ws (i : nat) j : (i < length ws)%nat -> 0 <= j < 8 ->
  wbytes ws !! (8 * i + Z.to_nat j)%nat = Some (byte_of (wrd ws (Z.of_nat i)) j).
Proof.
  intros Hi Hj. rewrite (bt_word ws (Z.of_nat i) j); [|lia | exact Hj].
  rewrite <- (wbytes_bt ws (8 * Z.of_nat i + j)); [f_equal; lia | lia].
Qed.

(** With the last c of the window from k at v, and none after it, the
    search's answer is v - k. *)
Lemma hit_at (bs : list Z) c k n v : (k + n <= length bs)%nat -> (k <= v < k + n)%nat ->
  bs !! v = Some c -> none_in bs c (S v) (k + n) -> last_hit (take n (drop k bs)) c (Some (v - k)%nat).
Proof.
  intros Hl Hv Hb Hn. cbn. rewrite window_lookup; [|exact Hl].
  replace ((v - k <? n)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (k + (v - k))%nat with v by lia. split; [exact Hb|].
  intros u Hu. rewrite window_lookup; [|exact Hl]. destruct (Nat.ltb_spec u n); [|discriminate].
  apply Hn. lia.
Qed.

(** With no c in the window from k, the search finds none. *)
Lemma hit_none (bs : list Z) c k n : (k + n <= length bs)%nat -> none_in bs c k (k + n) ->
  last_hit (take n (drop k bs)) c None.
Proof.
  intros Hl Hn u. rewrite window_lookup; [|exact Hl]. destruct (Nat.ltb_spec u n); [|discriminate].
  apply Hn. lia.
Qed.

(** No c in word i of ws, nor after it to hi: none from the word on. *)
Lemma none_word ws c (i : nat) hi : (i < length ws)%nat ->
  (forall j, 0 <= j < 8 -> byte_of (wrd ws (Z.of_nat i)) j <> c) -> none_in (wbytes ws) c (8 * S i) hi ->
  none_in (wbytes ws) c (8 * i) hi.
Proof.
  intros Hi Hw Hn u Hu. destruct (Nat.lt_ge_cases u (8 * S i)) as [Hl|Hl]; [|apply Hn; lia].
  replace u with (8 * i + Z.to_nat (Z.of_nat (u - 8 * i)))%nat by lia.
  rewrite wbytes_at; [|exact Hi | lia]. intros [= E]. exact (Hw (Z.of_nat (u - 8 * i)) ltac:(lia) E).
Qed.

(** The last c of word i of ws at byte j, none after it to hi: none
    from just past it. *)
Lemma none_after ws c (i : nat) j hi : (i < length ws)%nat -> 0 <= j < 8 ->
  (forall j', j < j' < 8 -> byte_of (wrd ws (Z.of_nat i)) j' <> c) -> none_in (wbytes ws) c (8 * S i) hi ->
  none_in (wbytes ws) c (S (8 * i + Z.to_nat j)) hi.
Proof.
  intros Hi Hj Hw Hn u Hu. destruct (Nat.lt_ge_cases u (8 * S i)) as [Hl|Hl]; [|apply Hn; lia].
  replace u with (8 * i + Z.to_nat (Z.of_nat (u - 8 * i)))%nat by lia.
  rewrite wbytes_at; [|exact Hi | lia]. intros [= E]. exact (Hw (Z.of_nat (u - 8 * i)) ltac:(lia) E).
Qed.

(** ## The bytes below the end *)

(** glibc's `shift_find_last` (string-fzc.h) as nanofil inlines it on
    the marks m of the last word, e its bytes below the end: m with
    every byte from e up cleared, every read wrapped. *)
Definition keep_low (m e : Z) : Z :=
  Z.land (m mod 2 ^ 64)
    (Z.lxor (((18446744073709551615 mod 2 ^ 64 *
               2 ^ ((((e mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64) mod 2 ^ 32) mod 64)) mod 2 ^ 64)
              mod 2 ^ 64) (-1 mod 2 ^ 64) mod 2 ^ 64).

(** The constant [keep_low] ands with has 255 in each byte below e and
    0 in the others, each of the 49 bytes computed. *)
Lemma keep_low_const e i : 0 < e < 8 -> 0 <= i < 8 ->
  byte_of (Z.lxor (((18446744073709551615 mod 2 ^ 64 *
               2 ^ ((((e mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64) mod 2 ^ 32) mod 64)) mod 2 ^ 64)
              mod 2 ^ 64) (-1 mod 2 ^ 64) mod 2 ^ 64) i = if i <? e then 255 else 0.
Proof.
  intros He Hi. assert (H : e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5 \/ e = 6 \/ e = 7) by lia.
  repeat destruct H as [H|H]; subst e; byte_cases i; vm_compute; reflexivity.
Qed.

(** Byte i of [keep_low] m e: m's below e, else 0. *)
Lemma keep_low_byte m e i : 0 < e < 8 -> 0 <= i < 8 ->
  byte_of (keep_low m e) i = if i <? e then byte_of m i else 0.
Proof.
  intros He Hi. unfold keep_low. rewrite byte_of_land; [|lia]. rewrite byte_of_mod64; [|exact Hi].
  rewrite keep_low_const; [|exact He | exact Hi]. pose proof (byte_of_range m i).
  destruct (i <? e); [|apply Z.land_0_r].
  change 255 with (Z.ones 8). rewrite Z.land_ones; [|lia]. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

(** [keep_low] m e is a word. *)
Lemma keep_low_range m e : 0 <= keep_low m e < 2 ^ 64.
Proof.
  unfold keep_low. apply land_range; apply Z.mod_pos_bound; lia.
Qed.

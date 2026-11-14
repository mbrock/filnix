(** In C, `c: strcmp` compares two NUL-terminated byte strings and
    returns zero when they match, or the difference between the first pair
    of bytes that differ. To run fast, glibc's implementation
    ([StrcmpCode](StrcmpCode.v)) reads aligned 64-bit [[word]] chunks instead
    of stepping one byte at a time. When the second string is unaligned,
    glibc loads two consecutive words and shifts them together with `MERGE`
    to line up the bytes.

    Proving that word-at-a-time code matches the byte-by-byte C contract
    requires bridging 64-bit bitmasks back to individual bytes. This
    module defines the byte-level specification [strcmp_res] and proves
    the arithmetic, bitmask, and [[word]]-window facts needed by the
    `c: strcmp` loop and entry proofs. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Syntax Values Memory Ops.
From Glibc Require Import StrlenBits StrlenLogic WordString.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The answer on byte lists

    Before reasoning about 64-bit words, we need a pure specification of
    what `c: strcmp` returns on two byte lists. This section defines
    [strcmp_res] recursively and introduces [agree_str], [same_upto], and
    [stop_at] so the loop proofs can read the final return value off any
    pair of byte functions that match the strings up to their first
    difference or NUL terminator. *)

(** Given two byte lists s1 and s2 without trailing NULs, [strcmp_res]
    returns 0 if they are equal, or the difference modulo 2^32 between
    the first differing bytes of s1 ++ [0] and s2 ++ [0]. *)
Fixpoint strcmp_res (s1 s2 : list Z) : Z :=
  match s1, s2 with
  | [], [] => 0
  | c1 :: s1', c2 :: s2' => if c1 =? c2 then strcmp_res s1' s2' else (c1 - c2) mod 2 ^ 32
  | [], c2 :: _ => (0 - c2) mod 2 ^ 32
  | c1 :: _, [] => (c1 - 0) mod 2 ^ 32
  end.

(** The difference between two distinct byte values c1 and c2 never wraps
    around to 0 modulo 2^32. *)
Lemma byte_diff_nonzero c1 c2 : 0 <= c1 < 256 -> 0 <= c2 < 256 -> c1 <> c2 -> (c1 - c2) mod 2 ^ 32 <> 0.
Proof. intros H1 H2 Hne E. apply Z.mod_divide in E; [|lia]. destruct E as [k Hk]. nia. Qed.

(** When s1 and s2 contain only nonzero bytes, [strcmp_res] returns 0 if
    and only if the two lists are identical. *)
Lemma strcmp_res_zero s1 s2 :
  Forall (fun c => 0 < c < 256) s1 -> Forall (fun c => 0 < c < 256) s2 -> (strcmp_res s1 s2 = 0 <-> s1 = s2).
Proof.
  revert s2. induction s1 as [|c1 s1 IH]; intros [|c2 s2] H1 H2; cbn [strcmp_res].
  - tauto.
  - apply Forall_cons_1 in H2 as [Hc _]. split; [|discriminate]. intros E.
    exfalso. apply (byte_diff_nonzero 0 c2); lia.
  - apply Forall_cons_1 in H1 as [Hc _]. split; [|discriminate]. intros E.
    exfalso. apply (byte_diff_nonzero c1 0); lia.
  - apply Forall_cons_1 in H1 as [Hc1 H1], H2 as [Hc2 H2]. destruct (Z.eqb_spec c1 c2) as [<-|Hne].
    + rewrite IH; [|exact H1|exact H2]. split; [intros ->; reflexivity | intros E; injection E as E; exact E].
    + split; [intros E; exfalso; exact (byte_diff_nonzero c1 c2 ltac:(lia) ltac:(lia) Hne E)|].
      intros E. injection E as E _. contradiction.
Qed.

(** A function f satisfies [agree_str] for a string s when f j equals
    byte j of s ++ [0] at every index through the NUL terminator. *)
Definition agree_str (f : Z -> Z) (s : list Z) : Prop :=
  forall j, 0 <= j <= Z.of_nat (length s) -> f j = nth (Z.to_nat j) (s ++ [0]) 0.

(** The predicate [same_upto] holds at index c when f1 and f2 agree on
    every byte before c and none of those bytes is zero. *)
Definition same_upto (f1 f2 : Z -> Z) (c : Z) : Prop :=
  forall j, 0 <= j < c -> f1 j = f2 j /\ f1 j <> 0.

(** A comparison reaches [stop_at] at index i when f1 i is zero or f1 i
    differs from f2 i. *)
Definition stop_at (f1 f2 : Z -> Z) (i : Z) : Prop := f1 i = 0 \/ f1 i <> f2 i.

(** Whenever f1 and f2 agree with strings s1 and s2 through their NULs
    and first stop at index i, [strcmp_res] equals their byte difference
    at i modulo 2^32. *)
Lemma strcmp_res_stop s1 s2 f1 f2 i :
  Forall (fun c => c <> 0) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= i -> same_upto f1 f2 i ->
  stop_at f1 f2 i -> strcmp_res s1 s2 = (f1 i - f2 i) mod 2 ^ 32.
Proof.
  revert s2 f1 f2 i. induction s1 as [|c1 s1 IH]; intros s2 f1 f2 i Hn A1 A2 Hi Hs Hst.
  - assert (E1 : f1 0 = 0) by (rewrite A1; cbn; [reflexivity | lia]).
    destruct (Z.eq_dec i 0) as [->|Hne]; [|destruct (Hs 0 ltac:(lia)); contradiction].
    rewrite E1. destruct s2 as [|c2 s2]; cbn [strcmp_res]; rewrite (A2 0); cbn [length]; try lia; reflexivity.
  - apply Forall_cons_1 in Hn as [Hc1 Hn].
    assert (E1 : f1 0 = c1) by (rewrite A1; cbn [length]; [reflexivity | lia]).
    destruct s2 as [|c2 s2].
    + assert (E2 : f2 0 = 0) by (rewrite A2; cbn; [reflexivity | lia]).
      destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite E1 E2; reflexivity|].
      destruct (Hs 0 ltac:(lia)) as [Ha Hb]. congruence.
    + assert (E2 : f2 0 = c2) by (rewrite A2; cbn [length]; [reflexivity | lia]).
      cbn [strcmp_res]. destruct (Z.eq_dec i 0) as [->|Hne].
      * rewrite E1 E2. destruct Hst as [Hz|Hd]; [congruence|].
        replace (c1 =? c2) with false by (symmetry; apply Z.eqb_neq; congruence). reflexivity.
      * destruct (Hs 0 ltac:(lia)) as [Ha _]. replace (c1 =? c2) with true by (symmetry; apply Z.eqb_eq; congruence).
        replace (f1 i - f2 i) with (f1 (i - 1 + 1) - f2 (i - 1 + 1)) by (f_equal; f_equal; lia).
        apply (IH s2 (fun j => f1 (j + 1)) (fun j => f2 (j + 1)) (i - 1) Hn).
        { intros j Hj. rewrite A1; [|cbn [length]; lia]. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
          reflexivity. }
        { intros j Hj. rewrite A2; [|cbn [length]; lia]. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
          reflexivity. }
        { lia. }
        { intros j Hj. apply Hs. lia. }
        { unfold stop_at in *. replace (i - 1 + 1) with i by lia. exact Hst. }
Qed.

(** A byte function that agrees with string s and stays nonzero below c
    cannot extend past the NUL byte, so c is at most the length of s. *)
Lemma nonzero_len f s c : agree_str f s -> (forall j, 0 <= j < c -> f j <> 0) -> c <= Z.of_nat (length s).
Proof.
  intros A H. destruct (Z.le_gt_cases c (Z.of_nat (length s))) as [Hc|Hc]; [exact Hc|].
  exfalso. apply (H (Z.of_nat (length s))); [lia|]. rewrite A; [|lia].
  rewrite Nat2Z.id app_nth2; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

(** When f1 and f2 satisfy [same_upto] through index c, that prefix
    stays within the lengths of both s1 and s2. *)
Lemma same_upto_len f1 f2 s1 s2 c : agree_str f1 s1 -> agree_str f2 s2 -> same_upto f1 f2 c ->
  c <= Z.of_nat (length s1) /\ c <= Z.of_nat (length s2).
Proof.
  intros A1 A2 H. split.
  - apply (nonzero_len f1 s1 c A1). intros j Hj. apply H, Hj.
  - apply (nonzero_len f2 s2 c A2). intros j Hj. destruct (H j Hj). congruence.
Qed.

(** If f1 and f2 agree and stay nonzero before c, and stop at z, then
    there exists a first stopping index i between c and z. *)
Lemma first_stop f1 f2 c z : 0 <= c <= z -> stop_at f1 f2 z -> same_upto f1 f2 c ->
  exists i, c <= i <= z /\ stop_at f1 f2 i /\ same_upto f1 f2 i.
Proof.
  intros Hz Hst Hs.
  assert (H : forall n : nat, same_upto f1 f2 (c + Z.of_nat n) \/
                exists i, c <= i < c + Z.of_nat n /\ stop_at f1 f2 i /\ same_upto f1 f2 i).
  { induction n as [|n [IH|IH]]; [left; rewrite Z.add_0_r; exact Hs| |right].
    - destruct (Z.eq_dec (f1 (c + Z.of_nat n)) 0) as [E|Ne];
        [|destruct (Z.eq_dec (f1 (c + Z.of_nat n)) (f2 (c + Z.of_nat n))) as [E'|Ne']].
      + right. exists (c + Z.of_nat n). split; [lia|]. split; [left; exact E | exact IH].
      + left. intros j Hj. destruct (Z.eq_dec j (c + Z.of_nat n)) as [->|Hne]; [split; assumption|].
        apply IH. lia.
      + right. exists (c + Z.of_nat n). split; [lia|]. split; [right; exact Ne' | exact IH].
    - destruct IH as (i & Hi & H1 & H2). exists i. split; [lia|]. auto. }
  destruct (H (Z.to_nat (z - c) + 1)%nat) as [Hall|(i & Hi & H1 & H2)].
  - exfalso. destruct (Hall z ltac:(lia)) as [E Hn]. destruct Hst; contradiction.
  - exists i. split; [lia|]. auto.
Qed.

(** ## Bytes of a window

    In Fil-C memory, each string lives inside an 8-byte-aligned window
    of 64-bit words rather than a raw byte array. To compare byte
    positions against word loads, we need functions that extract
    individual bytes from a list of 64-bit words and connect those reads
    to the string's NUL-terminated bytes. *)

(** Function [wrd] returns word q from the list ws, or 0 if q lies past
    the end of the list. *)
Definition wrd (ws : list Z) (q : Z) : Z := nth (Z.to_nat q) ws 0.

(** Function [bt] extracts byte i from the 64-bit word list ws in
    little-endian order. *)
Definition bt (ws : list Z) (i : Z) : Z := byte_of (wrd ws (i / 8)) (i mod 8).

(** Byte j of word q in ws equals [bt] at byte index 8 * q + j. *)
Lemma bt_word ws q j : 0 <= q -> 0 <= j < 8 -> byte_of (wrd ws q) j = bt ws (8 * q + j).
Proof.
  intros Hq Hj. unfold bt. replace ((8 * q + j) / 8) with q by (Z.div_mod_to_equations; lia).
  replace ((8 * q + j) mod 8) with j by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

(** Indexing into the flattened window byte list [wbytes] at i returns
    [bt] ws i whenever i lies inside the window. *)
Lemma wbytes_bt ws i : 0 <= i < 8 * Z.of_nat (length ws) -> wbytes ws !! Z.to_nat i = Some (bt ws i).
Proof.
  revert i. induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct (Z.lt_ge_cases i 8) as [H8|H8].
  - rewrite wbytes_head; [|lia]. unfold bt, wrd. rewrite Z.div_small; [|lia]. rewrite Z.mod_small; [|lia].
    rewrite Z2Nat.id; [reflexivity | lia].
  - replace (Z.to_nat i) with (8 + Z.to_nat (i - 8))%nat by lia. rewrite wbytes_tail IH; [|lia].
    unfold bt, wrd. replace (i / 8) with ((i - 8) / 8 + 1) by (Z.div_mod_to_equations; lia).
    replace (i mod 8) with ((i - 8) mod 8) by (Z.div_mod_to_equations; lia).
    replace (Z.to_nat ((i - 8) / 8 + 1)) with (S (Z.to_nat ((i - 8) / 8)))
      by (pose proof (Z.div_pos (i - 8) 8); lia). reflexivity.
Qed.

(** When a string at pointer p satisfies [str_shape], reading [bt] from
    p's offset inside its first word agrees with the string through its
    NUL terminator. *)
Lemma str_bt p b reg ws s : str_shape p b reg ws s -> agree_str (fun j => bt ws (ptr_addr p mod 8 + j)) s.
Proof.
  intros Hs j Hj. pose proof (str_shape_byte p b reg ws s (Z.to_nat j) Hs ltac:(lia)) as E.
  pose proof (ss_len _ _ _ _ _ Hs) as Hl. pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  replace (Z.to_nat (ptr_addr p mod 8) + Z.to_nat j)%nat with (Z.to_nat (ptr_addr p mod 8 + j)) in E by lia.
  rewrite wbytes_bt in E; [|Z.div_mod_to_equations; lia].
  rewrite (nth_lookup_Some (s ++ [0]) (Z.to_nat j) 0 (bt ws (ptr_addr p mod 8 + j))); [reflexivity|].
  rewrite <- E. reflexivity.
Qed.

(** ## The words' masks

    In the fast loop, glibc checks whether a 64-bit word contains any NUL
    byte by computing `has_zero`, which we model as [loop_mask]
    ([StrlenBits](StrlenBits.v)). These helper lemmas establish when
    [loop_mask] is zero or nonzero and show that any two distinct 64-bit
    words must differ in at least one byte. *)

(** The zero-detection mask [loop_mask] of a 64-bit word w is 0 if and
    only if all eight bytes of w are nonzero. *)
Lemma loop_mask_zero w : 0 <= w < 2 ^ 64 -> (loop_mask w = 0 <-> forall j, 0 <= j < 8 -> byte_of w j <> 0).
Proof.
  intros Hw. split.
  - intros E j Hj Hz.
    destruct (first_stop (byte_of w) (byte_of w) 0 j ltac:(lia) (or_introl Hz) ltac:(intros i Hi; lia))
      as (i & Hi & [Hz'|Hd] & Hs); [|contradiction].
    pose proof (loop_mask_at w i ltac:(lia) ltac:(intros k Hk; apply Hs; exact Hk) Hz') as H.
    rewrite E in H. unfold byte_of in H. rewrite Z.div_0_l in H; [discriminate | apply Z.pow_nonzero; lia].
  - intros H. apply zero_word; [apply loop_mask_range|]. intros j Hj. apply (loop_mask_below w 8 j); [lia | | exact Hj].
    intros k Hk. apply H, Hk.
Qed.

(** Every word returned by [wrd] lies in the unsigned 64-bit range
    whenever all elements of ws do. *)
Lemma wrd_range ws q : Forall (fun w => 0 <= w < 2 ^ 64) ws -> 0 <= wrd ws q < 2 ^ 64.
Proof.
  intros H. unfold wrd. destruct (Nat.lt_ge_cases (Z.to_nat q) (length ws)) as [Hq|Hq].
  - rewrite Forall_forall in H. apply H, nth_In, Hq.
  - rewrite nth_overflow; [lia | exact Hq].
Qed.

(** For any decidable predicate P on indices below n, either every index
    satisfies P or some index below n violates it. *)
Lemma idx_dec (P : Z -> Prop) (dec : forall j, {P j} + {~ P j}) (n : nat) :
  (forall j, 0 <= j < Z.of_nat n -> P j) \/ exists j, 0 <= j < Z.of_nat n /\ ~ P j.
Proof.
  induction n as [|n [IH|IH]].
  - left. intros j Hj. lia.
  - destruct (dec (Z.of_nat n)) as [H|H].
    + left. intros j Hj. destruct (Z.eq_dec j (Z.of_nat n)) as [->|Hne]; [exact H | apply IH; lia].
    + right. exists (Z.of_nat n). split; [lia | exact H].
  - right. destruct IH as (j & Hj & H). exists j. split; [lia | exact H].
Qed.

(** Any two distinct 64-bit words x and y differ in at least one byte
    position below 8. *)
Lemma words_differ x y : 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  exists t, 0 <= t < 8 /\ byte_of x t <> byte_of y t.
Proof.
  intros Hx Hy Hne. destruct (idx_dec (fun t => byte_of x t = byte_of y t) (fun t => Z.eq_dec _ _) 8) as [H|H].
  - exfalso. apply Hne. rewrite -(of_bytes_byte_of x Hx) -(of_bytes_byte_of y Hy). cbn [map idx8].
    rewrite (H 0) ?(H 1) ?(H 2) ?(H 3) ?(H 4) ?(H 5) ?(H 6) ?(H 7); cbn; lia.
  - destruct H as (t & Ht & H). exists t. split; [cbn in Ht; lia | exact H].
Qed.

(** Whenever [loop_mask] w is nonzero for a 64-bit word w, some byte of
    w is zero. *)
Lemma loop_mask_has_zero w : 0 <= w < 2 ^ 64 -> loop_mask w <> 0 -> exists j, 0 <= j < 8 /\ byte_of w j = 0.
Proof.
  intros Hw Hm. destruct (idx_dec (fun j => byte_of w j <> 0) (fun j => match Z.eq_dec (byte_of w j) 0 with left e => right (fun h => h e) | right n => left n end) 8) as [H|H].
  - exfalso. apply Hm, (loop_mask_zero w Hw). intros j Hj. apply H. cbn. lia.
  - destruct H as (j & Hj & H). exists j. split; [cbn in Hj; lia | lia].
Qed.

(** Bitwise OR of two 64-bit unsigned words produces a 64-bit unsigned
    word. *)
Lemma lor_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.lor a b mod 2 ^ 64 = Z.lor a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2; [|lia]. rewrite Z.lor_spec.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
    rewrite (bits64 a n Ha E) (bits64 b n Hb E). reflexivity. }
  rewrite -E. apply Z.mod_pos_bound. lia.
Qed.

(** ## The comparison mask

    When two words differ or contain a NUL byte, glibc calls
    `find_zero_ne_all` to mark every stopping byte with bit 7 set
    (`0x80`). This section defines [cmp_mask] to match the wrapped 64-bit
    arithmetic that nanofil's IR emits, and verifies byte-by-byte that
    each byte of [cmp_mask] equals 128 exactly at stopping positions. *)

(** Function [cmp_mask] computes glibc's `find_zero_ne_all` bitmask on
    words x and y using explicit 64-bit modular arithmetic. *)
Definition cmp_mask (x y : Z) : Z :=
  Z.land
    (Z.lor
       (Z.lor
          (((Z.land (Z.lxor (x mod 2 ^ 64) (y mod 2 ^ 64) mod 2 ^ 64) (9187201950435737471 mod 2 ^ 64)
               mod 2 ^ 64 + 9187201950435737471 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
          (Z.lxor (x mod 2 ^ 64) (y mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
       (Z.lxor
          (Z.lor
             (((Z.land (x mod 2 ^ 64) (9187201950435737471 mod 2 ^ 64) mod 2 ^ 64
                + 9187201950435737471 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
             (x mod 2 ^ 64) mod 2 ^ 64)
          (-1 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
    (9259542123273814144 mod 2 ^ 64).

(** Masking each byte to its low seven bits and adding 127 never carries
    across byte boundaries. *)
Lemma add_ones7 z i : 0 <= i < 8 -> byte_of (Z.land z ones7 mod 2 ^ 64 + ones7) i = Z.land (byte_of z i) 127 + 127.
Proof.
  intros Hi. rewrite byte_of_add; [| |lia].
  - rewrite byte_of_mod64; [|lia]. rewrite byte_of_land; [|lia]. rewrite byte_ones7; [reflexivity|lia].
  - intros j Hj. rewrite byte_of_mod64; [|lia]. rewrite byte_of_land; [|lia]. rewrite byte_ones7; [|lia].
    pose proof (land127 (byte_of z j) (byte_of_range z j)). lia.
Qed.

(** Exhaustive evaluation confirms that the byte-level formula of
    [cmp_mask] yields 128 when b1 is 0 or differs from b2, and 0
    otherwise. *)
Lemma cmp_on_bytes b1 b2 : 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Z.land (Z.lor (Z.lor (Z.land (Z.lxor b1 b2) 127 + 127) (Z.lxor b1 b2))
            (Z.lxor (Z.lor (Z.land b1 127 + 127) b1) 255)) 128 =
  if (b1 =? 0) || negb (b1 =? b2) then 128 else 0.
Proof.
  intros H1 H2. apply Z.eqb_eq.
  set (P := fun b1 b2 => Z.land (Z.lor (Z.lor (Z.land (Z.lxor b1 b2) 127 + 127) (Z.lxor b1 b2))
            (Z.lxor (Z.lor (Z.land b1 127 + 127) b1) 255)) 128 =? if (b1 =? 0) || negb (b1 =? b2) then 128 else 0).
  assert (H : forallb (fun b1 => forallb (P b1) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  exact (all_bytes (P b1) (all_bytes _ H b1 H1) b2 H2).
Qed.

(** Byte i of [cmp_mask] x y equals 128 when byte i of x is 0 or
    differs from byte i of y, and 0 otherwise. *)
Lemma cmp_mask_byte x y i : 0 <= i < 8 ->
  byte_of (cmp_mask x y) i = if (byte_of x i =? 0) || negb (byte_of x i =? byte_of y i) then 128 else 0.
Proof.
  intros Hi. assert (Hi0 : 0 <= i) by lia. unfold cmp_mask.
  change (9187201950435737471 mod 2 ^ 64) with ones7. change (9259542123273814144 mod 2 ^ 64) with highs.
  change (-1 mod 2 ^ 64) with all64.
  pose proof (fun z => byte_of_mod64 z i Hi) as M. pose proof (fun a b => byte_of_land a b i Hi0) as La.
  pose proof (fun a b => byte_of_lor a b i Hi0) as Lo. pose proof (fun a b => byte_of_lxor a b i Hi0) as Lx.
  pose proof (fun z => add_ones7 z i Hi) as Ad.
  do 6 rewrite ?M ?La ?Lo ?Lx ?Ad ?(byte_ones7 i Hi) ?(byte_highs i Hi) ?(byte_all64 i Hi).
  apply cmp_on_bytes; apply byte_of_range.
Qed.

(** The value of [cmp_mask] x y always fits in an unsigned 64-bit word. *)
Lemma cmp_mask_range x y : 0 <= cmp_mask x y < 2 ^ 64.
Proof. unfold cmp_mask. apply land_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** ## Words of an unaligned string

    When the first string's pointer is 8-byte aligned and the second
    string's pointer sits at byte offset o inside its word, glibc
    combines two consecutive words lo and hi using `MERGE`. This section
    models that shift-right-and-shift-left combination with [shd], [shu],
    and [merge], and proves that byte u of [merge] lo hi o equals byte
    u + o of the concatenated pair. *)

(** Function [shd] shifts word lo down by o bytes to place its high
    8 - o bytes at the bottom of a 64-bit word. *)
Definition shd (lo o : Z) : Z := (lo mod 2 ^ 64 / 2 ^ (((8 * o) mod 2 ^ 32) mod 64)) mod 2 ^ 64.

(** Function [shu] shifts word hi up by 8 - o bytes to place its low o
    bytes at the top of a 64-bit word. *)
Definition shu (hi o : Z) : Z := ((hi mod 2 ^ 64 * 2 ^ (((64 - 8 * o) mod 2 ^ 32) mod 64)) mod 2 ^ 64) mod 2 ^ 64.

(** Function [merge] models glibc's `MERGE` macro by combining [shd] lo o
    and [shu] hi o with bitwise OR. *)
Definition merge (lo hi o : Z) : Z := Z.lor (shd lo o) (shu hi o).

(** Multiplying z by 2^(8 * k) shifts every byte upward by k positions
    and fills the low k bytes with zero. *)
Lemma byte_of_mul_pow z k i : 0 <= k -> 0 <= i ->
  byte_of (z * 2 ^ (8 * k)) i = if i <? k then 0 else byte_of z (i - k).
Proof.
  intros Hk Hi. unfold byte_of. destruct (Z.ltb_spec i k) as [Hlt|Hge].
  - replace (z * 2 ^ (8 * k)) with (z * 2 ^ (8 * (k - i - 1)) * 256 * 2 ^ (8 * i)).
    + rewrite Z.div_mul; [|apply Z.pow_nonzero; lia]. apply Z.mod_mul. lia.
    + replace (8 * k) with (8 * (k - i - 1) + 8 + 8 * i) by lia.
      rewrite Z.pow_add_r; [|lia|lia]. rewrite Z.pow_add_r; [|lia|lia]. change (2 ^ 8) with 256. ring.
  - replace (2 ^ (8 * i)) with (2 ^ (8 * k) * 2 ^ (8 * (i - k))).
    + assert (P1 : 0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
      assert (P2 : 0 < 2 ^ (8 * (i - k))) by (apply Z.pow_pos_nonneg; lia).
      rewrite -(Z.div_div (z * 2 ^ (8 * k)) (2 ^ (8 * k)) (2 ^ (8 * (i - k))) ltac:(lia) ltac:(lia)). rewrite (Z.div_mul z (2 ^ (8 * k))); [reflexivity | lia].
    + rewrite -Z.pow_add_r; [f_equal; lia | lia | lia].
Qed.

(** Byte u of [shd] lo o equals byte u + o of lo when u + o < 8, and 0
    otherwise. *)
Lemma shd_byte lo o u : 0 <= o < 8 -> 0 <= u < 8 ->
  byte_of (shd lo o) u = if u + o <? 8 then byte_of lo (u + o) else 0.
Proof.
  intros Ho Hu. unfold shd. rewrite (Z.mod_small (8 * o) (2 ^ 32)); [|lia]. rewrite (Z.mod_small (8 * o) 64); [|lia].
  rewrite byte_of_mod64; [|lia]. rewrite byte_of_div; [|lia|lia]. destruct (Z.ltb_spec (u + o) 8).
  - apply byte_of_mod64. lia.
  - apply byte_of_high; [apply Z.mod_pos_bound; lia | lia].
Qed.

(** Byte u of [shu] hi o equals 0 when u + o < 8, and byte u + o - 8 of
    hi otherwise. *)
Lemma shu_byte hi o u : 0 < o < 8 -> 0 <= u < 8 ->
  byte_of (shu hi o) u = if u + o <? 8 then 0 else byte_of hi (u + o - 8).
Proof.
  intros Ho Hu. unfold shu. rewrite (Z.mod_small (64 - 8 * o) (2 ^ 32)); [|lia].
  rewrite (Z.mod_small (64 - 8 * o) 64); [|lia]. replace (64 - 8 * o) with (8 * (8 - o)) by lia.
  rewrite byte_of_mod64; [|lia]. rewrite byte_of_mod64; [|lia]. rewrite byte_of_mul_pow; [|lia|lia].
  destruct (Z.ltb_spec u (8 - o)), (Z.ltb_spec (u + o) 8); try lia.
  rewrite byte_of_mod64; [|lia]. f_equal. lia.
Qed.

(** Byte u of [merge] lo hi o equals byte u + o of lo when u + o < 8,
    and byte u + o - 8 of hi otherwise. *)
Lemma merge_byte lo hi o u : 0 < o < 8 -> 0 <= u < 8 ->
  byte_of (merge lo hi o) u = if u + o <? 8 then byte_of lo (u + o) else byte_of hi (u + o - 8).
Proof.
  intros Ho Hu. unfold merge. rewrite byte_of_lor; [|lia]. rewrite shd_byte; [|lia|lia]. rewrite shu_byte; [|lia|lia].
  destruct (u + o <? 8); [apply Z.lor_0_r | apply Z.lor_0_l].
Qed.

(** The result of [merge] lo hi o always lies in the unsigned 64-bit
    range. *)
Lemma merge_range lo hi o : 0 <= merge lo hi o < 2 ^ 64.
Proof. apply lor_range; apply Z.mod_pos_bound; lia. Qed.

(** ## Arithmetic of the IR

    When glibc checks pointer alignment, extends loaded bytes, or extracts
    a byte from a word by shifting, nanofil's IR wraps each intermediate
    value to 32 or 64 bits. The lemmas in this section simplify those
    IR-level bitmasks and extensions back to clean integer arithmetic. *)

(** Masking a 64-bit integer x with 7 extracts its low three bits, which
    equals x mod 8. *)
Lemma land7 x : 0 <= x < 2 ^ 64 -> Z.land (x mod 2 ^ 64) (7 mod 2 ^ 64) = x mod 8.
Proof.
  intros H. rewrite (Z.mod_small x); [|lia]. change (7 mod 2 ^ 64) with (Z.ones 3).
  rewrite Z.land_ones; [reflexivity|lia].
Qed.

(** Negating a 64-bit address a and masking with 7 computes (-a) mod 8,
    the number of bytes from a to the next 8-byte boundary. *)
Lemma neg_land7 a : 0 <= a < 2 ^ 64 -> Z.land ((- (a mod 2 ^ 64)) mod 2 ^ 64 mod 2 ^ 64) (7 mod 2 ^ 64) = (- a) mod 8.
Proof.
  intros H. rewrite (Z.mod_small a); [|lia]. rewrite Zmod_mod. change (7 mod 2 ^ 64) with (Z.ones 3).
  rewrite Z.land_ones; [|lia]. change (2 ^ 3) with 8. symmetry.
  apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 61); reflexivity].
Qed.

(** Loading a byte with sign extension and then truncating with unsigned
    byte extension recovers the original byte value c. *)
Lemma sb_ub c : 0 <= c < 256 -> extension Ub ((extension Sb c mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 = c.
Proof.
  intros H. apply Z.eqb_eq.
  exact (all_bytes (fun c => extension Ub ((extension Sb c mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 =? c)
           ltac:(vm_compute; reflexivity) c H).
Qed.

(** Sign-extending a nonnegative 31-bit counter c from 32 bits to 64
    bits leaves c unchanged. *)
Lemma sext_small c : 0 <= c < 2 ^ 31 -> extension Sw (c mod 2 ^ 32) mod 2 ^ 64 = c.
Proof.
  intros H. rewrite (Z.mod_small c); [|lia]. cbn [extension]. unfold sign_extension.
  rewrite (Z.mod_small c); [|lia]. replace (2 ^ 31 <=? c) with false; [apply Z.mod_small; lia|].
  symmetry. apply Z.leb_gt. lia.
Qed.

(** Shifting a 64-bit word x down by 8 * j bits and taking its unsigned
    low byte yields byte j of x. *)
Lemma ub_shift x j : 0 <= j < 8 ->
  extension Ub ((x mod 2 ^ 64 / 2 ^ (((8 * j) mod 2 ^ 32) mod 64)) mod 2 ^ 32) mod 2 ^ 32 = byte_of x j.
Proof.
  intros Hj. rewrite (Z.mod_small (8 * j) (2 ^ 32)); [|lia]. rewrite (Z.mod_small (8 * j) 64); [|lia].
  cbn [extension]. rewrite -(byte_of_mod64 x j Hj). unfold byte_of.
  rewrite -(Znumtheory.Zmod_div_mod 256 (2 ^ 32)); [| lia | lia | exists (2 ^ 24); reflexivity].
  apply Z.mod_small. pose proof (Z.mod_pos_bound (x mod 2 ^ 64 / 2 ^ (8 * j)) 256). lia.
Qed.

(** ## A string's window

    To verify word-aligned loads in the loop, we need to relate a
    pointer's byte offset in the string to its 8-byte word index in the
    window. This section unpacks [str_shape] into linear arithmetic
    bounds and translates string offsets into aligned [wrd] reads or
    unaligned [merge] reads. *)

(** Lemma [shape_facts] unpacks [str_shape] into the address, alignment,
    window length, and capability bounds needed by the loop invariants. *)
Lemma shape_facts p b reg ws s : str_shape p b reg ws s ->
  0 < b /\ b <= wstart p /\ wstart p mod 8 = 0 /\ ptr_addr p = wstart p + ptr_addr p mod 8 /\
  0 <= ptr_addr p mod 8 < 8 /\ wstart p + 8 * Z.of_nat (length ws) <= r_end reg /\ r_end reg <= 2 ^ 48 /\
  ptr_addr p mod 8 + Z.of_nat (length s) < 8 * Z.of_nat (length ws) /\ (ptr_cap p = Obj b \/ ptr_cap p = Ro b).
Proof.
  intros [Hc Hb0 Hb8 Hst Hf Hsp Hl Hw Hby Hch]. unfold wstart in *.
  pose proof (Z.div_mod (ptr_addr p) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  pose proof (Z.div_mod b 8 ltac:(lia)).
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  split; [lia|]. split; [nia|]. split.
  { replace (ptr_addr p - ptr_addr p mod 8) with (8 * (ptr_addr p / 8)) by lia. rewrite Z.mul_comm. apply Z_mod_mult. }
  repeat split; try lia. exact Hc.
Qed.

(** When string offset k + c lands at word boundary 8 * q, byte u after
    c equals byte u of word q in ws. *)
Lemma bt_at ws k c q u : k + c = 8 * q -> 0 <= q -> 0 <= u < 8 -> bt ws (k + (c + u)) = byte_of (wrd ws q) u.
Proof. intros E Hq Hu. rewrite (bt_word ws q u Hq Hu). f_equal. lia. Qed.

(** An unaligned string spans two consecutive words in memory. When
    offset k + c lands at byte offset o inside word q, [merge] combines
    words q and q + 1 so its byte u matches the window byte at k + c + u. *)
Lemma bt_merge ws k c q o u : k + c = 8 * q + o -> 0 <= q -> 0 < o < 8 -> 0 <= u < 8 ->
  bt ws (k + (c + u)) = byte_of (merge (wrd ws q) (wrd ws (q + 1)) o) u.
Proof.
  intros E Hq Ho Hu. rewrite merge_byte; [|lia|lia]. destruct (Z.ltb_spec (u + o) 8).
  - rewrite (bt_word ws q (u + o)); [|lia|lia]. f_equal. lia.
  - rewrite (bt_word ws (q + 1) (u + o - 8)); [|lia|lia]. f_equal. lia.
Qed.

(** ## Returns

    Once a loop iteration finds a zero byte or a mismatch, glibc either
    computes the final return value or advances by eight bytes to the
    next word pair. This section turns a word-level zero or mismatch
    into the byte-level answer [strcmp_res], or extends the matching
    prefix across all eight bytes. *)

(** When words x and y match the strings from offset c and stop within n
    bytes, [word_stop] finds the first stopping byte j and equates
    [strcmp_res] to their byte difference at j. *)
Lemma word_stop s1 s2 f1 f2 c x y n :
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= c -> same_upto f1 f2 c ->
  n <= 8 -> (forall u, 0 <= u < n -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of y u) ->
  (exists u, 0 <= u < n /\ stop_at (byte_of x) (byte_of y) u) ->
  exists j, 0 <= j < n /\ stop_at (byte_of x) (byte_of y) j /\ same_upto (byte_of x) (byte_of y) j /\
    strcmp_res s1 s2 = (byte_of x j - byte_of y j) mod 2 ^ 32.
Proof.
  intros Hc A1 A2 H0 Hs Hn Hb (u & Hu & Hst).
  destruct (first_stop (byte_of x) (byte_of y) 0 u ltac:(lia) Hst ltac:(intros j Hj; exfalso; lia))
    as (j & Hj & Hstj & Hsj).
  exists j. split; [lia|]. split; [exact Hstj|]. split; [exact Hsj|].
  destruct (Hb j ltac:(lia)) as [E1 E2]. rewrite -E1 -E2.
  apply strcmp_res_stop; [ | exact A1 | exact A2 | lia | | ].
  - eapply Forall_impl; [| exact Hc]. cbn. intros; lia.
  - intros i Hi. destruct (Z.lt_ge_cases i c); [apply Hs; lia|].
    destruct (Hb (i - c) ltac:(lia)) as [F1 F2]. replace (c + (i - c)) with i in F1, F2 by lia.
    rewrite F1 F2. apply Hsj. lia.
  - unfold stop_at in *. rewrite E1 E2. exact Hstj.
Qed.

(** When both strings match word x from offset c and x has a zero byte
    according to [loop_mask], both strings terminate together and
    [strcmp_res] is 0. *)
Lemma word_zero s1 s2 f1 f2 c x :
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> 0 <= c -> same_upto f1 f2 c ->
  0 <= x < 2 ^ 64 -> (forall u, 0 <= u < 8 -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of x u) ->
  loop_mask x <> 0 -> strcmp_res s1 s2 = 0.
Proof.
  intros Hc A1 A2 H0 Hs Hx Hb Hm. destruct (loop_mask_has_zero x Hx Hm) as (u & Hu & Hz).
  destruct (word_stop s1 s2 f1 f2 c x x 8 Hc A1 A2 H0 Hs ltac:(lia) Hb) as (j & _ & _ & _ & ->).
  - exists u. split; [exact Hu | left; exact Hz].
  - rewrite Z.sub_diag. reflexivity.
Qed.

(** When words x and y agree on all eight bytes from offset c with no
    zero byte, [same_upto] extends from c to c + 8. *)
Lemma word_same f1 f2 c x y : 0 <= c -> same_upto f1 f2 c ->
  (forall u, 0 <= u < 8 -> f1 (c + u) = byte_of x u /\ f2 (c + u) = byte_of y u) ->
  (forall u, 0 <= u < 8 -> byte_of x u = byte_of y u /\ byte_of x u <> 0) -> same_upto f1 f2 (c + 8).
Proof.
  intros H0 Hs Hb Hxy i Hi. destruct (Z.lt_ge_cases i c); [apply Hs; lia|].
  destruct (Hb (i - c) ltac:(lia)) as [F1 F2]. replace (c + (i - c)) with i in F1, F2 by lia.
  rewrite F1 F2. apply Hxy. lia.
Qed.

(** If j is the first stopping byte between words x and y, then
    [cmp_mask] x y is nonzero and its trailing bit count [tail] equals
    8 * j + 7. *)
Lemma cmp_mask_first x y j : 0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  tail (cmp_mask x y) = 8 * j + 7 /\ cmp_mask x y <> 0.
Proof.
  intros Hj Hst Hs.
  assert (Hat : byte_of (cmp_mask x y) j = 128).
  { rewrite cmp_mask_byte; [|lia]. destruct Hst as [E|E].
    - rewrite E. reflexivity.
    - replace (byte_of x j =? byte_of y j) with false; [rewrite orb_true_r; reflexivity|].
      symmetry. apply Z.eqb_neq. exact E. }
  split.
  - apply tail_first; [apply cmp_mask_range | | exact Hj | exact Hat |].
    + intros i Hi. rewrite cmp_mask_byte; [|lia]. destruct (_ || _); auto.
    + intros i Hi. rewrite cmp_mask_byte; [|lia]. destruct (Hs i Hi) as [E1 E2].
      replace (byte_of x i =? 0) with false; [|symmetry; apply Z.eqb_neq; exact E2].
      replace (byte_of x i =? byte_of y i) with true; [reflexivity|symmetry; apply Z.eqb_eq; exact E1].
  - intros E. rewrite E in Hat. unfold byte_of in Hat. rewrite Z.div_0_l in Hat; [discriminate | apply Z.pow_nonzero; lia].
Qed.

(** Function [sbyte] reads byte j of the string at pointer p from its
    word window ws. *)
Definition sbyte (p : ptr) (ws : list Z) (j : Z) : Z := bt ws (ptr_addr p mod 8 + j).

(** For any string satisfying [str_shape], [sbyte] agrees with the
    string through its NUL terminator. *)
Lemma sbyte_agree p b reg ws s : str_shape p b reg ws s -> agree_str (sbyte p ws) s.
Proof. exact (str_bt p b reg ws s). Qed.

(** Reducing [shd] lo o modulo 2^64 leaves it unchanged because [shd]
    already returns a 64-bit unsigned word. *)
Lemma shd_mod lo o : shd lo o mod 2 ^ 64 = shd lo o.
Proof. apply Zmod_mod. Qed.

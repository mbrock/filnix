(** glibc's fast string functions test eight bytes at once. They load a
    64-bit [[word]], combine it with constants such as `0x7f7f...7f`
    through additions, subtractions and bitwise operations, and read
    the answer for each byte from the matching byte of the result.
    Proving such a function means showing that each byte of the result
    depends only on the bytes in the same position, and computing that
    dependence once for all 256 byte values.

    Bitwise operations act on each byte independently, but addition
    and subtraction pass a carry or borrow from one byte to the next.
    This module models a word expression as a row of eight byte lanes
    joined by those carries. The theorem [sw_ripple] states that every
    byte of the 64-bit result equals the output of one lane, given the
    carries that the lower lanes pass up to it. The checkers that
    follow decide by computation that a lane never produces a carry,
    or produces one only after a byte that stops the search, and the
    lemmas built on them turn that check into a statement about every
    byte of every word.

    The per-function files such as [StrlenBits] and [StrcmpBits] used
    to prove each mask byte by byte with their own case analysis.
    With this module, a mask is written once as an expression of type
    [sw], and its byte-level meaning is a single computed check. *)

From Stdlib Require Import ZArith Lia List Bool.
From Nanofil Require Import Memory WordBits.
Import ListNotations.
Open Scope Z_scope.

(** ## Word expressions

    A mask in glibc's string code is built from its input words and
    repeated byte constants. The type [sw] records that construction,
    so that both its 64-bit value and its effect on one byte lane can
    be computed from the same term. *)

(** The constructors follow the operations that nanofil emits for
    glibc's `c: string-fza.h` and `c: string-fzb.h` helpers. [SVar] n
    names the n-th input word, [SRep] c repeats the byte c across the
    word, and the remaining constructors are the bitwise operations and
    the wrapping addition and subtraction of 64-bit integers. *)
Inductive sw : Type :=
  | SVar (n : nat)
  | SRep (c : Z)
  | SAnd (a b : sw)
  | SOr (a b : sw)
  | SXor (a b : sw)
  | SAdd (a b : sw)
  | SSub (a b : sw).

(** The 64-bit value of an expression applies the C operations to the
    input words ws, wrapping each input, sum and difference to 64 bits
    as the machine does. A missing input reads as zero. *)
Fixpoint sw_word (ws : list Z) (e : sw) : Z :=
  match e with
  | SVar n => nth n ws 0 mod 2 ^ 64
  | SRep c => repeat_byte (c mod 256)
  | SAnd a b => Z.land (sw_word ws a) (sw_word ws b)
  | SOr a b => Z.lor (sw_word ws a) (sw_word ws b)
  | SXor a b => Z.lxor (sw_word ws a) (sw_word ws b)
  | SAdd a b => (sw_word ws a + sw_word ws b) mod 2 ^ 64
  | SSub a b => (sw_word ws a - sw_word ws b) mod 2 ^ 64
  end.

(** An expression reads only inputs below n when [sw_vars_below] n
    holds. The checkers below enumerate the bytes of one or two inputs,
    so they need this bound to cover every input the expression reads. *)
Fixpoint sw_vars_below (n : nat) (e : sw) : bool :=
  match e with
  | SVar k => Nat.ltb k n
  | SRep _ => true
  | SAnd a b | SOr a b | SXor a b | SAdd a b | SSub a b => sw_vars_below n a && sw_vars_below n b
  end.

(** ## Byte lanes and their carries

    One byte position of an expression behaves like a small circuit.
    It reads one byte of each input and one incoming carry or borrow
    for each addition and subtraction, and it produces one output byte
    and the carries for the next position up. *)

(** A value of type [carries] holds one bit for each addition and
    subtraction in an expression, arranged in the same tree shape.
    The bit at a bitwise node is unused and kept false. *)
Inductive carries : Type :=
  | CLeaf
  | CNode (c : bool) (l r : carries).

(** No carry enters the lowest byte. The function [sw_zero] supplies
    false for every carry bit in the expression's tree. *)
Fixpoint sw_zero (e : sw) : carries :=
  match e with
  | SVar _ | SRep _ => CLeaf
  | SAnd a b | SOr a b | SXor a b | SAdd a b | SSub a b => CNode false (sw_zero a) (sw_zero b)
  end.

(** A lane passes nothing upward when every bit of its outgoing
    carries is false, which [carries_zero] decides. *)
Fixpoint carries_zero (cs : carries) : bool :=
  match cs with
  | CLeaf => true
  | CNode c l r => negb c && carries_zero l && carries_zero r
  end.

(** One lane of e reads the byte of input n as bs n and the incoming
    carries cs, and returns its output byte with the outgoing carries.
    An addition sets its carry when the byte sum reaches 256, and a
    subtraction sets its borrow when the byte difference is negative.
    A carry tree of the wrong shape counts as all false. *)
Fixpoint sw_lane (e : sw) (bs : nat -> Z) (cs : carries) : Z * carries :=
  let kids := match cs with CLeaf => (CLeaf, CLeaf) | CNode _ l r => (l, r) end in
  let cin := match cs with CLeaf => false | CNode c _ _ => c end in
  match e with
  | SVar n => (bs n mod 256, CLeaf)
  | SRep c => (c mod 256, CLeaf)
  | SAnd a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      (Z.land x y, CNode false ca cb)
  | SOr a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      (Z.lor x y, CNode false ca cb)
  | SXor a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      (Z.lxor x y, CNode false ca cb)
  | SAdd a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      let s := x + y + Z.b2z cin in (s mod 256, CNode (256 <=? s) ca cb)
  | SSub a b =>
      let '(x, ca) := sw_lane a bs (fst kids) in let '(y, cb) := sw_lane b bs (snd kids) in
      let d := x - y - Z.b2z cin in (d mod 256, CNode (d <? 0) ca cb)
  end.

(** The function [sw_bytes] reads position i from each input word. *)
Definition sw_bytes (ws : list Z) (i : Z) : nat -> Z := fun n => byte_of (nth n ws 0) i.

(** The carries that enter position i come from running every lower
    lane in turn, starting from no carries below byte zero. *)
Fixpoint sw_carry (ws : list Z) (e : sw) (i : nat) : carries :=
  match i with
  | O => sw_zero e
  | S i => snd (sw_lane e (sw_bytes ws (Z.of_nat i)) (sw_carry ws e i))
  end.

(** ## Words and their lanes

    The following facts connect the 64-bit value of an expression to
    its lanes. They hold for every expression and every input, and
    every later lemma in this module follows from them. *)

(** A word expression always yields an unsigned 64-bit value. *)
Lemma sw_word_range ws e : 0 <= sw_word ws e < 2 ^ 64.
Proof.
  induction e; cbn [sw_word]; try (apply Z.mod_pos_bound; lia).
  - pose proof (Z.mod_pos_bound c 256 ltac:(lia)). unfold repeat_byte, lows. lia.
  - apply land_range; assumption.
  - assert (H : Z.lor (sw_word ws e1) (sw_word ws e2) mod 2 ^ 64 =
                Z.lor (sw_word ws e1) (sw_word ws e2)).
    { apply Z.bits_inj'. intros n Hn.
      rewrite Z.testbit_mod_pow2, !Z.lor_spec by lia.
      destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
      rewrite !bits64 by assumption. reflexivity. }
    rewrite <- H. apply Z.mod_pos_bound. lia.
  - assert (H : Z.lxor (sw_word ws e1) (sw_word ws e2) mod 2 ^ 64 =
                Z.lxor (sw_word ws e1) (sw_word ws e2)).
    { apply Z.bits_inj'. intros n Hn.
      rewrite Z.testbit_mod_pow2, !Z.lxor_spec by lia.
      destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
      rewrite !bits64 by assumption. reflexivity. }
    rewrite <- H. apply Z.mod_pos_bound. lia.
Qed.

(** The low prefixes determine the carry entering an addition. The
    next prefix sets its carry precisely when the current byte overflows. *)
Lemma sw_add_digit x y i : 0 <= i ->
  let p := 2 ^ (8 * i) in
  let c := Z.b2z (p <=? x mod p + y mod p) in
  byte_of (x + y) i = (byte_of x i + byte_of y i + c) mod 256 /\
  (2 ^ (8 * (i + 1)) <=? x mod 2 ^ (8 * (i + 1)) + y mod 2 ^ (8 * (i + 1))) =
  (256 <=? byte_of x i + byte_of y i + c).
Proof.
  intros Hi p c.
  assert (Hp : 0 < p) by (unfold p; apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound x p Hp) as Hx.
  pose proof (Z.mod_pos_bound y p Hp) as Hy.
  assert (Hr : 0 <= x mod p + y mod p - p * c < p).
  { unfold c. destruct (Z.leb_spec p (x mod p + y mod p)); cbn; nia. }
  assert (Hq : (x + y) / p = x / p + y / p + c).
  { symmetry. apply Z.div_unique with (r := x mod p + y mod p - p * c).
    - left. exact Hr.
    - pose proof (Z.div_mod x p ltac:(lia)). pose proof (Z.div_mod y p ltac:(lia)). nia. }
  split.
  - unfold byte_of. change ((x + y) / p mod 256 = (x / p mod 256 + y / p mod 256 + c) mod 256).
    rewrite Hq. rewrite Z.add_mod, (Z.add_mod (x / p) (y / p)) by lia.
    rewrite (Z.add_mod (x / p mod 256 + y / p mod 256) c) by lia. reflexivity.
  - rewrite !low_step by lia.
    replace (2 ^ (8 * (i + 1))) with (p * 256)
      by (unfold p; rewrite Z.mul_add_distr_l, Z.pow_add_r by lia; reflexivity).
    fold p. apply Bool.eq_true_iff_eq. rewrite !Z.leb_le. nia.
Qed.

(** Subtraction uses the same prefix calculation with a borrow instead
    of a carry. This includes a borrow from a zero byte. *)
Lemma sw_sub_digit x y i : 0 <= i ->
  let p := 2 ^ (8 * i) in
  let c := Z.b2z (x mod p <? y mod p) in
  byte_of (x - y) i = (byte_of x i - byte_of y i - c) mod 256 /\
  (x mod 2 ^ (8 * (i + 1)) <? y mod 2 ^ (8 * (i + 1))) =
  (byte_of x i - byte_of y i - c <? 0).
Proof.
  intros Hi p c.
  assert (Hp : 0 < p) by (unfold p; apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound x p Hp) as Hx.
  pose proof (Z.mod_pos_bound y p Hp) as Hy.
  assert (Hr : 0 <= x mod p - y mod p + p * c < p).
  { unfold c. destruct (Z.ltb_spec (x mod p) (y mod p)); cbn; nia. }
  assert (Hq : (x - y) / p = x / p - y / p - c).
  { symmetry. apply Z.div_unique with (r := x mod p - y mod p + p * c).
    - left. exact Hr.
    - pose proof (Z.div_mod x p ltac:(lia)). pose proof (Z.div_mod y p ltac:(lia)). nia. }
  split.
  - unfold byte_of. change ((x - y) / p mod 256 = (x / p mod 256 - y / p mod 256 - c) mod 256).
    rewrite Hq. rewrite Zminus_mod, (Zminus_mod (x / p) (y / p)).
    rewrite (Zminus_mod (x / p mod 256 - y / p mod 256) c). reflexivity.
  - rewrite !low_step by lia. fold p.
    apply Bool.eq_true_iff_eq. rewrite !Z.ltb_lt. nia.
Qed.

(** The mathematical carry tree records each operation's low-prefix
    overflow. It connects the recursive lane execution to whole-word arithmetic. *)
Fixpoint sw_prefix (ws : list Z) (e : sw) (i : Z) : carries :=
  let p := 2 ^ (8 * i) in
  match e with
  | SVar _ | SRep _ => CLeaf
  | SAnd a b | SOr a b | SXor a b => CNode false (sw_prefix ws a i) (sw_prefix ws b i)
  | SAdd a b => CNode (p <=? sw_word ws a mod p + sw_word ws b mod p)
      (sw_prefix ws a i) (sw_prefix ws b i)
  | SSub a b => CNode (sw_word ws a mod p <? sw_word ws b mod p)
      (sw_prefix ws a i) (sw_prefix ws b i)
  end.

(** With the prefix carries as input, one lane returns the correct
    byte and the prefix carries for the next position. *)
Lemma sw_lane_prefix ws e i : 0 <= i < 8 ->
  sw_lane e (sw_bytes ws i) (sw_prefix ws e i) =
  (byte_of (sw_word ws e) i, sw_prefix ws e (i + 1)).
Proof.
  intros Hi. induction e; cbn [sw_prefix sw_lane sw_word fst snd].
  - unfold sw_bytes. rewrite byte_of_mod64 by lia.
    rewrite Z.mod_small by apply byte_of_range. reflexivity.
  - rewrite byte_repeat_byte by (try lia; apply Z.mod_pos_bound; lia). reflexivity.
  - rewrite IHe1, IHe2. rewrite byte_of_land by lia. reflexivity.
  - rewrite IHe1, IHe2. rewrite byte_of_lor by lia. reflexivity.
  - rewrite IHe1, IHe2. rewrite byte_of_lxor by lia. reflexivity.
  - rewrite IHe1, IHe2. rewrite byte_of_mod64 by lia.
    destruct (sw_add_digit (sw_word ws e1) (sw_word ws e2) i ltac:(lia)) as [Hb Hc].
    rewrite Hb, Hc. reflexivity.
  - rewrite IHe1, IHe2. rewrite byte_of_mod64 by lia.
    destruct (sw_sub_digit (sw_word ws e1) (sw_word ws e2) i ltac:(lia)) as [Hb Hc].
    rewrite Hb, Hc. reflexivity.
Qed.

(** No operation can overflow an empty prefix, which is the starting
    case for the lane recurrence. *)
Lemma sw_prefix_zero ws e : sw_prefix ws e 0 = sw_zero e.
Proof.
  induction e; cbn [sw_prefix sw_zero]; rewrite ?Z.mod_1_r, ?IHe1, ?IHe2; reflexivity.
Qed.

(** Running the lower lanes produces exactly their mathematical prefix
    carries, without any assumption that these carries vanish. *)
Lemma sw_carry_prefix ws e i : (i <= 8)%nat ->
  sw_carry ws e i = sw_prefix ws e (Z.of_nat i).
Proof.
  induction i as [|i IH]; intros Hi.
  - symmetry. apply sw_prefix_zero.
  - cbn [sw_carry]. rewrite IH by lia.
    rewrite sw_lane_prefix by lia. cbn [snd]. f_equal. lia.
Qed.

(** Byte i of an expression's value is the output of lane i, given
    the bytes of the inputs at i and the carries from the lanes below. *)
Theorem sw_ripple ws e (i : nat) : (i < 8)%nat ->
  byte_of (sw_word ws e) (Z.of_nat i) =
  fst (sw_lane e (sw_bytes ws (Z.of_nat i)) (sw_carry ws e i)).
Proof.
  intros Hi. rewrite sw_carry_prefix by lia.
  rewrite sw_lane_prefix by lia. reflexivity.
Qed.

(** An outgoing carry tree always has the expression's shape. If all
    its bits are false, it is therefore the canonical zero tree. *)
Lemma sw_lane_zero e bs cs :
  carries_zero (snd (sw_lane e bs cs)) = true ->
  snd (sw_lane e bs cs) = sw_zero e.
Proof.
  revert cs. induction e; intros cs; destruct cs; cbn [sw_lane sw_zero fst snd]; try reflexivity;
    repeat match goal with
    | |- context [sw_lane ?a bs ?c] => destruct (sw_lane a bs c) as [? ?] eqn:?
    end;
    cbn [snd carries_zero]; intros H;
    repeat rewrite andb_true_iff in H;
    repeat match type of H with _ /\ _ => destruct H as [H ?] end;
    repeat match goal with
    | IH : forall cs, _, E : sw_lane ?a bs ?c = (?v, ?k), Hk : carries_zero ?k = true |- _ =>
        specialize (IH c); rewrite E in IH; cbn [snd] in IH;
        specialize (IH Hk); subst k
    end;
    try reflexivity;
    try match goal with H : negb ?b = true |- _ => apply negb_true_iff in H; rewrite H; reflexivity end.
Qed.

(** When every lane below i passes no carries upward, lane i starts
    from no carries, as byte zero does. *)
Lemma sw_carry_zero ws e (i : nat) :
  (forall j, (j < i)%nat -> carries_zero (snd (sw_lane e (sw_bytes ws (Z.of_nat j)) (sw_zero e))) = true) ->
  sw_carry ws e i = sw_zero e.
Proof.
  induction i as [|i IH]; intros H; [reflexivity|].
  cbn [sw_carry]. rewrite IH by (intros; apply H; lia).
  apply sw_lane_zero, H. lia.
Qed.

(** Equal input bytes at every referenced variable give equal lane
    results. Unused input slots do not affect the computation. *)
Lemma sw_lane_ext n e bs bs' cs : sw_vars_below n e = true ->
  (forall k, (k < n)%nat -> bs k = bs' k) ->
  sw_lane e bs cs = sw_lane e bs' cs.
Proof.
  revert cs. induction e; intros cs H Heq; cbn [sw_vars_below] in H;
    cbn [sw_lane]; try reflexivity.
  - rewrite Heq by (apply Nat.ltb_lt; exact H). reflexivity.
  - apply andb_true_iff in H as [Ha Hb]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in H as [Ha Hb]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in H as [Ha Hb]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in H as [Ha Hb]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in H as [Ha Hb]. rewrite IHe1, IHe2 by assumption. reflexivity.
Qed.

(** A zero-carry check on every lower byte reduces the current byte
    to a lane started from zero, even when the current lane overflows. *)
Lemma sw_ripple_zero ws e i : 0 <= i < 8 ->
  (forall j, 0 <= j < i -> carries_zero (snd (sw_lane e (sw_bytes ws j) (sw_zero e))) = true) ->
  byte_of (sw_word ws e) i = fst (sw_lane e (sw_bytes ws i) (sw_zero e)).
Proof.
  intros Hi H. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite sw_ripple by lia. rewrite sw_carry_zero; [reflexivity|].
  intros j Hj. apply H. lia.
Qed.

(** ## Checking a lane by computation

    A lane reads at most two input bytes when the expression has at
    most two inputs, so its behaviour is fixed by 256 or 65,536 cases.
    The checkers below compute those cases, and the lemmas after each
    one turn a successful check into a statement about every byte of
    every input word. *)

(** The list [bytes256] contains byte values 0 to 255 in the order
    the checkers try them. *)
Definition bytes256 : list Z := map Z.of_nat (seq 0 256).

(** The function [lane2] gives byte b to the first input and byte c
    to every other input. *)
Definition lane2 (b c : Z) : nat -> Z := fun n => match n with O => b | _ => c end.

(** A one-input lane can use the enumerated input function without
    changing its result, because it never reads a second slot. *)
Lemma sw_inputs1 e x i cs : sw_vars_below 1 e = true ->
  sw_lane e (sw_bytes [x] i) cs = sw_lane e (lane2 (byte_of x i) (byte_of x i)) cs.
Proof.
  intros H. apply (sw_lane_ext 1); [exact H|].
  intros k Hk. assert (k = O) by lia. subst k. reflexivity.
Qed.

(** The two-input enumeration likewise supplies exactly the bytes
    that the expression can read. *)
Lemma sw_inputs2 e x y i cs : sw_vars_below 2 e = true ->
  sw_lane e (sw_bytes [x; y] i) cs = sw_lane e (lane2 (byte_of x i) (byte_of y i)) cs.
Proof.
  intros H. apply (sw_lane_ext 2); [exact H|].
  intros k Hk. assert (k = O \/ k = S O) by lia. destruct H0; subst k; reflexivity.
Qed.

(** A one-input expression e computes g on each byte when, for every
    byte b, its lane from no carries returns g b and passes no carries.
    The function g should return a byte, since the lane does. *)
Definition sw_check1 (e : sw) (g : Z -> Z) : bool :=
  sw_vars_below 1 e &&
  forallb (fun b => let '(y, cs) := sw_lane e (lane2 b b) (sw_zero e) in (y =? g b) && carries_zero cs)
    bytes256.

(** A search mask may borrow across a byte only after the byte that
    ends the search. This check requires the correct output for every
    byte, but forbids outgoing carries only when go allows the search
    to continue. *)
Definition sw_check1_upto (e : sw) (go : Z -> bool) (g : Z -> Z) : bool :=
  sw_vars_below 1 e &&
  forallb (fun b => let '(y, cs) := sw_lane e (lane2 b b) (sw_zero e) in
                    (y =? g b) && (negb (go b) || carries_zero cs))
    bytes256.

(** A successful [sw_check1] makes every byte of the result the image
    under g of the input byte in the same position. *)
Theorem sw_map1 e g : sw_check1 e g = true ->
  forall x i, 0 <= i < 8 -> byte_of (sw_word [x] e) i = g (byte_of x i).
Proof.
  unfold sw_check1. rewrite andb_true_iff. intros [Hv Hcheck] x i Hi.
  assert (Hlane : forall j,
    fst (sw_lane e (sw_bytes [x] j) (sw_zero e)) = g (byte_of x j) /\
    carries_zero (snd (sw_lane e (sw_bytes [x] j) (sw_zero e))) = true).
  { intros j. rewrite sw_inputs1 by exact Hv.
    pose proof (all_bytes _ Hcheck (byte_of x j) (byte_of_range x j)) as H.
    cbn beta in H.
    destruct (sw_lane e (lane2 (byte_of x j) (byte_of x j)) (sw_zero e)); cbn [fst snd].
    apply andb_true_iff in H as [H Hc]. apply Z.eqb_eq in H. auto. }
  rewrite sw_ripple_zero by (try lia; intros; apply Hlane).
  apply Hlane.
Qed.

(** The same check also gives the whole word as the bytes of the input,
    each mapped through g, which suits a later test of the word itself. *)
Corollary sw_map1_word e g : sw_check1 e g = true ->
  forall x, sw_word [x] e = of_bytes (map (fun i => g (byte_of x i)) idx8).
Proof.
  intros H x. rewrite <- (of_bytes_byte_of (sw_word [x] e) (sw_word_range [x] e)) at 1.
  f_equal. apply map_ext_in. intros i Hi.
  apply (sw_map1 e g H). unfold idx8 in Hi. cbn in Hi. lia.
Qed.

(** A successful [sw_check1_upto] gives byte i its value under g when
    every byte below i lets the search continue. *)
Theorem sw_map1_upto e go g : sw_check1_upto e go g = true ->
  forall x i, 0 <= i < 8 -> (forall j, 0 <= j < i -> go (byte_of x j) = true) ->
  byte_of (sw_word [x] e) i = g (byte_of x i).
Proof.
  unfold sw_check1_upto. rewrite andb_true_iff. intros [Hv Hcheck] x i Hi Hgo.
  assert (Hlane : forall j,
    fst (sw_lane e (sw_bytes [x] j) (sw_zero e)) = g (byte_of x j) /\
    (go (byte_of x j) = true -> carries_zero (snd (sw_lane e (sw_bytes [x] j) (sw_zero e))) = true)).
  { intros j. rewrite sw_inputs1 by exact Hv.
    pose proof (all_bytes _ Hcheck (byte_of x j) (byte_of_range x j)) as H.
    cbn beta in H.
    destruct (sw_lane e (lane2 (byte_of x j) (byte_of x j)) (sw_zero e)); cbn [fst snd].
    apply andb_true_iff in H as [H Hc]. apply Z.eqb_eq in H.
    split; [exact H|]. intros Hg. rewrite Hg in Hc. exact Hc. }
  rewrite sw_ripple_zero by (try lia; intros; apply Hlane, Hgo; assumption).
  apply Hlane.
Qed.

(** A two-input expression e computes g on each pair of bytes when,
    for all 65,536 pairs, its lane from no carries returns g b c and
    passes no carries. *)
Definition sw_check2 (e : sw) (g : Z -> Z -> Z) : bool :=
  sw_vars_below 2 e &&
  forallb (fun b => forallb (fun c =>
    let '(y, cs) := sw_lane e (lane2 b c) (sw_zero e) in (y =? g b c) && carries_zero cs) bytes256)
    bytes256.

(** The checker [sw_check2_upto] extends [sw_check1_upto] to two inputs.
    It permits borrows only after the first pair that ends the search. *)
Definition sw_check2_upto (e : sw) (go : Z -> Z -> bool) (g : Z -> Z -> Z) : bool :=
  sw_vars_below 2 e &&
  forallb (fun b => forallb (fun c =>
    let '(y, cs) := sw_lane e (lane2 b c) (sw_zero e) in
    (y =? g b c) && (negb (go b c) || carries_zero cs)) bytes256)
    bytes256.

(** A successful [sw_check2] makes every byte of the result the image
    under g of the two input bytes in the same position. *)
Theorem sw_map2 e g : sw_check2 e g = true ->
  forall x y i, 0 <= i < 8 -> byte_of (sw_word [x; y] e) i = g (byte_of x i) (byte_of y i).
Proof.
  unfold sw_check2. rewrite andb_true_iff. intros [Hv Hcheck] x y i Hi.
  assert (Hlane : forall j,
    fst (sw_lane e (sw_bytes [x; y] j) (sw_zero e)) = g (byte_of x j) (byte_of y j) /\
    carries_zero (snd (sw_lane e (sw_bytes [x; y] j) (sw_zero e))) = true).
  { intros j. rewrite sw_inputs2 by exact Hv.
    pose proof (all_bytes _ Hcheck (byte_of x j) (byte_of_range x j)) as Hb.
    pose proof (all_bytes _ Hb (byte_of y j) (byte_of_range y j)) as H.
    cbn beta in H.
    destruct (sw_lane e (lane2 (byte_of x j) (byte_of y j)) (sw_zero e)); cbn [fst snd].
    apply andb_true_iff in H as [H Hc]. apply Z.eqb_eq in H. auto. }
  rewrite sw_ripple_zero by (try lia; intros; apply Hlane).
  apply Hlane.
Qed.

(** A successful [sw_check2_upto] gives byte i its value under g when
    every pair of bytes below i lets the comparison continue. *)
Theorem sw_map2_upto e go g : sw_check2_upto e go g = true ->
  forall x y i, 0 <= i < 8 -> (forall j, 0 <= j < i -> go (byte_of x j) (byte_of y j) = true) ->
  byte_of (sw_word [x; y] e) i = g (byte_of x i) (byte_of y i).
Proof.
  unfold sw_check2_upto. rewrite andb_true_iff. intros [Hv Hcheck] x y i Hi Hgo.
  assert (Hlane : forall j,
    fst (sw_lane e (sw_bytes [x; y] j) (sw_zero e)) = g (byte_of x j) (byte_of y j) /\
    (go (byte_of x j) (byte_of y j) = true ->
      carries_zero (snd (sw_lane e (sw_bytes [x; y] j) (sw_zero e))) = true)).
  { intros j. rewrite sw_inputs2 by exact Hv.
    pose proof (all_bytes _ Hcheck (byte_of x j) (byte_of_range x j)) as Hb.
    pose proof (all_bytes _ Hb (byte_of y j) (byte_of_range y j)) as H.
    cbn beta in H.
    destruct (sw_lane e (lane2 (byte_of x j) (byte_of y j)) (sw_zero e)); cbn [fst snd].
    apply andb_true_iff in H as [H Hc]. apply Z.eqb_eq in H.
    split; [exact H|]. intros Hg. rewrite Hg in Hc. exact Hc. }
  rewrite sw_ripple_zero by (try lia; intros; apply Hlane, Hgo; assumption).
  apply Hlane.
Qed.

(** ## Reifying emitted word expressions

    The emitted code often wraps an already wrapped value again.
    Reification removes these redundant wraps and records the arithmetic
    tree, while a separate proof checks that its low 64 bits agree. *)

(** Truncation distributes through bitwise operations, including when
    an input is negative or larger than an unsigned word. *)
Lemma sw_mod_land x y : Z.land x y mod 2 ^ 64 = Z.land (x mod 2 ^ 64) (y mod 2 ^ 64).
Proof.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.testbit_mod_pow2, !Z.land_spec, !Z.testbit_mod_pow2 by lia.
  destruct (n <? 64); reflexivity.
Qed.

(** Bitwise or preserves the low 64 bits when both inputs are truncated
    before the operation. *)
Lemma sw_mod_lor x y : Z.lor x y mod 2 ^ 64 = Z.lor (x mod 2 ^ 64) (y mod 2 ^ 64).
Proof.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.testbit_mod_pow2, !Z.lor_spec, !Z.testbit_mod_pow2 by lia.
  destruct (n <? 64); reflexivity.
Qed.

(** Exclusive-or also commutes with truncation at the word boundary. *)
Lemma sw_mod_lxor x y : Z.lxor x y mod 2 ^ 64 = Z.lxor (x mod 2 ^ 64) (y mod 2 ^ 64).
Proof.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.testbit_mod_pow2, !Z.lxor_spec, !Z.testbit_mod_pow2 by lia.
  destruct (n <? 64); reflexivity.
Qed.

(** These reductions keep computation separate from the structural
    traversal and the abstraction of the goal's byte function. *)
Ltac sw_eval t := eval vm_compute in t.
Ltac sw_reduce t := eval cbv in t.
Ltac sw_append ws t := eval cbn in (ws ++ [t]).
Ltac sw_abstract1 b r := eval pattern b in r.
Ltac sw_abstract2 b c r := eval pattern b, c in r.

(** The reifier recognizes repeated constants by their low byte and
    checks the entire word, rather than maintaining a table of constants. *)
Ltac sw_constant t :=
  let v := sw_reduce t in
  lazymatch v with
  | Z0 => constr:(SRep 0)
  | Zpos _ =>
      let b := sw_eval constr:(v mod 256) in
      let ok := sw_eval constr:(v mod 2 ^ 64 =? repeat_byte b) in
      lazymatch ok with true => constr:(SRep b) end
  | Zneg _ =>
      let b := sw_eval constr:(v mod 256) in
      let ok := sw_eval constr:(v mod 2 ^ 64 =? repeat_byte b) in
      lazymatch ok with true => constr:(SRep b) end
  end.

(** Input slots retain their first assigned index when the same word
    appears more than once in an expression. *)
Ltac sw_index t ws :=
  lazymatch ws with
  | t :: _ => constr:(O)
  | _ :: ?xs => let n := sw_index t xs in constr:(S n)
  end.

(** Collecting inputs before reification gives both children of every
    node the same input numbering. *)
Ltac sw_inputs t ws :=
  lazymatch t with
  | ?a mod 2 ^ 64 => sw_inputs a ws
  | Z.land ?a ?b => let xs := sw_inputs a ws in sw_inputs b xs
  | Z.lor ?a ?b => let xs := sw_inputs a ws in sw_inputs b xs
  | Z.lxor ?a ?b => let xs := sw_inputs a ws in sw_inputs b xs
  | ?a + ?b => let xs := sw_inputs a ws in sw_inputs b xs
  | ?a - ?b => let xs := sw_inputs a ws in sw_inputs b xs
  | _ => match t with
         | _ => let e := sw_constant t in constr:(ws)
         | _ => let n := sw_index t ws in constr:(ws)
         | _ => sw_append ws t
         end
  end.

(** The tactic translates each emitted operator into its matching tree
    node. It records other word terms as inputs for the checker. *)
Ltac sw_reify t ws :=
  lazymatch t with
  | ?a mod 2 ^ 64 => sw_reify a ws
  | Z.land ?a ?b => let ea := sw_reify a ws in let eb := sw_reify b ws in constr:(SAnd ea eb)
  | Z.lor ?a ?b => let ea := sw_reify a ws in let eb := sw_reify b ws in constr:(SOr ea eb)
  | Z.lxor ?a ?b => let ea := sw_reify a ws in let eb := sw_reify b ws in constr:(SXor ea eb)
  | ?a + ?b => let ea := sw_reify a ws in let eb := sw_reify b ws in constr:(SAdd ea eb)
  | ?a - ?b => let ea := sw_reify a ws in let eb := sw_reify b ws in constr:(SSub ea eb)
  | _ => match t with
         | _ => sw_constant t
         | _ => let n := sw_index t ws in constr:(SVar n)
         end
  end.

(** The tactic proves that the translated expression preserves the low
    64 bits. It checks each operator separately and computes constant values. *)
Ltac sw_reify_sound :=
  lazymatch goal with
  | |- (?a mod 2 ^ 64) mod 2 ^ 64 = _ => rewrite Z.mod_mod by lia; sw_reify_sound
  | |- ?t = sw_word ?ws (SAnd ?a ?b) =>
      change (t = Z.land (sw_word ws a) (sw_word ws b));
      rewrite sw_mod_land; f_equal; sw_reify_sound
  | |- ?t = sw_word ?ws (SOr ?a ?b) =>
      change (t = Z.lor (sw_word ws a) (sw_word ws b));
      rewrite sw_mod_lor; f_equal; sw_reify_sound
  | |- ?t = sw_word ?ws (SXor ?a ?b) =>
      change (t = Z.lxor (sw_word ws a) (sw_word ws b));
      rewrite sw_mod_lxor; f_equal; sw_reify_sound
  | |- ?t = sw_word ?ws (SAdd ?a ?b) =>
      change (t = (sw_word ws a + sw_word ws b) mod 2 ^ 64);
      rewrite Z.add_mod by lia; f_equal; f_equal; sw_reify_sound
  | |- ?t = sw_word ?ws (SSub ?a ?b) =>
      change (t = (sw_word ws a - sw_word ws b) mod 2 ^ 64);
      rewrite Zminus_mod; f_equal; f_equal; sw_reify_sound
  | |- _ = sw_word ?ws (SRep ?c) => abstract (vm_cast_no_check (eq_refl (repeat_byte (c mod 256))))
  | |- _ = sw_word ?ws (SVar ?n) => reflexivity
  end.

(** The lane tactic abstracts the desired byte function from the goal.
    It first tries the full checker, then the search checker with the
    supplied continuation condition or the usual nonzero-byte condition.
    Search goals with a constant answer should first expose their byte
    test, so the computed function describes all input bytes. *)
Ltac sw_lanes :=
  lazymatch goal with
  | |- byte_of ?t ?i = ?r =>
      let ws := sw_inputs t constr:(@nil Z) in
      let e := sw_reify t ws in
      let E := fresh "Hreify" in
      assert (E : t mod 2 ^ 64 = sw_word ws e) by sw_reify_sound;
      rewrite <- (byte_of_mod64 t i) by lia; rewrite E; clear E;
      lazymatch ws with
      | [?x] =>
          let f := sw_abstract1 constr:(byte_of x i) r in
          lazymatch f with ?g _ =>
            first [apply (sw_map1 e g); [abstract (vm_cast_no_check (eq_refl true)) | lia] |
              let go := match goal with
                | H : forall j, _ -> ?go (byte_of x j) = true |- _ => constr:(go)
                | _ => constr:(fun b => negb (b =? 0))
                end in
              apply (sw_map1_upto e go g);
              [abstract (vm_cast_no_check (eq_refl true)) | lia |
               intros; solve [eauto | cbn beta; apply negb_true_iff, Z.eqb_neq;
                 match goal with H : forall j, _ -> byte_of x j <> 0 |- _ => apply H; lia end]]]
          end
      | [?x; ?y] =>
          let f := sw_abstract2 constr:(byte_of x i) constr:(byte_of y i) r in
          lazymatch f with ?g _ _ =>
            first [apply (sw_map2 e g); [abstract (vm_cast_no_check (eq_refl true)) | lia] |
              match goal with H : forall j, _ -> ?go (byte_of x j) (byte_of y j) = true |- _ =>
                apply (sw_map2_upto e go g);
                [abstract (vm_cast_no_check (eq_refl true)) | lia | intros; apply H; lia]
              end]
          end
      end
  end.

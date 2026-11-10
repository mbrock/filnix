(** What NFB's Gallina reader and writer (NfbTerm.v, Nfb.v) are proved
    to do (docs/nfb.md, Relation to the term form and the Rocq model).

    - Canonical: the words [decode] takes are the words [encode_with]
      writes for the module it gives, CONTEXT and tools' sections
      aside ([decode_canonical]). So two lists of words that decode to
      one module, with NAMES in both or in neither, are the same words
      ([decode_identity]): the words are the module's identity.
    - Round trip: toward [decode (encode m) = Some m], the words of
      each kind of field read back as what was written: a signed
      64-bit or 96-bit integer ([i64_round_trip], [wide_round_trip]),
      an inline constant ([inline_round_trip]), and an enumeration's
      code ([codes_round_trip]). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Transport Cfg.
From Backend Require Import NfbTerm Nfb.
Import ListNotations.
Open Scope Z_scope.

(** ## Canonical form *)

(** [words_eqb] is equality of word lists. *)
Lemma words_eqb_eq : forall xs ys, words_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; simpl in H; try discriminate; auto.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst. f_equal. auto.
Qed.

(** Whether the reader finds a NAMES section in ws. *)
Definition names_of (ws : list Z) : bool :=
  match read_term ws with Some (_, b) => b | None => false end.

(** The words [decode] takes are exactly the words [encode_with]
    writes for the module it gives, with NAMES if they have it: no
    other spelling of a module is read. *)
Theorem decode_canonical : forall ws m,
  decode ws = Some m -> encode_with (names_of ws) m = module_words ws.
Proof.
  intros ws m H. unfold decode, names_of in *.
  destruct (read_term ws) as [[t b]|]; try discriminate. simpl in H.
  destruct (decode_module t) as [m0|]; try discriminate.
  destruct (encode_with b m0) as [ws1|] eqn:E1; try discriminate.
  destruct (module_words ws) as [ws2|]; try discriminate.
  destruct (words_eqb ws1 ws2) eqn:E3; try discriminate.
  injection H as <-. apply words_eqb_eq in E3. subst. exact E1.
Qed.

(** Two lists of words that [decode] reads as the same module, both
    with NAMES or both without, are the same words once CONTEXT and
    tools' sections are set aside: the module id the document defines
    over them is sound. *)
Corollary decode_identity : forall ws1 ws2 m,
  decode ws1 = Some m -> decode ws2 = Some m -> names_of ws1 = names_of ws2 ->
  module_words ws1 = module_words ws2.
Proof.
  intros ws1 ws2 m H1 H2 E.
  rewrite <- (decode_canonical _ _ H1), <- (decode_canonical _ _ H2), E. reflexivity.
Qed.

(** ## Words read back *)

(** A signed 64-bit integer, written as two words, reads back. *)
Lemma i64_round_trip : forall n, i64ok n = true ->
  match i64_words n with [lo; hi] => i64_of lo hi = n | _ => False end.
Proof.
  intros n H. unfold i64ok in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold i64_words, i64_of, two32, two64 in *.
  change (18446744073709551616 / 2) with 9223372036854775808 in *.
  set (u := n mod 18446744073709551616).
  assert (Hu : u mod 4294967296 + u / 4294967296 * 4294967296 = u).
  { pose proof (Z.div_mod u 4294967296). lia. }
  rewrite Hu. subst u.
  destruct (Z_lt_le_dec n 0) as [Hn | Hn].
  - rewrite <- (Z.mod_unique n 18446744073709551616 (-1) (n + 18446744073709551616)) by lia.
    destruct (Z.ltb_spec (n + 18446744073709551616) 9223372036854775808); lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec n 9223372036854775808); lia.
Qed.

(** A signed 96-bit integer, written as three words, reads back. *)
Lemma wide_round_trip : forall n, wideok n = true ->
  match wide_words n with [w0; w1; w2] => wide_of w0 w1 w2 = n | _ => False end.
Proof.
  intros n H. unfold wideok in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold wide_words, wide_of, two32, two64, two96 in *.
  change (79228162514264337593543950336 / 2) with 39614081257132168796771975168 in *.
  set (u := n mod 79228162514264337593543950336).
  assert (Hr : 0 <= u < 79228162514264337593543950336) by (apply Z.mod_pos_bound; lia).
  assert (Hu : u mod 4294967296 + (u / 4294967296) mod 4294967296 * 4294967296
               + u / 18446744073709551616 * 18446744073709551616 = u).
  { pose proof (Z.div_mod u 4294967296 ltac:(lia)).
    pose proof (Z.div_mod (u / 4294967296) 4294967296 ltac:(lia)).
    rewrite Z.div_div in * by lia. change (4294967296 * 4294967296) with 18446744073709551616 in *.
    lia. }
  rewrite Hu. subst u.
  destruct (Z_lt_le_dec n 0) as [Hn | Hn].
  - rewrite <- (Z.mod_unique n 79228162514264337593543950336 (-1)
               (n + 79228162514264337593543950336)) by lia.
    destruct (Z.ltb_spec (n + 79228162514264337593543950336)
                39614081257132168796771975168); lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec n 39614081257132168796771975168); lia.
Qed.

(** An inline constant's operand word reads back as the constant,
    whatever the tables: tag 1, the constant in the payload. *)
Lemma inline_round_trip : forall r c n,
  inline n = true -> exists z, const_word c n = Some z /\ const_of r z = Some n.
Proof.
  intros r c n H. unfold const_word. rewrite H. eexists. split; [reflexivity|].
  unfold inline, inline_bound in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold const_of, inline_bound.
  set (p := n mod (2 * 536870912)).
  assert (Hp : 0 <= p < 2 * 536870912) by (apply Z.mod_pos_bound; lia).
  replace ((p * 4 + 1) mod 4) with 1 by (rewrite Z.add_comm, Z.mod_add; reflexivity || lia).
  replace ((p * 4 + 1) / 4) with p by (rewrite Z.add_comm, Z.div_add by lia; reflexivity).
  simpl. f_equal. subst p.
  destruct (Z_lt_le_dec n 0) as [Hn | Hn].
  - rewrite <- (Z.mod_unique n (2 * 536870912) (-1) (n + 2 * 536870912)) by lia.
    destruct (Z.ltb_spec (n + 2 * 536870912) 536870912); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec n 536870912); lia.
Qed.

(** Whether each key and each value of the table xs occurs once. *)
Definition table_ok (xs : list (string * Z)) : Prop :=
  NoDup (map fst xs) /\ NoDup (map snd xs).

(** A table whose keys and values each occur once gives back the key
    of the value of a key. *)
Lemma assoc_round_trip : forall xs s z,
  table_ok xs -> sassoc s xs = Some z -> srassoc z xs = Some s.
Proof.
  induction xs as [|[k v] xs IH]; intros s z [Hk Hv] H; simpl in *; try discriminate.
  inversion Hk as [|? ? Hk1 Hk2]; inversion Hv as [|? ? Hv1 Hv2]; subst.
  destruct (String.eqb_spec s k) as [<- | Hne].
  - injection H as <-. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec z v) as [-> | _].
    + exfalso. apply Hv1. clear -H. induction xs as [|[k' v'] xs IHx]; simpl in *; try discriminate.
      destruct (String.eqb s k'); [injection H as ->; left; reflexivity | right; auto].
    + apply IH; [split|]; assumption.
Qed.

(** Every enumeration's table has each atom once and each code once. *)
Lemma codes_ok : forall e, table_ok (codes e).
Proof.
  intros e; destruct e; split; simpl;
    repeat (constructor; [simpl; intuition discriminate |]); constructor.
Qed.

(** The code of an atom in an enumeration reads back as the atom. *)
Lemma codes_round_trip : forall e t z, enc_code e t = Some z -> dec_code e z = Some t.
Proof.
  intros e t z H. destruct t as [| s | |]; simpl in H; try discriminate.
  unfold dec_code. rewrite (assoc_round_trip _ _ _ (codes_ok e) H). reflexivity.
Qed.

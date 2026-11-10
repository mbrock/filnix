(** What NFB's Gallina reader and writer (NfbTerm.v, Nfb.v) are proved
    to do (docs/nfb.md, Relation to the term form and the Rocq model).

    - Canonical: the words [decode] takes are the words [encode_with]
      writes for the module it gives, CONTEXT and tools' sections
      aside ([decode_canonical]). So two lists of words that decode to
      one module, with NAMES in both or in neither, are the same words
      ([decode_identity]): the words are the module's identity.
    - Round trip: a module that Transport.v's [decode_module] gives is
      read back from its words as itself ([round_trip]). Its two
      halves are that the term reader gives back what the term writer
      wrote (NfbRead.v, [read_encode_term]) and that [decode_module]
      reads [enc_module m] as m (NfbTransport.v, [decode_enc_module]). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Transport Cfg.
From Backend Require Import NfbTerm Nfb NfbRead NfbTransport.
Import ListNotations.
Open Scope Z_scope.

(** ## Canonical form *)

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

(** ## Round trip *)

(** A list of words is equal to itself by [words_eqb]. *)
Lemma words_eqb_refl : forall xs, words_eqb xs xs = true.
Proof. induction xs as [|x xs IH]; simpl; [reflexivity|]. rewrite Z.eqb_refl. exact IH. Qed.

(** A module that [decode_module] reads from a term, once written as
    words, is read back as itself, NAMES included. *)
Theorem round_trip : forall t m ws,
  decode_module t = Some m -> encode m = Some ws -> decode ws = Some m.
Proof.
  intros t m ws Hd He. unfold encode, encode_with in He.
  destruct (read_encode_term _ _ He) as [b [Hr [Hb Hw]]].
  unfold decode. rewrite Hr. cbn [fst snd].
  rewrite (decode_enc_module _ _ Hd). unfold encode_with. rewrite Hb, Hw, words_eqb_refl.
  reflexivity.
Qed.

(** [decode_input], the reader without [decode]'s check, reads a
    module back as itself too. *)
Theorem input_round_trip : forall t m ws,
  decode_module t = Some m -> encode m = Some ws -> decode_input ws = Some m.
Proof.
  intros t m ws Hd He. unfold encode, encode_with in He.
  destruct (read_encode_term _ _ He) as [b [Hr _]].
  unfold decode_input. rewrite Hr. cbn [fst]. exact (decode_enc_module _ _ Hd).
Qed.

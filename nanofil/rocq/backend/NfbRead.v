(** NFB's term reader gives back what its writer wrote (NfbTerm.v,
    docs/nfb.md): for every module term t that [encode_term] writes
    with NAMES, [read_term] reads the words back as t itself, says
    whether they had NAMES, and those are words [encode_term] writes
    for t with that answer, which [module_words] keeps whole
    ([read_encode_term]).

    The proof goes up in layers. First the words: integers written as
    two or three words, inline constants, codes, tables numbered by
    [number] and read by [index_map], sorted string tables, bytes
    packed four to a word, and sections. Then one instruction: a term
    matched by its form's pattern is filled again from the holes its
    fields read back, given the reader's tables invert the writer's.
    The facts about the [forms] table, such as distinct opcodes and
    every hole read by a field, are checked once by computation. Then
    the groups of a block, the blocks and the body of a function, its
    temporaries named in the order of their first definitions; the
    data items, the side section of names, the items, and the
    module. *)

From Stdlib Require Import String ZArith List Bool Ascii Lia Sorted.
From Nanofil Require Import Term Maps Cfg.
From Backend Require Import Order NfbTerm.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** ## Words *)

(** [words_eqb] is equality of word lists. *)
Lemma words_eqb_eq : forall xs ys, words_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; simpl in H; try discriminate; auto.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst. f_equal. auto.
Qed.

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

(** A class's code is from 1 to 8. *)
Lemma class_code_range : forall t z, enc_code EClass t = Some z -> 1 <= z <= 8.
Proof.
  intros t z H. destruct t as [| s | |]; simpl in H; try discriminate.
  unfold sassoc, class_codes in H.
  repeat (destruct (String.eqb s _); [injection H as <-; lia |]). discriminate.
Qed.

(** The two words of a signed 64-bit integer, read as two words. *)
Lemma i64_words_rt : forall n, i64ok n = true ->
  exists lo hi, i64_words n = [lo; hi] /\ i64_of lo hi = n.
Proof.
  intros n H. pose proof (i64_round_trip n H) as R.
  destruct (i64_words n) as [|lo [|hi [|]]]; try contradiction. eauto.
Qed.

(** The three words of a signed 96-bit integer. *)
Lemma wide_words_rt : forall n, wideok n = true ->
  exists a b c, wide_words n = [a; b; c] /\ wide_of a b c = n.
Proof.
  intros n H. pose proof (wide_round_trip n H) as R.
  destruct (wide_words n) as [|a [|b [|c [|]]]]; try contradiction. eauto.
Qed.

(** ## Small facts *)

(** The arguments [app_args] finds are those of the compound. *)
Lemma app_args_inv : forall f n t ts, app_args f n t = Some ts -> t = TApp f ts /\ length ts = n.
Proof.
  intros f n t ts H. destruct t as [| | g us |]; simpl in H; try discriminate.
  destruct (String.eqb_spec f g); [|discriminate]. destruct (Nat.eqb_spec n (length us)); [|discriminate].
  injection H as <-. subst. auto.
Qed.

(** The atom [is_atom] recognizes. *)
Lemma is_atom_inv : forall a t, is_atom a t = true -> t = TAtom a.
Proof.
  intros a t H. destruct t; simpl in H; try discriminate. apply String.eqb_eq in H. subst. reflexivity.
Qed.

(** [mapo] relates each element to its image. *)
Lemma mapo_forall2 : forall {X Y} (f : X -> option Y) xs ys,
  mapo f xs = Some ys -> Forall2 (fun x y => f x = Some y) xs ys.
Proof.
  intros X Y f. induction xs as [|x xs IH]; intros ys H; simpl in H.
  - injection H as <-. constructor.
  - destruct (f x) eqn:E; [|discriminate]. destruct (mapo f xs) eqn:E2; [|discriminate].
    injection H as <-. constructor; auto.
Qed.

(** [mapo] over two lists joined. *)
Lemma mapo_app : forall {X Y} (f : X -> option Y) xs ys zs, mapo f (xs ++ ys) = Some zs ->
  exists as_ bs, zs = as_ ++ bs /\ mapo f xs = Some as_ /\ mapo f ys = Some bs.
Proof.
  intros X Y f. induction xs as [|x xs IH]; intros ys zs H; simpl in *.
  - exists [], zs. auto.
  - destruct (f x) eqn:E; [|discriminate]. destruct (mapo f (xs ++ ys)) eqn:E2; [|discriminate].
    injection H as <-. destruct (IH _ _ E2) as (a & b & -> & H1 & H2).
    exists (y :: a), b. rewrite H1. auto.
Qed.

(** [mapo] gives as many images as elements. *)
Lemma mapo_length : forall {X Y} (f : X -> option Y) xs ys, mapo f xs = Some ys -> length ys = length xs.
Proof. intros. apply mapo_forall2 in H. eapply Forall2_length in H. auto. Qed.

(** [take_acc] the first part of two joined lists, after what it took. *)
Lemma take_acc_app : forall xs ys acc, take_acc (length xs) (xs ++ ys) acc = Some (rev acc ++ xs, ys).
Proof.
  induction xs as [|x xs IH]; intros ys acc; cbn [length app take_acc].
  - rewrite rev_append_rev. reflexivity.
  - rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

(** [take] the first part of two joined lists. *)
Lemma take_app : forall xs ys, take (length xs) (xs ++ ys) = Some (xs, ys).
Proof. intros xs ys. unfold take. rewrite take_acc_app. reflexivity. Qed.

(** An integer that [take] counts. *)
Lemma take_app_z : forall xs ys, take (Z.to_nat (Z.of_nat (length xs))) (xs ++ ys) = Some (xs, ys).
Proof. intros. rewrite Nat2Z.id. apply take_app. Qed.

(** [at_least] n is whether there are n words or more. *)
Lemma at_least_len : forall n xs, at_least n xs = Nat.leb n (length xs).
Proof. induction n as [|n IH]; intros [|x xs]; simpl; auto. Qed.

(** [at_least] of a count, as a comparison of integers. *)
Lemma at_least_spec : forall n xs, at_least (Z.to_nat n) xs = negb (Z.of_nat (length xs) <? n).
Proof.
  intros n xs. rewrite at_least_len. destruct (Nat.leb_spec (Z.to_nat n) (length xs));
    destruct (Z.ltb_spec (Z.of_nat (length xs)) n); simpl; reflexivity || lia.
Qed.

(** A ZMap lookup after an add. *)
Lemma zfind_add : forall {A} k k' (v : A) m,
  ZMap.find k (ZMap.add k' v m) = if Z.eqb k' k then Some v else ZMap.find k m.
Proof.
  intros. destruct (Z.eqb_spec k' k) as [E|E].
  - apply ZF.add_eq_o. exact E.
  - apply ZF.add_neq_o. exact E.
Qed.

(** A lookup in the empty ZMap. *)
Lemma zfind_empty : forall {A} k, ZMap.find k (ZMap.empty A) = None.
Proof. intros. apply ZF.empty_o. Qed.

(** ## Tables *)

(** [index_map]'s fold leaves the keys below its start alone. *)
Lemma imap_below : forall {X} (xs : list X) m n i, i < n ->
  ZMap.find i (fst (fold_left (fun p x => (ZMap.add (snd p) x (fst p), snd p + 1)) xs (m, n)))
  = ZMap.find i m.
Proof.
  intros X xs. induction xs as [|y ys IH]; intros m n i H; simpl; [reflexivity|].
  rewrite IH by lia. rewrite zfind_add. destruct (Z.eqb_spec n i); [lia|reflexivity].
Qed.

(** [index_map]'s fold maps the key n + k to the k-th element. *)
Lemma imap_at : forall {X} (xs : list X) m n i x, n <= i ->
  nth_error xs (Z.to_nat (i - n)) = Some x ->
  ZMap.find i (fst (fold_left (fun p x => (ZMap.add (snd p) x (fst p), snd p + 1)) xs (m, n)))
  = Some x.
Proof.
  intros X xs. induction xs as [|y ys IH]; intros m n i x H1 H2; simpl.
  - destruct (Z.to_nat (i - n)); discriminate.
  - destruct (Z.eqb_spec i n) as [->|E].
    + rewrite Z.sub_diag in H2. simpl in H2. injection H2 as ->.
      rewrite imap_below by lia. rewrite zfind_add, Z.eqb_refl. reflexivity.
    + apply IH; [lia|]. replace (Z.to_nat (i - n)) with (S (Z.to_nat (i - (n + 1)))) in H2 by lia.
      exact H2.
Qed.

(** [index_map] maps i to the i-th element. *)
Lemma index_map_nth : forall {X} (xs : list X) i x, 0 <= i ->
  nth_error xs (Z.to_nat i) = Some x -> ZMap.find i (index_map xs) = Some x.
Proof. intros. unfold index_map. apply imap_at; [lia|]. rewrite Z.sub_0_r. assumption. Qed.

(** The table of wide constants maps a constant to an index of it. *)
Lemma cmap_find : forall (xs : list Z) m n c i,
  ZMap.find c (fst (fold_left (fun p c => (ZMap.add c (snd p) (fst p), snd p + 1)) xs (m, n)))
  = Some i ->
  ZMap.find c m = Some i \/ (n <= i /\ nth_error xs (Z.to_nat (i - n)) = Some c).
Proof.
  induction xs as [|y ys IH]; intros m n c i H; simpl in H; [left; exact H|].
  destruct (IH _ _ _ _ H) as [H1 | [H1 H2]].
  - rewrite zfind_add in H1. destruct (Z.eqb_spec y c) as [<-|E].
    + injection H1 as <-. right. split; [lia|]. rewrite Z.sub_diag. reflexivity.
    + left. exact H1.
  - right. split; [lia|]. replace (Z.to_nat (i - n)) with (S (Z.to_nat (i - (n + 1)))) by lia.
    exact H2.
Qed.

(** [number] never renumbers a name. *)
Lemma number_keep : forall xs m n acc x i, nm_find x m = Some i ->
  nm_find x (fst (fst (number xs m n acc))) = Some i.
Proof.
  induction xs as [|y ys IH]; intros m n acc x i H; simpl; [exact H|].
  destruct (nm_mem y m) eqn:E; apply IH; [exact H|].
  rewrite nm_find_add. destruct (name_eqb x y) eqn:Exy; [|exact H].
  apply term_eqb_eq in Exy. subst. unfold nm_mem in E. rewrite H in E. discriminate.
Qed.

(** What [number] makes: the names newly numbered come after those
    numbered before, each name's number is its place in the list of
    both, and the count is that list's length. *)
Lemma number_spec : forall xs m n acc (L0 : list term),
  (forall (x : term) i, nm_find x m = Some i -> 0 <= i /\ nth_error (L0 ++ rev acc) (Z.to_nat i) = Some x) ->
  n = Z.of_nat (length (L0 ++ rev acc)) ->
  forall m' n' F, number xs m n acc = (m', n', F) ->
  exists nw, F = rev acc ++ nw /\
    (forall (x : term) i, nm_find x m' = Some i -> 0 <= i /\ nth_error (L0 ++ F) (Z.to_nat i) = Some x) /\
    n' = Z.of_nat (length (L0 ++ F)) /\
    (forall x, In x xs -> nm_mem x m' = true) /\
    (length nw <= length xs)%nat /\ (length nw = length xs -> nw = xs).
Proof.
  induction xs as [|y ys IH]; intros m n acc L0 Hm Hn m' n' F E; simpl in E.
  - injection E as <- <- <-. exists []. rewrite app_nil_r.
    split; [reflexivity|]. split; [exact Hm|]. split; [exact Hn|]. split; [intros x []|].
    split; [simpl; lia | reflexivity].
  - pose proof (number_keep ys) as K.
    destruct (nm_mem y m) eqn:Ey.
    + destruct (IH m n acc L0 Hm Hn m' n' F E) as (nw & HF & H1 & H2 & H3 & H4 & H5).
      exists nw. split; [exact HF|]. split; [exact H1|]. split; [exact H2|]. split.
      * intros x [<-|Hx]; [|auto]. unfold nm_mem in Ey |- *.
        destruct (nm_find y m) as [i|] eqn:Ex; [|discriminate].
        specialize (K m n acc y i Ex). rewrite E in K. simpl in K. rewrite K. reflexivity.
      * split; [simpl; lia | intros Hl; simpl in Hl; lia].
    + assert (Hm' : forall (x : term) i, nm_find x (nm_add y n m) = Some i ->
                    0 <= i /\ nth_error (L0 ++ rev (y :: acc)) (Z.to_nat i) = Some x).
      { intros x i Hx. rewrite nm_find_add in Hx. simpl. rewrite app_assoc.
        destruct (name_eqb x y) eqn:Exy.
        - injection Hx as <-. apply term_eqb_eq in Exy. subst x. split; [lia|].
          rewrite Hn, Nat2Z.id, nth_error_app2 by apply Nat.le_refl. rewrite Nat.sub_diag. reflexivity.
        - destruct (Hm x i Hx) as [H0 H1]. split; [exact H0|].
          rewrite nth_error_app1; [exact H1|]. apply nth_error_Some. rewrite H1. discriminate. }
      assert (Hn' : n + 1 = Z.of_nat (length (L0 ++ rev (y :: acc)))).
      { simpl. rewrite app_assoc, length_app. simpl. lia. }
      destruct (IH _ _ _ L0 Hm' Hn' m' n' F E) as (nw & HF & H1 & H2 & H3 & H4 & H5).
      exists (y :: nw). simpl in HF. rewrite <- app_assoc in HF.
      split; [exact HF|]. split; [exact H1|]. split; [exact H2|]. split.
      * intros x [<-|Hx]; [|auto]. unfold nm_mem.
        specialize (K (nm_add y n m) (n + 1) (y :: acc) y n).
        rewrite nm_find_add in K. unfold name_eqb in K. rewrite term_eqb_refl in K.
        rewrite E in K. simpl in K. rewrite K by reflexivity. reflexivity.
      * split; [simpl; lia|]. intros Hl. simpl in Hl. f_equal. apply H5. lia.
Qed.

(** [number] from nothing: each name's number is its place among the
    names newly numbered. *)
Lemma number_fresh : forall xs m n F, number xs nm_empty 0 [] = (m, n, F) ->
  (forall (x : term) i, nm_find x m = Some i -> 0 <= i /\ nth_error F (Z.to_nat i) = Some x) /\
  n = Z.of_nat (length F) /\ (length F <= length xs)%nat /\ (length F = length xs -> F = xs) /\
  (forall x, In x xs -> nm_mem x m = true).
Proof.
  intros xs m n F E.
  assert (H0 : forall (x : term) i, nm_find x (@nm_empty Z) = Some i ->
               0 <= i /\ nth_error ([] ++ rev []) (Z.to_nat i) = Some x).
  { intros x i H. rewrite nm_find_empty in H. discriminate. }
  destruct (number_spec xs nm_empty 0 [] [] H0 eq_refl m n F E) as (nw & HF & H1 & H2 & H3 & H4 & H5).
  simpl in HF. subst F. simpl in *. auto.
Qed.

(** Names that differ are all numbered anew, in order. *)
Lemma number_nodup : forall xs m n acc, NoDup xs -> (forall x, In x xs -> nm_mem x m = false) ->
  snd (number xs m n acc) = rev acc ++ xs.
Proof.
  induction xs as [|y ys IH]; intros m n acc Hd Hm; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite (Hm y (or_introl eq_refl)). inversion Hd as [|? ? Hy Hys]; subst.
    rewrite IH; [simpl; rewrite <- app_assoc; reflexivity | exact Hys |].
    intros x Hx. rewrite nm_mem_add. destruct (name_eqb x y) eqn:E.
    + apply term_eqb_eq in E. subst. contradiction.
    + simpl. apply Hm. right. exact Hx.
Qed.

(** Distinct names numbered from nothing: the number of each is its
    place in the list. *)
Lemma number_ids : forall xs m n F, NoDup xs -> number xs nm_empty 0 [] = (m, n, F) ->
  F = xs /\ (forall (x : term) i, nm_find x m = Some i -> 0 <= i /\ nth_error xs (Z.to_nat i) = Some x).
Proof.
  intros xs m n F Hd E.
  assert (HF : F = xs).
  { pose proof (number_nodup xs nm_empty 0 [] Hd) as H. rewrite E in H. apply H.
    intros x _. unfold nm_mem. rewrite nm_find_empty. reflexivity. }
  subst F. destruct (number_fresh _ _ _ _ E) as (H1 & _). auto.
Qed.

(** Names numbered from nothing, as many as the names: they differ,
    and each one's number is its place. *)
Lemma number_count : forall xs m n F, number xs nm_empty 0 [] = (m, n, F) -> n = Z.of_nat (length xs) ->
  F = xs /\ (forall (x : term) i, nm_find x m = Some i -> 0 <= i /\ nth_error xs (Z.to_nat i) = Some x).
Proof.
  intros xs m n F E Hn. destruct (number_fresh _ _ _ _ E) as (H1 & H2 & H3 & H4 & H5).
  assert (F = xs) by (apply H4; lia). subst. auto.
Qed.

(** The places that [nth_error] finds for two names in a list without
    duplicates differ when the names do. *)
Lemma nth_error_nodup : forall {X} (xs : list X) i j x, NoDup xs ->
  nth_error xs i = Some x -> nth_error xs j = Some x -> i = j.
Proof.
  intros X xs i j x Hd Hi Hj. eapply NoDup_nth_error; eauto.
  apply nth_error_Some. rewrite Hi. discriminate. congruence.
Qed.

(** ## Sorted tables *)

Section Sort.
Variable X : Type.
Variables (lt eqb : X -> X -> bool).
Hypothesis eqb_true : forall x y, eqb x y = true <-> x = y.
Hypothesis lt_irrefl : forall x, lt x x = false.
Hypothesis lt_trans : forall x y z, lt x y = true -> lt y z = true -> lt x z = true.
Hypothesis lt_total : forall x y, eqb x y = false -> lt x y = false -> lt y x = true.

(** One step of [merge_uniq] on two lists that are not empty. *)
Lemma merge_uniq_cons : forall x xs y ys, merge_uniq lt eqb (x :: xs) (y :: ys) =
  if eqb x y then x :: merge_uniq lt eqb xs ys
  else if lt x y then x :: merge_uniq lt eqb xs (y :: ys) else y :: merge_uniq lt eqb (x :: xs) ys.
Proof. reflexivity. Qed.

(** [merge_uniq] with an empty side. *)
Lemma merge_uniq_nil : forall xs, merge_uniq lt eqb xs [] = xs /\ merge_uniq lt eqb [] xs = xs.
Proof. intros [|x xs]; split; reflexivity. Qed.

(** Every element of a merge is an element of one side. *)
Lemma merge_in : forall xs ys z, In z (merge_uniq lt eqb xs ys) -> In z xs \/ In z ys.
Proof.
  induction xs as [|x xs IHx]; intros ys z H.
  - rewrite (proj2 (merge_uniq_nil ys)) in H. auto.
  - induction ys as [|y ys IHy].
    + rewrite (proj1 (merge_uniq_nil _)) in H. auto.
    + rewrite merge_uniq_cons in H.
      destruct (eqb x y); [|destruct (lt x y)]; destruct H as [<-|H]; simpl; auto.
      * destruct (IHx _ _ H); auto.
      * destruct (IHx _ _ H); auto.
      * destruct (IHy H) as [H1|H1]; simpl in H1; auto.
Qed.

(** The merge of two strictly sorted lists is strictly sorted. *)
Lemma merge_sorted : forall xs ys, StronglySorted (fun a b => lt a b = true) xs ->
  StronglySorted (fun a b => lt a b = true) ys ->
  StronglySorted (fun a b => lt a b = true) (merge_uniq lt eqb xs ys).
Proof.
  induction xs as [|x xs IHx]; intros ys Hx Hy.
  - rewrite (proj2 (merge_uniq_nil ys)). exact Hy.
  - induction ys as [|y ys IHy].
    + rewrite (proj1 (merge_uniq_nil _)). exact Hx.
    + apply StronglySorted_inv in Hx as Hx'. destruct Hx' as [Hxs Fx].
      apply StronglySorted_inv in Hy as Hy'. destruct Hy' as [Hys Fy].
      rewrite Forall_forall in Fx, Fy. rewrite merge_uniq_cons.
      destruct (eqb x y) eqn:E1; [|destruct (lt x y) eqn:E2].
      * apply eqb_true in E1. subst y. constructor; [auto|].
        apply Forall_forall. intros z Hz. destruct (merge_in _ _ _ Hz); auto.
      * constructor; [auto|]. apply Forall_forall. intros z Hz.
        destruct (merge_in _ _ _ Hz) as [H|[<-|H]]; eauto.
      * pose proof (lt_total _ _ E1 E2) as E3. constructor; [auto|]. apply Forall_forall. intros z Hz.
        destruct (merge_in _ _ _ Hz) as [[<-|H]|H]; eauto.
Qed.

(** Merging the runs in pairs keeps each strictly sorted, and leaves
    fewer of them. *)
Lemma merge_pairs_sorted : forall rs, Forall (StronglySorted (fun a b => lt a b = true)) rs ->
  Forall (StronglySorted (fun a b => lt a b = true)) (merge_pairs lt eqb rs)
  /\ (2 * length (merge_pairs lt eqb rs) <= length rs + 1)%nat.
Proof.
  fix IH 1. intros [|r1 [|r2 rs]] H; simpl; [auto | split; [exact H | lia] |].
  inversion H as [|? ? H1 H']; subst. inversion H' as [|? ? H2 H'']; subst.
  destruct (IH rs H'') as [A B]. split; [constructor; [apply merge_sorted; auto | exact A] | lia].
Qed.

(** With enough rounds, merging leaves one strictly sorted run. *)
Lemma merge_all_sorted : forall fuel rs, Forall (StronglySorted (fun a b => lt a b = true)) rs ->
  (length rs <= S fuel)%nat -> StronglySorted (fun a b => lt a b = true) (merge_all lt eqb fuel rs).
Proof.
  induction fuel as [|f IH]; intros [|r1 [|r2 rs]] H Hl; simpl in *; try constructor;
    try (inversion H; assumption); try lia.
  destruct (merge_pairs_sorted (r1 :: r2 :: rs) H) as [A B].
  apply IH; [exact A|]. simpl in B |- *. lia.
Qed.

(** [sort_uniq] gives a strictly sorted list. *)
Lemma sort_uniq_sorted : forall xs, StronglySorted (fun a b => lt a b = true) (sort_uniq lt eqb xs).
Proof.
  intros xs. unfold sort_uniq. apply merge_all_sorted.
  - unfold singletons. induction xs; simpl; constructor; auto. repeat constructor.
  - unfold singletons. rewrite length_map. lia.
Qed.

(** [sort_uniq] gives each element once. *)
Lemma sort_uniq_nodup : forall xs, NoDup (sort_uniq lt eqb xs).
Proof.
  intros xs. pose proof (sort_uniq_sorted xs) as H. induction H as [|a l _ IH F]; constructor; auto.
  intros Ha. rewrite Forall_forall in F. specialize (F a Ha). rewrite lt_irrefl in F. discriminate.
Qed.

End Sort.

(** Strings compare equal to themselves. *)
Lemma string_compare_refl : forall s, String.compare s s = Eq.
Proof.
  induction s as [|c s IH]; simpl; [reflexivity|].
  unfold Ascii.compare. rewrite N.compare_refl. exact IH.
Qed.

(** The order of strings is transitive. *)
Lemma string_lt_trans : forall a b c,
  String.compare a b = Lt -> String.compare b c = Lt -> String.compare a c = Lt.
Proof.
  induction a as [|x a IH]; intros [|y b] [|z c]; cbn [String.compare]; try discriminate; auto.
  unfold Ascii.compare.
  destruct (N.compare_spec (N_of_ascii x) (N_of_ascii y)) as [E1|E1|E1]; try discriminate;
  destruct (N.compare_spec (N_of_ascii y) (N_of_ascii z)) as [E2|E2|E2]; try discriminate; intros H1 H2.
  - rewrite E1, E2, N.compare_refl. eauto.
  - rewrite E1. rewrite (proj2 (N.compare_lt_iff _ _) E2). reflexivity.
  - rewrite <- E2. rewrite (proj2 (N.compare_lt_iff _ _) E1). reflexivity.
  - rewrite (proj2 (N.compare_lt_iff _ _) (N.lt_trans _ _ _ E1 E2)). reflexivity.
Qed.

(** A sorted table of strings has each string once. *)
Lemma sort_strings_nodup : forall xs, NoDup (sort_uniq str_lt String.eqb xs).
Proof.
  apply sort_uniq_nodup.
  - apply String.eqb_eq.
  - intros x. unfold str_lt, atom_compare. rewrite string_compare_refl. reflexivity.
  - unfold str_lt, atom_compare. intros x y z H1 H2.
    destruct (String.compare x y) eqn:E1; try discriminate.
    destruct (String.compare y z) eqn:E2; try discriminate.
    rewrite (string_lt_trans _ _ _ E1 E2). reflexivity.
  - unfold str_lt, atom_compare. intros x y H1 H2.
    rewrite String.compare_antisym. destruct (String.compare x y) eqn:E; try discriminate; auto.
    apply String.compare_eq_iff in E. subst. rewrite String.eqb_refl in H1. discriminate.
Qed.

(** The atoms of distinct strings are distinct. *)
Lemma nodup_atoms : forall ss, NoDup ss -> NoDup (map TAtom ss).
Proof.
  intros ss H. induction H as [|a l Ha _ IH]; simpl; constructor; auto.
  intros Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as ->. contradiction.
Qed.

(** ## Bytes *)

(** A byte: from 0 to 255. *)
Definition byte (b : Z) : Prop := 0 <= b < 256.

(** The four bytes of a packed word come back. *)
Lemma byte_word : forall b0 b1 b2 b3, byte b0 -> byte b1 -> byte b2 -> byte b3 ->
  (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) mod 256 = b0 /\
  ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256) mod 256 = b1 /\
  ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 65536) mod 256 = b2 /\
  (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 16777216 = b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold byte in *. split; [|split; [|split]].
  - symmetry. apply (Z.mod_unique _ _ (b1 + b2 * 256 + b3 * 65536)); lia.
  - rewrite <- (Z.div_unique _ 256 (b1 + b2 * 256 + b3 * 65536) b0) by lia.
    symmetry. apply (Z.mod_unique _ _ (b2 + b3 * 256)); lia.
  - rewrite <- (Z.div_unique _ 65536 (b2 + b3 * 256) (b0 + b1 * 256)) by lia.
    symmetry. apply (Z.mod_unique _ _ b3); lia.
  - symmetry. apply (Z.div_unique _ _ _ (b0 + b1 * 256 + b2 * 65536)); lia.
Qed.

(** Bytes packed and unpacked come back first, and the packed words
    are a quarter as many, rounded up. *)
Lemma unpack_pack : forall bs, Forall byte bs ->
  firstn (length bs) (unpack (pack bs)) = bs /\
  (length bs <= 4 * length (pack bs) < length bs + 4)%nat.
Proof.
  fix IH 1. intros [|b0 [|b1 [|b2 [|b3 r]]]] H; [simpl; split; [reflexivity | lia] | | | |];
    inversion H as [|? ? Hb0 H1]; subst; try (inversion H1 as [|? ? Hb1 H2]; subst);
    try (inversion H2 as [|? ? Hb2 H3]; subst); try (inversion H3 as [|? ? Hb3 H4]; subst).
  - assert (Hz : byte 0) by (unfold byte; lia).
    destruct (byte_word b0 0 0 0 Hb0 Hz Hz Hz) as (A & _).
    simpl. replace (b0 + 0 * 256 + 0 * 65536 + 0 * 16777216) with b0 in A by ring.
    rewrite A. split; [reflexivity | lia].
  - assert (Hz : byte 0) by (unfold byte; lia).
    destruct (byte_word b0 b1 0 0 Hb0 Hb1 Hz Hz) as (A & B & _).
    simpl. replace (b0 + b1 * 256 + 0 * 65536 + 0 * 16777216) with (b0 + b1 * 256) in A, B by ring.
    rewrite A, B. split; [reflexivity | lia].
  - assert (Hz : byte 0) by (unfold byte; lia).
    destruct (byte_word b0 b1 b2 0 Hb0 Hb1 Hb2 Hz) as (A & B & C & _).
    simpl. replace (b0 + b1 * 256 + b2 * 65536 + 0 * 16777216) with (b0 + b1 * 256 + b2 * 65536)
      in A, B, C by ring.
    rewrite A, B, C. split; [reflexivity | lia].
  - destruct (byte_word b0 b1 b2 b3 Hb0 Hb1 Hb2 Hb3) as (A & B & C & D).
    destruct (IH r H4) as [E F]. simpl. rewrite A, B, C, D, E. split; [reflexivity | lia].
Qed.

(** A byte string's words read back. *)
Lemma read_bytes_rt : forall bs rest, Forall byte bs ->
  read_bytes (bytes_words bs ++ rest) = Some (bs, rest).
Proof.
  intros bs rest H. destruct (unpack_pack bs H) as [A B].
  unfold read_bytes, bytes_words. simpl app. cbv beta iota.
  replace (Z.to_nat ((Z.of_nat (length bs) + 3) / 4)) with (length (pack bs)).
  - rewrite at_least_len, length_app.
    replace ((Z.of_nat (length bs) <? 0) || negb (Nat.leb (length (pack bs)) (length (pack bs) + length rest)))
      with false by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge; lia|];
                     apply negb_false_iff, Nat.leb_le; lia).
    rewrite take_app. simpl. rewrite Nat2Z.id, A. reflexivity.
  - rewrite <- (Z.div_unique (Z.of_nat (length bs) + 3) 4 (Z.of_nat (length (pack bs)))
                 (Z.of_nat (length bs) + 3 - 4 * Z.of_nat (length (pack bs)))) by lia.
    lia.
Qed.

(** The bytes of a string are bytes. *)
Lemma string_bytes_byte : forall s, Forall byte (string_bytes s).
Proof.
  intros s. unfold string_bytes. apply Forall_forall. intros b Hb. apply in_map_iff in Hb.
  destruct Hb as (c & <- & _). pose proof (nat_ascii_bounded c). unfold byte. lia.
Qed.

(** A string's bytes give the string back. *)
Lemma bytes_string_rt : forall s, bytes_string (string_bytes s) = s.
Proof.
  intros s. unfold bytes_string, string_bytes. rewrite map_map.
  erewrite map_ext; [rewrite map_id; apply string_of_list_ascii_of_string|].
  intros c. simpl. rewrite Nat2Z.id. apply ascii_nat_embedding.
Qed.

(** ## Readers *)

(** [read_n] reads back the elements whose words follow one another. *)
Lemma read_n_rt : forall {X} (r : reader X) xs (wss : list (list Z)) rest,
  Forall2 (fun x ws => forall rest, r (ws ++ rest) = Some (x, rest)) xs wss ->
  read_n (length xs) r (concat wss ++ rest) = Some (xs, rest).
Proof.
  intros X r xs wss rest H. induction H as [|x ws xs wss Hx _ IH]; simpl; [reflexivity|].
  rewrite <- app_assoc, Hx. simpl. rewrite IH. reflexivity.
Qed.

(** Elements whose words are not empty are fewer than their words. *)
Lemma concat_length_ge : forall {X} (xs : list X) (wss : list (list Z)), Forall2 (fun _ ws => ws <> []) xs wss ->
  (length xs <= length (concat wss))%nat.
Proof.
  intros X xs wss H. induction H as [|x ws xs wss Hx _ IH]; simpl; [lia|].
  rewrite length_app. destruct ws; [congruence|]. simpl. lia.
Qed.

(** [read_counted] reads back the count and the elements. *)
Lemma read_counted_rt : forall {X} (r : reader X) xs (wss : list (list Z)) rest,
  Forall2 (fun x ws => ws <> [] /\ forall rest, r (ws ++ rest) = Some (x, rest)) xs wss ->
  read_counted r ((Z.of_nat (length xs) :: concat wss) ++ rest) = Some (xs, rest).
Proof.
  intros X r xs wss rest H. unfold read_counted. simpl app. cbv beta iota.
  assert (L : (length xs <= length (concat wss))%nat).
  { apply concat_length_ge. eapply Forall2_impl; [|exact H]. intros a b [H1 _]. exact H1. }
  rewrite at_least_spec.
  replace (Z.of_nat (length (concat wss ++ rest)) <? Z.of_nat (length xs)) with false
    by (symmetry; apply Z.ltb_ge; rewrite length_app; lia).
  rewrite Nat2Z.id. apply read_n_rt. eapply Forall2_impl; [|exact H]. intros a b [_ H2]. exact H2.
Qed.

(** A Forall2 of a map. *)
Lemma forall2_map : forall {X Y} (P : X -> Y -> Prop) (f : X -> Y) xs,
  (forall x, In x xs -> P x (f x)) -> Forall2 P xs (map f xs).
Proof. intros X Y P f xs H. induction xs; simpl; constructor; auto with datatypes. Qed.

(** A string table's words read back. *)
Lemma read_strings_rt : forall ss rest, read_strings (strings_words ss ++ rest) = Some (ss, rest).
Proof.
  intros ss rest. unfold read_strings, strings_words. rewrite flat_map_concat_map.
  apply read_counted_rt. apply forall2_map. intros s _. split; [unfold bytes_words; discriminate|].
  intros rest'. rewrite read_bytes_rt by apply string_bytes_byte. simpl. rewrite bytes_string_rt. reflexivity.
Qed.

(** A table of wide constants reads back. *)
Lemma read_wides_rt : forall cs rest, forallb wideok cs = true ->
  read_counted read_wide ((Z.of_nat (length cs) :: flat_map wide_words cs) ++ rest) = Some (cs, rest).
Proof.
  intros cs rest H. rewrite flat_map_concat_map. apply read_counted_rt. apply forall2_map.
  intros c Hc. rewrite forallb_forall in H. destruct (wide_words_rt c (H c Hc)) as (a & b & d & E & R).
  rewrite E. split; [discriminate|]. intros rest'. simpl. rewrite R. reflexivity.
Qed.

(** ## Sections *)

(** The sections' words split back into the sections. *)
Lemma read_sections_rt : forall ss fuel, (length (sections_words ss) <= fuel)%nat ->
  read_sections fuel (sections_words ss) = Some ss.
Proof.
  induction ss as [|[id ws] ss IH]; intros fuel H; [destruct fuel; reflexivity|].
  unfold sections_words in *. cbn [flat_map fst snd] in *. destruct fuel as [|f]; [simpl in H; lia|].
  cbn [read_sections]. simpl app. cbv iota. rewrite take_app_z. cbn [fst snd]. rewrite IH; [reflexivity|].
  simpl in H. rewrite length_app in H. lia.
Qed.

(** The sections of a module in their order: the core ones present,
    then NAMES if any. *)
Definition msecs (c1 c2 c3 c4 c5 b : bool) (a1 a2 a3 a4 a5 a6 : list Z) : list (Z * list Z) :=
  ((if c1 then [] else [(1, a1)]) ++ (if c2 then [] else [(2, a2)]) ++ (if c3 then [] else [(3, a3)])
   ++ (if c4 then [] else [(4, a4)]) ++ (if c5 then [] else [(5, a5)])) ++ (if b then [(256, a6)] else []).

(** What the reader finds in a module's sections. *)
Lemma msecs_spec : forall c1 c2 c3 c4 c5 b a1 a2 a3 a4 a5 a6,
  let ss := msecs c1 c2 c3 c4 c5 b a1 a2 a3 a4 a5 a6 in
  ids_ok 0 ss = true /\ filter (fun s => fst s <? 257) ss = ss /\
  section 1 ss = (if c1 then None else Some a1) /\ section 2 ss = (if c2 then None else Some a2) /\
  section 3 ss = (if c3 then None else Some a3) /\ section 4 ss = (if c4 then None else Some a4) /\
  section 5 ss = (if c5 then None else Some a5) /\ section 256 ss = (if b then Some a6 else None).
Proof.
  intros. subst ss. destruct c1, c2, c3, c4, c5, b; split; reflexivity || (repeat split; reflexivity).
Qed.

(** ## Patterns *)

(** The holes of a pattern, in order. *)
Fixpoint pat_holes (p : pat) : list nat :=
  match p with
  | PH i => [i]
  | PA _ => []
  | PC _ ps => flat_map pat_holes ps
  | PL ps => flat_map pat_holes ps
  end.

(** [match_pat] on the patterns ps and the terms ts in turn. *)
Fixpoint match_pats (ps : list pat) (ts : list term) (e : env) : option env :=
  match ps, ts with
  | [], [] => Some e
  | p :: ps', t :: ts' => let* e' := match_pat p t e in match_pats ps' ts' e'
  | _, _ => None
  end.

(** [fill_pat] on the patterns ps in turn. *)
Definition fill_pats (e : env) : list pat -> option (list term) :=
  fix go (ps : list pat) : option (list term) :=
    match ps with
    | [] => Some []
    | p :: ps' => let* t := fill_pat p e in let* ts := go ps' in Some (t :: ts)
    end.

(** [match_pat], one level unfolded. *)
Lemma match_pat_eq : forall p t e, match_pat p t e =
  match p with
  | PH i => Some ((i, t) :: e)
  | PA s => if is_atom s t then Some e else None
  | PC f ps => match t with TApp g ts => if String.eqb f g then match_pats ps ts e else None | _ => None end
  | PL ps => match t with TList ts => match_pats ps ts e | _ => None end
  end.
Proof. intros [i|s|f ps|ps] t e; reflexivity. Qed.

(** [fill_pat], one level unfolded. *)
Lemma fill_pat_eq : forall p e, fill_pat p e =
  match p with
  | PH i => env_get i e
  | PA s => Some (TAtom s)
  | PC f ps => let* ts := fill_pats e ps in Some (TApp f ts)
  | PL ps => let* ts := fill_pats e ps in Some (TList ts)
  end.
Proof. intros [i|s|f ps|ps] e; reflexivity. Qed.

(** Induction on patterns, with the hypothesis on every pattern of a
    list. *)
Definition pat_rect2 (P : pat -> Prop) (HH : forall i, P (PH i)) (HA : forall s, P (PA s))
  (HC : forall f ps, Forall P ps -> P (PC f ps)) (HL : forall ps, Forall P ps -> P (PL ps))
  : forall p, P p :=
  fix go (p : pat) : P p :=
    match p with
    | PH i => HH i
    | PA s => HA s
    | PC f ps => HC f ps ((fix gol (ps : list pat) : Forall P ps :=
                            match ps with
                            | [] => Forall_nil P
                            | q :: qs => @Forall_cons _ P q qs (go q) (gol qs)
                            end) ps)
    | PL ps => HL ps ((fix gol (ps : list pat) : Forall P ps :=
                         match ps with
                         | [] => Forall_nil P
                         | q :: qs => @Forall_cons _ P q qs (go q) (gol qs)
                         end) ps)
    end.

(** Every key of the bindings nw is one of the holes hs. *)
Definition keys_in (nw : env) (hs : list nat) : Prop := forall h, In h (map fst nw) -> In h hs.

(** Bindings in front of others do not hide a hole they do not bind. *)
Lemma env_get_app_out : forall nw e h, ~ In h (map fst nw) -> env_get h (nw ++ e) = env_get h e.
Proof.
  induction nw as [|[j t] nw IH]; intros e h H; simpl in *; [reflexivity|].
  destruct (Nat.eqb_spec h j); [subst; tauto|]. apply IH. tauto.
Qed.

(** A list without duplicates, split in two. *)
Lemma nodup_app_inv : forall {X} (a b : list X), NoDup (a ++ b) ->
  NoDup a /\ NoDup b /\ (forall h, In h a -> ~ In h b).
Proof.
  intros X a b. induction a as [|x a IH]; intros H; simpl in *.
  - split; [constructor|]. split; [exact H | intros h []].
  - inversion H as [|? ? Hx Hd]; subst. destruct (IH Hd) as (A & B & C). split; [|split; [exact B|]].
    + constructor; [intros Hin; apply Hx; apply in_or_app; auto | exact A].
    + intros h [<-|Hh] Hb; [apply Hx; apply in_or_app; auto | exact (C h Hh Hb)].
Qed.

(** What a pattern's match makes: bindings of its holes in front of
    the old ones; and the term, filled again from any bindings that
    agree on its holes, if the holes differ. *)
Definition pat_ok (p : pat) : Prop :=
  forall t e0 e, match_pat p t e0 = Some e ->
    (exists nw, e = nw ++ e0 /\ keys_in nw (pat_holes p)) /\
    (NoDup (pat_holes p) -> forall e', (forall h, In h (pat_holes p) -> env_get h e' = env_get h e) ->
     fill_pat p e' = Some t).

(** [pat_ok] for a list of patterns. *)
Lemma pats_ok : forall ps, Forall pat_ok ps ->
  forall ts e0 e, match_pats ps ts e0 = Some e ->
    (exists nw, e = nw ++ e0 /\ keys_in nw (flat_map pat_holes ps)) /\
    (NoDup (flat_map pat_holes ps) ->
     forall e', (forall h, In h (flat_map pat_holes ps) -> env_get h e' = env_get h e) ->
     fill_pats e' ps = Some ts).
Proof.
  induction 1 as [|p ps Hp Hps IH]; intros [|t ts] e0 e H; simpl in H; try discriminate.
  - injection H as <-. split; [exists []; split; [reflexivity | intros h []] | intros; reflexivity].
  - destruct (match_pat p t e0) as [e1|] eqn:E1; [|discriminate].
    destruct (Hp _ _ _ E1) as [(nw1 & -> & K1) F1].
    destruct (IH _ _ _ H) as [(nw2 & -> & K2) F2].
    split.
    + exists (nw2 ++ nw1). rewrite app_assoc. split; [reflexivity|].
      intros h Hh. simpl. rewrite map_app in Hh. apply in_app_or in Hh as [Hh|Hh]; apply in_or_app; auto.
    + intros Hd e' He. simpl in Hd. apply nodup_app_inv in Hd as (D1 & D2 & D3).
      simpl. rewrite (F1 D1 e').
      * rewrite (F2 D2 e'); [reflexivity|]. intros h Hh. apply He. simpl. apply in_or_app; auto.
      * intros h Hh. rewrite He by (simpl; apply in_or_app; auto).
        apply env_get_app_out. intros Hk. apply (D3 h Hh). apply K2. exact Hk.
Qed.

(** Every pattern is [pat_ok]. *)
Lemma match_fill_ok : forall p, pat_ok p.
Proof.
  apply pat_rect2.
  - intros i t e0 e H. rewrite match_pat_eq in H. injection H as <-. split.
    + exists [(i, t)]. split; [reflexivity|]. intros h H; exact H.
    + intros _ e' He. rewrite fill_pat_eq. rewrite He by (left; reflexivity). simpl.
      rewrite Nat.eqb_refl. reflexivity.
  - intros s t e0 e H. rewrite match_pat_eq in H. destruct (is_atom s t) eqn:E; [|discriminate].
    injection H as <-. apply is_atom_inv in E. subst. split.
    + exists []. split; [reflexivity | intros h []].
    + intros; reflexivity.
  - intros f ps Hps t e0 e H. rewrite match_pat_eq in H. destruct t as [| | g ts |]; try discriminate.
    destruct (String.eqb_spec f g) as [<-|]; [|discriminate].
    destruct (pats_ok ps Hps ts e0 e H) as [A B]. split; [exact A|].
    intros Hd e' He. rewrite fill_pat_eq. rewrite (B Hd e' He). reflexivity.
  - intros ps Hps t e0 e H. rewrite match_pat_eq in H. destruct t as [| | g ts | ts]; try discriminate.
    destruct (pats_ok ps Hps ts e0 e H) as [A B]. split; [exact A|].
    intros Hd e' He. rewrite fill_pat_eq. rewrite (B Hd e' He). reflexivity.
Qed.

(** The term a pattern matched is filled again from bindings that
    agree with the match on its holes, when they differ. *)
Lemma match_fill : forall p t e, match_pat p t [] = Some e -> NoDup (pat_holes p) ->
  forall e', (forall h, In h (pat_holes p) -> env_get h e' = env_get h e) -> fill_pat p e' = Some t.
Proof. intros p t e H. exact (proj2 (match_fill_ok p t [] e H)). Qed.

(** ## Fields *)

(** The hole a field reads. *)
Definition field_hole (f : field) : nat :=
  match f with
  | FDef i | FClass i | FEnum _ i | FU32 i | FI64 i | FOpnd i | FLabel i | FTarget i | FLocal i
  | FLocalDef i | FStr i | FResult i | FLower i | FFlightArg i => i
  end.

(** The hole an instruction's field reads. *)
Definition lfield_hole (lf : lfield) : nat :=
  match lf with FOne f => field_hole f | FCount i _ _ | FRest i _ _ => i end.

(** The reader's tables invert the writer's: each id maps back to the
    name, string or constant it was written for. *)
Record tabs_ok (w : wtab) (r : rtab) : Prop := {
  ok_syms : forall x i, nm_find x (w_syms w) = Some i -> ZMap.find i (r_syms r) = Some x;
  ok_strs : forall x i, nm_find x (w_strs w) = Some i -> ZMap.find i (r_strs r) = Some x;
  ok_consts : forall n i, ZMap.find n (w_consts w) = Some i -> ZMap.find i (r_consts r) = Some n;
  ok_temps : forall x i, nm_find x (w_temps w) = Some i -> ZMap.find i (r_temps r) = Some x;
  ok_labels : forall x i, nm_find x (w_labels w) = Some i -> ZMap.find i (r_labels r) = Some x;
  ok_locals : forall x i, nm_find x (w_locals w) = Some i -> ZMap.find i (r_locals r) = Some x
}.

(** Reading the definitions ds, the reader's rebind words and next id
    going from rb and n to rb' and n', names each in turn. *)
Fixpoint defs_read (r : rtab) (ds : list term) (rb : option (list Z)) (n : Z)
  (rb' : option (list Z)) (n' : Z) : Prop :=
  match ds with
  | [] => rb = rb' /\ n = n'
  | d :: ds' => exists rb1 n1, (forall ws x, def_name r (mkRst ws rb n x) = Some (d, mkRst ws rb1 n1 x))
                               /\ defs_read r ds' rb1 n1 rb' n'
  end.

(** [defs_read] of two lists joined. *)
Lemma defs_read_app : forall r a b rb n rb' n', defs_read r (a ++ b) rb n rb' n' ->
  exists rb1 n1, defs_read r a rb n rb1 n1 /\ defs_read r b rb1 n1 rb' n'.
Proof.
  induction a as [|d a IH]; intros b rb n rb' n' H; simpl in *.
  - exists rb, n. auto.
  - destruct H as (rb1 & n1 & H1 & H2). destruct (IH _ _ _ _ _ H2) as (rb2 & n2 & A & B).
    exists rb2, n2. split; [exists rb1, n1; auto | exact B].
Qed.

(** The reader's locals from the id x on are xs, up to the id x'. *)
Fixpoint locals_read (r : rtab) (xs : list term) (x x' : Z) : Prop :=
  match xs with
  | [] => x = x'
  | v :: xs' => ZMap.find x (r_locals r) = Some v /\ locals_read r xs' (x + 1) x'
  end.

(** [locals_read] of two lists joined. *)
Lemma locals_read_app : forall r a b x x', locals_read r (a ++ b) x x' ->
  exists x1, locals_read r a x x1 /\ locals_read r b x1 x'.
Proof.
  induction a as [|v a IH]; intros b x x' H; simpl in *.
  - exists x. auto.
  - destruct H as [H1 H2]. destruct (IH _ _ _ H2) as (x1 & A & B). exists x1. auto.
Qed.

(** The local a field defines, if it is [FLocalDef]. *)
Definition field_locals (e : env) (f : field) : list term :=
  match f with FLocalDef i => match env_get i e with Some v => [v] | None => [] end | _ => [] end.

(** Bindings e1 that the bindings e agree with. *)
Definition env_of (e e1 : env) : Prop := forall h v, In (h, v) e1 -> env_get h e = Some v.

(** A binding [env_get] finds is in the list. *)
Lemma env_get_in : forall h e v, env_get h e = Some v -> In (h, v) e.
Proof.
  induction e as [|[j t] e IH]; intros v H; simpl in *; [discriminate|].
  destruct (Nat.eqb_spec h j) as [->|]; [injection H as ->; auto | auto].
Qed.

(** A bound key has a value. *)
Lemma env_get_key : forall h e, In h (map fst e) -> exists v, env_get h e = Some v.
Proof.
  induction e as [|[j t] e IH]; intros H; simpl in *; [contradiction|].
  destruct (Nat.eqb_spec h j); [eauto|]. destruct H; [congruence | auto].
Qed.

(** An operand word reads back: tag 1 or 2 for a constant. *)
Lemma const_rt : forall w r n z, tabs_ok w r -> const_word (w_consts w) n = Some z ->
  (z mod 4 = 1 \/ z mod 4 = 2) /\ const_of r z = Some n.
Proof.
  intros w r n z T H. destruct (inline n) eqn:E.
  - destruct (inline_round_trip r (w_consts w) n E) as (z' & H1 & H2). rewrite H in H1.
    injection H1 as <-. split; [left | exact H2]. unfold const_word in H. rewrite E in H.
    injection H as <-. rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
  - unfold const_word in H. rewrite E in H.
    destruct (ZMap.find n (w_consts w)) as [i|] eqn:Ei; [|discriminate]. injection H as <-.
    assert (M : (i * 4 + 2) mod 4 = 2) by (rewrite Z.add_comm, Z.mod_add by lia; reflexivity).
    assert (D : (i * 4 + 2) / 4 = i) by (rewrite Z.add_comm, Z.div_add by lia; reflexivity).
    split; [right; exact M|]. unfold const_of. rewrite M, D. exact (ok_consts _ _ T _ _ Ei).
Qed.

(** An operand reads back from its one word. *)
Lemma opnd_rt : forall w r v o, tabs_ok w r -> opnd_out w v = Some o ->
  o_defs o = [] /\ exists z, o_words o = [z] /\ value_of r z = Some v.
Proof.
  intros w r v o T H. destruct v as [| | f [|x [|]] |]; try discriminate.
  cbv beta iota delta [opnd_out] in H.
  destruct (String.eqb_spec f "tmp") as [->|N1].
  - destruct (nm_find x (w_temps w)) as [i|] eqn:Ei; [|discriminate]. injection H as <-.
    split; [reflexivity|]. exists (i * 4). split; [reflexivity|]. unfold value_of.
    rewrite Z.mod_mul, Z.div_mul by lia. cbn [Z.eqb]. rewrite (ok_temps _ _ T _ _ Ei). reflexivity.
  - destruct (String.eqb_spec f "const") as [->|N2].
    + destruct x as [n| | |]; try discriminate.
      destruct (const_word (w_consts w) n) as [z|] eqn:Ez; [|discriminate]. injection H as <-.
      split; [reflexivity|]. exists z. split; [reflexivity|].
      destruct (const_rt w r n z T Ez) as [M C]. unfold value_of.
      destruct M as [M|M]; rewrite M; cbn [Z.eqb]; rewrite C; reflexivity.
    + destruct (String.eqb_spec f "global") as [->|N3]; [|discriminate].
      destruct (nm_find x (w_syms w)) as [i|] eqn:Ei; [|discriminate]. injection H as <-.
      split; [reflexivity|]. exists (i * 4 + 3). split; [reflexivity|].
      assert (M : (i * 4 + 3) mod 4 = 3) by (rewrite Z.add_comm, Z.mod_add by lia; reflexivity).
      assert (D : (i * 4 + 3) / 4 = i) by (rewrite Z.add_comm, Z.div_add by lia; reflexivity).
      unfold value_of. rewrite M, D. cbn [Z.eqb]. rewrite (ok_syms _ _ T _ _ Ei). reflexivity.
Qed.

(** The temporaries a call's result defines, and its one word, read
    back. *)
Lemma result_rt : forall r v o ws rb n x rb' n', result_out v = Some o ->
  defs_read r (o_defs o) rb n rb' n' ->
  exists z, o_words o = [z] /\ read_result r z (mkRst ws rb n x) = Some (v, mkRst ws rb' n' x).
Proof.
  intros r v o ws rb n x rb' n' H D. unfold result_out in H.
  destruct (result_defs v) as [ds|] eqn:Eds; [|discriminate].
  destruct (is_atom "void" v) eqn:Ev.
  - injection H as <-. apply is_atom_inv in Ev. subst v. simpl in D. destruct D as [<- <-].
    exists 0. split; reflexivity.
  - unfold result_defs in Eds. rewrite Ev in Eds.
    destruct (app_args "result" 2 v) as [[|d [|k [|]]]|] eqn:Er;
      try (apply app_args_inv in Er; destruct Er as [_ Er]; discriminate).
    + destruct (enc_code EClass k) as [c|] eqn:Ec; [|discriminate]. injection H as <-.
      destruct (app_args "tmp" 1 d) as [xs|] eqn:Et; [|discriminate]. injection Eds as <-.
      apply app_args_inv in Et as [-> Lx]. destruct xs as [|y [|]]; try discriminate.
      apply app_args_inv in Er as [-> _].
      simpl in D. destruct D as (rb1 & n1 & D1 & <- & <-).
      exists c. split; [reflexivity|]. pose proof (class_code_range _ _ Ec) as R.
      unfold read_result. replace (Z.eqb c 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (256 <=? c) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite (codes_round_trip _ _ _ Ec), D1. reflexivity.
    + destruct (app_args "tuple" 1 v) as [[|[| | |rs] []]|] eqn:Et; try discriminate.
      destruct rs as [|r1 [|r2 []]]; try discriminate.
      destruct (app_args "result" 2 r1) as [[|d1 [|k1 [|]]]|] eqn:E1; try discriminate.
      destruct (app_args "result" 2 r2) as [[|d2 [|k2 [|]]]|] eqn:E2; try discriminate.
      destruct (enc_code EClass k1) as [c1|] eqn:Ec1; [|discriminate].
      destruct (enc_code EClass k2) as [c2|] eqn:Ec2; [|discriminate]. injection H as <-.
      cbn [mapo] in Eds. rewrite E1, E2 in Eds.
      destruct (app_args "tmp" 1 d1) as [[|x1 []]|] eqn:Ed1; try discriminate.
      destruct (app_args "tmp" 1 d2) as [[|x2 []]|] eqn:Ed2; try discriminate.
      injection Eds as <-.
      apply app_args_inv in Ed1 as [-> _]. apply app_args_inv in Ed2 as [-> _].
      apply app_args_inv in E1 as [-> _]. apply app_args_inv in E2 as [-> _].
      apply app_args_inv in Et as [-> _].
      simpl in D. destruct D as (rb1 & n1 & D1 & rb2 & n2 & D2 & <- & <-).
      exists (256 + 16 * c1 + c2). split; [reflexivity|].
      pose proof (class_code_range _ _ Ec1). pose proof (class_code_range _ _ Ec2).
      unfold read_result.
      replace (Z.eqb (256 + 16 * c1 + c2) 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb (256 + 16 * c1 + c2) 15) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (256 <=? 256 + 16 * c1 + c2) with true by (symmetry; apply Z.leb_le; lia).
      replace ((256 + 16 * c1 + c2 - 256) / 16) with c1
        by (apply (Z.div_unique _ _ _ c2); lia).
      replace ((256 + 16 * c1 + c2) mod 16) with c2
        by (apply (Z.mod_unique _ _ (16 + c1)); lia).
      replace (c1 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite (codes_round_trip _ _ _ Ec1), (codes_round_trip _ _ _ Ec2).
      rewrite D1. cbn [fst snd]. rewrite D2. reflexivity.
Qed.

(** The next word of the reader's state. *)
Lemma next_word_cons : forall z ws rb n x, next_word (mkRst (z :: ws) rb n x) = Some (z, mkRst ws rb n x).
Proof. reflexivity. Qed.

(** The hole of a local's definition, which writes no word, is
    bound. *)
Definition field_bound (e : env) (f : field) : Prop :=
  match f with FLocalDef i => env_get i e <> None | _ => True end.

(** One field reads back into its hole the value it was written
    from. *)
Lemma read_field_rt : forall w r e f o e0 ws rb n x rb' n' x',
  tabs_ok w r -> field_out w e f = Some o -> field_bound e f ->
  defs_read r (o_defs o) rb n rb' n' -> locals_read r (field_locals e f) x x' ->
  exists v, env_get (field_hole f) e = Some v /\
    read_field r f e0 (mkRst (o_words o ++ ws) rb n x) = Some ((field_hole f, v) :: e0, mkRst ws rb' n' x').
Proof.
  intros w r e f o e0 ws rb n x rb' n' x' T H B D L.
  destruct f as [i|i|en i|i|i|i|i|i|i|i|i|i|i|i]; cbn [field_hole field_locals field_bound] in *;
    cbv beta iota delta [field_out] in H;
    destruct (env_get i e) as [v|] eqn:Ev; try discriminate; try congruence; exists v; split; try reflexivity;
    cbn [read_field].
  - (* FDef *)
    injection H as <-. cbn [o_words o_defs defs_read locals_read app] in *.
    destruct D as (rb1 & n1 & D1 & <- & <-). subst x'. rewrite D1. reflexivity.
  - (* FClass *)
    destruct (enc_code EClass v) as [z|] eqn:Ez; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wwords defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    rewrite next_word_cons. cbn [fst snd]. rewrite (codes_round_trip _ _ _ Ez). reflexivity.
  - (* FEnum *)
    destruct (enc_code en v) as [z|] eqn:Ez; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wwords defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    rewrite next_word_cons. cbn [fst snd]. rewrite (codes_round_trip _ _ _ Ez). reflexivity.
  - (* FU32 *)
    destruct v as [k| | |]; try discriminate. destruct (u32ok k); [|discriminate]. injection H as <-.
    cbn [o_words o_defs wwords defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    reflexivity.
  - (* FI64 *)
    destruct v as [k| | |]; try discriminate. destruct (i64ok k) eqn:Ek; [|discriminate].
    injection H as <-. destruct (i64_words_rt k Ek) as (lo & hi & Ew & R).
    cbn [o_words o_defs wwords defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    rewrite Ew. cbn. rewrite R. reflexivity.
  - (* FOpnd *)
    destruct (opnd_rt w r v o T H) as (Hd & z & Hw & Hv). rewrite Hd in D. rewrite Hw.
    cbn [defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    rewrite next_word_cons. cbn [fst snd]. rewrite Hv. reflexivity.
  - (* FLabel *)
    destruct (nm_find v (w_labels w)) as [z|] eqn:Ez; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wwords defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    rewrite next_word_cons. cbn [fst snd]. rewrite (ok_labels _ _ T _ _ Ez). reflexivity.
  - (* FTarget *)
    destruct (app_args "poll" 1 v) as [[|l [|]]|] eqn:Ep;
    [ | destruct (nm_find l (w_labels w)) as [z|] eqn:Ez; [|discriminate]; injection H as <-
      | | ];
    try (destruct (nm_find v (w_labels w)) as [z|] eqn:Ez; [|discriminate]; injection H as <-);
    cbn [o_words o_defs wwords defs_read locals_read app] in *; destruct D as [<- <-]; subst x';
    rewrite next_word_cons; cbn [fst snd];
    try (replace (z * 2 / 2) with z by (symmetry; apply Z.div_mul; lia);
         rewrite (ok_labels _ _ T _ _ Ez); rewrite Z.mod_mul by lia; reflexivity).
    apply app_args_inv in Ep as [-> _].
    replace ((z * 2 + 1) / 2) with z by (rewrite Z.add_comm, Z.div_add by lia; reflexivity).
    replace ((z * 2 + 1) mod 2) with 1 by (rewrite Z.add_comm, Z.mod_add by lia; reflexivity).
    rewrite (ok_labels _ _ T _ _ Ez). reflexivity.
  - (* FLocal *)
    destruct (nm_find v (w_locals w)) as [z|] eqn:Ez; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wwords defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    rewrite next_word_cons. cbn [fst snd]. rewrite (ok_locals _ _ T _ _ Ez). reflexivity.
  - (* FLocalDef *)
    injection H as <-. cbn [o_words o_defs wnil defs_read locals_read app] in *.
    destruct D as [<- <-]. destruct L as [L1 <-]. cbn [s_local s_words s_rebinds s_next].
    rewrite L1. reflexivity.
  - (* FStr *)
    destruct v as [|a| |]; try discriminate.
    destruct (nm_find (TAtom a) (w_strs w)) as [z|] eqn:Ez; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wwords defs_read locals_read app] in *. destruct D as [<- <-]. subst x'.
    rewrite next_word_cons. cbn [fst snd]. rewrite (ok_strs _ _ T _ _ Ez). reflexivity.
  - (* FResult *)
    cbn [locals_read] in L. subst x'.
    destruct (result_rt r v o ws rb n x rb' n' H D) as (z & Hw & R). rewrite Hw. cbn [app].
    rewrite next_word_cons. cbn [fst snd]. rewrite R. reflexivity.
  - (* FLower *)
    cbn [locals_read] in L. subst x'. destruct (is_atom "none" v) eqn:En.
    + injection H as <-. apply is_atom_inv in En. subst v. cbn [o_words o_defs wwords defs_read app] in *.
      destruct D as [<- <-]. reflexivity.
    + destruct (app_args "lower" 1 v) as [[|p [|]]|] eqn:Ep; try discriminate.
      destruct (opnd_out w p) as [op|] eqn:Eo; [|discriminate]. injection H as <-.
      destruct (opnd_rt w r p op T Eo) as (Hd & z & Hw & Hv).
      cbn [o_words o_defs wwords wapp defs_read app] in *. rewrite Hd, Hw in *. cbn [app] in *.
      destruct D as [<- <-]. apply app_args_inv in Ep as [-> _]. cbn. rewrite Hv. reflexivity.
  - (* FFlightArg *)
    cbn [locals_read] in L. subst x'.
    destruct (app_args "address" 1 v) as [[|p [|]]|] eqn:Ep;
    [ | destruct (opnd_out w p) as [op|] eqn:Eo; [|discriminate]; injection H as <-;
        destruct (opnd_rt w r p op T Eo) as (Hd & z & Hw & Hv);
        apply app_args_inv in Ep as [-> _]
      | | ];
    try (destruct (opnd_out w v) as [op|] eqn:Eo; [|discriminate]; injection H as <-;
         destruct (opnd_rt w r v op T Eo) as (Hd & z & Hw & Hv));
    cbn [o_words o_defs wwords wapp defs_read app] in *; rewrite Hd, Hw in *; cbn [app] in *;
    destruct D as [<- <-]; cbn; rewrite Hv; reflexivity.
Qed.

(** The fields fs read back into their holes the values they were
    written from. *)
Lemma read_fields_rt : forall w r e fs o e0 ws rb n x rb' n' x',
  tabs_ok w r -> fields_out w e fs = Some o -> Forall (field_bound e) fs ->
  defs_read r (o_defs o) rb n rb' n' -> locals_read r (flat_map (field_locals e) fs) x x' ->
  exists e1, read_fields r fs e0 (mkRst (o_words o ++ ws) rb n x) = Some (e1 ++ e0, mkRst ws rb' n' x')
    /\ env_of e e1 /\ (forall h, In h (map field_hole fs) -> In h (map fst e1)).
Proof.
  intros w r e fs. induction fs as [|f fs IH]; intros o e0 ws rb n x rb' n' x' T H B D L; simpl in H.
  - injection H as <-. cbn in D, L. destruct D as [<- <-]. subst x'. exists []. split; [reflexivity|].
    split; [intros h v []| intros h []].
  - destruct (field_out w e f) as [a|] eqn:Ea; [|discriminate].
    destruct (fields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wapp] in *. inversion B as [|? ? B1 B2]; subst.
    destruct (defs_read_app _ _ _ _ _ _ _ D) as (rb1 & n1 & D1 & D2).
    cbn [flat_map] in L. destruct (locals_read_app _ _ _ _ _ L) as (x1 & L1 & L2).
    destruct (read_field_rt w r e f a e0 (o_words b ++ ws) rb n x rb1 n1 x1 T Ea B1 D1 L1)
      as (v & Hv & R1).
    rewrite <- app_assoc. cbn [read_fields]. rewrite R1. cbn [fst snd].
    destruct (IH b ((field_hole f, v) :: e0) ws rb1 n1 x1 rb' n' x' T eq_refl B2 D2 L2) as (e1 & R2 & E2 & K2).
    exists (e1 ++ [(field_hole f, v)]). rewrite <- app_assoc. split; [exact R2|]. split.
    + intros h u Hin. apply in_app_or in Hin as [Hin|[Hin|[]]]; [auto|]. injection Hin as <- <-. exact Hv.
    + intros h [<-|Hh]; rewrite map_app; apply in_or_app; [right; left; reflexivity | left; auto].
Qed.

(** Whether a field writes a word. *)
Definition writes_word (f : field) : bool := match f with FDef _ | FLocalDef _ => false | _ => true end.

(** Whether a field defines a local. *)
Definition is_localdef (f : field) : bool := match f with FLocalDef _ => true | _ => false end.

(** Whether a field defines temporaries. *)
Definition defines (f : field) : bool := match f with FDef _ | FResult _ => true | _ => false end.

(** A field's temporaries defined less its words: at most this. *)
Definition fcost (f : field) : Z := match f with FDef _ | FResult _ => 1 | FLocalDef _ => 0 | _ => -1 end.

(** The sum of the fields' [fcost]. *)
Definition fscost (fs : list field) : Z := fold_right (fun f c => fcost f + c) 0 fs.

(** An operand's word. *)
Lemma opnd_shape : forall w v o, opnd_out w v = Some o -> o_defs o = [] /\ length (o_words o) = 1%nat.
Proof.
  intros w v o H. destruct v as [| | f [|x [|]] |]; try discriminate.
  cbv beta iota delta [opnd_out] in H.
  destruct (String.eqb f "tmp"); [destruct (nm_find x (w_temps w)); [injection H as <-; auto | discriminate]|].
  destruct (String.eqb f "const").
  - destruct x as [k| | |]; try discriminate. destruct (const_word (w_consts w) k); [|discriminate].
    injection H as <-. auto.
  - destruct (String.eqb f "global"); [|discriminate].
    destruct (nm_find x (w_syms w)); [injection H as <-; auto | discriminate].
Qed.

(** A call result's word and the temporaries it defines. *)
Lemma result_shape : forall v o, result_out v = Some o ->
  length (o_words o) = 1%nat /\ (length (o_defs o) <= 2)%nat /\ result_defs v = Some (o_defs o).
Proof.
  intros v o H. unfold result_out in H. destruct (result_defs v) as [ds|] eqn:Eds; [|discriminate].
  destruct (is_atom "void" v) eqn:Ev.
  - injection H as <-. unfold result_defs in Eds. rewrite Ev in Eds. injection Eds as <-. simpl. auto.
  - unfold result_defs in Eds. rewrite Ev in Eds.
    destruct (app_args "result" 2 v) as [[|d [|k [|]]]|] eqn:Er;
      try (apply app_args_inv in Er; destruct Er as [_ Er]; discriminate).
    + destruct (enc_code EClass k); [|discriminate]. injection H as <-. simpl.
      destruct (app_args "tmp" 1 d) as [xs|] eqn:Et; [|discriminate]. injection Eds as <-.
      apply app_args_inv in Et as [_ Lx]. split; [reflexivity|]. split; [lia | reflexivity].
    + destruct (app_args "tuple" 1 v) as [[|[| | |rs] []]|]; try discriminate.
      destruct rs as [|r1 [|r2 []]]; try discriminate.
      destruct (app_args "result" 2 r1) as [[|d1 [|k1 [|]]]|]; try discriminate.
      destruct (app_args "result" 2 r2) as [[|d2 [|k2 [|]]]|]; try discriminate.
      destruct (enc_code EClass k1); [|discriminate]. destruct (enc_code EClass k2); [|discriminate].
      injection H as <-. simpl. split; [reflexivity|]. split; [|reflexivity].
      apply mapo_length in Eds. simpl in Eds. lia.
Qed.

(** A field defines at most its words plus its [fcost]. *)
Lemma field_cost : forall w e f o, field_out w e f = Some o ->
  Z.of_nat (length (o_defs o)) <= Z.of_nat (length (o_words o)) + fcost f.
Proof.
  intros w e f o H.
  destruct f as [i|i|en i|i|i|i|i|i|i|i|i|i|i|i]; cbn [fcost];
    cbv beta iota delta [field_out] in H; try (destruct (env_get i e) as [v|]; [|discriminate]).
  - injection H as <-. simpl. lia.
  - destruct (enc_code EClass v); [injection H as <-; simpl; lia | discriminate].
  - destruct (enc_code en v); [injection H as <-; simpl; lia | discriminate].
  - destruct v; try discriminate. destruct (u32ok n); [injection H as <-; simpl; lia | discriminate].
  - destruct v; try discriminate. destruct (i64ok n); [injection H as <-; simpl; lia | discriminate].
  - destruct (opnd_shape _ _ _ H) as [A B]. rewrite A, B. simpl. lia.
  - destruct (nm_find v (w_labels w)); [injection H as <-; simpl; lia | discriminate].
  - destruct (app_args "poll" 1 v) as [[|l [|]]|];
      [ | destruct (nm_find l (w_labels w)); [injection H as <-; simpl; lia | discriminate] | | ];
      (destruct (nm_find v (w_labels w)); [injection H as <-; simpl; lia | discriminate]).
  - destruct (nm_find v (w_locals w)); [injection H as <-; simpl; lia | discriminate].
  - injection H as <-. simpl. lia.
  - destruct v; try discriminate. destruct (nm_find _ (w_strs w)); [injection H as <-; simpl; lia | discriminate].
  - destruct (result_shape _ _ H) as (A & B & _). lia.
  - destruct (is_atom "none" v); [injection H as <-; simpl; lia|].
    destruct (app_args "lower" 1 v) as [[|p [|]]|]; try discriminate.
    destruct (opnd_out w p) as [op|] eqn:Eo; [|discriminate]. injection H as <-.
    destruct (opnd_shape _ _ _ Eo) as [A B]. cbn [o_words o_defs wapp wwords]. rewrite !length_app, A, B. simpl. lia.
  - destruct (app_args "address" 1 v) as [[|p [|]]|];
      [ | destruct (opnd_out w p) as [op|] eqn:Eo; [|discriminate]; injection H as <-;
          destruct (opnd_shape _ _ _ Eo) as [A B]; cbn [o_words o_defs wapp wwords]; rewrite !length_app, A, B; simpl; lia | | ];
      (destruct (opnd_out w v) as [op|] eqn:Eo; [|discriminate]; injection H as <-;
       destruct (opnd_shape _ _ _ Eo) as [A B]; cbn [o_words o_defs wapp wwords]; rewrite !length_app, A, B; simpl; lia).
Qed.

(** A field that writes a word writes one at least. *)
Lemma field_words : forall w e f o, field_out w e f = Some o -> writes_word f = true ->
  (1 <= length (o_words o))%nat.
Proof.
  intros w e f o H W. pose proof (field_cost w e f o H) as C.
  destruct f; cbn [writes_word fcost] in *; try discriminate; try lia.
  cbv beta iota delta [field_out] in H. destruct (env_get i e); [|discriminate].
  destruct (result_shape _ _ H) as (A & _). lia.
Qed.

(** The fields define at most their words plus their [fscost]. *)
Lemma fields_cost : forall w e fs o, fields_out w e fs = Some o ->
  Z.of_nat (length (o_defs o)) <= Z.of_nat (length (o_words o)) + fscost fs
  /\ (existsb writes_word fs = true -> (1 <= length (o_words o))%nat).
Proof.
  intros w e. induction fs as [|f fs IH]; intros o H; simpl in H.
  - injection H as <-. simpl. split; [lia | discriminate].
  - destruct (field_out w e f) as [a|] eqn:Ea; [|discriminate].
    destruct (fields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    destruct (IH b eq_refl) as [C1 W1]. pose proof (field_cost _ _ _ _ Ea) as C0.
    cbn [o_words o_defs wapp fscost fold_right existsb] in *. rewrite !length_app.
    split; [unfold fscost in C1; lia|]. intros Hw. apply orb_true_iff in Hw as [Hw|Hw].
    + pose proof (field_words _ _ _ _ Ea Hw). lia.
    + specialize (W1 Hw). lia.
Qed.

(** The conditions on a list's element: its holes differ and are read
    by its fields, which define no local, write a word and define no
    more temporaries than words. *)
Definition elem_ok (el : pat) (fs : list field) : Prop :=
  NoDup (pat_holes el) /\ (forall h, In h (pat_holes el) -> In h (map field_hole fs))
  /\ Forall (fun f => is_localdef f = false) fs /\ existsb writes_word fs = true /\ fscost fs <= 0.

(** The elements of a list define no more temporaries than their
    words, and write as many words as elements at least. *)
Lemma elems_cost : forall w el fs ts o, elem_ok el fs -> elems_out w el fs ts = Some o ->
  (length (o_defs o) <= length (o_words o))%nat /\ (length ts <= length (o_words o))%nat.
Proof.
  intros w el fs. induction ts as [|t ts IH]; intros o Ok H; simpl in H.
  - injection H as <-. simpl. lia.
  - destruct (match_pat el t []) as [et|]; [|discriminate].
    destruct (fields_out w et fs) as [a|] eqn:Ea; [|discriminate].
    destruct (elems_out w el fs ts) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    destruct (IH b Ok eq_refl) as [C1 L1]. destruct (fields_cost _ _ _ _ Ea) as [C0 W0].
    destruct Ok as (_ & _ & _ & Wr & Cs). specialize (W0 Wr).
    cbn [o_words o_defs wapp length] in *. rewrite !length_app. split; lia.
Qed.

(** Fields that define no local define none. *)
Lemma no_locals : forall e fs, Forall (fun f => is_localdef f = false) fs ->
  flat_map (field_locals e) fs = [] /\ Forall (field_bound e) fs.
Proof.
  intros e fs H. induction H as [|f fs Hf _ [A B]]; simpl; [split; constructor|].
  destruct f; simpl in Hf; try discriminate; (split; [exact A | constructor; [exact I | exact B]]).
Qed.

(** The elements of a list read back, given their count. *)
Lemma read_count_rt : forall w r el fs ts o ws rb n x rb' n',
  tabs_ok w r -> elem_ok el fs -> elems_out w el fs ts = Some o ->
  defs_read r (o_defs o) rb n rb' n' ->
  read_count r el fs (length ts) (mkRst (o_words o ++ ws) rb n x) = Some (ts, mkRst ws rb' n' x).
Proof.
  intros w r el fs. induction ts as [|t ts IH]; intros o ws rb n x rb' n' T Ok H D; simpl in H.
  - injection H as <-. cbn in D |- *. destruct D as [<- <-]. reflexivity.
  - destruct (match_pat el t []) as [et|] eqn:Et; [|discriminate].
    destruct (fields_out w et fs) as [a|] eqn:Ea; [|discriminate].
    destruct (elems_out w el fs ts) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wapp] in *. destruct (defs_read_app _ _ _ _ _ _ _ D) as (rb1 & n1 & D1 & D2).
    destruct Ok as (Nd & Cov & NoL & Wr & Cs) eqn:Ok'. destruct (no_locals et fs NoL) as [Ln Bd].
    assert (L0 : locals_read r (flat_map (field_locals et) fs) x x) by (rewrite Ln; reflexivity).
    destruct (read_fields_rt w r et fs a [] (o_words b ++ ws) rb n x rb1 n1 x T Ea Bd D1 L0)
      as (e1 & R1 & E1 & K1).
    cbn [read_count length]. rewrite <- app_assoc, R1. cbn [fst snd]. rewrite app_nil_r.
    rewrite (match_fill el t et Et Nd e1).
    + rewrite (IH b ws rb1 n1 x rb' n' T (conj Nd (conj Cov (conj NoL (conj Wr Cs)))) eq_refl D2). reflexivity.
    + intros h Hh. destruct (env_get_key h e1 (K1 h (Cov h Hh))) as (v & Hv).
      rewrite Hv. symmetry. apply E1. apply env_get_in. exact Hv.
Qed.

(** The elements of a list read back to the end of its words. *)
Lemma read_rest_rt : forall w r el fs ts o rb n x rb' n' fuel,
  tabs_ok w r -> elem_ok el fs -> elems_out w el fs ts = Some o ->
  defs_read r (o_defs o) rb n rb' n' -> (length (o_words o) <= fuel)%nat ->
  read_rest r el fs fuel (mkRst (o_words o) rb n x) = Some (ts, mkRst [] rb' n' x).
Proof.
  intros w r el fs. induction ts as [|t ts IH]; intros o rb n x rb' n' fuel T Ok H D F; simpl in H.
  - injection H as <-. cbn in D |- *. destruct D as [<- <-]. destruct fuel; reflexivity.
  - destruct (match_pat el t []) as [et|] eqn:Et; [|discriminate].
    destruct (fields_out w et fs) as [a|] eqn:Ea; [|discriminate].
    destruct (elems_out w el fs ts) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    cbn [o_words o_defs wapp] in *. destruct (defs_read_app _ _ _ _ _ _ _ D) as (rb1 & n1 & D1 & D2).
    destruct Ok as (Nd & Cov & NoL & Wr & Cs) eqn:Ok'. destruct (no_locals et fs NoL) as [Ln Bd].
    assert (L0 : locals_read r (flat_map (field_locals et) fs) x x) by (rewrite Ln; reflexivity).
    destruct (read_fields_rt w r et fs a [] (o_words b) rb n x rb1 n1 x T Ea Bd D1 L0)
      as (e1 & R1 & E1 & K1).
    destruct (fields_cost _ _ _ _ Ea) as [_ W0]. specialize (W0 Wr).
    rewrite length_app in F. destruct fuel as [|f]; [lia|].
    destruct (o_words a) as [|w0 aw] eqn:Ew; [simpl in W0; lia|].
    cbn [read_rest s_words app]. change (w0 :: aw ++ o_words b) with ((w0 :: aw) ++ o_words b).
    rewrite R1. cbn [fst snd]. rewrite app_nil_r.
    rewrite (match_fill el t et Et Nd e1).
    + rewrite (IH b rb1 n1 x rb' n' f T (conj Nd (conj Cov (conj NoL (conj Wr Cs)))) eq_refl D2)
        by (simpl in F; lia).
      reflexivity.
    + intros h Hh. destruct (env_get_key h e1 (K1 h (Cov h Hh))) as (v & Hv).
      rewrite Hv. symmetry. apply E1. apply env_get_in. exact Hv.
Qed.

(** The fields of an instruction that define locals. *)
Definition lfields_locals (e : env) (fs : list lfield) : list term :=
  flat_map (fun lf => match lf with FOne f => field_locals e f | _ => [] end) fs.

(** Whether a list to the end of the words comes last, if at all. *)
Fixpoint rest_last (fs : list lfield) : bool :=
  match fs with
  | [] => true
  | FRest _ _ _ :: fs' => match fs' with [] => true | _ => false end
  | _ :: fs' => rest_last fs'
  end.

(** Whether no list goes to the end of the words. *)
Definition no_rest (fs : list lfield) : bool :=
  forallb (fun lf => match lf with FRest _ _ _ => false | _ => true end) fs.

(** The conditions on one field of an instruction. *)
Definition lfield_ok (e : env) (lf : lfield) : Prop :=
  match lf with FOne f => field_bound e f | FCount _ el fs | FRest _ el fs => elem_ok el fs end.

(** An instruction's fields read back into their holes the values
    they were written from. *)
Lemma read_lfields_rt : forall w r e fs o e0 ws rb n x rb' n' x',
  tabs_ok w r -> rest_last fs = true -> Forall (lfield_ok e) fs -> lfields_out w e fs = Some o ->
  (ws = [] \/ no_rest fs = true) ->
  defs_read r (o_defs o) rb n rb' n' -> locals_read r (lfields_locals e fs) x x' ->
  exists e1, read_lfields r fs e0 (mkRst (o_words o ++ ws) rb n x) = Some (e1 ++ e0, mkRst ws rb' n' x')
    /\ env_of e e1 /\ (forall h, In h (map lfield_hole fs) -> In h (map fst e1)).
Proof.
  intros w r e fs. induction fs as [|lf fs IH]; intros o e0 ws rb n x rb' n' x' T RL Ok H Ws D L;
    cbn [lfields_out] in H.
  - injection H as <-. cbn in D, L. destruct D as [<- <-]. subst x'. exists []. split; [reflexivity|].
    split; [intros h v []| intros h []].
  - inversion Ok as [|? ? Ok1 Ok2]; subst.
    destruct lf as [f|i el fs1|i el fs1].
    + destruct (field_out w e f) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [o_words o_defs wapp] in *. destruct (defs_read_app _ _ _ _ _ _ _ D) as (rb1 & n1 & D1 & D2).
      unfold lfields_locals in L. cbn [flat_map] in L.
      destruct (locals_read_app _ _ _ _ _ L) as (x1 & L1 & L2).
      destruct (read_field_rt w r e f a e0 (o_words b ++ ws) rb n x rb1 n1 x1 T Ea Ok1 D1 L1)
        as (v & Hv & R1).
      rewrite <- app_assoc. cbn [read_lfields]. rewrite R1. cbn [fst snd].
      destruct (IH b ((field_hole f, v) :: e0) ws rb1 n1 x1 rb' n' x' T RL Ok2 eq_refl Ws D2 L2)
        as (e1 & R2 & E2 & K2).
      exists (e1 ++ [(field_hole f, v)]). rewrite <- app_assoc. split; [exact R2|]. split.
      * intros h u Hin. apply in_app_or in Hin as [Hin|[Hin|[]]]; [auto|]. injection Hin as <- <-. exact Hv.
      * intros h [<-|Hh]; rewrite map_app; apply in_or_app; [right; left; reflexivity | left; auto].
    + destruct (env_get i e) as [[| | |ts]|] eqn:Ei; try discriminate.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [o_words o_defs wapp wwords app] in *. destruct (defs_read_app _ _ _ _ _ _ _ D) as (rb1 & n1 & D1 & D2).
      unfold lfields_locals in L. cbn [flat_map app] in L.
      destruct (elems_cost w el fs1 ts a Ok1 Ea) as [_ Lc].
      cbn [read_lfields]. rewrite next_word_cons. cbn [fst snd s_words].
      replace (Z.of_nat (length (Z.of_nat (length ts) :: (o_words a ++ o_words b) ++ ws)) <? Z.of_nat (length ts))
        with false by (symmetry; apply Z.ltb_ge; simpl; rewrite !length_app; lia).
      rewrite Nat2Z.id, <- app_assoc.
      rewrite (read_count_rt w r el fs1 ts a (o_words b ++ ws) rb n x rb1 n1 T Ok1 Ea D1). cbn [fst snd].
      destruct (IH b ((i, TList ts) :: e0) ws rb1 n1 x rb' n' x' T RL Ok2 eq_refl Ws D2 L)
        as (e1 & R2 & E2 & K2).
      exists (e1 ++ [(i, TList ts)]). rewrite <- app_assoc. split; [exact R2|]. split.
      * intros h u Hin. apply in_app_or in Hin as [Hin|[Hin|[]]]; [auto|]. injection Hin as <- <-. exact Ei.
      * intros h [<-|Hh]; rewrite map_app; apply in_or_app; [right; left; reflexivity | left; auto].
    + destruct fs as [|lf' fs]; [|discriminate]. destruct Ws as [->|Ws]; [|discriminate].
      destruct (env_get i e) as [[| | |ts]|] eqn:Ei; try discriminate.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate]. cbn [lfields_out] in H.
      injection H as <-. cbn [o_words o_defs wapp wnil] in *. rewrite !app_nil_r in *.
      unfold lfields_locals in L. cbn [flat_map app locals_read] in L. subst x'.
      cbn [read_lfields s_words]. rewrite (read_rest_rt w r el fs1 ts a rb n x rb' n' _ T Ok1 Ea D (le_n _)).
      cbn [fst snd]. exists [(i, TList ts)]. split; [reflexivity|]. split.
      * intros h u [Hin|[]]. injection Hin as <- <-. exact Ei.
      * intros h [<-|[]]. left. reflexivity.
Qed.

(** An instruction's fields define at most its words plus their
    costs; a list's elements cost nothing more. *)
Definition lcost (lf : lfield) : Z := match lf with FOne f => fcost f | FCount _ _ _ => -1 | FRest _ _ _ => 0 end.

(** The sum of an instruction's fields' [lcost]. *)
Definition lscost (fs : list lfield) : Z := fold_right (fun lf c => lcost lf + c) 0 fs.

(** The cost bound of an instruction's fields. *)
Lemma lfields_cost : forall w e fs o, Forall (lfield_ok e) fs -> lfields_out w e fs = Some o ->
  Z.of_nat (length (o_defs o)) <= Z.of_nat (length (o_words o)) + lscost fs.
Proof.
  intros w e. induction fs as [|lf fs IH]; intros o Ok H; cbn [lfields_out] in H.
  - injection H as <-. simpl. lia.
  - inversion Ok as [|? ? Ok1 Ok2]; subst. destruct lf as [f|i el fs1|i el fs1].
    + destruct (field_out w e f) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      pose proof (field_cost _ _ _ _ Ea). specialize (IH b Ok2 eq_refl).
      cbn [o_words o_defs wapp lscost lcost fold_right] in *. unfold lscost in IH. rewrite !length_app. lia.
    + destruct (env_get i e) as [[| | |ts]|]; try discriminate.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      destruct (elems_cost _ _ _ _ _ Ok1 Ea). specialize (IH b Ok2 eq_refl).
      cbn [o_words o_defs wapp wwords lscost lcost fold_right app] in *. unfold lscost in IH.
      cbn [length]. rewrite !length_app. lia.
    + destruct (env_get i e) as [[| | |ts]|]; try discriminate.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      destruct (elems_cost _ _ _ _ _ Ok1 Ea). specialize (IH b Ok2 eq_refl).
      cbn [o_words o_defs wapp lscost lcost fold_right] in *. unfold lscost in IH. rewrite !length_app. lia.
Qed.

(** ## What an instruction defines *)

(** The temporaries a field's words define. *)
Definition field_defs (e : env) (f : field) : list term :=
  match f with
  | FDef i => match env_get i e with Some d => [d] | None => [] end
  | FResult i => match env_get i e with
                 | Some v => match result_defs v with Some ds => ds | None => [] end
                 | None => []
                 end
  | _ => []
  end.

(** What a field writes defines its [field_defs]. *)
Lemma field_out_defs : forall w e f o, field_out w e f = Some o -> o_defs o = field_defs e f.
Proof.
  intros w e f o H.
  destruct f as [i|i|en i|i|i|i|i|i|i|i|i|i|i|i]; cbn [field_defs];
    cbv beta iota delta [field_out] in H; try (destruct (env_get i e) as [v|]; [|discriminate]).
  - injection H as <-. reflexivity.
  - destruct (enc_code EClass v); [injection H as <-; reflexivity | discriminate].
  - destruct (enc_code en v); [injection H as <-; reflexivity | discriminate].
  - destruct v; try discriminate. destruct (u32ok n); [injection H as <-; reflexivity | discriminate].
  - destruct v; try discriminate. destruct (i64ok n); [injection H as <-; reflexivity | discriminate].
  - apply (opnd_shape _ _ _ H).
  - destruct (nm_find v (w_labels w)); [injection H as <-; reflexivity | discriminate].
  - destruct (app_args "poll" 1 v) as [[|l [|]]|];
      [ | destruct (nm_find l (w_labels w)); [injection H as <-; reflexivity | discriminate] | | ];
      (destruct (nm_find v (w_labels w)); [injection H as <-; reflexivity | discriminate]).
  - destruct (nm_find v (w_locals w)); [injection H as <-; reflexivity | discriminate].
  - injection H as <-. reflexivity.
  - destruct v; try discriminate. destruct (nm_find _ (w_strs w)); [injection H as <-; reflexivity | discriminate].
  - destruct (result_shape _ _ H) as (_ & _ & R). rewrite R. reflexivity.
  - destruct (is_atom "none" v); [injection H as <-; reflexivity|].
    destruct (app_args "lower" 1 v) as [[|p [|]]|]; try discriminate.
    destruct (opnd_out w p) as [op|] eqn:Eo; [|discriminate]. injection H as <-.
    destruct (opnd_shape _ _ _ Eo) as [A _]. cbn [o_defs wapp wwords]. rewrite A. reflexivity.
  - destruct (app_args "address" 1 v) as [[|p [|]]|];
      [ | destruct (opnd_out w p) as [op|] eqn:Eo; [|discriminate]; injection H as <-;
          destruct (opnd_shape _ _ _ Eo) as [A _]; cbn [o_defs wapp wwords]; rewrite A; reflexivity | | ];
      (destruct (opnd_out w v) as [op|] eqn:Eo; [|discriminate]; injection H as <-;
       destruct (opnd_shape _ _ _ Eo) as [A _]; cbn [o_defs wapp wwords]; rewrite A; reflexivity).
Qed.

(** A value names no temporary it defines. *)
Lemma value_parts_defs : forall v, p_defs (value_parts v) = [].
Proof.
  intros v. unfold value_parts. destruct v as [| | f [|x []] |]; try reflexivity.
  destruct (String.eqb f "global"); [reflexivity|]. destruct (String.eqb f "const"); [|reflexivity].
  destruct x; reflexivity.
Qed.

(** What a field holds defines its [field_defs]. *)
Lemma field_parts_defs : forall e f p, field_parts e f = Some p -> p_defs p = field_defs e f.
Proof.
  intros e f p H. destruct f as [i|i|en i|i|i|i|i|i|i|i|i|i|i|i]; cbn [field_defs];
    cbv beta iota delta [field_parts] in H; try (injection H as <-; reflexivity);
    destruct (env_get i e) as [v|]; try discriminate.
  - injection H as <-. reflexivity.
  - injection H as <-. apply value_parts_defs.
  - injection H as <-. reflexivity.
  - destruct (result_defs v); [injection H as <-; reflexivity | discriminate].
  - destruct (app_args "lower" 1 v) as [[|p' [|]]|]; injection H as <-; try reflexivity.
    apply value_parts_defs.
  - destruct (app_args "address" 1 v) as [[|p' [|]]|]; injection H as <-; apply value_parts_defs.
Qed.

(** The temporaries some fields define are the same whether their
    words or their parts say so. *)
Lemma fields_parts_defs : forall w e fs o p, fields_out w e fs = Some o -> fields_parts e fs = Some p ->
  p_defs p = o_defs o.
Proof.
  intros w e fs. unfold fields_parts. induction fs as [|f fs IH]; intros o p H P; cbn [mapo fields_out] in *.
  - injection H as <-. injection P as <-. reflexivity.
  - destruct (field_parts e f) as [pf|] eqn:Ef; [|discriminate].
    destruct (mapo (field_parts e) fs) as [ps|] eqn:Eps; [|discriminate]. injection P as <-.
    destruct (field_out w e f) as [a|] eqn:Ea; [|discriminate].
    destruct (fields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    cbn [fold_right p_defs parts_app o_defs wapp].
    rewrite (IH b (fold_right parts_app no_parts ps) eq_refl eq_refl).
    rewrite (field_parts_defs _ _ _ Ef), (field_out_defs _ _ _ _ Ea). reflexivity.
Qed.

(** The same for the elements of a list. *)
Lemma elems_parts_defs : forall w el fs ts o p, elems_out w el fs ts = Some o ->
  elems_parts el fs ts = Some p -> p_defs p = o_defs o.
Proof.
  intros w el fs. unfold elems_parts. induction ts as [|t ts IH]; intros o p H P; cbn [mapo elems_out] in *.
  - injection H as <-. injection P as <-. reflexivity.
  - destruct (match_pat el t []) as [et|] eqn:Et; [|discriminate]. cbv beta iota in P, H.
    destruct (fields_parts et fs) as [pf|] eqn:Ef; [|discriminate].
    destruct (mapo _ ts) as [ps|] eqn:Eps; [|discriminate]. injection P as <-.
    destruct (fields_out w et fs) as [a|] eqn:Ea; [|discriminate].
    destruct (elems_out w el fs ts) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    cbn [fold_right p_defs parts_app o_defs wapp].
    rewrite (IH b (fold_right parts_app no_parts ps) eq_refl eq_refl).
    rewrite (fields_parts_defs _ _ _ _ _ Ea Ef). reflexivity.
Qed.

(** The temporaries an instruction defines are the same whether its
    words or its parts say so. *)
Lemma lfields_parts_defs : forall w e fs o p, lfields_out w e fs = Some o -> inst_parts e fs = Some p ->
  p_defs p = o_defs o.
Proof.
  intros w e fs. unfold inst_parts.
  induction fs as [|lf fs IH]; intros o p H P; cbn [mapo lfields_out] in *.
  - injection H as <-. injection P as <-. reflexivity.
  - destruct lf as [f|i el fs1|i el fs1].
    + destruct (field_parts e f) as [pf|] eqn:Ef; [|discriminate].
      destruct (mapo _ fs) as [ps|] eqn:Eps; [|discriminate]. injection P as <-.
      destruct (field_out w e f) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [fold_right p_defs parts_app o_defs wapp].
      rewrite (IH b (fold_right parts_app no_parts ps) eq_refl eq_refl).
      rewrite (field_parts_defs _ _ _ Ef), (field_out_defs _ _ _ _ Ea). reflexivity.
    + destruct (env_get i e) as [[| | |ts]|]; try discriminate. cbv beta iota in P, H.
      destruct (elems_parts el fs1 ts) as [pf|] eqn:Ef; [|discriminate].
      destruct (mapo _ fs) as [ps|] eqn:Eps; [|discriminate]. injection P as <-.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [fold_right p_defs parts_app o_defs wapp wwords app].
      rewrite (IH b (fold_right parts_app no_parts ps) eq_refl eq_refl).
      rewrite (elems_parts_defs _ _ _ _ _ _ Ea Ef). reflexivity.
    + destruct (env_get i e) as [[| | |ts]|]; try discriminate. cbv beta iota in P, H.
      destruct (elems_parts el fs1 ts) as [pf|] eqn:Ef; [|discriminate].
      destruct (mapo _ fs) as [ps|] eqn:Eps; [|discriminate]. injection P as <-.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [fold_right p_defs parts_app o_defs wapp].
      rewrite (IH b (fold_right parts_app no_parts ps) eq_refl eq_refl).
      rewrite (elems_parts_defs _ _ _ _ _ _ Ea Ef). reflexivity.
Qed.

(** ## The table of forms *)

(** Whether the numbers of l differ. *)
Fixpoint nodupb (l : list nat) : bool :=
  match l with [] => true | x :: l' => negb (existsb (Nat.eqb x) l') && nodupb l' end.

(** [nodupb] is sound. *)
Lemma nodupb_ok : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [|x l IH]; simpl; intros H; constructor.
  - apply andb_true_iff in H as [H _]. intros Hx. apply negb_true_iff in H.
    rewrite <- not_true_iff_false in H. apply H. apply existsb_exists. exists x.
    split; [exact Hx | apply Nat.eqb_refl].
  - apply andb_true_iff in H as [_ H]. auto.
Qed.

(** Whether every number of hs is one of ks. *)
Definition coveredb (hs ks : list nat) : bool := forallb (fun h => existsb (Nat.eqb h) ks) hs.

(** [coveredb] is sound. *)
Lemma coveredb_ok : forall hs ks, coveredb hs ks = true -> forall h, In h hs -> In h ks.
Proof.
  intros hs ks H h Hh. unfold coveredb in H. rewrite forallb_forall in H. specialize (H h Hh).
  apply existsb_exists in H as (k & Hk & E). apply Nat.eqb_eq in E. subst. exact Hk.
Qed.

(** [elem_ok] as a computation. *)
Definition elem_okb (el : pat) (fs : list field) : bool :=
  nodupb (pat_holes el) && coveredb (pat_holes el) (map field_hole fs)
  && forallb (fun f => negb (is_localdef f)) fs && existsb writes_word fs && (fscost fs <=? 0).

(** [elem_okb] is sound. *)
Lemma elem_okb_ok : forall el fs, elem_okb el fs = true -> elem_ok el fs.
Proof.
  intros el fs H. unfold elem_okb in H. repeat rewrite andb_true_iff in H.
  destruct H as ((((A & B) & C) & D) & E). split; [apply nodupb_ok; exact A|].
  split; [apply coveredb_ok; exact B|]. split; [|split; [exact D | apply Z.leb_le; exact E]].
  apply Forall_forall. intros f Hf. rewrite forallb_forall in C. specialize (C f Hf).
  apply negb_true_iff in C. exact C.
Qed.

(** Whether an instruction's field defines a local. *)
Definition lf_localdef (lf : lfield) : bool :=
  match lf with FOne f => is_localdef f | FCount _ _ fs | FRest _ _ fs => existsb is_localdef fs end.

(** Whether an instruction's field defines temporaries. *)
Definition lf_defines (lf : lfield) : bool :=
  match lf with FOne f => defines f | FCount _ _ fs | FRest _ _ fs => existsb defines fs end.

(** Whether a pattern can match a `local_alloc/2`. *)
Definition top_local (p : pat) : bool :=
  match p with PH _ => true | PC f [_; _] => String.eqb f "local_alloc" | _ => false end.

(** The form of `local_alloc(X, Size)`, the one that defines a local. *)
Definition local_form : form :=
  mkForm 100 (PC "local_alloc" [PH 0; PH 1]) [FOne (FLocalDef 0); FOne (FI64 1)].

(** What every form satisfies, as a computation. *)
Definition form_okb (f : form) : bool :=
  nodupb (pat_holes (f_pat f)) && coveredb (pat_holes (f_pat f)) (map lfield_hole (f_fields f))
  && rest_last (f_fields f)
  && forallb (fun lf => match lf with
                        | FOne _ => true
                        | FCount _ el fs1 | FRest _ el fs1 => elem_okb el fs1
                        end) (f_fields f)
  && (lscost (f_fields f) <=? 1)
  && (Z.eqb (f_code f) 100 || (negb (existsb lf_localdef (f_fields f)) && negb (top_local (f_pat f))))
  && (negb (Z.eqb (group (f_code f)) 2) || negb (existsb lf_defines (f_fields f)))
  && (2 <=? f_code f) && (f_code f <? 65536).

(** Whether the integers of cs differ. *)
Fixpoint codes_nodupb (cs : list Z) : bool :=
  match cs with [] => true | c :: cs' => negb (existsb (Z.eqb c) cs') && codes_nodupb cs' end.

(** The table of forms, checked: every form satisfies [form_okb], the
    opcodes differ, and opcode 100 is [local_form]. *)
Lemma forms_checked : forallb form_okb forms = true /\ codes_nodupb (map f_code forms) = true
  /\ form_of_code forms 100 = Some local_form.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** The form [find_form] picks is in the table and matches. *)
Lemma find_form_in : forall fs t f e, find_form fs t = Some (f, e) ->
  In f fs /\ match_pat (f_pat f) t [] = Some e.
Proof.
  induction fs as [|g fs IH]; intros t f e H; simpl in H; [discriminate|].
  destruct (match_pat (f_pat g) t []) as [e'|] eqn:E; [injection H as <- <-; simpl; auto|].
  destruct (IH _ _ _ H). simpl. auto.
Qed.

(** With distinct opcodes, a form is the form of its opcode. *)
Lemma form_of_code_in : forall fs f, codes_nodupb (map f_code fs) = true -> In f fs ->
  form_of_code fs (f_code f) = Some f.
Proof.
  induction fs as [|g fs IH]; intros f Hd Hin; [contradiction|]. simpl in *.
  apply andb_true_iff in Hd as [Hg Hd]. destruct Hin as [<-|Hin]; [rewrite Z.eqb_refl; reflexivity|].
  destruct (Z.eqb_spec (f_code g) (f_code f)) as [E|]; [|auto].
  exfalso. apply negb_true_iff in Hg. rewrite <- not_true_iff_false in Hg. apply Hg.
  apply existsb_exists. exists (f_code f). split; [apply in_map; exact Hin | apply Z.eqb_eq; exact E].
Qed.

(** What a form of the table satisfies. *)
Record form_ok (f : form) : Prop := {
  fo_nodup : NoDup (pat_holes (f_pat f));
  fo_cover : forall h, In h (pat_holes (f_pat f)) -> In h (map lfield_hole (f_fields f));
  fo_rest : rest_last (f_fields f) = true;
  fo_elems : Forall (fun lf => match lf with
                               | FOne _ => True
                               | FCount _ el fs1 | FRest _ el fs1 => elem_ok el fs1
                               end) (f_fields f);
  fo_cost : lscost (f_fields f) <= 1;
  fo_local : f = local_form \/ (existsb lf_localdef (f_fields f) = false /\ top_local (f_pat f) = false);
  fo_jump : group (f_code f) = 2 -> existsb lf_defines (f_fields f) = false;
  fo_code : 2 <= f_code f < 65536;
  fo_of_code : form_of_code forms (f_code f) = Some f
}.

(** Every form of the table is [form_ok]. *)
Lemma form_in_ok : forall f, In f forms -> form_ok f.
Proof.
  intros f Hf. destruct forms_checked as (A & B & C).
  pose proof (form_of_code_in _ _ B Hf) as Hc.
  rewrite forallb_forall in A. specialize (A f Hf). unfold form_okb in A.
  repeat rewrite andb_true_iff in A.
  destruct A as ((((((((A1 & A2) & A3) & A4) & A5) & A6) & A7) & A8) & A9).
  split.
  - apply nodupb_ok. exact A1.
  - apply coveredb_ok. exact A2.
  - exact A3.
  - rewrite forallb_forall in A4. apply Forall_forall. intros lf Hlf. specialize (A4 lf Hlf).
    destruct lf; [exact I | apply elem_okb_ok; exact A4 | apply elem_okb_ok; exact A4].
  - apply Z.leb_le. exact A5.
  - apply orb_true_iff in A6 as [A6|A6].
    + left. apply Z.eqb_eq in A6. rewrite A6 in Hc. rewrite C in Hc. injection Hc as <-. reflexivity.
    + right. apply andb_true_iff in A6 as [X Y]. apply negb_true_iff in X, Y. auto.
  - intros G. rewrite G in A7. simpl in A7. apply negb_true_iff. exact A7.
  - apply Z.leb_le in A8. apply Z.ltb_lt in A9. lia.
  - exact Hc.
Qed.

(** The locals an instruction defines: one for `local_alloc(X, _)`. *)
Definition inst_locals (t : term) : list term :=
  match app_args "local_alloc" 2 t with Some [x; _] => [x] | _ => [] end.

(** A list of patterns matches as many terms. *)
Lemma match_pats_length : forall ps ts e0 e, match_pats ps ts e0 = Some e -> length ts = length ps.
Proof.
  induction ps as [|p ps IH]; intros [|t ts] e0 e H; simpl in H; try discriminate; auto.
  destruct (match_pat p t e0); [|discriminate]. simpl. f_equal. eauto.
Qed.

(** The fields of a form that matched t define t's locals, and each is
    [lfield_ok]. *)
Lemma form_locals : forall f t e, In f forms -> match_pat (f_pat f) t [] = Some e ->
  lfields_locals e (f_fields f) = inst_locals t /\ Forall (lfield_ok e) (f_fields f).
Proof.
  intros f t e Hf Hm. destruct (form_in_ok f Hf) as [_ _ _ El _ Lo _ _ _].
  destruct Lo as [->|[L1 L2]].
  - cbn [f_pat local_form] in Hm. rewrite match_pat_eq in Hm.
    destruct t as [| | g ts |]; try discriminate.
    destruct (String.eqb_spec "local_alloc" g) as [<-|]; [|discriminate].
    destruct ts as [|x [|y []]]; cbn in Hm; try discriminate.
    injection Hm as <-. split; [reflexivity|].
    repeat constructor. cbn. discriminate.
  - assert (Hl : lfields_locals e (f_fields f) = []).
    { unfold lfields_locals. clear El. induction (f_fields f) as [|lf fs IH]; [reflexivity|].
      simpl in L1. apply orb_false_iff in L1 as [L1 L3]. simpl. rewrite (IH L3).
      destruct lf as [g| |]; [destruct g; simpl in L1; try discriminate | |]; reflexivity. }
    split.
    + rewrite Hl. unfold inst_locals. rewrite match_pat_eq in Hm.
      destruct (f_pat f) as [i|s|g ps|ps]; simpl in L2; try discriminate.
      * destruct (is_atom s t) eqn:E; [|discriminate]. apply is_atom_inv in E. subst. reflexivity.
      * destruct t as [| | h ts |]; try discriminate. destruct (String.eqb_spec g h) as [<-|]; [|discriminate].
        apply match_pats_length in Hm. unfold app_args.
        destruct (String.eqb_spec "local_alloc" g) as [<-|]; [|reflexivity].
        destruct (Nat.eqb_spec 2 (length ts)); [|reflexivity].
        destruct ps as [|p1 [|p2 [|]]]; simpl in Hm; try lia. simpl in L2. discriminate.
      * destruct t; try discriminate. reflexivity.
    + apply Forall_forall. intros lf Hlf. rewrite Forall_forall in El. specialize (El lf Hlf).
      destruct lf as [g| |]; [|exact El|exact El]. cbn [lfield_ok].
      assert (G : lf_localdef (FOne g) = false).
      { destruct (lf_localdef (FOne g)) eqn:E; [|reflexivity].
        rewrite <- L1. symmetry. apply existsb_exists. eauto. }
      destruct g; simpl in G; try discriminate; exact I.
Qed.

(** ## Temporaries *)

(** The writer's temporaries M and count N come from numbering, from
    the map m and the count n, the definitions q still to come; the
    numbers so far are below n. *)
Definition temps_inv (M : nmap Z) (N : Z) (n : Z) (q : list term) : Prop :=
  exists m acc, fst (fst (number q m n acc)) = M /\ snd (fst (number q m n acc)) = N /\
    0 <= n /\ (forall y i, nm_find y m = Some i -> 0 <= i < n).

(** The rebind words of definitions read back as the definitions,
    with the prefix or, if every word is 0, without it. *)
Lemma rebinds_rt : forall r (M : nmap Z) N ds n q rbw n',
  (forall y (i : Z), nm_find y M = Some i -> ZMap.find i (r_temps r) = Some y) ->
  rebinds M n ds = Some (rbw, n') -> temps_inv M N n (ds ++ q) ->
  temps_inv M N n' q /\ (forall more, defs_read r ds (Some (rbw ++ more)) n (Some more) n')
  /\ (existsb (fun z => negb (Z.eqb z 0)) rbw = false -> defs_read r ds None n None n').
Proof.
  intros r M N. induction ds as [|d ds IH]; intros n q rbw n' Ok H I; cbn [rebinds] in H.
  - injection H as <- <-. split; [exact I|]. split; intros; cbn; auto.
  - destruct (nm_find d M) as [i|] eqn:Ed; [|discriminate].
    destruct I as (m & acc & IM & IN & Hn & Hm). cbn [app number] in IM, IN.
    destruct (nm_mem d m) eqn:Em.
    + unfold nm_mem in Em. destruct (nm_find d m) as [j|] eqn:Ej; [|discriminate].
      pose proof (number_keep (ds ++ q) m n acc d j Ej) as K. rewrite IM, Ed in K. injection K as <-.
      destruct (Hm d i Ej) as [Hi0 Hi].
      replace (Z.eqb i n) with false in H by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in H.
      destruct (rebinds M _ ds) as [[rbw1 n1]|] eqn:Er; [|discriminate]. injection H as <- <-.
      destruct (IH n q rbw1 n1 Ok Er (ex_intro _ m (ex_intro _ acc (conj IM (conj IN (conj Hn Hm))))))
        as (I' & D1 & D2).
      split; [exact I'|]. split.
      * intros more. cbn [defs_read app fst snd]. exists (Some (rbw1 ++ more)), n. split; [|apply D1].
        intros ws x. unfold def_name. cbn [s_rebinds s_next s_words s_local].
        replace (Z.eqb (i + 1) 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (i + 1 - 1 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (i + 1 - 1) with i by lia. rewrite (Ok _ _ Ed). reflexivity.
      * cbn [existsb fst snd]. replace (Z.eqb (i + 1) 0) with false by (symmetry; apply Z.eqb_neq; lia).
        discriminate.
    + pose proof (number_keep (ds ++ q) (nm_add d n m) (n + 1) (d :: acc) d n) as K.
      rewrite nm_find_add in K. unfold name_eqb in K. rewrite term_eqb_refl in K. specialize (K eq_refl).
      rewrite IM, Ed in K. injection K as ->.
      rewrite Z.eqb_refl in H. cbv beta iota in H.
      destruct (rebinds M _ ds) as [[rbw1 n1]|] eqn:Er; [|discriminate]. injection H as <- <-.
      assert (I1 : temps_inv M N (n + 1) (ds ++ q)).
      { exists (nm_add d n m), (d :: acc). split; [exact IM|]. split; [exact IN|]. split; [lia|].
        intros y j Hy. rewrite nm_find_add in Hy. destruct (name_eqb y d); [injection Hy as <-; lia|].
        destruct (Hm y j Hy); lia. }
      destruct (IH (n + 1) q rbw1 n1 Ok Er I1) as (I' & D1 & D2).
      split; [exact I'|]. split.
      * intros more. cbn [defs_read app fst snd]. exists (Some (rbw1 ++ more)), (n + 1). split; [|apply D1].
        intros ws x. unfold def_name. cbn [s_rebinds s_next s_words s_local].
        rewrite (Ok _ _ Ed). reflexivity.
      * cbn [existsb fst snd defs_read]. intros Hx. exists None, (n + 1). split; [|apply D2; exact Hx].
        intros ws x. unfold def_name. cbn [s_rebinds s_next s_words s_local].
        rewrite (Ok _ _ Ed). reflexivity.
Qed.

(** ## One instruction *)

(** The reader's locals from the id x on are those of ql. *)
Definition locals_inv (r : rtab) (x : Z) (ql : list term) : Prop :=
  forall k v, nth_error ql k = Some v -> ZMap.find (x + Z.of_nat k) (r_locals r) = Some v.

(** The first locals of ql read, and the rest after them. *)
Lemma locals_inv_split : forall r a b x, locals_inv r x (a ++ b) ->
  locals_read r a x (x + Z.of_nat (length a)) /\ locals_inv r (x + Z.of_nat (length a)) b.
Proof.
  intros r a. induction a as [|v a IH]; intros b x H; cbn [locals_read length app] in *.
  - split; [lia|]. intros k u Hk. rewrite Z.add_0_r. apply H. exact Hk.
  - assert (H1 : locals_inv r (x + 1) (a ++ b)).
    { intros k u Hk. replace (x + 1 + Z.of_nat k) with (x + Z.of_nat (S k)) by lia. apply H. exact Hk. }
    destruct (IH b (x + 1) H1) as [A B]. split; [split|].
    + rewrite <- (Z.add_0_r x). apply (H 0%nat). reflexivity.
    + replace (x + Z.of_nat (S (length a))) with (x + 1 + Z.of_nat (length a)) by lia. exact A.
    + replace (x + Z.of_nat (S (length a))) with (x + 1 + Z.of_nat (length a)) by lia. exact B.
Qed.

(** The header word of an instruction of opcode c and length len. *)
Lemma header_word : forall c len, 0 <= c < 65536 -> 0 <= len ->
  (c + len * 65536) mod 65536 = c /\ (c + len * 65536) / 65536 = len.
Proof.
  intros c len Hc Hl. split.
  - rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(** An instruction without a rebind prefix reads back. *)
Lemma read_inst_plain : forall r g n x c body rest f e' t n2 x2,
  2 <= c < 65536 -> group c = g -> form_of_code forms c = Some f ->
  read_lfields r (f_fields f) [] (mkRst body None n x) = Some (e', mkRst [] None n2 x2) ->
  fill_pat (f_pat f) e' = Some t ->
  read_inst r g n x ((c + (Z.of_nat (length body) + 1) * 65536) :: body ++ rest) = Some (t, n2, x2, rest).
Proof.
  intros r g n x c body rest f e' t n2 x2 Hc Hg Hf Hr Ht.
  destruct (header_word c (Z.of_nat (length body) + 1) ltac:(lia) ltac:(lia)) as [M D].
  unfold read_inst. cbv beta iota zeta. rewrite M. unfold rebind_code.
  replace (Z.eqb c 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
  rewrite M, D, Hg, Z.eqb_refl. replace (Z.of_nat (length body) + 1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv beta iota. rewrite Hf. replace (Z.to_nat (Z.of_nat (length body) + 1 - 1)) with (length body) by lia.
  rewrite take_app. cbv beta iota. cbn [fst snd]. rewrite Hr. cbv beta iota. cbn [s_words s_rebinds s_next s_local].
  rewrite Ht. reflexivity.
Qed.

(** An instruction with a rebind prefix reads back. *)
Lemma read_inst_rebind : forall r g n x c rbw body rest f e' t n2 x2,
  2 <= c < 65536 -> group c = g -> form_of_code forms c = Some f -> rbw <> [] ->
  read_lfields r (f_fields f) [] (mkRst body (Some rbw) n x) = Some (e', mkRst [] (Some []) n2 x2) ->
  fill_pat (f_pat f) e' = Some t ->
  read_inst r g n x ((rebind_code + (Z.of_nat (length rbw) + 1) * 65536) :: rbw
                     ++ (c + (Z.of_nat (length body) + 1) * 65536) :: body ++ rest)
  = Some (t, n2, x2, rest).
Proof.
  intros r g n x c rbw body rest f e' t n2 x2 Hc Hg Hf Hrb Hr Ht.
  destruct (header_word c (Z.of_nat (length body) + 1) ltac:(lia) ltac:(lia)) as [M D].
  unfold rebind_code in *.
  destruct (header_word 1 (Z.of_nat (length rbw) + 1) ltac:(lia) ltac:(lia)) as [M1 D1].
  unfold read_inst. cbv beta iota zeta. rewrite M1. unfold rebind_code. rewrite Z.eqb_refl. cbv beta iota.
  rewrite D1. destruct rbw as [|z rbw]; [congruence|]. cbn [length].
  replace (Z.of_nat (S (length rbw)) + 1 <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv beta iota. replace (Z.to_nat (Z.of_nat (S (length rbw)) + 1 - 1)) with (length (z :: rbw)) by (cbn [length]; lia).
  rewrite take_app. cbv beta iota. cbn [fst snd].
  rewrite M, D, Hg, Z.eqb_refl. replace (Z.of_nat (length body) + 1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv beta iota. rewrite Hf. replace (Z.to_nat (Z.of_nat (length body) + 1 - 1)) with (length body) by lia.
  rewrite take_app. cbv beta iota. cbn [fst snd]. rewrite Hr. cbv beta iota. cbn [s_words s_rebinds s_next s_local].
  rewrite Ht. reflexivity.
Qed.

(** The words of an instruction: its form's fields' words, its opcode
    first, and words enough for the temporaries it defines. *)
Lemma inst_shape : forall w g b n t ws n' ord, inst_words w g b n t = Some (ws, n', ord) ->
  exists f e o, find_form forms t = Some (f, e) /\ group (f_code f) = g /\
    lfields_out w e (f_fields f) = Some o /\ (length (o_defs o) <= length ws)%nat /\
    (forall rest, next_opcode (ws ++ rest) = Some (f_code f)).
Proof.
  intros w g b n t ws n' ord H. unfold inst_words in H.
  destruct (find_form forms t) as [[f e]|] eqn:Ef; [|discriminate]. cbn [fst snd] in H.
  destruct (Z.eqb_spec (group (f_code f)) g) as [Eg|]; [|discriminate].
  change (negb true) with false in H. cbv beta iota in H.
  destruct (lfields_out w e (f_fields f)) as [o|] eqn:Eo; [|discriminate].
  destruct (rebinds (w_temps w) n (o_defs o)) as [[rbw n2]|] eqn:Erb; [|discriminate].
  cbv zeta in H. try change (fst (rbw, n2)) with rbw in H. try change (snd (rbw, n2)) with n2 in H.
  destruct (65536 <=? Z.of_nat (length (o_words o)) + 1) eqn:Elen; [discriminate|].
  remember (rebind_code + (Z.of_nat (length rbw) + 1) * 65536) as h0 eqn:E0 in H.
  injection H as <- <- _.
  destruct (find_form_in _ _ _ _ Ef) as [Hin Hm]. pose proof (form_in_ok f Hin) as Fo.
  destruct (form_locals f t e Hin Hm) as [_ Lok].
  pose proof (lfields_cost w e _ o Lok Eo) as C. pose proof (fo_cost f Fo) as C1.
  pose proof (fo_code f Fo) as Hc.
  destruct (header_word (f_code f) (Z.of_nat (length (o_words o)) + 1) ltac:(lia) ltac:(lia)) as [M D].
  exists f, e, o. split; [reflexivity|]. split; [exact Eg|]. split; [exact Eo|]. split.
  - rewrite length_app. cbn [length]. lia.
  - intros rest. rewrite <- app_assoc.
    remember (f_code f + (Z.of_nat (length (o_words o)) + 1) * 65536) as h1 eqn:E1.
    clear D.
    destruct (existsb (fun z => negb (Z.eqb z 0)) rbw).
    + rewrite <- !app_comm_cons.
      destruct (header_word rebind_code (Z.of_nat (length rbw) + 1) ltac:(unfold rebind_code; lia) ltac:(lia))
        as [M1 D1]. rewrite <- E0 in M1, D1.
      unfold next_opcode. cbv beta iota. rewrite M1, Z.eqb_refl, D1.
      replace (Z.to_nat (Z.of_nat (length rbw) + 1 - 1)) with (length rbw) by lia.
      rewrite nth_error_app2 by apply Nat.le_refl. rewrite Nat.sub_diag.
      cbn [nth_error]. cbv beta iota. rewrite M. reflexivity.
    + rewrite app_nil_l, <- app_comm_cons. unfold next_opcode. cbv beta iota. rewrite M. unfold rebind_code.
      replace (Z.eqb (f_code f) 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(** One instruction reads back, its definitions named as the writer
    numbered them and its locals in turn. *)
Lemma read_inst_rt : forall w r g b n t ws n' ord x ds q ql rest N,
  tabs_ok w r -> inst_words w g b n t = Some (ws, n', ord) ->
  (forall f e o, find_form forms t = Some (f, e) -> lfields_out w e (f_fields f) = Some o -> o_defs o = ds) ->
  temps_inv (w_temps w) N n (ds ++ q) -> locals_inv r x (inst_locals t ++ ql) ->
  temps_inv (w_temps w) N n' q /\ locals_inv r (x + Z.of_nat (length (inst_locals t))) ql /\
  read_inst r g n x (ws ++ rest) = Some (t, n', x + Z.of_nat (length (inst_locals t)), rest).
Proof.
  intros w r g b n t ws n' ord x ds q ql rest N T H Hds TI LI. unfold inst_words in H.
  destruct (find_form forms t) as [[f e]|] eqn:Ef; [|discriminate]. cbn [fst snd] in H.
  destruct (Z.eqb_spec (group (f_code f)) g) as [Eg|]; [|discriminate].
  change (negb true) with false in H. cbv beta iota in H.
  destruct (lfields_out w e (f_fields f)) as [o|] eqn:Eo; [|discriminate].
  destruct (rebinds (w_temps w) n (o_defs o)) as [[rbw n2]|] eqn:Erb; [|discriminate].
  cbv zeta in H. try change (fst (rbw, n2)) with rbw in H. try change (snd (rbw, n2)) with n2 in H.
  destruct (65536 <=? Z.of_nat (length (o_words o)) + 1) eqn:Elen; [discriminate|].
  remember (rebind_code + (Z.of_nat (length rbw) + 1) * 65536) as h0 eqn:E0 in H.
  injection H as <- <- _.
  destruct (find_form_in _ _ _ _ Ef) as [Hin Hm]. pose proof (form_in_ok f Hin) as Fo.
  destruct (form_locals f t e Hin Hm) as [Lt Lok].
  rewrite <- (Hds f e o eq_refl Eo) in TI.
  destruct (rebinds_rt r (w_temps w) N (o_defs o) n q rbw n2 (ok_temps _ _ T) Erb TI) as (TI' & D1 & D2).
  destruct (locals_inv_split r (inst_locals t) ql x LI) as [LR LI'].
  rewrite <- Lt in LR.
  split; [exact TI'|]. split; [exact LI'|].
  assert (Fill : forall e1, env_of e e1 ->
                 (forall h, In h (map lfield_hole (f_fields f)) -> In h (map fst e1)) ->
                 fill_pat (f_pat f) (e1 ++ []) = Some t).
  { intros e1 E1 K1. rewrite app_nil_r. apply (match_fill _ _ _ Hm (fo_nodup f Fo)).
    intros h Hh. destruct (env_get_key h e1 (K1 h (fo_cover f Fo h Hh))) as (v & Hv).
    rewrite Hv. symmetry. apply E1. apply env_get_in. exact Hv. }
  pose proof (fo_code f Fo) as Hc. pose proof (fo_of_code f Fo) as Hcode.
  destruct (existsb (fun z => negb (Z.eqb z 0)) rbw) eqn:Ex.
  - specialize (D1 []). rewrite app_nil_r in D1.
    destruct (read_lfields_rt w r e (f_fields f) o [] [] (Some rbw) n x (Some []) n2 _ T (fo_rest f Fo)
                Lok Eo (or_introl eq_refl) D1 LR) as (e1 & R & E1 & K1).
    rewrite (app_nil_r (o_words o)), Lt in R. rewrite <- app_assoc, <- !app_comm_cons. subst h0.
    apply (read_inst_rebind r g n x (f_code f) rbw (o_words o) rest f (e1 ++ [])); auto.
    destruct rbw; [discriminate | congruence].
  - specialize (D2 eq_refl).
    destruct (read_lfields_rt w r e (f_fields f) o [] [] None n x None n2 _ T (fo_rest f Fo)
                Lok Eo (or_introl eq_refl) D2 LR) as (e1 & R & E1 & K1).
    rewrite (app_nil_r (o_words o)), Lt in R. rewrite app_nil_l, <- app_comm_cons.
    apply (read_inst_plain r g n x (f_code f) (o_words o) rest f (e1 ++ [])); auto.
Qed.

(** ## Groups and blocks *)

(** The temporaries a phi or an instruction defines, as [body_words]
    gathers them. *)
Definition defs_of (t : term) : option (list term) := let* p := term_parts t in Some (p_defs p).

(** What [defs_of] gathers is what the instruction's words define. *)
Lemma defs_of_ok : forall w t d, defs_of t = Some d ->
  forall f e o, find_form forms t = Some (f, e) -> lfields_out w e (f_fields f) = Some o -> o_defs o = d.
Proof.
  intros w t d H f e o Ef Eo. unfold defs_of, term_parts in H. rewrite Ef in H. cbn [fst snd] in H.
  destruct (inst_parts e (f_fields f)) as [p|] eqn:Ep; [|discriminate]. injection H as <-.
  symmetry. apply (lfields_parts_defs w e (f_fields f) o p Eo Ep).
Qed.

(** Fields that define no temporary define none. *)
Lemma no_defines : forall w e fs o, existsb lf_defines fs = false -> lfields_out w e fs = Some o -> o_defs o = [].
Proof.
  intros w e. induction fs as [|lf fs IH]; intros o Hd H; cbn [lfields_out] in H.
  - injection H as <-. reflexivity.
  - cbn [existsb] in Hd. apply orb_false_iff in Hd as [H1 H2].
    assert (Hel : forall el fs1 ts oe, existsb defines fs1 = false -> elems_out w el fs1 ts = Some oe -> o_defs oe = []).
    { intros el fs1. induction ts as [|t ts IHt]; intros oe Hf He; cbn [elems_out] in He.
      - injection He as <-. reflexivity.
      - destruct (match_pat el t []) as [et|]; [|discriminate].
        destruct (fields_out w et fs1) as [a|] eqn:Ea; [|discriminate].
        destruct (elems_out w el fs1 ts) as [b|] eqn:Eb; [|discriminate]. injection He as <-.
        cbn [o_defs wapp]. rewrite (IHt b Hf eq_refl), app_nil_r.
        clear -Ea Hf. revert a Ea. induction fs1 as [|f fs1 IHf]; intros a Ea; cbn [fields_out] in Ea.
        + injection Ea as <-. reflexivity.
        + cbn [existsb] in Hf. apply orb_false_iff in Hf as [F1 F2].
          destruct (field_out w et f) as [a1|] eqn:E1; [|discriminate].
          destruct (fields_out w et fs1) as [a2|] eqn:E2; [|discriminate]. injection Ea as <-.
          cbn [o_defs wapp]. rewrite (IHf F2 a2 eq_refl), (field_out_defs _ _ _ _ E1), app_nil_r.
          destruct f; simpl in F1; try discriminate; reflexivity. }
    destruct lf as [f|i el fs1|i el fs1].
    + destruct (field_out w e f) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [o_defs wapp]. rewrite (IH b H2 eq_refl), (field_out_defs _ _ _ _ Ea), app_nil_r.
      destruct f; simpl in H1; try discriminate; reflexivity.
    + destruct (env_get i e) as [[| | |ts]|]; try discriminate.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [o_defs wapp wwords app]. rewrite (IH b H2 eq_refl), (Hel _ _ _ _ H1 Ea). reflexivity.
    + destruct (env_get i e) as [[| | |ts]|]; try discriminate.
      destruct (elems_out w el fs1 ts) as [a|] eqn:Ea; [|discriminate].
      destruct (lfields_out w e fs) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
      cbn [o_defs wapp]. rewrite (IH b H2 eq_refl), (Hel _ _ _ _ H1 Ea). reflexivity.
Qed.

(** A jump defines no temporary. *)
Lemma jump_defs : forall w b n t ws n' ord, inst_words w 2 b n t = Some (ws, n', ord) ->
  forall f e o, find_form forms t = Some (f, e) -> lfields_out w e (f_fields f) = Some o -> o_defs o = [].
Proof.
  intros w b n t ws n' ord H f e o Ef Eo. destruct (inst_shape _ _ _ _ _ _ _ _ H) as (f1 & e1 & o1 & E1 & G & _).
  rewrite Ef in E1. injection E1 as <- <-. destruct (find_form_in _ _ _ _ Ef) as [Hin _].
  apply (no_defines w e (f_fields f) o); [|exact Eo]. apply (fo_jump f (form_in_ok f Hin) G).
Qed.

(** A phi or a jump defines no local. *)
Lemma inst_locals_group : forall w g b n t ws n' ord, inst_words w g b n t = Some (ws, n', ord) ->
  g <> 1 -> inst_locals t = [].
Proof.
  intros w g b n t ws n' ord H G. destruct (inst_shape _ _ _ _ _ _ _ _ H) as (f & e & o & Ef & Eg & _).
  destruct (find_form_in _ _ _ _ Ef) as [Hin Hm]. pose proof (form_in_ok f Hin) as Fo.
  destruct (form_locals f t e Hin Hm) as [Lt _]. rewrite <- Lt.
  destruct (fo_local f Fo) as [->|[L1 _]]; [cbn in Eg; lia|].
  unfold lfields_locals. clear -L1. induction (f_fields f) as [|lf fs IH]; [reflexivity|].
  simpl in L1. apply orb_false_iff in L1 as [L1 L3]. simpl. rewrite (IH L3).
  destruct lf as [g| |]; [destruct g; simpl in L1; try discriminate | |]; reflexivity.
Qed.

(** The reader stops a group before the words ws. *)
Definition stops (g : Z) (ws : list Z) : Prop :=
  match next_opcode ws with Some c => group c <> g | None => True end.

(** The first opcode of a group's words that are not empty. *)
Lemma insts_next : forall w g b n ts ws n' ord, insts_words w g b n ts = Some (ws, n', ord) ->
  (ts = [] /\ ws = [] /\ n' = n) \/ (forall rest, exists c, next_opcode (ws ++ rest) = Some c /\ group c = g).
Proof.
  intros w g b n [|t ts] ws n' ord H; cbn [insts_words] in H.
  - injection H as <- <- _. left. auto.
  - right. destruct (inst_words w g b n t) as [[[ws1 n1] o1]|] eqn:E1; [|discriminate].
    destruct (insts_words w g b n1 ts) as [[[ws2 n2] o2]|]; [|discriminate]. injection H as <- <- _.
    intros rest. destruct (inst_shape _ _ _ _ _ _ _ _ E1) as (f & e & o & _ & G & _ & _ & N).
    exists (f_code f). rewrite <- app_assoc. auto.
Qed.

(** A group of instructions reads back, as many as its words hold. *)
Lemma read_group_rt : forall w r g b ts n ws n' ord x dl q ql rest fuel N,
  tabs_ok w r -> insts_words w g b n ts = Some (ws, n', ord) -> mapo defs_of ts = Some dl ->
  temps_inv (w_temps w) N n (concat dl ++ q) -> locals_inv r x (flat_map inst_locals ts ++ ql) ->
  (length ws <= fuel)%nat -> stops g rest ->
  temps_inv (w_temps w) N n' q /\ locals_inv r (x + Z.of_nat (length (flat_map inst_locals ts))) ql /\
  read_group r g fuel n x (ws ++ rest) = Some (ts, n', x + Z.of_nat (length (flat_map inst_locals ts)), rest)
  /\ (length (concat dl) <= length ws)%nat /\ (length ts <= length ws)%nat
  /\ (length (flat_map inst_locals ts) <= length ws)%nat.
Proof.
  intros w r g b. induction ts as [|t ts IH]; intros n ws n' ord x dl q ql rest fuel N T H Hd TI LI F S;
    cbn [insts_words mapo] in H, Hd.
  - injection H as <- <- _. injection Hd as <-. cbn in *. rewrite Z.add_0_r.
    split; [exact TI|]. split; [exact LI|]. split; [|lia].
    unfold stops in S. destruct fuel; cbn [read_group]; destruct (next_opcode rest) as [c|]; try reflexivity;
      replace (Z.eqb (group c) g) with false by (symmetry; apply Z.eqb_neq; exact S); reflexivity.
  - destruct (inst_words w g b n t) as [[[ws1 n1] o1]|] eqn:E1; [|discriminate].
    destruct (insts_words w g b n1 ts) as [[[ws2 n2] o2]|] eqn:E2; [|discriminate]. injection H as <- <- _.
    destruct (defs_of t) as [d|] eqn:Ed; [|discriminate].
    destruct (mapo defs_of ts) as [dl'|] eqn:Edl; [|discriminate]. injection Hd as <-.
    cbn [concat flat_map] in TI, LI |- *. rewrite <- app_assoc in TI, LI.
    destruct (read_inst_rt w r g b n t ws1 n1 o1 x d (concat dl' ++ q) (flat_map inst_locals ts ++ ql)
                (ws2 ++ rest) N T E1 (defs_of_ok w t d Ed) TI LI) as (TI1 & LI1 & R1).
    destruct (inst_shape _ _ _ _ _ _ _ _ E1) as (f & e & o & Ef & G & Eo & Ld & Nx).
    rewrite (defs_of_ok w t d Ed f e o Ef Eo) in Ld.
    assert (Lt : (length (inst_locals t) <= 1)%nat)
      by (unfold inst_locals; destruct (app_args _ _ _) as [[|? [|? [|]]]|]; simpl; lia).
    rewrite length_app in F.
    assert (Ne : ws1 <> []) by (intros ->; specialize (Nx []); discriminate).
    destruct fuel as [|fuel']; [destruct ws1; [congruence | simpl in F; lia]|].
    assert (F' : (length ws2 <= fuel')%nat) by (destruct ws1; [congruence | simpl in F; lia]).
    destruct (IH n1 ws2 n2 o2 _ dl' q ql rest fuel' N T E2 eq_refl TI1 LI1 F' S)
      as (TI2 & LI2 & R2 & L1 & L2 & L3).
    rewrite length_app, Nat2Z.inj_add, Z.add_assoc. split; [exact TI2|]. split; [exact LI2|].
    split.
    + cbn [read_group]. rewrite <- app_assoc, Nx, G, Z.eqb_refl. rewrite R1. cbv beta iota.
      rewrite R2. reflexivity.
    + rewrite !length_app. destruct ws1 as [|z ws1]; [congruence|]. cbn [length] in *.
      split; [|split]; lia.
Qed.


(** The locals a block's instructions define. *)
Definition block_locals (bt : term) : list term :=
  match block_parts bt with Some (_, _, insts, _) => flat_map inst_locals insts | None => [] end.

(** The reader's labels from the index b on are those of the blocks. *)
Fixpoint labels_at (r : rtab) (b : Z) (bs : list term) : Prop :=
  match bs with
  | [] => True
  | bt :: bs' => (forall l phis insts j, block_parts bt = Some (l, phis, insts, j) ->
                  ZMap.find b (r_labels r) = Some l) /\ labels_at r (b + 1) bs'
  end.

(** A block's parts make the block. *)
Lemma block_parts_inv : forall bt l phis insts j, block_parts bt = Some (l, phis, insts, j) ->
  bt = TApp "block" [l; TList phis; TList insts; j].
Proof.
  intros bt l phis insts j H. unfold block_parts in H.
  destruct (app_args "block" 4 bt) as [[|l' [|[| | |ps] [|[| | |is] [|j' []]]]]|] eqn:E; try discriminate.
  injection H as <- <- <- <-. apply app_args_inv in E as [-> _]. reflexivity.
Qed.

(** The phis of a group define no local. *)
Lemma phis_locals : forall w b n phis ws n' ord, insts_words w 0 b n phis = Some (ws, n', ord) ->
  flat_map inst_locals phis = [].
Proof.
  intros w b n phis. revert n. induction phis as [|t ts IH]; intros n ws n' ord H; [reflexivity|].
  cbn [insts_words] in H. destruct (inst_words w 0 b n t) as [[[a na] oa]|] eqn:Ea; [|discriminate].
  destruct (insts_words w 0 b na ts) as [[[c nc] oc]|] eqn:Ec; [|discriminate].
  cbn [flat_map]. rewrite (inst_locals_group _ _ _ _ _ _ _ _ Ea ltac:(lia)). exact (IH _ _ _ _ Ec).
Qed.

(** The blocks read back from their index, the temporaries of their
    phis and instructions named in order of definition. *)
Lemma read_blocks_rt : forall w r bs b n ws n' ord x dss q ql rest fuel N,
  tabs_ok w r -> blocks_words w b n bs = Some (ws, n', ord) ->
  Forall2 (fun bt ds => exists l phis insts j, block_parts bt = Some (l, phis, insts, j) /\
                                              mapo defs_of (phis ++ insts) = Some ds) bs dss ->
  temps_inv (w_temps w) N n (concat (concat dss) ++ q) ->
  locals_inv r x (flat_map block_locals bs ++ ql) -> labels_at r b bs -> (length ws <= fuel)%nat ->
  temps_inv (w_temps w) N n' q /\
  read_blocks r fuel b (length bs) n x (ws ++ rest)
    = Some (bs, n', x + Z.of_nat (length (flat_map block_locals bs)), rest) /\
  (length (concat (concat dss)) <= length ws)%nat /\ (length bs <= length ws)%nat /\
  (length (flat_map block_locals bs) <= length ws)%nat.
Proof.
  intros w r. induction bs as [|bt bs IH]; intros b n ws n' ord x dss q ql rest fuel N T H D TI LI La F;
    cbn [blocks_words] in H; inversion D as [|? ds ? dss' Dh Dt]; subst.
  - injection H as <- <- _. cbn in *. split; [exact TI|]. split; [rewrite Z.add_0_r; reflexivity | lia].
  - destruct Dh as (l & phis & insts & j & Eb & Ed).
    rewrite Eb in H. cbv beta iota in H.
    destruct (Z.eqb b 0 && negb (Nat.eqb (length phis) 0)) eqn:E0; [discriminate|].
    destruct (insts_words w 0 b n phis) as [[[ws1 n1] o1]|] eqn:E1; [|discriminate].
    destruct (insts_words w 1 b n1 insts) as [[[ws2 n2] o2]|] eqn:E2; [|discriminate].
    destruct (inst_words w 2 b n2 j) as [[[ws3 n3] o3]|] eqn:E3; [|discriminate].
    destruct (blocks_words w (b + 1) n3 bs) as [[[ws4 n4] o4]|] eqn:E4; [|discriminate].
    injection H as <- <- _.
    destruct (mapo_app _ _ _ _ Ed) as (dp & di & -> & Edp & Edi).
    pose proof (phis_locals _ _ _ _ _ _ _ E1) as Lp.
    pose proof (inst_locals_group _ _ _ _ _ _ _ _ E3 ltac:(lia)) as Lj.
    assert (Bl : block_locals bt = flat_map inst_locals insts) by (unfold block_locals; rewrite Eb; reflexivity).
    cbn [flat_map concat] in LI, TI |- *. rewrite Bl in LI |- *. rewrite !concat_app in TI.
    rewrite <- !app_assoc in TI. rewrite <- !app_assoc in LI. destruct La as [La1 La2].
    rewrite !length_app in F.
    (* the phis *)
    assert (S0 : stops 0 (ws2 ++ ws3 ++ ws4 ++ rest)).
    { unfold stops. destruct (insts_next _ _ _ _ _ _ _ _ E2) as [(_ & -> & _) | Nx].
      - destruct (inst_shape _ _ _ _ _ _ _ _ E3) as (f & e & o & _ & G & _ & _ & Nj).
        rewrite app_nil_l, Nj, G. lia.
      - destruct (Nx (ws3 ++ ws4 ++ rest)) as (c & -> & G). rewrite G. lia. }
    assert (LI0 : locals_inv r x (flat_map inst_locals phis ++ flat_map inst_locals insts
                                  ++ flat_map block_locals bs ++ ql)) by (rewrite Lp; exact LI).
    destruct (read_group_rt w r 0 b phis n ws1 n1 o1 x dp _ _ (ws2 ++ ws3 ++ ws4 ++ rest) fuel N
                T E1 Edp TI LI0 ltac:(lia) S0) as (TI1 & LI1 & R1 & A1 & A2 & A3).
    rewrite Lp in LI1, R1. cbn [length Z.of_nat] in LI1, R1. rewrite Z.add_0_r in LI1, R1.
    (* the instructions *)
    assert (S1 : stops 1 (ws3 ++ ws4 ++ rest)).
    { unfold stops. destruct (inst_shape _ _ _ _ _ _ _ _ E3) as (f & e & o & _ & G & _ & _ & Nj).
      rewrite Nj, G. lia. }
    destruct (read_group_rt w r 1 b insts n1 ws2 n2 o2 x di _ _ (ws3 ++ ws4 ++ rest) fuel N
                T E2 Edi TI1 LI1 ltac:(lia) S1) as (TI2 & LI2 & R2 & B1 & B2 & B3).
    (* the jump *)
    assert (TI2' : temps_inv (w_temps w) N n2 ([] ++ concat (concat dss') ++ q)) by exact TI2.
    assert (LI2' : locals_inv r (x + Z.of_nat (length (flat_map inst_locals insts)))
                     (inst_locals j ++ flat_map block_locals bs ++ ql)) by (rewrite Lj; exact LI2).
    destruct (read_inst_rt w r 2 b n2 j ws3 n3 o3 _ [] _ _ (ws4 ++ rest) N T E3
                (jump_defs _ _ _ _ _ _ _ E3) TI2' LI2') as (TI3 & LI3 & R3).
    rewrite Lj in LI3, R3. cbn [length Z.of_nat] in LI3, R3. rewrite Z.add_0_r in LI3, R3.
    destruct (inst_shape _ _ _ _ _ _ _ _ E3) as (fj & ej & oj & _ & _ & _ & _ & Nj).
    assert (Ne3 : (1 <= length ws3)%nat) by (destruct ws3; [specialize (Nj []); discriminate | simpl; lia]).
    destruct (IH (b + 1) n3 ws4 n4 o4 _ dss' q ql rest fuel N T E4 Dt TI3 LI3 La2 ltac:(lia))
      as (TI4 & R4 & C1 & C2 & C3).
    split; [exact TI4|]. split.
    + cbn [read_blocks length]. rewrite (La1 _ _ _ _ Eb). cbv beta iota.
      rewrite <- !app_assoc, R1. cbv beta iota. rewrite E0. cbv beta iota.
      rewrite R2. cbv beta iota. rewrite R3. cbv beta iota. rewrite R4. cbv beta iota.
      rewrite (block_parts_inv _ _ _ _ _ Eb). rewrite length_app, Nat2Z.inj_add, Z.add_assoc. reflexivity.
    + rewrite !length_app, !concat_app, !length_app. cbn [length]. split; [lia|]. split; lia.
Qed.

(** ## A function's body *)

(** [Some] is injective; unlike [injection], this leaves the terms as
    they are. *)
Lemma some_inj : forall {A} (a b : A), Some a = Some b -> a = b.
Proof. intros A a b H. congruence. Qed.

(** A function's return type reads back from its word. *)
Lemma ret_rt : forall ret rw, ret_word ret = Some rw -> read_ret rw = Some ret.
Proof.
  intros ret rw H. unfold ret_word in H. destruct (is_atom "void" ret) eqn:Ev.
  - injection H as <-. apply is_atom_inv in Ev. subst. reflexivity.
  - destruct (is_atom "data" ret) eqn:Ed.
    { injection H as <-. apply is_atom_inv in Ed. subst. reflexivity. }
    destruct (app_args "tuple" 1 ret) as [[|[| | |[|k1 [|k2 []]]] []]|] eqn:Et;
    try (pose proof (class_code_range _ _ H); unfold read_ret;
         replace (Z.eqb rw 0) with false by (symmetry; apply Z.eqb_neq; lia);
         replace (Z.eqb rw 15) with false by (symmetry; apply Z.eqb_neq; lia);
         replace (256 <=? rw) with false by (symmetry; apply Z.leb_gt; lia);
         apply codes_round_trip; exact H).
    destruct (enc_code EClass k1) as [c1|] eqn:E1; [|discriminate].
    destruct (enc_code EClass k2) as [c2|] eqn:E2; [|discriminate]. apply some_inj in H. subst rw.
    pose proof (class_code_range _ _ E1). pose proof (class_code_range _ _ E2).
    apply app_args_inv in Et as [-> _]. unfold read_ret.
    replace (Z.eqb (256 + 16 * c1 + c2) 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb (256 + 16 * c1 + c2) 15) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (256 <=? 256 + 16 * c1 + c2) with true by (symmetry; apply Z.leb_le; lia).
    replace ((256 + 16 * c1 + c2 - 256) / 16) with c1 by (apply (Z.div_unique _ _ _ c2); lia).
    replace ((256 + 16 * c1 + c2) mod 16) with c2 by (apply (Z.mod_unique _ _ (16 + c1)); lia).
    replace (c1 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (codes_round_trip _ _ _ E1), (codes_round_trip _ _ _ E2). reflexivity.
Qed.

(** The class of a parameter, as the reader checks it. *)
Definition param_class (c : Z) : option term :=
  let* k := dec_code EClass c in if class_in ["w"; "l"; "p"; "s"; "d"] k then Some k else None.

(** A function's parameters read back from their classes and their
    temporaries. *)
Lemma params_rt : forall ps pps, mapo param_parts ps = Some pps ->
  exists pks, mapo param_class (map snd pps) = Some pks /\ length pks = length pps /\
    map (fun q => TApp "param" [fst q; TApp "tmp" [snd q]]) (combine pks (map fst pps)) = ps.
Proof.
  induction ps as [|p ps IH]; intros pps H; cbn [mapo] in H.
  - injection H as <-. exists []. auto.
  - destruct (param_parts p) as [[x c]|] eqn:Ep; [|discriminate].
    destruct (mapo param_parts ps) as [pps'|] eqn:Eps; [|discriminate]. injection H as <-.
    destruct (IH pps' eq_refl) as (pks & A & B & C). unfold param_parts in Ep.
    destruct (app_args "param" 2 p) as [[|k [|d []]]|] eqn:E1; try discriminate.
    destruct (app_args "tmp" 1 d) as [[|x' []]|] eqn:E2; try discriminate.
    destruct (existsb (fun a => is_atom a k) ["w"; "l"; "p"; "s"; "d"]) eqn:E3; [|discriminate].
    destruct (enc_code EClass k) as [c'|] eqn:E4; [|discriminate]. injection Ep as <- <-.
    exists (k :: pks). cbn [map mapo fst snd]. unfold param_class at 1.
    rewrite (codes_round_trip _ _ _ E4). unfold class_in. rewrite E3. rewrite A.
    split; [reflexivity|]. split; [simpl; lia|]. cbn [combine map fst snd]. rewrite C.
    apply app_args_inv in E1 as [-> _]. apply app_args_inv in E2 as [-> _]. reflexivity.
Qed.

(** Two Forall2 chained. *)
Lemma forall2_compose : forall {X Y W} (P : X -> Y -> Prop) (Q : Y -> W -> Prop) (R : X -> W -> Prop) xs ys zs,
  Forall2 P xs ys -> Forall2 Q ys zs -> (forall x y z, P x y -> Q y z -> R x z) -> Forall2 R xs zs.
Proof.
  intros X Y W P Q R xs ys zs H1. revert zs. induction H1 as [|x y xs ys H H1 IH]; intros zs H2 HR;
    inversion H2; subst; constructor; eauto.
Qed.

(** The labels of the blocks, numbered from b. *)
Lemma labels_at_map : forall r bs bps, Forall2 (fun bt bp => block_parts bt = Some bp) bs bps ->
  forall b, (forall k l, nth_error (map (fun bp => let '(l, _, _, _) := bp in l) bps) k = Some l ->
             ZMap.find (b + Z.of_nat k) (r_labels r) = Some l) -> labels_at r b bs.
Proof.
  intros r bs bps H. induction H as [|bt bp bs bps H1 _ IH]; intros b Hl; cbn [labels_at]; [exact I|].
  split.
  - intros l phis insts j E. rewrite H1 in E. injection E as ->. rewrite <- (Z.add_0_r b).
    apply (Hl 0%nat). reflexivity.
  - apply IH. intros k l Hk. replace (b + 1 + Z.of_nat k) with (b + Z.of_nat (S k)) by lia.
    apply Hl. exact Hk.
Qed.

(** The locals the writer numbers are the blocks' locals. *)
Lemma locals_map : forall bs bps, Forall2 (fun bt bp => block_parts bt = Some bp) bs bps ->
  flat_map (fun bp => let '(_, _, insts, _) := bp in
                      flat_map (fun t => match app_args "local_alloc" 2 t with
                                         | Some [x; _] => [x]
                                         | _ => []
                                         end) insts) bps = flat_map block_locals bs.
Proof.
  intros bs bps H. induction H as [|bt [[[l phis] insts] j] bs bps H1 _ IH]; [reflexivity|].
  cbn [flat_map]. rewrite IH. unfold block_locals. rewrite H1. reflexivity.
Qed.

(** The module's tables a function is written and read with: symbols,
    strings and constants. *)
Definition mtabs_ok (w : wtab) (r : rtab) : Prop :=
  (forall x i, nm_find x (w_syms w) = Some i -> ZMap.find i (r_syms r) = Some x) /\
  (forall x i, nm_find x (w_strs w) = Some i -> ZMap.find i (r_strs r) = Some x) /\
  (forall n i, ZMap.find n (w_consts w) = Some i -> ZMap.find i (r_consts r) = Some n).

(** A function's body reads back, its names from NAMES. *)
Lemma read_body_rt : forall w r ret ps bs body ord nm name lk,
  mtabs_ok w r -> body_words w ret ps bs = Some (body, ord, nm) ->
  read_body r (Some nm) name lk body = Some (TApp "func" [name; lk; ret; TList ps; TList bs]).
Proof.
  intros w r ret ps bs body ord nm name lk [Ms [Mt Mc]] H. unfold body_words in H. cbv zeta in H.
  destruct (ret_word ret) as [rw|] eqn:Er; [|discriminate].
  destruct (mapo param_parts ps) as [pps|] eqn:Eps; [|discriminate].
  destruct (mapo block_parts bs) as [bps|] eqn:Ebps; [|discriminate].
  match type of H with context [mapo ?g bps] => destruct (mapo g bps) as [dss|] eqn:Edss end;
    [|discriminate].
  destruct (number (map fst pps) nm_empty 0 []) as [[m0 n0] firsts0] eqn:En0. cbv beta iota in H.
  destruct (Z.eqb_spec n0 (Z.of_nat (length pps))) as [Hn0|]; [|discriminate]. cbv beta iota in H.
  destruct (number (concat (concat dss)) m0 n0 []) as [[temps nt] firsts] eqn:En. cbv beta iota in H.
  match type of H with context [number ?xs nm_empty 0 []] =>
    destruct (number xs nm_empty 0 []) as [[lmap nb] lf] eqn:El end. cbv beta iota in H.
  match type of H with context [if negb (Z.eqb nb ?k) then _ else _] =>
    destruct (Z.eqb_spec nb k) as [Hnb|]; [|discriminate] end. cbv beta iota in H.
  match type of H with context [number ?xs nm_empty 0 []] =>
    destruct (number xs nm_empty 0 []) as [[xmap nl] xf] eqn:Ex end. cbv beta iota in H.
  match type of H with context [if negb (Z.eqb nl ?k) then _ else _] =>
    destruct (Z.eqb_spec nl k) as [Hnl|]; [|discriminate] end. cbv beta iota in H.
  match type of H with context [blocks_words ?w' 0 _ bs] =>
    destruct (blocks_words w' 0 (Z.of_nat (length pps)) bs) as [[[stream n'] ord']|] eqn:Eb end;
    [|discriminate].
  cbv beta iota in H. injection H as <- _ <-.
  apply mapo_forall2 in Ebps as Fbp. rewrite (locals_map bs bps Fbp) in Ex, Hnl |- *.
  set (L := map (fun bp => let '(l, _, _, _) := bp in l) bps) in *.
  set (XL := flat_map block_locals bs) in *.
  destruct (number_fresh _ _ _ _ En0) as (P0 & P0n & _ & P0f & _).
  assert (Hf0 : firsts0 = map fst pps) by (apply P0f; rewrite length_map; lia). subst firsts0.
  assert (Hm0 : forall (x : term) i, nm_find x m0 = Some i ->
                0 <= i /\ nth_error (map fst pps ++ rev []) (Z.to_nat i) = Some x)
    by (intros x i Hx; rewrite app_nil_r; auto).
  assert (Hn0' : n0 = Z.of_nat (length (map fst pps ++ rev [])))
    by (cbn [rev]; rewrite app_nil_r, length_map; lia).
  destruct (number_spec (concat (concat dss)) m0 n0 [] (map fst pps) Hm0 Hn0' temps nt firsts En)
    as (nw & HF & P1 & P1n & _ & P1l & _).
  cbn [rev app] in HF. subst nw.
  destruct (number_count _ _ _ _ El ltac:(unfold L in *; lia)) as [_ P2].
  destruct (number_count _ _ _ _ Ex Hnl) as [_ P3].
  set (w' := {| w_syms := w_syms w; w_strs := w_strs w; w_consts := w_consts w;
                w_temps := temps; w_labels := lmap; w_locals := xmap |}) in *.
  set (r' := mkRtab (r_syms r) (r_strs r) (r_consts r) (index_map (map fst pps ++ firsts))
                    (index_map L) (index_map XL)).
  assert (T' : tabs_ok w' r').
  { unfold w', r'. constructor; cbn [w_syms w_strs w_consts w_temps w_labels w_locals
                                     r_syms r_strs r_consts r_temps r_labels r_locals].
    - exact Ms.
    - exact Mt.
    - exact Mc.
    - intros x i Hx. destruct (P1 x i Hx). apply index_map_nth; auto.
    - intros x i Hx. destruct (P2 x i Hx). apply index_map_nth; auto.
    - intros x i Hx. destruct (P3 x i Hx). apply index_map_nth; auto. }
  assert (FD : Forall2 (fun bt ds => exists l phis insts j, block_parts bt = Some (l, phis, insts, j) /\
                                                           mapo defs_of (phis ++ insts) = Some ds) bs dss).
  { apply (forall2_compose _ _ _ bs bps dss Fbp (mapo_forall2 _ _ _ Edss)).
    intros bt [[[l phis] insts] j] ds E1 E2. exists l, phis, insts, j. split; [exact E1 | exact E2]. }
  assert (TI : temps_inv temps nt (Z.of_nat (length pps)) (concat (concat dss) ++ [])).
  { exists m0, []. rewrite app_nil_r, <- Hn0, En. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    intros y i Hy. destruct (P0 y i Hy) as [A B]. split; [exact A|].
    assert (B' : (Z.to_nat i < length (map fst pps))%nat) by (apply nth_error_Some; rewrite B; discriminate).
    rewrite length_map in B'. lia. }
  assert (LI : locals_inv r' 0 (XL ++ [])).
  { intros k v Hk. rewrite app_nil_r in Hk. unfold r'. cbn [r_locals].
    replace (0 + Z.of_nat k) with (Z.of_nat k) by lia. apply index_map_nth; [lia|].
    rewrite Nat2Z.id. exact Hk. }
  assert (LA : labels_at r' 0 bs).
  { apply (labels_at_map r' bs bps Fbp 0). intros k l Hk. unfold r'. cbn [r_labels].
    replace (0 + Z.of_nat k) with (Z.of_nat k) by lia. apply index_map_nth; [lia|].
    rewrite Nat2Z.id. exact Hk. }
  destruct (read_blocks_rt w' r' bs 0 (Z.of_nat (length pps)) stream n' ord' 0 dss [] [] [] (length stream) nt
              T' Eb FD TI LI LA (le_n _)) as (TIe & R & C1 & C2 & C3).
  rewrite app_nil_r in R. change (flat_map block_locals bs) with XL in C3, R.
  assert (En' : n' = nt) by (destruct TIe as (m & acc & _ & E2 & _); exact E2).
  pose proof (mapo_length _ _ _ Ebps) as Lb.
  assert (LL : length L = length bs) by (unfold L; rewrite length_map; exact Lb).
  rewrite length_app in P1n.
  destruct (params_rt ps pps Eps) as (pks & Pk & Pl & Pe).
  unfold read_body. cbv beta iota.
  rewrite (ret_rt _ _ Er). cbv beta iota.
  replace (Z.to_nat (Z.of_nat (length pps))) with (length (map snd pps)) by (rewrite length_map; lia).
  rewrite take_app. cbv beta iota. cbn [fst snd].
  replace (Z.of_nat (length pps) <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota.
  fold param_class. rewrite Pk. cbv beta iota zeta.
  assert (Hchk : ((nb <? 0) || (nt <? Z.of_nat (length pps)) || (nl <? 0)
                  || (Z.of_nat (length stream) <? nb) || (Z.of_nat (length stream) <? nt - Z.of_nat (length pps))
                  || (Z.of_nat (length stream) <? nl)) = false).
  { assert (Hnb' : nb = Z.of_nat (length bs)) by (rewrite Hnb, LL; reflexivity).
    rewrite length_map in P1n. repeat rewrite orb_false_iff. repeat split; apply Z.ltb_ge; lia. }
  rewrite Hchk. cbv beta iota. cbn [n_temps n_labels n_locals].
  rewrite length_app, Hnb, Hnl, P1n, !Z.eqb_refl. cbv beta iota zeta.
  rewrite LL, Nat2Z.id. unfold r' in R. rewrite R. cbv beta iota.
  rewrite En', P1n, Z.add_0_l, !Z.eqb_refl. cbv beta iota.
  rewrite Pl, <- (length_map fst pps), firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all, Pe.
  reflexivity.
Qed.

(** ## Data *)

(** A character's code is not negative. *)
Lemma char_code_nonneg : forall c b, char_code c = Some b -> 0 <= b.
Proof.
  intros c b H. destruct c as [|a| |]; try discriminate. destruct a as [|c1 [|c2 [|]]]; try discriminate.
  - cbn [char_code] in H. destruct (Z.of_nat (nat_of_ascii c1) <? 128); [|discriminate].
    injection H as <-. lia.
  - cbn [char_code] in H. destruct (_ && _) eqn:E; [|discriminate]. injection H as <-.
    repeat rewrite andb_true_iff in E. destruct E as (((E1 & _) & E2) & _).
    apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(** A signed 64-bit integer reads back. *)
Lemma read_i64_rt : forall n rest, i64ok n = true -> read_i64 (i64_words n ++ rest) = Some (n, rest).
Proof.
  intros n rest H. destruct (i64_words_rt n H) as (lo & hi & E & R). rewrite E. cbn. rewrite R. reflexivity.
Qed.

(** The module's tables that data items are written with invert the
    reader's: symbols and constants. *)
Definition dtabs_ok (t : mtab) (r : rtab) : Prop :=
  (forall x i, nm_find x (m_symids t) = Some i -> ZMap.find i (r_syms r) = Some x) /\
  (forall n i, ZMap.find n (m_constids t) = Some i -> ZMap.find i (r_consts r) = Some n).

(** The bytes of a string item's characters are bytes, and give the
    characters back. *)
Lemma str_bytes_rt : forall cs bs,
  mapo (fun c => let* b := char_code c in
                 if (b <? 256) && term_eqb (code_char b) c then Some b else None) cs = Some bs ->
  Forall byte bs /\ map code_char bs = cs.
Proof.
  induction cs as [|c cs IH]; intros bs E; cbn [mapo] in E.
  - injection E as <-. split; constructor.
  - destruct (char_code c) as [b|] eqn:Ec; [|discriminate]. cbv beta iota in E.
    destruct ((b <? 256) && term_eqb (code_char b) c) eqn:Eb; [|discriminate].
    destruct (mapo _ cs) as [bs'|] eqn:E2; [|discriminate]. injection E as <-.
    apply andb_true_iff in Eb as [B1 B2]. apply Z.ltb_lt in B1. apply term_eqb_eq in B2.
    destruct (IH bs' eq_refl) as [F M]. split.
    + constructor; [unfold byte; pose proof (char_code_nonneg _ _ Ec); lia | exact F].
    + cbn [map]. rewrite B2, M. reflexivity.
Qed.

(** A data item reads back from its words, which are not empty. *)
Lemma data_item_rt : forall t r x ws, dtabs_ok t r -> data_item_words t x = Some ws ->
  ws <> [] /\ forall rest, read_data_item r (ws ++ rest) = Some (x, rest).
Proof.
  intros t r x ws [Hs Hc] H. unfold data_item_words in H.
  destruct (app_args "item" 2 x) as [ts|] eqn:Ex.
  - apply app_args_inv in Ex as [-> L]. destruct ts as [|wd [|v [|]]]; try discriminate L. clear L.
    destruct (app_args "str" 1 v) as [us|] eqn:Ev.
    + apply app_args_inv in Ev as [-> L]. destruct us as [|a [|]]; try discriminate L. clear L.
      destruct a as [| | |cs]; cbn in H; try discriminate.
      destruct (is_atom "b" wd) eqn:Eb; [|discriminate].
      destruct (mapo _ cs) as [bs|] eqn:Ebs; [|discriminate]. injection H as <-.
      split; [discriminate|]. intros rest. cbn [app read_data_item].
      destruct (str_bytes_rt cs bs Ebs) as [F M].
      rewrite (read_bytes_rt bs rest F). cbv beta iota. cbn [fst snd].
      rewrite M. apply is_atom_inv in Eb. subst wd. reflexivity.
    + destruct (app_args "const" 1 v) as [us|] eqn:Ec.
      * apply app_args_inv in Ec as [-> L]. destruct us as [|a [|]]; try discriminate L. clear L.
        destruct a as [k| | |]; cbn in H; try discriminate.
        destruct (enc_code EWidth wd) as [c|] eqn:Ew; [|discriminate].
        destruct (const_word (m_constids t) k) as [z|] eqn:Ez; [|discriminate]. injection H as <-.
        split; [discriminate|]. intros rest. cbn [app read_data_item].
        rewrite (codes_round_trip _ _ _ Ew). cbv beta iota.
        assert (T : tabs_ok (mkWtab nm_empty nm_empty (m_constids t) nm_empty nm_empty nm_empty) r).
        { split; intros ? ? E; cbn [w_syms w_strs w_consts w_temps w_labels w_locals] in E;
          try exact (Hc _ _ E); rewrite nm_find_empty in E; discriminate. }
        destruct (const_rt _ r k z T Ez) as [_ C]. rewrite C. reflexivity.
      * destruct (app_args "sym" 2 v) as [us|] eqn:Es; [|discriminate].
        apply app_args_inv in Es as [-> L]. destruct us as [|s [|a [|]]]; try discriminate L. clear L.
        destruct a as [k| | |]; try discriminate.
        destruct ((is_atom "l" wd || is_atom "p" wd) && i64ok k) eqn:Eo; [|discriminate].
        destruct (enc_code EWidth wd) as [c|] eqn:Ew; [|discriminate].
        destruct (nm_find s (m_symids t)) as [sid|] eqn:Ei; [|discriminate].
        injection H as <-. split; [discriminate|]. intros rest. cbn [app read_data_item].
        apply andb_true_iff in Eo as [_ Eo].
        rewrite (codes_round_trip _ _ _ Ew). cbv beta iota. rewrite (Hs _ _ Ei). cbv beta iota.
        rewrite (read_i64_rt k rest Eo). reflexivity.
  - destruct (app_args "zero" 1 x) as [us|] eqn:Ez; [|discriminate].
    apply app_args_inv in Ez as [-> L]. destruct us as [|a [|]]; try discriminate L. clear L.
    destruct a as [k| | |]; try discriminate.
    destruct (i64ok k) eqn:Ek; [|discriminate]. injection H as <-. split; [discriminate|].
    intros rest. cbn [app read_data_item]. rewrite (read_i64_rt k rest Ek). reflexivity.
Qed.

(** ## Names *)

(** The ids [number] gives distinct terms are their places in the
    reader's [index_map]. *)
Lemma number_index : forall xs m n F, NoDup xs -> number xs nm_empty 0 [] = (m, n, F) ->
  forall x i, nm_find x m = Some i -> ZMap.find i (index_map xs) = Some x.
Proof.
  intros xs m n F Hd E x i H. destruct (number_ids _ _ _ _ Hd E) as [_ P].
  destruct (P x i H) as [P1 P2]. apply index_map_nth; assumption.
Qed.

(** The words of a list of side terms, joined. *)
Lemma side_go : forall (ids : nmap Z) ts ws,
  (fix go (ts : list term) : option (list Z) :=
     match ts with
     | [] => Some []
     | t :: ts' => let* a := side_term_words ids t in let* b := go ts' in Some (a ++ b)
     end) ts = Some ws ->
  exists wss, Forall2 (fun t w => side_term_words ids t = Some w) ts wss /\ ws = concat wss.
Proof.
  intros ids. induction ts as [|t ts IH]; intros ws H.
  - injection H as <-. exists []. split; constructor.
  - destruct (side_term_words ids t) as [a|] eqn:Ea; [|discriminate].
    match type of H with context [match ?g ts with _ => _ end] => destruct (g ts) as [b|] eqn:Eb end;
      [|discriminate].
    injection H as <-. destruct (IH b eq_refl) as (wss & F & ->). exists (a :: wss). split; [constructor; auto|reflexivity].
Qed.

(** A side term's words are not empty. *)
Lemma side_nonempty : forall (ids : nmap Z) t ws, side_term_words ids t = Some ws -> ws <> [].
Proof.
  intros ids t ws H. destruct t as [n|a|f ts|ts]; cbn [side_term_words] in H.
  - destruct (wideok n); [|discriminate]. injection H as <-. discriminate.
  - destruct (nm_find _ ids); [|discriminate]. injection H as <-. discriminate.
  - destruct (Nat.eqb _ _); [discriminate|]. destruct (nm_find _ ids); [|discriminate].
    match type of H with context [match ?g ts with _ => _ end] => destruct (g ts) end; [|discriminate].
    injection H as <-. discriminate.
  - match type of H with context [match ?g ts with _ => _ end] => destruct (g ts) end; [|discriminate].
    injection H as <-. discriminate.
Qed.

(** One joined part's length bounds each part's. *)
Lemma concat_in_length : forall (wss : list (list Z)) w, In w wss -> (length w <= length (concat wss))%nat.
Proof.
  induction wss as [|v wss IH]; intros w H; [contradiction|]. simpl. rewrite length_app.
  destruct H as [<-|H]; [lia|]. specialize (IH w H). lia.
Qed.

(** A side term reads back from its words, given enough fuel and a
    pool that inverts the ids. *)
Lemma side_term_rt : forall (ids : nmap Z) (pool : ZMap.t term) fuel t ws rest,
  (forall x i, nm_find x ids = Some i -> ZMap.find i pool = Some x) ->
  side_term_words ids t = Some ws -> (length ws <= fuel)%nat ->
  read_side_term pool fuel (ws ++ rest) = Some (t, rest).
Proof.
  intros ids pool fuel. induction fuel as [|f IH]; intros t ws rest P H L.
  { destruct ws; [destruct (side_nonempty _ _ _ H eq_refl)|simpl in L; lia]. }
  assert (Hlist : forall ts wss, Forall2 (fun t w => side_term_words ids t = Some w) ts wss ->
            (length (concat wss) < S f)%nat ->
            Forall2 (fun x ws => ws <> [] /\ forall rest, read_side_term pool f (ws ++ rest) = Some (x, rest))
              ts wss).
  { intros ts wss F Lc. induction F as [|x w ts wss Hx F IHF]; constructor.
    - split; [exact (side_nonempty _ _ _ Hx)|]. intros r'. apply IH; [exact P|exact Hx|].
      simpl in Lc. rewrite length_app in Lc. lia.
    - apply IHF. simpl in Lc. rewrite length_app in Lc. lia. }
  destruct t as [n|a|g ts|ts]; cbn [side_term_words] in H.
  - destruct (wideok n) eqn:Ew; [|discriminate]. injection H as <-.
    destruct (wide_words_rt n Ew) as (a & b & c & E & R). rewrite E. cbn. rewrite R. reflexivity.
  - destruct (nm_find (TAtom a) ids) as [i|] eqn:Ei; [|discriminate]. cbv beta iota in H. injection H as <-.
    cbn. rewrite (P _ _ Ei). reflexivity.
  - destruct (Nat.eqb_spec (length ts) 0) as [|Hl]; [discriminate|].
    destruct (nm_find (TAtom g) ids) as [i|] eqn:Ei; [|discriminate].
    match type of H with context [match ?g ts with _ => _ end] => destruct (g ts) as [w|] eqn:Eg end;
      [|discriminate].
    cbv beta iota in H. injection H as <-. destruct (side_go _ _ _ Eg) as (wss & F & ->).
    simpl app. cbn [read_side_term]. rewrite (P _ _ Ei). cbv beta iota. cbn [atom_string]. cbv beta iota.
    pose proof (Forall2_length F) as FL.
    replace (Z.of_nat (length ts) :: concat wss ++ rest) with ((Z.of_nat (length ts) :: concat wss) ++ rest)
      by reflexivity.
    rewrite read_counted_rt; [|apply Hlist; [exact F|simpl in L; lia]]. cbn [fst snd].
    destruct ts; [contradiction|reflexivity].
  - match type of H with context [match ?g ts with _ => _ end] => destruct (g ts) as [w|] eqn:Eg end;
      [|discriminate].
    injection H as <-. destruct (side_go _ _ _ Eg) as (wss & F & ->).
    simpl app. cbn [read_side_term].
    replace (Z.of_nat (length ts) :: concat wss ++ rest) with ((Z.of_nat (length ts) :: concat wss) ++ rest)
      by reflexivity.
    rewrite read_counted_rt; [reflexivity|apply Hlist; [exact F|simpl in L; lia]].
Qed.

(** A counted list of side terms reads back, given enough fuel. *)
Lemma side_list_rt : forall (ids : nmap Z) (pool : ZMap.t term) ts wss fuel rest,
  (forall x i, nm_find x ids = Some i -> ZMap.find i pool = Some x) ->
  mapo (side_term_words ids) ts = Some wss -> (length (concat wss) <= fuel)%nat ->
  read_counted (read_side_term pool fuel) (Z.of_nat (length ts) :: concat wss ++ rest) = Some (ts, rest).
Proof.
  intros ids pool ts wss fuel rest P H L. apply (read_counted_rt _ _ _ rest). apply mapo_forall2 in H.
  induction H as [|t w ts wss Ht _ IH]; constructor.
  - split; [exact (side_nonempty _ _ _ Ht)|]. intros r'. apply (side_term_rt ids); [exact P|exact Ht|].
    simpl in L. rewrite length_app in L. lia.
  - apply IH. simpl in L. rewrite length_app in L. lia.
Qed.

(** The NAMES section reads back. *)
Lemma read_names_rt : forall ns ws, names_words ns = Some ws -> read_names ws = Some ns.
Proof.
  intros ns ws H. unfold names_words in H.
  set (pool := sort_uniq str_lt String.eqb _) in H.
  destruct (number (map TAtom pool) nm_empty 0 []) as [[ids k] F] eqn:En. cbv beta iota zeta in H.
  match type of H with context [mapo ?g ns] => destruct (mapo g ns) as [recs|] eqn:Er end; [|discriminate].
  injection H as <-. unfold read_names.
  rewrite (read_strings_rt pool (concat recs)
           : read_strings (Z.of_nat (length pool) :: flat_map _ pool ++ concat recs) = _).
  cbv beta iota. cbn [fst snd].
  pose proof (number_index (map TAtom pool) _ _ _ (nodup_atoms pool (sort_strings_nodup _)) En) as P.
  clearbody pool. clear En.
  apply mapo_forall2 in Er. cbv zeta.
  enough (G : forall d fuel, (length (concat recs) <= d)%nat -> (length (concat recs) <= fuel)%nat ->
              read_name_recs (index_map (map TAtom pool)) d fuel (concat recs) = Some ns)
    by (apply G; lia).
  induction Er as [|f w ns recs Hf _ IH]; intros d fuel Ld L; [destruct fuel; reflexivity|].
  destruct (mapo (side_term_words ids) (n_temps f)) as [wa|] eqn:Ea; [|discriminate]. cbv beta iota in Hf.
  destruct (mapo (side_term_words ids) (n_labels f)) as [wb|] eqn:Eb; [|discriminate]. cbv beta iota in Hf.
  destruct (mapo (side_term_words ids) (n_locals f)) as [wc|] eqn:Ec; [|discriminate]. cbv beta iota in Hf.
  injection Hf as <-. cbn [concat] in *. repeat (rewrite length_app in L, Ld || (progress cbn [length] in L, Ld)).
  destruct fuel as [|fuel]; [lia|].
  repeat (rewrite <- app_assoc || (progress cbn [app])). cbn [read_name_recs].
  rewrite (side_list_rt ids); [|exact P|exact Ea|repeat (rewrite length_app || (progress cbn [length])); lia].
  cbv beta iota. cbn [fst snd].
  rewrite (side_list_rt ids); [|exact P|exact Eb|repeat (rewrite length_app || (progress cbn [length])); lia].
  cbv beta iota. cbn [fst snd].
  rewrite (side_list_rt ids); [|exact P|exact Ec|repeat (rewrite length_app || (progress cbn [length])); lia].
  cbv beta iota. cbn [fst snd].
  rewrite IH by lia. destruct f; reflexivity.
Qed.

(** ## Items *)

(** A symbol's kind and linkage code come back out of its word. *)
Lemma kind_word : forall k c, 0 <= k < 256 -> (k + c * 256) mod 256 = k /\ (k + c * 256) / 256 = c.
Proof.
  intros k c H. split.
  - rewrite Z.mod_add by lia. apply Z.mod_small. exact H.
  - rewrite Z.div_add by lia. rewrite Z.div_small by exact H. reflexivity.
Qed.

(** A function's linkage code reads back. *)
Lemma func_linkage_rt : forall s c, sassoc s func_linkage_codes = Some c ->
  srassoc c func_linkage_codes = Some s.
Proof.
  intros s c H. apply assoc_round_trip; [|exact H].
  split; simpl; repeat (constructor; [simpl; intuition discriminate |]); constructor.
Qed.

(** An alias's linkage code reads back. *)
Lemma alias_linkage_rt : forall s c, sassoc s alias_linkage_codes = Some c ->
  srassoc c alias_linkage_codes = Some s.
Proof.
  intros s c H. apply assoc_round_trip; [|exact H].
  split; simpl; repeat (constructor; [simpl; intuition discriminate |]); constructor.
Qed.

(** A data linkage of the table reads back from its code. *)
Lemma data_table_rt : forall lk z, tassoc lk data_linkage_codes = Some z -> read_data_linkage z 0 = Some lk.
Proof.
  intros lk z Et. unfold data_linkage_codes in Et. cbn [tassoc] in Et.
  repeat (destruct (term_eqb lk _) eqn:E;
          [apply term_eqb_eq in E; subst lk; injection Et as <-; reflexivity|clear E]).
  discriminate.
Qed.

(** A data object's linkage reads back from its code and word. *)
Lemma data_linkage_rt : forall lk c e, data_linkage_word lk = Some (c, e) -> read_data_linkage c e = Some lk.
Proof.
  intros lk c e H. unfold data_linkage_word in H.
  assert (T : (let* c := tassoc lk data_linkage_codes in Some (c, 0)) = Some (c, e) ->
              read_data_linkage c e = Some lk).
  { intros H1. destruct (tassoc lk data_linkage_codes) as [z|] eqn:Et; [|discriminate].
    injection H1 as <- <-. apply data_table_rt. exact Et. }
  destruct (app_args "init" 2 lk) as [us|] eqn:Ei; [|exact (T H)].
  pose proof Ei as Ei'. apply app_args_inv in Ei' as [Elk L].
  destruct us as [|wh [|p [|]]]; try discriminate L.
  destruct p as [p| | |]; try exact (T H).
  subst lk. destruct (u32ok p); [|discriminate].
  destruct (is_atom "ctor" wh) eqn:Ec; [injection H as <- <-; apply is_atom_inv in Ec; subst; reflexivity|].
  destruct (is_atom "dtor" wh) eqn:Ed; [injection H as <- <-; apply is_atom_inv in Ed; subst; reflexivity|].
  discriminate.
Qed.

(** The function names a part of NAMES adds before the rest. *)
Definition ncons (a : list fnames) (o : option (list fnames)) : option (list fnames) :=
  match o with Some l => Some (a ++ l) | None => None end.

(** A function, data object or alias reads back from its symbol's
    words, its DATA words and its FUNCTIONS words, before the items
    after it. *)
Lemma item_rt : forall t r it n k sw dw fw o nmx,
  mtabs_ok (mkWtab (m_symids t) (m_strids t) (m_constids t) nm_empty nm_empty nm_empty) r ->
  item_symbol it = Some (n, k) -> symbol_words t (n, k, Some it) = Some sw ->
  data_words t it = Some dw -> func_words t it = Some (fw, o, nmx) ->
  exists sid kw extra, sw = [sid; kw; extra] /\ nm_find n (m_strids t) = Some sid /\
  forall syms dws fws nms rest, (nms = None -> nmx = []) -> read_items r syms dws fws nms = Some rest ->
    read_items r ((n, kw, extra) :: syms) (dw ++ dws) (fw ++ fws) (ncons nmx nms) = Some (it :: rest).
Proof.
  intros t r it n k sw dw fw o nmx M Hi Hs Hd Hf.
  assert (D : dtabs_ok t r) by (destruct M as (M1 & _ & M3); split; [exact M1|exact M3]).
  destruct it as [| | f args |]; try discriminate. destruct args as [|n' args]; try discriminate.
  cbn [item_symbol] in Hi. unfold symbol_words in Hs.
  destruct (nm_find n (m_strids t)) as [sid|] eqn:Esid; [|discriminate]. cbv beta iota in Hs.
  destruct (String.eqb_spec f "func") as [->|Nf]; [|destruct (String.eqb_spec f "data") as [->|Nd];
    [|destruct (String.eqb_spec f "alias") as [->|Na]; [|discriminate]]];
    injection Hi as <- <-.
  - (* a function *)
    destruct args as [|lk [|ret [|ps [|bs [|]]]]]; cbn -[sassoc func_linkage_codes] in Hs; try discriminate.
    destruct lk as [|s| |]; try discriminate. cbn [atom_string] in Hs.
    destruct (sassoc s func_linkage_codes) as [c|] eqn:Ec; [|discriminate]. injection Hs as <-.
    unfold func_words in Hf. cbn -[body_words] in Hf.
    destruct ps as [| | |ps]; cbv beta iota in Hf; try discriminate.
    destruct bs as [| | |bs]; cbv beta iota in Hf; try discriminate.
    match type of Hf with context [body_words ?w ret ps bs] =>
      destruct (body_words w ret ps bs) as [[[body ord] nm]|] eqn:Eb end; [|discriminate].
    injection Hf as <- <- <-. unfold data_words in Hd. cbn in Hd. injection Hd as <-.
    exists sid, (0 + c * 256), 0. split; [reflexivity|]. split; [reflexivity|].
    intros syms dws fws nms rest Hn R. destruct nms as [l|]; [|specialize (Hn eq_refl); discriminate].
    cbn [read_items]. destruct (kind_word 0 c ltac:(lia)) as [K1 K2]. rewrite K1, K2.
    cbn [Z.eqb]. rewrite (func_linkage_rt _ _ Ec). cbv beta iota. cbn [negb app ncons].
    rewrite take_app_z. cbv beta iota. cbn [fst snd].
    rewrite (read_body_rt _ _ _ _ _ _ _ _ _ _ M Eb). cbv beta iota. rewrite R. reflexivity.
  - (* a data object *)
    destruct args as [|lk [|al [|its [|]]]]; cbn -[data_linkage_word] in Hs; try discriminate.
    destruct (data_linkage_word lk) as [[c e]|] eqn:El; [|discriminate]. cbn [fst snd] in Hs.
    injection Hs as <-. unfold func_words in Hf. cbn in Hf. injection Hf as <- <- <-.
    unfold data_words in Hd. cbn -[data_item_words mapo u32ok] in Hd.
    destruct al as [al| | |]; cbv beta iota in Hd; try discriminate.
    destruct its as [| | |its]; cbv beta iota in Hd; try discriminate.
    destruct (u32ok al); [|discriminate].
    destruct (mapo (data_item_words t) its) as [wss|] eqn:Ew; [|discriminate]. injection Hd as <-.
    exists sid, (1 + c * 256), e. split; [reflexivity|]. split; [reflexivity|].
    intros syms dws fws nms rest _ R.
    apply mapo_forall2 in Ew.
    assert (F : Forall2 (fun x w => w <> [] /\ forall rest, read_data_item r (w ++ rest) = Some (x, rest)) its wss).
    { induction Ew as [|x w xs ws Hx _ IH]; constructor; [exact (data_item_rt _ _ _ _ D Hx)|exact IH]. }
    cbn [read_items]. destruct (kind_word 1 c ltac:(lia)) as [K1 K2]. rewrite K1, K2.
    cbn [Z.eqb]. rewrite (data_linkage_rt _ _ _ El). cbv beta iota. cbn [app].
    assert (L : (length its <= length (concat wss ++ dws))%nat).
    { rewrite length_app. pose proof (concat_length_ge its wss) as G.
      assert (Forall2 (fun _ ws => ws <> []) its wss) by (eapply Forall2_impl; [|exact F]; intros ? ? []; auto).
      specialize (G H). lia. }
    rewrite at_least_spec.
    destruct (Z.ltb_spec (Z.of_nat (length (concat wss ++ dws))) (Z.of_nat (length its))); [lia|].
    rewrite Nat2Z.id.
    rewrite (read_n_rt _ its wss dws) by (eapply Forall2_impl; [|exact F]; intros ? ? []; auto).
    cbv beta iota. cbn [fst snd]. replace (ncons [] nms) with nms by (destruct nms; reflexivity).
    rewrite R. reflexivity.
  - (* an alias *)
    destruct args as [|lk [|tg [|]]]; cbn -[sassoc alias_linkage_codes] in Hs; try discriminate.
    destruct lk as [|s| |]; cbn [atom_string] in Hs; try discriminate.
    destruct (sassoc s alias_linkage_codes) as [c|] eqn:Ec; [|discriminate]. cbv beta iota in Hs.
    destruct (nm_find tg (m_symids t)) as [tid|] eqn:Et; [|discriminate]. injection Hs as <-.
    unfold func_words in Hf. cbn in Hf. injection Hf as <- <- <-.
    unfold data_words in Hd. cbn in Hd. injection Hd as <-.
    exists sid, (2 + c * 256), tid. split; [reflexivity|]. split; [reflexivity|].
    intros syms dws fws nms rest _ R.
    cbn [read_items]. destruct (kind_word 2 c ltac:(lia)) as [K1 K2]. rewrite K1, K2.
    cbn [Z.eqb]. rewrite (alias_linkage_rt _ _ Ec). cbv beta iota.
    destruct M as (M1 & _). rewrite (M1 _ _ Et). cbv beta iota. cbn [app].
    replace (ncons [] nms) with nms by (destruct nms; reflexivity). rewrite R. reflexivity.
Qed.


(** The reader's view of a symbol: its words hold the string id of its
    name, then its kind word and extra word. *)
Definition sym_read (r : rtab) (w : list Z) (y : term * Z * Z) : Prop :=
  exists sid, w = [sid; snd (fst y); snd y] /\ ZMap.find sid (r_strs r) = Some (fst (fst y)).

(** The items read back from their symbols, DATA words and FUNCTIONS
    words, before the items after them. *)
Lemma items_rt : forall t r items defined sd datas fs,
  mtabs_ok (mkWtab (m_symids t) (m_strids t) (m_constids t) nm_empty nm_empty nm_empty) r ->
  mapo (fun it => let* p := item_symbol it in Some (fst p, snd p, Some it)) items = Some defined ->
  mapo (symbol_words t) defined = Some sd ->
  mapo (data_words t) items = Some datas ->
  mapo (func_words t) items = Some fs ->
  exists ys, Forall2 (sym_read r) sd ys /\
  map (fun y => let '(n, _, _) := y in n) ys = map (fun d => let '(n, _, _) := d in n) defined /\
  forall syms dws fws nms rest,
    (nms = None -> concat (map (fun x => let '(_, _, n) := x in n) fs) = []) ->
    read_items r syms dws fws nms = Some rest ->
    read_items r (ys ++ syms) (concat datas ++ dws)
      (concat (map (fun x => let '(ws, _, _) := x in ws) fs) ++ fws)
      (ncons (concat (map (fun x => let '(_, _, n) := x in n) fs)) nms) = Some (items ++ rest).
Proof.
  intros t r items. induction items as [|it items IH]; intros defined sd datas fs M Hdef Hsd Hd Hf.
  - cbn [mapo] in *. injection Hdef as <-. cbn [mapo] in Hsd. injection Hsd as <-.
    injection Hd as <-. injection Hf as <-. exists []. split; [constructor|]. split; [reflexivity|].
    intros syms dws fws nms rest _ R. cbn. destruct nms; exact R.
  - cbn [mapo] in Hdef, Hd, Hf.
    destruct (item_symbol it) as [[n k]|] eqn:Ei; [|discriminate]. cbv beta iota in Hdef. cbn [fst snd] in Hdef.
    destruct (mapo _ items) as [defs|] eqn:Edefs; [|discriminate]. injection Hdef as <-.
    cbn [mapo] in Hsd. destruct (symbol_words t (n, k, Some it)) as [sw|] eqn:Es; [|discriminate].
    destruct (mapo (symbol_words t) defs) as [sds|] eqn:Esds; [|discriminate]. injection Hsd as <-.
    destruct (data_words t it) as [dw|] eqn:Edw; [|discriminate].
    destruct (mapo (data_words t) items) as [dws'|] eqn:Edws; [|discriminate]. injection Hd as <-.
    destruct (func_words t it) as [[[fw o] nmx]|] eqn:Efw; [|discriminate].
    destruct (mapo (func_words t) items) as [fs'|] eqn:Efs; [|discriminate]. injection Hf as <-.
    destruct (item_rt t r it n k sw dw fw o nmx M Ei Es Edw Efw) as (sid & kw & extra & -> & Hsid & Hit).
    destruct (IH defs sds dws' fs' M eq_refl Esds eq_refl eq_refl) as (ys & F & Nm & Hrest).
    exists ((n, kw, extra) :: ys). split; [|split; [cbn [map]; rewrite Nm; reflexivity|]].
    + constructor; [|exact F]. exists sid. split; [reflexivity|].
      destruct M as (_ & M2 & _). exact (M2 _ _ Hsid).
    + intros syms dws fws nms rest Hn R. cbn [map concat app]. rewrite <- !app_assoc.
      replace (ncons (nmx ++ concat (map (fun x => let '(_, _, n) := x in n) fs')) nms)
        with (ncons nmx (ncons (concat (map (fun x => let '(_, _, n) := x in n) fs')) nms))
        by (destruct nms; cbn; [rewrite app_assoc|]; reflexivity).
      apply Hit.
      * intros E. destruct nms; [discriminate|]. specialize (Hn eq_refl). cbn in Hn.
        apply app_eq_nil in Hn as [Hn _]. exact Hn.
      * apply Hrest; [|exact R]. intros E. specialize (Hn E). cbn in Hn.
        apply app_eq_nil in Hn as [_ Hn]. exact Hn.
Qed.

(** The symbols a module names without defining read back, and the
    reader skips them. *)
Lemma named_rt : forall t r named sn,
  mtabs_ok (mkWtab (m_symids t) (m_strids t) (m_constids t) nm_empty nm_empty nm_empty) r ->
  mapo (symbol_words t) (map (fun s => (TAtom s, 3, @None term)) named) = Some sn ->
  exists ys, Forall2 (sym_read r) sn ys /\
  map (fun y => let '(n, _, _) := y in n) ys
    = map (fun d => let '(n, _, _) := d in n) (map (fun s => (TAtom s, 3, @None term)) named) /\
  forall dws fws nms, read_items r ys dws fws nms = read_items r [] dws fws nms.
Proof.
  intros t r named. induction named as [|s named IH]; intros sn M H.
  - injection H as <-. exists []. split; [constructor|]. split; reflexivity.
  - cbn [map mapo] in H. destruct (symbol_words t (TAtom s, 3, None)) as [w|] eqn:Ew; [|discriminate].
    destruct (mapo (symbol_words t) (map _ named)) as [ws|] eqn:Ews; [|discriminate]. injection H as <-.
    destruct (IH ws M eq_refl) as (ys & F & Nm & R).
    unfold symbol_words in Ew. destruct (nm_find (TAtom s) (m_strids t)) as [sid|] eqn:Es; [|discriminate].
    cbv beta iota in Ew. injection Ew as <-.
    exists ((TAtom s, 3, 0) :: ys). split; [|split; [cbn [map]; rewrite Nm; reflexivity|]].
    + constructor; [|exact F]. exists sid. split; [reflexivity|].
      destruct M as (_ & M2 & _). exact (M2 _ _ Es).
    + intros dws fws nms. rewrite <- R. reflexivity.
Qed.


(** A name [first_ids] numbers is at its place in the names, or was
    already in the map it started from. *)
Lemma first_ids_at : forall ns i (m : nmap Z) x j, nm_find x (first_ids ns i m) = Some j ->
  nm_find x m = Some j \/ (i <= j /\ nth_error ns (Z.to_nat (j - i)) = Some x).
Proof.
  induction ns as [|y ys IH]; intros i m x j H; cbn [first_ids] in H; [left; exact H|].
  destruct (IH _ _ _ _ H) as [H1|[H1 H2]].
  - destruct (nm_mem y m); [left; exact H1|].
    rewrite nm_find_add in H1. destruct (name_eqb x y) eqn:E; [|left; exact H1].
    injection H1 as <-. apply term_eqb_eq in E. subst. right. split; [lia|].
    rewrite Z.sub_diag. reflexivity.
  - right. split; [lia|]. replace (Z.to_nat (j - i)) with (S (Z.to_nat (j - (i + 1)))) by lia.
    exact H2.
Qed.

(** The reader's tables of a module invert the writer's: symbols,
    strings and constants. *)
Lemma tables_rt : forall items t, module_tables items = Some t ->
  (exists defined named,
     mapo (fun it => let* p := item_symbol it in Some (fst p, snd p, Some it)) items = Some defined /\
     m_syms t = defined ++ map (fun s => (TAtom s, 3, None)) named) /\
  forallb wideok (m_consts t) = true /\
  mtabs_ok (mkWtab (m_symids t) (m_strids t) (m_constids t) nm_empty nm_empty nm_empty)
    (mkRtab (index_map (map (fun d => let '(n, _, _) := d in n) (m_syms t))) (index_map (map TAtom (m_strs t)))
       (index_map (m_consts t)) (ZMap.empty term) (ZMap.empty term) (ZMap.empty term)).
Proof.
  intros items t H. unfold module_tables in H.
  match type of H with context [mapo ?g items] => destruct (mapo g items) as [defined|] eqn:Ed end;
    [|discriminate]. cbv beta iota in H.
  destruct (mapo item_parts items) as [pss|] eqn:Ep; [|discriminate]. cbv beta iota zeta in H.
  match type of H with context [mapo ?g ?l] => destruct (mapo g l) as [defnames|] eqn:Edn end;
    [|discriminate]. cbv beta iota in H.
  match type of H with context [mapo atom_string ?l] => destruct (mapo atom_string l) as [named|] eqn:En end;
    [|discriminate]. cbv beta iota in H.
  match type of H with context [mapo atom_string ?l] => destruct (mapo atom_string l) as [files|] eqn:Ef end;
    [|discriminate]. cbv beta iota in H.
  match type of H with context [number (map TAtom ?xs) nm_empty 0 []] =>
    destruct (number (map TAtom xs) nm_empty 0 []) as [[strids k2] F2] eqn:E2 end. cbv beta iota in H.
  match type of H with context [forallb wideok ?cs] => destruct (forallb wideok cs) eqn:Ew end;
    [|discriminate]. cbv beta iota in H.
  injection H as <-. cbn [m_syms m_consts m_strs m_symids m_strids m_constids].
  split; [eauto|]. split; [exact Ew|].
  split; [|split].
  - cbn [w_syms r_syms]. intros x i Hx. apply first_ids_at in Hx as [Hx|[H1 H2]].
    + rewrite nm_find_empty in Hx. discriminate.
    + apply index_map_nth; [lia|]. rewrite Z.sub_0_r in H2. exact H2.
  - cbn [w_strs r_strs]. intros x i Hx.
    exact (number_index _ _ _ _ (nodup_atoms _ (sort_strings_nodup _)) E2 x i Hx).
  - cbn [w_consts r_consts]. intros c i Hc. apply cmap_find in Hc as [Hc|[H1 H2]].
    + rewrite zfind_empty in Hc. discriminate.
    + apply index_map_nth; [lia|]. rewrite Z.sub_0_r in H2. exact H2.
Qed.

(** ## The module *)

(** The SYMBOLS words read back as the reader's symbols. *)
Lemma syms_read_rt : forall r sws ys rest, Forall2 (sym_read r) sws ys ->
  exists trips,
  read_counted (fun ws => match ws with a :: b :: c :: ws' => Some ((a, b, c), ws') | _ => None end)
    ((Z.of_nat (length sws) :: concat sws) ++ rest) = Some (trips, rest) /\
  mapo (fun y => let '(sid, kw, extra) := y in let* n := ZMap.find sid (r_strs r) in Some (n, kw, extra))
    trips = Some ys.
Proof.
  intros r sws ys rest F.
  exists (map (fun w => match w with [a; b; c] => (a, b, c) | _ => (0, 0, 0) end) sws). split.
  - rewrite <- (length_map (fun w => match w with [a; b; c] => (a, b, c) | _ => (0, 0, 0) end) sws).
    apply read_counted_rt.
    induction F as [|w y sws ys (sid & -> & _) _ IH]; constructor; [|exact IH].
    split; [discriminate|]. intros rest'. reflexivity.
  - induction F as [|w [[n kw] extra] sws ys (sid & -> & Hs) _ IH]; [reflexivity|].
    cbn [map mapo fst snd] in *. rewrite Hs. cbv beta iota. rewrite IH. reflexivity.
Qed.

(** A section's payload, or the words of an empty table when the
    section is absent because the table is empty. *)
Lemma or_empty_eq : forall (c : bool) (a d : list Z), (c = true -> a = d) ->
  match (if c then None else Some a) with Some x => x | None => d end = a.
Proof. intros [|] a d H; [symmetry; apply H|]; reflexivity. Qed.

(** The words [encode_term] writes read back as the module, with NAMES
    exactly when the module has functions; they are also what
    [encode_term] writes without NAMES in that case, and [module_words]
    keeps them all. *)
Theorem read_encode_term : forall t ws,
  encode_term true t = Some ws ->
  exists b, read_term ws = Some (t, b) /\ encode_term b t = Some ws /\ module_words ws = Some ws.
Proof.
  intros m ws H. pose proof H as H0. unfold encode_term in H.
  destruct (app_args "module" 1 m) as [xs|] eqn:Em; [|discriminate]. cbv beta iota in H.
  apply app_args_inv in Em as [-> _].
  destruct xs as [|x [|]]; try discriminate. destruct x as [| | |items]; try discriminate.
  destruct (module_tables items) as [t|] eqn:Et; [|discriminate]. cbv beta iota in H.
  destruct (mapo (symbol_words t) (m_syms t)) as [syms|] eqn:Es; [|discriminate]. cbv beta iota in H.
  destruct (mapo (data_words t) items) as [datas|] eqn:Ed; [|discriminate]. cbv beta iota in H.
  destruct (mapo (func_words t) items) as [fs|] eqn:Ef; [|discriminate]. cbv beta iota zeta in H.
  destruct (tables_rt items t Et) as ((defined & named & Edef & Hsyms) & Wk & Mt).
  set (R0 := mkRtab _ _ _ _ _ _) in Mt.
  pose proof Es as Es'. rewrite Hsyms in Es'. apply mapo_app in Es' as (sd & sn & Esyms & Esd & Esn).
  destruct (items_rt t R0 items defined sd datas fs Mt Edef Esd Ed Ef) as (yd & Fd & Nd & Hitems).
  destruct (named_rt t R0 _ sn Mt Esn) as (yn & Fn & Nn & Hn).
  destruct (syms_read_rt R0 (sd ++ sn) (yd ++ yn) [] (Forall2_app Fd Fn)) as (trips & Rc & Rm).
  cbn [r_strs R0] in Rm.
  set (FWS := concat (map (fun x => let '(ws, _, _) := x in ws) fs)) in *.
  set (FN := concat (map (fun x => let '(_, _, n) := x in n) fs)) in *.
  set (fl := (if module_checked items then 1 else 0) + (if module_filc items then 2 else 0)
             + (if forallb (fun x => let '(_, o, _) := x in o) fs then 4 else 0)) in *.
  assert (Hfl : (0 <=? fl) = true /\ (fl <? 8) = true).
  { unfold fl. destruct (module_checked items), (module_filc items), (forallb _ fs); split; reflexivity. }
  assert (Main : forall (b : bool) nw, (if b then names_words FN = Some nw else FN = []) ->
            ws = [magic; version; fl; Z.of_nat (length (msecs
                   (length (m_strs t) =? 0)%nat (length (m_consts t) =? 0)%nat (length (m_syms t) =? 0)%nat
                   (length (concat datas) =? 0)%nat (length FWS =? 0)%nat b
                   (strings_words (m_strs t)) (Z.of_nat (length (m_consts t)) :: flat_map wide_words (m_consts t))
                   (Z.of_nat (length (m_syms t)) :: concat syms) (concat datas) FWS nw))]
                 ++ sections_words (msecs
                   (length (m_strs t) =? 0)%nat (length (m_consts t) =? 0)%nat (length (m_syms t) =? 0)%nat
                   (length (concat datas) =? 0)%nat (length FWS =? 0)%nat b
                   (strings_words (m_strs t)) (Z.of_nat (length (m_consts t)) :: flat_map wide_words (m_consts t))
                   (Z.of_nat (length (m_syms t)) :: concat syms) (concat datas) FWS nw) ->
            read_term ws = Some (TApp "module" [TList items], b) /\ module_words ws = Some ws).
  { intros b nw Hb Hws. subst ws.
    pose proof (msecs_spec (length (m_strs t) =? 0)%nat (length (m_consts t) =? 0)%nat (length (m_syms t) =? 0)%nat
                   (length (concat datas) =? 0)%nat (length FWS =? 0)%nat b
                   (strings_words (m_strs t)) (Z.of_nat (length (m_consts t)) :: flat_map wide_words (m_consts t))
                   (Z.of_nat (length (m_syms t)) :: concat syms) (concat datas) FWS nw) as MS.
    cbv zeta in MS. set (ss := msecs _ _ _ _ _ _ _ _ _ _ _ _) in *.
    destruct MS as (Sid & Sf & S1 & S2 & S3 & S4 & S5 & S6).
    split.
    - unfold read_term. cbn [app]. rewrite !Z.eqb_refl. destruct Hfl as [F1 F2]. rewrite F1, F2.
      cbn [andb negb]. rewrite read_sections_rt by lia. cbv beta iota. rewrite Z.eqb_refl, Sid.
      cbn [andb negb]. rewrite S1, S2, S3, S4, S5, S6.
      rewrite (or_empty_eq _ (strings_words (m_strs t)) [0])
        by (intros E; apply Nat.eqb_eq, length_zero_iff_nil in E; rewrite E; reflexivity).
      rewrite <- (app_nil_r (strings_words (m_strs t))), read_strings_rt. cbv beta iota.
      rewrite (or_empty_eq _ (Z.of_nat (length (m_consts t)) :: flat_map wide_words (m_consts t)) [0])
        by (intros E; apply Nat.eqb_eq, length_zero_iff_nil in E; rewrite E; reflexivity).
      rewrite <- (app_nil_r (Z.of_nat (length (m_consts t)) :: flat_map wide_words (m_consts t))).
      rewrite (read_wides_rt _ _ Wk). cbv beta iota.
      rewrite (or_empty_eq _ (Z.of_nat (length (m_syms t)) :: concat syms) [0])
        by (intros E; apply Nat.eqb_eq, length_zero_iff_nil in E; rewrite E in Es; injection Es as <-;
            rewrite E; reflexivity).
      rewrite <- (mapo_length _ _ _ Es), Esyms.
      rewrite <- (app_nil_r (Z.of_nat (length (sd ++ sn)) :: concat (sd ++ sn))), Rc.
      cbv beta iota. cbn [fst snd]. rewrite Rm. cbv beta iota.
      rewrite map_app, Nd, Nn, <- map_app, <- Hsyms.
      rewrite (or_empty_eq _ (concat datas) []) by (intros E; apply Nat.eqb_eq, length_zero_iff_nil in E; exact E).
      rewrite (or_empty_eq _ FWS []) by (intros E; apply Nat.eqb_eq, length_zero_iff_nil in E; exact E).
      destruct b.
      + rewrite (read_names_rt _ _ Hb). cbv beta iota.
        pose proof (Hitems yn [] [] (Some []) [] ltac:(discriminate) ltac:(rewrite Hn; reflexivity)) as RI.
        cbn [ncons] in RI. rewrite !app_nil_r in RI. unfold R0 in RI. rewrite RI. reflexivity.
      + cbv beta iota.
        pose proof (Hitems yn [] [] None [] ltac:(intros _; exact Hb) ltac:(rewrite Hn; reflexivity)) as RI.
        cbn [ncons] in RI. rewrite !app_nil_r in RI. unfold R0 in RI. rewrite RI. reflexivity.
    - unfold module_words. cbn [app]. rewrite read_sections_rt by lia. cbv beta iota. rewrite Sf. reflexivity. }
  destruct (Nat.eqb_spec (length FN) 0) as [Hz|Hz].
  - replace ((length FN =? 0)%nat) with true in H by (symmetry; apply Nat.eqb_eq; exact Hz).
    cbn [andb negb] in H. cbv beta iota in H. injection H as Hws.
    exists false. destruct (Main false [] ltac:(apply length_zero_iff_nil; exact Hz) (eq_sym Hws)) as [R W].
    split; [exact R|]. split; [|exact W].
    unfold encode_term. cbn [app_args String.eqb Ascii.eqb Bool.eqb andb length Nat.eqb]. cbv beta iota.
    rewrite Et. cbv beta iota. rewrite Es. cbv beta iota. rewrite Ed. cbv beta iota. rewrite Ef.
    cbv beta iota zeta. cbn [andb]. cbv beta iota. rewrite <- Hws. reflexivity.
  - replace ((length FN =? 0)%nat) with false in H by (symmetry; apply Nat.eqb_neq; exact Hz).
    cbn [andb negb] in H. destruct (names_words FN) as [nw|] eqn:Enw; [|discriminate]. cbv beta iota in H.
    injection H as Hws. exists true. destruct (Main true nw eq_refl ltac:(rewrite <- Hws; reflexivity)) as [R W]. auto.
Qed.

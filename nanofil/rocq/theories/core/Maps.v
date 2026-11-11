(** Finite maps keyed by names, the model's counterpart of
    library(assoc), which ir.pl and cfg.pl use for every table indexed
    by a [[block]] label or a [[temporary]].

    The association lists of Term.v ([lookup], [put]) take time
    linear in their length, and a function of a thousand blocks and
    twenty thousand temporaries asks them millions of questions. A
    [[name-map|name map]] hashes each name to an integer and keeps,
    under each hash, an association list of the names that share it.
    A lookup compares names with [name_eqb] within its bucket, so two
    names with one hash stay apart: the hash decides only speed, never
    an answer.

    The buckets are kept in the stdlib's AVL tree keyed by integers,
    whose [[extraction|extracted]] lookups compare integers. A tree
    keyed by positives (FMapPositive) walks its key bit by bit, and
    each bit is a division of a zarith integer once extracted: the
    [[validator]] was thirty times slower with it. *)


From Stdlib Require Import String ZArith List Ascii OrderedTypeEx FMapAVL FMapFacts.
From Nanofil Require Import Term.
Import ListNotations.
Local Open Scope Z_scope.

(** The stdlib's AVL trees keyed by integers, which hold the buckets. *)
Module ZMap := FMapAVL.Make Z_as_OT.

(** ## Hashing *)

(** The bound of every hash: hashes are the integers below 2^20. *)
Definition hash_bound : Z := 2 ^ 20.

(** One step of a hash: the hash h so far times 31, plus the next
    number x, modulo [hash_bound]. *)
Definition hash_step (h x : Z) : Z := (h * 31 + x) mod hash_bound.

(** The hash of the string s, its character codes folded into the
    hash h by [hash_step]. *)
Fixpoint string_hash (s : string) (h : Z) : Z :=
  match s with
  | EmptyString => h
  | String c s' => string_hash s' (hash_step h (Z.of_N (N_of_ascii c)))
  end.

(** A hash of the ground term t, from its form (each of the four starts
    from its own seed) and its parts. *)
Fixpoint term_hash (t : term) : Z :=
  let fix list_hash (ts : list term) (h : Z) : Z :=
    match ts with
    | [] => h
    | t :: ts' => list_hash ts' (hash_step h (term_hash t))
    end in
  match t with
  | TInt n => hash_step 1 (n mod hash_bound)
  | TAtom a => string_hash a 2
  | TApp f args => list_hash args (string_hash f 3)
  | TList ts => list_hash ts 4
  end.

(** The key of the bucket a name n sits in: its [term_hash]. *)
Definition name_key (n : name) : Z := term_hash n.

(** ## Name maps *)

(** A [[name-map|name map]] from names to values of A: under each hash,
    the association list of the names with that hash and their
    values. *)
Definition nmap (A : Type) : Type := ZMap.t (list (name * A)).

(** The map with no names, `empty_assoc/1`. *)
Definition nm_empty {A : Type} : nmap A := ZMap.empty _.

(** As `get_assoc(Key, Assoc, V)`: the value of the name n in the map
    m, found in n's bucket by [lookup], which compares names, not
    hashes. *)
Definition nm_find {A : Type} (n : name) (m : nmap A) : option A :=
  match ZMap.find (name_key n) m with
  | Some bucket => lookup n bucket
  | None => None
  end.

(** As `put_assoc(Key, Assoc0, V, Assoc)`: the map m with the name n
    now mapped to v. *)
Definition nm_add {A : Type} (n : name) (v : A) (m : nmap A) : nmap A :=
  let k := name_key n in
  let bucket := match ZMap.find k m with Some b => b | None => [] end in
  ZMap.add k (put n v bucket) m.

(** As `del_assoc(Key, Assoc0, V, Assoc)`: the map m in which the name
    n no longer has a value. *)
Definition nm_remove {A : Type} (n : name) (m : nmap A) : nmap A :=
  let k := name_key n in
  match ZMap.find k m with
  | Some bucket => ZMap.add k (filter (fun p => negb (name_eqb n (fst p))) bucket) m
  | None => m
  end.

(** Whether the name n has a value in the map m. *)
Definition nm_mem {A : Type} (n : name) (m : nmap A) : bool :=
  match nm_find n m with Some _ => true | None => false end.

(** As `list_to_assoc(Pairs, Assoc)`: the map of the pairs ps, for
    pairs whose keys differ (here a later pair would replace an earlier
    one; list_to_assoc/2 throws). *)
Definition nm_of_list {A : Type} (ps : list (name * A)) : nmap A :=
  fold_left (fun m p => nm_add (fst p) (snd p) m) ps nm_empty.

(** ## What a lookup answers

    The lemmas below say what each operation does to a lookup, by name
    and not by hash: a map answers as the association list of its
    puts would. *)

(** The stdlib's facts about [ZMap]'s lookups, for the proofs below. *)
Module ZF := FMapFacts.WFacts_fun Z_as_OT ZMap.

(** Names a and b that [name_eqb] calls equal have the same
    [name_key], so they share a bucket. *)
Lemma name_key_eqb : forall a b, name_eqb a b = true -> name_key a = name_key b.
Proof. intros a b H. apply term_eqb_eq in H. subst. reflexivity. Qed.

(** Looking up the name k after [put] n v answers v if k is n, and
    otherwise what the association list ps answered before. *)
Lemma lookup_put_name : forall (A : Type) k n (v : A) ps,
  lookup k (put n v ps) = if name_eqb k n then Some v else lookup k ps.
Proof.
  intros A k n v ps. simpl. destruct (name_eqb k n) eqn:E; [reflexivity|].
  induction ps as [|[k' v'] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb n k') eqn:E'; simpl.
  - apply term_eqb_eq in E'. subst k'. rewrite E. exact IH.
  - destruct (name_eqb k k'); [reflexivity | exact IH].
Qed.

(** The empty map has no value for any name k. *)
Lemma nm_find_empty : forall (A : Type) k, nm_find k (@nm_empty A) = None.
Proof. intros A k. unfold nm_find, nm_empty. rewrite ZF.empty_o. reflexivity. Qed.

(** After [nm_add] n v, the map answers v for the name n and what it
    answered before for every other name k: a shared hash never
    shows. *)
Lemma nm_find_add : forall (A : Type) k n (v : A) m,
  nm_find k (nm_add n v m) = if name_eqb k n then Some v else nm_find k m.
Proof.
  intros A k n v m. unfold nm_find, nm_add.
  destruct (Z.eq_dec (name_key n) (name_key k)) as [E | E].
  - rewrite ZF.add_eq_o by exact E. rewrite lookup_put_name.
    destruct (name_eqb k n) eqn:Ek; [reflexivity|].
    rewrite <- E. destruct (ZMap.find (name_key n) m); reflexivity.
  - rewrite ZF.add_neq_o by exact E. destruct (name_eqb k n) eqn:Ek; [|reflexivity].
    exfalso. apply E. symmetry. apply name_key_eqb. exact Ek.
Qed.

(** After [nm_remove] n, the map has no value for the name n and its
    old value for every other name k. *)
Lemma nm_find_remove : forall (A : Type) k n (m : nmap A),
  nm_find k (nm_remove n m) = if name_eqb k n then None else nm_find k m.
Proof.
  intros A k n m. unfold nm_find, nm_remove.
  destruct (ZMap.find (name_key n) m) as [bucket|] eqn:Eb.
  - destruct (Z.eq_dec (name_key n) (name_key k)) as [E | E].
    + rewrite ZF.add_eq_o by exact E. rewrite <- E, Eb.
      destruct (name_eqb k n) eqn:Ek.
      * apply term_eqb_eq in Ek. subst k. clear Eb E. induction bucket as [|[k' v'] b IH]; simpl; [reflexivity|].
        destruct (name_eqb n k') eqn:E'; simpl; [exact IH|]. rewrite E'. exact IH.
      * clear Eb E. induction bucket as [|[k' v'] b IH]; simpl; [reflexivity|].
        destruct (name_eqb n k') eqn:E'; simpl.
        -- apply term_eqb_eq in E'. subst k'. rewrite Ek. exact IH.
        -- destruct (name_eqb k k'); [reflexivity | exact IH].
    + rewrite ZF.add_neq_o by exact E. destruct (name_eqb k n) eqn:Ek; [|reflexivity].
      exfalso. apply E. symmetry. apply name_key_eqb. exact Ek.
  - destruct (name_eqb k n) eqn:Ek; [|reflexivity].
    apply term_eqb_eq in Ek. subst k. rewrite Eb. reflexivity.
Qed.

(** A name k has a value after adding the name n exactly when k is n
    or it had one already. *)
Lemma nm_mem_add : forall (A : Type) k n (v : A) m,
  nm_mem k (nm_add n v m) = name_eqb k n || nm_mem k m.
Proof. intros A k n v m. unfold nm_mem. rewrite nm_find_add. destruct (name_eqb k n); reflexivity. Qed.

(** A lookup of k in two association lists joined, ps then qs, answers
    from ps if k is there, and otherwise from qs. *)
Lemma lookup_app : forall (A : Type) k (ps qs : list (name * A)),
  lookup k (ps ++ qs) = match lookup k ps with Some v => Some v | None => lookup k qs end.
Proof.
  intros A k ps qs. induction ps as [|[k' v'] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb k k'); [reflexivity | exact IH].
Qed.

(** Adding the pairs ps to a map m one by one, as [nm_of_list] does
    from the empty map, a later pair replaces an earlier one: a lookup
    of k answers as the reversed list does, and falls back to m. *)
Lemma nm_find_fold_add : forall (A : Type) k (ps : list (name * A)) m,
  nm_find k (fold_left (fun m p => nm_add (fst p) (snd p) m) ps m)
  = match lookup k (rev ps) with Some v => Some v | None => nm_find k m end.
Proof.
  intros A k ps. induction ps as [|[k' v'] ps IH]; intros m; simpl; [reflexivity|].
  rewrite IH, lookup_app, nm_find_add. simpl.
  destruct (lookup k (rev ps)); [reflexivity|]. destruct (name_eqb k k'); reflexivity.
Qed.

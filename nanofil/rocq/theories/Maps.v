(** Finite maps keyed by names, the model's counterpart of
    library(assoc), which ir.pl and cfg.pl use for every table indexed
    by a label or a temporary.

    The association lists of Term.v (`lookup`, `put`) take time
    linear in their length, and a function of a thousand blocks and
    twenty thousand temporaries asks them millions of questions. A
    name map hashes each name to an integer and keeps, under each
    hash, an association list of the names that share it. A lookup
    compares names with `name_eqb` within its bucket, so two names
    with one hash stay apart: the hash decides only speed, never an
    answer.

    The buckets are kept in the stdlib's AVL tree keyed by integers,
    whose extracted lookups compare integers. A tree keyed by
    positives (FMapPositive) walks its key bit by bit, and each bit is
    a division of a zarith integer once extracted: the validator was
    thirty times slower with it. *)


From Stdlib Require Import String ZArith List Ascii OrderedTypeEx FMapAVL FMapFacts.
From Nanofil Require Import Term.
Import ListNotations.
Local Open Scope Z_scope.

Module ZMap := FMapAVL.Make Z_as_OT.

(** ## Hashing *)

(** The hashes stay below 2^20. *)
Definition hash_bound : Z := 2 ^ 20.

Definition hash_step (h x : Z) : Z := (h * 31 + x) mod hash_bound.

Fixpoint string_hash (s : string) (h : Z) : Z :=
  match s with
  | EmptyString => h
  | String c s' => string_hash s' (hash_step h (Z.of_N (N_of_ascii c)))
  end.

(** A hash of a ground term, from its form and parts. *)
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

Definition name_key (n : name) : Z := term_hash n.

(** ## Name maps *)

Definition nmap (A : Type) : Type := ZMap.t (list (name * A)).

Definition nm_empty {A : Type} : nmap A := ZMap.empty _.

(** `get_assoc(Key, Assoc, V)`. *)
Definition nm_find {A : Type} (n : name) (m : nmap A) : option A :=
  match ZMap.find (name_key n) m with
  | Some bucket => lookup n bucket
  | None => None
  end.

(** `put_assoc(Key, Assoc0, V, Assoc)`: Key now maps to V. *)
Definition nm_add {A : Type} (n : name) (v : A) (m : nmap A) : nmap A :=
  let k := name_key n in
  let bucket := match ZMap.find k m with Some b => b | None => [] end in
  ZMap.add k (put n v bucket) m.

(** `del_assoc(Key, Assoc0, V, Assoc)`: Key no longer has a value. *)
Definition nm_remove {A : Type} (n : name) (m : nmap A) : nmap A :=
  let k := name_key n in
  match ZMap.find k m with
  | Some bucket => ZMap.add k (filter (fun p => negb (name_eqb n (fst p))) bucket) m
  | None => m
  end.

Definition nm_mem {A : Type} (n : name) (m : nmap A) : bool :=
  match nm_find n m with Some _ => true | None => false end.

(** `list_to_assoc(Pairs, Assoc)`, for pairs whose keys differ (a later
    pair would replace an earlier one; list_to_assoc/2 throws). *)
Definition nm_of_list {A : Type} (ps : list (name * A)) : nmap A :=
  fold_left (fun m p => nm_add (fst p) (snd p) m) ps nm_empty.

(** ## What a lookup answers

    The lemmas below say what each operation does to a lookup, by name
    and not by hash: a map answers as the association list of its
    puts would. *)

Module ZF := FMapFacts.WFacts_fun Z_as_OT ZMap.

Lemma name_key_eqb : forall a b, name_eqb a b = true -> name_key a = name_key b.
Proof. intros a b H. apply term_eqb_eq in H. subst. reflexivity. Qed.

Lemma lookup_put_name : forall (A : Type) k n (v : A) ps,
  lookup k (put n v ps) = if name_eqb k n then Some v else lookup k ps.
Proof.
  intros A k n v ps. simpl. destruct (name_eqb k n) eqn:E; [reflexivity|].
  induction ps as [|[k' v'] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb n k') eqn:E'; simpl.
  - apply term_eqb_eq in E'. subst k'. rewrite E. exact IH.
  - destruct (name_eqb k k'); [reflexivity | exact IH].
Qed.

Lemma nm_find_empty : forall (A : Type) k, nm_find k (@nm_empty A) = None.
Proof. intros A k. unfold nm_find, nm_empty. rewrite ZF.empty_o. reflexivity. Qed.

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

Lemma nm_mem_add : forall (A : Type) k n (v : A) m,
  nm_mem k (nm_add n v m) = name_eqb k n || nm_mem k m.
Proof. intros A k n v m. unfold nm_mem. rewrite nm_find_add. destruct (name_eqb k n); reflexivity. Qed.

Lemma lookup_app : forall (A : Type) k (ps qs : list (name * A)),
  lookup k (ps ++ qs) = match lookup k ps with Some v => Some v | None => lookup k qs end.
Proof.
  intros A k ps qs. induction ps as [|[k' v'] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb k k'); [reflexivity | exact IH].
Qed.

(** `nm_of_list`: a later pair replaces an earlier one, so a lookup
    answers as the reversed list does. *)
Lemma nm_find_fold_add : forall (A : Type) k (ps : list (name * A)) m,
  nm_find k (fold_left (fun m p => nm_add (fst p) (snd p) m) ps m)
  = match lookup k (rev ps) with Some v => Some v | None => nm_find k m end.
Proof.
  intros A k ps. induction ps as [|[k' v'] ps IH]; intros m; simpl; [reflexivity|].
  rewrite IH, lookup_app, nm_find_add. simpl.
  destruct (lookup k (rev ps)); [reflexivity|]. destruct (name_eqb k k'); reflexivity.
Qed.

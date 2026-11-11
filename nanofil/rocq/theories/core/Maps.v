(** Compiler tables repeatedly look up [[block]] labels and
    [[temporary]] names, making a linear search costly in a large function.
    This module supplies [[name-map|name maps]] for those tables,
    replacing repeated full-list scans with hash buckets stored in a balanced tree.
    They serve the role of Prolog's association maps in ir.pl and
    cfg.pl, while accepting the model's structured names as keys.

    Each name hashes to an integer bucket, and a lookup compares
    complete names within that bucket before selecting its answer.
    Distinct names therefore remain separate even when their hashes
    collide; changing the hash can affect performance but not the returned value.
    The tree uses integer comparisons rather than a bit-by-bit key
    walk, avoiding repeated big-integer divisions in the [[extraction|extracted]] OCaml program. *)


From Stdlib Require Import String ZArith List Ascii OrderedTypeEx FMapAVL FMapFacts.
From Nanofil Require Import Term.
Import ListNotations.
Local Open Scope Z_scope.

(** The bucket table uses the standard library's balanced integer-keyed
    tree, instantiated as [ZMap], rather than storing buckets in a linear list. *)
Module ZMap := FMapAVL.Make Z_as_OT.

(** ## Hashing

    A hash chooses where to search for a name, not whether two names
    are equal, so collisions need no special proof assumption.
    The following functions combine term structure and character codes
    into bounded integers that index the bucket tree. *)

(** Hash mixing reduces each result modulo [hash_bound], limiting the
    bucket keys produced for names to the integers below two to the twentieth power. *)
Definition hash_bound : Z := 2 ^ 20.

(** Adding one number to a running hash uses [hash_step], which
    multiplies the previous value by 31 before reducing the sum modulo the bound. *)
Definition hash_step (h x : Z) : Z := (h * 31 + x) mod hash_bound.

(** Hashing a string folds its character codes into the supplied
    initial value, as [string_hash] repeatedly applies the single-number mixing step. *)
Fixpoint string_hash (s : string) (h : Z) : Z :=
  match s with
  | EmptyString => h
  | String c s' => string_hash s' (hash_step h (Z.of_N (N_of_ascii c)))
  end.

(** Structured names need hashes for integers, atoms, compounds, and
    lists, which [term_hash] distinguishes with separate initial values.
    It recursively hashes each compound argument or list element and
    combines those results in their original order. *)
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

(** A name's bucket key comes from [name_key], which applies the term
    hash because names may be structured terms rather than strings. *)
Definition name_key (n : name) : Z := term_hash n.

(** ## Name maps

    Each tree entry holds a list of complete names and their values,
    allowing several distinct keys to share one hash bucket.
    Lookup, insertion, and removal inspect that list by name, preserving
    all other names even when they occupy the same bucket. *)

(** A table of named values uses [nmap], whose integer-keyed tree holds
    association lists for all names assigned to each bucket. *)
Definition nmap (A : Type) : Type := ZMap.t (list (name * A)).

(** A newly empty table uses [nm_empty], which contains neither named
    values nor bucket entries and corresponds to Prolog's empty association map. *)
Definition nm_empty {A : Type} : nmap A := ZMap.empty _.

(** Looking up a name uses [nm_find] to select its bucket and search
    for the complete name, returning no value when either search fails. *)
Definition nm_find {A : Type} (n : name) (m : nmap A) : option A :=
  match ZMap.find (name_key n) m with
  | Some bucket => lookup n bucket
  | None => None
  end.

(** Inserting or replacing a named value uses [nm_add], which changes
    only that name's entry within its selected bucket. *)
Definition nm_add {A : Type} (n : name) (v : A) (m : nmap A) : nmap A :=
  let k := name_key n in
  let bucket := match ZMap.find k m with Some b => b | None => [] end in
  ZMap.add k (put n v bucket) m.

(** Removing a name uses [nm_remove], which filters that name out of
    its bucket while leaving any colliding names and their values intact. *)
Definition nm_remove {A : Type} (n : name) (m : nmap A) : nmap A :=
  let k := name_key n in
  match ZMap.find k m with
  | Some bucket => ZMap.add k (filter (fun p => negb (name_eqb n (fst p))) bucket) m
  | None => m
  end.

(** A caller that needs only membership uses [nm_mem], which reports
    whether lookup finds any value for the requested name. *)
Definition nm_mem {A : Type} (n : name) (m : nmap A) : bool :=
  match nm_find n m with Some _ => true | None => false end.

(** Building a table from pairs uses [nm_of_list], which inserts them
    in order and lets a later occurrence replace an earlier value.
    This agrees with Prolog's list-to-map construction for distinct
    keys, but repeated keys replace values here rather than raising an error. *)
Definition nm_of_list {A : Type} (ps : list (name * A)) : nmap A :=
  fold_left (fun m p => nm_add (fst p) (snd p) m) ps nm_empty.

(** ## What a lookup answers

    A caller should reason about named values without depending on
    bucket selection, tree balancing, or collisions between different names.
    The following lemmas show that map operations answer exactly as
    the corresponding updates to a simple association list would answer. *)

(** The following proofs use [ZF] to obtain the standard library's
    lookup facts for insertion, removal, and empty integer-keyed trees. *)
Module ZF := FMapFacts.WFacts_fun Z_as_OT ZMap.

(** Equal names must select the same bucket, which [name_key_eqb]
    proves by connecting the name comparison with equality of bucket keys. *)
Lemma name_key_eqb : forall a b, name_eqb a b = true -> name_key a = name_key b.
Proof. intros a b H. apply term_eqb_eq in H. subst. reflexivity. Qed.

(** Updating an association list changes the answer for the updated
    name alone, as [lookup_put_name] proves for the bucket-level operation. *)
Lemma lookup_put_name : forall (A : Type) k n (v : A) ps,
  lookup k (put n v ps) = if name_eqb k n then Some v else lookup k ps.
Proof.
  intros A k n v ps. simpl. destruct (name_eqb k n) eqn:E; [reflexivity|].
  induction ps as [|[k' v'] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb n k') eqn:E'; simpl.
  - apply term_eqb_eq in E'. subst k'. rewrite E. exact IH.
  - destruct (name_eqb k k'); [reflexivity | exact IH].
Qed.

(** Every lookup in a newly empty map returns no value, which
    [nm_find_empty] establishes independently of the requested name or value type. *)
Lemma nm_find_empty : forall (A : Type) k, nm_find k (@nm_empty A) = None.
Proof. intros A k. unfold nm_find, nm_empty. rewrite ZF.empty_o. reflexivity. Qed.

(** Inserting a value changes the answer for that name and preserves
    every other answer, even for names sharing its hash bucket.
    The lemma [nm_find_add] gives this observable update rule without
    exposing the map's tree or bucket representation. *)
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

(** Removing a name leaves it without a value and preserves the answer
    for every other name, as [nm_find_remove] proves across possible hash collisions. *)
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

(** After insertion, membership holds for the inserted name and every
    previously present name, as [nm_mem_add] derives from the lookup rule. *)
Lemma nm_mem_add : forall (A : Type) k n (v : A) m,
  nm_mem k (nm_add n v m) = name_eqb k n || nm_mem k m.
Proof. intros A k n v m. unfold nm_mem. rewrite nm_find_add. destruct (name_eqb k n); reflexivity. Qed.

(** Searching concatenated association lists prefers the first list
    whenever it contains the requested name, as [lookup_app] shows for the combined lookup. *)
Lemma lookup_app : forall (A : Type) k (ps qs : list (name * A)),
  lookup k (ps ++ qs) = match lookup k ps with Some v => Some v | None => lookup k qs end.
Proof.
  intros A k ps qs. induction ps as [|[k' v'] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb k k'); [reflexivity | exact IH].
Qed.

(** Inserting pairs in order gives the last occurrence of a name
    priority, while preserving old values for names absent from the inserted pairs.
    The lemma [nm_find_fold_add] expresses this result as lookup in the
    reversed pair list, falling back to the original map. *)
Lemma nm_find_fold_add : forall (A : Type) k (ps : list (name * A)) m,
  nm_find k (fold_left (fun m p => nm_add (fst p) (snd p) m) ps m)
  = match lookup k (rev ps) with Some v => Some v | None => nm_find k m end.
Proof.
  intros A k ps. induction ps as [|[k' v'] ps IH]; intros m; simpl; [reflexivity|].
  rewrite IH, lookup_app, nm_find_add. simpl.
  destruct (lookup k (rev ps)); [reflexivity|]. destruct (name_eqb k k'); reflexivity.
Qed.

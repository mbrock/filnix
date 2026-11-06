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


From Stdlib Require Import String ZArith List Ascii OrderedTypeEx FMapAVL.
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

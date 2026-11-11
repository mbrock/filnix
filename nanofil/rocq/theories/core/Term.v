(** In Nanofil, the Prolog compiler and the formal Rocq model exchange
    intermediate-representation modules, identifier names, and run
    outcomes as ground Prolog terms. Every ground Prolog term is an
    integer, an atom, a compound term with a functor name and
    arguments, or a proper list.

    This module defines the inductive type [term] for those ground
    terms, proves that its boolean equality test [term_eqb] matches
    Rocq equality, and provides association-list maps keyed by names.
    In the formal model, [term] serves two roles. First, all names in
    the intermediate representation—[[temporary|temporaries]],
    [[block]] labels, global symbols, and named local variables—are
    ground terms that the semantics compares only for equality. Second,
    when a compiled module or an [[outcome]] crosses between Prolog and
    the [[extraction|extracted]] model, [Transport](Transport.v)
    [[transport|decodes]] the raw term into the syntax of
    [Syntax](Syntax.v) and encodes the result back. *)

From Stdlib Require Import String ZArith List Bool Ascii.
Import ListNotations.

(** ## Ground terms and structural equality

    Before a Prolog term is decoded into an instruction or value, it
    has only its syntactic tree structure. This section defines that
    tree structure and its decidable equality test so that later
    modules can compare terms and use them as map keys. *)

(** The inductive type [term] represents a ground Prolog term with one
    constructor for each syntactic form. Proper lists use their own
    [TList] constructor rather than nested two-argument list compounds
    so that decoding a list of blocks or instructions is a direct list
    map. *)
Inductive term : Type :=
| TInt (n : Z) (* an integer literal *)
| TAtom (a : string) (* an atom, including the empty list atom *)
| TApp (f : string) (args : list term) (* a compound term with a functor name and one or more arguments *)
| TList (ts : list term). (* a proper list of terms *)

(** The function [term_eqb] tests whether two ground terms are
    structurally identical, matching Prolog's `==/2` comparison on
    ground terms. *)
Fixpoint term_eqb (t u : term) : bool :=
  let fix list_eqb (ts us : list term) : bool :=
    match ts, us with
    | [], [] => true
    | t :: ts', u :: us' => term_eqb t u && list_eqb ts' us'
    | _, _ => false
    end in
  match t, u with
  | TInt n, TInt m => Z.eqb n m
  | TAtom a, TAtom b => String.eqb a b
  | TApp f ts, TApp g us => String.eqb f g && list_eqb ts us
  | TList ts, TList us => list_eqb ts us
  | _, _ => false
  end.

(** When [term_eqb] returns `true`, the two terms are propositionally
    equal, so a lookup that matches a key by [term_eqb] finds that
    exact term. *)
Lemma term_eqb_eq : forall t u, term_eqb t u = true -> t = u.
Proof.
  fix IH 1. intros t u H.
  destruct t as [n | a | f ts | ts], u as [n' | a' | f' us | us]; simpl in H; try discriminate H.
  - f_equal. apply Z.eqb_eq. exact H.
  - f_equal. apply String.eqb_eq. exact H.
  - apply andb_true_iff in H as [Hf Hl]. apply String.eqb_eq in Hf. subst f'. f_equal.
    revert us Hl. induction ts as [|t ts IHl]; intros [|u us] Hl; simpl in Hl; try discriminate Hl; auto.
    apply andb_true_iff in Hl as [H1 H2]. f_equal; [apply IH; exact H1 | apply IHl; exact H2].
  - f_equal.
    revert us H. induction ts as [|t ts IHl]; intros [|u us] Hl; simpl in Hl; try discriminate Hl; auto.
    apply andb_true_iff in Hl as [H1 H2]. f_equal; [apply IH; exact H1 | apply IHl; exact H2].
Qed.

(** Every ground term compares equal to itself under [term_eqb]. *)
Lemma term_eqb_refl : forall t, term_eqb t t = true.
Proof.
  fix IH 1. intros t. destruct t as [n | a | f ts | ts]; simpl.
  - apply Z.eqb_refl.
  - apply String.eqb_refl.
  - rewrite String.eqb_refl. simpl. induction ts as [|t ts IHl]; simpl; auto.
    rewrite IH. exact IHl.
  - induction ts as [|t ts IHl]; simpl; auto. rewrite IH. exact IHl.
Qed.

(** ## Identifiers and association lists

    In the intermediate representation, every identifier is a ground
    Prolog term, and environments map those identifiers to values or
    definitions. This section defines the [name] alias and the basic
    lookup and update operations on association lists. *)

(** An IR [name] identifies a [[temporary]], a [[block]] label, a
    global symbol, or a named local variable, and is represented as an
    arbitrary ground [term]. *)
Definition name := term.

(** The function [name_eqb] compares two IR names for structural
    equality using [term_eqb]. *)
Definition name_eqb : name -> name -> bool := term_eqb.

(** Given a key and an association list, [lookup] returns the value
    from the first pair whose key matches, or `None` when no pair
    matches. Because updates always place the new binding at the front
    and remove any older binding for the same key, [lookup] agrees with
    Prolog's association-list lookup on every query. *)
Fixpoint lookup {A : Type} (k : name) (ps : list (name * A)) : option A :=
  match ps with
  | [] => None
  | (k', v) :: ps' => if name_eqb k k' then Some v else lookup k ps'
  end.

(** Given a key, a value, and an association list, [put] places the new
    key-value pair at the front and filters out any existing entry for
    that key. *)
Definition put {A : Type} (k : name) (v : A) (ps : list (name * A))
  : list (name * A) :=
  (k, v) :: filter (fun p => negb (name_eqb k (fst p))) ps.

Local Open Scope Z_scope.

(** When a Prolog string literal is exported as a list of one-character
    atoms, [char_code] decodes each atom into its Unicode code point in
    the range 0 to 2047. It accepts a single ASCII byte below 128 or a
    two-byte UTF-8 sequence, and returns `None` for any other term. *)
Definition char_code (t : term) : option Z :=
  match t with
  | TAtom (String c EmptyString) =>
      let a := Z.of_nat (nat_of_ascii c) in if a <? 128 then Some a else None
  | TAtom (String c1 (String c2 EmptyString)) =>
      let a := Z.of_nat (nat_of_ascii c1) in
      let b := Z.of_nat (nat_of_ascii c2) in
      if (192 <=? a) && (a <? 224) && (128 <=? b) && (b <? 192)
      then Some ((a - 192) * 64 + (b - 128)) else None
  | _ => None
  end.

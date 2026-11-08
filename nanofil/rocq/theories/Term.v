(** Ground Prolog terms, the shape every nanofil product has before
    it means anything: an integer, an atom, a compound of a name and
    arguments, or a proper list.

    The model uses them twice. The names of nanofil's intermediate
    representation (IR), its [[temporary|temporaries]], [[block]]
    labels, symbols and named locals, are ground terms, compared only
    for equality, as ir.pl says: "Temps are ground names". And a module or
    an [[outcome]] crosses between Prolog and the [[extraction|extracted]]
    model as a term, which Transport.v [[transport|decodes]] into the
    syntax of Syntax.v and encodes back. *)

From Stdlib Require Import String ZArith List Bool Ascii.
Import ListNotations.

(** A ground Prolog term, one constructor per form. A proper list is
    its own form rather than nested `'[|]'/2` compounds, so that
    decoding a list of blocks or instructions is a map. *)
Inductive term : Type :=
| TInt (n : Z) (* the integer n *)
| TAtom (a : string) (* the atom a, `[]` included *)
| TApp (f : string) (args : list term) (* the compound `f(A1, ..., An)`, with at least one argument *)
| TList (ts : list term). (* the proper list `[T1, ..., Tn]` *)

(** Term equality, structural, as Prolog's `==/2` on ground terms. *)
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

(** [term_eqb] is sound: two terms t and u it calls equal are the same
    term, so a name found by comparing is the very name asked for. *)
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

(** Every term t is [term_eqb]-equal to itself, as Prolog's `==/2`
    holds of a term and itself. *)
Lemma term_eqb_refl : forall t, term_eqb t t = true.
Proof.
  fix IH 1. intros t. destruct t as [n | a | f ts | ts]; simpl.
  - apply Z.eqb_refl.
  - apply String.eqb_refl.
  - rewrite String.eqb_refl. simpl. induction ts as [|t ts IHl]; simpl; auto.
    rewrite IH. exact IHl.
  - induction ts as [|t ts IHl]; simpl; auto. rewrite IH. exact IHl.
Qed.

(** A name of the IR: a [[temporary]], a [[block]] label, a symbol or a
    named local, any ground term. *)
Definition name := term.

(** Equality of names, which is [term_eqb]. *)
Definition name_eqb : name -> name -> bool := term_eqb.

(** As `memberchk(Key-V, Pairs)`: the value of the first pair of the
    association list ps whose key is k, if any. Prolog's library(assoc)
    and the association lists here agree on every lookup: a key is put
    once, or replaced. *)
Fixpoint lookup {A : Type} (k : name) (ps : list (name * A)) : option A :=
  match ps with
  | [] => None
  | (k', v) :: ps' => if name_eqb k k' then Some v else lookup k ps'
  end.

(** As `put_assoc(Key, Assoc0, V, Assoc)`: the association list ps
    with k now mapped to v, in front, and k's old pair dropped. *)
Definition put {A : Type} (k : name) (v : A) (ps : list (name * A))
  : list (name * A) :=
  (k, v) :: filter (fun p => negb (name_eqb k (fst p))) ps.

Local Open Scope Z_scope.

(** The code of t, a one-character atom, as `char_code/2` gives it, for
    the codes 0 to 2047: one byte below 128, or a two-byte UTF-8
    sequence. Any other term, or an atom of another code, has none. *)
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

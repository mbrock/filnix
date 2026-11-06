(** Ground Prolog terms, the shape every nanofil product has before
    it means anything: an integer, an atom, a compound of a name and
    arguments, or a proper list.

    The model uses them twice. Names in the IR (temporaries, labels,
    symbols, named locals) are ground terms, compared only for equality,
    as ir.pl says: "Temps are ground names". And a module or an outcome
    crosses between Prolog and the extracted model as a term, which
    Transport.v decodes into the syntax of Syntax.v and encodes back.

    ## Forms

    | Term | Prolog |
    |---|---|
    | `TInt n` | the integer `n` |
    | `TAtom a` | the atom `a` (including `[]`) |
    | `TApp f args` | the compound `f(Args...)`, at least one argument |
    | `TList ts` | the proper list `[T1, T2, ...]` |

    A list is its own form rather than nested `'[|]'/2` compounds, so
    that decoding a list of blocks or instructions is a map. *)

From Stdlib Require Import String ZArith List Bool.
Import ListNotations.

Inductive term : Type :=
| TInt (n : Z)
| TAtom (a : string)
| TApp (f : string) (args : list term)
| TList (ts : list term).

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

(** A name of the IR: a temporary, label, symbol or named local. *)
Definition name := term.

Definition name_eqb : name -> name -> bool := term_eqb.

(** `memberchk(Key-V, Pairs)`: the value of the first pair whose key is
    Key. Prolog's assoc (library(assoc)) and the association lists here
    agree on every lookup: a key is put once, or replaced. *)
Fixpoint lookup {A : Type} (k : name) (ps : list (name * A)) : option A :=
  match ps with
  | [] => None
  | (k', v) :: ps' => if name_eqb k k' then Some v else lookup k ps'
  end.

(** `put_assoc(Key, Assoc0, V, Assoc)`: Key now maps to V. *)
Definition put {A : Type} (k : name) (v : A) (ps : list (name * A))
  : list (name * A) :=
  (k, v) :: filter (fun p => negb (name_eqb k (fst p))) ps.

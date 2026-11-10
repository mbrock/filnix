(** Prolog's standard order of terms, and the sorted lists the Prolog
    compiler makes with it: `sort/2`, `msort/2` and the ordsets of
    library(ordsets). The backend's plans list temporaries, live
    ranges and thunks in this order, so the Gallina backend sorts by
    it too.

    For the ground terms of Term.v the order is: integers by value,
    then `[]`, then atoms by character code, then compounds, by
    arity, then by name, then by their arguments from the left. A
    list that is not empty is the compound `'[|]'(Head, Tail)`. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term.
Import ListNotations.

(** ## Comparing *)

(** The order of two atoms' names: by character code, a prefix
    first. Extract.v makes it OCaml's comparison of strings. *)
Definition atom_compare (a b : string) : comparison := String.compare a b.

(** [c], or [d] if c finds its two sides equal: one more key of a
    comparison by several. *)
Definition thenc (c d : comparison) : comparison :=
  match c with Eq => d | _ => c end.

(** As `compare(Order, T, U)`: the standard order of the terms t and
    u. *)
Fixpoint term_compare (t u : term) {struct t} : comparison :=
  let fix args_compare (ts us : list term) {struct ts} : comparison :=
    match ts, us with
    | [], [] => Eq
    | [], _ :: _ => Lt
    | _ :: _, [] => Gt
    | t' :: ts', u' :: us' => thenc (term_compare t' u') (args_compare ts' us')
    end in
  (* The list ts against the term u. *)
  let fix list_compare (ts : list term) (u : term) {struct ts} : comparison :=
    match ts with
    | [] => match u with
            | TInt _ => Gt
            | TList [] => Eq
            | _ => Lt
            end
    | h :: ts' =>
        match u with
        | TInt _ | TAtom _ | TList [] => Gt
        | TList (h' :: us') => thenc (term_compare h h') (list_compare ts' (TList us'))
        | TApp g [b1; b2] =>
            thenc (atom_compare "[|]" g) (thenc (term_compare h b1) (list_compare ts' b2))
        | TApp _ bs => Nat.compare 2 (length bs)
        end
    end in
  match t with
  | TInt n => match u with TInt m => Z.compare n m | _ => Lt end
  | TAtom a => match u with
               | TInt _ | TList [] => Gt
               | TAtom b => atom_compare a b
               | _ => Lt
               end
  | TList ts => list_compare ts u
  | TApp f ts =>
      match u with
      | TInt _ | TAtom _ | TList [] => Gt
      | TApp g us =>
          thenc (Nat.compare (length ts) (length us))
                (thenc (atom_compare f g) (args_compare ts us))
      | TList (h' :: us') =>
          match ts with
          | [a1; a2] =>
              thenc (atom_compare f "[|]")
                    (thenc (term_compare a1 h') (term_compare a2 (TList us')))
          | _ => Nat.compare (length ts) 2
          end
      end
  end.

(** ## Sorting *)

Section Sorting.
  Context {A : Type} (cmp : A -> A -> comparison).

  (** The sorted lists xs and ys merged; of two equal elements, xs's
      comes first. *)
  Fixpoint merge (xs : list A) : list A -> list A :=
    fix merge_into (ys : list A) : list A :=
      match xs, ys with
      | [], _ => ys
      | _, [] => xs
      | x :: xs', y :: ys' =>
          match cmp x y with
          | Gt => y :: merge_into ys'
          | _ => x :: merge xs' ys
          end
      end.

  (** A merge sort's stack of sorted runs: the run at depth i, if
      there is one, has 2^i elements. *)
  Fixpoint push_run (stack : list (option (list A))) (run : list A)
    : list (option (list A)) :=
    match stack with
    | [] => [Some run]
    | None :: stack' => Some run :: stack'
    | Some run' :: stack' => None :: push_run stack' (merge run' run)
    end.

  (** The runs of a stack merged, the oldest first. *)
  Fixpoint merge_runs (stack : list (option (list A))) : list A :=
    match stack with
    | [] => []
    | None :: stack' => merge_runs stack'
    | Some run :: stack' => merge (merge_runs stack') run
    end.

  (** As `msort(Xs, Sorted)`: xs in the order of cmp, equal elements
      in the order they had (a merge sort, as SWI-Prolog's is). *)
  Definition msort (xs : list A) : list A :=
    merge_runs (fold_left (fun stack x => push_run stack [x]) xs []).

  (** A sorted list with one element of each run of equal ones. *)
  Fixpoint dedup (xs : list A) : list A :=
    match xs with
    | x :: (y :: _) as xs' =>
        match cmp x y with Eq => dedup xs' | _ => x :: dedup xs' end
    | _ => xs
    end.

  (** As `sort(Xs, Sorted)`: xs sorted, without duplicates. Its
      results are ordsets. *)
  Definition sort (xs : list A) : list A := dedup (msort xs).

  (** As `ord_union(Xs, Ys, Zs)`: the union of two ordsets. *)
  Fixpoint ord_union (xs : list A) : list A -> list A :=
    fix union_into (ys : list A) : list A :=
      match xs, ys with
      | [], _ => ys
      | _, [] => xs
      | x :: xs', y :: ys' =>
          match cmp x y with
          | Lt => x :: ord_union xs' ys
          | Eq => x :: ord_union xs' ys'
          | Gt => y :: union_into ys'
          end
      end.

  (** As `ord_subtract(Xs, Ys, Zs)`: the elements of the ordset xs
      that are not in the ordset ys. *)
  Fixpoint ord_subtract (xs : list A) : list A -> list A :=
    fix subtract_from (ys : list A) : list A :=
      match xs, ys with
      | [], _ => []
      | _, [] => xs
      | x :: xs', y :: ys' =>
          match cmp x y with
          | Lt => x :: ord_subtract xs' ys
          | Eq => ord_subtract xs' ys'
          | Gt => subtract_from ys'
          end
      end.
End Sorting.

(** Whether two ordsets of names are the same. *)
Fixpoint names_eqb (xs ys : list name) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => name_eqb x y && names_eqb xs' ys'
  | _, _ => false
  end.

Example order_kinds :
  msort term_compare
    [TApp "g" [TAtom "a"; TAtom "b"]; TList [TAtom "a"]; TAtom "b";
     TApp "-" [TAtom "a"; TAtom "b"]; TList []; TInt 3; TAtom "a"; TInt (-1)]
  = [TInt (-1); TInt 3; TList []; TAtom "a"; TAtom "b";
     TApp "-" [TAtom "a"; TAtom "b"]; TList [TAtom "a"];
     TApp "g" [TAtom "a"; TAtom "b"]].
Proof. reflexivity. Qed.

Example sort_dedups :
  sort Z.compare [3; 1; 2; 3; 1]%Z = [1; 2; 3]%Z.
Proof. reflexivity. Qed.

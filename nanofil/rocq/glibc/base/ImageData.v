(** Image proofs check the addresses of named objects and read the bytes
    emitted for global data. These operations use the module and the
    loader's symbol table. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory MemLogic.
Import ListNotations.
Open Scope Z_scope.

(** A data object of the image starting at b lives in region reg. *)
Definition gd (b e : Z) : region := mkRegion b e GlobalData Live.

(** A symbol names the read-only object at b. *)
Definition lookup_ro (g : list (name * ptr)) (n : string) (b : Z) : bool :=
  match Term.lookup (TAtom n) g with
  | Some p => (ptr_addr p =? b) && match ptr_cap p with Ro c => c =? b | _ => false end
  | None => false
  end.

Lemma lookup_ro_ok g n b : lookup_ro g n b = true -> Term.lookup (TAtom n) g = Some (mkPtr b (Ro b)).
Proof.
  unfold lookup_ro. destruct (Term.lookup (TAtom n) g) as [[a c]|]; [|discriminate]. cbn [ptr_addr ptr_cap].
  destruct c; try (rewrite andb_false_r; discriminate). intros H. apply andb_true_iff in H as [Ha Hc].
  apply Z.eqb_eq in Ha, Hc. subst. reflexivity.
Qed.

Lemma places_ok g (ns : list string) (bs : list (Z * region)) : List.length ns = List.length bs ->
  forallb (fun nb : string * (Z * region) => lookup_ro g nb.1 nb.2.1) (combine ns bs) = true ->
  Forall2 (fun n br => Term.lookup (TAtom n) g = Some (mkPtr br.1 (Ro br.1))) ns bs.
Proof.
  revert bs. induction ns as [|n ns IH]; intros [|br bs] Hl H; try discriminate Hl; [constructor|].
  cbn in H. apply andb_true_iff in H as [H1 H2]. constructor; [exact (lookup_ro_ok _ _ _ H1) | apply IH; auto].
Qed.

(** A symbol names the writable object at b. *)
Definition lookup_obj (g : list (name * ptr)) (n : string) (b : Z) : bool :=
  match Term.lookup (TAtom n) g with
  | Some p => (ptr_addr p =? b) && match ptr_cap p with Obj c => c =? b | _ => false end
  | None => false
  end.

Lemma lookup_obj_ok g n b : lookup_obj g n b = true -> Term.lookup (TAtom n) g = Some (mkPtr b (Obj b)).
Proof.
  unfold lookup_obj. destruct (Term.lookup (TAtom n) g) as [[a c]|]; [|discriminate]. cbn [ptr_addr ptr_cap].
  destruct c; try (rewrite andb_false_r; discriminate). intros H. apply andb_true_iff in H as [Ha Hc].
  apply Z.eqb_eq in Ha, Hc. subst. reflexivity.
Qed.

(** These are the bytes that the image gives the object named n, in
    order. A wide string stores four bytes for each character. *)
Definition data_bytes (md : module) (n : string) : list Z :=
  match find (fun it => match it with IData k _ _ _ => name_eqb k (TAtom n) | _ => false end) md with
  | Some (IData _ _ _ its) => flat_map (fun it => match it with
      | Str c => c | Item Wb x => [x] | Item Ww x => le_bytes x 4 | _ => [] end) its
  | _ => []
  end.

(** The C string that starts the bytes xs ends at their first zero. *)
Fixpoint upto_zero (xs : list Z) : list Z :=
  match xs with [] => [] | x :: xs' => if x =? 0 then [] else x :: upto_zero xs' end.

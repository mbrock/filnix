(** A lemma about a function that reads a C structure must own the
    structure's fields. Written cell by cell, each lemma repeats the
    same offsets, and a reader has to know that offset 8 is
    `c: write_ptr`. The layout tables of a fixture record every field's
    name, offset and size. This module turns such a table into one
    predicate, so a lemma names the fields it uses and never writes an
    offset.

    A proof says which fields of a structure it owns by listing their
    names, each with a value. The value says whether the field holds a
    pointer, an integer or bytes. The predicate [struct_at] owns the
    fields of such a list, and it takes each field's offset and width
    from the table. A proof cannot own a field whose name is
    misspelled, because the predicate is false for a name that the
    table lacks. The predicate [struct_live] owns the lifetime of the
    object that holds the structure, and it says that the object has
    room for the structure. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap.
From Glibc Require Import Fix OsMemLogic.
Import ListNotations ML0 LG0 LG0.L.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Layout tables *)

(** A row of a layout table has a record's tag, a field's name, its
    byte offset, the size of its type and the alignment of its type. *)
Definition layout : Type := list (string * string * Z * Z * Z).

(** The function [field_at] finds the offset and the size of a field
    in a layout table. *)
Definition field_at (L : layout) (tag f : string) : option (Z * Z) :=
  option_map (fun entry => let '(_, _, off, size, _) := entry in (off, size))
    (find (fun entry => let '(t, g, _, _, _) := entry in (String.eqb t tag && String.eqb g f)%bool) L).

(** The function [field_off] gives the offset of a field, and
    [field_end] gives the offset of the first byte after the field.
    Both give zero for a field that the table lacks. *)
Definition field_off (L : layout) (tag f : string) : Z :=
  match field_at L tag f with Some (off, _) => off | None => 0 end.

Definition field_end (L : layout) (tag f : string) : Z :=
  match field_at L tag f with Some (off, size) => off + size | None => 0 end.

(** The function [record_at] finds the size and the alignment of a
    record. *)
Definition record_at (R : list (string * (Z * Z))) (tag : string) : Z * Z :=
  match find (fun entry => String.eqb (fst entry) tag) R with Some (_, sa) => sa | None => (0, 1) end.

(** ## Field values *)

(** A field holds a pointer, an integer of the field's width, or bytes. *)
Inductive fval : Type :=
| VPtr (p : ptr)
| VInt (z : Z)
| VBytes (xs : list Z).

(** The function [fset] replaces the value of one field. *)
Fixpoint fset (f : string) (v : fval) (vs : list (string * fval)) : list (string * fval) :=
  match vs with
  | [] => []
  | (g, w) :: rest => if String.eqb f g then (g, v) :: rest else (g, w) :: fset f v rest
  end.

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** One field of the object b is owned as a pointer cell, an eight-byte
    integer, a four-byte integer or a run of bytes. Any other pairing
    of a width and a value is false. *)
Definition field_own (b : Z) (place : option (Z * Z)) (v : fval) : iProp Σ :=
  match place, v with
  | Some (off, size), VPtr p => if size =? 8 then pcell b off p else False
  | Some (off, size), VInt z =>
      if size =? 8 then icell b off z else if size =? 4 then int_cell b off z else False
  | Some (off, size), VBytes xs => ⌜Z.of_nat (length xs) = size⌝ ∗ bytes b off xs
  | None, _ => False
  end%I.

(** The structure with tag tag at the object b owns each listed field
    with its listed value. *)
Definition struct_at (L : layout) (tag : string) (b : Z) (vs : list (string * fval)) : iProp Σ :=
  [∗ list] fv ∈ vs, field_own b (field_at L tag fv.1) fv.2.

(** The object b is alive in the region reg, starts at an aligned
    positive address and has room for the whole record. *)
Definition struct_live (R : list (string * (Z * Z))) (tag : string) (b : Z) (reg : region) : iProp Σ :=
  ⌜0 < b /\ b mod snd (record_at R tag) = 0 /\ b + fst (record_at R tag) <= r_end reg /\ r_end reg <= 2 ^ 63⌝ ∗
  live b reg.

(** The predicate [struct_liveq] states the same facts and owns only a
    reader's share of the object's lifetime. *)
Definition struct_liveq (dq : dfrac) (R : list (string * (Z * Z))) (tag : string) (b : Z) (reg : region)
    : iProp Σ :=
  ⌜0 < b /\ b mod snd (record_at R tag) = 0 /\ b + fst (record_at R tag) <= r_end reg /\ r_end reg <= 2 ^ 63⌝ ∗
  liveq dq b reg.

(** The first field of a list is owned beside the others. *)
Lemma struct_at_cons L tag b f v vs :
  struct_at L tag b ((f, v) :: vs) ⊣⊢ field_own b (field_at L tag f) v ∗ struct_at L tag b vs.
Proof using Type. unfold struct_at. rewrite big_sepL_cons. reflexivity. Qed.

Lemma struct_at_nil L tag b : struct_at L tag b [] ⊣⊢ emp.
Proof using Type. unfold struct_at. rewrite big_sepL_nil. reflexivity. Qed.

End own.

(** ## Tactics *)

(** The tactics below turn a structure into its cells and back. A
    proof usually names a structure by a short definition, such as the
    one for the printf buffer, and the tactics must unfold that
    definition first. A module that makes such a definition adds it to
    the hint database `structs`, and the tactics unfold every
    definition in that database. *)
Create HintDb structs.

(** The tactic [struct_cells] rewrites every [struct_at] over a
    written-out field list into its cells. It computes each field's
    place from the layout table, so the offsets appear only in the
    proof state and never in a proof script. *)
Ltac struct_cells :=
  autounfold with structs; rewrite ?struct_at_cons ?struct_at_nil;
  repeat match goal with
    | |- context [field_at ?L ?t ?f] =>
        let v := eval vm_compute in (field_at L t f) in change (field_at L t f) with v
    end;
  cbv [field_own Z.eqb Pos.eqb fst snd].

(** The tactic [struct_open] splits the structure in the hypothesis H
    into its cells, named by the pattern pat. *)
Tactic Notation "struct_open" constr(H) "as" constr(pat) :=
  iEval (struct_cells) in H; iDestruct H as pat.

(** The tactic [struct_close] turns a goal that is a structure into its
    cells and takes them from the context. *)
Ltac struct_close := iEval (struct_cells); iFrame.

(** The tactic [struct_sizes] unfolds every [struct_live] and
    [struct_liveq] and computes the record's size and alignment from
    the table. *)
Ltac struct_sizes :=
  autounfold with structs; cbv delta [struct_live struct_liveq] beta;
  repeat match goal with
    | |- context [record_at ?R ?t] =>
        let v := eval vm_compute in (record_at R t) in change (record_at R t) with v
    end;
  cbn [fst snd].

(** The tactic [struct_live_open] splits the lifetime in the hypothesis
    H into its pure facts and the token, named by the pattern pat. *)
Tactic Notation "struct_live_open" constr(H) "as" constr(pat) :=
  iEval (struct_sizes) in H; iDestruct H as pat.

(** The tactic [struct_live_close] proves a structure's lifetime from
    the token in the hypothesis H and the pure facts in the context. *)
Ltac struct_live_close H :=
  iEval (struct_sizes); iSplit; [iPureIntro; first [eassumption | lia] | iExact H].

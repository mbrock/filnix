(** This file defines checked IR from the `roots` object of Strncmp.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item_strncmp_roots : item :=
  (IData (a "strncmp_roots") (LRo (a "export")) 8 [(Sym (a "strncmp") 0)]).

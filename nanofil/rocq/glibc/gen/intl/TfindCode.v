(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_misc_tsearch_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition tfind_module : module :=
  [(IData (a "tfind_roots") (LRo (a "export")) 8 [(Sym (a "__GI___tfind") 0)]);
  IFunc Unit_misc_tsearch_os.fn___GI___tfind].

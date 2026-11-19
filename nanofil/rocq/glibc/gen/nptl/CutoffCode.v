(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_nptl_alloca_cutoff_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition cutoff_module : module :=
  [(IData (a "cutoff_roots") (LRo (a "export")) 8 [(Sym (a "__libc_alloca_cutoff") 0)]);
  IFunc Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff;
  Unit_nptl_alloca_cutoff_os.item___libc_alloca_cutoff].

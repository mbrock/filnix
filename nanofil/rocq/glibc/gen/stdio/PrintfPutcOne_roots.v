(** This file defines checked IR from the `roots` object of PrintfPutcOne.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item_printfputcone_roots : item :=
  (IData (a "printfputcone_roots") (LRo (a "export")) 8 [(Sym (a "__printf_buffer_putc_1") 0)]).

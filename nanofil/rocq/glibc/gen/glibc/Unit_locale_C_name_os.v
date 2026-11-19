(** This file defines checked IR from glibc’s `locale/C_name.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRBytes.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_codeset : item :=
  (IData (a "_nl_C_codeset") (LRo (a "export")) 1 ["ANSI_X3.4-1968"%irbytes; (Zero 1)]).

Definition item__nl_C_name : item :=
  (IData (a "_nl_C_name") (LRo (a "export")) 1 ["C"%irbytes; (Zero 1)]).

Definition item__nl_POSIX_name : item :=
  (IData (a "_nl_POSIX_name") (LRo (a "export")) 1 ["POSIX"%irbytes; (Zero 1)]).

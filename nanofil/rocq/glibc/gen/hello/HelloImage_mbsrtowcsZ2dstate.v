(** This file defines checked IR from the `mbsrtowcs-state` object of HelloImage.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__gl_mbsrtowcs_state : item :=
  (IData (a "_gl_mbsrtowcs_state") LExport 4 [(Zero 8)]).

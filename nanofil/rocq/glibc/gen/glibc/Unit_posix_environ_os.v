(** This file defines checked IR from glibc’s `posix/environ.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___environ : item :=
  (IData (a "__environ") LExport 8 [(Item Wl 0)]).

Definition item___environ_counter : item :=
  (IData (a "__environ_counter") LExport 8 [(Zero 8)]).

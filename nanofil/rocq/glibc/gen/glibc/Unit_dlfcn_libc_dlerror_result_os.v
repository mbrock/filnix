(** This file defines checked IR from glibc’s `dlfcn/libc_dlerror_result.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___libc_dlerror_result_string : item :=
  (IData (a "__libc_dlerror_result_string") (LTls (a "export")) 8 [(Zero 8)]).

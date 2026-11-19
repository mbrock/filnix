(** This file defines checked IR from glibc’s `locale/SYS_libc.os` object.
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

Definition item___GI__libc_intl_domainname : item :=
  (IData (a "__GI__libc_intl_domainname") (LRo (a "export")) 1 ["libc"%irbytes; (Zero 1)]).

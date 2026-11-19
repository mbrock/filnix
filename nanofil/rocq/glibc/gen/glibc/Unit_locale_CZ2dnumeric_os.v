(** This file defines checked IR from glibc’s `locale/C-numeric.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_LC_NUMERIC : item :=
  (IData (a "_nl_C_LC_NUMERIC") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 6); (Zero 4); (Sym (a "glibc_C_numeric#str.40") 0); (Sym (a "glibc_C_numeric#str.41") 0); (Sym (a "glibc_C_numeric#str.41") 0); (Item Ww 46); (Zero 4); (Item Ww 0); (Zero 4); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_numeric'23str'2e40 : item :=
  (IData (a "glibc_C_numeric#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 0)]).

Definition item_glibc_C_numeric'23str'2e41 : item :=
  (IData (a "glibc_C_numeric#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).

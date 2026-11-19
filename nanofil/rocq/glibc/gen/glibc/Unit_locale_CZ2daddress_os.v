(** This file defines checked IR from glibc’s `locale/C-address.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_LC_ADDRESS : item :=
  (IData (a "_nl_C_LC_ADDRESS") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 13); (Zero 4); (Sym (a "glibc_C_address#str.40") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Item Ww 0); (Zero 4); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_address'23str'2e40 : item :=
  (IData (a "glibc_C_address#str.40") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 97); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 102); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 100); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 98); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 37); (Item Wb 104); (Item Wb 32); (Item Wb 37); (Item Wb 101); (Item Wb 32); (Item Wb 37); (Item Wb 114); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 67); (Item Wb 45); (Item Wb 37); (Item Wb 122); (Item Wb 32); (Item Wb 37); (Item Wb 84); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 99); (Item Wb 37); (Item Wb 78); (Item Wb 0)]).

Definition item_glibc_C_address'23str'2e41 : item :=
  (IData (a "glibc_C_address#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).

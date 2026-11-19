(** This file defines checked IR from glibc’s `locale/C-monetary.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_LC_MONETARY : item :=
  (IData (a "_nl_C_LC_MONETARY") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 46); (Zero 4); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#str.41") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#str.40") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Sym (a "glibc_C_monetary#not_available") 0); (Item Ww 10101); (Zero 4); (Item Ww 99991231); (Zero 4); (Item Ww 10101); (Zero 4); (Item Ww 99991231); (Zero 4); (Sym (a "glibc_C_monetary#conversion_rate") 0); (Item Ww 0); (Zero 4); (Item Ww 0); (Zero 4); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_monetary'23conversion_rate : item :=
  (IData (a "glibc_C_monetary#conversion_rate") (LRo (a "local")) 4 [(Str [1; 0; 0; 0; 1; 0; 0; 0])]).

Definition item_glibc_C_monetary'23not_available : item :=
  (IData (a "glibc_C_monetary#not_available") (LRo (a "local")) 1 [(Str [255]); (Zero 1)]).

Definition item_glibc_C_monetary'23str'2e40 : item :=
  (IData (a "glibc_C_monetary#str.40") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_glibc_C_monetary'23str'2e41 : item :=
  (IData (a "glibc_C_monetary#str.41") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 0)]).

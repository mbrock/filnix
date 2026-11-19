(** This file defines checked IR from the `roots` object of MemFwd.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item_memfwd_roots : item :=
  (IData (a "memfwd_roots") (LRo (a "export")) 8 [(Sym (a "memcpy") 0); (Sym (a "mempcpy") 0); (Sym (a "memset") 0); (Sym (a "strdup") 0); (Sym (a "__errno_location") 0); (Sym (a "mbsinit") 0); (Sym (a "towlower") 0); (Sym (a "towupper") 0); (Sym (a "__ctype_b_loc") 0); (Sym (a "__ctype_tolower_loc") 0); (Sym (a "__ctype_toupper_loc") 0); (Sym (a "__ctype_init") 0); (Sym (a "__ctype_get_mb_cur_max") 0)]).

(** This file defines checked IR from glibc’s `ctype/ctype-info.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___GI___ctype_init : func :=
  ir_fn{ "export" "__GI___ctype_init"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"v1" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v1";
    %"v2" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v5" = %"v4" +p #56;
    %"chk2" : A = (Check 0 8 Read 8) %"v5";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v11" = %"v10" +p #256;
    %"chk3" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk3" + 0] <- %"v11";
    %"v12" : P = Copy $"__libc_tsd_CTYPE_TOUPPER";
    %"v13" : P = Copy $"__libc_tsd_LOCALE";
    %"chk4" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v14";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v17" = %"v16" +p #56;
    %"v21" = %"v17" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v23" = %"v22" +p #512;
    %"chk7" : A = (Check 0 8 Write 8) %"v12";
    store.ptr [%"chk7" + 0] <- %"v23";
    %"v24" : P = Copy $"__libc_tsd_CTYPE_TOLOWER";
    %"v25" : P = Copy $"__libc_tsd_LOCALE";
    %"chk8" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"v26";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v29" = %"v28" +p #56;
    %"v33" = %"v29" +p #24;
    %"chk10" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v35" = %"v34" +p #512;
    %"chk11" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk11" + 0] <- %"v35"
    => ret void
} }.

Definition item___ctype32_b : item :=
  (IData (a "__ctype32_b") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_class32") 0)]).

Definition item___ctype32_tolower : item :=
  (IData (a "__ctype32_tolower") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_tolower") 512)]).

Definition item___ctype32_toupper : item :=
  (IData (a "__ctype32_toupper") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_toupper") 512)]).

Definition item___ctype_b : item :=
  (IData (a "__ctype_b") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_class") 256)]).

Definition fn___ctype_b_loc : func :=
  ir_fn{ "export" "__ctype_b_loc"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_B"
    => ret %"v0"
} }.

Definition item___ctype_init : item :=
  (IAlias (a "__ctype_init") (a "export") (a "__GI___ctype_init")).

Definition item___ctype_tolower : item :=
  (IData (a "__ctype_tolower") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_tolower") 512)]).

Definition fn___ctype_tolower_loc : func :=
  ir_fn{ "export" "__ctype_tolower_loc"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_TOLOWER"
    => ret %"v0"
} }.

Definition item___ctype_toupper : item :=
  (IData (a "__ctype_toupper") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_toupper") 512)]).

Definition fn___ctype_toupper_loc : func :=
  ir_fn{ "export" "__ctype_toupper_loc"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_TOUPPER"
    => ret %"v0"
} }.

Definition item___libc_tsd_CTYPE_B : item :=
  (IData (a "__libc_tsd_CTYPE_B") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_class") 256)]).

Definition item___libc_tsd_CTYPE_TOLOWER : item :=
  (IData (a "__libc_tsd_CTYPE_TOLOWER") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_tolower") 512)]).

Definition item___libc_tsd_CTYPE_TOUPPER : item :=
  (IData (a "__libc_tsd_CTYPE_TOUPPER") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_toupper") 512)]).

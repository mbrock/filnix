(** This file defines checked IR from glibc’s `misc/init-misc.os` object.
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

Definition fn___init_misc : func :=
  ir_fn{ "export" "__init_misc"(W %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v10" : L = Ptoi %"v2";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L12" : "L13";
  @"L12":
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v17" : L = Ptoi %"v16";
    %"v18" : W = (Cmp Ne L) %"v17", #0
    => goto "L13";
  @"L13" [%"v20" : W = phi("start" => #0, "L12" => %"v18")]:
    => br %"v20" ? "L6" : "L8";
  @"L6":
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v25" : P = $"__GI_strrchr"(P %"v24", W #47);
    %"v30" : L = Ptoi %"v25";
    %"v31" : L = Ptoi #0;
    %"v32" : W = (Cmp Eq L) %"v30", %"v31"
    => br %"v32" ? "L26" : "L27";
  @"L26":
    %"v33" : P = Copy $"__progname";
    %"chk2" : A = (Renew 0 8 Read 8) %"chk1", %"v2";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (Check 0 8 Write 8) %"v33";
    store.ptr [%"chk3" + 0] <- %"v36"
    => goto "L28";
  @"L27":
    %"v37" : P = Copy $"__progname";
    %"v39" = %"v25" +p #1;
    %"chk4" : A = (Check 0 8 Write 8) %"v37";
    store.ptr [%"chk4" + 0] <- %"v39"
    => goto "L28";
  @"L28":
    %"v40" : P = Copy $"__progname_full";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"v2";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Write 8) %"v40";
    store.ptr [%"chk6" + 0] <- %"v43"
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition item___progname : item :=
  (IData (a "__progname") LExport 8 [(Sym (a "glibc_init_misc#str.61") 0)]).

Definition item___progname_full : item :=
  (IData (a "__progname_full") LExport 8 [(Sym (a "glibc_init_misc#str.61") 0)]).

Definition item_glibc_init_misc'23str'2e61 : item :=
  (IData (a "glibc_init_misc#str.61") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_program_invocation_name : item :=
  (IAlias (a "program_invocation_name") (a "weak") (a "__progname_full")).

Definition item_program_invocation_short_name : item :=
  (IAlias (a "program_invocation_short_name") (a "weak") (a "__progname")).

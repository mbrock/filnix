(** This file defines checked IR from glibc’s `dirent/readdir64.os` object.
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

Definition fn___GI___readdir64 : func :=
  ir_fn{ "export" "__GI___readdir64"(P %"v0") -> (RClass P) {
  @"start":
    %"v4" = %"v0" +p #4;
    %"chk0" : A = (Check 0 4 Write 4) %"v4";
    %"v11" : W = (RawCas (CasNarrow Sw) 0) %"chk0", #0, #1;
    %"v12" : W = (Cmp Eq W) %"v11", #0
    => br %"v12" ? "L14" : "L13";
  @"L13":
    => goto "L14";
  @"L14":
    %"v15" : W = (Cmp Ne W) %"v11", #0
    => br %"v15" ? "L18" : "iw_1.start";
  @"L18":
    call void $"__GI___lll_lock_wait_private"(P %"v4")
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v4" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Read 1) %"iw_1.v4";
    %"iw_1.v5" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"iw_1.v10" = %"v0" +p #24;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v10";
    %"iw_1.v11" : L = (RawLoad LdL 0) %"chk2";
    %"iw_1.v13" = %"v0" +p #16;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v13";
    %"iw_1.v14" : L = (RawLoad LdL 0) %"chk3";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v11", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    %"iw_1.v18" = %"v0" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v18";
    %"iw_1.v19" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"iw_1.v24" = %"v0" +p #48;
    call %"iw_1.v26" : L = $"__GI___getdents64"(W %"iw_1.v22", P %"iw_1.v24", L %"iw_1.v19");
    %"iw_1.v31" : W = (Cmp Sle L) %"iw_1.v26", #0
    => br %"iw_1.v31" ? "iw_1.L27" : "iw_1.L29";
  @"iw_1.L27":
    %"iw_1.v36" : W = (Cmp Eq L) %"iw_1.v26", #0
    => br %"iw_1.v36" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v39" : P = Copy $"__libc_errno";
    %"chk6" : A = (Check 0 4 Read 1) %"iw_1.v39";
    %"iw_1.v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"iw_1.v41" : W = (Cmp Eq W) %"iw_1.v40", #2
    => goto "iw_1.L38";
  @"iw_1.L38" [%"iw_1.v43" : W = phi("iw_1.L27" => #1, "iw_1.L37" => %"iw_1.v41")]:
    => br %"iw_1.v43" ? "iw_1.L32" : "iw_1.join";
  @"iw_1.L32":
    %"iw_1.v44" : P = Copy $"__libc_errno";
    %"chk7" : A = (Check 0 4 Write 1) %"iw_1.v44";
    store Ww [%"chk7" + 0] <- %"iw_1.v5"
    => goto "iw_1.join";
  @"iw_1.L29":
    %"iw_1.v48" = %"v0" +p #16;
    %"chk8" : A = (Renew 0 8 Write 1) %"chk3", %"iw_1.v48";
    store Wl [%"chk8" + 0] <- %"iw_1.v26";
    %"iw_1.v51" = %"v0" +p #24;
    %"chk9" : A = (Renew 0 8 Write 1) %"chk2", %"iw_1.v51";
    store Wl [%"chk9" + 0] <- #0
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"iw_1.v53" = %"v0" +p #48;
    %"iw_1.v55" = %"v0" +p #24;
    %"chk10" : A = (Renew 0 8 Read 1) %"chk2", %"iw_1.v55";
    %"iw_1.v56" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v57" = %"iw_1.v53" +p %"iw_1.v56";
    %"iw_1.v60" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v62" = %"iw_1.v57" +p #16;
    %"chk12" : A = (Check 0 2 Read 1) %"iw_1.v62";
    %"iw_1.v63" : W = (RawLoad (LdNarrow Uh) 0) %"chk12";
    %"iw_1.v64" : L = (Ext Uw) %"iw_1.v63";
    %"iw_1.v65" : L = Add %"iw_1.v60", %"iw_1.v64";
    %"chk13" : A = (Renew 0 8 Write 1) %"chk2", %"iw_1.v55";
    store Wl [%"chk13" + 0] <- %"iw_1.v65";
    %"iw_1.v67" = %"v0" +p #32;
    %"iw_1.v69" = %"iw_1.v57" +p #8;
    %"chk14" : A = (HalfCheck Lower 0 8 Read 1) %"chk12", %"iw_1.v69";
    %"iw_1.v70" : L = (RawLoad LdL 0) %"chk14";
    %"chk15" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v67";
    store Wl [%"chk15" + 0] <- %"iw_1.v70"
    => goto "iw_1.join";
  @"iw_1.join" [%"v30" : P = phi("iw_1.L8" => %"iw_1.v57", "iw_1.L38" => #0, "iw_1.L32" => #0)]:
    %"v33" = %"v0" +p #4;
    %"chk16" : A = (Renew 0 4 Read 1) %"chk0", %"v33";
    %"v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk16"
    => goto "L38";
  @"L38" [%"v40" : W = phi("iw_1.join" => %"v37", "L38" => %"v41")]:
    %"chk17" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v33";
    %"v41" : W = (RawCas (CasNarrow Sw) 0) %"chk17", %"v40", #0;
    %"v42" : W = (Cmp Eq W) %"v41", %"v40"
    => br %"v42" ? "L39" : poll "L38";
  @"L39":
    %"v47" : W = (Cmp Sgt W) %"v40", #1
    => br %"v47" ? "L50" : "L45";
  @"L50":
    call void $"__GI___lll_lock_wake_private"(P %"v33")
    => goto "L45";
  @"L45":
    => ret %"v30"
} }.

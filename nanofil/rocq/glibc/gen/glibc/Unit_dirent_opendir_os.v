(** This file defines checked IR from glibc’s `dirent/opendir.os` object.
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

Definition fn___alloc_dir : func :=
  ir_fn{ "export" "__alloc_dir"(W %"v0", W %"v2", W %"v4", P %"v6") -> (RClass P) {
  @"start":
    %"v11" : W = (Ext Ub) %"v2";
    %"v12" : W = (Cmp Eq W) %"v11", #0
    => br %"v12" ? "L13" : "L14";
  @"L13":
    call %"v16" : W = $"__GI___fcntl64_nocancel"(W %"v0", W #2, W #1);
    %"v17" : W = (Cmp Slt W) %"v16", #0
    => goto "L14";
  @"L14" [%"v21" : W = phi("start" => #0, "L13" => %"v17")]:
    => br %"v21" ? "L8" : "L10";
  @"L8":
    => ret #0;
  @"L10":
    %"v31" = %"v6" +p #56;
    %"chk0" : A = (Check 0 8 Read 1) %"v31";
    %"v32" : L = (RawLoad LdL 0) %"chk0";
    %"v33" : W = (Cmp Ugt L) %"v32", #32768
    => br %"v33" ? "L27" : "L29";
  @"L27":
    %"v35" = %"v6" +p #56;
    %"v36" : L = (RawLoad LdL 0) %"chk0"
    => goto "L29";
  @"L29" [%"v37" : L = phi("L27" => %"v36", "L10" => #32768)]:
    %"v38" : W = (Cmp Ult L) %"v37", #1048576
    => br %"v38" ? "L24" : "L26";
  @"L24":
    %"v43" = %"v6" +p #56;
    %"v44" : L = (RawLoad LdL 0) %"chk0";
    %"v45" : W = (Cmp Ugt L) %"v44", #32768
    => br %"v45" ? "L39" : "L26";
  @"L39":
    %"v47" = %"v6" +p #56;
    %"v48" : L = (RawLoad LdL 0) %"chk0"
    => goto "L26";
  @"L26" [%"v50" : L = phi("L39" => %"v48", "L24" => #32768, "L29" => #1048576)]:
    %"v53" : L = Add %"v50", #48;
    call %"v54" : P = $"malloc"(L %"v53");
    %"v59" : L = Ptoi %"v54";
    %"v60" : L = Ptoi #0;
    %"v61" : W = (Cmp Eq L) %"v59", %"v60"
    => br %"v61" ? "L55" : "L57";
  @"L55":
    => br %"v11" ? "L62" : "L64";
  @"L62":
    call void $"__GI___close_nocancel_nostatus"(W %"v0")
    => goto "L64";
  @"L64":
    => ret #0;
  @"L57":
    %"chk4" : A = (Check 0 4 Write 1) %"v54";
    store Ww [%"chk4" + 0] <- %"v0";
    %"v71" = %"v54" +p #4;
    %"chk5" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v71";
    store Ww [%"chk5" + 0] <- #0;
    %"v73" = %"v54" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v73";
    store Wl [%"chk6" + 0] <- %"v50";
    %"v76" = %"v54" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v76";
    store Wl [%"chk7" + 0] <- #0;
    %"v78" = %"v54" +p #24;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v78";
    store Wl [%"chk8" + 0] <- #0;
    %"v80" = %"v54" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 1) %"chk4", %"v80";
    store Wl [%"chk9" + 0] <- #0;
    %"v82" = %"v54" +p #40;
    %"chk10" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v82";
    store Ww [%"chk10" + 0] <- #0
    => ret %"v54"
} }.

Definition fn___opendir : func :=
  ir_fn{ "export" "__opendir"(P %"v0") -> (RClass P) {
  @"start":
    %"chk0" : A = (Check 0 1 Read 1) %"v0";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"iw_1.v8" : W = (Cmp Eq W) %"iw_1.v7", #0
    => br %"iw_1.v8" ? "iw_1.L2" : "iw_1.join";
  @"iw_1.L2":
    %"iw_1.v11" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v11";
    store Ww [%"chk1" + 0] <- #2
    => goto "iw_1.join";
  @"iw_1.join" [%"v6" : W = phi("iw_1.L2" => #1, "start" => #0)]:
    => br %"v6" ? "L2" : "L4";
  @"L2":
    => ret #0;
  @"L4":
    call %"v12" : W = $"__GI___open_nocancel"(P %"v0", W #591872);
    %"iw_2.v10" : P = (Alloc 8) #144;
    %"iw_2.v6" : W = (Cmp Slt W) %"v12", #0
    => br %"iw_2.v6" ? "iw_2.join" : "iw_2.L4";
  @"iw_2.L4":
    call %"iw_2.v15" : W = $"__GI___fstat64"(W %"v12", P %"iw_2.v10");
    %"iw_2.v16" : W = (Cmp Slt W) %"iw_2.v15", #0
    => br %"iw_2.v16" ? "iw_2.L19" : "iw_2.L13";
  @"iw_2.L13":
    %"iw_2.v24" = %"iw_2.v10" +p #24;
    %"chk2" : A = (Check 0 4 Read 1) %"iw_2.v24";
    %"iw_2.v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"iw_2.v26" : W = And %"iw_2.v25", #61440;
    %"iw_2.v28" : W = (Cmp Ne W) %"iw_2.v26", #16384
    => br %"iw_2.v28" ? "iw_2.L21" : "iw_2.L23";
  @"iw_2.L21":
    %"iw_2.v31" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"iw_2.v31";
    store Ww [%"chk3" + 0] <- #20
    => goto "iw_2.L19";
  @"iw_2.L19":
    call void $"__GI___close_nocancel_nostatus"(W %"v12")
    => goto "iw_2.join";
  @"iw_2.L23":
    call %"iw_2.v36" : P = $"__alloc_dir"(W %"v12", W #1, W #0, P %"iw_2.v10")
    => goto "iw_2.join";
  @"iw_2.join" [%"v13" : P = phi("iw_2.L19" => #0, "iw_2.L23" => %"iw_2.v36", "L4" => #0)]:
    => ret %"v13"
} }.

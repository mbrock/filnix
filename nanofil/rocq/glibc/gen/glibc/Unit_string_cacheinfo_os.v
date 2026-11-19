(** This file defines checked IR from glibc’s `string/cacheinfo.os` object.
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

Definition fn___cache_sysconf : func :=
  ir_fn{ "export" "__cache_sysconf"(W %"v0") -> (RClass L) {
  @"start":
    %"v3" : P = Copy $"_dl_x86_cpu_features";
    %"v57" : W = (Cmp Slt W) %"v0", #192
    => br %"v57" ? "L58" : "L59";
  @"L7":
    %"v9" = %"v3" +p #424;
    %"chk0" : A = (Check 0 8 Read 1) %"v9";
    %"v10" : L = (RawLoad LdL 0) %"chk0"
    => ret %"v10";
  @"L11":
    %"v13" = %"v3" +p #432;
    %"chk1" : A = (Check 0 8 Read 1) %"v13";
    %"v14" : L = (RawLoad LdL 0) %"chk1"
    => ret %"v14";
  @"L15":
    %"v17" = %"v3" +p #440;
    %"chk2" : A = (Check 0 8 Read 1) %"v17";
    %"v18" : L = (RawLoad LdL 0) %"chk2"
    => ret %"v18";
  @"L19":
    %"v21" = %"v3" +p #448;
    %"chk3" : A = (Check 0 8 Read 1) %"v21";
    %"v22" : L = (RawLoad LdL 0) %"chk3"
    => ret %"v22";
  @"L23":
    %"v25" = %"v3" +p #456;
    %"chk4" : A = (Check 0 8 Read 1) %"v25";
    %"v26" : L = (RawLoad LdL 0) %"chk4"
    => ret %"v26";
  @"L27":
    %"v29" = %"v3" +p #464;
    %"chk5" : A = (Check 0 8 Read 1) %"v29";
    %"v30" : L = (RawLoad LdL 0) %"chk5"
    => ret %"v30";
  @"L31":
    %"v33" = %"v3" +p #472;
    %"chk6" : A = (Check 0 8 Read 1) %"v33";
    %"v34" : L = (RawLoad LdL 0) %"chk6"
    => ret %"v34";
  @"L35":
    %"v37" = %"v3" +p #480;
    %"chk7" : A = (Check 0 8 Read 1) %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk7"
    => ret %"v38";
  @"L39":
    %"v41" = %"v3" +p #488;
    %"chk8" : A = (Check 0 8 Read 1) %"v41";
    %"v42" : L = (RawLoad LdL 0) %"chk8"
    => ret %"v42";
  @"L43":
    %"v45" = %"v3" +p #496;
    %"chk9" : A = (Check 0 8 Read 1) %"v45";
    %"v46" : L = (RawLoad LdL 0) %"chk9"
    => ret %"v46";
  @"L47":
    %"v49" = %"v3" +p #504;
    %"chk10" : A = (Check 0 8 Read 1) %"v49";
    %"v50" : L = (RawLoad LdL 0) %"chk10"
    => ret %"v50";
  @"L51":
    %"v53" = %"v3" +p #512;
    %"chk11" : A = (Check 0 8 Read 1) %"v53";
    %"v54" : L = (RawLoad LdL 0) %"chk11"
    => ret %"v54";
  @"L58":
    %"v60" : W = (Cmp Slt W) %"v0", #189
    => br %"v60" ? "L61" : "L62";
  @"L61":
    %"v63" : W = (Cmp Eq W) %"v0", #185
    => br %"v63" ? poll "L7" : "L64";
  @"L64":
    %"v65" : W = (Cmp Eq W) %"v0", #187
    => br %"v65" ? poll "L11" : "L66";
  @"L66":
    %"v67" : W = (Cmp Eq W) %"v0", #188
    => br %"v67" ? poll "L15" : "L6";
  @"L62":
    %"v69" : W = (Cmp Eq W) %"v0", #189
    => br %"v69" ? poll "L19" : "L70";
  @"L70":
    %"v71" : W = (Cmp Eq W) %"v0", #190
    => br %"v71" ? poll "L23" : "L72";
  @"L72":
    %"v73" : W = (Cmp Eq W) %"v0", #191
    => br %"v73" ? poll "L27" : "L6";
  @"L59":
    %"v75" : W = (Cmp Slt W) %"v0", #195
    => br %"v75" ? "L76" : "L77";
  @"L76":
    %"v78" : W = (Cmp Eq W) %"v0", #192
    => br %"v78" ? poll "L31" : "L79";
  @"L79":
    %"v80" : W = (Cmp Eq W) %"v0", #193
    => br %"v80" ? poll "L35" : "L81";
  @"L81":
    %"v82" : W = (Cmp Eq W) %"v0", #194
    => br %"v82" ? poll "L39" : "L6";
  @"L77":
    %"v84" : W = (Cmp Eq W) %"v0", #195
    => br %"v84" ? poll "L43" : "L85";
  @"L85":
    %"v86" : W = (Cmp Eq W) %"v0", #196
    => br %"v86" ? poll "L47" : "L87";
  @"L87":
    %"v88" : W = (Cmp Eq W) %"v0", #197
    => br %"v88" ? poll "L51" : "L6";
  @"L6":
    => ret #18446744073709551615
} }.

(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn_glibc_printf_fp'23round_away : func :=
  ir_fn{ "local" "glibc_printf_fp#round_away"(W %"v0", W %"v2", W %"v4", W %"v6", W %"v8") -> (RClass W) {
  @"start":
    %"v56" : W = (Cmp Eq W) %"v8", #1024
    => br %"v56" ? "L13" : "L57";
  @"L13":
    %"v14" : W = (Ext Ub) %"v0"
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v17" : W = (Ext Ub) %"v4"
    => br %"v17" ? "L16" : "L18";
  @"L18":
    %"v20" : W = (Ext Ub) %"v6";
    %"v21" : W = (Cmp Ne W) %"v20", #0
    => goto "L16";
  @"L16" [%"v24" : W = phi("L13" => #0, "L15" => #1, "L18" => %"v21")]:
    => ret %"v24";
  @"L26":
    %"v27" : W = (Ext Ub) %"v4"
    => br %"v27" ? "L28" : "L29";
  @"L28":
    %"v30" : W = (Ext Ub) %"v2"
    => br %"v30" ? "L29" : "L31";
  @"L31":
    %"v33" : W = (Ext Ub) %"v6";
    %"v34" : W = (Cmp Ne W) %"v33", #0
    => goto "L29";
  @"L29" [%"v37" : W = phi("L26" => #0, "L28" => #1, "L31" => %"v34")]:
    => ret %"v37";
  @"L39":
    => ret #0;
  @"L41":
    %"v42" : W = (Ext Ub) %"v0";
    %"v43" : W = (Cmp Eq W) %"v42", #0
    => br %"v43" ? "L44" : "L45";
  @"L44":
    %"v46" : W = (Ext Ub) %"v4"
    => br %"v46" ? "L45" : "L47";
  @"L47":
    %"v49" : W = (Ext Ub) %"v6";
    %"v50" : W = (Cmp Ne W) %"v49", #0
    => goto "L45";
  @"L45" [%"v53" : W = phi("L41" => #0, "L44" => #1, "L47" => %"v50")]:
    => ret %"v53";
  @"L55":
    call void $"__GI_abort"()
    => ret #0;
  @"L57":
    %"v58" : W = (Cmp Eq W) %"v8", #0
    => br %"v58" ? poll "L26" : "L59";
  @"L59":
    %"v60" : W = (Cmp Eq W) %"v8", #3072
    => br %"v60" ? poll "L39" : "L61";
  @"L61":
    %"v62" : W = (Cmp Eq W) %"v8", #2048
    => br %"v62" ? poll "L41" : poll "L55"
} }.

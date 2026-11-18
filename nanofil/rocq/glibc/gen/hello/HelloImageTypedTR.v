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

Definition hello_image_fn_glibc_dcigettext'23transcmp : func :=
  ir_fn{ "local" "glibc_dcigettext#transcmp"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v13" = %"v0" +p #32;
    %"chk0" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" : L = Ptoi %"v14";
    %"v16" : L = Ptoi #0;
    %"v17" : W = (Cmp Ne L) %"v15", %"v16"
    => br %"v17" ? "L9" : "L10";
  @"L9":
    %"v19" = %"v0" +p #56
    => goto "L11";
  @"L10":
    %"v21" = %"v0" +p #56;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L11";
  @"L11" [%"v23" : P = phi("L9" => %"v19", "L10" => %"v22")]:
    %"v28" = %"v2" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v30" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v16"
    => br %"v32" ? "L24" : "L25";
  @"L24":
    %"v34" = %"v2" +p #56
    => goto "L26";
  @"L25":
    %"v36" = %"v2" +p #56;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk3"
    => goto "L26";
  @"L26" [%"v38" : P = phi("L24" => %"v34", "L25" => %"v37")]:
    call %"v39" : W = $"__GI_strcmp"(P %"v23", P %"v38");
    %"v44" : W = (Cmp Eq W) %"v39", #0
    => br %"v44" ? "L40" : "L42";
  @"L40":
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v2";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v49" : W = $"__GI_strcmp"(P %"v46", P %"v48");
    %"v54" : W = (Cmp Eq W) %"v49", #0
    => br %"v54" ? "L50" : "L42";
  @"L50":
    %"v56" = %"v0" +p #16;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v59" = %"v2" +p #16;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call %"v61" : W = $"__GI_strcmp"(P %"v57", P %"v60");
    %"v66" : W = (Cmp Eq W) %"v61", #0
    => br %"v66" ? "L62" : "L42";
  @"L62":
    %"v68" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v68";
    %"v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v71" = %"v2" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk2", %"v71";
    %"v72" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v73" : W = Sub %"v69", %"v72"
    => goto "L42";
  @"L42" [%"pr.1" : W = phi("L62" => %"v73", "L50" => %"v61", "L40" => %"v49", "L26" => %"v39")]:
    => ret %"pr.1"
} }.

Definition hello_image_fn_glibc_tsearch'23trecurse_r : func :=
  ir_fn{ "local" "glibc_tsearch#trecurse_r"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v12" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : L = Ptoi %"v13";
    %"v15" : L = Ptoi #0;
    %"v16" : W = (Cmp Eq L) %"v14", %"v15"
    => br %"v16" ? "L17" : "L18";
  @"L17":
    %"v20" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v22" : L = Ptoi %"v21";
    %"v24" : W = (Cmp Eq L) %"v22", %"v15"
    => goto "L18";
  @"L18" [%"v26" : W = phi("start" => #0, "L17" => %"v24")]:
    => br %"v26" ? "L8" : "L9";
  @"L8":
    %"chk2" : F = CheckFunction %"v2";
    rawcall void %"chk2"(P %"v0", W #3, P %"v4")
    => goto "L10";
  @"L9":
    %"chk3" : F = CheckFunction %"v2";
    rawcall void %"chk3"(P %"v0", W #0, P %"v4");
    %"v37" = %"v0" +p #8;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v39" : L = Ptoi %"v38";
    %"v41" : W = (Cmp Ne L) %"v39", %"v15"
    => br %"v41" ? "L33" : "L35";
  @"L33":
    %"v43" = %"v0" +p #8;
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk4";
    call void $"glibc_tsearch#trecurse_r"(P %"v44", P %"v2", P %"v4")
    => goto "L35";
  @"L35":
    %"chk6" : F = CheckFunction %"v2";
    rawcall void %"chk6"(P %"v0", W #1, P %"v4");
    %"v54" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v56" : L = Ptoi %"v55";
    %"v58" : W = (Cmp Ne L) %"v56", %"v15"
    => br %"v58" ? "L50" : "L52";
  @"L50":
    %"v60" = %"v0" +p #16;
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call void $"glibc_tsearch#trecurse_r"(P %"v61", P %"v2", P %"v4")
    => goto "L52";
  @"L52":
    %"chk9" : F = CheckFunction %"v2";
    rawcall void %"chk9"(P %"v0", W #2, P %"v4")
    => goto "L10";
  @"L10":
    => ret void
} }.

Definition hello_image_fn___translated_number_width : func :=
  ir_fn{ "export" "__translated_number_width"(P %"v0", P %"v2", P %"v4") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v9" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" = %"v11" +p #19;
    %"chk2" : A = (Check 0 1 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"v18" : W = (Cmp Sgt W) %"v17", #0
    => br %"v18" ? "L12" : "L33";
  @"L12":
    %"v21" : L = Ptoi %"v4";
    %"v22" : L = Ptoi %"v2";
    %"v23" : L = Sub %"v21", %"v22";
    %"v25" = %"v11" +p #19;
    %"v26" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"v27" : L = (Ext Uw) %"v26";
    %"v28" : L = Mul %"v23", %"v27"
    => ret %"v28";
  @"L33" [%"pr.2" : P = phi("L44" => %"v69", "start" => %"v2"); %"pr.1" : W = phi("L44" => %"v67", "start" => #0)]:
    %"v39" : L = Ptoi %"pr.2";
    %"v40" : L = Ptoi %"v4";
    %"v41" : W = (Cmp Ult L) %"v39", %"v40"
    => br %"v41" ? "L34" : "L36";
  @"L34":
    %"chk4" : A = (Check 0 1 Read 1) %"pr.2";
    %"v46" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v47" : W = (Cmp Sge W) %"v46", #48
    => br %"v47" ? "L48" : "L49";
  @"L48":
    %"v51" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v52" : W = (Cmp Sle W) %"v51", #57
    => goto "L49";
  @"L49" [%"v54" : W = phi("L34" => #0, "L48" => %"v52")]:
    => br %"v54" ? "L44" : "L43";
  @"L43":
    %"v55" : P = Copy $"glibc_translated_number_width#str.45";
    %"v56" : P = Copy $"glibc_translated_number_width#str.46";
    %"v57" : P = Copy $"glibc_translated_number_width#str.47";
    call void $"__libc_assert_fail"(P %"v55", P %"v56", W #37, P %"v57")
    => goto "L44";
  @"L44":
    %"v60" = %"v11" +p #9;
    %"chk6" : A = (Renew 0 1 Read 1) %"chk4", %"pr.2";
    %"v62" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v63" : W = Sub %"v62", #48;
    %"v64" : L = (Ext Sw) %"v63";
    %"v65" = %"v60" +p %"v64";
    %"chk7" : A = (Check 0 1 Read 1) %"v65";
    %"v66" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v67" : W = Add %"pr.1", %"v66";
    %"v69" = %"pr.2" +p #1
    => goto poll "L33";
  @"L36":
    => ret %"pr.1"
} }.

(** This file defines checked IR from glibc’s `wctype/wcfuncs.os` object.
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

Definition fn___GI___towlower : func :=
  ir_fn{ "export" "__GI___towlower"(W %"v0") -> (RClass W) {
  @"start":
    %"v3" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v3";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v7" = %"v6" +p #56;
    %"v11" = %"v7" +p #144;
    %"chk2" : A = (Check 0 4 Read 1) %"v11";
    %"v12" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v13" : W = Add %"v12", #1;
    %"v14" : L = (Ext Uw) %"v13";
    %"v16" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Check 0 8 Read 8) %"v17";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v20" = %"v19" +p #56;
    %"v22" : W = And %"v14", #65535;
    %"v23" : L = (Ext Sw) %"v22";
    %"v24" : L = Shl %"v23", #3;
    %"v25" = %"v20" +p %"v24";
    %"chk5" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 4 Read 1) %"v26";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_1.v11" : W = Shr %"v0", %"iw_1.v7";
    %"iw_1.v14" = %"v26" +p #4;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v14";
    %"iw_1.v15" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"iw_1.v21" : W = (Cmp Ult W) %"iw_1.v11", %"iw_1.v15"
    => br %"iw_1.v21" ? "iw_1.L16" : "iw_1.join";
  @"iw_1.L16":
    %"iw_1.v25" : W = Add %"iw_1.v11", #5;
    %"iw_1.v26" : L = (Ext Uw) %"iw_1.v25";
    %"iw_1.v27" : L = Shl %"iw_1.v26", #2;
    %"iw_1.v28" = %"v26" +p %"iw_1.v27";
    %"chk8" : A = (Check 0 4 Read 1) %"iw_1.v28";
    %"iw_1.v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"iw_1.v34" : W = (Cmp Ne W) %"iw_1.v29", #0
    => br %"iw_1.v34" ? "iw_1.L30" : "iw_1.join";
  @"iw_1.L30":
    %"iw_1.v37" = %"v26" +p #8;
    %"chk9" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v37";
    %"iw_1.v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"iw_1.v41" = %"v26" +p #12;
    %"chk10" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v41";
    %"iw_1.v42" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"iw_1.v46" : W = Shr %"v0", %"iw_1.v38";
    %"iw_1.v48" : W = And %"iw_1.v46", %"iw_1.v42";
    %"iw_1.v52" : L = (Ext Uw) %"iw_1.v29";
    %"iw_1.v53" = %"v26" +p %"iw_1.v52";
    %"iw_1.v55" : L = (Ext Uw) %"iw_1.v48";
    %"iw_1.v56" : L = Shl %"iw_1.v55", #2;
    %"iw_1.v57" = %"iw_1.v53" +p %"iw_1.v56";
    %"chk11" : A = (Check 0 4 Read 1) %"iw_1.v57";
    %"iw_1.v58" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"iw_1.v63" : W = (Cmp Ne W) %"iw_1.v58", #0
    => br %"iw_1.v63" ? "iw_1.L59" : "iw_1.join";
  @"iw_1.L59":
    %"iw_1.v66" = %"v26" +p #16;
    %"chk12" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v66";
    %"iw_1.v67" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"iw_1.v71" : W = And %"v0", %"iw_1.v67";
    %"iw_1.v75" : L = (Ext Uw) %"iw_1.v58";
    %"iw_1.v76" = %"v26" +p %"iw_1.v75";
    %"iw_1.v78" : L = (Ext Uw) %"iw_1.v71";
    %"iw_1.v79" : L = Shl %"iw_1.v78", #2;
    %"iw_1.v80" = %"iw_1.v76" +p %"iw_1.v79";
    %"chk13" : A = (Check 0 4 Read 1) %"iw_1.v80";
    %"iw_1.v81" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"iw_1.v84" : W = Add %"v0", %"iw_1.v81"
    => goto "iw_1.join";
  @"iw_1.join" [%"v29" : W = phi("iw_1.L59" => %"iw_1.v84", "start" => %"v0", "iw_1.L16" => %"v0", "iw_1.L30" => %"v0")]:
    => ret %"v29"
} }.

Definition fn___GI___towupper : func :=
  ir_fn{ "export" "__GI___towupper"(W %"v0") -> (RClass W) {
  @"start":
    %"v3" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v3";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v7" = %"v6" +p #56;
    %"v11" = %"v7" +p #144;
    %"chk2" : A = (Check 0 4 Read 1) %"v11";
    %"v12" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v14" : L = (Ext Uw) %"v12";
    %"v16" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Check 0 8 Read 8) %"v17";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v20" = %"v19" +p #56;
    %"v22" : W = And %"v14", #65535;
    %"v23" : L = (Ext Sw) %"v22";
    %"v24" : L = Shl %"v23", #3;
    %"v25" = %"v20" +p %"v24";
    %"chk5" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 4 Read 1) %"v26";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_1.v11" : W = Shr %"v0", %"iw_1.v7";
    %"iw_1.v14" = %"v26" +p #4;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v14";
    %"iw_1.v15" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"iw_1.v21" : W = (Cmp Ult W) %"iw_1.v11", %"iw_1.v15"
    => br %"iw_1.v21" ? "iw_1.L16" : "iw_1.join";
  @"iw_1.L16":
    %"iw_1.v25" : W = Add %"iw_1.v11", #5;
    %"iw_1.v26" : L = (Ext Uw) %"iw_1.v25";
    %"iw_1.v27" : L = Shl %"iw_1.v26", #2;
    %"iw_1.v28" = %"v26" +p %"iw_1.v27";
    %"chk8" : A = (Check 0 4 Read 1) %"iw_1.v28";
    %"iw_1.v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"iw_1.v34" : W = (Cmp Ne W) %"iw_1.v29", #0
    => br %"iw_1.v34" ? "iw_1.L30" : "iw_1.join";
  @"iw_1.L30":
    %"iw_1.v37" = %"v26" +p #8;
    %"chk9" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v37";
    %"iw_1.v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"iw_1.v41" = %"v26" +p #12;
    %"chk10" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v41";
    %"iw_1.v42" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"iw_1.v46" : W = Shr %"v0", %"iw_1.v38";
    %"iw_1.v48" : W = And %"iw_1.v46", %"iw_1.v42";
    %"iw_1.v52" : L = (Ext Uw) %"iw_1.v29";
    %"iw_1.v53" = %"v26" +p %"iw_1.v52";
    %"iw_1.v55" : L = (Ext Uw) %"iw_1.v48";
    %"iw_1.v56" : L = Shl %"iw_1.v55", #2;
    %"iw_1.v57" = %"iw_1.v53" +p %"iw_1.v56";
    %"chk11" : A = (Check 0 4 Read 1) %"iw_1.v57";
    %"iw_1.v58" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"iw_1.v63" : W = (Cmp Ne W) %"iw_1.v58", #0
    => br %"iw_1.v63" ? "iw_1.L59" : "iw_1.join";
  @"iw_1.L59":
    %"iw_1.v66" = %"v26" +p #16;
    %"chk12" : A = (HalfCheck Upper 0 4 Read 1) %"chk6", %"iw_1.v66";
    %"iw_1.v67" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"iw_1.v71" : W = And %"v0", %"iw_1.v67";
    %"iw_1.v75" : L = (Ext Uw) %"iw_1.v58";
    %"iw_1.v76" = %"v26" +p %"iw_1.v75";
    %"iw_1.v78" : L = (Ext Uw) %"iw_1.v71";
    %"iw_1.v79" : L = Shl %"iw_1.v78", #2;
    %"iw_1.v80" = %"iw_1.v76" +p %"iw_1.v79";
    %"chk13" : A = (Check 0 4 Read 1) %"iw_1.v80";
    %"iw_1.v81" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"iw_1.v84" : W = Add %"v0", %"iw_1.v81"
    => goto "iw_1.join";
  @"iw_1.join" [%"v29" : W = phi("iw_1.L59" => %"iw_1.v84", "start" => %"v0", "iw_1.L16" => %"v0", "iw_1.L30" => %"v0")]:
    => ret %"v29"
} }.

Definition fn___iswprint : func :=
  ir_fn{ "export" "__iswprint"(W %"v0") -> (RClass W) {
  @"start":
    %"v7" : W = And %"v0", #4294967168;
    %"v8" : W = (Cmp Eq W) %"v7", #0
    => br %"v8" ? "iw_1.start" : "L4";
  @"iw_1.start":
    %"iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v12" : L = (Ext Sw) %"v0";
    %"v13" : L = Shl %"v12", #1;
    %"v14" = %"v10" +p %"v13";
    %"chk1" : A = (Check 0 2 Read 1) %"v14";
    %"v15" : W = (RawLoad (LdNarrow Uh) 0) %"chk1";
    %"v16" : W = And %"v15", #16384
    => ret %"v16";
  @"L4":
    %"v19" : P = Copy $"__libc_tsd_LOCALE";
    %"chk2" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (Check 0 8 Read 8) %"v20";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v23" = %"v22" +p #56;
    %"v27" = %"v23" +p #136;
    %"chk4" : A = (Check 0 4 Read 1) %"v27";
    %"v28" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v29" : W = Add %"v28", #6;
    %"v30" : L = (Ext Uw) %"v29";
    %"v32" : P = Copy $"__libc_tsd_LOCALE";
    %"chk5" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Read 8) %"v33";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v36" = %"v35" +p #56;
    %"v38" : W = And %"v30", #65535;
    %"v39" : L = (Ext Sw) %"v38";
    %"v40" : L = Shl %"v39", #3;
    %"v41" = %"v36" +p %"v40";
    %"chk7" : A = (Check 0 8 Read 8) %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 4 Read 1) %"v42";
    %"iw_2.v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"iw_2.v11" : W = Shr %"v0", %"iw_2.v7";
    %"iw_2.v14" = %"v42" +p #4;
    %"chk9" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"iw_2.v14";
    %"iw_2.v15" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"iw_2.v21" : W = (Cmp Ult W) %"iw_2.v11", %"iw_2.v15"
    => br %"iw_2.v21" ? "iw_2.L16" : "iw_2.join";
  @"iw_2.L16":
    %"iw_2.v25" : W = Add %"iw_2.v11", #5;
    %"iw_2.v26" : L = (Ext Uw) %"iw_2.v25";
    %"iw_2.v27" : L = Shl %"iw_2.v26", #2;
    %"iw_2.v28" = %"v42" +p %"iw_2.v27";
    %"chk10" : A = (Check 0 4 Read 1) %"iw_2.v28";
    %"iw_2.v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"iw_2.v34" : W = (Cmp Ne W) %"iw_2.v29", #0
    => br %"iw_2.v34" ? "iw_2.L30" : "iw_2.join";
  @"iw_2.L30":
    %"iw_2.v37" = %"v42" +p #8;
    %"chk11" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"iw_2.v37";
    %"iw_2.v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"iw_2.v41" = %"v42" +p #12;
    %"chk12" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"iw_2.v41";
    %"iw_2.v42" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"iw_2.v46" : W = Shr %"v0", %"iw_2.v38";
    %"iw_2.v48" : W = And %"iw_2.v46", %"iw_2.v42";
    %"iw_2.v52" : L = (Ext Uw) %"iw_2.v29";
    %"iw_2.v53" = %"v42" +p %"iw_2.v52";
    %"iw_2.v55" : L = (Ext Uw) %"iw_2.v48";
    %"iw_2.v56" : L = Shl %"iw_2.v55", #2;
    %"iw_2.v57" = %"iw_2.v53" +p %"iw_2.v56";
    %"chk13" : A = (Check 0 4 Read 1) %"iw_2.v57";
    %"iw_2.v58" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"iw_2.v63" : W = (Cmp Ne W) %"iw_2.v58", #0
    => br %"iw_2.v63" ? "iw_2.L59" : "iw_2.join";
  @"iw_2.L59":
    %"iw_2.v66" = %"v42" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"iw_2.v66";
    %"iw_2.v67" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"iw_2.v70" : W = Shr %"v0", #5;
    %"iw_2.v72" : W = And %"iw_2.v70", %"iw_2.v67";
    %"iw_2.v76" : L = (Ext Uw) %"iw_2.v58";
    %"iw_2.v77" = %"v42" +p %"iw_2.v76";
    %"iw_2.v79" : L = (Ext Uw) %"iw_2.v72";
    %"iw_2.v80" : L = Shl %"iw_2.v79", #2;
    %"iw_2.v81" = %"iw_2.v77" +p %"iw_2.v80";
    %"chk15" : A = (Check 0 4 Read 1) %"iw_2.v81";
    %"iw_2.v82" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"iw_2.v85" : W = And %"v0", #31;
    %"iw_2.v86" : W = Shr %"iw_2.v82", %"iw_2.v85";
    %"iw_2.v87" : W = And %"iw_2.v86", #1
    => goto "iw_2.join";
  @"iw_2.join" [%"v45" : W = phi("iw_2.L59" => %"iw_2.v87", "L4" => #0, "iw_2.L16" => #0, "iw_2.L30" => #0)]:
    => ret %"v45"
} }.

Definition item_iswprint : item :=
  (IAlias (a "iswprint") (a "export") (a "__iswprint")).

Definition item_towlower : item :=
  (IAlias (a "towlower") (a "weak") (a "__GI___towlower")).

Definition item_towupper : item :=
  (IAlias (a "towupper") (a "weak") (a "__GI___towupper")).

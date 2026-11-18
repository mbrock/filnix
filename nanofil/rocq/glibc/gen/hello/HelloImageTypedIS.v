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

Definition hello_image_fn___is_decorate_maps_enabled : func :=
  ir_fn{ "export" "__is_decorate_maps_enabled"() -> (RClass W) {
  @"start":
    %"v9" : P = (Alloc 4) #4;
    %"v0" : P = Copy $"glibc_setvmaname#decorate_maps";
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v1" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v29" : W = (Cmp Eq W) %"v1", #(-1)
    => br %"v29" ? "L4" : "L30";
  @"L4":
    call void $"__tunable_get_val"(W #26, P %"v9", P #0);
    %"chk1" : A = (Check 0 4 Read 1) %"v9";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v12" : W = (Cmp Ne W) %"v11", #0
    => br %"v12" ? "L13" : "L19";
  @"L13":
    %"v16" : P = Copy $"glibc_setvmaname#decorate_maps";
    %"chk2" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk2" + 0] <- #1
    => ret #1;
  @"L19":
    %"v22" : P = Copy $"glibc_setvmaname#decorate_maps";
    %"chk3" : A = (Check 0 4 Write 1) %"v22";
    store Ww [%"chk3" + 0] <- #0
    => ret #0;
  @"L24":
    => ret #0;
  @"L26":
    => ret #1;
  @"L30":
    %"v31" : W = (Cmp Eq W) %"v1", #0
    => br %"v31" ? poll "L24" : "L32";
  @"L32":
    %"v33" : W = (Cmp Eq W) %"v1", #1
    => br %"v33" ? poll "L26" : "L3";
  @"L3":
    => unreachable
} }.

Definition hello_image_fn___GI___isoc23_strtol : func :=
  ir_fn{ "export" "__GI___isoc23_strtol"(P %"v0", P %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v10" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v12" : L = $"__GI_____strtol_l_internal"(P %"v0", P %"v2", W %"v4", W #0, W #1, P %"v11")
    => ret %"v12"
} }.

Definition hello_image_fn___GI___isoc23_strtoul : func :=
  ir_fn{ "export" "__GI___isoc23_strtoul"(P %"v0", P %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v10" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v12" : L = $"__GI_____strtoul_l_internal"(P %"v0", P %"v2", W %"v4", W #0, W #1, P %"v11")
    => ret %"v12"
} }.

Definition hello_image_fn___isatty_nostatus : func :=
  ir_fn{ "export" "__isatty_nostatus"(W %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 4) #44;
    call %"v18" : W = $"zsys_ioctl"(W %"v0", W #2150388778, P %"v2");
    %"v19" : W = (Cmp Eq W) %"v18", #0
    => ret %"v19"
} }.

Definition hello_image_fn___iswprint : func :=
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

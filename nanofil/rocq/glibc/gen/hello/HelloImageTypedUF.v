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

Definition hello_image_fn___GI___uflow : func :=
  ir_fn{ "export" "__GI___uflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v24" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v26" : W = (Cmp Eq W) %"v25", #0
    => br %"v26" ? "L20" : "L22";
  @"L20":
    %"v28" = %"v0" +p #192;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v28";
    store Ww [%"chk1" + 0] <- #4294967295
    => goto "L22";
  @"L22":
    %"v31" = %"v0" +p #192;
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v55" : W = (Cmp Ne W) %"v32", #4294967295
    => br %"v55" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v64" = %"v0" +p #192;
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v66" : W = (Cmp Eq W) %"v65", #0
    => br %"v66" ? "L69" : "L62";
  @"L69":
    %"v83" = %"v0" +p #192;
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v85" : W = (Cmp Eq W) %"v84", #0
    => br %"v85" ? "L79" : "L81";
  @"L79":
    %"v87" = %"v0" +p #192;
    %"chk5" : A = (Renew 0 4 Write 1) %"chk0", %"v87";
    store Ww [%"chk5" + 0] <- #4294967295
    => goto "L81";
  @"L81":
    %"v90" = %"v0" +p #192;
    %"v91" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => goto "L62";
  @"L62":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v117" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v118" : W = And %"v117", #2048
    => br %"v118" ? "L113" : "L115";
  @"L113":
    call %"v123" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v125" : W = (Cmp Eq W) %"v123", #4294967295
    => br %"v125" ? "L119" : "L115";
  @"L119":
    => ret #4294967295;
  @"L115":
    %"v132" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v132";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v135" = %"v0" +p #16;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v135";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v137" : L = Ptoi %"v133";
    %"v138" : L = Ptoi %"v136";
    %"v139" : W = (Cmp Ult L) %"v137", %"v138"
    => br %"v139" ? "L128" : "L130";
  @"L128":
    %"v141" = %"v0" +p #8;
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v143" = %"v142" +p #1;
    %"chk11" : A = (Renew 0 8 Write 8) %"chk8", %"v141";
    store.ptr [%"chk11" + 0] <- %"v143";
    %"chk12" : A = (Check 0 1 Read 1) %"v142";
    %"v144" : W = (RawLoad (LdNarrow Ub) 0) %"chk12"
    => ret %"v144";
  @"L130":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk7", %"v0";
    %"v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v151" : W = And %"v150", #256
    => br %"v151" ? "L146" : "L148";
  @"L146":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v157" = %"v0" +p #8;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk8", %"v157";
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v160" = %"v0" +p #16;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk9", %"v160";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v162" : L = Ptoi %"v158";
    %"v163" : L = Ptoi %"v161";
    %"v164" : W = (Cmp Ult L) %"v162", %"v163"
    => br %"v164" ? "L153" : "L148";
  @"L153":
    %"v166" = %"v0" +p #8;
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v168" = %"v167" +p #1;
    %"chk17" : A = (Renew 0 8 Write 8) %"chk8", %"v166";
    store.ptr [%"chk17" + 0] <- %"v168";
    %"chk18" : A = (Check 0 1 Read 1) %"v167";
    %"v169" : W = (RawLoad (LdNarrow Ub) 0) %"chk18"
    => ret %"v169";
  @"L148":
    %"v175" = %"v0" +p #96;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v175";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v177" : L = Ptoi %"v176";
    %"v178" : L = Ptoi #0;
    %"v179" : W = (Cmp Ne L) %"v177", %"v178"
    => br %"v179" ? "L171" : "L172";
  @"L171":
    %"v185" = %"v0" +p #16;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk9", %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk20";
    call %"v187" : W = $"glibc_genops#save_for_backup"(P %"v0", P %"v186")
    => br %"v187" ? "L180" : "L173";
  @"L180":
    => ret #4294967295;
  @"L172":
    %"v194" = %"v0" +p #80;
    %"chk21" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v194";
    %"v195" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v196" : L = Ptoi %"v195";
    %"v198" : W = (Cmp Ne L) %"v196", %"v178"
    => br %"v198" ? "L190" : "L173";
  @"L190":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L173";
  @"L173":
    %"v201" = %"v0" +p #216;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_1.v4" : L = Ptoi %"v202";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v204" = %"v202" +p #40;
    %"chk23" : A = (Check 0 8 Read 8) %"v204";
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : F = CheckFunction %"v205";
    rawcall %"v207" : W = %"chk24"(P %"v0")
    => ret %"v207"
} }.

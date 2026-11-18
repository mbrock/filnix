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

Definition hello_image_fn___GI___wunderflow : func :=
  ir_fn{ "export" "__GI___wunderflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v8" : W = (Cmp Slt W) %"v7", #0
    => br %"v8" ? "L10" : "L9";
  @"L9":
    %"v12" = %"v0" +p #192;
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v14" : W = (Cmp Eq W) %"v13", #0
    => br %"v14" ? "L42" : "L10";
  @"L42":
    call %"v59" : W = $"_IO_fwide"(P %"v0", W #1);
    %"v61" : W = (Cmp Ne W) %"v59", #1
    => goto "L10";
  @"L10" [%"v65" : W = phi("start" => #1, "L9" => #0, "L42" => %"v61")]:
    => br %"v65" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v71" = %"v0" +p #192;
    %"chk2" : A = (Renew 0 4 Read 1) %"chk0", %"v71";
    %"v72" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v73" : W = (Cmp Eq W) %"v72", #0
    => br %"v73" ? "L99" : "L69";
  @"L99":
    call %"v116" : W = $"_IO_fwide"(P %"v0", W #1)
    => goto "L69";
  @"L69":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v123" : W = And %"v122", #2048
    => br %"v123" ? "L118" : "L120";
  @"L118":
    call %"v128" : W = $"__GI__IO_switch_to_wget_mode"(P %"v0");
    %"v130" : W = (Cmp Eq W) %"v128", #4294967295
    => br %"v130" ? "L124" : "L120";
  @"L124":
    => ret #4294967295;
  @"L120":
    %"v136" = %"v0" +p #160;
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v142" = %"v141" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v142";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v144" : L = Ptoi %"v138";
    %"v145" : L = Ptoi %"v143";
    %"v146" : W = (Cmp Ult L) %"v144", %"v145"
    => br %"v146" ? "L132" : "L134";
  @"L132":
    %"v148" = %"v0" +p #160;
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk9" : A = (Check 0 8 Read 8) %"v149";
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 4 Read 1) %"v150";
    %"v151" : W = (RawLoad (LdNarrow Sw) 0) %"chk10"
    => ret %"v151";
  @"L134":
    %"chk11" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v157" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"v158" : W = And %"v157", #256
    => br %"v158" ? "L153" : "L155";
  @"L153":
    call void $"__GI__IO_switch_to_main_wget_area"(P %"v0");
    %"v164" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk4", %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Check 0 8 Read 8) %"v165";
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v170" = %"v169" +p #8;
    %"chk15" : A = (Check 0 8 Read 8) %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v172" : L = Ptoi %"v166";
    %"v173" : L = Ptoi %"v171";
    %"v174" : W = (Cmp Ult L) %"v172", %"v173"
    => br %"v174" ? "L160" : "L155";
  @"L160":
    %"v176" = %"v0" +p #160;
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk17" : A = (Check 0 8 Read 8) %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Read 1) %"v178";
    %"v179" : W = (RawLoad (LdNarrow Sw) 0) %"chk18"
    => ret %"v179";
  @"L155":
    %"v185" = %"v0" +p #96;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v187" : L = Ptoi %"v186";
    %"v188" : L = Ptoi #0;
    %"v189" : W = (Cmp Ne L) %"v187", %"v188"
    => br %"v189" ? "L181" : "L182";
  @"L181":
    %"v195" = %"v0" +p #160;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk4", %"v195";
    %"v196" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v197" = %"v196" +p #8;
    %"chk21" : A = (Check 0 8 Read 8) %"v197";
    %"v198" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"v199" : W = $"glibc_wgenops#save_for_wbackup"(P %"v0", P %"v198")
    => br %"v199" ? "L190" : "L183";
  @"L190":
    => ret #4294967295;
  @"L182":
    %"v205" = %"v0" +p #160;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk4", %"v205";
    %"v206" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v207" = %"v206" +p #72;
    %"chk23" : A = (Check 0 8 Read 8) %"v207";
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v209" : L = Ptoi %"v208";
    %"v211" : W = (Cmp Ne L) %"v209", %"v188"
    => br %"v211" ? "L201" : "L183";
  @"L201":
    call void $"__GI__IO_free_wbackup_area"(P %"v0")
    => goto "L183";
  @"L183":
    %"v214" = %"v0" +p #216;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_1.v4" : L = Ptoi %"v215";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v217" = %"v215" +p #32;
    %"chk25" : A = (Check 0 8 Read 8) %"v217";
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : F = CheckFunction %"v218";
    rawcall %"v220" : W = %"chk26"(P %"v0")
    => ret %"v220"
} }.

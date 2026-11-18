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

Definition hi_fn___GI___underflow : func :=
  ir_fn{ "export" "__GI___underflow"(P %"v0") -> (RClass W) {
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
    %"chk11" : A = (Check 0 1 Read 1) %"v142";
    %"v143" : W = (RawLoad (LdNarrow Ub) 0) %"chk11"
    => ret %"v143";
  @"L130":
    %"chk12" : A = (Renew 0 4 Read 1) %"chk7", %"v0";
    %"v149" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v150" : W = And %"v149", #256
    => br %"v150" ? "L145" : "L147";
  @"L145":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v156" = %"v0" +p #8;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk8", %"v156";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v159" = %"v0" +p #16;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk9", %"v159";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v161" : L = Ptoi %"v157";
    %"v162" : L = Ptoi %"v160";
    %"v163" : W = (Cmp Ult L) %"v161", %"v162"
    => br %"v163" ? "L152" : "L147";
  @"L152":
    %"v165" = %"v0" +p #8;
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk16" : A = (Check 0 1 Read 1) %"v166";
    %"v167" : W = (RawLoad (LdNarrow Ub) 0) %"chk16"
    => ret %"v167";
  @"L147":
    %"v173" = %"v0" +p #96;
    %"chk17" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v175" : L = Ptoi %"v174";
    %"v176" : L = Ptoi #0;
    %"v177" : W = (Cmp Ne L) %"v175", %"v176"
    => br %"v177" ? "L169" : "L170";
  @"L169":
    %"v183" = %"v0" +p #16;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk9", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call %"v185" : W = $"glibc_genops#save_for_backup"(P %"v0", P %"v184")
    => br %"v185" ? "L178" : "L171";
  @"L178":
    => ret #4294967295;
  @"L170":
    %"v192" = %"v0" +p #80;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v192";
    %"v193" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v194" : L = Ptoi %"v193";
    %"v196" : W = (Cmp Ne L) %"v194", %"v176"
    => br %"v196" ? "L188" : "L171";
  @"L188":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L171";
  @"L171":
    %"v199" = %"v0" +p #216;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v199";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_1.v4" : L = Ptoi %"v200";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v202" = %"v200" +p #32;
    %"chk21" : A = (Check 0 8 Read 8) %"v202";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : F = CheckFunction %"v203";
    rawcall %"v205" : W = %"chk22"(P %"v0")
    => ret %"v205"
} }.

(** This file defines checked IR from glibc’s `stdio-common/printf-parsemb.os` object.
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

Definition fn___parse_one_specmb : func :=
  ir_fn{ "export" "__parse_one_specmb"(P %"v0", L %"v2", P %"v4", P %"v6", P %"v8") -> (RClass L) blocks ((app (app [ir_blk{ @"start":
    %"v1" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v1";
    store.ptr [%"chk0" + 0] <- %"v0";
    %"chk1" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" = %"v13" +p #1;
    %"chk2" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk2" + 0] <- %"v14";
    %"v16" = %"v4" +p #48;
    %"chk3" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk3" + 0] <- #4294967295;
    %"v19" = %"v4" +p #12;
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v19";
    %"v20" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v21" : W = And %"v20", #4294967287;
    store Ww [%"chk4" + 0] <- %"v21";
    %"v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v30" : W = And %"v29", #4294967279;
    store Ww [%"chk4" + 0] <- %"v30";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v39" : W = And %"v38", #4294967263;
    store Ww [%"chk4" + 0] <- %"v39";
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v48" : W = And %"v47", #4294967231;
    store Ww [%"chk4" + 0] <- %"v48";
    %"v56" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v57" : W = And %"v56", #4294967167;
    store Ww [%"chk4" + 0] <- %"v57";
    %"v65" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v66" : W = And %"v65", #4294965247;
    store Ww [%"chk4" + 0] <- %"v66";
    %"v74" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v75" : W = And %"v74", #4294967039;
    store Ww [%"chk4" + 0] <- %"v75";
    %"v82" = %"v4" +p #16;
    store Ww [%"chk4" + 4] <- #32;
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v87" : W = And %"v86", #4294966271;
    store Ww [%"chk4" + 0] <- %"v87";
    %"v95" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v96" : W = And %"v95", #4294963199;
    store Ww [%"chk4" + 0] <- %"v96";
    %"chk23" : A = (Check 0 1 Write 1) %"v8";
    store Wb [%"chk23" + 0] <- #0;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk25" : A = (Check 0 1 Read 1) %"v108";
    %"v109" : W = (RawLoad (LdNarrow Ub) 0) %"chk25";
    %"v111" : W = (Cmp Sge W) %"v109", #48
    => br %"v111" ? "L112" : "L113" };
  ir_blk{ @"L112":
    %"v115" : W = (Cmp Sle W) %"v109", #57
    => goto "L113" };
  ir_blk{ @"L113" [%"v117" : W = phi("start" => #0, "L112" => %"v115")]:
    => br %"v117" ? "L104" : "L160" };
  ir_blk{ @"L104":
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_1.v4" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk28" : A = (Check 0 1 Read 1) %"iw_1.v4";
    %"iw_1.v5" : W = (RawLoad (LdNarrow Ub) 0) %"chk28";
    %"iw_1.v6" : W = Sub %"iw_1.v5", #48
    => goto "iw_1.L7" };
  ir_blk{ @"iw_1.L7" [%"iw_1.pr.4" : W = phi("L104" => %"iw_1.v6", "iw_1.L23" => #4294967295, "iw_1.L43" => %"iw_1.v52", "iw_1.L29" => #4294967295, "iw_1.L8" => %"iw_1.pr.4")]:
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_1.v13" = %"iw_1.v12" +p #1;
    %"chk30" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk30" + 0] <- %"iw_1.v13";
    %"chk31" : A = (Check 0 1 Read 1) %"iw_1.v13";
    %"iw_1.v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk31";
    %"iw_1.v16" : W = (Cmp Sge W) %"iw_1.v14", #48
    => br %"iw_1.v16" ? "iw_1.L17" : "iw_1.L18" };
  ir_blk{ @"iw_1.L17":
    %"iw_1.v20" : W = (Cmp Sle W) %"iw_1.v14", #57
    => goto "iw_1.L18" };
  ir_blk{ @"iw_1.L18" [%"iw_1.v22" : W = phi("iw_1.L7" => #0, "iw_1.L17" => %"iw_1.v20")]:
    => br %"iw_1.v22" ? "iw_1.L8" : "iw_1.join" };
  ir_blk{ @"iw_1.L8":
    %"iw_1.v27" : W = (Cmp Sge W) %"iw_1.pr.4", #0
    => br %"iw_1.v27" ? "iw_1.L23" : poll "iw_1.L7" };
  ir_blk{ @"iw_1.L23":
    %"iw_1.v33" : W = (Cmp Sgt W) %"iw_1.pr.4", #214748364
    => br %"iw_1.v33" ? poll "iw_1.L7" : "iw_1.L29" };
  ir_blk{ @"iw_1.L29":
    %"chk32" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_1.v37" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Check 0 1 Read 1) %"iw_1.v37";
    %"iw_1.v38" : W = (RawLoad (LdNarrow Ub) 0) %"chk33";
    %"iw_1.v39" : W = Sub %"iw_1.v38", #48;
    %"iw_1.v41" : W = Mul %"iw_1.pr.4", #10;
    %"iw_1.v46" : W = Sub #2147483647, %"iw_1.v39";
    %"iw_1.v48" : W = (Cmp Slt W) %"iw_1.v46", %"iw_1.v41"
    => br %"iw_1.v48" ? poll "iw_1.L7" : "iw_1.L43" };
  ir_blk{ @"iw_1.L43":
    %"iw_1.v52" : W = Add %"iw_1.v41", %"iw_1.v39"
    => goto poll "iw_1.L7" };
  ir_blk{ @"iw_1.join":
    %"v125" : W = (Cmp Ne W) %"iw_1.pr.4", #0
    => br %"v125" ? "L126" : "L127" };
  ir_blk{ @"L126":
    %"chk34" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (Check 0 1 Read 1) %"v128";
    %"v129" : W = (RawLoad (LdNarrow Ub) 0) %"chk35";
    %"v130" : W = (Cmp Eq W) %"v129", #36
    => goto "L127" };
  ir_blk{ @"L127" [%"v132" : W = phi("iw_1.join" => #0, "L126" => %"v130")]:
    => br %"v132" ? "L121" : "L122" };
  ir_blk{ @"L121":
    %"chk36" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v134" = %"v133" +p #1;
    %"chk37" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk37" + 0] <- %"v134";
    %"v140" : W = (Cmp Ne W) %"iw_1.pr.4", #4294967295
    => br %"v140" ? "L135" : "L160" };
  ir_blk{ @"L135":
    %"v142" = %"v4" +p #48;
    %"v144" : W = Sub %"iw_1.pr.4", #1;
    %"chk38" : A = (Renew 0 4 Write 1) %"chk3", %"v142";
    store Ww [%"chk38" + 0] <- %"v144";
    %"chk39" : A = (Check 0 8 Read 1) %"v6";
    %"v150" : L = (RawLoad LdL 0) %"chk39";
    %"v152" : L = (Ext Uw) %"iw_1.pr.4";
    %"v153" : W = (Cmp Ugt L) %"v150", %"v152"
    => br %"v153" ? "L146" : "L148" };
  ir_blk{ @"L146":
    %"v155" : L = (RawLoad LdL 0) %"chk39"
    => goto "L148" };
  ir_blk{ @"L148" [%"v158" : L = phi("L146" => %"v155", "L135" => %"v152")]:
    %"chk41" : A = (Renew 0 8 Write 1) %"chk39", %"v6";
    store Wl [%"chk41" + 0] <- %"v158"
    => goto "L160" };
  ir_blk{ @"L122":
    %"chk42" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk42" + 0] <- %"v119"
    => goto "L160" };
  ir_blk{ @"L160":
    %"chk43" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"chk44" : A = (Check 0 1 Read 1) %"v163";
    %"v164" : W = (RawLoad (LdNarrow Ub) 0) %"chk44";
    %"v232" : W = (Cmp Slt W) %"v164", #43
    => br %"v232" ? "L233" : "L234" };
  ir_blk{ @"L167":
    %"v169" = %"v4" +p #12;
    %"chk45" : A = (Renew 0 4 Read 1) %"chk4", %"v169";
    %"v170" : W = (RawLoad (LdNarrow Uw) 0) %"chk45";
    %"v171" : W = And %"v170", #4294967279;
    %"v174" : W = Or %"v171", #16;
    %"chk46" : A = (Renew 0 4 Write 1) %"chk4", %"v169";
    store Ww [%"chk46" + 0] <- %"v174"
    => goto "L161" };
  ir_blk{ @"L177":
    %"v179" = %"v4" +p #12;
    %"chk47" : A = (Renew 0 4 Read 1) %"chk4", %"v179";
    %"v180" : W = (RawLoad (LdNarrow Uw) 0) %"chk47";
    %"v181" : W = And %"v180", #4294967231;
    %"v184" : W = Or %"v181", #64;
    %"chk48" : A = (Renew 0 4 Write 1) %"chk4", %"v179";
    store Ww [%"chk48" + 0] <- %"v184"
    => goto "L161" };
  ir_blk{ @"L187":
    %"v189" = %"v4" +p #12;
    %"chk49" : A = (Renew 0 4 Read 1) %"chk4", %"v189";
    %"v190" : W = (RawLoad (LdNarrow Uw) 0) %"chk49";
    %"v191" : W = And %"v190", #4294967263;
    %"v194" : W = Or %"v191", #32;
    %"chk50" : A = (Renew 0 4 Write 1) %"chk4", %"v189";
    store Ww [%"chk50" + 0] <- %"v194"
    => goto "L161" };
  ir_blk{ @"L197":
    %"v199" = %"v4" +p #12;
    %"chk51" : A = (Renew 0 4 Read 1) %"chk4", %"v199";
    %"v200" : W = (RawLoad (LdNarrow Uw) 0) %"chk51";
    %"v201" : W = And %"v200", #4294967287;
    %"v204" : W = Or %"v201", #8;
    %"chk52" : A = (Renew 0 4 Write 1) %"chk4", %"v199";
    store Ww [%"chk52" + 0] <- %"v204"
    => goto "L161" };
  ir_blk{ @"L207":
    %"v209" = %"v4" +p #16;
    %"chk53" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v209";
    store Ww [%"chk53" + 0] <- #48
    => goto "L161" };
  ir_blk{ @"L210":
    %"v212" = %"v4" +p #12;
    %"chk54" : A = (Renew 0 4 Read 1) %"chk4", %"v212";
    %"v213" : W = (RawLoad (LdNarrow Uw) 0) %"chk54";
    %"v214" : W = And %"v213", #4294967167;
    %"v217" : W = Or %"v214", #128;
    %"chk55" : A = (Renew 0 4 Write 1) %"chk4", %"v212";
    store Ww [%"chk55" + 0] <- %"v217"
    => goto "L161" };
  ir_blk{ @"L220":
    %"v222" = %"v4" +p #12;
    %"chk56" : A = (Renew 0 4 Read 1) %"chk4", %"v222";
    %"v223" : W = (RawLoad (LdNarrow Uw) 0) %"chk56";
    %"v224" : W = And %"v223", #4294965247;
    %"v227" : W = Or %"v224", #2048;
    %"chk57" : A = (Renew 0 4 Write 1) %"chk4", %"v222";
    store Ww [%"chk57" + 0] <- %"v227"
    => goto "L161" };
  ir_blk{ @"L233":
    %"v235" : W = (Cmp Eq W) %"v164", #32
    => br %"v235" ? poll "L167" : "L236" };
  ir_blk{ @"L236":
    %"v237" : W = (Cmp Eq W) %"v164", #35
    => br %"v237" ? poll "L197" : "L238" };
  ir_blk{ @"L238":
    %"v239" : W = (Cmp Eq W) %"v164", #39
    => br %"v239" ? poll "L210" : "L162" };
  ir_blk{ @"L234":
    %"v241" : W = (Cmp Eq W) %"v164", #43
    => br %"v241" ? poll "L177" : "L242" };
  ir_blk{ @"L242":
    %"v243" : W = (Cmp Eq W) %"v164", #45
    => br %"v243" ? poll "L187" : "L244" };
  ir_blk{ @"L244":
    %"v245" : W = (Cmp Eq W) %"v164", #48
    => br %"v245" ? poll "L207" : "L246" };
  ir_blk{ @"L246":
    %"v247" : W = (Cmp Eq W) %"v164", #73
    => br %"v247" ? poll "L220" : "L162" };
  ir_blk{ @"L161":
    %"chk58" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v249" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v250" = %"v249" +p #1;
    %"chk59" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk59" + 0] <- %"v250";
    %"chk60" : A = (Check 0 1 Read 1) %"v250";
    %"v251" : W = (RawLoad (LdNarrow Ub) 0) %"chk60"
    => br %"v251" ? poll "L160" : "L162" };
  ir_blk{ @"L162":
    %"v256" = %"v4" +p #12;
    %"chk61" : A = (Renew 0 4 Read 1) %"chk4", %"v256";
    %"v257" : W = (RawLoad (LdNarrow Uw) 0) %"chk61";
    %"v258" : W = Shl %"v257", #26;
    %"v259" : W = Shr %"v258", #31
    => br %"v259" ? "L252" : "L254" };
  ir_blk{ @"L252":
    %"v261" = %"v4" +p #16;
    %"chk62" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v261";
    store Ww [%"chk62" + 0] <- #32
    => goto "L254" };
  ir_blk{ @"L254":
    %"v263" = %"v4" +p #44;
    %"chk63" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v263";
    store Ww [%"chk63" + 0] <- #4294967295;
    %"v266" = %"v4" +p #4;
    %"chk64" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v266";
    store Ww [%"chk64" + 0] <- #0;
    %"chk65" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v270" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Check 0 1 Read 1) %"v270";
    %"v271" : W = (RawLoad (LdNarrow Ub) 0) %"chk66";
    %"v272" : W = (Cmp Eq W) %"v271", #42
    => br %"v272" ? "L267" : "L268" };
  ir_blk{ @"L267":
    %"v274" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v275" = %"v274" +p #1;
    %"chk68" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk68" + 0] <- %"v275";
    %"chk69" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v280" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"chk70" : A = (Check 0 1 Read 1) %"v280";
    %"v281" : W = (RawLoad (LdNarrow Ub) 0) %"chk70";
    %"v283" : W = (Cmp Sge W) %"v281", #48
    => br %"v283" ? "L284" : "L285" };
  ir_blk{ @"L284":
    %"v287" : W = (Cmp Sle W) %"v281", #57
    => goto "L285" };
  ir_blk{ @"L285" [%"v289" : W = phi("L267" => #0, "L284" => %"v287")]:
    => br %"v289" ? "iw_2.start" : "L278" };
  ir_blk{ @"iw_2.start":
    %"iw_2.v4" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"chk72" : A = (Check 0 1 Read 1) %"iw_2.v4";
    %"iw_2.v5" : W = (RawLoad (LdNarrow Ub) 0) %"chk72";
    %"iw_2.v6" : W = Sub %"iw_2.v5", #48
    => goto "iw_2.L7" };
  ir_blk{ @"iw_2.L7" [%"iw_2.pr.4" : W = phi("iw_2.start" => %"iw_2.v6", "iw_2.L23" => #4294967295, "iw_2.L43" => %"iw_2.v52", "iw_2.L29" => #4294967295, "iw_2.L8" => %"iw_2.pr.4")]:
    %"chk73" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"iw_2.v13" = %"iw_2.v12" +p #1;
    %"chk74" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk74" + 0] <- %"iw_2.v13";
    %"chk75" : A = (Check 0 1 Read 1) %"iw_2.v13";
    %"iw_2.v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk75";
    %"iw_2.v16" : W = (Cmp Sge W) %"iw_2.v14", #48
    => br %"iw_2.v16" ? "iw_2.L17" : "iw_2.L18" };
  ir_blk{ @"iw_2.L17":
    %"iw_2.v20" : W = (Cmp Sle W) %"iw_2.v14", #57
    => goto "iw_2.L18" };
  ir_blk{ @"iw_2.L18" [%"iw_2.v22" : W = phi("iw_2.L7" => #0, "iw_2.L17" => %"iw_2.v20")]:
    => br %"iw_2.v22" ? "iw_2.L8" : "iw_2.join" };
  ir_blk{ @"iw_2.L8":
    %"iw_2.v27" : W = (Cmp Sge W) %"iw_2.pr.4", #0
    => br %"iw_2.v27" ? "iw_2.L23" : poll "iw_2.L7" };
  ir_blk{ @"iw_2.L23":
    %"iw_2.v33" : W = (Cmp Sgt W) %"iw_2.pr.4", #214748364
    => br %"iw_2.v33" ? poll "iw_2.L7" : "iw_2.L29" };
  ir_blk{ @"iw_2.L29":
    %"chk76" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_2.v37" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"chk77" : A = (Check 0 1 Read 1) %"iw_2.v37";
    %"iw_2.v38" : W = (RawLoad (LdNarrow Ub) 0) %"chk77";
    %"iw_2.v39" : W = Sub %"iw_2.v38", #48;
    %"iw_2.v41" : W = Mul %"iw_2.pr.4", #10;
    %"iw_2.v46" : W = Sub #2147483647, %"iw_2.v39";
    %"iw_2.v48" : W = (Cmp Slt W) %"iw_2.v46", %"iw_2.v41"
    => br %"iw_2.v48" ? poll "iw_2.L7" : "iw_2.L43" };
  ir_blk{ @"iw_2.L43":
    %"iw_2.v52" : W = Add %"iw_2.v41", %"iw_2.v39"
    => goto poll "iw_2.L7" };
  ir_blk{ @"iw_2.join":
    %"v295" : W = (Cmp Ne W) %"iw_2.pr.4", #0
    => br %"v295" ? "L296" : "L297" };
  ir_blk{ @"L296":
    %"chk78" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"chk79" : A = (Check 0 1 Read 1) %"v298";
    %"v299" : W = (RawLoad (LdNarrow Ub) 0) %"chk79";
    %"v300" : W = (Cmp Eq W) %"v299", #36
    => goto "L297" };
  ir_blk{ @"L297" [%"v302" : W = phi("iw_2.join" => #0, "L296" => %"v300")]:
    => br %"v302" ? "L291" : "L278" };
  ir_blk{ @"L291":
    %"v308" : W = (Cmp Ne W) %"iw_2.pr.4", #4294967295
    => br %"v308" ? "L303" : "L305" };
  ir_blk{ @"L303":
    %"v310" = %"v4" +p #44;
    %"v312" : W = Sub %"iw_2.pr.4", #1;
    %"chk80" : A = (Renew 0 4 Write 1) %"chk63", %"v310";
    store Ww [%"chk80" + 0] <- %"v312";
    %"chk81" : A = (Check 0 8 Read 1) %"v6";
    %"v318" : L = (RawLoad LdL 0) %"chk81";
    %"v320" : L = (Ext Uw) %"iw_2.pr.4";
    %"v321" : W = (Cmp Ugt L) %"v318", %"v320"
    => br %"v321" ? "L314" : "L316" };
  ir_blk{ @"L314":
    %"v323" : L = (RawLoad LdL 0) %"chk81"
    => goto "L316" };
  ir_blk{ @"L316" [%"v326" : L = phi("L314" => %"v323", "L303" => %"v320")]:
    %"chk83" : A = (Renew 0 8 Write 1) %"chk81", %"v6";
    store Wl [%"chk83" + 0] <- %"v326"
    => goto "L305" }] [ir_blk{ @"L305":
    %"chk84" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"v328" = %"v327" +p #1;
    %"chk85" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk85" + 0] <- %"v328"
    => goto "L278" };
  ir_blk{ @"L278":
    %"v333" = %"v4" +p #44;
    %"chk86" : A = (Renew 0 4 Read 1) %"chk63", %"v333";
    %"v334" : W = (RawLoad (LdNarrow Sw) 0) %"chk86";
    %"v335" : W = (Cmp Slt W) %"v334", #0
    => br %"v335" ? "L329" : "L269" };
  ir_blk{ @"L329":
    %"v337" = %"v4" +p #44;
    %"v339" : L = Add %"v2", #1;
    %"chk87" : A = (Renew 0 4 Write 1) %"chk63", %"v337";
    store Ww [%"chk87" + 0] <- %"v2";
    %"chk88" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk88" + 0] <- %"v275"
    => goto "L269" };
  ir_blk{ @"L268":
    %"v347" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk90" : A = (Check 0 1 Read 1) %"v347";
    %"v348" : W = (RawLoad (LdNarrow Ub) 0) %"chk90";
    %"v350" : W = (Cmp Sge W) %"v348", #48
    => br %"v350" ? "L351" : "L352" };
  ir_blk{ @"L351":
    %"v354" : W = (Cmp Sle W) %"v348", #57
    => goto "L352" };
  ir_blk{ @"L352" [%"v356" : W = phi("L268" => #0, "L351" => %"v354")]:
    => br %"v356" ? "iw_3.start" : "L269" };
  ir_blk{ @"iw_3.start":
    %"iw_3.v4" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk92" : A = (Check 0 1 Read 1) %"iw_3.v4";
    %"iw_3.v5" : W = (RawLoad (LdNarrow Ub) 0) %"chk92";
    %"iw_3.v6" : W = Sub %"iw_3.v5", #48
    => goto "iw_3.L7" };
  ir_blk{ @"iw_3.L7" [%"iw_3.pr.4" : W = phi("iw_3.start" => %"iw_3.v6", "iw_3.L23" => #4294967295, "iw_3.L43" => %"iw_3.v52", "iw_3.L29" => #4294967295, "iw_3.L8" => %"iw_3.pr.4")]:
    %"chk93" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_3.v12" : P = (RawLoadPointer 0 load_effects) %"chk93";
    %"iw_3.v13" = %"iw_3.v12" +p #1;
    %"chk94" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk94" + 0] <- %"iw_3.v13";
    %"chk95" : A = (Check 0 1 Read 1) %"iw_3.v13";
    %"iw_3.v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk95";
    %"iw_3.v16" : W = (Cmp Sge W) %"iw_3.v14", #48
    => br %"iw_3.v16" ? "iw_3.L17" : "iw_3.L18" };
  ir_blk{ @"iw_3.L17":
    %"iw_3.v20" : W = (Cmp Sle W) %"iw_3.v14", #57
    => goto "iw_3.L18" };
  ir_blk{ @"iw_3.L18" [%"iw_3.v22" : W = phi("iw_3.L7" => #0, "iw_3.L17" => %"iw_3.v20")]:
    => br %"iw_3.v22" ? "iw_3.L8" : "iw_3.join" };
  ir_blk{ @"iw_3.L8":
    %"iw_3.v27" : W = (Cmp Sge W) %"iw_3.pr.4", #0
    => br %"iw_3.v27" ? "iw_3.L23" : poll "iw_3.L7" };
  ir_blk{ @"iw_3.L23":
    %"iw_3.v33" : W = (Cmp Sgt W) %"iw_3.pr.4", #214748364
    => br %"iw_3.v33" ? poll "iw_3.L7" : "iw_3.L29" };
  ir_blk{ @"iw_3.L29":
    %"chk96" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_3.v37" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"chk97" : A = (Check 0 1 Read 1) %"iw_3.v37";
    %"iw_3.v38" : W = (RawLoad (LdNarrow Ub) 0) %"chk97";
    %"iw_3.v39" : W = Sub %"iw_3.v38", #48;
    %"iw_3.v41" : W = Mul %"iw_3.pr.4", #10;
    %"iw_3.v46" : W = Sub #2147483647, %"iw_3.v39";
    %"iw_3.v48" : W = (Cmp Slt W) %"iw_3.v46", %"iw_3.v41"
    => br %"iw_3.v48" ? poll "iw_3.L7" : "iw_3.L43" };
  ir_blk{ @"iw_3.L43":
    %"iw_3.v52" : W = Add %"iw_3.v41", %"iw_3.v39"
    => goto poll "iw_3.L7" };
  ir_blk{ @"iw_3.join":
    %"v364" : W = (Cmp Ne W) %"iw_3.pr.4", #4294967295
    => br %"v364" ? "L359" : "L269" };
  ir_blk{ @"L359":
    %"v366" = %"v4" +p #4;
    %"chk98" : A = (Renew 0 4 Write 1) %"chk64", %"v366";
    store Ww [%"chk98" + 0] <- %"iw_3.pr.4"
    => goto "L269" };
  ir_blk{ @"L269" [%"pr.7" : L = phi("L329" => #1, "L278" => #0, "L359" => #0, "iw_3.join" => #0, "L352" => #0); %"pr.1" : L = phi("L329" => %"v339", "L278" => %"v2", "L359" => %"v2", "iw_3.join" => %"v2", "L352" => %"v2")]:
    %"v369" = %"v4" +p #40;
    %"chk99" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v369";
    store Ww [%"chk99" + 0] <- #4294967295;
    %"chk100" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v4";
    store Ww [%"chk100" + 0] <- #4294967295;
    %"chk101" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v376" : P = (RawLoadPointer 0 load_effects) %"chk101";
    %"chk102" : A = (Check 0 1 Read 1) %"v376";
    %"v377" : W = (RawLoad (LdNarrow Ub) 0) %"chk102";
    %"v378" : W = (Cmp Eq W) %"v377", #46
    => br %"v378" ? "L373" : "L375" };
  ir_blk{ @"L373":
    %"v379" : P = (RawLoadPointer 0 load_effects) %"chk101";
    %"v380" = %"v379" +p #1;
    %"chk104" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk104" + 0] <- %"v380";
    %"chk105" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v384" : P = (RawLoadPointer 0 load_effects) %"chk105";
    %"chk106" : A = (Check 0 1 Read 1) %"v384";
    %"v385" : W = (RawLoad (LdNarrow Ub) 0) %"chk106";
    %"v386" : W = (Cmp Eq W) %"v385", #42
    => br %"v386" ? "L381" : "L382" };
  ir_blk{ @"L381":
    %"v388" : P = (RawLoadPointer 0 load_effects) %"chk105";
    %"v389" = %"v388" +p #1;
    %"chk108" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk108" + 0] <- %"v389";
    %"chk109" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v394" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"chk110" : A = (Check 0 1 Read 1) %"v394";
    %"v395" : W = (RawLoad (LdNarrow Ub) 0) %"chk110";
    %"v397" : W = (Cmp Sge W) %"v395", #48
    => br %"v397" ? "L398" : "L399" };
  ir_blk{ @"L398":
    %"v401" : W = (Cmp Sle W) %"v395", #57
    => goto "L399" };
  ir_blk{ @"L399" [%"v403" : W = phi("L381" => #0, "L398" => %"v401")]:
    => br %"v403" ? "iw_4.start" : "L392" };
  ir_blk{ @"iw_4.start":
    %"iw_4.v4" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"chk112" : A = (Check 0 1 Read 1) %"iw_4.v4";
    %"iw_4.v5" : W = (RawLoad (LdNarrow Ub) 0) %"chk112";
    %"iw_4.v6" : W = Sub %"iw_4.v5", #48
    => goto "iw_4.L7" };
  ir_blk{ @"iw_4.L7" [%"iw_4.pr.4" : W = phi("iw_4.start" => %"iw_4.v6", "iw_4.L23" => #4294967295, "iw_4.L43" => %"iw_4.v52", "iw_4.L29" => #4294967295, "iw_4.L8" => %"iw_4.pr.4")]:
    %"chk113" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_4.v12" : P = (RawLoadPointer 0 load_effects) %"chk113";
    %"iw_4.v13" = %"iw_4.v12" +p #1;
    %"chk114" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk114" + 0] <- %"iw_4.v13";
    %"chk115" : A = (Check 0 1 Read 1) %"iw_4.v13";
    %"iw_4.v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk115";
    %"iw_4.v16" : W = (Cmp Sge W) %"iw_4.v14", #48
    => br %"iw_4.v16" ? "iw_4.L17" : "iw_4.L18" };
  ir_blk{ @"iw_4.L17":
    %"iw_4.v20" : W = (Cmp Sle W) %"iw_4.v14", #57
    => goto "iw_4.L18" };
  ir_blk{ @"iw_4.L18" [%"iw_4.v22" : W = phi("iw_4.L7" => #0, "iw_4.L17" => %"iw_4.v20")]:
    => br %"iw_4.v22" ? "iw_4.L8" : "iw_4.join" };
  ir_blk{ @"iw_4.L8":
    %"iw_4.v27" : W = (Cmp Sge W) %"iw_4.pr.4", #0
    => br %"iw_4.v27" ? "iw_4.L23" : poll "iw_4.L7" };
  ir_blk{ @"iw_4.L23":
    %"iw_4.v33" : W = (Cmp Sgt W) %"iw_4.pr.4", #214748364
    => br %"iw_4.v33" ? poll "iw_4.L7" : "iw_4.L29" };
  ir_blk{ @"iw_4.L29":
    %"chk116" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_4.v37" : P = (RawLoadPointer 0 load_effects) %"chk116";
    %"chk117" : A = (Check 0 1 Read 1) %"iw_4.v37";
    %"iw_4.v38" : W = (RawLoad (LdNarrow Ub) 0) %"chk117";
    %"iw_4.v39" : W = Sub %"iw_4.v38", #48;
    %"iw_4.v41" : W = Mul %"iw_4.pr.4", #10;
    %"iw_4.v46" : W = Sub #2147483647, %"iw_4.v39";
    %"iw_4.v48" : W = (Cmp Slt W) %"iw_4.v46", %"iw_4.v41"
    => br %"iw_4.v48" ? poll "iw_4.L7" : "iw_4.L43" };
  ir_blk{ @"iw_4.L43":
    %"iw_4.v52" : W = Add %"iw_4.v41", %"iw_4.v39"
    => goto poll "iw_4.L7" };
  ir_blk{ @"iw_4.join":
    %"v409" : W = (Cmp Ne W) %"iw_4.pr.4", #0
    => br %"v409" ? "L410" : "L411" };
  ir_blk{ @"L410":
    %"chk118" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v412" : P = (RawLoadPointer 0 load_effects) %"chk118";
    %"chk119" : A = (Check 0 1 Read 1) %"v412";
    %"v413" : W = (RawLoad (LdNarrow Ub) 0) %"chk119";
    %"v414" : W = (Cmp Eq W) %"v413", #36
    => goto "L411" };
  ir_blk{ @"L411" [%"v416" : W = phi("iw_4.join" => #0, "L410" => %"v414")]:
    => br %"v416" ? "L405" : "L392" };
  ir_blk{ @"L405":
    %"v422" : W = (Cmp Ne W) %"iw_4.pr.4", #4294967295
    => br %"v422" ? "L417" : "L419" };
  ir_blk{ @"L417":
    %"v424" = %"v4" +p #40;
    %"v426" : W = Sub %"iw_4.pr.4", #1;
    %"chk120" : A = (Renew 0 4 Write 1) %"chk99", %"v424";
    store Ww [%"chk120" + 0] <- %"v426";
    %"chk121" : A = (Check 0 8 Read 1) %"v6";
    %"v432" : L = (RawLoad LdL 0) %"chk121";
    %"v434" : L = (Ext Uw) %"iw_4.pr.4";
    %"v435" : W = (Cmp Ugt L) %"v432", %"v434"
    => br %"v435" ? "L428" : "L430" };
  ir_blk{ @"L428":
    %"v437" : L = (RawLoad LdL 0) %"chk121"
    => goto "L430" };
  ir_blk{ @"L430" [%"v440" : L = phi("L428" => %"v437", "L417" => %"v434")]:
    %"chk123" : A = (Renew 0 8 Write 1) %"chk121", %"v6";
    store Wl [%"chk123" + 0] <- %"v440"
    => goto "L419" };
  ir_blk{ @"L419":
    %"chk124" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v441" : P = (RawLoadPointer 0 load_effects) %"chk124";
    %"v442" = %"v441" +p #1;
    %"chk125" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk125" + 0] <- %"v442"
    => goto "L392" };
  ir_blk{ @"L392":
    %"v447" = %"v4" +p #40;
    %"chk126" : A = (Renew 0 4 Read 1) %"chk99", %"v447";
    %"v448" : W = (RawLoad (LdNarrow Sw) 0) %"chk126";
    %"v449" : W = (Cmp Slt W) %"v448", #0
    => br %"v449" ? "L443" : "L375" };
  ir_blk{ @"L443":
    %"v451" = %"v4" +p #40;
    %"v453" : L = Add %"pr.1", #1;
    %"chk127" : A = (Renew 0 4 Write 1) %"chk99", %"v451";
    store Ww [%"chk127" + 0] <- %"pr.1";
    %"v455" : L = Add %"pr.7", #1;
    %"chk128" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk128" + 0] <- %"v389"
    => goto "L375" };
  ir_blk{ @"L382":
    %"v461" : P = (RawLoadPointer 0 load_effects) %"chk105";
    %"chk130" : A = (Check 0 1 Read 1) %"v461";
    %"v462" : W = (RawLoad (LdNarrow Ub) 0) %"chk130";
    %"v464" : W = (Cmp Sge W) %"v462", #48
    => br %"v464" ? "L465" : "L466" };
  ir_blk{ @"L465":
    %"v468" : W = (Cmp Sle W) %"v462", #57
    => goto "L466" };
  ir_blk{ @"L466" [%"v470" : W = phi("L382" => #0, "L465" => %"v468")]:
    => br %"v470" ? "iw_5.start" : "L458" };
  ir_blk{ @"iw_5.start":
    %"iw_5.v4" : P = (RawLoadPointer 0 load_effects) %"chk105";
    %"chk132" : A = (Check 0 1 Read 1) %"iw_5.v4";
    %"iw_5.v5" : W = (RawLoad (LdNarrow Ub) 0) %"chk132";
    %"iw_5.v6" : W = Sub %"iw_5.v5", #48
    => goto "iw_5.L7" };
  ir_blk{ @"iw_5.L7" [%"iw_5.pr.4" : W = phi("iw_5.start" => %"iw_5.v6", "iw_5.L23" => #4294967295, "iw_5.L43" => %"iw_5.v52", "iw_5.L29" => #4294967295, "iw_5.L8" => %"iw_5.pr.4")]:
    %"chk133" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_5.v12" : P = (RawLoadPointer 0 load_effects) %"chk133";
    %"iw_5.v13" = %"iw_5.v12" +p #1;
    %"chk134" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk134" + 0] <- %"iw_5.v13";
    %"chk135" : A = (Check 0 1 Read 1) %"iw_5.v13";
    %"iw_5.v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk135";
    %"iw_5.v16" : W = (Cmp Sge W) %"iw_5.v14", #48
    => br %"iw_5.v16" ? "iw_5.L17" : "iw_5.L18" };
  ir_blk{ @"iw_5.L17":
    %"iw_5.v20" : W = (Cmp Sle W) %"iw_5.v14", #57
    => goto "iw_5.L18" };
  ir_blk{ @"iw_5.L18" [%"iw_5.v22" : W = phi("iw_5.L7" => #0, "iw_5.L17" => %"iw_5.v20")]:
    => br %"iw_5.v22" ? "iw_5.L8" : "iw_5.join" };
  ir_blk{ @"iw_5.L8":
    %"iw_5.v27" : W = (Cmp Sge W) %"iw_5.pr.4", #0
    => br %"iw_5.v27" ? "iw_5.L23" : poll "iw_5.L7" };
  ir_blk{ @"iw_5.L23":
    %"iw_5.v33" : W = (Cmp Sgt W) %"iw_5.pr.4", #214748364
    => br %"iw_5.v33" ? poll "iw_5.L7" : "iw_5.L29" };
  ir_blk{ @"iw_5.L29":
    %"chk136" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_5.v37" : P = (RawLoadPointer 0 load_effects) %"chk136";
    %"chk137" : A = (Check 0 1 Read 1) %"iw_5.v37";
    %"iw_5.v38" : W = (RawLoad (LdNarrow Ub) 0) %"chk137";
    %"iw_5.v39" : W = Sub %"iw_5.v38", #48;
    %"iw_5.v41" : W = Mul %"iw_5.pr.4", #10;
    %"iw_5.v46" : W = Sub #2147483647, %"iw_5.v39";
    %"iw_5.v48" : W = (Cmp Slt W) %"iw_5.v46", %"iw_5.v41"
    => br %"iw_5.v48" ? poll "iw_5.L7" : "iw_5.L43" };
  ir_blk{ @"iw_5.L43":
    %"iw_5.v52" : W = Add %"iw_5.v41", %"iw_5.v39"
    => goto poll "iw_5.L7" };
  ir_blk{ @"iw_5.join":
    %"v478" : W = (Cmp Ne W) %"iw_5.pr.4", #4294967295
    => br %"v478" ? "L473" : "L375" };
  ir_blk{ @"L473":
    %"chk138" : A = (Renew 0 4 Write 1) %"chk100", %"v4";
    store Ww [%"chk138" + 0] <- %"iw_5.pr.4"
    => goto "L375" };
  ir_blk{ @"L458":
    %"chk139" : A = (Renew 0 4 Write 1) %"chk100", %"v4";
    store Ww [%"chk139" + 0] <- #0
    => goto "L375" };
  ir_blk{ @"L375" [%"pr.9" : L = phi("L443" => %"v455", "L392" => %"pr.7", "L458" => %"pr.7", "L473" => %"pr.7", "iw_5.join" => %"pr.7", "L269" => %"pr.7"); %"pr.3" : L = phi("L443" => %"v453", "L392" => %"pr.1", "L458" => %"pr.1", "L473" => %"pr.1", "iw_5.join" => %"pr.1", "L269" => %"pr.1")]:
    %"v483" = %"v4" +p #12;
    %"chk140" : A = (Renew 0 4 Read 1) %"chk4", %"v483";
    %"v484" : W = (RawLoad (LdNarrow Uw) 0) %"chk140";
    %"v485" : W = And %"v484", #4294967294;
    %"chk141" : A = (Renew 0 4 Write 1) %"chk4", %"v483";
    store Ww [%"chk141" + 0] <- %"v485";
    %"v492" : W = (RawLoad (LdNarrow Uw) 0) %"chk141";
    %"v493" : W = And %"v492", #4294967293;
    store Ww [%"chk141" + 0] <- %"v493";
    %"v501" : W = (RawLoad (LdNarrow Uw) 0) %"chk141";
    %"v502" : W = And %"v501", #4294967291;
    store Ww [%"chk141" + 0] <- %"v502";
    %"v510" : W = (RawLoad (LdNarrow Uw) 0) %"chk141";
    %"v511" : W = And %"v510", #4294966783;
    store Ww [%"chk141" + 0] <- %"v511";
    %"v518" = %"v4" +p #14;
    store Wh [%"chk141" + 2] <- #0;
    %"v522" : P = Copy $"__printf_modifier_table";
    %"chk149" : A = (Check 0 8 Read 8) %"v522";
    %"v523" : P = (RawLoadPointer 0 load_effects) %"chk149";
    %"v524" : L = Ptoi %"v523";
    %"v525" : L = Ptoi #0;
    %"v526" : W = (Cmp Eq L) %"v524", %"v525"
    => br %"v526" ? "L530" : "L529" };
  ir_blk{ @"L529":
    %"v531" : P = Copy $"__printf_modifier_table";
    %"chk150" : A = (Check 0 8 Read 8) %"v531";
    %"v532" : P = (RawLoadPointer 0 load_effects) %"chk150";
    %"chk151" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v533" : P = (RawLoadPointer 0 load_effects) %"chk151";
    %"chk152" : A = (Check 0 1 Read 1) %"v533";
    %"v534" : W = (RawLoad (LdNarrow Ub) 0) %"chk152";
    %"v535" : L = (Ext Uw) %"v534";
    %"v536" : L = Shl %"v535", #3;
    %"v537" = %"v532" +p %"v536";
    %"chk153" : A = (Check 0 8 Read 8) %"v537";
    %"v538" : P = (RawLoadPointer 0 load_effects) %"chk153";
    %"v539" : L = Ptoi %"v538";
    %"v541" : W = (Cmp Eq L) %"v539", %"v525"
    => goto "L530" };
  ir_blk{ @"L530" [%"v543" : W = phi("L375" => #1, "L529" => %"v541")]:
    => br %"v543" ? "L545" : "L544" }]) (app [ir_blk{ @"L544":
    call %"v547" : W = $"__handle_registered_modifier_mb"(P %"v1", P %"v4");
    %"v548" : W = (Cmp Ne W) %"v547", #0
    => goto "L545" };
  ir_blk{ @"L545" [%"v550" : W = phi("L530" => #1, "L544" => %"v548")]:
    => br %"v550" ? "L519" : "L521" };
  ir_blk{ @"L519":
    %"chk154" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v551" : P = (RawLoadPointer 0 load_effects) %"chk154";
    %"v552" = %"v551" +p #1;
    %"chk155" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk155" + 0] <- %"v552";
    %"chk156" : A = (Check 0 1 Read 1) %"v551";
    %"v553" : W = (RawLoad (LdNarrow Ub) 0) %"chk156";
    %"v752" : W = (Cmp Slt W) %"v553", #108
    => br %"v752" ? "L753" : "L754" };
  ir_blk{ @"L556":
    %"chk157" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v560" : P = (RawLoadPointer 0 load_effects) %"chk157";
    %"chk158" : A = (Check 0 1 Read 1) %"v560";
    %"v561" : W = (RawLoad (LdNarrow Ub) 0) %"chk158";
    %"v562" : W = (Cmp Ne W) %"v561", #104
    => br %"v562" ? "L557" : "L558" };
  ir_blk{ @"L557":
    %"v564" = %"v4" +p #12;
    %"chk159" : A = (Renew 0 4 Read 1) %"chk4", %"v564";
    %"v565" : W = (RawLoad (LdNarrow Uw) 0) %"chk159";
    %"v566" : W = And %"v565", #4294967293;
    %"v569" : W = Or %"v566", #2;
    %"chk160" : A = (Renew 0 4 Write 1) %"chk4", %"v564";
    store Ww [%"chk160" + 0] <- %"v569"
    => goto "L521" };
  ir_blk{ @"L558":
    %"v572" : P = (RawLoadPointer 0 load_effects) %"chk157";
    %"v573" = %"v572" +p #1;
    %"chk162" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk162" + 0] <- %"v573";
    %"v575" = %"v4" +p #12;
    %"chk163" : A = (Renew 0 4 Read 1) %"chk4", %"v575";
    %"v576" : W = (RawLoad (LdNarrow Uw) 0) %"chk163";
    %"v577" : W = And %"v576", #4294966783;
    %"v580" : W = Or %"v577", #512;
    %"chk164" : A = (Renew 0 4 Write 1) %"chk4", %"v575";
    store Ww [%"chk164" + 0] <- %"v580"
    => goto "L521" };
  ir_blk{ @"L583":
    %"v585" = %"v4" +p #12;
    %"chk165" : A = (Renew 0 4 Read 1) %"chk4", %"v585";
    %"v586" : W = (RawLoad (LdNarrow Uw) 0) %"chk165";
    %"v587" : W = And %"v586", #4294967291;
    %"v590" : W = Or %"v587", #4;
    %"chk166" : A = (Renew 0 4 Write 1) %"chk4", %"v585";
    store Ww [%"chk166" + 0] <- %"v590";
    %"chk167" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v596" : P = (RawLoadPointer 0 load_effects) %"chk167";
    %"chk168" : A = (Check 0 1 Read 1) %"v596";
    %"v597" : W = (RawLoad (LdNarrow Ub) 0) %"chk168";
    %"v598" : W = (Cmp Ne W) %"v597", #108
    => br %"v598" ? "L521" : "L595" };
  ir_blk{ @"L595":
    %"v600" : P = (RawLoadPointer 0 load_effects) %"chk167";
    %"v601" = %"v600" +p #1;
    %"chk170" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk170" + 0] <- %"v601"
    => goto "L603" };
  ir_blk{ @"L603":
    %"v605" = %"v4" +p #12;
    %"chk171" : A = (Renew 0 4 Read 1) %"chk4", %"v605";
    %"v606" : W = (RawLoad (LdNarrow Uw) 0) %"chk171";
    %"v607" : W = And %"v606", #4294967294;
    %"v609" : W = Or %"v607", #1;
    %"chk172" : A = (Renew 0 4 Write 1) %"chk4", %"v605";
    store Ww [%"chk172" + 0] <- %"v609"
    => goto "L521" };
  ir_blk{ @"L613":
    %"v615" = %"v4" +p #12;
    %"chk173" : A = (Renew 0 4 Read 1) %"chk4", %"v615";
    %"v617" : W = (RawLoad (LdNarrow Uw) 0) %"chk173";
    %"v618" : W = And %"v617", #4294967291;
    %"v621" : W = Or %"v618", #4;
    %"chk174" : A = (Renew 0 4 Write 1) %"chk4", %"v615";
    store Ww [%"chk174" + 0] <- %"v621"
    => goto "L521" };
  ir_blk{ @"L624":
    %"v626" = %"v4" +p #12;
    %"chk175" : A = (Renew 0 4 Read 1) %"chk4", %"v626";
    %"v628" : W = (RawLoad (LdNarrow Uw) 0) %"chk175";
    %"v629" : W = And %"v628", #4294967291;
    %"v632" : W = Or %"v629", #4;
    %"chk176" : A = (Renew 0 4 Write 1) %"chk4", %"v626";
    store Ww [%"chk176" + 0] <- %"v632"
    => goto "L521" };
  ir_blk{ @"L635":
    %"v637" = %"v4" +p #12;
    %"chk177" : A = (Renew 0 4 Read 1) %"chk4", %"v637";
    %"v639" : W = (RawLoad (LdNarrow Uw) 0) %"chk177";
    %"v640" : W = And %"v639", #4294967291;
    %"v643" : W = Or %"v640", #4;
    %"chk178" : A = (Renew 0 4 Write 1) %"chk4", %"v637";
    store Ww [%"chk178" + 0] <- %"v643"
    => goto "L521" };
  ir_blk{ @"L646":
    %"chk179" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v651" : P = (RawLoadPointer 0 load_effects) %"chk179";
    %"chk180" : A = (Check 0 1 Read 1) %"v651";
    %"v652" : W = (RawLoad (LdNarrow Ub) 0) %"chk180";
    %"v653" : W = (Cmp Eq W) %"v652", #102
    => br %"v653" ? "L648" : "L650" };
  ir_blk{ @"L648":
    %"v654" : P = (RawLoadPointer 0 load_effects) %"chk179";
    %"v655" = %"v654" +p #1;
    %"chk182" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk182" + 0] <- %"v655"
    => goto "L650" };
  ir_blk{ @"L650" [%"pr.12" : W = phi("L648" => #1, "L646" => #0)]:
    %"chk183" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v662" : P = (RawLoadPointer 0 load_effects) %"chk183";
    %"chk184" : A = (Check 0 1 Read 1) %"v662";
    %"v663" : W = (RawLoad (LdNarrow Ub) 0) %"chk184";
    %"v665" : W = (Cmp Sge W) %"v663", #48
    => br %"v665" ? "L666" : "L667" };
  ir_blk{ @"L666":
    %"v669" : W = (Cmp Sle W) %"v663", #57
    => goto "L667" };
  ir_blk{ @"L667" [%"v671" : W = phi("L650" => #0, "L666" => %"v669")]:
    => br %"v671" ? "iw_6.start" : "L660" };
  ir_blk{ @"iw_6.start":
    %"iw_6.v4" : P = (RawLoadPointer 0 load_effects) %"chk183";
    %"chk186" : A = (Check 0 1 Read 1) %"iw_6.v4";
    %"iw_6.v5" : W = (RawLoad (LdNarrow Ub) 0) %"chk186";
    %"iw_6.v6" : W = Sub %"iw_6.v5", #48
    => goto "iw_6.L7" };
  ir_blk{ @"iw_6.L7" [%"iw_6.pr.4" : W = phi("iw_6.start" => %"iw_6.v6", "iw_6.L23" => #4294967295, "iw_6.L43" => %"iw_6.v52", "iw_6.L29" => #4294967295, "iw_6.L8" => %"iw_6.pr.4")]:
    %"chk187" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_6.v12" : P = (RawLoadPointer 0 load_effects) %"chk187";
    %"iw_6.v13" = %"iw_6.v12" +p #1;
    %"chk188" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk188" + 0] <- %"iw_6.v13";
    %"chk189" : A = (Check 0 1 Read 1) %"iw_6.v13";
    %"iw_6.v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk189";
    %"iw_6.v16" : W = (Cmp Sge W) %"iw_6.v14", #48
    => br %"iw_6.v16" ? "iw_6.L17" : "iw_6.L18" };
  ir_blk{ @"iw_6.L17":
    %"iw_6.v20" : W = (Cmp Sle W) %"iw_6.v14", #57
    => goto "iw_6.L18" };
  ir_blk{ @"iw_6.L18" [%"iw_6.v22" : W = phi("iw_6.L7" => #0, "iw_6.L17" => %"iw_6.v20")]:
    => br %"iw_6.v22" ? "iw_6.L8" : "L660" };
  ir_blk{ @"iw_6.L8":
    %"iw_6.v27" : W = (Cmp Sge W) %"iw_6.pr.4", #0
    => br %"iw_6.v27" ? "iw_6.L23" : poll "iw_6.L7" };
  ir_blk{ @"iw_6.L23":
    %"iw_6.v33" : W = (Cmp Sgt W) %"iw_6.pr.4", #214748364
    => br %"iw_6.v33" ? poll "iw_6.L7" : "iw_6.L29" };
  ir_blk{ @"iw_6.L29":
    %"chk190" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"iw_6.v37" : P = (RawLoadPointer 0 load_effects) %"chk190";
    %"chk191" : A = (Check 0 1 Read 1) %"iw_6.v37";
    %"iw_6.v38" : W = (RawLoad (LdNarrow Ub) 0) %"chk191";
    %"iw_6.v39" : W = Sub %"iw_6.v38", #48;
    %"iw_6.v41" : W = Mul %"iw_6.pr.4", #10;
    %"iw_6.v46" : W = Sub #2147483647, %"iw_6.v39";
    %"iw_6.v48" : W = (Cmp Slt W) %"iw_6.v46", %"iw_6.v41"
    => br %"iw_6.v48" ? poll "iw_6.L7" : "iw_6.L43" };
  ir_blk{ @"iw_6.L43":
    %"iw_6.v52" : W = Add %"iw_6.v41", %"iw_6.v39"
    => goto poll "iw_6.L7" };
  ir_blk{ @"L660" [%"pr.13" : W = phi("iw_6.L18" => %"iw_6.pr.4", "L667" => #0)]:
    => br %"pr.12" ? "L678" : "L675" };
  ir_blk{ @"L678":
    %"v685" : W = (Cmp Eq W) %"pr.13", #8
    => br %"v685" ? "L675" : "L686" };
  ir_blk{ @"L686":
    %"v687" : W = (Cmp Eq W) %"pr.13", #16
    => br %"v687" ? "L675" : "L688" };
  ir_blk{ @"L688":
    %"v689" : W = (Cmp Eq W) %"pr.13", #32
    => br %"v689" ? "L675" : "L690" };
  ir_blk{ @"L690":
    %"v691" : W = (Cmp Eq W) %"pr.13", #64
    => br %"v691" ? "L675" : "L692" };
  ir_blk{ @"L692":
    => goto "L675" };
  ir_blk{ @"L675" [%"pr.14" : W = phi("L692" => %"pr.13", "L678" => #8, "L686" => #64, "L688" => #64, "L690" => #64, "L660" => %"pr.13")]:
    %"v740" : W = (Cmp Eq W) %"pr.14", #8
    => br %"v740" ? "L696" : "L741" };
  ir_blk{ @"L696":
    %"v698" = %"v4" +p #12;
    %"chk192" : A = (Renew 0 4 Read 1) %"chk4", %"v698";
    %"v699" : W = (RawLoad (LdNarrow Uw) 0) %"chk192";
    %"v700" : W = And %"v699", #4294966783;
    %"v703" : W = Or %"v700", #512;
    %"chk193" : A = (Renew 0 4 Write 1) %"chk4", %"v698";
    store Ww [%"chk193" + 0] <- %"v703"
    => goto "L521" };
  ir_blk{ @"L706":
    %"v708" = %"v4" +p #12;
    %"chk194" : A = (Renew 0 4 Read 1) %"chk4", %"v708";
    %"v709" : W = (RawLoad (LdNarrow Uw) 0) %"chk194";
    %"v710" : W = And %"v709", #4294967293;
    %"v713" : W = Or %"v710", #2;
    %"chk195" : A = (Renew 0 4 Write 1) %"chk4", %"v708";
    store Ww [%"chk195" + 0] <- %"v713"
    => goto "L521" };
  ir_blk{ @"L717":
    %"v719" = %"v4" +p #12;
    %"chk196" : A = (Renew 0 4 Read 1) %"chk4", %"v719";
    %"v720" : W = (RawLoad (LdNarrow Uw) 0) %"chk196";
    %"v721" : W = And %"v720", #4294967294;
    %"v723" : W = Or %"v721", #1;
    %"chk197" : A = (Renew 0 4 Write 1) %"chk4", %"v719";
    store Ww [%"chk197" + 0] <- %"v723";
    %"v728" : W = (RawLoad (LdNarrow Uw) 0) %"chk197";
    %"v729" : W = And %"v728", #4294967291;
    %"v732" : W = Or %"v729", #4;
    store Ww [%"chk197" + 0] <- %"v732"
    => goto "L521" };
  ir_blk{ @"L735":
    %"v736" : P = Copy $"__libc_errno";
    %"chk200" : A = (Check 0 4 Write 1) %"v736";
    store Ww [%"chk200" + 0] <- #22;
    %"chk201" : A = (Renew 0 1 Write 1) %"chk23", %"v8";
    store Wb [%"chk201" + 0] <- #1
    => goto "L521" };
  ir_blk{ @"L741":
    %"v742" : W = (Cmp Eq W) %"pr.14", #16
    => br %"v742" ? poll "L706" : "L743" };
  ir_blk{ @"L743":
    %"v744" : W = (Cmp Eq W) %"pr.14", #32
    => br %"v744" ? "L521" : "L745" };
  ir_blk{ @"L745":
    %"v746" : W = (Cmp Eq W) %"pr.14", #64
    => br %"v746" ? poll "L717" : poll "L735" };
  ir_blk{ @"L748":
    %"chk202" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v749" : P = (RawLoadPointer 0 load_effects) %"chk202";
    (Flight (a "v750") Sub [(FAddress (t "v749")); (FValue (Const 1))] (LowerOf (t "v749")));
    %"chk203" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk203" + 0] <- %"v750"
    => goto "L521" };
  ir_blk{ @"L753":
    %"v755" : W = (Cmp Eq W) %"v553", #76
    => br %"v755" ? poll "L603" : "L756" };
  ir_blk{ @"L756":
    %"v757" : W = (Cmp Eq W) %"v553", #90
    => br %"v757" ? poll "L613" : "L758" };
  ir_blk{ @"L758":
    %"v759" : W = (Cmp Eq W) %"v553", #104
    => br %"v759" ? poll "L556" : "L760" };
  ir_blk{ @"L760":
    %"v761" : W = (Cmp Eq W) %"v553", #106
    => br %"v761" ? poll "L635" : poll "L748" };
  ir_blk{ @"L754":
    %"v763" : W = (Cmp Slt W) %"v553", #116
    => br %"v763" ? "L764" : "L765" };
  ir_blk{ @"L764":
    %"v766" : W = (Cmp Eq W) %"v553", #108
    => br %"v766" ? poll "L583" : "L767" };
  ir_blk{ @"L767":
    %"v768" : W = (Cmp Eq W) %"v553", #113
    => br %"v768" ? poll "L603" : poll "L748" };
  ir_blk{ @"L765":
    %"v770" : W = (Cmp Eq W) %"v553", #116
    => br %"v770" ? poll "L624" : "L771" };
  ir_blk{ @"L771":
    %"v772" : W = (Cmp Eq W) %"v553", #119
    => br %"v772" ? poll "L646" : "L773" };
  ir_blk{ @"L773":
    %"v774" : W = (Cmp Eq W) %"v553", #122
    => br %"v774" ? poll "L613" : poll "L748" };
  ir_blk{ @"L521":
    %"v777" = %"v4" +p #8;
    %"chk204" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v778" : P = (RawLoadPointer 0 load_effects) %"chk204";
    %"v779" = %"v778" +p #1;
    %"chk205" : A = (Renew 0 8 Write 8) %"chk0", %"v1";
    store.ptr [%"chk205" + 0] <- %"v779";
    %"chk206" : A = (Check 0 1 Read 1) %"v778";
    %"v780" : W = (RawLoad (LdNarrow Ub) 0) %"chk206";
    %"chk207" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v777";
    store Ww [%"chk207" + 0] <- %"v780";
    %"v782" = %"v4" +p #64;
    %"chk208" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v782";
    store Ww [%"chk208" + 0] <- #4294967295;
    %"v787" : P = Copy $"__printf_function_table";
    %"chk209" : A = (Check 0 8 Read 8) %"v787";
    %"v788" : P = (RawLoadPointer 0 load_effects) %"chk209";
    %"v789" : L = Ptoi %"v788";
    %"v791" : W = (Cmp Eq L) %"v789", %"v525"
    => br %"v791" ? "L795" : "L794" };
  ir_blk{ @"L794":
    %"v797" = %"v4" +p #8;
    %"chk210" : A = (Renew 0 4 Read 1) %"chk207", %"v797";
    %"v798" : W = (RawLoad (LdNarrow Sw) 0) %"chk210";
    %"v801" : W = (Cmp Sgt W) %"v798", #255
    => goto "L795" };
  ir_blk{ @"L795" [%"v803" : W = phi("L521" => #1, "L794" => %"v801")]:
    => br %"v803" ? "L805" : "L804" };
  ir_blk{ @"L804":
    %"v806" : P = Copy $"__printf_arginfo_table";
    %"chk211" : A = (Check 0 8 Read 8) %"v806";
    %"v807" : P = (RawLoadPointer 0 load_effects) %"chk211";
    %"v809" = %"v4" +p #8;
    %"chk212" : A = (Renew 0 4 Read 1) %"chk207", %"v809";
    %"v810" : W = (RawLoad (LdNarrow Sw) 0) %"chk212";
    %"v811" : L = (Ext Sw) %"v810";
    %"v812" : L = Shl %"v811", #3;
    %"v813" = %"v807" +p %"v812";
    %"chk213" : A = (Check 0 8 Read 8) %"v813";
    %"v814" : P = (RawLoadPointer 0 load_effects) %"chk213";
    %"v815" : L = Ptoi %"v814";
    %"v817" : W = (Cmp Eq L) %"v815", %"v525"
    => goto "L805" };
  ir_blk{ @"L805" [%"v819" : W = phi("L795" => #1, "L804" => %"v817")]:
    => br %"v819" ? "L821" : "L820" };
  ir_blk{ @"L820":
    %"v823" = %"v4" +p #56;
    %"v824" : P = Copy $"__printf_arginfo_table";
    %"chk214" : A = (Check 0 8 Read 8) %"v824";
    %"v825" : P = (RawLoadPointer 0 load_effects) %"chk214";
    %"v827" = %"v4" +p #8;
    %"chk215" : A = (Renew 0 4 Read 1) %"chk207", %"v827";
    %"v828" : W = (RawLoad (LdNarrow Sw) 0) %"chk215";
    %"v829" : L = (Ext Sw) %"v828";
    %"v830" : L = Shl %"v829", #3;
    %"v831" = %"v825" +p %"v830";
    %"chk216" : A = (Check 0 8 Read 8) %"v831";
    %"v832" : P = (RawLoadPointer 0 load_effects) %"chk216";
    %"v835" = %"v4" +p #52;
    %"v837" = %"v4" +p #64;
    %"chk217" : F = CheckFunction %"v832";
    rawcall %"v838" : W = %"chk217"(P %"v4", L #1, P %"v835", P %"v837");
    %"v839" : L = (Ext Sw) %"v838";
    %"chk218" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v823";
    store Wl [%"chk218" + 0] <- %"v839";
    %"v840" : W = (Cmp Slt W) %"v839", #0
    => goto "L821" }] [ir_blk{ @"L821" [%"v842" : W = phi("L805" => #1, "L820" => %"v840")]:
    => br %"v842" ? "L784" : "L786" };
  ir_blk{ @"L784":
    %"v844" = %"v4" +p #56;
    %"chk219" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v844";
    store Wl [%"chk219" + 0] <- #1;
    %"v846" = %"v4" +p #8;
    %"chk220" : A = (Renew 0 4 Read 1) %"chk207", %"v846";
    %"v847" : W = (RawLoad (LdNarrow Sw) 0) %"chk220";
    %"v941" : W = (Cmp Slt W) %"v847", #100
    => br %"v941" ? "L942" : "L943" };
  ir_blk{ @"L857":
    %"v862" = %"v4" +p #12;
    %"chk221" : A = (Renew 0 4 Read 1) %"chk4", %"v862";
    %"v863" : W = (RawLoad (LdNarrow Uw) 0) %"chk221";
    %"v864" : W = Shl %"v863", #29;
    %"v865" : W = Shr %"v864", #31
    => br %"v865" ? "L858" : "L859" };
  ir_blk{ @"L858":
    %"v867" = %"v4" +p #52;
    %"chk222" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v867";
    store Ww [%"chk222" + 0] <- #512
    => goto "L786" };
  ir_blk{ @"L859":
    %"v874" = %"v4" +p #12;
    %"v875" : W = (RawLoad (LdNarrow Uw) 0) %"chk221";
    %"v876" : W = Shl %"v875", #30;
    %"v877" : W = Shr %"v876", #31
    => br %"v877" ? "L870" : "L871" };
  ir_blk{ @"L870":
    %"v879" = %"v4" +p #52;
    %"chk224" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v879";
    store Ww [%"chk224" + 0] <- #1024
    => goto "L786" };
  ir_blk{ @"L871":
    %"v886" = %"v4" +p #12;
    %"v887" : W = (RawLoad (LdNarrow Uw) 0) %"chk221";
    %"v888" : W = Shl %"v887", #22;
    %"v889" : W = Shr %"v888", #31
    => br %"v889" ? "L882" : "L883" };
  ir_blk{ @"L882":
    %"v891" = %"v4" +p #52;
    %"chk226" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v891";
    store Ww [%"chk226" + 0] <- #1
    => goto "L786" };
  ir_blk{ @"L883":
    %"v893" = %"v4" +p #52;
    %"chk227" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v893";
    store Ww [%"chk227" + 0] <- #0
    => goto "L786" };
  ir_blk{ @"L901":
    %"v906" = %"v4" +p #12;
    %"chk228" : A = (Renew 0 4 Read 1) %"chk4", %"v906";
    %"v907" : W = (RawLoad (LdNarrow Uw) 0) %"chk228";
    %"v908" : W = Shl %"v907", #31;
    %"v909" : W = Shr %"v908", #31
    => br %"v909" ? "L902" : "L903" };
  ir_blk{ @"L902":
    %"v911" = %"v4" +p #52;
    %"chk229" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v911";
    store Ww [%"chk229" + 0] <- #263
    => goto "L786" };
  ir_blk{ @"L903":
    %"v915" = %"v4" +p #52;
    %"chk230" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v915";
    store Ww [%"chk230" + 0] <- #7
    => goto "L786" };
  ir_blk{ @"L916":
    %"v918" = %"v4" +p #52;
    %"chk231" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v918";
    store Ww [%"chk231" + 0] <- #1
    => goto "L786" };
  ir_blk{ @"L919":
    %"v921" = %"v4" +p #52;
    %"chk232" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v921";
    store Ww [%"chk232" + 0] <- #2
    => goto "L786" };
  ir_blk{ @"L922":
    %"v924" = %"v4" +p #52;
    %"chk233" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v924";
    store Ww [%"chk233" + 0] <- #3
    => goto "L786" };
  ir_blk{ @"L925":
    %"v927" = %"v4" +p #52;
    %"chk234" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v927";
    store Ww [%"chk234" + 0] <- #4
    => goto "L786" };
  ir_blk{ @"L928":
    %"v930" = %"v4" +p #52;
    %"chk235" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v930";
    store Ww [%"chk235" + 0] <- #5
    => goto "L786" };
  ir_blk{ @"L931":
    %"v933" = %"v4" +p #52;
    %"chk236" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v933";
    store Ww [%"chk236" + 0] <- #2048
    => goto "L786" };
  ir_blk{ @"L937":
    %"v939" = %"v4" +p #56;
    %"chk237" : A = (Renew 0 8 Write 1) %"chk219", %"v939";
    store Wl [%"chk237" + 0] <- #0
    => goto "L786" };
  ir_blk{ @"L942":
    %"v944" : W = (Cmp Slt W) %"v847", #71
    => br %"v944" ? "L945" : "L946" };
  ir_blk{ @"L945":
    %"v947" : W = (Cmp Slt W) %"v847", #67
    => br %"v947" ? "L948" : "L949" };
  ir_blk{ @"L948":
    %"v950" : W = (Cmp Eq W) %"v847", #65
    => br %"v950" ? poll "L901" : "L951" };
  ir_blk{ @"L951":
    %"v952" : W = (Cmp Eq W) %"v847", #66
    => br %"v952" ? poll "L857" : poll "L937" };
  ir_blk{ @"L949":
    %"v954" : W = (Cmp Eq W) %"v847", #67
    => br %"v954" ? poll "L919" : "L955" };
  ir_blk{ @"L955":
    %"v956" : W = (Cmp Eq W) %"v847", #69
    => br %"v956" ? poll "L901" : "L957" };
  ir_blk{ @"L957":
    %"v958" : W = (Cmp Eq W) %"v847", #70
    => br %"v958" ? poll "L901" : poll "L937" };
  ir_blk{ @"L946":
    %"v960" : W = (Cmp Slt W) %"v847", #97
    => br %"v960" ? "L961" : "L962" };
  ir_blk{ @"L961":
    %"v963" : W = (Cmp Eq W) %"v847", #71
    => br %"v963" ? poll "L901" : "L964" };
  ir_blk{ @"L964":
    %"v965" : W = (Cmp Eq W) %"v847", #83
    => br %"v965" ? poll "L925" : "L966" };
  ir_blk{ @"L966":
    %"v967" : W = (Cmp Eq W) %"v847", #88
    => br %"v967" ? poll "L857" : poll "L937" };
  ir_blk{ @"L962":
    %"v969" : W = (Cmp Eq W) %"v847", #97
    => br %"v969" ? poll "L901" : "L970" };
  ir_blk{ @"L970":
    %"v971" : W = (Cmp Eq W) %"v847", #98
    => br %"v971" ? poll "L857" : "L972" };
  ir_blk{ @"L972":
    %"v973" : W = (Cmp Eq W) %"v847", #99
    => br %"v973" ? poll "L916" : poll "L937" };
  ir_blk{ @"L943":
    %"v975" : W = (Cmp Slt W) %"v847", #110
    => br %"v975" ? "L976" : "L977" };
  ir_blk{ @"L976":
    %"v978" : W = (Cmp Slt W) %"v847", #103
    => br %"v978" ? "L979" : "L980" };
  ir_blk{ @"L979":
    %"v981" : W = (Cmp Eq W) %"v847", #100
    => br %"v981" ? poll "L857" : "L982" };
  ir_blk{ @"L982":
    %"v983" : W = (Cmp Eq W) %"v847", #101
    => br %"v983" ? poll "L901" : "L984" };
  ir_blk{ @"L984":
    %"v985" : W = (Cmp Eq W) %"v847", #102
    => br %"v985" ? poll "L901" : poll "L937" };
  ir_blk{ @"L980":
    %"v987" : W = (Cmp Eq W) %"v847", #103
    => br %"v987" ? poll "L901" : "L988" };
  ir_blk{ @"L988":
    %"v989" : W = (Cmp Eq W) %"v847", #105
    => br %"v989" ? poll "L857" : "L990" };
  ir_blk{ @"L990":
    %"v991" : W = (Cmp Eq W) %"v847", #109
    => br %"v991" ? poll "L937" : "L992" };
  ir_blk{ @"L992":
    => goto poll "L937" };
  ir_blk{ @"L977":
    %"v993" : W = (Cmp Slt W) %"v847", #115
    => br %"v993" ? "L994" : "L995" };
  ir_blk{ @"L994":
    %"v996" : W = (Cmp Eq W) %"v847", #110
    => br %"v996" ? poll "L931" : "L997" };
  ir_blk{ @"L997":
    %"v998" : W = (Cmp Eq W) %"v847", #111
    => br %"v998" ? poll "L857" : "L999" };
  ir_blk{ @"L999":
    %"v1000" : W = (Cmp Eq W) %"v847", #112
    => br %"v1000" ? poll "L928" : poll "L937" };
  ir_blk{ @"L995":
    %"v1002" : W = (Cmp Eq W) %"v847", #115
    => br %"v1002" ? poll "L922" : "L1003" };
  ir_blk{ @"L1003":
    %"v1004" : W = (Cmp Eq W) %"v847", #117
    => br %"v1004" ? poll "L857" : "L1005" };
  ir_blk{ @"L1005":
    %"v1006" : W = (Cmp Eq W) %"v847", #120
    => br %"v1006" ? poll "L857" : poll "L937" };
  ir_blk{ @"L786":
    %"v1012" = %"v4" +p #48;
    %"chk238" : A = (Renew 0 4 Read 1) %"chk3", %"v1012";
    %"v1013" : W = (RawLoad (LdNarrow Sw) 0) %"chk238";
    %"v1015" : W = (Cmp Eq W) %"v1013", #4294967295
    => br %"v1015" ? "L1016" : "L1017" };
  ir_blk{ @"L1016":
    %"v1019" = %"v4" +p #56;
    %"chk239" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v1019";
    %"v1020" : L = (RawLoad LdL 0) %"chk239";
    %"v1021" : W = (Cmp Ugt L) %"v1020", #0
    => goto "L1017" };
  ir_blk{ @"L1017" [%"v1023" : W = phi("L786" => #0, "L1016" => %"v1021")]:
    => br %"v1023" ? "L1008" : "L1010" };
  ir_blk{ @"L1008":
    %"v1025" = %"v4" +p #48;
    %"chk240" : A = (Renew 0 4 Write 1) %"chk3", %"v1025";
    store Ww [%"chk240" + 0] <- %"pr.3";
    %"v1029" = %"v4" +p #56;
    %"chk241" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v1029";
    %"v1030" : L = (RawLoad LdL 0) %"chk241";
    %"v1031" : L = Add %"pr.9", %"v1030"
    => goto "L1010" };
  ir_blk{ @"L1010" [%"pr.6" : L = phi("L1008" => %"v1031", "L1017" => %"pr.9")]:
    %"v1036" = %"v4" +p #8;
    %"chk242" : A = (Renew 0 4 Read 1) %"chk207", %"v1036";
    %"v1037" : W = (RawLoad (LdNarrow Sw) 0) %"chk242";
    %"v1038" : W = (Cmp Eq W) %"v1037", #0
    => br %"v1038" ? "L1032" : "L1033" };
  ir_blk{ @"L1032":
    %"v1040" = %"v4" +p #24;
    %"v1042" = %"v4" +p #32;
    %"chk243" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v1043" : P = (RawLoadPointer 0 load_effects) %"chk243";
    (Flight (a "v1044") Sub [(FAddress (t "v1043")); (FValue (Const 1))] (LowerOf (t "v1043")));
    %"chk244" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v1042";
    store.ptr [%"chk244" + 0] <- %"v1044";
    %"chk245" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v1040";
    store.ptr [%"chk245" + 0] <- %"v1044"
    => goto "L1034" };
  ir_blk{ @"L1033":
    %"v1046" = %"v4" +p #24;
    %"chk246" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v1047" : P = (RawLoadPointer 0 load_effects) %"chk246";
    %"chk247" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v1046";
    store.ptr [%"chk247" + 0] <- %"v1047";
    %"v1049" = %"v4" +p #32;
    %"chk248" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v1050" : P = (RawLoadPointer 0 load_effects) %"chk248";
    call %"iw_7.v3" : P = $"__GI___strchrnul"(P %"v1050", W #37);
    %"chk249" : A = (HalfCheck Lower 0 8 Write 8) %"chk3", %"v1049";
    store.ptr [%"chk249" + 0] <- %"iw_7.v3"
    => goto "L1034" };
  ir_blk{ @"L1034":
    => ret %"pr.6" }]))) }.

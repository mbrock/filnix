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

Definition hello_image_fn_glibc_vfprintf_internal'23printf_positional : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#printf_positional"(P %"v0", P %"v2", W %"v4", P %"v6", P %"v8", W %"v10", P %"v12", P %"v14", W %"v16", P %"v18", P %"v20", W %"v22") -> RVoid blocks ((app (app (app [ir_blk{ @"start":
    %"v24" : P = (Alloc 16) #1040;
    %"v31" : P = (Alloc 16) #1040;
    %"v34" : P = (Alloc 8) #8;
    %"v107" : P = (Alloc 4) #1;
    %"v1248" : P = (Alloc 8) #24;
    %"v1887" : P = (Alloc 4) #16;
    %"v1888" : P = (Alloc 4) #8;
    %"v1936" : P = (Alloc 8) #8;
    call void $"glibc_vfprintf_internal#scratch_buffer_init"(P %"v24");
    %"chk0" : A = (Check 0 8 Read 8) %"v24";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v28" = %"v24" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v28";
    %"v29" : L = (RawLoad LdL 0) %"chk1";
    %"v30" : L = Udiv %"v29", #72;
    call void $"glibc_vfprintf_internal#scratch_buffer_init"(P %"v31");
    %"chk2" : A = (Check 0 8 Write 1) %"v34";
    store Wl [%"chk2" + 0] <- #0;
    (Flight (a "v42") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v43" : L = Ptoi %"v18";
    %"v44" : L = Ptoi %"v42";
    %"v45" : W = (Cmp Eq L) %"v43", %"v44"
    => br %"v45" ? "L36" : "L38" };
  ir_blk{ @"L36":
    %"v46" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v48" = %"v47" +p #8;
    %"chk4" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v50" = %"v49" +p #56;
    %"v54" = %"v50" +p #8;
    %"chk5" : A = (Check 0 8 Read 8) %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v56" : P = Copy $"__libc_tsd_LOCALE";
    %"chk6" : A = (Check 0 8 Read 8) %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v58" = %"v57" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v60" = %"v59" +p #56;
    %"v64" = %"v60" +p #16;
    %"chk8" : A = (Check 0 8 Read 8) %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 1 Read 1) %"v65";
    %"v70" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v71" : W = (Cmp Eq W) %"v70", #0
    => br %"v71" ? "L73" : "L72" };
  ir_blk{ @"L72":
    %"v75" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v76" : W = (Cmp Eq W) %"v75", #127
    => goto "L73" };
  ir_blk{ @"L73" [%"v78" : W = phi("L36" => #1, "L72" => %"v76")]:
    => br %"v78" ? "L38" : "L67" };
  ir_blk{ @"L67":
    => goto "L38" };
  ir_blk{ @"L38" [%"pr.6" : P = phi("L67" => %"v55", "L73" => %"v55", "start" => %"v20")]:
    => goto "L81" };
  ir_blk{ @"L81" [%"pr.15" : P = phi("L38" => %"v12", "L83" => %"v129"); %"pr.12" : L = phi("L38" => #0, "L83" => %"v116"); %"pr.11" : L = phi("L38" => #0, "L83" => %"v125"); %"pr.9" : L = phi("L38" => %"v30", "L83" => %"pr.10"); %"pr.7" : P = phi("L38" => %"v26", "L83" => %"pr.8")]:
    %"chk11" : A = (Check 0 1 Read 1) %"pr.15";
    %"v86" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"v87" : W = (Cmp Ne W) %"v86", #0
    => br %"v87" ? "L82" : "L84" };
  ir_blk{ @"L82":
    %"v93" : W = (Cmp Eq L) %"pr.11", %"pr.9"
    => br %"v93" ? "iw_1.start" : "L90" };
  ir_blk{ @"iw_1.start":
    call %"iw_1.v3" : W = $"__GI___libc_scratch_buffer_grow_preserve"(P %"v24");
    %"iw_1.v4" : W = (Ext Ub) %"iw_1.v3";
    %"iw_1.v5" : L = (Ext Uw) %"iw_1.v4";
    %"v99" : W = (Cmp Eq L) %"iw_1.v5", #0
    => br %"v99" ? "L94" : "L96" };
  ir_blk{ @"L94":
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L96":
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v24";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v104" = %"v24" +p #8;
    %"chk13" : A = (Renew 0 8 Read 1) %"chk1", %"v104";
    %"v105" : L = (RawLoad LdL 0) %"chk13";
    %"v106" : L = Udiv %"v105", #72
    => goto "L90" };
  ir_blk{ @"L90" [%"pr.10" : L = phi("L96" => %"v106", "L82" => %"pr.9"); %"pr.8" : P = phi("L96" => %"v103", "L82" => %"pr.7")]:
    %"v113" : L = Mul %"pr.11", #72;
    %"v114" = %"pr.8" +p %"v113";
    call %"v115" : L = $"__parse_one_specmb"(P %"pr.15", L %"pr.12", P %"v114", P %"v34", P %"v107");
    %"v116" : L = Add %"pr.12", %"v115";
    %"chk14" : A = (Check 0 1 Read 1) %"v107";
    %"v120" : W = (RawLoad (LdNarrow Ub) 0) %"chk14"
    => br %"v120" ? "L117" : "L83" };
  ir_blk{ @"L117":
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L83":
    %"v125" : L = Add %"pr.11", #1;
    %"v128" = %"v114" +p #32;
    %"chk15" : A = (Check 0 8 Read 8) %"v128";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk15"
    => goto poll "L81" };
  ir_blk{ @"L84":
    %"chk16" : A = (Renew 0 8 Read 1) %"chk2", %"v34";
    %"v134" : L = (RawLoad LdL 0) %"chk16";
    %"v135" : W = (Cmp Ugt L) %"pr.12", %"v134"
    => br %"v135" ? "L132" : "L131" };
  ir_blk{ @"L131":
    %"v137" : L = (RawLoad LdL 0) %"chk16"
    => goto "L132" };
  ir_blk{ @"L132" [%"v138" : L = phi("L131" => %"v137", "L84" => %"pr.12")]:
    call %"iw_2.v9" : W = $"__GI___libc_scratch_buffer_set_array_size"(P %"v31", L %"v138", L #24);
    %"iw_2.v10" : W = (Ext Ub) %"iw_2.v9";
    %"iw_2.v11" : L = (Ext Uw) %"iw_2.v10";
    %"v154" : W = (Cmp Eq L) %"iw_2.v11", #0
    => br %"v154" ? "L147" : "L149" };
  ir_blk{ @"L147":
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L149":
    %"chk18" : A = (Check 0 8 Read 8) %"v31";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v160" : L = Shl %"v138", #4;
    %"v161" = %"v157" +p %"v160";
    %"v164" : L = Shl %"v138", #2;
    %"v165" = %"v161" +p %"v164";
    %"v169" = %"v165" +p %"v164";
    %"v175" : W = And %"v22", #2;
    %"v176" : W = (Cmp Ne W) %"v175", #0
    => br %"v176" ? "L173" : "L172" };
  ir_blk{ @"L172":
    => goto "L173" };
  ir_blk{ @"L173" [%"v177" : W = phi("L172" => #0, "L149" => #(-1))]:
    call %"v180" : P = $"__GI_memset"(P %"v165", W %"v177", L %"v164")
    => goto "L181" };
  ir_blk{ @"L181" [%"pr.13" : L = phi("L173" => #0, "L183" => %"v322")]:
    %"v187" : W = (Cmp Ult L) %"pr.13", %"pr.11"
    => br %"v187" ? "L182" : "L323" };
  ir_blk{ @"L182":
    %"v193" : L = Mul %"pr.13", #72;
    %"v194" = %"pr.7" +p %"v193";
    %"v195" = %"v194" +p #44;
    %"chk19" : A = (Check 0 4 Read 1) %"v195";
    %"v196" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v198" : W = (Cmp Ne W) %"v196", #4294967295
    => br %"v198" ? "L188" : "L190" };
  ir_blk{ @"L188":
    %"v204" = %"v194" +p #44;
    %"v205" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v206" : L = (Ext Sw) %"v205";
    %"v207" : L = Shl %"v206", #2;
    %"v208" = %"v165" +p %"v207";
    %"chk21" : A = (Check 0 4 Write 1) %"v208";
    store Ww [%"chk21" + 0] <- #0
    => goto "L190" };
  ir_blk{ @"L190":
    %"v216" = %"v194" +p #40;
    %"chk22" : A = (HalfCheck Lower 0 4 Read 1) %"chk19", %"v216";
    %"v217" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v219" : W = (Cmp Ne W) %"v217", #4294967295
    => br %"v219" ? "L209" : "L211" };
  ir_blk{ @"L209":
    %"v225" = %"v194" +p #40;
    %"v226" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v227" : L = (Ext Sw) %"v226";
    %"v228" : L = Shl %"v227", #2;
    %"v229" = %"v165" +p %"v228";
    %"chk24" : A = (Check 0 4 Write 1) %"v229";
    store Ww [%"chk24" + 0] <- #0
    => goto "L211" };
  ir_blk{ @"L211":
    %"v234" = %"v194" +p #56;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 1) %"chk19", %"v234";
    %"v235" : L = (RawLoad LdL 0) %"chk25";
    %"v317" : W = (Cmp Eq L) %"v235", #0
    => br %"v317" ? "L183" : "L318" };
  ir_blk{ @"L239":
    %"v245" = %"v194" +p #48;
    %"chk26" : A = (HalfCheck Upper 0 4 Read 1) %"chk19", %"v245";
    %"v246" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v247" : L = (Ext Sw) %"v246";
    %"v248" : L = Shl %"v247", #2;
    %"v249" = %"v165" +p %"v248";
    %"v254" = %"v194" +p #52;
    %"chk27" : A = (HalfCheck Upper 0 4 Read 1) %"chk19", %"v254";
    %"v255" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"chk28" : A = (Check 0 4 Write 1) %"v249";
    store Ww [%"chk28" + 0] <- %"v255";
    %"v262" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v263" : L = (Ext Sw) %"v262";
    %"v264" : L = Shl %"v263", #2;
    %"v265" = %"v161" +p %"v264";
    %"v270" = %"v194" +p #64;
    %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk19", %"v270";
    %"v271" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"chk31" : A = (Check 0 4 Write 1) %"v265";
    store Ww [%"chk31" + 0] <- %"v271"
    => goto "L183" };
  ir_blk{ @"L272":
    %"v273" : P = Copy $"__printf_arginfo_table";
    %"chk32" : A = (Check 0 8 Read 8) %"v273";
    %"v274" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v279" = %"v194" +p #8;
    %"chk33" : A = (HalfCheck Lower 0 4 Read 1) %"chk19", %"v279";
    %"v280" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"v281" : L = (Ext Sw) %"v280";
    %"v282" : L = Shl %"v281", #3;
    %"v283" = %"v274" +p %"v282";
    %"chk34" : A = (Check 0 8 Read 8) %"v283";
    %"v284" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v293" = %"v194" +p #56;
    %"chk35" : A = (Renew 0 8 Read 1) %"chk25", %"v293";
    %"v294" : L = (RawLoad LdL 0) %"chk35";
    %"v300" = %"v194" +p #48;
    %"v301" : W = (RawLoad (LdNarrow Sw) (-8)) %"chk35";
    %"v302" : L = (Ext Sw) %"v301";
    %"v303" : L = Shl %"v302", #2;
    %"v304" = %"v165" +p %"v303";
    %"v311" : W = (RawLoad (LdNarrow Sw) (-8)) %"chk35";
    %"v312" : L = (Ext Sw) %"v311";
    %"v313" : L = Shl %"v312", #2;
    %"v314" = %"v161" +p %"v313";
    %"chk38" : F = CheckFunction %"v284";
    rawcall %"v315" : W = %"chk38"(P %"v194", L %"v294", P %"v304", P %"v314")
    => goto "L183" };
  ir_blk{ @"L318":
    %"v319" : W = (Cmp Eq L) %"v235", #1
    => br %"v319" ? poll "L239" : poll "L272" };
  ir_blk{ @"L183":
    %"v322" : L = Add %"pr.13", #1
    => goto poll "L181" };
  ir_blk{ @"L323" [%"pr.31" : P = phi("L336" => %"pr.32", "L181" => %"v169"); %"pr.26" : P = phi("L336" => %"pr.27", "L181" => %"v165"); %"pr.21" : P = phi("L336" => %"pr.22", "L181" => %"v161"); %"pr.16" : P = phi("L336" => %"pr.17", "L181" => %"v157"); %"pr.14" : L = phi("L336" => %"v586", "L181" => #0)]:
    %"v329" : W = (Cmp Ult L) %"pr.14", %"v138"
    => br %"v329" ? "L324" : "L587" };
  ir_blk{ @"L324":
    %"v332" : L = Shl %"pr.14", #2;
    %"v333" = %"pr.26" +p %"v332";
    %"chk39" : A = (Check 0 4 Read 1) %"v333";
    %"v334" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"v550" : W = (Cmp Slt W) %"v334", #5
    => br %"v550" ? "L551" : "L552" };
  ir_blk{ @"L337":
    %"v340" : L = Shl %"pr.14", #4;
    %"v341" = %"pr.16" +p %"v340";
    %"v343" : W = VaArg %"v8";
    %"chk40" : A = (Check 0 4 Write 1) %"v341";
    store Ww [%"chk40" + 0] <- %"v343"
    => goto "L336" };
  ir_blk{ @"L346":
    %"v349" : L = Shl %"pr.14", #4;
    %"v350" = %"pr.16" +p %"v349";
    %"v352" : W = VaArg %"v8";
    %"chk41" : A = (Check 0 4 Write 1) %"v350";
    store Ww [%"chk41" + 0] <- %"v352"
    => goto "L336" }] [ir_blk{ @"L354":
    %"v357" : L = Shl %"pr.14", #4;
    %"v358" = %"pr.16" +p %"v357";
    %"v360" : L = VaArg %"v8";
    %"chk42" : A = (Check 0 8 Write 1) %"v358";
    store Wl [%"chk42" + 0] <- %"v360"
    => goto "L336" };
  ir_blk{ @"L362":
    %"v365" : L = Shl %"pr.14", #4;
    %"v366" = %"pr.16" +p %"v365";
    %"v368" : Double = VaArg %"v8";
    %"chk43" : A = (Check 0 8 Write 1) %"v366";
    store Wd [%"chk43" + 0] <- %"v368"
    => goto "L336" };
  ir_blk{ @"L369":
    %"v374" : W = And %"v22", #1
    => br %"v374" ? "L370" : "L371" };
  ir_blk{ @"L370":
    %"v380" : L = Shl %"pr.14", #4;
    %"v381" = %"pr.16" +p %"v380";
    %"v383" : Double = VaArg %"v8";
    %"chk44" : A = (Check 0 8 Write 1) %"v381";
    store Wd [%"chk44" + 0] <- %"v383";
    %"chk45" : A = (Renew 0 4 Read 1) %"chk39", %"v333";
    %"v388" : W = (RawLoad (LdNarrow Sw) 0) %"chk45";
    %"v391" : W = And %"v388", #4294967039;
    %"chk46" : A = (Renew 0 4 Write 1) %"chk39", %"v333";
    store Ww [%"chk46" + 0] <- %"v391"
    => goto "L336" };
  ir_blk{ @"L371":
    %"v394" : L = Shl %"pr.14", #4;
    %"v395" = %"pr.16" +p %"v394";
    %"v397" : Extended = VaArg %"v8";
    %"chk47" : A = (Check 0 10 Write 8) %"v395";
    store Wx [%"chk47" + 0] <- %"v397"
    => goto "L336" };
  ir_blk{ @"L400":
    %"v403" : L = Shl %"pr.14", #4;
    %"v404" = %"pr.16" +p %"v403";
    %"v406" : P = VaArg %"v8";
    %"chk48" : A = (Check 0 8 Write 8) %"v404";
    store.ptr [%"chk48" + 0] <- %"v406"
    => goto "L336" };
  ir_blk{ @"L407":
    %"chk49" : A = (Renew 0 4 Read 1) %"chk39", %"v333";
    %"v415" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"v417" : W = And %"v415", #2048;
    %"v418" : W = (Cmp Ne W) %"v417", #0
    => br %"v418" ? "L408" : "L409" };
  ir_blk{ @"L408":
    %"v421" : L = Shl %"pr.14", #4;
    %"v422" = %"pr.16" +p %"v421";
    %"v424" : P = VaArg %"v8";
    %"chk50" : A = (Check 0 8 Write 8) %"v422";
    store.ptr [%"chk50" + 0] <- %"v424"
    => goto "L336" };
  ir_blk{ @"L409":
    %"v428" : P = Copy $"__printf_va_arg_table";
    %"chk51" : A = (Check 0 8 Read 8) %"v428";
    %"v429" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v430" : L = Ptoi %"v429";
    %"v431" : L = Ptoi #0;
    %"v432" : W = (Cmp Ne L) %"v430", %"v431"
    => br %"v432" ? "L435" : "L436" };
  ir_blk{ @"L435":
    %"v437" : P = Copy $"__printf_va_arg_table";
    %"chk52" : A = (Check 0 8 Read 8) %"v437";
    %"v438" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"chk53" : A = (Renew 0 4 Read 1) %"chk39", %"v333";
    %"v443" : W = (RawLoad (LdNarrow Sw) 0) %"chk53";
    %"v444" : W = Sub %"v443", #8;
    %"v445" : L = (Ext Sw) %"v444";
    %"v446" : L = Shl %"v445", #3;
    %"v447" = %"v438" +p %"v446";
    %"chk54" : A = (Check 0 8 Read 8) %"v447";
    %"v448" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v449" : L = Ptoi %"v448";
    %"v451" : W = (Cmp Ne L) %"v449", %"v431"
    => goto "L436" };
  ir_blk{ @"L436" [%"v453" : W = phi("L409" => #0, "L435" => %"v451")]:
    => br %"v453" ? "L454" : "L426" };
  ir_blk{ @"L454" [%"pr.35" : P = phi("L482" => %"v502", "L436" => %"pr.31"); %"pr.30" : P = phi("L482" => %"v496", "L436" => %"pr.26"); %"pr.25" : P = phi("L482" => %"v492", "L436" => %"pr.21"); %"pr.20" : P = phi("L482" => %"v488", "L436" => %"pr.16")]:
    %"v461" = %"pr.25" +p %"v332";
    %"chk55" : A = (Check 0 4 Read 1) %"v461";
    %"v462" : W = (RawLoad (LdNarrow Sw) 0) %"chk55";
    %"v463" : L = (Ext Sw) %"v462";
    %"v464" = %"pr.35" +p %"v463";
    %"chk56" : A = (Renew 0 8 Read 8) %"chk18", %"v31";
    %"v465" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v466" = %"v31" +p #8;
    %"chk57" : A = (HalfCheck Upper 0 8 Read 1) %"chk18", %"v466";
    %"v467" : L = (RawLoad LdL 0) %"chk57";
    %"v468" = %"v465" +p %"v467";
    %"v469" : L = Ptoi %"v464";
    %"v470" : L = Ptoi %"v468";
    %"v471" : W = (Cmp Ugt L) %"v469", %"v470"
    => br %"v471" ? "L455" : "L456" };
  ir_blk{ @"L455":
    %"v476" = %"pr.30" +p %"v164";
    %"v477" : L = Ptoi %"pr.35";
    %"v478" : L = Ptoi %"v476";
    %"v479" : L = Sub %"v477", %"v478";
    call %"iw_3.v3" : W = $"__GI___libc_scratch_buffer_grow_preserve"(P %"v31");
    %"iw_3.v4" : W = (Ext Ub) %"iw_3.v3";
    %"iw_3.v5" : L = (Ext Uw) %"iw_3.v4";
    %"v485" : W = (Cmp Eq L) %"iw_3.v5", #0
    => br %"v485" ? "L480" : "L482" };
  ir_blk{ @"L480":
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L482":
    %"chk58" : A = (Renew 0 8 Read 8) %"chk18", %"v31";
    %"v488" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v492" = %"v488" +p %"v160";
    %"v496" = %"v492" +p %"v164";
    %"v500" = %"v496" +p %"v164";
    %"v502" = %"v500" +p %"v479"
    => goto poll "L454" };
  ir_blk{ @"L456":
    %"v505" : L = Shl %"pr.14", #4;
    %"v506" = %"pr.20" +p %"v505";
    %"chk59" : A = (Check 0 8 Write 8) %"v506";
    store.ptr [%"chk59" + 0] <- %"pr.35";
    %"chk60" : A = (Renew 0 4 Read 1) %"chk55", %"v461";
    %"v513" : W = (RawLoad (LdNarrow Sw) 0) %"chk60";
    %"v514" : L = (Ext Sw) %"v513";
    %"v515" = %"pr.35" +p %"v514";
    %"v516" : P = Copy $"__printf_va_arg_table";
    %"chk61" : A = (Check 0 8 Read 8) %"v516";
    %"v517" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v521" = %"pr.30" +p %"v332";
    %"chk62" : A = (Check 0 4 Read 1) %"v521";
    %"v522" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v523" : W = Sub %"v522", #8;
    %"v524" : L = (Ext Sw) %"v523";
    %"v525" : L = Shl %"v524", #3;
    %"v526" = %"v517" +p %"v525";
    %"chk63" : A = (Check 0 8 Read 8) %"v526";
    %"v527" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"chk64" : A = (Renew 0 8 Read 8) %"chk59", %"v506";
    %"v532" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"chk65" : F = CheckFunction %"v527";
    rawcall void %"chk65"(P %"v532", P %"v8")
    => goto "L336" };
  ir_blk{ @"L426":
    %"v536" : L = Shl %"pr.14", #4;
    %"v537" = %"pr.16" +p %"v536";
    call %"v538" : P = $"__GI_memset"(P %"v537", W #0, L #16)
    => goto "L336" };
  ir_blk{ @"L539":
    => br %"v176" ? "L542" : "L541" };
  ir_blk{ @"L541":
    %"v546" : P = Copy $"glibc_vfprintf_internal#str.290";
    %"v547" : P = Copy $"glibc_vfprintf_internal#str.291";
    %"v548" : P = Copy $"glibc_vfprintf_internal#str.292";
    call void $"__libc_assert_fail"(P %"v546", P %"v547", W #1270, P %"v548")
    => goto "L542" };
  ir_blk{ @"L542":
    %"v549" : P = Copy $"glibc_vfprintf_internal#str.293";
    call void $"__GI___libc_fatal"(P %"v549")
    => goto "L336" };
  ir_blk{ @"L551":
    %"v553" : W = (Cmp Slt W) %"v334", #2
    => br %"v553" ? "L554" : "L555" };
  ir_blk{ @"L554":
    %"v556" : W = (Cmp Eq W) %"v334", #(-1)
    => br %"v556" ? poll "L539" : "L557" };
  ir_blk{ @"L557":
    %"v558" : W = (Cmp Eq W) %"v334", #0
    => br %"v558" ? poll "L346" : "L559" };
  ir_blk{ @"L559":
    %"v560" : W = (Cmp Eq W) %"v334", #1
    => br %"v560" ? poll "L346" : poll "L407" };
  ir_blk{ @"L555":
    %"v562" : W = (Cmp Eq W) %"v334", #2
    => br %"v562" ? poll "L337" : "L563" };
  ir_blk{ @"L563":
    %"v564" : W = (Cmp Eq W) %"v334", #3
    => br %"v564" ? poll "L400" : "L565" };
  ir_blk{ @"L565":
    %"v566" : W = (Cmp Eq W) %"v334", #4
    => br %"v566" ? poll "L400" : poll "L407" };
  ir_blk{ @"L552":
    %"v568" : W = (Cmp Slt W) %"v334", #256
    => br %"v568" ? "L569" : "L570" };
  ir_blk{ @"L569":
    %"v571" : W = (Cmp Eq W) %"v334", #5
    => br %"v571" ? poll "L400" : "L572" };
  ir_blk{ @"L572":
    %"v573" : W = (Cmp Eq W) %"v334", #6
    => br %"v573" ? poll "L362" : "L574" };
  ir_blk{ @"L574":
    %"v575" : W = (Cmp Eq W) %"v334", #7
    => br %"v575" ? poll "L362" : poll "L407" };
  ir_blk{ @"L570":
    %"v577" : W = (Cmp Eq W) %"v334", #256
    => br %"v577" ? poll "L354" : "L578" };
  ir_blk{ @"L578":
    %"v579" : W = (Cmp Eq W) %"v334", #263
    => br %"v579" ? poll "L369" : "L580" };
  ir_blk{ @"L580":
    %"v581" : W = (Cmp Eq W) %"v334", #512
    => br %"v581" ? poll "L354" : "L582" };
  ir_blk{ @"L582":
    %"v583" : W = (Cmp Eq W) %"v334", #1024
    => br %"v583" ? poll "L346" : poll "L407" };
  ir_blk{ @"L336" [%"pr.32" : P = phi("L337" => %"pr.31", "L346" => %"pr.31", "L354" => %"pr.31", "L362" => %"pr.31", "L400" => %"pr.31", "L542" => %"pr.31", "L370" => %"pr.31", "L371" => %"pr.31", "L408" => %"pr.31", "L456" => %"v515", "L426" => %"pr.31"); %"pr.27" : P = phi("L337" => %"pr.26", "L346" => %"pr.26", "L354" => %"pr.26", "L362" => %"pr.26", "L400" => %"pr.26", "L542" => %"pr.26", "L370" => %"pr.26", "L371" => %"pr.26", "L408" => %"pr.26", "L456" => %"pr.30", "L426" => %"pr.26"); %"pr.22" : P = phi("L337" => %"pr.21", "L346" => %"pr.21", "L354" => %"pr.21", "L362" => %"pr.21", "L400" => %"pr.21", "L542" => %"pr.21", "L370" => %"pr.21", "L371" => %"pr.21", "L408" => %"pr.21", "L456" => %"pr.25", "L426" => %"pr.21"); %"pr.17" : P = phi("L337" => %"pr.16", "L346" => %"pr.16", "L354" => %"pr.16", "L362" => %"pr.16", "L400" => %"pr.16", "L542" => %"pr.16", "L370" => %"pr.16", "L371" => %"pr.16", "L408" => %"pr.16", "L456" => %"pr.20", "L426" => %"pr.16")]:
    %"v586" : L = Add %"pr.14", #1
    => goto poll "L323" }]) (app [ir_blk{ @"L587" [%"pr.5" : W = phi("L866" => %"v2032", "L323" => %"v10"); %"pr.3" : W = phi("L866" => %"pr.4", "L323" => %"v4")]:
    %"v592" : L = (Ext Sw) %"pr.5";
    %"v594" : W = (Cmp Ult L) %"v592", %"pr.11"
    => br %"v594" ? "L595" : "L596" };
  ir_blk{ @"L595":
    call %"v598" : W = $"glibc_vfprintf_internal#__printf_buffer_has_failed"(P %"v0");
    %"v599" : W = (Ext Ub) %"v598";
    %"v600" : W = (Cmp Eq W) %"v599", #0
    => goto "L596" };
  ir_blk{ @"L596" [%"v602" : W = phi("L587" => #0, "L595" => %"v600")]:
    => br %"v602" ? "L588" : "L101" };
  ir_blk{ @"L588":
    %"v611" : L = Mul %"v592", #72;
    %"v612" = %"pr.7" +p %"v611";
    %"v613" = %"v612" +p #12;
    %"chk66" : A = (Check 0 4 Read 1) %"v613";
    %"v614" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v615" : W = Shl %"v614", #28;
    %"v616" : W = Shr %"v615", #31;
    %"v624" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v625" : W = Shl %"v624", #27;
    %"v626" : W = Shr %"v625", #31;
    %"v634" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v635" : W = Shl %"v634", #26;
    %"v636" : W = Shr %"v635", #31;
    %"v644" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v645" : W = Shl %"v644", #25;
    %"v646" : W = Shr %"v645", #31;
    %"v654" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v655" : W = Shl %"v654", #24;
    %"v656" : W = Shr %"v655", #31;
    %"v664" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v674" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v675" : W = Shl %"v674", #30;
    %"v676" : W = Shr %"v675", #31;
    %"v684" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v685" : W = Shl %"v684", #22;
    %"v686" : W = Shr %"v685", #31;
    %"v694" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v695" : W = Shl %"v694", #29;
    %"v696" : W = Shr %"v695", #31;
    %"v703" = %"v612" +p #4;
    %"chk75" : A = (HalfCheck Lower 0 4 Read 1) %"chk66", %"v703";
    %"v704" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"chk76" : A = (HalfCheck Lower 0 4 Read 1) %"chk66", %"v612";
    %"v711" : W = (RawLoad (LdNarrow Sw) 0) %"chk76";
    %"v719" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v720" : W = Shl %"v719", #20;
    %"v721" : W = Shr %"v720", #31;
    %"v728" = %"v612" +p #16;
    %"chk78" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v728";
    %"v729" : W = (RawLoad (LdNarrow Sw) 0) %"chk78";
    %"v730" : W = (Ext Sb) %"v729";
    %"v737" = %"v612" +p #8;
    %"v738" : W = (RawLoad (LdNarrow Sw) 4) %"chk75";
    %"v739" : W = (Ext Sb) %"v738";
    %"v742" = %"v14" +p #1000;
    %"v751" = %"v612" +p #44;
    %"chk80" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v751";
    %"v752" : W = (RawLoad (LdNarrow Sw) 0) %"chk80";
    %"v754" : W = (Cmp Ne W) %"v752", #4294967295
    => br %"v754" ? "L743" : "L745" };
  ir_blk{ @"L743":
    %"v760" = %"v612" +p #4;
    %"v767" = %"v612" +p #44;
    %"v768" : W = (RawLoad (LdNarrow Sw) 0) %"chk80";
    %"v769" : L = (Ext Sw) %"v768";
    %"v770" : L = Shl %"v769", #4;
    %"v771" = %"pr.16" +p %"v770";
    %"chk82" : A = (Check 0 4 Read 1) %"v771";
    %"v772" : W = (RawLoad (LdNarrow Sw) 0) %"chk82";
    %"chk83" : A = (Renew 0 4 Write 1) %"chk75", %"v760";
    store Ww [%"chk83" + 0] <- %"v772";
    %"v782" : W = (RawLoad (LdNarrow Sw) 0) %"chk83";
    %"v783" : W = (Cmp Slt W) %"v782", #0
    => br %"v783" ? "L773" : "L775" };
  ir_blk{ @"L773":
    %"v789" = %"v612" +p #4;
    %"v790" : W = (RawLoad (LdNarrow Sw) 0) %"chk83";
    %"v792" : W = Mul %"v790", #4294967295;
    store Ww [%"chk83" + 0] <- %"v792";
    %"v798" = %"v612" +p #12;
    %"v799" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v800" : W = And %"v799", #4294967263;
    %"v803" : W = Or %"v800", #32;
    store Ww [%"chk66" + 0] <- %"v803"
    => goto "L775" };
  ir_blk{ @"L775" [%"pr.65" : W = phi("L773" => #1, "L743" => %"v636")]:
    %"v811" = %"v612" +p #4;
    %"v812" : W = (RawLoad (LdNarrow Sw) 0) %"chk83"
    => goto "L745" };
  ir_blk{ @"L745" [%"pr.81" : W = phi("L775" => %"v812", "L588" => %"v704"); %"pr.64" : W = phi("L775" => %"pr.65", "L588" => %"v636")]:
    %"v821" = %"v612" +p #40;
    %"v822" : W = (RawLoad (LdNarrow Sw) (-4)) %"chk80";
    %"v824" : W = (Cmp Ne W) %"v822", #4294967295
    => br %"v824" ? "L813" : "L815" };
  ir_blk{ @"L813":
    %"v836" = %"v612" +p #40;
    %"v837" : W = (RawLoad (LdNarrow Sw) (-4)) %"chk80";
    %"v838" : L = (Ext Sw) %"v837";
    %"v839" : L = Shl %"v838", #4;
    %"v840" = %"pr.16" +p %"v839";
    %"chk92" : A = (Check 0 4 Read 1) %"v840";
    %"v841" : W = (RawLoad (LdNarrow Sw) 0) %"chk92";
    %"chk93" : A = (Renew 0 4 Write 1) %"chk76", %"v612";
    store Ww [%"chk93" + 0] <- %"v841";
    %"v850" : W = (RawLoad (LdNarrow Sw) 0) %"chk93";
    %"v851" : W = (Cmp Slt W) %"v850", #0
    => br %"v851" ? "L842" : "L844" };
  ir_blk{ @"L842":
    store Ww [%"chk93" + 0] <- #4294967295
    => goto "L844" };
  ir_blk{ @"L844":
    %"v863" : W = (RawLoad (LdNarrow Sw) 0) %"chk93"
    => goto "L815" };
  ir_blk{ @"L815" [%"pr.89" : W = phi("L844" => %"v863", "L745" => %"v711")]:
    %"v872" : P = Copy $"__printf_function_table";
    %"chk97" : A = (Check 0 8 Read 8) %"v872";
    %"v873" : P = (RawLoadPointer 0 load_effects) %"chk97";
    %"v874" : L = Ptoi %"v873";
    %"v875" : L = Ptoi #0;
    %"v876" : W = (Cmp Ne L) %"v874", %"v875"
    => br %"v876" ? "L879" : "L880" };
  ir_blk{ @"L879":
    %"v881" : P = Copy $"__printf_function_table";
    %"chk98" : A = (Check 0 8 Read 8) %"v881";
    %"v882" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"v884" : L = (Ext Sw) %"v739";
    %"v885" : L = Shl %"v884", #3;
    %"v886" = %"v882" +p %"v885";
    %"chk99" : A = (Check 0 8 Read 8) %"v886";
    %"v887" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"v888" : L = Ptoi %"v887";
    %"v890" : W = (Cmp Ne L) %"v888", %"v875"
    => goto "L880" };
  ir_blk{ @"L880" [%"v892" : W = phi("L815" => #0, "L879" => %"v890")]:
    => br %"v892" ? "L867" : "L940" };
  ir_blk{ @"L867":
    %"v895" : P = Copy $"__printf_function_table";
    %"chk100" : A = (Check 0 8 Read 8) %"v895";
    %"v896" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"v898" : L = (Ext Sw) %"v739";
    %"v899" : L = Shl %"v898", #3;
    %"v900" = %"v896" +p %"v899";
    %"chk101" : A = (Check 0 8 Read 8) %"v900";
    %"v901" : P = (RawLoadPointer 0 load_effects) %"chk101";
    %"v908" = %"v612" +p #48;
    %"chk102" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v908";
    %"v909" : W = (RawLoad (LdNarrow Sw) 0) %"chk102";
    %"v910" : L = (Ext Sw) %"v909";
    %"v911" : L = Shl %"v910", #4;
    %"v912" = %"pr.16" +p %"v911";
    %"v918" = %"v612" +p #56;
    %"chk103" : A = (HalfCheck Upper 0 8 Read 1) %"chk66", %"v918";
    %"v919" : L = (RawLoad LdL 0) %"chk103";
    call %"v925" : W = $"__printf_function_invoke"(P %"v0", P %"v901", P %"v912", L %"v919", P %"v612");
    %"v931" : W = (Cmp Ne W) %"v925", #4294967294
    => br %"v931" ? "L926" : "L940" };
  ir_blk{ @"L926":
    %"v936" : W = (Cmp Slt W) %"v925", #0
    => br %"v936" ? "L932" : "L866" };
  ir_blk{ @"L932":
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L940":
    %"v950" : W = (Cmp Slt W) %"v739", #32
    => br %"v950" ? "L952" : "L951" };
  ir_blk{ @"L951":
    %"v954" : W = (Cmp Sgt W) %"v739", #122
    => goto "L952" };
  ir_blk{ @"L952" [%"v956" : W = phi("L940" => #1, "L951" => %"v954")]:
    => br %"v956" ? "L948" : "L947" };
  ir_blk{ @"L947":
    %"v960" : P = Copy $"glibc_vfprintf_internal#printf_positional.step4_jumps.294";
    %"v961" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v963" : W = Sub %"v739", #32;
    %"v964" : L = (Ext Sw) %"v963";
    %"v965" = %"v961" +p %"v964";
    %"chk104" : A = (Check 0 1 Read 1) %"v965";
    %"v966" : W = (RawLoad (LdNarrow Ub) 0) %"chk104";
    %"v967" : L = (Ext Uw) %"v966";
    %"v968" : L = Shl %"v967", #2;
    %"v969" = %"v960" +p %"v968";
    %"chk105" : A = (Check 0 4 Read 1) %"v969";
    %"v970" : W = (RawLoad (LdNarrow Sw) 0) %"chk105";
    %"v971" : L = (Ext Sw) %"v970"
    => goto "L948" };
  ir_blk{ @"L948" [%"v972" : L = phi("L947" => %"v971", "L952" => #0)]:
    %"v973" : W = Copy %"v972";
    %"v974" : L = (Ext Sw) %"v973";
    %"v975" = #1 +p %"v974";
    %"v977" : L = Ptoi %"v975";
    %"v2035" : W = (Cmp Ult L) %"v977", #8
    => br %"v2035" ? "L2036" : "L2037" };
  ir_blk{ @"L980":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #37)
    => goto "L866" };
  ir_blk{ @"L984":
    => br %"v696" ? "L1012" : "L1013" };
  ir_blk{ @"L1012":
    %"v1022" = %"v612" +p #48;
    %"chk106" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1022";
    %"v1023" : W = (RawLoad (LdNarrow Sw) 0) %"chk106";
    %"v1024" : L = (Ext Sw) %"v1023";
    %"v1025" : L = Shl %"v1024", #4;
    %"v1026" = %"pr.16" +p %"v1025";
    %"chk107" : A = (Check 0 8 Read 1) %"v1026";
    %"v1027" : L = (RawLoad LdL 0) %"chk107"
    => goto "L1014" };
  ir_blk{ @"L1013":
    => br %"v686" ? "L1028" : "L1029" };
  ir_blk{ @"L1028":
    %"v1038" = %"v612" +p #48;
    %"chk108" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1038";
    %"v1039" : W = (RawLoad (LdNarrow Sw) 0) %"chk108";
    %"v1040" : L = (Ext Sw) %"v1039";
    %"v1041" : L = Shl %"v1040", #4;
    %"v1042" = %"pr.16" +p %"v1041";
    %"chk109" : A = (Check 0 4 Read 1) %"v1042";
    %"v1043" : W = (RawLoad (LdNarrow Uw) 0) %"chk109";
    %"v1044" : W = (Ext Sb) %"v1043";
    %"v1045" : L = (Ext Sw) %"v1044"
    => goto "L1014" };
  ir_blk{ @"L1029":
    %"v1050" : W = (Cmp Eq W) %"v676", #0
    => br %"v1050" ? "L1046" : "L1047" };
  ir_blk{ @"L1046":
    %"v1057" = %"v612" +p #48;
    %"chk110" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1057";
    %"v1058" : W = (RawLoad (LdNarrow Sw) 0) %"chk110";
    %"v1059" : L = (Ext Sw) %"v1058";
    %"v1060" : L = Shl %"v1059", #4;
    %"v1061" = %"pr.16" +p %"v1060";
    %"chk111" : A = (Check 0 4 Read 1) %"v1061";
    %"v1062" : W = (RawLoad (LdNarrow Sw) 0) %"chk111";
    %"v1063" : L = (Ext Sw) %"v1062"
    => goto "L1014" };
  ir_blk{ @"L1047":
    %"v1070" = %"v612" +p #48;
    %"chk112" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1070";
    %"v1071" : W = (RawLoad (LdNarrow Sw) 0) %"chk112";
    %"v1072" : L = (Ext Sw) %"v1071";
    %"v1073" : L = Shl %"v1072", #4;
    %"v1074" = %"pr.16" +p %"v1073";
    %"chk113" : A = (Check 0 4 Read 1) %"v1074";
    %"v1075" : W = (RawLoad (LdNarrow Uw) 0) %"chk113";
    %"v1076" : W = (Ext Sh) %"v1075";
    %"v1077" : L = (Ext Sw) %"v1076"
    => goto "L1014" };
  ir_blk{ @"L1014" [%"pr.95" : L = phi("L1012" => %"v1027", "L1028" => %"v1045", "L1046" => %"v1063", "L1047" => %"v1077")]:
    %"v1079" : W = (Cmp Slt L) %"pr.95", #0
    => br %"v1079" ? "L1080" : "L1088" };
  ir_blk{ @"L1080":
    %"v1085" : L = Neg %"pr.95"
    => goto "L1088" };
  ir_blk{ @"L1090" [%"pr.48" : W = phi("L2040" => #10, "L2048" => #8, "L2050" => #16, "L2071" => #2)]:
    => br %"v696" ? "L1147" : "L1148" };
  ir_blk{ @"L1147":
    %"v1157" = %"v612" +p #48;
    %"chk114" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1157";
    %"v1158" : W = (RawLoad (LdNarrow Sw) 0) %"chk114";
    %"v1159" : L = (Ext Sw) %"v1158";
    %"v1160" : L = Shl %"v1159", #4;
    %"v1161" = %"pr.16" +p %"v1160";
    %"chk115" : A = (Check 0 8 Read 1) %"v1161";
    %"v1162" : L = (RawLoad LdL 0) %"chk115"
    => goto "L1088" };
  ir_blk{ @"L1148":
    => br %"v686" ? "L1163" : "L1164" };
  ir_blk{ @"L1163":
    %"v1173" = %"v612" +p #48;
    %"chk116" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1173";
    %"v1174" : W = (RawLoad (LdNarrow Sw) 0) %"chk116";
    %"v1175" : L = (Ext Sw) %"v1174";
    %"v1176" : L = Shl %"v1175", #4;
    %"v1177" = %"pr.16" +p %"v1176";
    %"chk117" : A = (Check 0 4 Read 1) %"v1177";
    %"v1178" : W = (RawLoad (LdNarrow Uw) 0) %"chk117";
    %"v1179" : W = (Ext Ub) %"v1178";
    %"v1180" : L = (Ext Uw) %"v1179"
    => goto "L1088" }] [ir_blk{ @"L1164":
    %"v1185" : W = (Cmp Eq W) %"v676", #0
    => br %"v1185" ? "L1181" : "L1182" };
  ir_blk{ @"L1181":
    %"v1192" = %"v612" +p #48;
    %"chk118" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1192";
    %"v1193" : W = (RawLoad (LdNarrow Sw) 0) %"chk118";
    %"v1194" : L = (Ext Sw) %"v1193";
    %"v1195" : L = Shl %"v1194", #4;
    %"v1196" = %"pr.16" +p %"v1195";
    %"chk119" : A = (Check 0 4 Read 1) %"v1196";
    %"v1197" : W = (RawLoad (LdNarrow Uw) 0) %"chk119";
    %"v1198" : L = (Ext Uw) %"v1197"
    => goto "L1088" };
  ir_blk{ @"L1182":
    %"v1205" = %"v612" +p #48;
    %"chk120" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1205";
    %"v1206" : W = (RawLoad (LdNarrow Sw) 0) %"chk120";
    %"v1207" : L = (Ext Sw) %"v1206";
    %"v1208" : L = Shl %"v1207", #4;
    %"v1209" = %"pr.16" +p %"v1208";
    %"chk121" : A = (Check 0 4 Read 1) %"v1209";
    %"v1210" : W = (RawLoad (LdNarrow Uw) 0) %"chk121";
    %"v1211" : W = (Ext Uh) %"v1210";
    %"v1212" : L = (Ext Uw) %"v1211"
    => goto "L1088" };
  ir_blk{ @"L1088" [%"pr.93" : W = phi("L1080" => %"v739", "L1014" => %"v739", "L1147" => %"v739", "L1163" => %"v739", "L1181" => %"v739", "L1182" => %"v739", "L1603" => #120, "L1739" => %"v739", "L1728" => %"v739"); %"pr.69" : W = phi("L1080" => %"v656", "L1014" => %"v656", "L1147" => %"v656", "L1163" => %"v656", "L1181" => %"v656", "L1182" => %"v656", "L1603" => #0, "L1739" => %"v656", "L1728" => %"v656"); %"pr.67" : W = phi("L1080" => %"v646", "L1014" => %"v646", "L1147" => #0, "L1163" => #0, "L1181" => #0, "L1182" => #0, "L1603" => %"v646", "L1739" => %"v646", "L1728" => %"v646"); %"pr.62" : W = phi("L1080" => %"v626", "L1014" => %"v626", "L1147" => #0, "L1163" => #0, "L1181" => #0, "L1182" => #0, "L1603" => %"v626", "L1739" => %"v626", "L1728" => %"v626"); %"pr.59" : W = phi("L1080" => %"v616", "L1014" => %"v616", "L1147" => %"v616", "L1163" => %"v616", "L1181" => %"v616", "L1182" => %"v616", "L1603" => #1, "L1739" => %"v616", "L1728" => %"v616"); %"pr.47" : W = phi("L1080" => #10, "L1014" => #10, "L1147" => %"pr.48", "L1163" => %"pr.48", "L1181" => %"pr.48", "L1182" => %"pr.48", "L1603" => #16, "L1739" => #10, "L1728" => #10); %"pr.40" : L = phi("L1080" => %"v1085", "L1014" => %"pr.95", "L1147" => %"v1162", "L1163" => %"v1180", "L1181" => %"v1198", "L1182" => %"v1212", "L1603" => %"v1621", "L1739" => %"v1744", "L1728" => %"v1738"); %"pr.37" : W = phi("L1080" => %"v1079", "L1014" => %"v1079", "L1147" => #0, "L1163" => #0, "L1181" => #0, "L1182" => #0, "L1603" => #0, "L1739" => %"v1736", "L1728" => %"v1736")]:
    %"v1217" : W = (Cmp Slt W) %"pr.89", #0
    => br %"v1217" ? "L1215" : "L1214" };
  ir_blk{ @"L1214":
    => goto "L1215" };
  ir_blk{ @"L1215" [%"pr.92" : W = phi("L1214" => #32, "L1088" => %"v730"); %"pr.86" : W = phi("L1214" => %"pr.89", "L1088" => #1)]:
    %"v1222" : W = (Cmp Eq W) %"pr.86", #0
    => br %"v1222" ? "L1223" : "L1224" };
  ir_blk{ @"L1223":
    %"v1226" : W = (Cmp Eq L) %"pr.40", #0
    => goto "L1224" };
  ir_blk{ @"L1224" [%"v1228" : W = phi("L1215" => #0, "L1223" => %"v1226")]:
    => br %"v1228" ? "L1218" : "L1219" };
  ir_blk{ @"L1218":
    %"v1234" : W = (Cmp Eq W) %"pr.47", #8
    => br %"v1234" ? "L1235" : "L1236" };
  ir_blk{ @"L1235":
    %"v1238" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1236" };
  ir_blk{ @"L1236" [%"v1239" : W = phi("L1218" => #0, "L1235" => %"v1238")]:
    => br %"v1239" ? "L1230" : "L1220" };
  ir_blk{ @"L1230":
    (Flight (a "v1241") Sub [(FAddress (t "v742")); (FValue (Const 1))] (LowerOf (t "v742")));
    %"chk122" : A = (Check 0 1 Write 1) %"v1241";
    store Wb [%"chk122" + 0] <- #48
    => goto "L1220" };
  ir_blk{ @"L1219":
    %"v1245" : W = (Ext Sb) %"pr.93";
    %"v1246" : W = (Cmp Eq W) %"v1245", #88;
    call %"v1247" : P = $"_itoa_word"(L %"pr.40", P %"v742", W %"pr.47", W %"v1246")
    => goto "L1220" };
  ir_blk{ @"L1220" [%"pr.53" : P = phi("L1219" => %"v1247", "L1230" => %"v1241", "L1236" => %"v742")]:
    => br %"pr.69" ? "L1252" : "L1251" };
  ir_blk{ @"L1251":
    => br %"v721" ? "L1254" : "L1252" };
  ir_blk{ @"L1254":
    %"v1257" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1252" };
  ir_blk{ @"L1252" [%"v1261" : W = phi("L1220" => #1, "L1251" => #0, "L1254" => %"v1257")]:
    => br %"pr.69" ? "L1263" : "L1264" };
  ir_blk{ @"L1263":
    %"v1267" : P = Copy $"__libc_tsd_LOCALE";
    %"chk123" : A = (Check 0 8 Read 8) %"v1267";
    %"v1268" : P = (RawLoadPointer 0 load_effects) %"chk123";
    %"v1271" : L = Ptoi %"v742";
    %"v1272" : L = Ptoi %"pr.53";
    %"v1273" : L = Sub %"v1271", %"v1272";
    call %"v1274" : W = $"__grouping_iterator_init"(P %"v1248", W #1, P %"v1268", W %"v1273")
    => goto "L1265" };
  ir_blk{ @"L1264":
    => br %"v721" ? "L1280" : "L1281" };
  ir_blk{ @"L1280":
    %"v1283" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1281" };
  ir_blk{ @"L1281" [%"v1285" : W = phi("L1264" => #0, "L1280" => %"v1283")]:
    => br %"v1285" ? "L1276" : "L1265" };
  ir_blk{ @"L1276":
    %"v1288" : L = Ptoi %"v742";
    %"v1289" : L = Ptoi %"pr.53";
    %"v1290" : L = Sub %"v1288", %"v1289";
    call %"v1291" : W = $"__grouping_iterator_init_none"(P %"v1248", W %"v1290")
    => goto "L1265" };
  ir_blk{ @"L1265":
    => br %"v721" ? "L1298" : "L1299" };
  ir_blk{ @"L1298":
    %"v1301" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1299" };
  ir_blk{ @"L1299" [%"v1303" : W = phi("L1265" => #0, "L1298" => %"v1301")]:
    => br %"v1303" ? "L1294" : "L1295" };
  ir_blk{ @"L1294":
    %"v1304" : P = Copy $"__libc_tsd_LOCALE";
    %"chk124" : A = (Check 0 8 Read 8) %"v1304";
    %"v1305" : P = (RawLoadPointer 0 load_effects) %"chk124";
    call %"v1308" : W = $"__translated_number_width"(P %"v1305", P %"pr.53", P %"v742")
    => goto "L1296" };
  ir_blk{ @"L1295":
    %"v1311" : L = Ptoi %"v742";
    %"v1312" : L = Ptoi %"pr.53";
    %"v1313" : L = Sub %"v1311", %"v1312"
    => goto "L1296" };
  ir_blk{ @"L1296" [%"pr.98" : W = phi("L1294" => %"v1308", "L1295" => %"v1313")]:
    => br %"pr.69" ? "L1314" : "L1316" };
  ir_blk{ @"L1314":
    %"v1319" = %"v1248" +p #20;
    %"chk125" : A = (Check 0 4 Read 1) %"v1319";
    %"v1320" : W = (RawLoad (LdNarrow Uw) 0) %"chk125";
    call %"v1322" : L = $"__GI_strlen"(P %"pr.6");
    %"v1323" : L = (Ext Uw) %"v1320";
    %"v1324" : L = Mul %"v1323", %"v1322";
    %"v1325" : L = (Ext Sw) %"pr.98";
    %"v1326" : L = Add %"v1325", %"v1324"
    => goto "L1316" };
  ir_blk{ @"L1316" [%"pr.99" : W = phi("L1314" => %"v1326", "L1296" => %"pr.98")]:
    %"v1330" : W = (Cmp Sle W) %"pr.86", %"pr.99"
    => br %"v1330" ? "L1331" : "L1332" };
  ir_blk{ @"L1331":
    %"v1334" : W = (Cmp Ne L) %"pr.40", #0
    => goto "L1332" };
  ir_blk{ @"L1332" [%"v1336" : W = phi("L1316" => #0, "L1331" => %"v1334")]:
    => br %"v1336" ? "L1337" : "L1338" };
  ir_blk{ @"L1337":
    %"v1340" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1338" };
  ir_blk{ @"L1338" [%"v1341" : W = phi("L1332" => #0, "L1337" => %"v1340")]:
    => br %"v1341" ? "L1342" : "L1343" };
  ir_blk{ @"L1342":
    %"v1345" : W = (Cmp Eq W) %"pr.47", #8
    => goto "L1343" };
  ir_blk{ @"L1343" [%"v1347" : W = phi("L1338" => #0, "L1342" => %"v1345")]:
    %"v1356" : L = Ptoi %"v742";
    %"v1357" : L = Ptoi %"pr.53";
    %"v1358" : L = Sub %"v1356", %"v1357";
    %"v1359" : L = (Ext Sw) %"pr.86";
    %"v1360" : L = Sub %"v1359", %"v1358";
    %"v1361" : W = (Cmp Slt L) %"v1360", #0
    => br %"v1361" ? "L1352" : "L1351" }])) (app (app [ir_blk{ @"L1351":
    => goto "L1352" };
  ir_blk{ @"L1352" [%"v1370" : L = phi("L1351" => %"v1360", "L1343" => #0)]:
    %"v1375" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1375" ? "L1371" : "L1372" };
  ir_blk{ @"L1371":
    %"v1378" : W = Copy %"v1370";
    %"v1379" : W = Add %"pr.99", %"v1378";
    %"v1380" : W = Sub %"pr.81", %"v1379";
    %"v1385" : W = (Cmp Ne L) %"pr.40", #0
    => br %"v1385" ? "L1386" : "L1387" };
  ir_blk{ @"L1386":
    %"v1389" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1387" };
  ir_blk{ @"L1387" [%"v1390" : W = phi("L1371" => #0, "L1386" => %"v1389")]:
    => br %"v1390" ? "L1391" : "L1392" };
  ir_blk{ @"L1391":
    %"v1394" : W = (Cmp Eq W) %"pr.47", #16
    => br %"v1394" ? "L1392" : "L1395" };
  ir_blk{ @"L1395":
    %"v1398" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L1392" };
  ir_blk{ @"L1392" [%"v1402" : W = phi("L1387" => #0, "L1391" => #1, "L1395" => %"v1398")]:
    => br %"v1402" ? "L1381" : "L1383" };
  ir_blk{ @"L1381":
    %"v1404" : W = Sub %"v1380", #2
    => goto "L1383" };
  ir_blk{ @"L1383" [%"pr.72" : W = phi("L1381" => %"v1404", "L1392" => %"v1380")]:
    => br %"v1347" ? "L1405" : "L1407" };
  ir_blk{ @"L1405":
    %"v1410" : W = Sub %"pr.72", #1
    => goto "L1407" };
  ir_blk{ @"L1407" [%"pr.73" : W = phi("L1405" => %"v1410", "L1383" => %"pr.72")]:
    => br %"pr.37" ? "L1416" : "L1415" };
  ir_blk{ @"L1415":
    %"v1418" : W = (Cmp Ne W) %"pr.67", #0
    => goto "L1416" };
  ir_blk{ @"L1416" [%"v1419" : W = phi("L1407" => #1, "L1415" => %"v1418")]:
    => br %"v1419" ? "L1421" : "L1420" };
  ir_blk{ @"L1420":
    %"v1423" : W = (Cmp Ne W) %"pr.62", #0
    => goto "L1421" };
  ir_blk{ @"L1421" [%"v1424" : W = phi("L1416" => #1, "L1420" => %"v1423")]:
    => br %"v1424" ? "L1411" : "L1413" };
  ir_blk{ @"L1411":
    %"v1426" : W = Sub %"pr.73", #1
    => goto "L1413" };
  ir_blk{ @"L1413" [%"pr.74" : W = phi("L1411" => %"v1426", "L1421" => %"pr.73")]:
    %"v1430" : W = (Ext Sb) %"pr.92";
    %"v1431" : W = (Cmp Eq W) %"v1430", #32
    => br %"v1431" ? "L1427" : "L1429" };
  ir_blk{ @"L1427":
    %"v1434" : L = (Ext Sw) %"pr.74";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1434")
    => goto "L1429" };
  ir_blk{ @"L1429" [%"pr.75" : W = phi("L1427" => #0, "L1413" => %"pr.74")]:
    => br %"pr.37" ? "L1435" : "L1436" };
  ir_blk{ @"L1435":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #45)
    => goto "L1437" };
  ir_blk{ @"L1436":
    => br %"pr.67" ? "L1440" : "L1441" };
  ir_blk{ @"L1440":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #43)
    => goto "L1437" };
  ir_blk{ @"L1441":
    => br %"pr.62" ? "L1445" : "L1437" };
  ir_blk{ @"L1445":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #32)
    => goto "L1437" };
  ir_blk{ @"L1437":
    => br %"v1385" ? "L1455" : "L1456" };
  ir_blk{ @"L1455":
    %"v1458" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1456" };
  ir_blk{ @"L1456" [%"v1459" : W = phi("L1437" => #0, "L1455" => %"v1458")]:
    => br %"v1459" ? "L1460" : "L1461" };
  ir_blk{ @"L1460":
    %"v1463" : W = (Cmp Eq W) %"pr.47", #16
    => br %"v1463" ? "L1461" : "L1464" };
  ir_blk{ @"L1464":
    %"v1467" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L1461" };
  ir_blk{ @"L1461" [%"v1471" : W = phi("L1456" => #0, "L1460" => #1, "L1464" => %"v1467")]:
    => br %"v1471" ? "L1450" : "L1452" };
  ir_blk{ @"L1450":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48);
    %"v1474" : W = (Ext Sb) %"pr.93";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v1474")
    => goto "L1452" };
  ir_blk{ @"L1452":
    %"v1476" : W = Copy %"v1370";
    %"v1477" : W = Add %"pr.75", %"v1476";
    %"v1480" : L = (Ext Sw) %"v1477";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #48, L %"v1480")
    => br %"v1347" ? "L1481" : "L1483" };
  ir_blk{ @"L1481":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48)
    => goto "L1483" };
  ir_blk{ @"L1483":
    => br %"v1261" ? "L1486" : "L1487" };
  ir_blk{ @"L1486":
    => br %"v721" ? "L1495" : "L1496" }] [ir_blk{ @"L1495":
    %"v1498" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1496" };
  ir_blk{ @"L1496" [%"v1500" : W = phi("L1486" => #0, "L1495" => %"v1498")]:
    call void $"glibc_vfprintf_internal#group_number"(P %"v0", P %"v1248", P %"pr.53", P %"v742", P %"pr.6", W %"v1500")
    => goto "L866" };
  ir_blk{ @"L1487":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.53", L %"v1358")
    => goto "L866" };
  ir_blk{ @"L1372":
    => br %"pr.37" ? "L1510" : "L1511" };
  ir_blk{ @"L1510":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #45);
    %"v1516" : W = Sub %"pr.81", #1
    => goto "L1512" };
  ir_blk{ @"L1511":
    => br %"pr.67" ? "L1517" : "L1518" };
  ir_blk{ @"L1517":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #43);
    %"v1523" : W = Sub %"pr.81", #1
    => goto "L1512" };
  ir_blk{ @"L1518":
    => br %"pr.62" ? "L1524" : "L1512" };
  ir_blk{ @"L1524":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #32);
    %"v1530" : W = Sub %"pr.81", #1
    => goto "L1512" };
  ir_blk{ @"L1512" [%"pr.76" : W = phi("L1510" => %"v1516", "L1517" => %"v1523", "L1524" => %"v1530", "L1518" => %"pr.81")]:
    %"v1535" : W = (Cmp Ne L) %"pr.40", #0
    => br %"v1535" ? "L1536" : "L1537" };
  ir_blk{ @"L1536":
    %"v1539" : W = (Cmp Ne W) %"pr.59", #0
    => goto "L1537" };
  ir_blk{ @"L1537" [%"v1540" : W = phi("L1512" => #0, "L1536" => %"v1539")]:
    => br %"v1540" ? "L1541" : "L1542" };
  ir_blk{ @"L1541":
    %"v1544" : W = (Cmp Eq W) %"pr.47", #16
    => br %"v1544" ? "L1542" : "L1545" };
  ir_blk{ @"L1545":
    %"v1548" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L1542" };
  ir_blk{ @"L1542" [%"v1552" : W = phi("L1537" => #0, "L1541" => #1, "L1545" => %"v1548")]:
    => br %"v1552" ? "L1531" : "L1533" };
  ir_blk{ @"L1531":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48);
    %"v1555" : W = (Ext Sb) %"pr.93";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v1555");
    %"v1557" : W = Sub %"pr.76", #2
    => goto "L1533" };
  ir_blk{ @"L1533" [%"pr.79" : W = phi("L1531" => %"v1557", "L1542" => %"pr.76")]:
    => br %"v1347" ? "L1558" : "L1560" };
  ir_blk{ @"L1558":
    %"v1563" : W = Sub %"pr.79", #1
    => goto "L1560" };
  ir_blk{ @"L1560" [%"pr.80" : W = phi("L1558" => %"v1563", "L1533" => %"pr.79")]:
    %"v1566" : W = Copy %"v1370";
    %"v1567" : W = Add %"pr.99", %"v1566";
    %"v1568" : W = Sub %"pr.80", %"v1567";
    %"v1570" : W = Copy %"v1370";
    %"v1571" : L = (Ext Uw) %"v1570";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #48, L %"v1571")
    => br %"v1347" ? "L1572" : "L1574" };
  ir_blk{ @"L1572":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48)
    => goto "L1574" };
  ir_blk{ @"L1574":
    => br %"v1261" ? "L1577" : "L1578" };
  ir_blk{ @"L1577":
    => br %"v721" ? "L1586" : "L1587" };
  ir_blk{ @"L1586":
    %"v1589" : W = (Cmp Eq W) %"pr.47", #10
    => goto "L1587" };
  ir_blk{ @"L1587" [%"v1591" : W = phi("L1577" => #0, "L1586" => %"v1589")]:
    call void $"glibc_vfprintf_internal#group_number"(P %"v0", P %"v1248", P %"pr.53", P %"v742", P %"pr.6", W %"v1591")
    => goto "L1579" };
  ir_blk{ @"L1578":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.53", L %"v1358")
    => goto "L1579" };
  ir_blk{ @"L1579":
    %"v1602" : L = (Ext Sw) %"v1568";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1602")
    => goto "L866" };
  ir_blk{ @"L1603":
    %"v1611" = %"v612" +p #48;
    %"chk126" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1611";
    %"v1612" : W = (RawLoad (LdNarrow Sw) 0) %"chk126";
    %"v1613" : L = (Ext Sw) %"v1612";
    %"v1614" : L = Shl %"v1613", #4;
    %"v1615" = %"pr.16" +p %"v1614";
    %"chk127" : A = (Check 0 8 Read 8) %"v1615";
    %"v1616" : P = (RawLoadPointer 0 load_effects) %"chk127";
    %"v1621" : L = Ptoi %"v1616";
    %"v1623" : W = (Cmp Ne L) %"v1621", %"v875"
    => br %"v1623" ? poll "L1088" : "L1618" };
  ir_blk{ @"L1618":
    %"v1627" : P = Copy $"glibc_vfprintf_internal#str.284";
    %"v1632" : W = (Cmp Slt W) %"pr.89", #5
    => br %"v1632" ? "L1634" : "L1629" };
  ir_blk{ @"L1629":
    => goto "L1634" };
  ir_blk{ @"L1635":
    => br %"v176" ? "L1636" : "L1638" };
  ir_blk{ @"L1636":
    %"v1646" : W = (Cmp Eq W) %"pr.3", #0
    => br %"v1646" ? "L1642" : "L1644" };
  ir_blk{ @"L1642":
    call %"v1649" : L = $"__GI_strlen"(P %"v2");
    %"v1650" : L = Add %"v1649", #1;
    call %"v1652" : W = $"__readonly_area"(P %"v2", L %"v1650")
    => goto "L1644" };
  ir_blk{ @"L1644" [%"pr.2" : W = phi("L1642" => %"v1652", "L1636" => %"pr.3")]:
    %"v1663" : W = (Cmp Eq W) %"pr.2", #1
    => br %"v1663" ? "L1656" : "L1664" };
  ir_blk{ @"L1656":
    %"v1657" : P = Copy $"glibc_vfprintf_internal#str.285";
    call void $"__GI___libc_fatal"(P %"v1657")
    => goto "L1658" };
  ir_blk{ @"L1658":
    %"v1659" : P = Copy $"glibc_vfprintf_internal#str.286";
    call void $"__GI___libc_fatal"(P %"v1659")
    => goto "L1638" };
  ir_blk{ @"L1664":
    %"v1665" : W = (Cmp Eq W) %"pr.2", #3
    => br %"v1665" ? poll "L1658" : "L1666" }]) (app [ir_blk{ @"L1666":
    %"v1667" : W = (Cmp Eq W) %"pr.2", #2
    => br %"v1667" ? "L1638" : "L1668" };
  ir_blk{ @"L1668":
    %"v1669" : W = (Cmp Eq W) %"pr.2", #0
    => br %"v1669" ? "L1638" : "L1670" };
  ir_blk{ @"L1670":
    => goto "L1638" };
  ir_blk{ @"L1638" [%"pr.1" : W = phi("L1670" => %"pr.2", "L1668" => %"pr.2", "L1658" => %"pr.2", "L1666" => %"pr.2", "L1635" => %"pr.3")]:
    %"v1678" = %"v612" +p #48;
    %"chk128" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1678";
    %"v1679" : W = (RawLoad (LdNarrow Sw) 0) %"chk128";
    %"v1680" : L = (Ext Sw) %"v1679";
    %"v1681" : L = Shl %"v1680", #4;
    %"v1682" = %"pr.16" +p %"v1681";
    %"chk129" : A = (Check 0 8 Read 8) %"v1682";
    %"v1683" : P = (RawLoadPointer 0 load_effects) %"chk129";
    call %"v1686" : W = $"__printf_buffer_done"(P %"v0")
    => br %"v696" ? "L1693" : "L1694" };
  ir_blk{ @"L1693":
    %"v1699" : L = (Ext Uw) %"v1686";
    %"chk130" : A = (Check 0 8 Write 1) %"v1683";
    store Wl [%"chk130" + 0] <- %"v1699"
    => goto "L866" };
  ir_blk{ @"L1694":
    => br %"v686" ? "L1700" : "L1701" };
  ir_blk{ @"L1700":
    %"v1706" : W = (Ext Sb) %"v1686";
    %"chk131" : A = (Check 0 1 Write 1) %"v1683";
    store Wb [%"chk131" + 0] <- %"v1706"
    => goto "L866" };
  ir_blk{ @"L1701":
    %"v1711" : W = (Cmp Eq W) %"v676", #0
    => br %"v1711" ? "L1707" : "L1708" };
  ir_blk{ @"L1707":
    %"chk132" : A = (Check 0 4 Write 1) %"v1683";
    store Ww [%"chk132" + 0] <- %"v1686"
    => goto "L866" };
  ir_blk{ @"L1708":
    %"v1716" : W = (Ext Sh) %"v1686";
    %"chk133" : A = (Check 0 2 Write 1) %"v1683";
    store Wh [%"chk133" + 0] <- %"v1716"
    => goto "L866" };
  ir_blk{ @"L1717":
    => br %"v616" ? "L1718" : "L1719" };
  ir_blk{ @"L1718":
    call %"v1723" : P = $"__get_errname"(W %"v16")
    => goto "L1720" };
  ir_blk{ @"L1719":
    call %"v1727" : P = $"__GI___strerror_r"(W %"v16", P %"v14", L #1000)
    => goto "L1720" };
  ir_blk{ @"L1720" [%"pr.56" : P = phi("L1718" => %"v1723", "L1719" => %"v1727")]:
    %"v1732" : L = Ptoi %"pr.56";
    %"v1734" : W = (Cmp Eq L) %"v1732", %"v875"
    => br %"v1734" ? "L1728" : "L1634" };
  ir_blk{ @"L1728":
    %"v1736" : W = (Cmp Slt W) %"v16", #0;
    %"v1738" : L = (Ext Sw) %"v16"
    => br %"v1736" ? "L1739" : poll "L1088" };
  ir_blk{ @"L1739":
    %"v1744" : L = Neg %"v1738"
    => goto poll "L1088" };
  ir_blk{ @"L1746":
    => br %"v696" ? "L1751" : "L1749" };
  ir_blk{ @"L1749":
    %"v1754" : W = Sub %"pr.81", #1;
    %"v1759" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1759" ? "L1755" : "L1757" };
  ir_blk{ @"L1755":
    %"v1762" : L = (Ext Sw) %"v1754";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1762")
    => goto "L1757" };
  ir_blk{ @"L1757":
    %"v1770" = %"v612" +p #48;
    %"chk134" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1770";
    %"v1771" : W = (RawLoad (LdNarrow Sw) 0) %"chk134";
    %"v1772" : L = (Ext Sw) %"v1771";
    %"v1773" : L = Shl %"v1772", #4;
    %"v1774" = %"pr.16" +p %"v1773";
    %"chk135" : A = (Check 0 4 Read 1) %"v1774";
    %"v1775" : W = (RawLoad (LdNarrow Sw) 0) %"chk135";
    %"v1776" : W = (Ext Ub) %"v1775";
    %"v1777" : W = (Ext Sb) %"v1776";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v1777")
    => br %"pr.64" ? "L1778" : "L866" };
  ir_blk{ @"L1778":
    %"v1784" : L = (Ext Sw) %"v1754";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1784")
    => goto "L866" };
  ir_blk{ @"L1785":
    %"v1793" = %"v612" +p #48;
    %"chk136" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1793";
    %"v1794" : W = (RawLoad (LdNarrow Sw) 0) %"chk136";
    %"v1795" : L = (Ext Sw) %"v1794";
    %"v1796" : L = Shl %"v1795", #4;
    %"v1797" = %"pr.16" +p %"v1796";
    %"chk137" : A = (Check 0 8 Read 8) %"v1797";
    %"v1798" : P = (RawLoadPointer 0 load_effects) %"chk137"
    => goto "L1634" };
  ir_blk{ @"L1634" [%"pr.88" : W = phi("L1785" => %"pr.89", "L1629" => %"pr.89", "L1618" => #5, "L1720" => %"pr.89"); %"pr.71" : W = phi("L1785" => %"v696", "L1629" => #0, "L1618" => #0, "L1720" => #0); %"pr.55" : P = phi("L1785" => %"v1798", "L1629" => %"v1627", "L1618" => %"v1627", "L1720" => %"pr.56")]:
    %"v1803" : L = Ptoi %"pr.55";
    %"v1805" : W = (Cmp Eq L) %"v1803", %"v875"
    => br %"v1805" ? "L1799" : "L1800" };
  ir_blk{ @"L1799":
    %"v1811" : W = (Cmp Eq W) %"pr.88", #4294967295
    => br %"v1811" ? "L1813" : "L1812" };
  ir_blk{ @"L1812":
    %"v1819" : W = (Cmp Sge W) %"pr.88", #6
    => goto "L1813" };
  ir_blk{ @"L1813" [%"v1821" : W = phi("L1799" => #1, "L1812" => %"v1819")]:
    => br %"v1821" ? "L1806" : "L1807" };
  ir_blk{ @"L1806":
    %"v1822" : P = Copy $"glibc_vfprintf_internal#null"
    => goto "L1801" };
  ir_blk{ @"L1807":
    %"v1827" : P = Copy $"glibc_vfprintf_internal#str.289"
    => goto "L1801" };
  ir_blk{ @"L1800":
    %"v1832" : W = (Cmp Eq W) %"pr.71", #0
    => br %"v1832" ? "L1833" : "L1834" };
  ir_blk{ @"L1833":
    %"v1836" : W = (Cmp Ne W) %"v739", #83
    => goto "L1834" };
  ir_blk{ @"L1834" [%"v1838" : W = phi("L1800" => #0, "L1833" => %"v1836")]:
    => br %"v1838" ? "L1828" : "L1829" };
  ir_blk{ @"L1828":
    %"v1844" : W = (Cmp Ne W) %"pr.88", #4294967295
    => br %"v1844" ? "L1839" : "L1840" };
  ir_blk{ @"L1839":
    %"v1847" : L = (Ext Sw) %"pr.88";
    call %"v1848" : L = $"__GI___strnlen"(P %"pr.55", L %"v1847")
    => goto "L1841" };
  ir_blk{ @"L1840":
    call %"v1850" : L = $"__GI_strlen"(P %"pr.55")
    => goto "L1841" };
  ir_blk{ @"L1841" [%"pr.103" : L = phi("L1839" => %"v1848", "L1840" => %"v1850")]:
    => goto "L1801" };
  ir_blk{ @"L1829":
    %"v1856" : W = (Cmp Ne W) %"pr.64", #0;
    call void $"glibc_vfprintf_internal#outstring_converted_wide_string"(P %"v0", P %"pr.55", W %"pr.88", W %"pr.81", W %"v1856")
    => goto "L866" }] [ir_blk{ @"L1801" [%"pr.101" : L = phi("L1806" => #6, "L1807" => #0, "L1841" => %"pr.103"); %"pr.57" : P = phi("L1806" => %"v1822", "L1807" => %"v1827", "L1841" => %"pr.55")]:
    %"v1862" : L = (Ext Sw) %"pr.81";
    %"v1863" : L = Sub %"v1862", %"pr.101";
    %"v1864" : W = (Cmp Slt W) %"v1863", #0
    => br %"v1864" ? "L1857" : "L1859" };
  ir_blk{ @"L1857":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.57", L %"pr.101")
    => goto "L866" };
  ir_blk{ @"L1859":
    %"v1873" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1873" ? "L1869" : "L1871" };
  ir_blk{ @"L1869":
    %"v1875" : W = Copy %"v1863";
    %"v1876" : L = (Ext Sw) %"v1875";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1876")
    => goto "L1871" };
  ir_blk{ @"L1871":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.57", L %"pr.101")
    => br %"pr.64" ? "L1880" : "L866" };
  ir_blk{ @"L1880":
    %"v1885" : W = Copy %"v1863";
    %"v1886" : L = (Ext Sw) %"v1885";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1886")
    => goto "L866" };
  ir_blk{ @"L1751":
    call %"v1890" : P = $"__GI_memset"(P %"v1888", W #0, L #8);
    %"v1897" = %"v612" +p #48;
    %"chk138" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1897";
    %"v1898" : W = (RawLoad (LdNarrow Sw) 0) %"chk138";
    %"v1899" : L = (Ext Sw) %"v1898";
    %"v1900" : L = Shl %"v1899", #4;
    %"v1901" = %"pr.16" +p %"v1900";
    %"chk139" : A = (Check 0 4 Read 1) %"v1901";
    %"v1902" : W = (RawLoad (LdNarrow Sw) 0) %"chk139";
    call %"v1903" : L = $"__wcrtomb"(P %"v1887", W %"v1902", P %"v1888");
    %"v1910" : W = (Cmp Eq L) %"v1903", #18446744073709551615
    => br %"v1910" ? "L1904" : "L1906" };
  ir_blk{ @"L1904":
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L101" };
  ir_blk{ @"L1906":
    %"v1915" : L = (Ext Sw) %"pr.81";
    %"v1916" : L = Sub %"v1915", %"v1903";
    %"v1921" : W = (Cmp Eq W) %"pr.64", #0
    => br %"v1921" ? "L1917" : "L1919" };
  ir_blk{ @"L1917":
    %"v1923" : W = Copy %"v1916";
    %"v1924" : L = (Ext Sw) %"v1923";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1924")
    => goto "L1919" };
  ir_blk{ @"L1919":
    call void $"__printf_buffer_write"(P %"v0", P %"v1887", L %"v1903")
    => br %"pr.64" ? "L1927" : "L866" };
  ir_blk{ @"L1927":
    %"v1932" : W = Copy %"v1916";
    %"v1933" : L = (Ext Sw) %"v1932";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1933")
    => goto "L866" };
  ir_blk{ @"L1935":
    %"v1943" = %"v612" +p #48;
    %"chk140" : A = (HalfCheck Upper 0 4 Read 1) %"chk66", %"v1943";
    %"v1944" : W = (RawLoad (LdNarrow Sw) 0) %"chk140";
    %"v1945" : L = (Ext Sw) %"v1944";
    %"v1946" : L = Shl %"v1945", #4;
    %"v1947" = %"pr.16" +p %"v1946";
    %"chk141" : A = (Check 0 8 Write 8) %"v1936";
    store.ptr [%"chk141" + 0] <- %"v1947";
    %"v1952" : W = And %"v22", #1
    => br %"v1952" ? "L1948" : "L1974" };
  ir_blk{ @"L1948":
    %"v1961" = %"v612" +p #52;
    %"chk142" : A = (HalfCheck Upper 0 4 Write 1) %"chk66", %"v1961";
    store Ww [%"chk142" + 0] <- #7;
    %"v1967" = %"v612" +p #12;
    %"chk143" : A = (Renew 0 4 Read 1) %"chk66", %"v1967";
    %"v1968" : W = (RawLoad (LdNarrow Uw) 0) %"chk143";
    %"v1969" : W = And %"v1968", #4294967294;
    store Ww [%"chk143" + 0] <- %"v1969"
    => goto "L1974" };
  ir_blk{ @"L1974":
    %"v1982" = %"v612" +p #12;
    %"chk145" : A = (Renew 0 4 Read 1) %"chk66", %"v1982";
    %"v1983" : W = (RawLoad (LdNarrow Uw) 0) %"chk145";
    %"v1984" : W = And %"v1983", #4294963199;
    %"chk146" : A = (Renew 0 4 Write 1) %"chk66", %"v1982";
    store Ww [%"chk146" + 0] <- %"v1984";
    call void $"glibc_vfprintf_internal#__printf_fp_spec"(P %"v0", P %"v612", P %"v1936")
    => goto "L866" };
  ir_blk{ @"L1996":
    call void $"glibc_vfprintf_internal#printf_unknown"(P %"v0", P %"v612")
    => goto "L866" };
  ir_blk{ @"L866" [%"pr.4" : W = phi("L1579" => %"pr.3", "L1829" => %"pr.3", "L1857" => %"pr.3", "L1974" => %"pr.3", "L1996" => %"pr.3", "L980" => %"pr.3", "L926" => %"pr.3", "L1496" => %"pr.3", "L1487" => %"pr.3", "L1693" => %"pr.1", "L1700" => %"pr.1", "L1707" => %"pr.1", "L1708" => %"pr.1", "L1778" => %"pr.3", "L1757" => %"pr.3", "L1880" => %"pr.3", "L1871" => %"pr.3", "L1927" => %"pr.3", "L1919" => %"pr.3")]:
    %"v2012" = %"v612" +p #24;
    %"chk147" : A = (HalfCheck Upper 0 8 Read 8) %"chk66", %"v2012";
    %"v2013" : P = (RawLoadPointer 0 load_effects) %"chk147";
    %"v2019" = %"v612" +p #32;
    %"chk148" : A = (HalfCheck Upper 0 8 Read 8) %"chk66", %"v2019";
    %"v2020" : P = (RawLoadPointer 0 load_effects) %"chk148";
    %"v2027" : P = (RawLoadPointer 0 load_effects) %"chk147";
    %"v2028" : L = Ptoi %"v2020";
    %"v2029" : L = Ptoi %"v2027";
    %"v2030" : L = Sub %"v2028", %"v2029";
    call void $"__printf_buffer_write"(P %"v0", P %"v2013", L %"v2030");
    %"v2032" : W = Add %"pr.5", #1
    => goto poll "L587" };
  ir_blk{ @"L101":
    call void $"glibc_vfprintf_internal#scratch_buffer_free"(P %"v31");
    call void $"glibc_vfprintf_internal#scratch_buffer_free"(P %"v24")
    => ret void };
  ir_blk{ @"L2036":
    %"v2038" : W = (Cmp Ult L) %"v977", #4
    => br %"v2038" ? "L2039" : "L2040" };
  ir_blk{ @"L2039":
    %"v2041" : W = (Cmp Eq L) %"v977", #1
    => br %"v2041" ? poll "L1996" : "L2042" };
  ir_blk{ @"L2042":
    %"v2043" : W = (Cmp Eq L) %"v977", #2
    => br %"v2043" ? poll "L980" : "L2044" };
  ir_blk{ @"L2044":
    %"v2045" : W = (Cmp Eq L) %"v977", #3
    => br %"v2045" ? poll "L984" : "L2034" };
  ir_blk{ @"L2040":
    %"v2047" : W = (Cmp Eq L) %"v977", #4
    => br %"v2047" ? poll "L1090" : "L2048" };
  ir_blk{ @"L2048":
    %"v2049" : W = (Cmp Eq L) %"v977", #5
    => br %"v2049" ? poll "L1090" : "L2050" };
  ir_blk{ @"L2050":
    %"v2051" : W = (Cmp Eq L) %"v977", #6
    => br %"v2051" ? poll "L1090" : "L2052" };
  ir_blk{ @"L2052":
    %"v2053" : W = (Cmp Eq L) %"v977", #7
    => br %"v2053" ? poll "L1935" : "L2034" };
  ir_blk{ @"L2037":
    %"v2055" : W = (Cmp Ult L) %"v977", #12
    => br %"v2055" ? "L2056" : "L2057" };
  ir_blk{ @"L2056":
    %"v2058" : W = (Cmp Eq L) %"v977", #8
    => br %"v2058" ? poll "L1746" : "L2059" };
  ir_blk{ @"L2059":
    %"v2060" : W = (Cmp Eq L) %"v977", #9
    => br %"v2060" ? poll "L1785" : "L2061" };
  ir_blk{ @"L2061":
    %"v2062" : W = (Cmp Eq L) %"v977", #10
    => br %"v2062" ? poll "L1603" : "L2063" };
  ir_blk{ @"L2063":
    %"v2064" : W = (Cmp Eq L) %"v977", #11
    => br %"v2064" ? poll "L1635" : "L2034" };
  ir_blk{ @"L2057":
    %"v2066" : W = (Cmp Eq L) %"v977", #12
    => br %"v2066" ? poll "L1717" : "L2067" };
  ir_blk{ @"L2067":
    %"v2068" : W = (Cmp Eq L) %"v977", #13
    => br %"v2068" ? poll "L1751" : "L2069" };
  ir_blk{ @"L2069":
    %"v2070" : W = (Cmp Eq L) %"v977", #14
    => br %"v2070" ? poll "L1935" : "L2071" };
  ir_blk{ @"L2071":
    %"v2072" : W = (Cmp Eq L) %"v977", #15
    => br %"v2072" ? poll "L1090" : "L2034" };
  ir_blk{ @"L2034":
    => unreachable }])))) }.

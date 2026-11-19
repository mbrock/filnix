(** This file defines checked IR from glibc’s `stdlib/strtol_l.os` object.
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

Definition fn___GI_____strtol_l_internal : func :=
  ir_fn{ "export" "__GI_____strtol_l_internal"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8", P %"v10") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v24" = %"v10" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v33" : L = (Ext Sw) %"v6";
    %"v34" : W = (Cmp Ne L) %"v33", #0
    => br %"v34" ? "L29" : "L31" };
  ir_blk{ @"L29":
    %"v36" = %"v25" +p #56;
    %"v40" = %"v36" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 1 Read 1) %"v41";
    %"v46" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v47" : W = (Cmp Sle W) %"v46", #0
    => br %"v47" ? "L49" : "L48" };
  ir_blk{ @"L48":
    %"v51" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v52" : W = (Cmp Eq W) %"v51", #127
    => goto "L49" };
  ir_blk{ @"L49" [%"v54" : W = phi("L29" => #1, "L48" => %"v52")]:
    => br %"v54" ? "L31" : "L43" };
  ir_blk{ @"L43":
    %"v56" = %"v25" +p #56;
    %"v60" = %"v56" +p #8;
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 1 Read 1) %"v61";
    %"v66" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v67" : W = (Cmp Eq W) %"v66", #0
    => br %"v67" ? "L31" : "L63" };
  ir_blk{ @"L63":
    => goto "L31" };
  ir_blk{ @"L31" [%"pr.52" : P = phi("L49" => #0, "L63" => %"v41", "L43" => #0, "start" => #0); %"pr.47" : P = phi("L49" => #0, "L63" => %"v61", "L43" => #0, "start" => #0)]:
    %"v72" : W = (Cmp Slt W) %"v4", #0
    => br %"v72" ? "L74" : "L73" };
  ir_blk{ @"L73":
    %"v76" : W = (Cmp Eq W) %"v4", #1
    => goto "L74" };
  ir_blk{ @"L74" [%"v78" : W = phi("L31" => #1, "L73" => %"v76")]:
    => br %"v78" ? "L80" : "L79" };
  ir_blk{ @"L79":
    %"v82" : W = (Cmp Sgt W) %"v4", #36
    => goto "L80" };
  ir_blk{ @"L80" [%"v84" : W = phi("L74" => #1, "L79" => %"v82")]:
    => br %"v84" ? "L68" : "L88" };
  ir_blk{ @"L68":
    %"v85" : P = Copy $"__libc_errno";
    %"chk6" : A = (Check 0 4 Write 1) %"v85";
    store Ww [%"chk6" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L88" [%"pr.23" : P = phi("L89" => %"v102", "L80" => %"v0")]:
    %"v92" = %"v10" +p #104;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v92";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 1 Read 1) %"pr.23";
    %"v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v96" : L = (Ext Sw) %"v95";
    %"v97" : L = Shl %"v96", #1;
    %"v98" = %"v93" +p %"v97";
    %"chk9" : A = (Check 0 2 Read 1) %"v98";
    %"v99" : W = (RawLoad (LdNarrow Uh) 0) %"chk9";
    %"v100" : W = And %"v99", #8192
    => br %"v100" ? "L89" : "L90" };
  ir_blk{ @"L89":
    %"v102" = %"pr.23" +p #1
    => goto poll "L88" };
  ir_blk{ @"L90":
    %"v107" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v108" : W = (Cmp Eq W) %"v107", #0
    => br %"v108" ? "L111" : "L105" };
  ir_blk{ @"L105":
    %"v117" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v118" : W = (Cmp Eq W) %"v117", #45
    => br %"v118" ? "L113" : "L114" };
  ir_blk{ @"L113":
    %"v120" = %"pr.23" +p #1
    => goto "L115" };
  ir_blk{ @"L114":
    %"v125" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v126" : W = (Cmp Eq W) %"v125", #43
    => br %"v126" ? "L121" : "L115" };
  ir_blk{ @"L121":
    %"v128" = %"pr.23" +p #1
    => goto "L115" };
  ir_blk{ @"L115" [%"pr.12" : P = phi("L113" => %"v120", "L121" => %"v128", "L114" => %"pr.23"); %"pr.6" : W = phi("L113" => #1, "L121" => #0, "L114" => #0)]:
    %"chk13" : A = (Check 0 1 Read 1) %"pr.12";
    %"v133" : W = (RawLoad (LdNarrow Sb) 0) %"chk13";
    %"v134" : W = (Cmp Eq W) %"v133", #48
    => br %"v134" ? "L129" : "L130" };
  ir_blk{ @"L129":
    %"v139" : W = (Cmp Eq W) %"v4", #0
    => br %"v139" ? "L141" : "L140" };
  ir_blk{ @"L140":
    %"v143" : W = (Cmp Eq W) %"v4", #16
    => goto "L141" };
  ir_blk{ @"L141" [%"v145" : W = phi("L129" => #1, "L140" => %"v143")]:
    => br %"v145" ? "L150" : "L147" };
  ir_blk{ @"L150":
    %"v187" : P = Copy $"_nl_C_locobj";
    %"v188" = %"v187" +p #120;
    %"chk14" : A = (Check 0 8 Read 8) %"v188";
    %"v189" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v191" = %"pr.12" +p #1;
    %"chk15" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v191";
    %"v192" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"v193" : L = (Ext Sw) %"v192";
    %"v194" : L = Shl %"v193", #2;
    %"v195" = %"v189" +p %"v194";
    %"chk16" : A = (Check 0 4 Read 1) %"v195";
    %"v196" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v198" : W = (Cmp Eq W) %"v196", #88
    => goto "L147" };
  ir_blk{ @"L147" [%"v200" : W = phi("L141" => #0, "L150" => %"v198")]:
    => br %"v200" ? "L135" : "L136" };
  ir_blk{ @"L135":
    %"v202" = %"pr.12" +p #2
    => goto "L131" };
  ir_blk{ @"L136":
    %"v206" : W = (Ext Ub) %"v8"
    => br %"v206" ? "L207" : "L208" };
  ir_blk{ @"L207":
    => br %"v139" ? "L208" : "L211" };
  ir_blk{ @"L211":
    %"v214" : W = (Cmp Eq W) %"v4", #2
    => goto "L208" };
  ir_blk{ @"L208" [%"v218" : W = phi("L136" => #0, "L207" => #1, "L211" => %"v214")]:
    => br %"v218" ? "L223" : "L220" };
  ir_blk{ @"L223":
    %"v260" : P = Copy $"_nl_C_locobj";
    %"v261" = %"v260" +p #120;
    %"chk17" : A = (Check 0 8 Read 8) %"v261";
    %"v262" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v264" = %"pr.12" +p #1;
    %"chk18" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v264";
    %"v265" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"v266" : L = (Ext Sw) %"v265";
    %"v267" : L = Shl %"v266", #2;
    %"v268" = %"v262" +p %"v267";
    %"chk19" : A = (Check 0 4 Read 1) %"v268";
    %"v269" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v271" : W = (Cmp Eq W) %"v269", #66
    => goto "L220" };
  ir_blk{ @"L220" [%"v273" : W = phi("L208" => #0, "L223" => %"v271")]:
    => br %"v273" ? "L203" : "L204" };
  ir_blk{ @"L203":
    %"v275" = %"pr.12" +p #2
    => goto "L131" };
  ir_blk{ @"L204":
    => br %"v139" ? "L131" : "L277" };
  ir_blk{ @"L277":
    => goto "L131" };
  ir_blk{ @"L130":
    %"v285" : W = (Cmp Eq W) %"v4", #0
    => br %"v285" ? "L131" : "L282" };
  ir_blk{ @"L282":
    => goto "L131" };
  ir_blk{ @"L131" [%"pr.14" : P = phi("L135" => %"v202", "L203" => %"v275", "L277" => %"pr.12", "L204" => %"pr.12", "L282" => %"pr.12", "L130" => %"pr.12"); %"pr.1" : W = phi("L135" => #16, "L203" => #2, "L277" => %"v4", "L204" => #8, "L282" => %"v4", "L130" => #10)]:
    %"v291" : W = (Cmp Ne W) %"pr.1", #10
    => br %"v291" ? "L289" : "L288" };
  ir_blk{ @"L288":
    => goto "L289" };
  ir_blk{ @"L289" [%"pr.51" : P = phi("L288" => %"pr.52", "L131" => #0)]:
    %"v296" : L = Ptoi %"pr.51";
    %"v297" : L = Ptoi #0;
    %"v298" : W = (Cmp Ne L) %"v296", %"v297"
    => br %"v298" ? "L292" : "L294" };
  ir_blk{ @"L292":
    call %"v302" : L = $"__GI_strlen"(P %"pr.47")
    => goto "L307" };
  ir_blk{ @"L307" [%"pr.43" : L = phi("L292" => #0, "L309" => %"v328")]:
    %"v313" : W = (Cmp Ult L) %"pr.43", %"v302"
    => br %"v313" ? "L308" : "L310" };
  ir_blk{ @"L308":
    %"v319" = %"pr.47" +p %"pr.43";
    %"chk20" : A = (Check 0 1 Read 1) %"v319";
    %"v320" : W = (RawLoad (LdNarrow Sb) 0) %"chk20";
    %"v323" = %"pr.14" +p %"pr.43";
    %"chk21" : A = (Check 0 1 Read 1) %"v323";
    %"v324" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v325" : W = (Cmp Ne W) %"v320", %"v324"
    => br %"v325" ? "L310" : "L309" };
  ir_blk{ @"L309":
    %"v328" : L = Add %"pr.43", #1
    => goto poll "L307" };
  ir_blk{ @"L310":
    => br %"v313" ? "L304" : "L294" };
  ir_blk{ @"L304":
    %"chk22" : A = (Check 0 1 Read 1) %"pr.14";
    %"v333" : W = (RawLoad (LdNarrow Sb) 0) %"chk22";
    %"v334" : W = (Ext Ub) %"v333"
    => goto "L335" };
  ir_blk{ @"L335" [%"pr.36" : P = phi("L304" => %"pr.14", "L337" => %"v451"); %"pr.25" : W = phi("L304" => %"v334", "L337" => %"v453")]:
    %"v339" : W = (Ext Ub) %"pr.25";
    %"v340" : W = (Cmp Ne W) %"v339", #0
    => br %"v340" ? "L336" : "L338" };
  ir_blk{ @"L336":
    %"v345" : W = (Ext Sb) %"v339";
    %"v346" : W = (Cmp Slt W) %"v345", #48
    => br %"v346" ? "L348" : "L347" };
  ir_blk{ @"L347":
    %"v351" : W = (Cmp Sgt W) %"v345", #57
    => goto "L348" };
  ir_blk{ @"L348" [%"v353" : W = phi("L336" => #1, "L347" => %"v351")]:
    => br %"v353" ? "L356" : "L355" };
  ir_blk{ @"L356" [%"pr.44" : L = phi("L358" => %"v377", "L348" => #0)]:
    %"v362" : W = (Cmp Ult L) %"pr.44", %"v302"
    => br %"v362" ? "L357" : "L355" };
  ir_blk{ @"L357":
    %"v368" = %"pr.47" +p %"pr.44";
    %"chk23" : A = (Check 0 1 Read 1) %"v368";
    %"v369" : W = (RawLoad (LdNarrow Sb) 0) %"chk23";
    %"v372" = %"pr.36" +p %"pr.44";
    %"chk24" : A = (Check 0 1 Read 1) %"v372";
    %"v373" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"v374" : W = (Cmp Ne W) %"v369", %"v373"
    => br %"v374" ? "L355" : "L358" };
  ir_blk{ @"L358":
    %"v377" : L = Add %"pr.44", #1
    => goto poll "L356" };
  ir_blk{ @"L355" [%"v382" : W = phi("L348" => #0, "L356" => %"v362", "L357" => %"v362")]:
    => br %"v382" ? "L383" : "L384" };
  ir_blk{ @"L383":
    %"v385" : P = Copy $"_nl_C_locobj";
    %"v386" = %"v385" +p #104;
    %"chk25" : A = (Check 0 8 Read 8) %"v386";
    %"v387" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v389" : L = (Ext Sw) %"v339";
    %"v390" : L = Shl %"v389", #1;
    %"v391" = %"v387" +p %"v390";
    %"chk26" : A = (Check 0 2 Read 1) %"v391";
    %"v392" : W = (RawLoad (LdNarrow Uh) 0) %"chk26";
    %"v393" : W = And %"v392", #1024;
    %"v394" : W = (Cmp Eq W) %"v393", #0
    => br %"v394" ? "L384" : "L399" }] [ir_blk{ @"L399":
    %"v432" : P = Copy $"_nl_C_locobj";
    %"v433" = %"v432" +p #120;
    %"chk27" : A = (Check 0 8 Read 8) %"v433";
    %"v434" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v437" : L = Shl %"v389", #2;
    %"v438" = %"v434" +p %"v437";
    %"chk28" : A = (Check 0 4 Read 1) %"v438";
    %"v439" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v441" : W = Sub %"v439", #65;
    %"v442" : W = Add %"v441", #10;
    %"v444" : W = (Cmp Sge W) %"v442", %"pr.1"
    => goto "L384" };
  ir_blk{ @"L384" [%"v448" : W = phi("L355" => #0, "L383" => #1, "L399" => %"v444")]:
    => br %"v448" ? "L338" : "L337" };
  ir_blk{ @"L337":
    %"v451" = %"pr.36" +p #1;
    %"chk29" : A = (Check 0 1 Read 1) %"v451";
    %"v452" : W = (RawLoad (LdNarrow Sb) 0) %"chk29";
    %"v453" : W = (Ext Ub) %"v452"
    => goto poll "L335" };
  ir_blk{ @"L338":
    call %"v458" : P = $"__correctly_grouped_prefixmb"(P %"pr.14", P %"pr.36", P %"pr.47", P %"pr.51")
    => goto "L294" };
  ir_blk{ @"L294" [%"pr.50" : L = phi("L338" => %"v302", "L310" => %"v302", "L289" => #0); %"pr.34" : P = phi("L338" => %"v458", "L310" => %"pr.14", "L289" => #0)]:
    %"v459" : P = Copy $"__strtol_ul_max_tab";
    %"v461" : W = Sub %"pr.1", #2;
    %"v462" : L = (Ext Sw) %"v461";
    %"v463" : L = Shl %"v462", #3;
    %"v464" = %"v459" +p %"v463";
    %"chk30" : A = (Check 0 8 Read 1) %"v464";
    %"v465" : L = (RawLoad LdL 0) %"chk30";
    %"v466" : P = Copy $"__strtol_ul_rem_tab";
    %"v470" = %"v466" +p %"v462";
    %"chk31" : A = (Check 0 1 Read 1) %"v470";
    %"v471" : W = (RawLoad (LdNarrow Ub) 0) %"chk31";
    %"chk32" : A = (Check 0 1 Read 1) %"pr.14";
    %"v473" : W = (RawLoad (LdNarrow Sb) 0) %"chk32";
    %"v474" : W = (Ext Ub) %"v473"
    => goto "L701" };
  ir_blk{ @"L701" [%"pr.39" : W = phi("L703" => %"pr.40", "L294" => #0); %"pr.30" : W = phi("L703" => %"v924", "L294" => %"v474"); %"pr.21" : P = phi("L703" => %"v922", "L294" => %"pr.14"); %"pr.9" : L = phi("L703" => %"pr.10", "L294" => #0)]:
    %"v705" : W = (Ext Ub) %"pr.30";
    %"v706" : W = (Cmp Ne W) %"v705", #0
    => br %"v706" ? "L702" : "L477" };
  ir_blk{ @"L702":
    %"v712" : L = Ptoi %"pr.21";
    %"v713" : L = Ptoi %"pr.34";
    %"v714" : W = (Cmp Eq L) %"v712", %"v713"
    => br %"v714" ? "L477" : "L709" };
  ir_blk{ @"L709":
    %"v720" : W = (Cmp Sge W) %"v705", #48
    => br %"v720" ? "L721" : "L722" };
  ir_blk{ @"L721":
    %"v724" : W = (Cmp Sle W) %"v705", #57
    => goto "L722" };
  ir_blk{ @"L722" [%"v726" : W = phi("L709" => #0, "L721" => %"v724")]:
    => br %"v726" ? "L716" : "L717" };
  ir_blk{ @"L716":
    %"v728" : W = Sub %"v705", #48;
    %"v729" : W = (Ext Ub) %"v728"
    => goto "L718" };
  ir_blk{ @"L717":
    %"v734" : W = (Cmp Ne L) %"pr.50", #0
    => br %"v734" ? "L735" : "L731" };
  ir_blk{ @"L735" [%"pr.46" : L = phi("L737" => %"v756", "L717" => #0)]:
    %"v741" : W = (Cmp Ult L) %"pr.46", %"pr.50"
    => br %"v741" ? "L736" : "L738" };
  ir_blk{ @"L736":
    %"v747" = %"pr.47" +p %"pr.46";
    %"chk33" : A = (Check 0 1 Read 1) %"v747";
    %"v748" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v751" = %"pr.21" +p %"pr.46";
    %"chk34" : A = (Check 0 1 Read 1) %"v751";
    %"v752" : W = (RawLoad (LdNarrow Sb) 0) %"chk34";
    %"v753" : W = (Cmp Ne W) %"v748", %"v752"
    => br %"v753" ? "L738" : "L737" };
  ir_blk{ @"L737":
    %"v756" : L = Add %"pr.46", #1
    => goto poll "L735" };
  ir_blk{ @"L738":
    %"v762" : W = (Cmp Eq L) %"pr.46", %"pr.50"
    => br %"v762" ? "L757" : "L759" };
  ir_blk{ @"L757":
    %"v765" : L = Sub %"pr.50", #1;
    %"v766" = %"pr.21" +p %"v765"
    => goto "L703" };
  ir_blk{ @"L759":
    %"v771" : P = Copy $"_nl_C_locobj";
    %"v772" = %"v771" +p #104;
    %"chk35" : A = (Check 0 8 Read 8) %"v772";
    %"v773" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v775" : L = (Ext Sw) %"v705";
    %"v776" : L = Shl %"v775", #1;
    %"v777" = %"v773" +p %"v776";
    %"chk36" : A = (Check 0 2 Read 1) %"v777";
    %"v778" : W = (RawLoad (LdNarrow Uh) 0) %"chk36";
    %"v779" : W = And %"v778", #1024
    => br %"v779" ? "L782" : "L477" };
  ir_blk{ @"L782":
    %"v815" : P = Copy $"_nl_C_locobj";
    %"v816" = %"v815" +p #120;
    %"chk37" : A = (Check 0 8 Read 8) %"v816";
    %"v817" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v820" : L = Shl %"v775", #2;
    %"v821" = %"v817" +p %"v820";
    %"chk38" : A = (Check 0 4 Read 1) %"v821";
    %"v822" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"v824" : W = Sub %"v822", #65;
    %"v825" : W = Add %"v824", #10;
    %"v826" : W = (Ext Ub) %"v825"
    => goto "L718" };
  ir_blk{ @"L731":
    %"v830" : P = Copy $"_nl_C_locobj";
    %"v831" = %"v830" +p #104;
    %"chk39" : A = (Check 0 8 Read 8) %"v831";
    %"v832" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v834" : L = (Ext Sw) %"v705";
    %"v835" : L = Shl %"v834", #1;
    %"v836" = %"v832" +p %"v835";
    %"chk40" : A = (Check 0 2 Read 1) %"v836";
    %"v837" : W = (RawLoad (LdNarrow Uh) 0) %"chk40";
    %"v838" : W = And %"v837", #1024
    => br %"v838" ? "L841" : "L477" };
  ir_blk{ @"L841":
    %"v874" : P = Copy $"_nl_C_locobj";
    %"v875" = %"v874" +p #120;
    %"chk41" : A = (Check 0 8 Read 8) %"v875";
    %"v876" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v879" : L = Shl %"v834", #2;
    %"v880" = %"v876" +p %"v879";
    %"chk42" : A = (Check 0 4 Read 1) %"v880";
    %"v881" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v883" : W = Sub %"v881", #65;
    %"v884" : W = Add %"v883", #10;
    %"v885" : W = (Ext Ub) %"v884"
    => goto "L718" };
  ir_blk{ @"L718" [%"pr.31" : W = phi("L716" => %"v729", "L782" => %"v826", "L841" => %"v885")]:
    %"v889" : W = (Ext Ub) %"pr.31";
    %"v891" : W = (Cmp Sge W) %"v889", %"pr.1"
    => br %"v891" ? "L477" : "L888" };
  ir_blk{ @"L888":
    %"v898" : W = (Cmp Ugt L) %"pr.9", %"v465"
    => br %"v898" ? "L900" : "L899" };
  ir_blk{ @"L899":
    %"v903" : W = (Cmp Eq L) %"pr.9", %"v465"
    => br %"v903" ? "L904" : "L900" };
  ir_blk{ @"L904":
    %"v908" : W = (Cmp Ugt W) %"v889", %"v471"
    => goto "L900" };
  ir_blk{ @"L900" [%"v912" : W = phi("L888" => #1, "L899" => #0, "L904" => %"v908")]:
    => br %"v912" ? "L703" : "L687" };
  ir_blk{ @"L687":
    %"v915" : L = (Ext Sw) %"pr.1";
    %"v916" : L = Mul %"pr.9", %"v915";
    %"v919" : L = (Ext Uw) %"v889";
    %"v920" : L = Add %"v916", %"v919"
    => goto "L703" };
  ir_blk{ @"L703" [%"pr.40" : W = phi("L757" => %"pr.39", "L687" => %"pr.39", "L900" => #1); %"pr.22" : P = phi("L757" => %"v766", "L687" => %"pr.21", "L900" => %"pr.21"); %"pr.10" : L = phi("L757" => %"pr.9", "L687" => %"v920", "L900" => %"pr.9")]:
    %"v922" = %"pr.22" +p #1;
    %"chk43" : A = (Check 0 1 Read 1) %"v922";
    %"v923" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"v924" : W = (Ext Ub) %"v923"
    => goto poll "L701" };
  ir_blk{ @"L477":
    %"v930" : L = Ptoi %"pr.21";
    %"v931" : L = Ptoi %"pr.14";
    %"v932" : W = (Cmp Eq L) %"v930", %"v931"
    => br %"v932" ? "L111" : "L927" };
  ir_blk{ @"L927":
    %"v938" : L = Ptoi %"v2";
    %"v940" : W = (Cmp Ne L) %"v938", %"v297"
    => br %"v940" ? "L934" : "L936" };
  ir_blk{ @"L934":
    %"chk44" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk44" + 0] <- %"pr.21"
    => goto "L936" };
  ir_blk{ @"L936":
    %"v947" : W = (Cmp Eq W) %"pr.39", #0
    => br %"v947" ? "L948" : "L949" };
  ir_blk{ @"L948":
    => br %"pr.6" ? "L953" : "L952" };
  ir_blk{ @"L952":
    => goto "L953" };
  ir_blk{ @"L953" [%"v960" : L = phi("L952" => #9223372036854775807, "L948" => #9223372036854775808)]:
    %"v961" : W = (Cmp Ugt L) %"pr.9", %"v960"
    => goto "L949" };
  ir_blk{ @"L949" [%"v963" : W = phi("L936" => #0, "L953" => %"v961")]:
    => br %"v963" ? "L945" : "L944" };
  ir_blk{ @"L944":
    => goto "L945" };
  ir_blk{ @"L945" [%"pr.42" : W = phi("L944" => %"pr.39", "L949" => #1)]:
    %"v968" : L = (Ext Sw) %"pr.42";
    %"v969" : W = (Cmp Ne L) %"v968", #0
    => br %"v969" ? "L964" : "L966" };
  ir_blk{ @"L964":
    %"v970" : P = Copy $"__libc_errno";
    %"chk45" : A = (Check 0 4 Write 1) %"v970";
    store Ww [%"chk45" + 0] <- #34
    => br %"pr.6" ? "L973" : "L972" };
  ir_blk{ @"L972":
    => goto "L973" };
  ir_blk{ @"L973" [%"v977" : L = phi("L972" => #9223372036854775807, "L964" => #9223372036854775808)]:
    => ret %"v977" };
  ir_blk{ @"L966":
    => br %"pr.6" ? "L979" : "L981" };
  ir_blk{ @"L979":
    %"v984" : L = Neg %"pr.9"
    => goto "L981" };
  ir_blk{ @"L981" [%"v986" : L = phi("L979" => %"v984", "L966" => %"pr.9")]:
    => ret %"v986" };
  ir_blk{ @"L111" [%"pr.33" : P = phi("L90" => %"v0", "L477" => %"pr.14")]:
    %"v991" : L = Ptoi %"v2";
    %"v992" : L = Ptoi #0;
    %"v993" : W = (Cmp Ne L) %"v991", %"v992"
    => br %"v993" ? "L987" : "L989" };
  ir_blk{ @"L987":
    %"v999" : L = Ptoi %"pr.33";
    %"v1000" : L = Ptoi %"v0";
    %"v1001" : L = Sub %"v999", %"v1000";
    %"v1002" : W = (Cmp Sge L) %"v1001", #2
    => br %"v1002" ? "L1007" : "L1004" };
  ir_blk{ @"L1007":
    %"v1048" : P = Copy $"_nl_C_locobj";
    %"v1049" = %"v1048" +p #120;
    %"chk46" : A = (Check 0 8 Read 8) %"v1049";
    %"v1050" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v1054" = %"pr.33" +p #18446744073709551615;
    %"chk47" : A = (Check 0 1 Read 1) %"v1054";
    %"v1055" : W = (RawLoad (LdNarrow Sb) 0) %"chk47";
    %"v1056" : L = (Ext Sw) %"v1055";
    %"v1057" : L = Shl %"v1056", #2;
    %"v1058" = %"v1050" +p %"v1057";
    %"chk48" : A = (Check 0 4 Read 1) %"v1058";
    %"v1059" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"v1061" : W = (Cmp Eq W) %"v1059", #88
    => br %"v1061" ? "L1004" : "L1062" };
  ir_blk{ @"L1062":
    %"v1064" : W = (Ext Ub) %"v8"
    => br %"v1064" ? "L1069" : "L1004" };
  ir_blk{ @"L1069":
    %"v1110" : P = Copy $"_nl_C_locobj";
    %"v1111" = %"v1110" +p #120;
    %"chk49" : A = (Check 0 8 Read 8) %"v1111";
    %"v1112" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v1116" = %"pr.33" +p #18446744073709551615;
    %"chk50" : A = (Renew 0 1 Read 1) %"chk47", %"v1116";
    %"v1117" : W = (RawLoad (LdNarrow Sb) 0) %"chk50";
    %"v1118" : L = (Ext Sw) %"v1117";
    %"v1119" : L = Shl %"v1118", #2;
    %"v1120" = %"v1112" +p %"v1119";
    %"chk51" : A = (Check 0 4 Read 1) %"v1120";
    %"v1121" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    %"v1123" : W = (Cmp Eq W) %"v1121", #66
    => goto "L1004" };
  ir_blk{ @"L1004" [%"v1129" : W = phi("L987" => #0, "L1007" => #1, "L1062" => #0, "L1069" => %"v1123")]:
    => br %"v1129" ? "L1130" : "L1131" };
  ir_blk{ @"L1130":
    %"v1135" = %"pr.33" +p #18446744073709551614;
    %"chk52" : A = (Check 0 1 Read 1) %"v1135";
    %"v1136" : W = (RawLoad (LdNarrow Sb) 0) %"chk52";
    %"v1137" : W = (Cmp Eq W) %"v1136", #48
    => goto "L1131" };
  ir_blk{ @"L1131" [%"v1139" : W = phi("L1004" => #0, "L1130" => %"v1137")]:
    => br %"v1139" ? "L994" : "L995" };
  ir_blk{ @"L994":
    %"v1144" = %"pr.33" +p #18446744073709551615;
    %"chk53" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk53" + 0] <- %"v1144"
    => goto "L989" };
  ir_blk{ @"L995":
    %"chk54" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk54" + 0] <- %"v0"
    => goto "L989" };
  ir_blk{ @"L989":
    => ret #0 }])) }.

Definition item___strtol_ul_max_tab : item :=
  (IData (a "__strtol_ul_max_tab") (LRo (a "export")) 8 [(Item Wl 9223372036854775807); (Item Wl 6148914691236517205); (Item Wl 4611686018427387903); (Item Wl 3689348814741910323); (Item Wl 3074457345618258602); (Item Wl 2635249153387078802); (Item Wl 2305843009213693951); (Item Wl 2049638230412172401); (Item Wl 1844674407370955161); (Item Wl 1676976733973595601); (Item Wl 1537228672809129301); (Item Wl 1418980313362273201); (Item Wl 1317624576693539401); (Item Wl 1229782938247303441); (Item Wl 1152921504606846975); (Item Wl 1085102592571150095); (Item Wl 1024819115206086200); (Item Wl 970881267037344821); (Item Wl 922337203685477580); (Item Wl 878416384462359600); (Item Wl 838488366986797800); (Item Wl 802032351030850070); (Item Wl 768614336404564650); (Item Wl 737869762948382064); (Item Wl 709490156681136600); (Item Wl 683212743470724133); (Item Wl 658812288346769700); (Item Wl 636094623231363848); (Item Wl 614891469123651720); (Item Wl 595056260442243600); (Item Wl 576460752303423487); (Item Wl 558992244657865200); (Item Wl 542551296285575047); (Item Wl 527049830677415760); (Item Wl 512409557603043100)]).

Definition item___strtol_ul_rem_tab : item :=
  (IData (a "__strtol_ul_rem_tab") (LRo (a "export")) 1 [(Item Wb 1); (Item Wb 0); (Item Wb 3); (Item Wb 0); (Item Wb 3); (Item Wb 1); (Item Wb 7); (Item Wb 6); (Item Wb 5); (Item Wb 4); (Item Wb 3); (Item Wb 2); (Item Wb 1); (Item Wb 0); (Item Wb 15); (Item Wb 0); (Item Wb 15); (Item Wb 16); (Item Wb 15); (Item Wb 15); (Item Wb 15); (Item Wb 5); (Item Wb 15); (Item Wb 15); (Item Wb 15); (Item Wb 24); (Item Wb 15); (Item Wb 23); (Item Wb 15); (Item Wb 15); (Item Wb 31); (Item Wb 15); (Item Wb 17); (Item Wb 15); (Item Wb 15)]).

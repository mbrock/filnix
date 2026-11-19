(** This file defines checked IR from glibc’s `stdlib/strtoul_l.os` object.
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

Definition fn___GI_____strtoul_l_internal : func :=
  ir_fn{ "export" "__GI_____strtoul_l_internal"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8", P %"v10") -> (RClass L) blocks ((app [ir_blk{ @"start":
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
  ir_blk{ @"L31" [%"pr.51" : P = phi("L49" => #0, "L63" => %"v41", "L43" => #0, "start" => #0); %"pr.46" : P = phi("L49" => #0, "L63" => %"v61", "L43" => #0, "start" => #0)]:
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
  ir_blk{ @"L289" [%"pr.50" : P = phi("L288" => %"pr.51", "L131" => #0)]:
    %"v296" : L = Ptoi %"pr.50";
    %"v297" : L = Ptoi #0;
    %"v298" : W = (Cmp Ne L) %"v296", %"v297"
    => br %"v298" ? "L292" : "L294" };
  ir_blk{ @"L292":
    call %"v302" : L = $"__GI_strlen"(P %"pr.46")
    => goto "L307" };
  ir_blk{ @"L307" [%"pr.42" : L = phi("L292" => #0, "L309" => %"v328")]:
    %"v313" : W = (Cmp Ult L) %"pr.42", %"v302"
    => br %"v313" ? "L308" : "L310" };
  ir_blk{ @"L308":
    %"v319" = %"pr.46" +p %"pr.42";
    %"chk20" : A = (Check 0 1 Read 1) %"v319";
    %"v320" : W = (RawLoad (LdNarrow Sb) 0) %"chk20";
    %"v323" = %"pr.14" +p %"pr.42";
    %"chk21" : A = (Check 0 1 Read 1) %"v323";
    %"v324" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v325" : W = (Cmp Ne W) %"v320", %"v324"
    => br %"v325" ? "L310" : "L309" };
  ir_blk{ @"L309":
    %"v328" : L = Add %"pr.42", #1
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
  ir_blk{ @"L356" [%"pr.43" : L = phi("L358" => %"v377", "L348" => #0)]:
    %"v362" : W = (Cmp Ult L) %"pr.43", %"v302"
    => br %"v362" ? "L357" : "L355" }] [ir_blk{ @"L357":
    %"v368" = %"pr.46" +p %"pr.43";
    %"chk23" : A = (Check 0 1 Read 1) %"v368";
    %"v369" : W = (RawLoad (LdNarrow Sb) 0) %"chk23";
    %"v372" = %"pr.36" +p %"pr.43";
    %"chk24" : A = (Check 0 1 Read 1) %"v372";
    %"v373" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"v374" : W = (Cmp Ne W) %"v369", %"v373"
    => br %"v374" ? "L355" : "L358" };
  ir_blk{ @"L358":
    %"v377" : L = Add %"pr.43", #1
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
    => br %"v394" ? "L384" : "L399" };
  ir_blk{ @"L399":
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
    call %"v458" : P = $"__correctly_grouped_prefixmb"(P %"pr.14", P %"pr.36", P %"pr.46", P %"pr.50")
    => goto "L294" };
  ir_blk{ @"L294" [%"pr.49" : L = phi("L338" => %"v302", "L310" => %"v302", "L289" => #0); %"pr.34" : P = phi("L338" => %"v458", "L310" => %"pr.14", "L289" => #0)]:
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
    %"v734" : W = (Cmp Ne L) %"pr.49", #0
    => br %"v734" ? "L735" : "L731" };
  ir_blk{ @"L735" [%"pr.45" : L = phi("L737" => %"v756", "L717" => #0)]:
    %"v741" : W = (Cmp Ult L) %"pr.45", %"pr.49"
    => br %"v741" ? "L736" : "L738" };
  ir_blk{ @"L736":
    %"v747" = %"pr.46" +p %"pr.45";
    %"chk33" : A = (Check 0 1 Read 1) %"v747";
    %"v748" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v751" = %"pr.21" +p %"pr.45";
    %"chk34" : A = (Check 0 1 Read 1) %"v751";
    %"v752" : W = (RawLoad (LdNarrow Sb) 0) %"chk34";
    %"v753" : W = (Cmp Ne W) %"v748", %"v752"
    => br %"v753" ? "L738" : "L737" };
  ir_blk{ @"L737":
    %"v756" : L = Add %"pr.45", #1
    => goto poll "L735" };
  ir_blk{ @"L738":
    %"v762" : W = (Cmp Eq L) %"pr.45", %"pr.49"
    => br %"v762" ? "L757" : "L759" };
  ir_blk{ @"L757":
    %"v765" : L = Sub %"pr.49", #1;
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
    %"v947" : L = (Ext Sw) %"pr.39";
    %"v948" : W = (Cmp Ne L) %"v947", #0
    => br %"v948" ? "L943" : "L945" };
  ir_blk{ @"L943":
    %"v949" : P = Copy $"__libc_errno";
    %"chk45" : A = (Check 0 4 Write 1) %"v949";
    store Ww [%"chk45" + 0] <- #34
    => ret #18446744073709551615 };
  ir_blk{ @"L945":
    => br %"pr.6" ? "L953" : "L955" };
  ir_blk{ @"L953":
    %"v958" : L = Neg %"pr.9"
    => goto "L955" };
  ir_blk{ @"L955" [%"v960" : L = phi("L953" => %"v958", "L945" => %"pr.9")]:
    => ret %"v960" };
  ir_blk{ @"L111" [%"pr.33" : P = phi("L90" => %"v0", "L477" => %"pr.14")]:
    %"v965" : L = Ptoi %"v2";
    %"v966" : L = Ptoi #0;
    %"v967" : W = (Cmp Ne L) %"v965", %"v966"
    => br %"v967" ? "L961" : "L963" };
  ir_blk{ @"L961":
    %"v973" : L = Ptoi %"pr.33";
    %"v974" : L = Ptoi %"v0";
    %"v975" : L = Sub %"v973", %"v974";
    %"v976" : W = (Cmp Sge L) %"v975", #2
    => br %"v976" ? "L981" : "L978" };
  ir_blk{ @"L981":
    %"v1022" : P = Copy $"_nl_C_locobj";
    %"v1023" = %"v1022" +p #120;
    %"chk46" : A = (Check 0 8 Read 8) %"v1023";
    %"v1024" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v1028" = %"pr.33" +p #18446744073709551615;
    %"chk47" : A = (Check 0 1 Read 1) %"v1028";
    %"v1029" : W = (RawLoad (LdNarrow Sb) 0) %"chk47";
    %"v1030" : L = (Ext Sw) %"v1029";
    %"v1031" : L = Shl %"v1030", #2;
    %"v1032" = %"v1024" +p %"v1031";
    %"chk48" : A = (Check 0 4 Read 1) %"v1032";
    %"v1033" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"v1035" : W = (Cmp Eq W) %"v1033", #88
    => br %"v1035" ? "L978" : "L1036" };
  ir_blk{ @"L1036":
    %"v1038" : W = (Ext Ub) %"v8"
    => br %"v1038" ? "L1043" : "L978" };
  ir_blk{ @"L1043":
    %"v1084" : P = Copy $"_nl_C_locobj";
    %"v1085" = %"v1084" +p #120;
    %"chk49" : A = (Check 0 8 Read 8) %"v1085";
    %"v1086" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v1090" = %"pr.33" +p #18446744073709551615;
    %"chk50" : A = (Renew 0 1 Read 1) %"chk47", %"v1090";
    %"v1091" : W = (RawLoad (LdNarrow Sb) 0) %"chk50";
    %"v1092" : L = (Ext Sw) %"v1091";
    %"v1093" : L = Shl %"v1092", #2;
    %"v1094" = %"v1086" +p %"v1093";
    %"chk51" : A = (Check 0 4 Read 1) %"v1094";
    %"v1095" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    %"v1097" : W = (Cmp Eq W) %"v1095", #66
    => goto "L978" };
  ir_blk{ @"L978" [%"v1103" : W = phi("L961" => #0, "L981" => #1, "L1036" => #0, "L1043" => %"v1097")]:
    => br %"v1103" ? "L1104" : "L1105" };
  ir_blk{ @"L1104":
    %"v1109" = %"pr.33" +p #18446744073709551614;
    %"chk52" : A = (Check 0 1 Read 1) %"v1109";
    %"v1110" : W = (RawLoad (LdNarrow Sb) 0) %"chk52";
    %"v1111" : W = (Cmp Eq W) %"v1110", #48
    => goto "L1105" };
  ir_blk{ @"L1105" [%"v1113" : W = phi("L978" => #0, "L1104" => %"v1111")]:
    => br %"v1113" ? "L968" : "L969" };
  ir_blk{ @"L968":
    %"v1118" = %"pr.33" +p #18446744073709551615;
    %"chk53" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk53" + 0] <- %"v1118"
    => goto "L963" };
  ir_blk{ @"L969":
    %"chk54" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk54" + 0] <- %"v0"
    => goto "L963" };
  ir_blk{ @"L963":
    => ret #0 }])) }.

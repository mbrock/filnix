(** This file defines checked IR from glibc’s `string/memmem.os` object.
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

Definition fn___GI___memmem : func :=
  ir_fn{ "export" "__GI___memmem"(P %"v0", L %"v2", P %"v4", L %"v6") -> (RClass P) {
  @"start":
    %"v114" : P = (Alloc 4) #256;
    %"v16" : W = (Cmp Eq L) %"v6", #0
    => br %"v16" ? "L12" : "L14";
  @"L12":
    => ret %"v0";
  @"L14":
    %"v23" : W = (Cmp Eq L) %"v6", #1
    => br %"v23" ? "L19" : "L21";
  @"L19":
    %"chk0" : A = (Check 0 1 Read 1) %"v4";
    %"v27" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    call %"v29" : P = $"__GI_memchr"(P %"v0", W %"v27", L %"v2")
    => ret %"v29";
  @"L21":
    %"v36" : W = (Cmp Ult L) %"v2", %"v6"
    => br %"v36" ? "L31" : "L33";
  @"L31":
    => ret #0;
  @"L33":
    %"v41" = %"v0" +p %"v2";
    (Flight (a "v43") Sub [(FAddress (t "v41")); (FValue (t "v6"))] (LowerOf (t "v41")));
    %"v48" : W = (Cmp Eq L) %"v6", #2
    => br %"v48" ? "L44" : "L46";
  @"L44":
    %"chk1" : A = (Check 0 1 Read 1) %"v4";
    %"v52" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v53" : W = Shl %"v52", #16;
    %"v55" = %"v4" +p #1;
    %"chk2" : A = (HalfCheck Upper 0 1 Read 1) %"chk1", %"v55";
    %"v56" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"v57" : W = Or %"v53", %"v56";
    %"chk3" : A = (Check 0 1 Read 1) %"v0";
    %"v61" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"v62" : W = Shl %"v61", #16;
    %"v64" = %"v0" +p #1;
    %"chk4" : A = (HalfCheck Upper 0 1 Read 1) %"chk3", %"v64";
    %"v65" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"v66" : W = Or %"v62", %"v65"
    => goto "L69";
  @"L69" [%"pr.5" : W = phi("L44" => %"v66", "L70" => %"v90"); %"pr.4" : P = phi("L44" => %"v64", "L70" => %"v88")]:
    %"v75" : L = Ptoi %"pr.4";
    %"v76" : L = Ptoi %"v43";
    %"v77" : W = (Cmp Ule L) %"v75", %"v76"
    => br %"v77" ? "L78" : "L79";
  @"L78":
    %"v82" : W = (Cmp Ne W) %"pr.5", %"v57"
    => goto "L79";
  @"L79" [%"v84" : W = phi("L69" => #0, "L78" => %"v82")]:
    => br %"v84" ? "L70" : "L72";
  @"L70":
    %"v86" : W = Shl %"pr.5", #16;
    %"v88" = %"pr.4" +p #1;
    %"chk5" : A = (Check 0 1 Read 1) %"v88";
    %"v89" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"v90" : W = Or %"v86", %"v89"
    => goto poll "L69";
  @"L72":
    %"v96" : W = (Cmp Eq W) %"pr.5", %"v57"
    => br %"v96" ? "L91" : "L93";
  @"L91":
    (Flight (a "v98") Sub [(FAddress (t "pr.4")); (FValue (Const 1))] (LowerOf (t "pr.4")))
    => goto "L93";
  @"L93" [%"v99" : P = phi("L91" => %"v98", "L72" => #0)]:
    => ret %"v99";
  @"L46":
    %"v105" : W = (Cmp Ugt L) %"v6", #256
    => br %"v105" ? "L101" : "L103";
  @"L101":
    call %"v112" : P = $"glibc_memmem#two_way_long_needle"(P %"v0", L %"v2", P %"v4", L %"v6")
    => ret %"v112";
  @"L103":
    %"v119" : L = Sub %"v6", #1;
    call %"v121" : P = $"__GI_memset"(P %"v114", W #0, L #256)
    => goto "L123";
  @"L123" [%"pr.9" : W = phi("L103" => #1, "L124" => %"v154")]:
    %"v129" : L = (Ext Sw) %"pr.9";
    %"v130" : W = (Cmp Ult L) %"v129", %"v119"
    => br %"v130" ? "L124" : "L126";
  @"L124":
    %"v134" = %"v4" +p %"v129";
    %"chk6" : A = (Check 0 1 Read 1) %"v134";
    %"v136" : W = (RawLoad (LdNarrow Ub) 0) %"chk6";
    %"v137" : L = (Ext Uw) %"v136";
    %"v144" = %"v134" +p #18446744073709551615;
    %"chk7" : A = (HalfCheck Lower 0 1 Read 1) %"chk6", %"v144";
    %"v145" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v146" : L = (Ext Uw) %"v145";
    %"v147" : L = Shl %"v146", #3;
    %"v148" : L = Sub %"v137", %"v147";
    %"v149" : L = And %"v148", #255;
    %"v150" = %"v114" +p %"v149";
    %"v152" : W = (Ext Ub) %"pr.9";
    %"chk8" : A = (Check 0 1 Write 1) %"v150";
    store Wb [%"chk8" + 0] <- %"v152";
    %"v154" : W = Add %"pr.9", #1
    => goto poll "L123";
  @"L126":
    %"v158" = %"v4" +p %"v119";
    %"chk9" : A = (Check 0 1 Read 1) %"v158";
    %"v160" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v161" : L = (Ext Uw) %"v160";
    %"v167" = %"v158" +p #18446744073709551615;
    %"chk10" : A = (HalfCheck Lower 0 1 Read 1) %"chk9", %"v167";
    %"v168" : W = (RawLoad (LdNarrow Ub) 0) %"chk10";
    %"v169" : L = (Ext Uw) %"v168";
    %"v170" : L = Shl %"v169", #3;
    %"v171" : L = Sub %"v161", %"v170";
    %"v172" : L = And %"v171", #255;
    %"v173" = %"v114" +p %"v172";
    %"chk11" : A = (Check 0 1 Read 1) %"v173";
    %"v174" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"v175" : L = (Ext Uw) %"v174";
    %"v176" : L = Sub %"v119", %"v175";
    %"v181" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v182" : L = (Ext Uw) %"v181";
    %"v189" : W = (RawLoad (LdNarrow Ub) 0) %"chk10";
    %"v190" : L = (Ext Uw) %"v189";
    %"v191" : L = Shl %"v190", #3;
    %"v192" : L = Sub %"v182", %"v191";
    %"v193" : L = And %"v192", #255;
    %"v194" = %"v114" +p %"v193";
    %"v196" : W = (Ext Ub) %"v119";
    %"chk14" : A = (Check 0 1 Write 1) %"v194";
    store Wb [%"chk14" + 0] <- %"v196"
    => goto "L197";
  @"L197" [%"pr.6" : L = phi("L126" => #0, "L251" => %"pr.8", "L208" => %"pr.6"); %"pr.1" : P = phi("L126" => %"v0", "L251" => %"v287", "L208" => %"v241")]:
    %"v203" : L = Ptoi %"pr.1";
    %"v204" : L = Ptoi %"v43";
    %"v205" : W = (Cmp Ule L) %"v203", %"v204"
    => br %"v205" ? "L206" : "L200";
  @"L206" [%"pr.3" : P = phi("L231" => %"v211", "L197" => %"pr.1")]:
    %"v211" = %"pr.3" +p %"v119";
    %"chk15" : A = (Check 0 1 Read 1) %"v211";
    %"v214" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v215" : L = (Ext Uw) %"v214";
    %"v219" = %"v211" +p #18446744073709551615;
    %"chk16" : A = (HalfCheck Lower 0 1 Read 1) %"chk15", %"v219";
    %"v220" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v221" : L = (Ext Uw) %"v220";
    %"v222" : L = Shl %"v221", #3;
    %"v223" : L = Sub %"v215", %"v222";
    %"v224" : L = And %"v223", #255;
    %"v225" = %"v114" +p %"v224";
    %"chk17" : A = (Check 0 1 Read 1) %"v225";
    %"v226" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v227" : L = (Ext Uw) %"v226";
    %"v229" : W = (Cmp Eq L) %"v227", #0
    => br %"v229" ? "L230" : "L231";
  @"L230":
    %"v234" : L = Ptoi %"v211";
    %"v236" : W = (Cmp Ule L) %"v234", %"v204"
    => goto "L231";
  @"L231" [%"v238" : W = phi("L206" => #0, "L230" => %"v236")]:
    => br %"v238" ? poll "L206" : "L208";
  @"L208":
    (Flight (a "v241") Sub [(FAddress (t "v211")); (FValue (t "v227"))] (LowerOf (t "v211")));
    %"v247" : W = (Cmp Ult L) %"v227", %"v119"
    => br %"v247" ? poll "L197" : "L244";
  @"L244":
    %"v253" : W = (Cmp Ult L) %"v119", #15
    => br %"v253" ? "L255" : "L254";
  @"L254":
    %"v258" = %"v241" +p %"pr.6";
    %"v261" = %"v4" +p %"pr.6";
    call %"v262" : W = $"__GI_memcmp"(P %"v258", P %"v261", L #8);
    %"v263" : W = (Cmp Eq W) %"v262", #0
    => goto "L255";
  @"L255" [%"v265" : W = phi("L244" => #1, "L254" => %"v263")]:
    => br %"v265" ? "L249" : "L251";
  @"L249":
    call %"v272" : W = $"__GI_memcmp"(P %"v241", P %"v4", L %"v119");
    %"v273" : W = (Cmp Eq W) %"v272", #0
    => br %"v273" ? "L266" : "L268";
  @"L266":
    => ret %"v241";
  @"L268":
    %"v280" : W = (Cmp Uge L) %"pr.6", #8
    => br %"v280" ? "L278" : "L277";
  @"L277":
    => goto "L278";
  @"L278" [%"v283" : L = phi("L277" => %"v119", "L268" => %"pr.6")]:
    %"v284" : L = Sub %"v283", #8
    => goto "L251";
  @"L251" [%"pr.8" : L = phi("L278" => %"v284", "L255" => %"pr.6")]:
    %"v287" = %"v241" +p %"v176"
    => goto poll "L197";
  @"L200":
    => ret #0
} }.

Definition fn_glibc_memmem'23two_way_long_needle : func :=
  ir_fn{ "local" "glibc_memmem#two_way_long_needle"(P %"v0", L %"v2", P %"v4", L %"v6") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v12" : P = (Alloc 8) #2048
    => goto "iw_1.L13" };
  ir_blk{ @"iw_1.L13" [%"iw_1.pr.24" : L = phi("iw_1.L33" => %"iw_1.v44", "iw_1.L46" => #1, "iw_1.L51" => %"iw_1.pr.24", "iw_1.L52" => %"iw_1.pr.24", "start" => #1); %"iw_1.pr.17" : L = phi("iw_1.L33" => #1, "iw_1.L46" => #1, "iw_1.L51" => %"iw_1.v58", "iw_1.L52" => #1, "start" => #1); %"iw_1.pr.9" : L = phi("iw_1.L33" => %"iw_1.v18", "iw_1.L46" => %"iw_1.v63", "iw_1.L51" => %"iw_1.pr.9", "iw_1.L52" => %"iw_1.v61", "start" => #0); %"iw_1.pr.1" : L = phi("iw_1.L33" => %"iw_1.pr.1", "iw_1.L46" => %"iw_1.pr.9", "iw_1.L51" => %"iw_1.pr.1", "iw_1.L52" => %"iw_1.pr.1", "start" => #18446744073709551615)]:
    %"iw_1.v18" : L = Add %"iw_1.pr.9", %"iw_1.pr.17";
    %"iw_1.v20" : W = (Cmp Ult L) %"iw_1.v18", %"v6"
    => br %"iw_1.v20" ? "iw_1.L14" : "iw_1.L66" };
  ir_blk{ @"iw_1.L14":
    %"iw_1.v25" = %"v4" +p %"iw_1.v18";
    %"chk0" : A = (Check 0 1 Read 1) %"iw_1.v25";
    %"iw_1.v26" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"iw_1.v30" : L = Add %"iw_1.pr.1", %"iw_1.pr.17";
    %"iw_1.v31" = %"v4" +p %"iw_1.v30";
    %"chk1" : A = (Check 0 1 Read 1) %"iw_1.v31";
    %"iw_1.v32" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"iw_1.v38" : W = (Cmp Slt W) %"iw_1.v26", %"iw_1.v32"
    => br %"iw_1.v38" ? "iw_1.L33" : "iw_1.L34" };
  ir_blk{ @"iw_1.L33":
    %"iw_1.v44" : L = Sub %"iw_1.v18", %"iw_1.pr.1"
    => goto poll "iw_1.L13" };
  ir_blk{ @"iw_1.L34":
    %"iw_1.v50" : W = (Cmp Eq W) %"iw_1.v26", %"iw_1.v32"
    => br %"iw_1.v50" ? "iw_1.L45" : "iw_1.L46" };
  ir_blk{ @"iw_1.L45":
    %"iw_1.v56" : W = (Cmp Ne L) %"iw_1.pr.17", %"iw_1.pr.24"
    => br %"iw_1.v56" ? "iw_1.L51" : "iw_1.L52" };
  ir_blk{ @"iw_1.L51":
    %"iw_1.v58" : L = Add %"iw_1.pr.17", #1
    => goto poll "iw_1.L13" };
  ir_blk{ @"iw_1.L52":
    %"iw_1.v61" : L = Add %"iw_1.pr.9", %"iw_1.pr.24"
    => goto poll "iw_1.L13" };
  ir_blk{ @"iw_1.L46":
    %"iw_1.v63" : L = Add %"iw_1.pr.9", #1
    => goto poll "iw_1.L13" };
  ir_blk{ @"iw_1.L66" [%"iw_1.pr.27" : L = phi("iw_1.L86" => %"iw_1.v97", "iw_1.L99" => #1, "iw_1.L104" => %"iw_1.pr.27", "iw_1.L105" => %"iw_1.pr.27", "iw_1.L13" => #1); %"iw_1.pr.21" : L = phi("iw_1.L86" => #1, "iw_1.L99" => #1, "iw_1.L104" => %"iw_1.v111", "iw_1.L105" => #1, "iw_1.L13" => #1); %"iw_1.pr.13" : L = phi("iw_1.L86" => %"iw_1.v71", "iw_1.L99" => %"iw_1.v116", "iw_1.L104" => %"iw_1.pr.13", "iw_1.L105" => %"iw_1.v114", "iw_1.L13" => #0); %"iw_1.pr.5" : L = phi("iw_1.L86" => %"iw_1.pr.5", "iw_1.L99" => %"iw_1.pr.13", "iw_1.L104" => %"iw_1.pr.5", "iw_1.L105" => %"iw_1.pr.5", "iw_1.L13" => #18446744073709551615)]:
    %"iw_1.v71" : L = Add %"iw_1.pr.13", %"iw_1.pr.21";
    %"iw_1.v73" : W = (Cmp Ult L) %"iw_1.v71", %"v6"
    => br %"iw_1.v73" ? "iw_1.L67" : "iw_1.L68" };
  ir_blk{ @"iw_1.L67":
    %"iw_1.v78" = %"v4" +p %"iw_1.v71";
    %"chk2" : A = (Check 0 1 Read 1) %"iw_1.v78";
    %"iw_1.v79" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"iw_1.v83" : L = Add %"iw_1.pr.5", %"iw_1.pr.21";
    %"iw_1.v84" = %"v4" +p %"iw_1.v83";
    %"chk3" : A = (Check 0 1 Read 1) %"iw_1.v84";
    %"iw_1.v85" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"iw_1.v91" : W = (Cmp Slt W) %"iw_1.v85", %"iw_1.v79"
    => br %"iw_1.v91" ? "iw_1.L86" : "iw_1.L87" };
  ir_blk{ @"iw_1.L86":
    %"iw_1.v97" : L = Sub %"iw_1.v71", %"iw_1.pr.5"
    => goto poll "iw_1.L66" };
  ir_blk{ @"iw_1.L87":
    %"iw_1.v103" : W = (Cmp Eq W) %"iw_1.v79", %"iw_1.v85"
    => br %"iw_1.v103" ? "iw_1.L98" : "iw_1.L99" };
  ir_blk{ @"iw_1.L98":
    %"iw_1.v109" : W = (Cmp Ne L) %"iw_1.pr.21", %"iw_1.pr.27"
    => br %"iw_1.v109" ? "iw_1.L104" : "iw_1.L105" };
  ir_blk{ @"iw_1.L104":
    %"iw_1.v111" : L = Add %"iw_1.pr.21", #1
    => goto poll "iw_1.L66" };
  ir_blk{ @"iw_1.L105":
    %"iw_1.v114" : L = Add %"iw_1.pr.13", %"iw_1.pr.27"
    => goto poll "iw_1.L66" };
  ir_blk{ @"iw_1.L99":
    %"iw_1.v116" : L = Add %"iw_1.pr.13", #1
    => goto poll "iw_1.L66" };
  ir_blk{ @"iw_1.L68":
    %"iw_1.v121" : L = Add %"iw_1.pr.5", #1;
    %"iw_1.v123" : L = Add %"iw_1.pr.1", #1;
    %"iw_1.v124" : W = (Cmp Ult L) %"iw_1.v121", %"iw_1.v123"
    => br %"iw_1.v124" ? "iw_1.join" : "iw_1.L119" };
  ir_blk{ @"iw_1.L119":
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v15" : L = phi("iw_1.L119" => %"iw_1.v121", "iw_1.L68" => %"iw_1.v123"); %"pr.11" : L = phi("iw_1.L119" => %"iw_1.pr.27", "iw_1.L68" => %"iw_1.pr.24")]:
    => goto "L16" };
  ir_blk{ @"L16" [%"pr.2" : L = phi("L17" => %"v29", "iw_1.join" => #0)]:
    %"v23" : W = (Cmp Ult L) %"pr.2", #256
    => br %"v23" ? "L17" : "L30" };
  ir_blk{ @"L17":
    %"v25" : L = Shl %"pr.2", #3;
    %"v26" = %"v12" +p %"v25";
    %"chk4" : A = (Check 0 8 Write 1) %"v26";
    store Wl [%"chk4" + 0] <- %"v6";
    %"v29" : L = Add %"pr.2", #1
    => goto poll "L16" };
  ir_blk{ @"L30" [%"pr.6" : L = phi("L31" => %"v49", "L16" => #0)]:
    %"v36" : W = (Cmp Ult L) %"pr.6", %"v6"
    => br %"v36" ? "L31" : "L33" };
  ir_blk{ @"L31":
    %"v39" = %"v4" +p %"pr.6";
    %"chk5" : A = (Check 0 1 Read 1) %"v39";
    %"v40" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"v41" : L = (Ext Uw) %"v40";
    %"v42" : L = Shl %"v41", #3;
    %"v43" = %"v12" +p %"v42";
    %"v46" : L = Sub %"v6", %"pr.6";
    %"v47" : L = Sub %"v46", #1;
    %"chk6" : A = (Check 0 8 Write 1) %"v43";
    store Wl [%"chk6" + 0] <- %"v47";
    %"v49" : L = Add %"pr.6", #1
    => goto poll "L30" };
  ir_blk{ @"L33":
    %"v56" = %"v4" +p %"pr.11";
    call %"v58" : W = $"__GI_memcmp"(P %"v4", P %"v56", L %"v15");
    %"v59" : W = (Cmp Eq W) %"v58", #0
    => br %"v59" ? "L62" : "L51" };
  ir_blk{ @"L62" [%"pr.13" : L = phi("L90" => #0, "L33" => #0, "L183" => %"v198", "L145" => #0); %"pr.10" : L = phi("L90" => %"v105", "L33" => #0, "L183" => %"v195", "L145" => %"v204")]:
    %"v68" : L = Sub %"v2", %"v6";
    %"v69" : W = (Cmp Ule L) %"pr.10", %"v68"
    => br %"v69" ? "L63" : "L52" };
  ir_blk{ @"L63":
    %"v75" : L = Add %"pr.10", %"v6";
    %"v76" : L = Sub %"v75", #1;
    %"v77" = %"v0" +p %"v76";
    %"chk7" : A = (Check 0 1 Read 1) %"v77";
    %"v78" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v79" : L = (Ext Uw) %"v78";
    %"v80" : L = Shl %"v79", #3;
    %"v81" = %"v12" +p %"v80";
    %"chk8" : A = (Check 0 8 Read 1) %"v81";
    %"v82" : L = (RawLoad LdL 0) %"chk8";
    %"v87" : W = (Cmp Ugt L) %"v82", #0
    => br %"v87" ? "L83" : "L85" };
  ir_blk{ @"L83":
    %"v92" : W = (Cmp Ne L) %"pr.13", #0
    => br %"v92" ? "L93" : "L94" };
  ir_blk{ @"L93":
    %"v97" : W = (Cmp Ult L) %"v82", %"pr.11"
    => goto "L94" };
  ir_blk{ @"L94" [%"v99" : W = phi("L83" => #0, "L93" => %"v97")]:
    => br %"v99" ? "L88" : "L90" };
  ir_blk{ @"L88":
    %"v102" : L = Sub %"v6", %"pr.11"
    => goto "L90" };
  ir_blk{ @"L90" [%"pr.14" : L = phi("L88" => %"v102", "L94" => %"v82")]:
    %"v105" : L = Add %"pr.10", %"pr.14"
    => goto poll "L62" };
  ir_blk{ @"L85":
    %"v112" : W = (Cmp Ugt L) %"v15", %"pr.13"
    => br %"v112" ? "L109" : "L108" };
  ir_blk{ @"L108":
    => goto "L109" };
  ir_blk{ @"L109" [%"v115" : L = phi("L108" => %"pr.13", "L85" => %"v15")]:
    %"v118" = %"v4" +p %"v115";
    %"v122" : L = Add %"v115", %"pr.10";
    %"v123" = %"v0" +p %"v122"
    => goto "L124" }] [ir_blk{ @"L124" [%"pr.19" : P = phi("L109" => %"v123", "L125" => %"pr.20"); %"pr.15" : P = phi("L109" => %"v118", "L125" => %"pr.16"); %"pr.1" : L = phi("L109" => %"v115", "L125" => %"v143")]:
    %"v129" : L = Sub %"v6", #1;
    %"v130" : W = (Cmp Ult L) %"pr.1", %"v129"
    => br %"v130" ? "L131" : "L132" };
  ir_blk{ @"L131":
    %"v134" = %"pr.15" +p #1;
    %"chk9" : A = (Check 0 1 Read 1) %"pr.15";
    %"v135" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v137" = %"pr.19" +p #1;
    %"chk10" : A = (Check 0 1 Read 1) %"pr.19";
    %"v138" : W = (RawLoad (LdNarrow Ub) 0) %"chk10";
    %"v139" : W = (Cmp Eq W) %"v135", %"v138"
    => goto "L132" };
  ir_blk{ @"L132" [%"v141" : W = phi("L124" => #0, "L131" => %"v139"); %"pr.20" : P = phi("L124" => %"pr.19", "L131" => %"v137"); %"pr.16" : P = phi("L124" => %"pr.15", "L131" => %"v134")]:
    => br %"v141" ? "L125" : "L126" };
  ir_blk{ @"L125":
    %"v143" : L = Add %"pr.1", #1
    => goto poll "L124" };
  ir_blk{ @"L126":
    %"v150" : W = (Cmp Ule L) %"v129", %"pr.1"
    => br %"v150" ? "L144" : "L145" };
  ir_blk{ @"L144":
    %"v152" : L = Sub %"v15", #1;
    %"v155" = %"v4" +p %"v152";
    %"v159" : L = Add %"v152", %"pr.10";
    %"v160" = %"v0" +p %"v159"
    => goto "L161" };
  ir_blk{ @"L161" [%"pr.21" : P = phi("L144" => %"v160", "L162" => %"pr.22"); %"pr.17" : P = phi("L144" => %"v155", "L162" => %"pr.18"); %"pr.3" : L = phi("L144" => %"v152", "L162" => %"v180")]:
    %"v166" : L = Add %"pr.3", #1;
    %"v167" : W = (Cmp Ult L) %"pr.13", %"v166"
    => br %"v167" ? "L168" : "L169" };
  ir_blk{ @"L168":
    (Flight (a "v171") Sub [(FAddress (t "pr.17")); (FValue (Const 1))] (LowerOf (t "pr.17")));
    %"chk11" : A = (Check 0 1 Read 1) %"pr.17";
    %"v172" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    (Flight (a "v174") Sub [(FAddress (t "pr.21")); (FValue (Const 1))] (LowerOf (t "pr.21")));
    %"chk12" : A = (Check 0 1 Read 1) %"pr.21";
    %"v175" : W = (RawLoad (LdNarrow Ub) 0) %"chk12";
    %"v176" : W = (Cmp Eq W) %"v172", %"v175"
    => goto "L169" };
  ir_blk{ @"L169" [%"v178" : W = phi("L161" => #0, "L168" => %"v176"); %"pr.22" : P = phi("L161" => %"pr.21", "L168" => %"v174"); %"pr.18" : P = phi("L161" => %"pr.17", "L168" => %"v171")]:
    => br %"v178" ? "L162" : "L163" };
  ir_blk{ @"L162":
    %"v180" : L = Sub %"pr.3", #1
    => goto poll "L161" };
  ir_blk{ @"L163":
    %"v187" : L = Add %"pr.13", #1;
    %"v188" : W = (Cmp Ult L) %"v166", %"v187"
    => br %"v188" ? "L181" : "L183" };
  ir_blk{ @"L181":
    %"v191" = %"v0" +p %"pr.10"
    => ret %"v191" };
  ir_blk{ @"L183":
    %"v195" : L = Add %"pr.10", %"pr.11";
    %"v198" : L = Sub %"v6", %"pr.11"
    => goto poll "L62" };
  ir_blk{ @"L145":
    %"v202" : L = Sub %"pr.1", %"v15";
    %"v203" : L = Add %"v202", #1;
    %"v204" : L = Add %"pr.10", %"v203"
    => goto poll "L62" };
  ir_blk{ @"L51":
    %"v212" : L = Sub %"v6", %"v15";
    %"v213" : W = (Cmp Ugt L) %"v15", %"v212"
    => br %"v213" ? "L208" : "L207" };
  ir_blk{ @"L207":
    => goto "L208" };
  ir_blk{ @"L208" [%"v218" : L = phi("L207" => %"v212", "L51" => %"v15")]:
    %"v219" : L = Add %"v218", #1
    => goto "L220" };
  ir_blk{ @"L220" [%"pr.8" : L = phi("L208" => #0, "L241" => %"v248", "L316" => %"v325", "L280" => %"v331")]:
    %"v226" : L = Sub %"v2", %"v6";
    %"v227" : W = (Cmp Ule L) %"pr.8", %"v226"
    => br %"v227" ? "L221" : "L52" };
  ir_blk{ @"L221":
    %"v233" : L = Add %"pr.8", %"v6";
    %"v234" : L = Sub %"v233", #1;
    %"v235" = %"v0" +p %"v234";
    %"chk13" : A = (Check 0 1 Read 1) %"v235";
    %"v236" : W = (RawLoad (LdNarrow Ub) 0) %"chk13";
    %"v237" : L = (Ext Uw) %"v236";
    %"v238" : L = Shl %"v237", #3;
    %"v239" = %"v12" +p %"v238";
    %"chk14" : A = (Check 0 8 Read 1) %"v239";
    %"v240" : L = (RawLoad LdL 0) %"chk14";
    %"v245" : W = (Cmp Ugt L) %"v240", #0
    => br %"v245" ? "L241" : "L243" };
  ir_blk{ @"L241":
    %"v248" : L = Add %"pr.8", %"v240"
    => goto poll "L220" };
  ir_blk{ @"L243":
    %"v253" = %"v4" +p %"v15";
    %"v257" : L = Add %"v15", %"pr.8";
    %"v258" = %"v0" +p %"v257"
    => goto "L259" };
  ir_blk{ @"L259" [%"pr.27" : P = phi("L243" => %"v258", "L260" => %"pr.28"); %"pr.23" : P = phi("L243" => %"v253", "L260" => %"pr.24"); %"pr.4" : L = phi("L243" => %"v15", "L260" => %"v278")]:
    %"v264" : L = Sub %"v6", #1;
    %"v265" : W = (Cmp Ult L) %"pr.4", %"v264"
    => br %"v265" ? "L266" : "L267" };
  ir_blk{ @"L266":
    %"v269" = %"pr.23" +p #1;
    %"chk15" : A = (Check 0 1 Read 1) %"pr.23";
    %"v270" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v272" = %"pr.27" +p #1;
    %"chk16" : A = (Check 0 1 Read 1) %"pr.27";
    %"v273" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v274" : W = (Cmp Eq W) %"v270", %"v273"
    => goto "L267" };
  ir_blk{ @"L267" [%"v276" : W = phi("L259" => #0, "L266" => %"v274"); %"pr.28" : P = phi("L259" => %"pr.27", "L266" => %"v272"); %"pr.24" : P = phi("L259" => %"pr.23", "L266" => %"v269")]:
    => br %"v276" ? "L260" : "L261" };
  ir_blk{ @"L260":
    %"v278" : L = Add %"pr.4", #1
    => goto poll "L259" };
  ir_blk{ @"L261":
    %"v285" : W = (Cmp Ule L) %"v264", %"pr.4"
    => br %"v285" ? "L279" : "L280" };
  ir_blk{ @"L279":
    %"v287" : L = Sub %"v15", #1;
    %"v290" = %"v4" +p %"v287";
    %"v294" : L = Add %"v287", %"pr.8";
    %"v295" = %"v0" +p %"v294"
    => goto "L296" };
  ir_blk{ @"L296" [%"pr.29" : P = phi("L279" => %"v295", "L297" => %"pr.30"); %"pr.25" : P = phi("L279" => %"v290", "L297" => %"pr.26"); %"pr.5" : L = phi("L279" => %"v287", "L297" => %"v313")]:
    %"v300" : W = (Cmp Ne L) %"pr.5", #18446744073709551615
    => br %"v300" ? "L301" : "L302" };
  ir_blk{ @"L301":
    (Flight (a "v304") Sub [(FAddress (t "pr.25")); (FValue (Const 1))] (LowerOf (t "pr.25")));
    %"chk17" : A = (Check 0 1 Read 1) %"pr.25";
    %"v305" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    (Flight (a "v307") Sub [(FAddress (t "pr.29")); (FValue (Const 1))] (LowerOf (t "pr.29")));
    %"chk18" : A = (Check 0 1 Read 1) %"pr.29";
    %"v308" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v309" : W = (Cmp Eq W) %"v305", %"v308"
    => goto "L302" };
  ir_blk{ @"L302" [%"v311" : W = phi("L296" => #0, "L301" => %"v309"); %"pr.30" : P = phi("L296" => %"pr.29", "L301" => %"v307"); %"pr.26" : P = phi("L296" => %"pr.25", "L301" => %"v304")]:
    => br %"v311" ? "L297" : "L298" };
  ir_blk{ @"L297":
    %"v313" : L = Sub %"pr.5", #1
    => goto poll "L296" };
  ir_blk{ @"L298":
    %"v318" : W = (Cmp Eq L) %"pr.5", #18446744073709551615
    => br %"v318" ? "L314" : "L316" };
  ir_blk{ @"L314":
    %"v321" = %"v0" +p %"pr.8"
    => ret %"v321" };
  ir_blk{ @"L316":
    %"v325" : L = Add %"pr.8", %"v219"
    => goto poll "L220" };
  ir_blk{ @"L280":
    %"v329" : L = Sub %"pr.4", %"v15";
    %"v330" : L = Add %"v329", #1;
    %"v331" : L = Add %"pr.8", %"v330"
    => goto poll "L220" };
  ir_blk{ @"L52":
    => ret #0 }])) }.

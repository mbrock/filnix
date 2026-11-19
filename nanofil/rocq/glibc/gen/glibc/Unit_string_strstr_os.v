(** This file defines checked IR from glibc’s `string/strstr.os` object.
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

Definition fn___GI_strstr : func :=
  ir_fn{ "export" "__GI_strstr"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    %"v105" : P = (Alloc 4) #256;
    %"chk0" : A = (Check 0 1 Read 1) %"v2";
    %"v13" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"v14" : W = (Cmp Eq W) %"v13", #0
    => br %"v14" ? "L8" : "L10";
  @"L8":
    => ret %"v0";
  @"L10":
    %"v20" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    call %"v21" : P = $"__GI_strchr"(P %"v0", W %"v20");
    %"v26" : L = Ptoi %"v21";
    %"v27" : L = Ptoi #0;
    %"v28" : W = (Cmp Eq L) %"v26", %"v27"
    => br %"v28" ? "L30" : "L29";
  @"L29":
    %"v32" = %"v2" +p #1;
    %"chk2" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v32";
    %"v33" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"v34" : W = (Cmp Eq W) %"v33", #0
    => goto "L30";
  @"L30" [%"v36" : W = phi("L10" => #1, "L29" => %"v34")]:
    => br %"v36" ? "L22" : "L24";
  @"L22":
    => ret %"v21";
  @"L24":
    %"v43" = %"v2" +p #2;
    %"chk3" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v43";
    %"v44" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"v45" : W = (Cmp Eq W) %"v44", #0
    => br %"v45" ? "iw_1.start" : "L41";
  @"iw_1.start":
    %"chk4" : A = (Renew 0 1 Read 1) %"chk0", %"v2";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"iw_1.v8" : W = Shl %"iw_1.v7", #16;
    %"iw_1.v10" = %"v2" +p #1;
    %"iw_1.v11" : W = (RawLoad (LdNarrow Ub) 1) %"chk4";
    %"iw_1.v12" : W = Or %"iw_1.v8", %"iw_1.v11";
    %"chk6" : A = (Check 0 1 Read 1) %"v21";
    %"iw_1.v17" : W = (RawLoad (LdNarrow Ub) 0) %"chk6"
    => goto "iw_1.L18";
  @"iw_1.L18" [%"iw_1.pr.3" : W = phi("iw_1.L19" => %"iw_1.v37", "iw_1.start" => %"iw_1.v17"); %"iw_1.pr.2" : W = phi("iw_1.L19" => %"iw_1.v34", "iw_1.start" => #0); %"iw_1.pr.1" : P = phi("iw_1.L19" => %"iw_1.v36", "iw_1.start" => %"v21")]:
    %"iw_1.v24" : W = (Cmp Ne W) %"iw_1.v12", %"iw_1.pr.2"
    => br %"iw_1.v24" ? "iw_1.L25" : "iw_1.L26";
  @"iw_1.L25":
    %"iw_1.v28" : W = (Cmp Ne W) %"iw_1.pr.3", #0
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.v30" : W = phi("iw_1.L18" => #0, "iw_1.L25" => %"iw_1.v28")]:
    => br %"iw_1.v30" ? "iw_1.L19" : "iw_1.L21";
  @"iw_1.L19":
    %"iw_1.v32" : W = Shl %"iw_1.pr.2", #16;
    %"iw_1.v34" : W = Or %"iw_1.v32", %"iw_1.pr.3";
    %"iw_1.v36" = %"iw_1.pr.1" +p #1;
    %"chk7" : A = (Check 0 1 Read 1) %"iw_1.v36";
    %"iw_1.v37" : W = (RawLoad (LdNarrow Ub) 0) %"chk7"
    => goto poll "iw_1.L18";
  @"iw_1.L21":
    %"iw_1.v43" : W = (Cmp Eq W) %"iw_1.v12", %"iw_1.pr.2"
    => br %"iw_1.v43" ? "iw_1.L38" : "iw_1.L40";
  @"iw_1.L38":
    (Flight (a "iw_1.v45") Sub [(FAddress (t "iw_1.pr.1")); (FValue (Const 2))] (LowerOf (t "iw_1.pr.1")))
    => goto "iw_1.L40";
  @"iw_1.L40" [%"iw_1.v46" : P = phi("iw_1.L38" => %"iw_1.v45", "iw_1.L21" => #0)]:
    => ret %"iw_1.v46";
  @"L41":
    %"v54" = %"v2" +p #3;
    %"chk8" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v54";
    %"v55" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v56" : W = (Cmp Eq W) %"v55", #0
    => br %"v56" ? "iw_2.start" : "L52";
  @"iw_2.start":
    %"chk9" : A = (Renew 0 1 Read 1) %"chk0", %"v2";
    %"iw_2.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"iw_2.v8" : W = Shl %"iw_2.v7", #24;
    %"iw_2.v10" = %"v2" +p #1;
    %"iw_2.v11" : W = (RawLoad (LdNarrow Ub) 1) %"chk9";
    %"iw_2.v12" : W = Shl %"iw_2.v11", #16;
    %"iw_2.v13" : W = Or %"iw_2.v8", %"iw_2.v12";
    %"iw_2.v15" = %"v2" +p #2;
    %"iw_2.v16" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"iw_2.v17" : W = Shl %"iw_2.v16", #8;
    %"iw_2.v18" : W = Or %"iw_2.v13", %"iw_2.v17";
    %"chk12" : A = (Check 0 1 Read 1) %"v21";
    %"iw_2.v23" : W = (RawLoad (LdNarrow Ub) 0) %"chk12"
    => goto "iw_2.L24";
  @"iw_2.L24" [%"iw_2.pr.3" : W = phi("iw_2.L25" => %"iw_2.v43", "iw_2.start" => %"iw_2.v23"); %"iw_2.pr.2" : W = phi("iw_2.L25" => %"iw_2.v40", "iw_2.start" => #0); %"iw_2.pr.1" : P = phi("iw_2.L25" => %"iw_2.v42", "iw_2.start" => %"v21")]:
    %"iw_2.v30" : W = (Cmp Ne W) %"iw_2.v18", %"iw_2.pr.2"
    => br %"iw_2.v30" ? "iw_2.L31" : "iw_2.L32";
  @"iw_2.L31":
    %"iw_2.v34" : W = (Cmp Ne W) %"iw_2.pr.3", #0
    => goto "iw_2.L32";
  @"iw_2.L32" [%"iw_2.v36" : W = phi("iw_2.L24" => #0, "iw_2.L31" => %"iw_2.v34")]:
    => br %"iw_2.v36" ? "iw_2.L25" : "iw_2.L27";
  @"iw_2.L25":
    %"iw_2.v39" : W = Or %"iw_2.pr.2", %"iw_2.pr.3";
    %"iw_2.v40" : W = Shl %"iw_2.v39", #8;
    %"iw_2.v42" = %"iw_2.pr.1" +p #1;
    %"chk13" : A = (Check 0 1 Read 1) %"iw_2.v42";
    %"iw_2.v43" : W = (RawLoad (LdNarrow Ub) 0) %"chk13"
    => goto poll "iw_2.L24";
  @"iw_2.L27":
    %"iw_2.v49" : W = (Cmp Eq W) %"iw_2.v18", %"iw_2.pr.2"
    => br %"iw_2.v49" ? "iw_2.L44" : "iw_2.L46";
  @"iw_2.L44":
    (Flight (a "iw_2.v51") Sub [(FAddress (t "iw_2.pr.1")); (FValue (Const 3))] (LowerOf (t "iw_2.pr.1")))
    => goto "iw_2.L46";
  @"iw_2.L46" [%"iw_2.v52" : P = phi("iw_2.L44" => %"iw_2.v51", "iw_2.L27" => #0)]:
    => ret %"iw_2.v52";
  @"L52":
    call %"v63" : L = $"__GI_strlen"(P %"v2");
    %"v67" : L = Or %"v63", #512;
    call %"v68" : L = $"__GI___strnlen"(P %"v21", L %"v67");
    %"v74" : W = (Cmp Ult L) %"v68", %"v63"
    => br %"v74" ? "L69" : "L71";
  @"L69":
    => ret #0;
  @"L71":
    call %"v82" : W = $"__GI_memcmp"(P %"v21", P %"v2", L %"v63");
    %"v83" : W = (Cmp Eq W) %"v82", #0
    => br %"v83" ? "L76" : "L78";
  @"L76":
    => ret %"v21";
  @"L78":
    %"v90" : W = (Cmp Ugt L) %"v63", #256
    => br %"v90" ? "L86" : "L88";
  @"L86":
    call %"v97" : P = $"glibc_strstr#two_way_long_needle"(P %"v21", L %"v68", P %"v2", L %"v63")
    => ret %"v97";
  @"L88":
    %"v102" = %"v21" +p %"v68";
    (Flight (a "v104") Sub [(FAddress (t "v102")); (FValue (t "v63"))] (LowerOf (t "v102")));
    %"v110" : L = Sub %"v63", #1;
    call %"v112" : P = $"__GI_memset"(P %"v105", W #0, L #256)
    => goto "L114";
  @"L114" [%"pr.7" : W = phi("L115" => %"v145", "L88" => #1)]:
    %"v120" : L = (Ext Sw) %"pr.7";
    %"v121" : W = (Cmp Ult L) %"v120", %"v110"
    => br %"v121" ? "L115" : "L117";
  @"L115":
    %"v125" = %"v2" +p %"v120";
    %"chk14" : A = (Check 0 1 Read 1) %"v125";
    %"v127" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"v128" : L = (Ext Uw) %"v127";
    %"v135" = %"v125" +p #18446744073709551615;
    %"chk15" : A = (HalfCheck Lower 0 1 Read 1) %"chk14", %"v135";
    %"v136" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v137" : L = (Ext Uw) %"v136";
    %"v138" : L = Shl %"v137", #3;
    %"v139" : L = Sub %"v128", %"v138";
    %"v140" : L = And %"v139", #255;
    %"v141" = %"v105" +p %"v140";
    %"v143" : W = (Ext Ub) %"pr.7";
    %"chk16" : A = (Check 0 1 Write 1) %"v141";
    store Wb [%"chk16" + 0] <- %"v143";
    %"v145" : W = Add %"pr.7", #1
    => goto poll "L114";
  @"L117":
    %"v149" = %"v2" +p %"v110";
    %"chk17" : A = (Check 0 1 Read 1) %"v149";
    %"v151" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v152" : L = (Ext Uw) %"v151";
    %"v158" = %"v149" +p #18446744073709551615;
    %"chk18" : A = (HalfCheck Lower 0 1 Read 1) %"chk17", %"v158";
    %"v159" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v160" : L = (Ext Uw) %"v159";
    %"v161" : L = Shl %"v160", #3;
    %"v162" : L = Sub %"v152", %"v161";
    %"v163" : L = And %"v162", #255;
    %"v164" = %"v105" +p %"v163";
    %"chk19" : A = (Check 0 1 Read 1) %"v164";
    %"v165" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v166" : L = (Ext Uw) %"v165";
    %"v167" : L = Sub %"v110", %"v166";
    %"v172" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v173" : L = (Ext Uw) %"v172";
    %"v180" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v181" : L = (Ext Uw) %"v180";
    %"v182" : L = Shl %"v181", #3;
    %"v183" : L = Sub %"v173", %"v182";
    %"v184" : L = And %"v183", #255;
    %"v185" = %"v105" +p %"v184";
    %"v187" : W = (Ext Ub) %"v110";
    %"chk22" : A = (Check 0 1 Write 1) %"v185";
    store Wb [%"chk22" + 0] <- %"v187"
    => goto "L188";
  @"L188" [%"pr.5" : L = phi("L117" => #0, "L262" => %"pr.6", "L219" => %"pr.5"); %"pr.3" : P = phi("L117" => %"v104", "L262" => %"pr.4", "L219" => %"pr.4"); %"pr.1" : P = phi("L117" => %"v21", "L262" => %"v298", "L219" => %"v252")]:
    %"v196" : L = Ptoi %"pr.1";
    %"v197" : L = Ptoi %"pr.3";
    %"v198" : W = (Cmp Ugt L) %"v196", %"v197"
    => br %"v198" ? "L191" : "L193";
  @"L191":
    %"v204" = %"pr.3" +p %"v110";
    %"v205" = %"v204" +p #1;
    call %"v206" : L = $"__GI___strnlen"(P %"v205", L #2048);
    %"v207" = %"pr.3" +p %"v206";
    %"v214" : L = Ptoi %"v207";
    %"v215" : W = (Cmp Ugt L) %"v196", %"v214"
    => br %"v215" ? "L208" : "L193";
  @"L208":
    => ret #0;
  @"L193" [%"pr.4" : P = phi("L191" => %"v207", "L188" => %"pr.3")]:
    => goto "L217";
  @"L217" [%"pr.2" : P = phi("L193" => %"pr.1", "L242" => %"v222")]:
    %"v222" = %"pr.2" +p %"v110";
    %"chk23" : A = (Check 0 1 Read 1) %"v222";
    %"v225" : W = (RawLoad (LdNarrow Ub) 0) %"chk23";
    %"v226" : L = (Ext Uw) %"v225";
    %"v230" = %"v222" +p #18446744073709551615;
    %"chk24" : A = (HalfCheck Lower 0 1 Read 1) %"chk23", %"v230";
    %"v231" : W = (RawLoad (LdNarrow Ub) 0) %"chk24";
    %"v232" : L = (Ext Uw) %"v231";
    %"v233" : L = Shl %"v232", #3;
    %"v234" : L = Sub %"v226", %"v233";
    %"v235" : L = And %"v234", #255;
    %"v236" = %"v105" +p %"v235";
    %"chk25" : A = (Check 0 1 Read 1) %"v236";
    %"v237" : W = (RawLoad (LdNarrow Ub) 0) %"chk25";
    %"v238" : L = (Ext Uw) %"v237";
    %"v240" : W = (Cmp Eq L) %"v238", #0
    => br %"v240" ? "L241" : "L242";
  @"L241":
    %"v245" : L = Ptoi %"v222";
    %"v246" : L = Ptoi %"pr.4";
    %"v247" : W = (Cmp Ule L) %"v245", %"v246"
    => goto "L242";
  @"L242" [%"v249" : W = phi("L217" => #0, "L241" => %"v247")]:
    => br %"v249" ? poll "L217" : "L219";
  @"L219":
    (Flight (a "v252") Sub [(FAddress (t "v222")); (FValue (t "v238"))] (LowerOf (t "v222")));
    %"v258" : W = (Cmp Ult L) %"v238", %"v110"
    => br %"v258" ? poll "L188" : "L255";
  @"L255":
    %"v264" : W = (Cmp Ult L) %"v110", #15
    => br %"v264" ? "L266" : "L265";
  @"L265":
    %"v269" = %"v252" +p %"pr.5";
    %"v272" = %"v2" +p %"pr.5";
    call %"v273" : W = $"__GI_memcmp"(P %"v269", P %"v272", L #8);
    %"v274" : W = (Cmp Eq W) %"v273", #0
    => goto "L266";
  @"L266" [%"v276" : W = phi("L255" => #1, "L265" => %"v274")]:
    => br %"v276" ? "L260" : "L262";
  @"L260":
    call %"v283" : W = $"__GI_memcmp"(P %"v252", P %"v2", L %"v110");
    %"v284" : W = (Cmp Eq W) %"v283", #0
    => br %"v284" ? "L277" : "L279";
  @"L277":
    => ret %"v252";
  @"L279":
    %"v291" : W = (Cmp Uge L) %"pr.5", #8
    => br %"v291" ? "L289" : "L288";
  @"L288":
    => goto "L289";
  @"L289" [%"v294" : L = phi("L288" => %"v110", "L279" => %"pr.5")]:
    %"v295" : L = Sub %"v294", #8
    => goto "L262";
  @"L262" [%"pr.6" : L = phi("L289" => %"v295", "L266" => %"pr.5")]:
    %"v298" = %"v252" +p %"v167"
    => goto poll "L188"
} }.

Definition fn_glibc_strstr'23two_way_long_needle : func :=
  ir_fn{ "local" "glibc_strstr#two_way_long_needle"(P %"v0", L %"v2", P %"v4", L %"v6") -> (RClass P) blocks ((app [ir_blk{ @"start":
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
  ir_blk{ @"iw_1.join" [%"v15" : L = phi("iw_1.L119" => %"iw_1.v121", "iw_1.L68" => %"iw_1.v123"); %"pr.15" : L = phi("iw_1.L119" => %"iw_1.pr.27", "iw_1.L68" => %"iw_1.pr.24")]:
    => goto "L16" };
  ir_blk{ @"L16" [%"pr.6" : L = phi("L17" => %"v29", "iw_1.join" => #0)]:
    %"v23" : W = (Cmp Ult L) %"pr.6", #256
    => br %"v23" ? "L17" : "L30" };
  ir_blk{ @"L17":
    %"v25" : L = Shl %"pr.6", #3;
    %"v26" = %"v12" +p %"v25";
    %"chk4" : A = (Check 0 8 Write 1) %"v26";
    store Wl [%"chk4" + 0] <- %"v6";
    %"v29" : L = Add %"pr.6", #1
    => goto poll "L16" };
  ir_blk{ @"L30" [%"pr.9" : L = phi("L31" => %"v49", "L16" => #0)]:
    %"v36" : W = (Cmp Ult L) %"pr.9", %"v6"
    => br %"v36" ? "L31" : "L33" };
  ir_blk{ @"L31":
    %"v39" = %"v4" +p %"pr.9";
    %"chk5" : A = (Check 0 1 Read 1) %"v39";
    %"v40" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"v41" : L = (Ext Uw) %"v40";
    %"v42" : L = Shl %"v41", #3;
    %"v43" = %"v12" +p %"v42";
    %"v46" : L = Sub %"v6", %"pr.9";
    %"v47" : L = Sub %"v46", #1;
    %"chk6" : A = (Check 0 8 Write 1) %"v43";
    store Wl [%"chk6" + 0] <- %"v47";
    %"v49" : L = Add %"pr.9", #1
    => goto poll "L30" };
  ir_blk{ @"L33":
    %"v56" = %"v4" +p %"pr.15";
    call %"v58" : W = $"__GI_memcmp"(P %"v4", P %"v56", L %"v15");
    %"v59" : W = (Cmp Eq W) %"v58", #0
    => br %"v59" ? "L62" : "L51" };
  ir_blk{ @"L62" [%"pr.17" : L = phi("L107" => #0, "L33" => #0, "L200" => %"v215", "L162" => #0); %"pr.14" : L = phi("L107" => %"v122", "L33" => #0, "L200" => %"v212", "L162" => %"v221"); %"pr.3" : L = phi("L107" => %"pr.4", "L33" => %"v2", "L200" => %"pr.4", "L162" => %"pr.4")]:
    %"v67" : L = Add %"pr.14", %"v6";
    %"v69" : W = (Cmp Ule L) %"v67", %"pr.3"
    => br %"v69" ? "L71" : "L70" };
  ir_blk{ @"L70":
    %"v75" = %"v0" +p %"pr.3";
    %"v77" : L = Add %"v6", #512;
    call %"v78" : L = $"__GI___strnlen"(P %"v75", L %"v77");
    %"v79" : L = Add %"pr.3", %"v78";
    %"v84" : W = (Cmp Ule L) %"v67", %"v79"
    => goto "L71" };
  ir_blk{ @"L71" [%"v86" : W = phi("L62" => #1, "L70" => %"v84"); %"pr.4" : L = phi("L62" => %"pr.3", "L70" => %"v79")]:
    => br %"v86" ? "L63" : "L52" };
  ir_blk{ @"L63":
    %"v93" : L = Sub %"v67", #1;
    %"v94" = %"v0" +p %"v93";
    %"chk7" : A = (Check 0 1 Read 1) %"v94";
    %"v95" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v96" : L = (Ext Uw) %"v95";
    %"v97" : L = Shl %"v96", #3;
    %"v98" = %"v12" +p %"v97";
    %"chk8" : A = (Check 0 8 Read 1) %"v98";
    %"v99" : L = (RawLoad LdL 0) %"chk8";
    %"v104" : W = (Cmp Ugt L) %"v99", #0
    => br %"v104" ? "L100" : "L102" };
  ir_blk{ @"L100":
    %"v109" : W = (Cmp Ne L) %"pr.17", #0
    => br %"v109" ? "L110" : "L111" };
  ir_blk{ @"L110":
    %"v114" : W = (Cmp Ult L) %"v99", %"pr.15"
    => goto "L111" };
  ir_blk{ @"L111" [%"v116" : W = phi("L100" => #0, "L110" => %"v114")]:
    => br %"v116" ? "L105" : "L107" };
  ir_blk{ @"L105":
    %"v119" : L = Sub %"v6", %"pr.15"
    => goto "L107" };
  ir_blk{ @"L107" [%"pr.18" : L = phi("L105" => %"v119", "L111" => %"v99")]:
    %"v122" : L = Add %"pr.14", %"pr.18"
    => goto poll "L62" };
  ir_blk{ @"L102":
    %"v129" : W = (Cmp Ugt L) %"v15", %"pr.17"
    => br %"v129" ? "L126" : "L125" };
  ir_blk{ @"L125":
    => goto "L126" };
  ir_blk{ @"L126" [%"v132" : L = phi("L125" => %"pr.17", "L102" => %"v15")]:
    %"v135" = %"v4" +p %"v132";
    %"v139" : L = Add %"v132", %"pr.14";
    %"v140" = %"v0" +p %"v139"
    => goto "L141" }] [ir_blk{ @"L141" [%"pr.23" : P = phi("L126" => %"v140", "L142" => %"pr.24"); %"pr.19" : P = phi("L126" => %"v135", "L142" => %"pr.20"); %"pr.5" : L = phi("L126" => %"v132", "L142" => %"v160")]:
    %"v146" : L = Sub %"v6", #1;
    %"v147" : W = (Cmp Ult L) %"pr.5", %"v146"
    => br %"v147" ? "L148" : "L149" };
  ir_blk{ @"L148":
    %"v151" = %"pr.19" +p #1;
    %"chk9" : A = (Check 0 1 Read 1) %"pr.19";
    %"v152" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v154" = %"pr.23" +p #1;
    %"chk10" : A = (Check 0 1 Read 1) %"pr.23";
    %"v155" : W = (RawLoad (LdNarrow Ub) 0) %"chk10";
    %"v156" : W = (Cmp Eq W) %"v152", %"v155"
    => goto "L149" };
  ir_blk{ @"L149" [%"v158" : W = phi("L141" => #0, "L148" => %"v156"); %"pr.24" : P = phi("L141" => %"pr.23", "L148" => %"v154"); %"pr.20" : P = phi("L141" => %"pr.19", "L148" => %"v151")]:
    => br %"v158" ? "L142" : "L143" };
  ir_blk{ @"L142":
    %"v160" : L = Add %"pr.5", #1
    => goto poll "L141" };
  ir_blk{ @"L143":
    %"v167" : W = (Cmp Ule L) %"v146", %"pr.5"
    => br %"v167" ? "L161" : "L162" };
  ir_blk{ @"L161":
    %"v169" : L = Sub %"v15", #1;
    %"v172" = %"v4" +p %"v169";
    %"v176" : L = Add %"v169", %"pr.14";
    %"v177" = %"v0" +p %"v176"
    => goto "L178" };
  ir_blk{ @"L178" [%"pr.25" : P = phi("L161" => %"v177", "L179" => %"pr.26"); %"pr.21" : P = phi("L161" => %"v172", "L179" => %"pr.22"); %"pr.7" : L = phi("L161" => %"v169", "L179" => %"v197")]:
    %"v183" : L = Add %"pr.7", #1;
    %"v184" : W = (Cmp Ult L) %"pr.17", %"v183"
    => br %"v184" ? "L185" : "L186" };
  ir_blk{ @"L185":
    (Flight (a "v188") Sub [(FAddress (t "pr.21")); (FValue (Const 1))] (LowerOf (t "pr.21")));
    %"chk11" : A = (Check 0 1 Read 1) %"pr.21";
    %"v189" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    (Flight (a "v191") Sub [(FAddress (t "pr.25")); (FValue (Const 1))] (LowerOf (t "pr.25")));
    %"chk12" : A = (Check 0 1 Read 1) %"pr.25";
    %"v192" : W = (RawLoad (LdNarrow Ub) 0) %"chk12";
    %"v193" : W = (Cmp Eq W) %"v189", %"v192"
    => goto "L186" };
  ir_blk{ @"L186" [%"v195" : W = phi("L178" => #0, "L185" => %"v193"); %"pr.26" : P = phi("L178" => %"pr.25", "L185" => %"v191"); %"pr.22" : P = phi("L178" => %"pr.21", "L185" => %"v188")]:
    => br %"v195" ? "L179" : "L180" };
  ir_blk{ @"L179":
    %"v197" : L = Sub %"pr.7", #1
    => goto poll "L178" };
  ir_blk{ @"L180":
    %"v204" : L = Add %"pr.17", #1;
    %"v205" : W = (Cmp Ult L) %"v183", %"v204"
    => br %"v205" ? "L198" : "L200" };
  ir_blk{ @"L198":
    %"v208" = %"v0" +p %"pr.14"
    => ret %"v208" };
  ir_blk{ @"L200":
    %"v212" : L = Add %"pr.14", %"pr.15";
    %"v215" : L = Sub %"v6", %"pr.15"
    => goto poll "L62" };
  ir_blk{ @"L162":
    %"v219" : L = Sub %"pr.5", %"v15";
    %"v220" : L = Add %"v219", #1;
    %"v221" : L = Add %"pr.14", %"v220"
    => goto poll "L62" };
  ir_blk{ @"L51":
    %"v229" : L = Sub %"v6", %"v15";
    %"v230" : W = (Cmp Ugt L) %"v15", %"v229"
    => br %"v230" ? "L225" : "L224" };
  ir_blk{ @"L224":
    => goto "L225" };
  ir_blk{ @"L225" [%"v235" : L = phi("L224" => %"v229", "L51" => %"v15")]:
    %"v236" : L = Add %"v235", #1
    => goto "L237" };
  ir_blk{ @"L237" [%"pr.12" : L = phi("L225" => #0, "L275" => %"v282", "L350" => %"v359", "L314" => %"v365"); %"pr.1" : L = phi("L225" => %"v2", "L275" => %"pr.2", "L350" => %"pr.2", "L314" => %"pr.2")]:
    %"v242" : L = Add %"pr.12", %"v6";
    %"v244" : W = (Cmp Ule L) %"v242", %"pr.1"
    => br %"v244" ? "L246" : "L245" };
  ir_blk{ @"L245":
    %"v250" = %"v0" +p %"pr.1";
    %"v252" : L = Add %"v6", #512;
    call %"v253" : L = $"__GI___strnlen"(P %"v250", L %"v252");
    %"v254" : L = Add %"pr.1", %"v253";
    %"v259" : W = (Cmp Ule L) %"v242", %"v254"
    => goto "L246" };
  ir_blk{ @"L246" [%"v261" : W = phi("L237" => #1, "L245" => %"v259"); %"pr.2" : L = phi("L237" => %"pr.1", "L245" => %"v254")]:
    => br %"v261" ? "L238" : "L52" };
  ir_blk{ @"L238":
    %"v268" : L = Sub %"v242", #1;
    %"v269" = %"v0" +p %"v268";
    %"chk13" : A = (Check 0 1 Read 1) %"v269";
    %"v270" : W = (RawLoad (LdNarrow Ub) 0) %"chk13";
    %"v271" : L = (Ext Uw) %"v270";
    %"v272" : L = Shl %"v271", #3;
    %"v273" = %"v12" +p %"v272";
    %"chk14" : A = (Check 0 8 Read 1) %"v273";
    %"v274" : L = (RawLoad LdL 0) %"chk14";
    %"v279" : W = (Cmp Ugt L) %"v274", #0
    => br %"v279" ? "L275" : "L277" };
  ir_blk{ @"L275":
    %"v282" : L = Add %"pr.12", %"v274"
    => goto poll "L237" };
  ir_blk{ @"L277":
    %"v287" = %"v4" +p %"v15";
    %"v291" : L = Add %"v15", %"pr.12";
    %"v292" = %"v0" +p %"v291"
    => goto "L293" };
  ir_blk{ @"L293" [%"pr.31" : P = phi("L277" => %"v292", "L294" => %"pr.32"); %"pr.27" : P = phi("L277" => %"v287", "L294" => %"pr.28"); %"pr.8" : L = phi("L277" => %"v15", "L294" => %"v312")]:
    %"v298" : L = Sub %"v6", #1;
    %"v299" : W = (Cmp Ult L) %"pr.8", %"v298"
    => br %"v299" ? "L300" : "L301" };
  ir_blk{ @"L300":
    %"v303" = %"pr.27" +p #1;
    %"chk15" : A = (Check 0 1 Read 1) %"pr.27";
    %"v304" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v306" = %"pr.31" +p #1;
    %"chk16" : A = (Check 0 1 Read 1) %"pr.31";
    %"v307" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v308" : W = (Cmp Eq W) %"v304", %"v307"
    => goto "L301" };
  ir_blk{ @"L301" [%"v310" : W = phi("L293" => #0, "L300" => %"v308"); %"pr.32" : P = phi("L293" => %"pr.31", "L300" => %"v306"); %"pr.28" : P = phi("L293" => %"pr.27", "L300" => %"v303")]:
    => br %"v310" ? "L294" : "L295" };
  ir_blk{ @"L294":
    %"v312" : L = Add %"pr.8", #1
    => goto poll "L293" };
  ir_blk{ @"L295":
    %"v319" : W = (Cmp Ule L) %"v298", %"pr.8"
    => br %"v319" ? "L313" : "L314" };
  ir_blk{ @"L313":
    %"v321" : L = Sub %"v15", #1;
    %"v324" = %"v4" +p %"v321";
    %"v328" : L = Add %"v321", %"pr.12";
    %"v329" = %"v0" +p %"v328"
    => goto "L330" };
  ir_blk{ @"L330" [%"pr.33" : P = phi("L313" => %"v329", "L331" => %"pr.34"); %"pr.29" : P = phi("L313" => %"v324", "L331" => %"pr.30"); %"pr.10" : L = phi("L313" => %"v321", "L331" => %"v347")]:
    %"v334" : W = (Cmp Ne L) %"pr.10", #18446744073709551615
    => br %"v334" ? "L335" : "L336" };
  ir_blk{ @"L335":
    (Flight (a "v338") Sub [(FAddress (t "pr.29")); (FValue (Const 1))] (LowerOf (t "pr.29")));
    %"chk17" : A = (Check 0 1 Read 1) %"pr.29";
    %"v339" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    (Flight (a "v341") Sub [(FAddress (t "pr.33")); (FValue (Const 1))] (LowerOf (t "pr.33")));
    %"chk18" : A = (Check 0 1 Read 1) %"pr.33";
    %"v342" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v343" : W = (Cmp Eq W) %"v339", %"v342"
    => goto "L336" };
  ir_blk{ @"L336" [%"v345" : W = phi("L330" => #0, "L335" => %"v343"); %"pr.34" : P = phi("L330" => %"pr.33", "L335" => %"v341"); %"pr.30" : P = phi("L330" => %"pr.29", "L335" => %"v338")]:
    => br %"v345" ? "L331" : "L332" };
  ir_blk{ @"L331":
    %"v347" : L = Sub %"pr.10", #1
    => goto poll "L330" };
  ir_blk{ @"L332":
    %"v352" : W = (Cmp Eq L) %"pr.10", #18446744073709551615
    => br %"v352" ? "L348" : "L350" };
  ir_blk{ @"L348":
    %"v355" = %"v0" +p %"pr.12"
    => ret %"v355" };
  ir_blk{ @"L350":
    %"v359" : L = Add %"pr.12", %"v236"
    => goto poll "L237" };
  ir_blk{ @"L314":
    %"v363" : L = Sub %"pr.8", %"v15";
    %"v364" : L = Add %"v363", #1;
    %"v365" : L = Add %"pr.12", %"v364"
    => goto poll "L237" };
  ir_blk{ @"L52":
    => ret #0 }])) }.

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

Definition hello_image_fn___GI_strstr : func :=
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

Definition hello_image_fn___GI___strtok_r : func :=
  ir_fn{ "export" "__GI___strtok_r"(P %"v0", P %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v11" : L = Ptoi %"v0";
    %"v12" : L = Ptoi #0;
    %"v13" : W = (Cmp Eq L) %"v11", %"v12"
    => br %"v13" ? "L7" : "L9";
  @"L7":
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L9";
  @"L9" [%"pr.1" : P = phi("L7" => %"v15", "start" => %"v0")]:
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v20" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => br %"v21" ? "L16" : "L18";
  @"L16":
    %"chk2" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk2" + 0] <- %"pr.1"
    => ret #0;
  @"L18":
    call %"v28" : L = $"__GI_strspn"(P %"pr.1", P %"v2");
    %"v29" = %"pr.1" +p %"v28";
    %"chk3" : A = (Check 0 1 Read 1) %"v29";
    %"v34" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v35" : W = (Cmp Eq W) %"v34", #0
    => br %"v35" ? "L30" : "L32";
  @"L30":
    %"chk4" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk4" + 0] <- %"v29"
    => ret #0;
  @"L32":
    call %"v42" : L = $"__GI_strcspn"(P %"v29", P %"v2");
    %"v43" = %"v29" +p %"v42";
    %"chk5" : A = (Check 0 1 Read 1) %"v43";
    %"v48" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v49" : W = (Cmp Eq W) %"v48", #0
    => br %"v49" ? "L44" : "L46";
  @"L44":
    %"chk6" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk6" + 0] <- %"v43"
    => ret %"v29";
  @"L46":
    %"chk7" : A = (Renew 0 1 Write 1) %"chk5", %"v43";
    store Wb [%"chk7" + 0] <- #0;
    %"v57" = %"v43" +p #1;
    %"chk8" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk8" + 0] <- %"v57"
    => ret %"v29"
} }.

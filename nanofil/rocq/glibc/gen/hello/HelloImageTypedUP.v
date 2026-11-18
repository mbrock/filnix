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

Definition hello_image_fn_glibc_libc_start'23update_active : func :=
  ir_fn{ "local" "glibc_libc_start#update_active"(P %"v0") -> RVoid {
  @"start":
    code ((app (app (app ir[ %"v1523" : P = (Alloc 4) #4;
      %"v1524" : P = (Alloc 4) #4;
      %"v1525" : P = (Alloc 4) #4;
      %"v1526" : P = (Alloc 4) #4;
      %"v1562" : P = (Alloc 4) #80;
      %"v1563" : P = (Alloc 4) #80;
      %"v3" = %"v0" +p #20;
      %"v5" = %"v3" +p #16;
      %"v6" = %"v5" +p #8;
      %"chk0" : A = (Check 0 4 Read 1) %"v6";
      %"v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
      %"v11" = %"v3" +p #8;
      %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v11";
      %"v12" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v14" : W = And %"v12", #1;
      %"v15" : W = Or %"v7", %"v14";
      %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v6";
      store Ww [%"chk2" + 0] <- %"v15";
      %"v21" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v26" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v28" : W = And %"v26", #2;
      %"v29" : W = Or %"v21", %"v28";
      store Ww [%"chk2" + 0] <- %"v29";
      %"v35" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v40" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v42" : W = And %"v40", #512;
      %"v43" : W = Or %"v35", %"v42";
      store Ww [%"chk2" + 0] <- %"v43";
      %"v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v54" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v56" : W = And %"v54", #8192;
      %"v57" : W = Or %"v49", %"v56";
      store Ww [%"chk2" + 0] <- %"v57";
      %"v63" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v68" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v70" : W = And %"v68", #524288;
      %"v71" : W = Or %"v63", %"v70";
      store Ww [%"chk2" + 0] <- %"v71";
      %"v77" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v82" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v84" : W = And %"v82", #1048576] ir[ %"v85" : W = Or %"v77", %"v84";
      store Ww [%"chk2" + 0] <- %"v85";
      %"v91" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v96" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v98" : W = And %"v96", #4194304;
      %"v99" : W = Or %"v91", %"v98";
      store Ww [%"chk2" + 0] <- %"v99";
      %"v105" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v110" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v112" : W = And %"v110", #8388608;
      %"v113" : W = Or %"v105", %"v112";
      store Ww [%"chk2" + 0] <- %"v113";
      %"v119" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v124" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v126" : W = And %"v124", #33554432;
      %"v127" : W = Or %"v119", %"v126";
      store Ww [%"chk2" + 0] <- %"v127";
      %"v133" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v138" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v140" : W = And %"v138", #134217728;
      %"v141" : W = Or %"v133", %"v140";
      store Ww [%"chk2" + 0] <- %"v141";
      %"v146" = %"v5" +p #12;
      %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v146";
      %"v147" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v151" = %"v3" +p #12;
      %"v152" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v154" : W = And %"v152", #16;
      %"v155" : W = Or %"v147", %"v154";
      store Ww [%"chk30" + 0] <- %"v155";
      %"v161" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v166" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v168" : W = And %"v166", #256;
      %"v169" : W = Or %"v161", %"v168";
      store Ww [%"chk30" + 0] <- %"v169";
      %"v175" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v180" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v182" : W = And %"v180", #32768;
      %"v183" : W = Or %"v175", %"v182";
      store Ww [%"chk30" + 0] <- %"v183";
      %"v189" : W = (RawLoad (LdNarrow Uw) 0) %"chk30"]) (app ir[ %"v194" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v196" : W = And %"v194", #524288;
      %"v197" : W = Or %"v189", %"v196";
      store Ww [%"chk30" + 0] <- %"v197";
      %"v203" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v208" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v210" : W = And %"v208", #8388608;
      %"v211" : W = Or %"v203", %"v210";
      store Ww [%"chk30" + 0] <- %"v211";
      %"v217" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v222" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v224" : W = And %"v222", #16777216;
      %"v225" : W = Or %"v217", %"v224";
      store Ww [%"chk30" + 0] <- %"v225";
      %"v231" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v236" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v238" : W = And %"v236", #33554432;
      %"v239" : W = Or %"v231", %"v238";
      store Ww [%"chk30" + 0] <- %"v239";
      %"v245" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v250" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v252" : W = And %"v250", #67108864;
      %"v253" : W = Or %"v245", %"v252";
      store Ww [%"chk30" + 0] <- %"v253";
      %"v259" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v264" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v266" : W = And %"v264", #268435456;
      %"v267" : W = Or %"v259", %"v266";
      store Ww [%"chk30" + 0] <- %"v267";
      %"v270" = %"v3" +p #32;
      %"v271" = %"v270" +p #16;
      %"v272" = %"v271" +p #4;
      %"chk57" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v272";
      %"v273" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v277" = %"v270" +p #4;
      %"v278" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v280" : W = And %"v278", #8;
      %"v281" : W = Or %"v273", %"v280";
      store Ww [%"chk57" + 0] <- %"v281";
      %"v287" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v292" : W = (RawLoad (LdNarrow Uw) 8) %"chk30"] ir[ %"v294" : W = And %"v292", #16;
      %"v295" : W = Or %"v287", %"v294";
      store Ww [%"chk57" + 0] <- %"v295";
      %"v301" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v306" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v308" : W = And %"v306", #256;
      %"v309" : W = Or %"v301", %"v308";
      store Ww [%"chk57" + 0] <- %"v309";
      %"v315" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v320" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v322" : W = And %"v320", #512;
      %"v323" : W = Or %"v315", %"v322";
      store Ww [%"chk57" + 0] <- %"v323";
      %"v329" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v334" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v336" : W = And %"v334", #262144;
      %"v337" : W = Or %"v329", %"v336";
      store Ww [%"chk57" + 0] <- %"v337";
      %"v343" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v348" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v350" : W = And %"v348", #524288;
      %"v351" : W = Or %"v343", %"v350";
      store Ww [%"chk57" + 0] <- %"v351";
      %"v357" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v362" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v364" : W = And %"v362", #8388608;
      %"v365" : W = Or %"v357", %"v364";
      store Ww [%"chk57" + 0] <- %"v365";
      %"v371" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v376" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v378" : W = And %"v376", #16777216;
      %"v379" : W = Or %"v371", %"v378";
      store Ww [%"chk57" + 0] <- %"v379";
      %"v385" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v390" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v392" : W = And %"v390", #536870912;
      %"v393" : W = Or %"v385", %"v392";
      store Ww [%"chk57" + 0] <- %"v393";
      %"v398" = %"v271" +p #8;
      %"chk84" : A = (HalfCheck Upper 0 4 Read 1) %"chk57", %"v398";
      %"v399" : W = (RawLoad (LdNarrow Uw) 0) %"chk84"])) (app (app ir[ %"v403" = %"v270" +p #8;
      %"v404" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v406" : W = And %"v404", #1;
      %"v407" : W = Or %"v399", %"v406";
      store Ww [%"chk84" + 0] <- %"v407";
      %"v413" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v418" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v420" : W = And %"v418", #16;
      %"v421" : W = Or %"v413", %"v420";
      store Ww [%"chk84" + 0] <- %"v421";
      %"v427" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v432" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v434" : W = And %"v432", #32;
      %"v435" : W = Or %"v427", %"v434";
      store Ww [%"chk84" + 0] <- %"v435";
      %"v441" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v446" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v448" : W = And %"v446", #256;
      %"v449" : W = Or %"v441", %"v448";
      store Ww [%"chk84" + 0] <- %"v449";
      %"v455" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v460" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v462" : W = And %"v460", #4194304;
      %"v463" : W = Or %"v455", %"v462";
      store Ww [%"chk84" + 0] <- %"v463";
      %"v469" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v474" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v476" : W = And %"v474", #1073741824;
      %"v477" : W = Or %"v469", %"v476";
      store Ww [%"chk2" + 0] <- %"v477";
      %"v483" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v488" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v490" : W = And %"v488", #33554432;
      %"v491" : W = Or %"v483", %"v490";
      store Ww [%"chk84" + 0] <- %"v491";
      %"v497" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v502" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v504" : W = And %"v502", #134217728;
      %"v505" : W = Or %"v497", %"v504";
      store Ww [%"chk84" + 0] <- %"v505";
      %"v511" : W = (RawLoad (LdNarrow Uw) 0) %"chk84"] ir[ %"v516" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v518" : W = And %"v516", #268435456;
      %"v519" : W = Or %"v511", %"v518";
      store Ww [%"chk84" + 0] <- %"v519";
      %"v524" = %"v271" +p #12;
      %"chk111" : A = (HalfCheck Upper 0 4 Read 1) %"chk57", %"v524";
      %"v525" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v529" = %"v270" +p #12;
      %"v530" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v532" : W = And %"v530", #16;
      %"v533" : W = Or %"v525", %"v532";
      store Ww [%"chk111" + 0] <- %"v533";
      %"v539" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v544" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v546" : W = And %"v544", #2048;
      %"v547" : W = Or %"v539", %"v546";
      store Ww [%"chk111" + 0] <- %"v547";
      %"v553" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v558" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v560" : W = And %"v558", #16384;
      %"v561" : W = Or %"v553", %"v560";
      store Ww [%"chk111" + 0] <- %"v561";
      %"v567" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v572" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v574" : W = And %"v572", #65536;
      %"v575" : W = Or %"v567", %"v574";
      store Ww [%"chk111" + 0] <- %"v575";
      %"v578" = %"v3" +p #64;
      %"v579" = %"v578" +p #16;
      %"v580" = %"v579" +p #8;
      %"chk123" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v580";
      %"v581" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v585" = %"v578" +p #8;
      %"v586" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v588" : W = And %"v586", #1;
      %"v589" : W = Or %"v581", %"v588";
      store Ww [%"chk123" + 0] <- %"v589";
      %"v595" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v600" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v602" : W = And %"v600", #32;
      %"v603" : W = Or %"v595", %"v602"]) (app ir[ store Ww [%"chk123" + 0] <- %"v603";
      %"v609" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v614" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v616" : W = And %"v614", #64;
      %"v617" : W = Or %"v609", %"v616";
      store Ww [%"chk123" + 0] <- %"v617";
      %"v623" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v628" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v630" : W = And %"v628", #256;
      %"v631" : W = Or %"v623", %"v630";
      store Ww [%"chk123" + 0] <- %"v631";
      %"v637" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v642" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v644" : W = And %"v642", #2097152;
      %"v645" : W = Or %"v637", %"v644";
      store Ww [%"chk123" + 0] <- %"v645";
      %"v650" = %"v579" +p #12;
      %"chk138" : A = (HalfCheck Upper 0 4 Read 1) %"chk123", %"v650";
      %"v651" : W = (RawLoad (LdNarrow Uw) 0) %"chk138";
      %"v655" = %"v578" +p #12;
      %"v656" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk123";
      %"v658" : W = And %"v656", #134217728;
      %"v659" : W = Or %"v651", %"v658";
      store Ww [%"chk138" + 0] <- %"v659";
      %"v662" = %"v3" +p #160;
      %"v663" = %"v662" +p #16;
      %"v664" = %"v663" +p #4;
      %"chk141" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v664";
      %"v665" : W = (RawLoad (LdNarrow Uw) 0) %"chk141";
      %"v669" = %"v662" +p #4;
      %"v670" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk141";
      %"v672" : W = And %"v670", #512;
      %"v673" : W = Or %"v665", %"v672";
      store Ww [%"chk141" + 0] <- %"v673";
      %"v676" = %"v3" +p #192;
      %"v677" = %"v676" +p #16;
      %"chk144" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v677";
      %"v678" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v682" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v684" : W = And %"v682", #8;
      %"v685" : W = Or %"v678", %"v684"] ir[ store Ww [%"chk144" + 0] <- %"v685";
      %"v690" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v694" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v696" : W = And %"v694", #128;
      %"v697" : W = Or %"v690", %"v696";
      store Ww [%"chk144" + 0] <- %"v697";
      %"v702" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v706" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v708" : W = And %"v706", #1024;
      %"v709" : W = Or %"v702", %"v708";
      store Ww [%"chk144" + 0] <- %"v709";
      %"v714" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v718" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v720" : W = And %"v718", #2048;
      %"v721" : W = Or %"v714", %"v720";
      store Ww [%"chk144" + 0] <- %"v721";
      %"v726" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v730" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v732" : W = And %"v730", #4096;
      %"v733" : W = Or %"v726", %"v732";
      store Ww [%"chk144" + 0] <- %"v733";
      %"v738" = %"v677" +p #12;
      %"chk159" : A = (HalfCheck Upper 0 4 Read 1) %"chk144", %"v738";
      %"v739" : W = (RawLoad (LdNarrow Uw) 0) %"chk159";
      %"v743" = %"v676" +p #12;
      %"v744" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk144";
      %"v746" : W = And %"v744", #16384;
      %"v747" : W = Or %"v739", %"v746";
      store Ww [%"chk159" + 0] <- %"v747";
      %"v750" = %"v3" +p #256;
      %"v751" = %"v750" +p #16;
      %"v752" = %"v751" +p #4;
      %"chk162" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v752";
      %"v753" : W = (RawLoad (LdNarrow Uw) 0) %"chk162";
      %"v757" = %"v750" +p #4;
      %"v758" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk162";
      %"v760" : W = And %"v758", #16;
      %"v761" : W = Or %"v753", %"v760";
      store Ww [%"chk162" + 0] <- %"v761";
      %"v769" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v771" : W = And %"v769", #2048;
      %"v773" : W = (Cmp Eq W) %"v771", #0]))))
    => br %"v773" ? "L762" : "L764";
  @"L762":
    %"v775" = %"v0" +p #20;
    %"v776" = %"v775" +p #32;
    %"v777" = %"v776" +p #16;
    %"v778" = %"v777" +p #4;
    %"v779" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
    %"v783" = %"v776" +p #4;
    %"v784" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
    %"v786" : W = And %"v784", #2048;
    %"v787" : W = Or %"v779", %"v786";
    store Ww [%"chk57" + 0] <- %"v787"
    => goto "L764";
  @"L764":
    %"v793" = %"v0" +p #20;
    %"v795" = %"v793" +p #8;
    %"v796" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v798" : W = And %"v796", #134217728;
    %"v799" : W = (Cmp Ne W) %"v798", #0
    => br %"v799" ? "L789" : "L791";
  @"L789":
    %"v802" = %"v0" +p #20;
    %"v803" = %"v802" +p #192;
    %"v804" = %"v803" +p #16;
    %"v805" = %"v804" +p #12;
    %"v806" : W = (RawLoad (LdNarrow Uw) 0) %"chk159";
    %"v810" = %"v803" +p #12;
    %"v811" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk144";
    %"v813" : W = And %"v811", #524288;
    %"v814" : W = Or %"v806", %"v813";
    store Ww [%"chk159" + 0] <- %"v814";
    call %"v815" : L = $"zxgetbv"();
    %"v819" : W = Copy %"v815";
    %"v823" : W = And %"v819", #6;
    %"v827" : W = (Cmp Eq W) %"v823", #6
    => br %"v827" ? "L816" : "L818";
  @"L816":
    %"v832" = %"v0" +p #20;
    %"v834" = %"v832" +p #8;
    %"chk173" : A = (Renew 0 4 Read 1) %"chk1", %"v834";
    %"v835" : W = (RawLoad (LdNarrow Uw) 0) %"chk173";
    %"v837" : W = And %"v835", #268435456;
    %"v838" : W = (Cmp Ne W) %"v837", #0
    => br %"v838" ? "L828" : "L830";
  @"L828":
    %"v842" = %"v0" +p #20;
    %"v844" = %"v842" +p #16;
    %"v845" = %"v844" +p #8;
    %"chk174" : A = (Renew 0 4 Read 1) %"chk0", %"v845";
    %"v846" : W = (RawLoad (LdNarrow Uw) 0) %"chk174";
    %"v848" : W = Or %"v846", #268435456;
    %"chk175" : A = (Renew 0 4 Write 1) %"chk0", %"v845";
    store Ww [%"chk175" + 0] <- %"v848";
    %"v854" = %"v842" +p #32;
    %"v855" = %"v854" +p #4;
    %"chk176" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v855";
    %"v856" : W = (RawLoad (LdNarrow Uw) 0) %"chk176";
    %"v858" : W = And %"v856", #32;
    %"v859" : W = (Cmp Ne W) %"v858", #0
    => br %"v859" ? "L849" : "L851";
  @"L849":
    %"v861" = %"v0" +p #20;
    %"v862" = %"v861" +p #32;
    %"v863" = %"v862" +p #16;
    %"v864" = %"v863" +p #4;
    %"chk177" : A = (Renew 0 4 Read 1) %"chk57", %"v864";
    %"v865" : W = (RawLoad (LdNarrow Uw) 0) %"chk177";
    %"v867" : W = Or %"v865", #32;
    store Ww [%"chk177" + 0] <- %"v867";
    %"v869" = %"v0" +p #340;
    %"chk179" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v869";
    %"v871" : W = (RawLoad (LdNarrow Uw) 0) %"chk179";
    %"v872" : W = Or %"v871", #512;
    store Ww [%"chk179" + 0] <- %"v872"
    => goto "L851";
  @"L851":
    %"v874" = %"v0" +p #20;
    %"v875" = %"v874" +p #192;
    %"v876" = %"v875" +p #16;
    %"chk181" : A = (Renew 0 4 Read 1) %"chk144", %"v876";
    %"v877" : W = (RawLoad (LdNarrow Uw) 0) %"chk181";
    %"v881" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk181";
    %"v883" : W = And %"v881", #8388608;
    %"v884" : W = Or %"v877", %"v883";
    store Ww [%"chk181" + 0] <- %"v884";
    %"v889" = %"v876" +p #12;
    %"chk184" : A = (Renew 0 4 Read 1) %"chk159", %"v889";
    %"v890" : W = (RawLoad (LdNarrow Uw) 0) %"chk184";
    %"v894" = %"v875" +p #12;
    %"v895" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk181";
    %"v897" : W = And %"v895", #32;
    %"v898" : W = Or %"v890", %"v897";
    store Ww [%"chk184" + 0] <- %"v898";
    %"v903" : W = (RawLoad (LdNarrow Uw) 0) %"chk181";
    %"v907" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk181";
    %"v909" : W = And %"v907", #16;
    %"v910" : W = Or %"v903", %"v909";
    store Ww [%"chk181" + 0] <- %"v910";
    %"v916" : W = (RawLoad (LdNarrow Uw) 0) %"chk184";
    %"v921" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk181";
    %"v923" : W = And %"v921", #16;
    %"v924" : W = Or %"v916", %"v923";
    store Ww [%"chk184" + 0] <- %"v924";
    %"v928" = %"v874" +p #16;
    %"v929" = %"v928" +p #8;
    %"v930" : W = (RawLoad (LdNarrow Uw) 0) %"chk175";
    %"v934" = %"v874" +p #8;
    %"v935" : W = (RawLoad (LdNarrow Uw) 0) %"chk173";
    %"v937" : W = And %"v935", #4096;
    %"v938" : W = Or %"v930", %"v937";
    store Ww [%"chk175" + 0] <- %"v938";
    %"v941" = %"v874" +p #32;
    %"v942" = %"v941" +p #16;
    %"v943" = %"v942" +p #8;
    %"v944" : W = (RawLoad (LdNarrow Uw) 20) %"chk176";
    %"v948" = %"v941" +p #8;
    %"v949" : W = (RawLoad (LdNarrow Uw) 4) %"chk176";
    %"v951" : W = And %"v949", #512;
    %"v952" : W = Or %"v944", %"v951";
    store Ww [%"chk176" + 20] <- %"v952";
    %"v958" : W = (RawLoad (LdNarrow Uw) 20) %"chk176";
    %"v963" : W = (RawLoad (LdNarrow Uw) 4) %"chk176";
    %"v965" : W = And %"v963", #1024;
    %"v966" : W = Or %"v958", %"v965";
    store Ww [%"chk176" + 20] <- %"v966";
    %"v969" = %"v874" +p #64;
    %"v970" = %"v969" +p #16;
    %"v971" = %"v970" +p #8;
    %"v972" : W = (RawLoad (LdNarrow Uw) 52) %"chk176";
    %"v976" = %"v969" +p #8;
    %"v977" : W = (RawLoad (LdNarrow Uw) 36) %"chk176";
    %"v979" : W = And %"v977", #2048;
    %"v980" : W = Or %"v972", %"v979";
    store Ww [%"chk176" + 52] <- %"v980";
    %"v986" : W = (RawLoad (LdNarrow Uw) 0) %"chk175";
    %"v991" : W = (RawLoad (LdNarrow Uw) 0) %"chk173";
    %"v993" : W = And %"v991", #536870912;
    %"v994" : W = Or %"v986", %"v993";
    store Ww [%"chk175" + 0] <- %"v994"
    => goto "L830";
  @"L830" [%"pr.2" : W = phi("L851" => #3, "L816" => #1)]:
    %"v998" : W = Copy %"v815";
    %"v1004" : W = And %"v998", #224;
    %"v1010" : W = (Cmp Eq W) %"v1004", #224
    => br %"v1010" ? "L995" : "L818";
  @"L995":
    %"v1012" : W = Or %"pr.2", #4;
    %"v1017" = %"v0" +p #20;
    %"v1018" = %"v1017" +p #32;
    %"v1019" = %"v1018" +p #4;
    %"chk208" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1019";
    %"v1020" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
    %"v1022" : W = And %"v1020", #65536;
    %"v1023" : W = (Cmp Ne W) %"v1022", #0
    => br %"v1023" ? "L1013" : "L818";
  @"L1013":
    code ((app ir[ %"v1025" = %"v0" +p #20;
      %"v1026" = %"v1025" +p #32;
      %"v1027" = %"v1026" +p #16;
      %"v1028" = %"v1027" +p #4;
      %"chk209" : A = (Renew 0 4 Read 1) %"chk57", %"v1028";
      %"v1029" : W = (RawLoad (LdNarrow Uw) 0) %"chk209";
      %"v1031" : W = Or %"v1029", #65536;
      %"chk210" : A = (Renew 0 4 Write 1) %"chk57", %"v1028";
      store Ww [%"chk210" + 0] <- %"v1031";
      %"v1037" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1041" = %"v1026" +p #4;
      %"v1042" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1044" : W = And %"v1042", #268435456;
      %"v1045" : W = Or %"v1037", %"v1044";
      store Ww [%"chk210" + 0] <- %"v1045";
      %"v1051" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1056" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1058" : W = And %"v1056", #134217728;
      %"v1059" : W = Or %"v1051", %"v1058";
      store Ww [%"chk210" + 0] <- %"v1059";
      %"v1065" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1070" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1072" : W = And %"v1070", #67108864;
      %"v1073" : W = Or %"v1065", %"v1072";
      store Ww [%"chk210" + 0] <- %"v1073";
      %"v1079" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1084" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1086" : W = And %"v1084", #2147483648;
      %"v1087" : W = Or %"v1079", %"v1086";
      store Ww [%"chk210" + 0] <- %"v1087";
      %"v1093" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1098" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1100" : W = And %"v1098", #131072;
      %"v1101" : W = Or %"v1093", %"v1100";
      store Ww [%"chk210" + 0] <- %"v1101";
      %"v1107" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1112" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1114" : W = And %"v1112", #1073741824;
      %"v1115" : W = Or %"v1107", %"v1114";
      store Ww [%"chk210" + 0] <- %"v1115";
      %"v1120" = %"v1027" +p #12;
      %"chk229" : A = (Renew 0 4 Read 1) %"chk111", %"v1120";
      %"v1121" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1125" = %"v1026" +p #12;
      %"v1126" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1128" : W = And %"v1126", #8;
      %"v1129" : W = Or %"v1121", %"v1128";
      store Ww [%"chk229" + 0] <- %"v1129";
      %"v1135" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1140" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1142" : W = And %"v1140", #4] ir[ %"v1143" : W = Or %"v1135", %"v1142";
      store Ww [%"chk229" + 0] <- %"v1143";
      %"v1148" = %"v1027" +p #8;
      %"v1149" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1153" = %"v1026" +p #8;
      %"v1154" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1156" : W = And %"v1154", #4096;
      %"v1157" : W = Or %"v1149", %"v1156";
      store Ww [%"chk229" + (-4)] <- %"v1157";
      %"v1163" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1168" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1170" : W = And %"v1168", #2097152;
      %"v1171" : W = Or %"v1163", %"v1170";
      store Ww [%"chk210" + 0] <- %"v1171";
      %"v1177" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1182" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1184" : W = And %"v1182", #2;
      %"v1185" : W = Or %"v1177", %"v1184";
      store Ww [%"chk229" + (-4)] <- %"v1185";
      %"v1191" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1196" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1198" : W = And %"v1196", #64;
      %"v1199" : W = Or %"v1191", %"v1198";
      store Ww [%"chk229" + (-4)] <- %"v1199";
      %"v1205" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1210" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1212" : W = And %"v1210", #2048;
      %"v1213" : W = Or %"v1205", %"v1212";
      store Ww [%"chk229" + (-4)] <- %"v1213";
      %"v1219" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1224" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1226" : W = And %"v1224", #16384;
      %"v1227" : W = Or %"v1219", %"v1226";
      store Ww [%"chk229" + (-4)] <- %"v1227";
      %"v1233" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1238" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1240" : W = And %"v1238", #256;
      %"v1241" : W = Or %"v1233", %"v1240";
      store Ww [%"chk229" + 0] <- %"v1241";
      %"v1244" = %"v1025" +p #192;
      %"v1245" = %"v1244" +p #16;
      %"chk256" : A = (Renew 0 4 Read 1) %"chk144", %"v1245";
      %"v1246" : W = (RawLoad (LdNarrow Uw) 0) %"chk256";
      %"v1250" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk256";
      %"v1252" : W = And %"v1250", #32;
      %"v1253" : W = Or %"v1246", %"v1252";
      store Ww [%"chk256" + 0] <- %"v1253";
      %"v1259" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1264" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1266" : W = And %"v1264", #8388608;
      %"v1267" : W = Or %"v1259", %"v1266";
      store Ww [%"chk229" + 0] <- %"v1267"]))
    => goto "L818";
  @"L818" [%"pr.1" : W = phi("L1013" => %"v1012", "L995" => %"v1012", "L830" => %"pr.2", "L789" => #1)]:
    %"v1272" = %"v0" +p #20;
    %"v1273" = %"v1272" +p #192;
    %"v1274" = %"v1273" +p #12;
    %"chk262" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1274";
    %"v1275" : W = (RawLoad (LdNarrow Uw) 0) %"chk262";
    %"v1277" : W = And %"v1275", #524288;
    %"v1278" : W = (Cmp Ne W) %"v1277", #0
    => br %"v1278" ? "L1279" : "L1280";
  @"L1279":
    %"v1282" = %"v0" +p #4;
    %"chk263" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v1282";
    %"v1283" : W = (RawLoad (LdNarrow Sw) 0) %"chk263";
    %"v1284" : W = (Cmp Sge W) %"v1283", #36
    => goto "L1280";
  @"L1280" [%"v1286" : W = phi("L818" => #0, "L1279" => %"v1284")]:
    => br %"v1286" ? "L1268" : "L1270";
  @"L1268":
    %"v1288" = %"v0" +p #20;
    %"v1289" = %"v1288" +p #288;
    %"v1293" = %"v1289" +p #4;
    %"v1297" = %"v1289" +p #8;
    %"v1301" = %"v1289" +p #12;
    call void $"zcpuid_count"(W #36, W #0, P %"v1289", P %"v1293", P %"v1297", P %"v1301");
    %"v1306" : W = And %"pr.1", #1
    => br %"v1306" ? "L1302" : "L1304";
  @"L1302":
    %"v1308" = %"v0" +p #20;
    %"v1309" = %"v1308" +p #288;
    %"v1310" = %"v1309" +p #16;
    %"v1311" = %"v1310" +p #4;
    %"chk264" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1311";
    %"v1312" : W = (RawLoad (LdNarrow Uw) 0) %"chk264";
    %"v1316" = %"v1309" +p #4;
    %"chk265" : A = (HalfCheck Lower 0 4 Read 1) %"chk264", %"v1316";
    %"v1317" : W = (RawLoad (LdNarrow Uw) 0) %"chk265";
    %"v1319" : W = And %"v1317", #65536;
    %"v1320" : W = Or %"v1312", %"v1319";
    %"chk266" : A = (Renew 0 4 Write 1) %"chk264", %"v1311";
    store Ww [%"chk266" + 0] <- %"v1320"
    => goto "L1304";
  @"L1304":
    %"v1325" : W = And %"pr.1", #2
    => br %"v1325" ? "L1321" : "L1323";
  @"L1321":
    %"v1327" = %"v0" +p #20;
    %"v1328" = %"v1327" +p #288;
    %"v1329" = %"v1328" +p #16;
    %"v1330" = %"v1329" +p #4;
    %"chk267" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1330";
    %"v1331" : W = (RawLoad (LdNarrow Uw) 0) %"chk267";
    %"v1335" = %"v1328" +p #4;
    %"chk268" : A = (HalfCheck Lower 0 4 Read 1) %"chk267", %"v1335";
    %"v1336" : W = (RawLoad (LdNarrow Uw) 0) %"chk268";
    %"v1338" : W = And %"v1336", #131072;
    %"v1339" : W = Or %"v1331", %"v1338";
    %"chk269" : A = (Renew 0 4 Write 1) %"chk267", %"v1330";
    store Ww [%"chk269" + 0] <- %"v1339"
    => goto "L1323";
  @"L1323":
    %"v1344" : W = And %"pr.1", #4
    => br %"v1344" ? "L1340" : "L1270";
  @"L1340":
    %"v1346" = %"v0" +p #20;
    %"v1347" = %"v1346" +p #288;
    %"v1348" = %"v1347" +p #16;
    %"v1349" = %"v1348" +p #4;
    %"chk270" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1349";
    %"v1350" : W = (RawLoad (LdNarrow Uw) 0) %"chk270";
    %"v1354" = %"v1347" +p #4;
    %"chk271" : A = (HalfCheck Lower 0 4 Read 1) %"chk270", %"v1354";
    %"v1355" : W = (RawLoad (LdNarrow Uw) 0) %"chk271";
    %"v1357" : W = And %"v1355", #262144;
    %"v1358" : W = Or %"v1350", %"v1357";
    %"chk272" : A = (Renew 0 4 Write 1) %"chk270", %"v1349";
    store Ww [%"chk272" + 0] <- %"v1358"
    => goto "L1270";
  @"L1270":
    %"v1362" : W = Copy %"v815";
    %"v1366" : W = And %"v1362", #393216;
    %"v1370" : W = (Cmp Eq W) %"v1366", #393216
    => br %"v1370" ? "L1359" : "L1361";
  @"L1359":
    %"v1372" = %"v0" +p #20;
    %"v1373" = %"v1372" +p #32;
    %"v1374" = %"v1373" +p #16;
    %"v1375" = %"v1374" +p #12;
    %"chk273" : A = (Renew 0 4 Read 1) %"chk111", %"v1375";
    %"v1376" : W = (RawLoad (LdNarrow Uw) 0) %"chk273";
    %"v1380" = %"v1373" +p #12;
    %"chk274" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1380";
    %"v1381" : W = (RawLoad (LdNarrow Uw) 0) %"chk274";
    %"v1383" : W = And %"v1381", #4194304;
    %"v1384" : W = Or %"v1376", %"v1383";
    %"chk275" : A = (Renew 0 4 Write 1) %"chk111", %"v1375";
    store Ww [%"chk275" + 0] <- %"v1384";
    %"v1390" : W = (RawLoad (LdNarrow Uw) 0) %"chk275";
    %"v1395" : W = (RawLoad (LdNarrow Uw) 0) %"chk274";
    %"v1397" : W = And %"v1395", #16777216;
    %"v1398" : W = Or %"v1390", %"v1397";
    store Ww [%"chk275" + 0] <- %"v1398";
    %"v1404" : W = (RawLoad (LdNarrow Uw) 0) %"chk275";
    %"v1409" : W = (RawLoad (LdNarrow Uw) 0) %"chk274";
    %"v1411" : W = And %"v1409", #33554432;
    %"v1412" : W = Or %"v1404", %"v1411";
    store Ww [%"chk275" + 0] <- %"v1412";
    %"v1415" = %"v1372" +p #192;
    %"v1416" = %"v1415" +p #16;
    %"chk282" : A = (Renew 0 4 Read 1) %"chk144", %"v1416";
    %"v1417" : W = (RawLoad (LdNarrow Uw) 0) %"chk282";
    %"v1421" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk282";
    %"v1423" : W = And %"v1421", #2097152;
    %"v1424" : W = Or %"v1417", %"v1423";
    store Ww [%"chk282" + 0] <- %"v1424";
    %"v1429" = %"v1416" +p #12;
    %"chk285" : A = (Renew 0 4 Read 1) %"chk159", %"v1429";
    %"v1430" : W = (RawLoad (LdNarrow Uw) 0) %"chk285";
    %"v1434" = %"v1415" +p #12;
    %"v1435" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk282";
    %"v1437" : W = And %"v1435", #256;
    %"v1438" : W = Or %"v1430", %"v1437";
    store Ww [%"chk285" + 0] <- %"v1438"
    => goto "L1361";
  @"L1361":
    %"v1442" : W = Copy %"v815";
    %"v1444" : W = And %"v1442", #524288;
    %"v1445" : W = (Cmp Ne W) %"v1444", #0
    => br %"v1445" ? "L1439" : "L1441";
  @"L1439":
    %"v1447" = %"v0" +p #20;
    %"v1448" = %"v1447" +p #192;
    %"v1449" = %"v1448" +p #16;
    %"v1450" = %"v1449" +p #12;
    %"chk288" : A = (Renew 0 4 Read 1) %"chk159", %"v1450";
    %"v1451" : W = (RawLoad (LdNarrow Uw) 0) %"chk288";
    %"v1455" = %"v1448" +p #12;
    %"chk289" : A = (Renew 0 4 Read 1) %"chk262", %"v1455";
    %"v1456" : W = (RawLoad (LdNarrow Uw) 0) %"chk289";
    %"v1458" : W = And %"v1456", #2097152;
    %"v1459" : W = Or %"v1451", %"v1458";
    %"chk290" : A = (Renew 0 4 Write 1) %"chk159", %"v1450";
    store Ww [%"chk290" + 0] <- %"v1459"
    => goto "L1441";
  @"L1441":
    %"v1461" = %"v0" +p #20;
    %"v1463" = %"v1461" +p #16;
    %"v1464" = %"v1463" +p #8;
    %"chk291" : A = (Renew 0 4 Read 1) %"chk0", %"v1464";
    %"v1465" : W = (RawLoad (LdNarrow Uw) 0) %"chk291";
    %"v1467" : W = Or %"v1465", #67108864;
    %"chk292" : A = (Renew 0 4 Write 1) %"chk0", %"v1464";
    store Ww [%"chk292" + 0] <- %"v1467";
    %"v1470" = %"v1461" +p #96;
    %"v1471" = %"v1470" +p #16;
    %"chk293" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1471";
    %"v1472" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1476" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1478" : W = And %"v1476", #1;
    %"v1479" : W = Or %"v1472", %"v1478";
    store Ww [%"chk293" + 0] <- %"v1479";
    %"v1484" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1488" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1490" : W = And %"v1488", #2;
    %"v1491" : W = Or %"v1484", %"v1490";
    store Ww [%"chk293" + 0] <- %"v1491";
    %"v1496" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1500" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1502" : W = And %"v1500", #4;
    %"v1503" : W = Or %"v1496", %"v1502";
    store Ww [%"chk293" + 0] <- %"v1503";
    %"v1508" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1512" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1514" : W = And %"v1512", #16;
    %"v1515" : W = Or %"v1508", %"v1514";
    store Ww [%"chk293" + 0] <- %"v1515";
    %"v1520" = %"v0" +p #4;
    %"chk305" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v1520";
    %"v1521" : W = (RawLoad (LdNarrow Sw) 0) %"chk305";
    %"v1522" : W = (Cmp Sge W) %"v1521", #13
    => br %"v1522" ? "L1516" : "L791";
  @"L1516":
    call void $"zcpuid_count"(W #13, W #0, P %"v1523", P %"v1524", P %"v1525", P %"v1526");
    %"chk306" : A = (Check 0 4 Read 1) %"v1524";
    %"v1530" : W = (RawLoad (LdNarrow Uw) 0) %"chk306";
    %"v1531" : W = (Cmp Ne W) %"v1530", #0
    => br %"v1531" ? "L1527" : "L791";
  @"L1527":
    %"v1533" : W = (RawLoad (LdNarrow Uw) 0) %"chk306";
    %"v1537" : W = Add %"v1533", #88;
    %"v1538" : W = Add %"v1537", #64;
    %"v1539" : W = Sub %"v1538", #1;
    %"v1541" : W = And %"v1539", #4294967232;
    %"v1543" = %"v0" +p #352;
    %"v1545" : L = (Ext Uw) %"v1541";
    %"chk308" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v1543";
    store Wl [%"chk308" + 0] <- %"v1545";
    %"v1547" = %"v0" +p #360;
    %"chk309" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v1547";
    store Ww [%"chk309" + 0] <- %"v1541";
    %"v1549" : P = Copy $"_dl_x86_features_tlsdesc_state_size";
    %"chk310" : A = (Check 0 8 Write 1) %"v1549";
    store Wl [%"chk310" + 0] <- %"v1545";
    %"v1556" = %"v0" +p #20;
    %"v1557" = %"v1556" +p #96;
    %"chk311" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1557";
    %"v1558" : W = (RawLoad (LdNarrow Uw) 0) %"chk311";
    %"v1560" : W = And %"v1558", #2;
    %"v1561" : W = (Cmp Ne W) %"v1560", #0
    => br %"v1561" ? "L1552" : "L791";
  @"L1552":
    %"chk312" : A = (Check 0 4 Write 1) %"v1562";
    store Ww [%"chk312" + 0] <- #0;
    %"v1566" = %"v1562" +p #4;
    %"chk313" : A = (HalfCheck Upper 0 4 Write 1) %"chk312", %"v1566";
    store Ww [%"chk313" + 0] <- #160;
    %"v1567" = %"v1562" +p #8;
    %"chk314" : A = (HalfCheck Upper 0 4 Write 1) %"chk312", %"v1567";
    store Ww [%"chk314" + 0] <- #576;
    %"chk315" : A = (Check 0 4 Write 1) %"v1563";
    store Ww [%"chk315" + 0] <- #160;
    %"v1569" = %"v1563" +p #4;
    %"chk316" : A = (HalfCheck Upper 0 4 Write 1) %"chk315", %"v1569";
    store Ww [%"chk316" + 0] <- #256
    => goto "L1570";
  @"L1570" [%"pr.4" : W = phi("L1552" => #2, "L1572" => %"v1653")]:
    %"v1575" : W = (Cmp Ule W) %"pr.4", #19
    => br %"v1575" ? "L1571" : "L1573";
  @"L1571":
    %"v1597" : W = Shl #1, %"pr.4";
    %"v1598" : W = And %"v1597", #917742;
    %"v1599" : W = (Cmp Ne W) %"v1598", #0
    => br %"v1599" ? "L1576" : "L1577";
  @"L1576":
    call void $"zcpuid_count"(W #13, W %"pr.4", P %"v1523", P %"v1524", P %"v1525", P %"v1526");
    %"v1602" : L = (Ext Uw) %"pr.4";
    %"v1603" : L = Shl %"v1602", #2;
    %"v1604" = %"v1563" +p %"v1603";
    %"chk317" : A = (Check 0 4 Read 1) %"v1523";
    %"v1605" : W = (RawLoad (LdNarrow Uw) 0) %"chk317";
    %"chk318" : A = (Check 0 4 Write 1) %"v1604";
    store Ww [%"chk318" + 0] <- %"v1605"
    => goto "L1578";
  @"L1577":
    %"chk319" : A = (Check 0 4 Write 1) %"v1525";
    store Ww [%"chk319" + 0] <- #0;
    %"v1607" : L = (Ext Uw) %"pr.4";
    %"v1608" : L = Shl %"v1607", #2;
    %"v1609" = %"v1563" +p %"v1608";
    %"chk320" : A = (Check 0 4 Write 1) %"v1609";
    store Ww [%"chk320" + 0] <- #0
    => goto "L1578";
  @"L1578":
    %"v1614" : W = (Cmp Ugt W) %"pr.4", #2
    => br %"v1614" ? "L1610" : "L1572";
  @"L1610":
    %"v1616" : L = (Ext Uw) %"pr.4";
    %"v1617" : L = Shl %"v1616", #2;
    %"v1618" = %"v1562" +p %"v1617";
    %"v1620" : W = Sub %"pr.4", #1;
    %"v1621" : L = (Ext Uw) %"v1620";
    %"v1622" : L = Shl %"v1621", #2;
    %"v1623" = %"v1562" +p %"v1622";
    %"chk321" : A = (Check 0 4 Read 1) %"v1623";
    %"v1624" : W = (RawLoad (LdNarrow Uw) 0) %"chk321";
    %"v1629" = %"v1563" +p %"v1622";
    %"chk322" : A = (Check 0 4 Read 1) %"v1629";
    %"v1630" : W = (RawLoad (LdNarrow Uw) 0) %"chk322";
    %"v1631" : W = Add %"v1624", %"v1630";
    %"chk323" : A = (Check 0 4 Write 1) %"v1618";
    store Ww [%"chk323" + 0] <- %"v1631";
    %"chk324" : A = (Check 0 4 Read 1) %"v1525";
    %"v1635" : W = (RawLoad (LdNarrow Uw) 0) %"chk324";
    %"v1637" : W = And %"v1635", #2;
    %"v1638" : W = (Cmp Ne W) %"v1637", #0
    => br %"v1638" ? "L1632" : "L1572";
  @"L1632":
    %"v1647" : W = (RawLoad (LdNarrow Uw) 0) %"chk323";
    %"v1648" : W = Add %"v1647", #64;
    %"v1649" : W = Sub %"v1648", #1;
    %"v1651" : W = And %"v1649", #4294967232;
    store Ww [%"chk323" + 0] <- %"v1651"
    => goto "L1572";
  @"L1572":
    %"v1653" : W = Add %"pr.4", #1
    => goto poll "L1570";
  @"L1573":
    %"v1655" = %"v1562" +p #76;
    %"chk327" : A = (HalfCheck Upper 0 4 Read 1) %"chk312", %"v1655";
    %"v1656" : W = (RawLoad (LdNarrow Uw) 0) %"chk327";
    %"v1657" = %"v1563" +p #76;
    %"chk328" : A = (HalfCheck Upper 0 4 Read 1) %"chk315", %"v1657";
    %"v1658" : W = (RawLoad (LdNarrow Uw) 0) %"chk328";
    %"v1659" : W = Add %"v1656", %"v1658"
    => br %"v1659" ? "L1660" : "L791";
  @"L1660":
    %"v1668" : W = Add %"v1659", #88;
    %"v1669" : W = Add %"v1668", #64;
    %"v1670" : W = Sub %"v1669", #1;
    %"v1672" : W = And %"v1670", #4294967232;
    %"v1673" : P = Copy $"_dl_x86_features_tlsdesc_state_size";
    %"v1675" : L = (Ext Uw) %"v1672";
    %"chk329" : A = (Check 0 8 Write 1) %"v1673";
    store Wl [%"chk329" + 0] <- %"v1675";
    %"v1680" = %"v1562" +p #76;
    %"chk330" : A = (Renew 0 4 Read 1) %"chk327", %"v1680";
    %"v1681" : W = (RawLoad (LdNarrow Uw) 0) %"chk330";
    %"v1682" = %"v1562" +p #68;
    %"chk331" : A = (HalfCheck Upper 0 4 Read 1) %"chk312", %"v1682";
    %"v1683" : W = (RawLoad (LdNarrow Uw) 0) %"chk331";
    %"v1684" : W = Sub %"v1681", %"v1683";
    %"v1685" : W = Sub %"v1672", %"v1684";
    %"v1687" = %"v0" +p #352;
    %"v1689" : L = (Ext Uw) %"v1685";
    %"chk332" : A = (Renew 0 8 Write 1) %"chk308", %"v1687";
    store Wl [%"chk332" + 0] <- %"v1689";
    %"v1691" = %"v0" +p #20;
    %"v1692" = %"v1691" +p #96;
    %"v1693" = %"v1692" +p #16;
    %"chk333" : A = (Renew 0 4 Read 1) %"chk293", %"v1693";
    %"v1694" : W = (RawLoad (LdNarrow Uw) 0) %"chk333";
    %"v1696" : W = Or %"v1694", #2;
    store Ww [%"chk333" + 0] <- %"v1696"
    => goto "L791";
  @"L791":
    %"v1701" = %"v0" +p #20;
    %"v1702" = %"v1701" +p #32;
    %"v1703" = %"v1702" +p #8;
    %"chk335" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1703";
    %"v1704" : W = (RawLoad (LdNarrow Uw) 0) %"chk335";
    %"v1706" : W = And %"v1704", #16;
    %"v1707" : W = (Cmp Ne W) %"v1706", #0
    => br %"v1707" ? "L1697" : "L1699";
  @"L1697":
    %"v1709" = %"v0" +p #20;
    %"v1710" = %"v1709" +p #32;
    %"v1711" = %"v1710" +p #16;
    %"v1712" = %"v1711" +p #8;
    %"chk336" : A = (Renew 0 4 Read 1) %"chk84", %"v1712";
    %"v1713" : W = (RawLoad (LdNarrow Uw) 0) %"chk336";
    %"v1715" : W = Or %"v1713", #8;
    %"chk337" : A = (Renew 0 4 Write 1) %"chk84", %"v1712";
    store Ww [%"chk337" + 0] <- %"v1715"
    => goto "L1699";
  @"L1699":
    %"v1720" = %"v0" +p #20;
    %"v1721" = %"v1720" +p #224;
    %"v1722" = %"v1721" +p #4;
    %"chk338" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1722";
    %"v1723" : W = (RawLoad (LdNarrow Uw) 0) %"chk338";
    %"v1725" : W = And %"v1723", #1
    => br %"v1725" ? "L1716" : "iw_1.start";
  @"L1716":
    %"v1728" = %"v0" +p #20;
    %"v1729" = %"v1728" +p #224;
    %"v1730" = %"v1729" +p #16;
    %"v1731" = %"v1730" +p #4;
    %"chk339" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1731";
    %"v1732" : W = (RawLoad (LdNarrow Uw) 0) %"chk339";
    %"v1734" : W = Or %"v1732", #1;
    %"chk340" : A = (Renew 0 4 Write 1) %"chk339", %"v1731";
    store Ww [%"chk340" + 0] <- %"v1734";
    %"v1737" = %"v1728" +p #32;
    %"v1738" = %"v1737" +p #16;
    %"v1739" = %"v1738" +p #8;
    %"v1740" : W = (RawLoad (LdNarrow Uw) 16) %"chk335";
    %"v1744" = %"v1737" +p #8;
    %"v1745" : W = (RawLoad (LdNarrow Uw) 0) %"chk335";
    %"v1747" : W = And %"v1745", #8388608;
    %"v1748" : W = Or %"v1740", %"v1747";
    store Ww [%"chk335" + 16] <- %"v1748";
    %"v1754" : W = (RawLoad (LdNarrow Uw) 0) %"chk340";
    %"v1758" = %"v1729" +p #4;
    %"v1759" : W = (RawLoad (LdNarrow Uw) 0) %"chk338";
    %"v1761" : W = And %"v1759", #4;
    %"v1762" : W = Or %"v1754", %"v1761";
    store Ww [%"chk340" + 0] <- %"v1762"
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v5" : P = Copy $"_dl_hwcap2";
    %"chk347" : A = (Check 0 8 Read 1) %"iw_1.v5";
    %"iw_1.v6" : L = (RawLoad LdL 0) %"chk347";
    %"iw_1.v9" : L = And %"iw_1.v6", #2;
    %"iw_1.v10" : W = (Cmp Ne L) %"iw_1.v9", #0
    => br %"iw_1.v10" ? "iw_1.L2" : "iw_1.join";
  @"iw_1.L2":
    %"iw_1.v12" = %"v0" +p #20;
    %"iw_1.v13" = %"iw_1.v12" +p #32;
    %"iw_1.v14" = %"iw_1.v13" +p #16;
    %"iw_1.v15" = %"iw_1.v14" +p #4;
    %"chk348" : A = (Renew 0 4 Read 1) %"chk57", %"iw_1.v15";
    %"iw_1.v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk348";
    %"iw_1.v20" = %"iw_1.v13" +p #4;
    %"chk349" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_1.v20";
    %"iw_1.v21" : W = (RawLoad (LdNarrow Uw) 0) %"chk349";
    %"iw_1.v23" : W = And %"iw_1.v21", #1;
    %"iw_1.v24" : W = Or %"iw_1.v16", %"iw_1.v23";
    %"chk350" : A = (Renew 0 4 Write 1) %"chk57", %"iw_1.v15";
    store Ww [%"chk350" + 0] <- %"iw_1.v24"
    => goto "iw_1.join";
  @"iw_1.join":
    %"v1765" = %"v0" +p #344;
    call %"v1767" : W = $"glibc_libc_start#get_isa_level"(P %"v0");
    %"chk351" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v1765";
    store Ww [%"chk351" + 0] <- %"v1767"
    => ret void
} }.

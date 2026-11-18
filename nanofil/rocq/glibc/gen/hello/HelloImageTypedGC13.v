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

Definition hello_image_fn___GI___gconv_transliterate : func :=
  ir_fn{ "export" "__GI___gconv_transliterate"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", P %"v12") -> (RClass W) {
  @"start":
    %"v211" : P = (Alloc 8) #8;
    %"v212" : P = (Alloc 8) #8;
    %"v481" : P = (Alloc 8) #8;
    %"v494" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v28" = %"v0" +p #40;
    %"chk1" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v0";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v35" : L = Ptoi %"v34";
    %"v36" : L = Ptoi #0;
    %"v37" : W = (Cmp Ne L) %"v35", %"v36"
    => br %"v37" ? "L32" : "L31";
  @"L31":
    => goto "L32";
  @"L32":
    %"v39" : P = Copy $"__libc_tsd_LOCALE";
    %"chk3" : A = (Check 0 8 Read 8) %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Check 0 8 Read 8) %"v40";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v43" = %"v42" +p #56;
    %"v47" = %"v43" +p #488;
    %"chk5" : A = (Check 0 4 Read 1) %"v47";
    %"v48" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v53" : W = (Cmp Eq W) %"v48", #0
    => br %"v53" ? "L54" : "L51";
  @"L51":
    %"v56" : P = Copy $"__libc_tsd_LOCALE";
    %"chk6" : A = (Check 0 8 Read 8) %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Read 8) %"v57";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v60" = %"v59" +p #56;
    %"v64" = %"v60" +p #496;
    %"chk8" : A = (Check 0 8 Read 8) %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v66" : P = Copy $"__libc_tsd_LOCALE";
    %"chk9" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 8 Read 8) %"v67";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v70" = %"v69" +p #56;
    %"v74" = %"v70" +p #504;
    %"chk11" : A = (Check 0 8 Read 8) %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v76" : P = Copy $"__libc_tsd_LOCALE";
    %"chk12" : A = (Check 0 8 Read 8) %"v76";
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Check 0 8 Read 8) %"v77";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v80" = %"v79" +p #56;
    %"v84" = %"v80" +p #512;
    %"chk14" : A = (Check 0 8 Read 8) %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v86" : P = Copy $"__libc_tsd_LOCALE";
    %"chk15" : A = (Check 0 8 Read 8) %"v86";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Check 0 8 Read 8) %"v87";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v90" = %"v89" +p #56;
    %"v94" = %"v90" +p #520;
    %"chk17" : A = (Check 0 8 Read 8) %"v94";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v100" = %"v24" +p #4;
    %"v102" : L = Ptoi %"v100";
    %"v103" : L = Ptoi %"v8";
    %"v104" : W = (Cmp Ugt L) %"v102", %"v103"
    => br %"v104" ? "L96" : "L116";
  @"L96":
    %"v110" : L = Ptoi %"v24";
    %"v112" : W = (Cmp Eq L) %"v110", %"v103"
    => br %"v112" ? "L107" : "L106";
  @"L106":
    => goto "L107";
  @"L107" [%"v113" : W = phi("L106" => #7, "L96" => #4)]:
    => ret %"v113";
  @"L116" [%"pr.3" : W = phi("L51" => %"v48", "L304" => %"pr.3", "L317" => %"v126"); %"pr.1" : W = phi("L51" => #0, "L304" => %"v336", "L317" => %"pr.1")]:
    %"v121" : W = (Cmp Ult W) %"pr.1", %"pr.3"
    => br %"v121" ? "L117" : "L54";
  @"L117":
    %"v125" : W = Add %"pr.1", %"pr.3";
    %"v126" : W = Shr %"v125", #1;
    %"v131" : L = (Ext Uw) %"v126";
    %"v132" : L = Shl %"v131", #2;
    %"v133" = %"v65" +p %"v132";
    %"chk18" : A = (Check 0 4 Read 1) %"v133";
    %"v134" : W = (RawLoad (LdNarrow Uw) 0) %"chk18"
    => goto "L135";
  @"L135" [%"pr.5" : W = phi("L117" => #0, "L169" => %"v158")]:
    %"v144" : W = Add %"v134", %"pr.5";
    %"v145" : L = (Ext Uw) %"v144";
    %"v146" : L = Shl %"v145", #2;
    %"v147" = %"v75" +p %"v146";
    %"chk19" : A = (Check 0 4 Read 1) %"v147";
    %"v148" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v151" : L = (Ext Sw) %"pr.5";
    %"v152" : L = Shl %"v151", #2;
    %"v153" = %"v24" +p %"v152";
    %"chk20" : A = (Check 0 4 Read 1) %"v153";
    %"v154" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v155" : W = (Cmp Ne W) %"v148", %"v154"
    => br %"v155" ? "L137" : "L140";
  @"L140":
    %"v158" : W = Add %"pr.5", #1;
    %"v162" : W = Add %"v134", %"v158";
    %"v163" : L = (Ext Uw) %"v162";
    %"v164" : L = Shl %"v163", #2;
    %"v165" = %"v75" +p %"v164";
    %"chk21" : A = (Check 0 4 Read 1) %"v165";
    %"v166" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v167" : W = (Cmp Ne W) %"v166", #0
    => br %"v167" ? "L168" : "L169";
  @"L168":
    %"v172" : L = (Ext Sw) %"v158";
    %"v173" : L = Shl %"v172", #2;
    %"v174" = %"v24" +p %"v173";
    %"v176" : L = Ptoi %"v174";
    %"v178" : W = (Cmp Ult L) %"v176", %"v103"
    => goto "L169";
  @"L169" [%"v180" : W = phi("L140" => #0, "L168" => %"v178")]:
    => br %"v180" ? poll "L135" : "L137";
  @"L137" [%"pr.6" : W = phi("L169" => %"v158", "L135" => %"pr.5")]:
    %"v185" : W = (Cmp Sgt W) %"pr.6", #0
    => br %"v185" ? "L186" : "L187";
  @"L186":
    %"v191" : W = Add %"v134", %"pr.6";
    %"v192" : L = (Ext Uw) %"v191";
    %"v193" : L = Shl %"v192", #2;
    %"v194" = %"v75" +p %"v193";
    %"chk22" : A = (Check 0 4 Read 1) %"v194";
    %"v195" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v196" : W = (Cmp Eq W) %"v195", #0
    => goto "L187";
  @"L187" [%"v198" : W = phi("L137" => #0, "L186" => %"v196")]:
    => br %"v198" ? "L181" : "L182";
  @"L181":
    %"v204" = %"v85" +p %"v132";
    %"chk23" : A = (Check 0 4 Read 1) %"v204";
    %"v205" : W = (RawLoad (LdNarrow Uw) 0) %"chk23"
    => goto "L206";
  @"L206" [%"pr.7" : W = phi("L181" => %"v205", "L248" => %"v277")]:
    => goto "L213";
  @"L213" [%"pr.8" : W = phi("L206" => #0, "L214" => %"v226")]:
    %"v219" : W = Add %"pr.7", %"pr.8";
    %"v220" : L = (Ext Uw) %"v219";
    %"v221" : L = Shl %"v220", #2;
    %"v222" = %"v95" +p %"v221";
    %"chk24" : A = (Check 0 4 Read 1) %"v222";
    %"v223" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"v224" : W = (Cmp Ne W) %"v223", #0
    => br %"v224" ? "L214" : "L215";
  @"L214":
    %"v226" : W = Add %"pr.8", #1
    => goto poll "L213";
  @"L215":
    %"v229" : L = (Ext Uw) %"pr.7";
    %"v230" : L = Shl %"v229", #2;
    %"v231" = %"v95" +p %"v230";
    %"chk25" : A = (Check 0 8 Write 8) %"v211";
    store.ptr [%"chk25" + 0] <- %"v231";
    %"chk26" : A = (Check 0 8 Read 8) %"v10";
    %"v233" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (Check 0 8 Write 8) %"v212";
    store.ptr [%"chk27" + 0] <- %"v233";
    %"chk28" : F = CheckFunction %"v29";
    rawcall %"v245" : W = %"chk28"(P %"v0", P %"v2", P %"v211", P %"v222", P %"v212", P #0, W #0, W #0);
    %"v250" : W = (Cmp Ne W) %"v245", #6
    => br %"v250" ? "L246" : "L248";
  @"L246":
    %"v255" : W = (Cmp Eq W) %"v245", #4
    => br %"v255" ? "L251" : "L253";
  @"L251":
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v6";
    %"v257" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v259" : L = (Ext Sw) %"pr.6";
    %"v260" : L = Shl %"v259", #2;
    %"v261" = %"v257" +p %"v260";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk0", %"v6";
    store.ptr [%"chk30" + 0] <- %"v261";
    %"chk31" : A = (Check 0 8 Read 1) %"v12";
    %"v263" : L = (RawLoad LdL 0) %"chk31";
    %"v264" : L = Add %"v263", #1;
    %"chk32" : A = (Renew 0 8 Write 1) %"chk31", %"v12";
    store Wl [%"chk32" + 0] <- %"v264"
    => goto "L253";
  @"L253" [%"pr.9" : W = phi("L251" => #0, "L246" => %"v245")]:
    %"v269" : W = (Cmp Ne W) %"pr.9", #5
    => br %"v269" ? "L265" : "L267";
  @"L265":
    %"chk33" : A = (Renew 0 8 Read 8) %"chk27", %"v212";
    %"v271" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (Renew 0 8 Write 8) %"chk26", %"v10";
    store.ptr [%"chk34" + 0] <- %"v271"
    => goto "L267";
  @"L267":
    => ret %"pr.9";
  @"L248":
    %"v276" : W = Add %"pr.8", #1;
    %"v277" : W = Add %"pr.7", %"v276";
    %"v280" : L = (Ext Uw) %"v277";
    %"v281" : L = Shl %"v280", #2;
    %"v282" = %"v95" +p %"v281";
    %"chk35" : A = (Check 0 4 Read 1) %"v282";
    %"v283" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v284" : W = (Cmp Ne W) %"v283", #0
    => br %"v284" ? poll "L206" : "L183";
  @"L182":
    => br %"v185" ? "L290" : "L291";
  @"L290":
    %"v294" : L = (Ext Sw) %"pr.6";
    %"v295" : L = Shl %"v294", #2;
    %"v296" = %"v24" +p %"v295";
    %"v298" : L = Ptoi %"v296";
    %"v300" : W = (Cmp Eq L) %"v298", %"v103"
    => goto "L291";
  @"L291" [%"v302" : W = phi("L182" => #0, "L290" => %"v300")]:
    => br %"v302" ? "L285" : "L183";
  @"L285":
    => ret #7;
  @"L183":
    %"v309" : L = (Ext Sw) %"pr.6";
    %"v310" : L = Shl %"v309", #2;
    %"v311" = %"v24" +p %"v310";
    %"v313" : L = Ptoi %"v311";
    %"v315" : W = (Cmp Uge L) %"v313", %"v103"
    => br %"v315" ? "L317" : "L316";
  @"L316":
    %"v321" : W = Add %"v134", %"pr.6";
    %"v322" : L = (Ext Uw) %"v321";
    %"v323" : L = Shl %"v322", #2;
    %"v324" = %"v75" +p %"v323";
    %"chk36" : A = (Check 0 4 Read 1) %"v324";
    %"v325" : W = (RawLoad (LdNarrow Uw) 0) %"chk36";
    %"chk37" : A = (Check 0 4 Read 1) %"v311";
    %"v331" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v332" : W = (Cmp Ult W) %"v325", %"v331"
    => goto "L317";
  @"L317" [%"v334" : W = phi("L183" => #1, "L316" => %"v332")]:
    => br %"v334" ? "L304" : poll "L116";
  @"L304":
    %"v336" : W = Add %"v126", #1
    => goto poll "L116";
  @"L54":
    %"v341" : P = Copy $"__libc_tsd_LOCALE";
    %"chk38" : A = (Check 0 8 Read 8) %"v341";
    %"v342" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 8 Read 8) %"v342";
    %"v344" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v345" = %"v344" +p #56;
    %"v349" = %"v345" +p #544;
    %"chk40" : A = (Check 0 4 Read 1) %"v349";
    %"v350" : W = (RawLoad (LdNarrow Uw) 0) %"chk40";
    %"v351" : W = (Cmp Ne W) %"v350", #0
    => br %"v351" ? "L338" : "L340";
  @"L338":
    %"v353" : P = Copy $"__libc_tsd_LOCALE";
    %"chk41" : A = (Check 0 8 Read 8) %"v353";
    %"v354" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"chk42" : A = (Check 0 8 Read 8) %"v354";
    %"v356" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v357" = %"v356" +p #56;
    %"v361" = %"v357" +p #544;
    %"chk43" : A = (Check 0 4 Read 1) %"v361";
    %"v362" : W = (RawLoad (LdNarrow Uw) 0) %"chk43";
    %"v364" : P = Copy $"__libc_tsd_LOCALE";
    %"chk44" : A = (Check 0 8 Read 8) %"v364";
    %"v365" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 8 Read 8) %"v365";
    %"v367" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v368" = %"v367" +p #56;
    %"v372" = %"v368" +p #552;
    %"chk46" : A = (Check 0 8 Read 8) %"v372";
    %"v373" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"chk47" : A = (Renew 0 8 Read 8) %"chk0", %"v6";
    %"v376" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"chk48" : A = (Check 0 4 Read 1) %"v376";
    %"v377" : W = (RawLoad (LdNarrow Uw) 0) %"chk48";
    %"v383" = %"v24" +p #4;
    %"v385" : L = Ptoi %"v383";
    %"v386" : L = Ptoi %"v8";
    %"v387" : W = (Cmp Ugt L) %"v385", %"v386"
    => br %"v387" ? "L379" : "L398";
  @"L379":
    %"v393" : L = Ptoi %"v24";
    %"v395" : W = (Cmp Eq L) %"v393", %"v386"
    => br %"v395" ? "L390" : "L389";
  @"L389":
    => goto "L390";
  @"L390" [%"v396" : W = phi("L389" => #7, "L379" => #4)]:
    => ret %"v396";
  @"L398" [%"pr.11" : W = phi("L400" => %"v455", "L338" => #0); %"pr.10" : P = phi("L400" => %"v453", "L338" => %"v373")]:
    %"v404" : W = (Cmp Slt W) %"pr.11", %"v362"
    => br %"v404" ? "L399" : "L340";
  @"L399":
    %"chk49" : A = (Check 0 4 Read 1) %"pr.10";
    %"v410" : W = (RawLoad (LdNarrow Uw) 0) %"chk49";
    %"v412" : W = (Cmp Ule W) %"v410", %"v377"
    => br %"v412" ? "L413" : "L414";
  @"L413":
    %"v417" = %"pr.10" +p #4;
    %"chk50" : A = (HalfCheck Upper 0 4 Read 1) %"chk49", %"v417";
    %"v418" : W = (RawLoad (LdNarrow Uw) 0) %"chk50";
    %"v419" : W = (Cmp Ule W) %"v377", %"v418"
    => goto "L414";
  @"L414" [%"v421" : W = phi("L399" => #0, "L413" => %"v419")]:
    => br %"v421" ? "L422" : "L423";
  @"L422":
    %"v427" : W = (RawLoad (LdNarrow Uw) 0) %"chk49";
    %"v428" : W = Sub %"v377", %"v427";
    %"v430" = %"pr.10" +p #8;
    %"chk52" : A = (HalfCheck Upper 0 4 Read 1) %"chk49", %"v430";
    %"v431" : W = (RawLoad (LdNarrow Uw) 0) %"chk52";
    %"v432" : W = Urem %"v428", %"v431";
    %"v433" : W = (Cmp Eq W) %"v432", #0
    => goto "L423";
  @"L423" [%"v435" : W = phi("L414" => #0, "L422" => %"v433")]:
    => br %"v435" ? "L405" : "L406";
  @"L405":
    %"chk53" : A = (Renew 0 8 Read 8) %"chk0", %"v6";
    %"v437" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v438" = %"v437" +p #4;
    %"chk54" : A = (Renew 0 8 Write 8) %"chk0", %"v6";
    store.ptr [%"chk54" + 0] <- %"v438";
    %"chk55" : A = (Check 0 8 Read 1) %"v12";
    %"v440" : L = (RawLoad LdL 0) %"chk55";
    %"v441" : L = Add %"v440", #1;
    %"chk56" : A = (Renew 0 8 Write 1) %"chk55", %"v12";
    store Wl [%"chk56" + 0] <- %"v441"
    => ret #0;
  @"L406":
    %"v449" : W = (RawLoad (LdNarrow Uw) 0) %"chk49";
    %"v450" : W = (Cmp Ult W) %"v377", %"v449"
    => br %"v450" ? "L340" : "L400";
  @"L400":
    %"v453" = %"pr.10" +p #12;
    %"v455" : W = Add %"pr.11", #1
    => goto poll "L398";
  @"L340":
    %"v459" : P = Copy $"__libc_tsd_LOCALE";
    %"chk58" : A = (Check 0 8 Read 8) %"v459";
    %"v460" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"chk59" : A = (Check 0 8 Read 8) %"v460";
    %"v462" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"v463" = %"v462" +p #56;
    %"v467" = %"v463" +p #528;
    %"chk60" : A = (Check 0 4 Read 1) %"v467";
    %"v468" : W = (RawLoad (LdNarrow Uw) 0) %"chk60";
    %"v469" : W = (Cmp Ne W) %"v468", #0
    => br %"v469" ? "L456" : "iw_3.start";
  @"L456":
    %"v471" : P = Copy $"__libc_tsd_LOCALE";
    %"chk61" : A = (Check 0 8 Read 8) %"v471";
    %"v472" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"chk62" : A = (Check 0 8 Read 8) %"v472";
    %"v474" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v475" = %"v474" +p #56;
    %"v479" = %"v475" +p #536;
    %"chk63" : A = (Check 0 8 Read 8) %"v479";
    %"v480" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"chk64" : A = (Check 0 8 Write 8) %"v481";
    store.ptr [%"chk64" + 0] <- %"v480";
    %"v484" : P = Copy $"__libc_tsd_LOCALE";
    %"chk65" : A = (Check 0 8 Read 8) %"v484";
    %"v485" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Check 0 8 Read 8) %"v485";
    %"v487" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"v488" = %"v487" +p #56;
    %"v492" = %"v488" +p #528;
    %"chk67" : A = (Check 0 4 Read 1) %"v492";
    %"v493" : W = (RawLoad (LdNarrow Uw) 0) %"chk67";
    %"v500" = %"v24" +p #4;
    %"v502" : L = Ptoi %"v500";
    %"v503" : L = Ptoi %"v8";
    %"v504" : W = (Cmp Ugt L) %"v502", %"v503"
    => br %"v504" ? "L496" : "L498";
  @"L496":
    %"v510" : L = Ptoi %"v24";
    %"v512" : W = (Cmp Eq L) %"v510", %"v503"
    => br %"v512" ? "L507" : "L506";
  @"L506":
    => goto "L507";
  @"L507" [%"v513" : W = phi("L506" => #7, "L496" => #4)]:
    => ret %"v513";
  @"L498":
    %"chk68" : A = (Check 0 8 Read 8) %"v10";
    %"v516" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"chk69" : A = (Check 0 8 Write 8) %"v494";
    store.ptr [%"chk69" + 0] <- %"v516";
    %"v523" : L = (Ext Uw) %"v493";
    %"v524" : L = Shl %"v523", #2;
    %"v525" = %"v480" +p %"v524";
    %"chk70" : F = CheckFunction %"v29";
    rawcall %"v526" : W = %"chk70"(P %"v0", P %"v2", P %"v481", P %"v525", P %"v494", P #0, W #0, W #0);
    %"v531" : W = (Cmp Ne W) %"v526", #6
    => br %"v531" ? "L527" : "iw_3.start";
  @"L527":
    %"v536" : W = (Cmp Eq W) %"v526", #4
    => br %"v536" ? "L532" : "L534";
  @"L532":
    %"chk71" : A = (Check 0 8 Read 1) %"v12";
    %"v538" : L = (RawLoad LdL 0) %"chk71";
    %"v539" : L = Add %"v538", #1;
    %"chk72" : A = (Renew 0 8 Write 1) %"chk71", %"v12";
    store Wl [%"chk72" + 0] <- %"v539";
    %"chk73" : A = (Renew 0 8 Read 8) %"chk0", %"v6";
    %"v541" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"v542" = %"v541" +p #4;
    %"chk74" : A = (Renew 0 8 Write 8) %"chk0", %"v6";
    store.ptr [%"chk74" + 0] <- %"v542"
    => goto "L534";
  @"L534" [%"pr.12" : W = phi("L532" => #0, "L527" => %"v526")]:
    %"chk75" : A = (Renew 0 8 Read 8) %"chk69", %"v494";
    %"v544" : P = (RawLoadPointer 0 load_effects) %"chk75";
    %"chk76" : A = (Renew 0 8 Write 8) %"chk68", %"v10";
    store.ptr [%"chk76" + 0] <- %"v544"
    => ret %"pr.12";
  @"iw_3.start":
    %"iw_3.v3" = %"v2" +p #16;
    %"chk77" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk77";
    %"iw_3.v5" : W = Or %"iw_3.v4", #1073741824;
    %"chk78" : A = (Renew 0 4 Write 1) %"chk77", %"iw_3.v3";
    store Ww [%"chk78" + 0] <- %"iw_3.v5"
    => ret #6
} }.

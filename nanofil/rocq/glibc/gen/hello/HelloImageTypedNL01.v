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

Definition hello_image_fn__nl_find_msg : func :=
  ir_fn{ "export" "_nl_find_msg"(P %"v0", P %"v2", P %"v4", W %"v6", P %"v8") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v528" : P = (Alloc 8) #8;
    %"v585" : P = (Alloc 8) #24;
    %"v770" : P = (Alloc 8) #8;
    %"v771" : P = (Alloc 8) #8;
    %"v814" : P = (Alloc 8) #8;
    %"v19" = %"v0" +p #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v19";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v21" : W = (Cmp Sle W) %"v20", #0
    => br %"v21" ? "L15" : "L17" };
  ir_blk{ @"L15":
    call void $"_nl_load_domain"(P %"v0", P %"v2")
    => goto "L17" };
  ir_blk{ @"L17":
    %"v28" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v30" : L = Ptoi %"v29";
    %"v31" : L = Ptoi #0;
    %"v32" : W = (Cmp Eq L) %"v30", %"v31"
    => br %"v32" ? "L24" : "L26" };
  ir_blk{ @"L24":
    => ret #0 };
  ir_blk{ @"L26":
    %"v35" = %"v0" +p #16;
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v38" = %"v36" +p #40;
    %"chk3" : A = (Check 0 4 Read 1) %"v38";
    %"v39" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v44" = %"v36" +p #96;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v46" : L = Ptoi %"v45";
    %"v48" : W = (Cmp Ne L) %"v46", %"v31"
    => br %"v48" ? "L40" : "L41" };
  ir_blk{ @"L40":
    call %"v51" : L = $"__GI_strlen"(P %"v4");
    call %"v54" : L = $"__hash_string"(P %"v4");
    %"v56" : W = Copy %"v54";
    %"v58" = %"v36" +p #88;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v58";
    %"v59" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v60" : W = Urem %"v56", %"v59";
    %"v62" : W = Copy %"v54";
    %"v65" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v66" : W = Sub %"v65", #2;
    %"v67" : W = Urem %"v62", %"v66";
    %"v68" : W = Add %"v67", #1
    => goto "L69" };
  ir_blk{ @"L69" [%"pr.9" : W = phi("L40" => %"v60", "L213" => %"v229", "L214" => %"v232")]:
    %"v77" = %"v36" +p #104;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v77";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk7"
    => br %"v78" ? "L73" : "L74" };
  ir_blk{ @"L73":
    %"v80" = %"v36" +p #96;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk4", %"v80";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v83" : L = (Ext Uw) %"pr.9";
    %"v84" : L = Shl %"v83", #2;
    %"v85" = %"v81" +p %"v84";
    %"chk9" : A = (Check 0 4 Read 1) %"v85";
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    call %"v87" : W = $"glibc_dcigettext#__bswap_32"(W %"v86")
    => goto "L75" };
  ir_blk{ @"L74":
    %"v89" = %"v36" +p #96;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk4", %"v89";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v92" : L = (Ext Uw) %"pr.9";
    %"v93" : L = Shl %"v92", #2;
    %"v94" = %"v90" +p %"v93";
    %"chk11" : A = (Check 0 4 Read 1) %"v94";
    %"v95" : W = (RawLoad (LdNarrow Uw) 0) %"chk11"
    => goto "L75" };
  ir_blk{ @"L75" [%"v96" : W = phi("L73" => %"v87", "L74" => %"v95")]:
    %"v101" : W = (Cmp Eq W) %"v96", #0
    => br %"v101" ? "L97" : "L99" };
  ir_blk{ @"L97":
    => ret #0 };
  ir_blk{ @"L99":
    %"v104" : W = Sub %"v96", #1;
    %"v113" : W = (Cmp Ult W) %"v104", %"v39"
    => br %"v113" ? "L108" : "L109" };
  ir_blk{ @"L108":
    %"v118" = %"v36" +p #24;
    %"chk12" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v118";
    %"v119" : W = (RawLoad (LdNarrow Sw) 0) %"chk12"
    => br %"v119" ? "L114" : "L115" };
  ir_blk{ @"L114":
    %"v121" = %"v36" +p #48;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v124" : L = (Ext Uw) %"v104";
    %"v125" : L = Shl %"v124", #3;
    %"v126" = %"v122" +p %"v125";
    %"chk14" : A = (Check 0 4 Read 1) %"v126";
    %"v127" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    call %"v128" : W = $"glibc_dcigettext#__bswap_32"(W %"v127")
    => goto "L116" };
  ir_blk{ @"L115":
    %"v130" = %"v36" +p #48;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v130";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v133" : L = (Ext Uw) %"v104";
    %"v134" : L = Shl %"v133", #3;
    %"v135" = %"v131" +p %"v134";
    %"chk16" : A = (Check 0 4 Read 1) %"v135";
    %"v136" : W = (RawLoad (LdNarrow Uw) 0) %"chk16"
    => goto "L116" };
  ir_blk{ @"L116" [%"v137" : W = phi("L114" => %"v128", "L115" => %"v136")]:
    %"v138" : W = Copy %"v51";
    %"v139" : W = (Cmp Uge W) %"v137", %"v138"
    => br %"v139" ? "L140" : "L110" };
  ir_blk{ @"L140":
    %"chk17" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"v36";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v149" = %"v36" +p #24;
    %"chk18" : A = (Renew 0 4 Read 1) %"chk12", %"v149";
    %"v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk18"
    => br %"v150" ? "L145" : "L146" };
  ir_blk{ @"L145":
    %"v152" = %"v36" +p #48;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v152";
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v155" : L = (Ext Uw) %"v104";
    %"v156" : L = Shl %"v155", #3;
    %"v157" = %"v153" +p %"v156";
    %"v158" = %"v157" +p #4;
    %"chk20" : A = (Check 0 4 Read 1) %"v158";
    %"v159" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    call %"v160" : W = $"glibc_dcigettext#__bswap_32"(W %"v159")
    => goto "L147" };
  ir_blk{ @"L146":
    %"v162" = %"v36" +p #48;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v162";
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v165" : L = (Ext Uw) %"v104";
    %"v166" : L = Shl %"v165", #3;
    %"v167" = %"v163" +p %"v166";
    %"v168" = %"v167" +p #4;
    %"chk22" : A = (Check 0 4 Read 1) %"v168";
    %"v169" : W = (RawLoad (LdNarrow Uw) 0) %"chk22"
    => goto "L147" };
  ir_blk{ @"L147" [%"v170" : W = phi("L145" => %"v160", "L146" => %"v169")]:
    %"v171" : L = (Ext Uw) %"v170";
    %"v172" = %"v144" +p %"v171";
    call %"v173" : W = $"__GI_strcmp"(P %"v4", P %"v172");
    %"v174" : W = (Cmp Eq W) %"v173", #0
    => goto "L110" };
  ir_blk{ @"L109":
    %"v178" = %"v36" +p #72;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v178";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v182" : W = Sub %"v104", %"v39";
    %"v183" : L = (Ext Uw) %"v182";
    %"v184" : L = Shl %"v183", #4;
    %"v185" = %"v179" +p %"v184";
    %"chk24" : A = (Check 0 8 Read 1) %"v185";
    %"v186" : L = (RawLoad LdL 0) %"chk24";
    %"v187" : W = Copy %"v51";
    %"v188" : L = (Ext Uw) %"v187";
    %"v189" : W = (Cmp Ugt L) %"v186", %"v188"
    => br %"v189" ? "L190" : "L110" };
  ir_blk{ @"L190":
    %"v194" = %"v36" +p #72;
    %"v195" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v201" = %"v195" +p %"v184";
    %"v202" = %"v201" +p #8;
    %"chk26" : A = (Check 0 8 Read 8) %"v202";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call %"v204" : W = $"__GI_strcmp"(P %"v4", P %"v203");
    %"v205" : W = (Cmp Eq W) %"v204", #0
    => goto "L110" };
  ir_blk{ @"L110" [%"v208" : W = phi("L116" => #0, "L147" => %"v174", "L109" => #0, "L190" => %"v205")]:
    => br %"v208" ? "L105" : "L107" };
  ir_blk{ @"L105":
    %"v210" : L = (Ext Uw) %"v104"
    => goto "L211" };
  ir_blk{ @"L107":
    %"v218" = %"v36" +p #88;
    %"chk27" : A = (Renew 0 4 Read 1) %"chk5", %"v218";
    %"v219" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v221" : W = Sub %"v219", %"v68";
    %"v222" : W = (Cmp Uge W) %"pr.9", %"v221"
    => br %"v222" ? "L213" : "L214" };
  ir_blk{ @"L213":
    %"v225" = %"v36" +p #88;
    %"v226" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v228" : W = Sub %"v226", %"v68";
    %"v229" : W = Sub %"pr.9", %"v228"
    => goto poll "L69" };
  ir_blk{ @"L214":
    %"v232" : W = Add %"pr.9", %"v68"
    => goto poll "L69" };
  ir_blk{ @"L41":
    %"v236" : L = (Ext Uw) %"v39"
    => goto "L237" };
  ir_blk{ @"L237" [%"pr.12" : L = phi("L41" => #0, "L253" => %"pr.12", "L284" => %"v290"); %"pr.10" : L = phi("L41" => %"v236", "L253" => %"v247", "L284" => %"pr.10")]:
    %"v242" : W = (Cmp Ult L) %"pr.12", %"pr.10"
    => br %"v242" ? "L238" : "L239" };
  ir_blk{ @"L238":
    %"v246" : L = Add %"pr.12", %"pr.10";
    %"v247" : L = Shr %"v246", #1;
    %"chk29" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"v36";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v255" = %"v36" +p #24;
    %"chk30" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v255";
    %"v256" : W = (RawLoad (LdNarrow Sw) 0) %"chk30"
    => br %"v256" ? "L251" : "L252" };
  ir_blk{ @"L251":
    %"v258" = %"v36" +p #48;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v258";
    %"v259" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v261" : L = Shl %"v247", #3;
    %"v262" = %"v259" +p %"v261";
    %"v263" = %"v262" +p #4;
    %"chk32" : A = (Check 0 4 Read 1) %"v263";
    %"v264" : W = (RawLoad (LdNarrow Uw) 0) %"chk32";
    call %"v265" : W = $"glibc_dcigettext#__bswap_32"(W %"v264")
    => goto "L253" };
  ir_blk{ @"L252":
    %"v267" = %"v36" +p #48;
    %"chk33" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v267";
    %"v268" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v270" : L = Shl %"v247", #3;
    %"v271" = %"v268" +p %"v270";
    %"v272" = %"v271" +p #4;
    %"chk34" : A = (Check 0 4 Read 1) %"v272";
    %"v273" : W = (RawLoad (LdNarrow Uw) 0) %"chk34"
    => goto "L253" };
  ir_blk{ @"L253" [%"v274" : W = phi("L251" => %"v265", "L252" => %"v273")]:
    %"v275" : L = (Ext Uw) %"v274";
    %"v276" = %"v250" +p %"v275";
    call %"v277" : W = $"__GI_strcmp"(P %"v4", P %"v276");
    %"v282" : W = (Cmp Slt W) %"v277", #0
    => br %"v282" ? poll "L237" : "L279" };
  ir_blk{ @"L279":
    %"v288" : W = (Cmp Sgt W) %"v277", #0
    => br %"v288" ? "L284" : "L211" };
  ir_blk{ @"L284":
    %"v290" : L = Add %"v247", #1
    => goto poll "L237" };
  ir_blk{ @"L239":
    => ret #0 };
  ir_blk{ @"L211" [%"pr.1" : L = phi("L105" => %"v210", "L279" => %"v247")]:
    %"v296" : L = (Ext Uw) %"v39";
    %"v297" : W = (Cmp Ult L) %"pr.1", %"v296"
    => br %"v297" ? "L291" : "L292" };
  ir_blk{ @"L291":
    %"chk35" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"v36";
    %"v299" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v304" = %"v36" +p #24;
    %"chk36" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v304";
    %"v305" : W = (RawLoad (LdNarrow Sw) 0) %"chk36"
    => br %"v305" ? "L300" : "L301" };
  ir_blk{ @"L300":
    %"v307" = %"v36" +p #56;
    %"chk37" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v307";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v310" : L = Shl %"pr.1", #3;
    %"v311" = %"v308" +p %"v310";
    %"v312" = %"v311" +p #4;
    %"chk38" : A = (Check 0 4 Read 1) %"v312";
    %"v313" : W = (RawLoad (LdNarrow Uw) 0) %"chk38";
    call %"v314" : W = $"glibc_dcigettext#__bswap_32"(W %"v313")
    => goto "L302" };
  ir_blk{ @"L301":
    %"v316" = %"v36" +p #56;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v316";
    %"v317" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v319" : L = Shl %"pr.1", #3;
    %"v320" = %"v317" +p %"v319";
    %"v321" = %"v320" +p #4;
    %"chk40" : A = (Check 0 4 Read 1) %"v321";
    %"v322" : W = (RawLoad (LdNarrow Uw) 0) %"chk40"
    => goto "L302" };
  ir_blk{ @"L302" [%"v323" : W = phi("L300" => %"v314", "L301" => %"v322")]:
    %"v324" : L = (Ext Uw) %"v323";
    %"v325" = %"v299" +p %"v324";
    %"v330" = %"v36" +p #24;
    %"chk41" : A = (Renew 0 4 Read 1) %"chk36", %"v330";
    %"v331" : W = (RawLoad (LdNarrow Sw) 0) %"chk41"
    => br %"v331" ? "L326" : "L327" };
  ir_blk{ @"L326":
    %"v333" = %"v36" +p #56;
    %"chk42" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v333";
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v336" : L = Shl %"pr.1", #3;
    %"v337" = %"v334" +p %"v336";
    %"chk43" : A = (Check 0 4 Read 1) %"v337";
    %"v338" : W = (RawLoad (LdNarrow Uw) 0) %"chk43";
    call %"v339" : W = $"glibc_dcigettext#__bswap_32"(W %"v338")
    => goto "L328" };
  ir_blk{ @"L327":
    %"v341" = %"v36" +p #56;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v341";
    %"v342" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v344" : L = Shl %"pr.1", #3;
    %"v345" = %"v342" +p %"v344";
    %"chk45" : A = (Check 0 4 Read 1) %"v345";
    %"v346" : W = (RawLoad (LdNarrow Uw) 0) %"chk45"
    => goto "L328" };
  ir_blk{ @"L328" [%"v347" : W = phi("L326" => %"v339", "L327" => %"v346")]:
    %"v348" : W = Add %"v347", #1;
    %"v349" : L = (Ext Uw) %"v348"
    => goto "L293" };
  ir_blk{ @"L292":
    %"v351" = %"v36" +p #80;
    %"chk46" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v351";
    %"v352" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v356" : L = Sub %"pr.1", %"v296";
    %"v357" : L = Shl %"v356", #4;
    %"v358" = %"v352" +p %"v357";
    %"v359" = %"v358" +p #8;
    %"chk47" : A = (Check 0 8 Read 8) %"v359";
    %"v360" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v363" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v369" = %"v363" +p %"v357";
    %"chk49" : A = (Check 0 8 Read 1) %"v369";
    %"v370" : L = (RawLoad LdL 0) %"chk49"
    => goto "L293" };
  ir_blk{ @"L293" [%"pr.5" : L = phi("L292" => %"v370", "L328" => %"v349"); %"pr.2" : P = phi("L292" => %"v360", "L328" => %"v325")]:
    => br %"v6" ? "L371" : "L373" };
  ir_blk{ @"L371":
    call %"v377" : P = $"glibc_dcigettext#get_output_charset"(P %"v2");
    %"v382" = %"v36" +p #128;
    call %"v383" : W = $"__GI___pthread_rwlock_rdlock"(P %"v382");
    %"v385" = %"v36" +p #120;
    %"chk50" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v385";
    %"v386" : L = (RawLoad LdL 0) %"chk50"
    => goto "L388" };
  ir_blk{ @"L388" [%"pr.17" : L = phi("L371" => %"v386", "L389" => %"v395")]:
    %"v393" : W = (Cmp Ugt L) %"pr.17", #0
    => br %"v393" ? "L389" : "L391" };
  ir_blk{ @"L389":
    %"v395" : L = Sub %"pr.17", #1;
    %"v400" = %"v36" +p #112;
    %"chk51" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v400";
    %"v401" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v403" : L = Mul %"v395", #24;
    %"v404" = %"v401" +p %"v403";
    %"chk52" : A = (Check 0 8 Read 8) %"v404";
    %"v405" : P = (RawLoadPointer 0 load_effects) %"chk52";
    call %"v407" : W = $"__GI_strcmp"(P %"v405", P %"v377");
    %"v408" : W = (Cmp Eq W) %"v407", #0
    => br %"v408" ? "L396" : poll "L388" };
  ir_blk{ @"L396":
    %"v410" = %"v36" +p #112;
    %"chk53" : A = (Renew 0 8 Read 8) %"chk51", %"v410";
    %"v411" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v414" = %"v411" +p %"v403"
    => goto "L391" };
  ir_blk{ @"L391" [%"pr.14" : P = phi("L388" => #0, "L396" => %"v414")]:
    %"v417" = %"v36" +p #128;
    call %"v418" : W = $"__GI___pthread_rwlock_unlock"(P %"v417");
    %"v423" : L = Ptoi %"pr.14";
    %"v425" : W = (Cmp Eq L) %"v423", %"v31"
    => br %"v425" ? "L419" : "L421" };
  ir_blk{ @"L419":
    %"v427" = %"v36" +p #128;
    call %"v428" : W = $"__GI___pthread_rwlock_wrlock"(P %"v427");
    %"v430" = %"v36" +p #120;
    %"chk54" : A = (Renew 0 8 Read 1) %"chk50", %"v430";
    %"v431" : L = (RawLoad LdL 0) %"chk54"
    => goto "L433" };
  ir_blk{ @"L433" [%"pr.18" : L = phi("L419" => %"v431", "L434" => %"v440")]:
    %"v438" : W = (Cmp Ugt L) %"pr.18", #0
    => br %"v438" ? "L434" : "L436" };
  ir_blk{ @"L434":
    %"v440" : L = Sub %"pr.18", #1;
    %"v445" = %"v36" +p #112;
    %"chk55" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v445";
    %"v446" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v448" : L = Mul %"v440", #24;
    %"v449" = %"v446" +p %"v448";
    %"chk56" : A = (Check 0 8 Read 8) %"v449";
    %"v450" : P = (RawLoadPointer 0 load_effects) %"chk56";
    call %"v452" : W = $"__GI_strcmp"(P %"v450", P %"v377");
    %"v453" : W = (Cmp Eq W) %"v452", #0
    => br %"v453" ? "L441" : poll "L433" };
  ir_blk{ @"L441":
    %"v455" = %"v36" +p #112;
    %"chk57" : A = (Renew 0 8 Read 8) %"chk55", %"v455";
    %"v456" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"v459" = %"v456" +p %"v448"
    => goto "L460" };
  ir_blk{ @"L436":
    %"v467" = %"v36" +p #112;
    %"chk58" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v467";
    %"v468" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v469" : L = Ptoi %"v468";
    %"v471" : W = (Cmp Ne L) %"v469", %"v31"
    => br %"v471" ? "L463" : "L464" };
  ir_blk{ @"L463":
    %"v473" = %"v36" +p #112;
    %"v474" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v476" : L = Add %"v431", #1;
    %"v477" : L = Mul %"v476", #24;
    call %"v478" : P = $"realloc"(P %"v474", L %"v477")
    => goto "L465" };
  ir_blk{ @"L464":
    %"v480" : L = Add %"v431", #1;
    %"v481" : L = Mul %"v480", #24;
    call %"v482" : P = $"malloc"(L %"v481")
    => goto "L465" };
  ir_blk{ @"L465" [%"v483" : P = phi("L463" => %"v478", "L464" => %"v482")]:
    %"v488" : L = Ptoi %"v483";
    %"v490" : W = (Cmp Eq L) %"v488", %"v31"
    => br %"v490" ? "L493" : "L486" };
  ir_blk{ @"L493":
    %"v495" = %"v36" +p #128;
    call %"v496" : W = $"__GI___pthread_rwlock_unlock"(P %"v495");
    (Flight (a "v499") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v499" };
  ir_blk{ @"L486":
    %"v502" = %"v36" +p #112;
    %"chk60" : A = (Renew 0 8 Write 8) %"chk58", %"v502";
    store.ptr [%"chk60" + 0] <- %"v483";
    call %"v505" : P = $"__GI___strdup"(P %"v377");
    %"v510" : L = Ptoi %"v505";
    %"v512" : W = (Cmp Eq L) %"v510", %"v31"
    => br %"v512" ? poll "L493" : "L508" }] [ir_blk{ @"L508":
    %"v518" : L = Mul %"v431", #24;
    %"v519" = %"v483" +p %"v518";
    %"chk61" : A = (Check 0 8 Write 8) %"v519";
    store.ptr [%"chk61" + 0] <- %"v505";
    %"v523" = %"v519" +p #8;
    (Flight (a "v526") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk62" : A = (HalfCheck Upper 0 8 Write 8) %"chk61", %"v523";
    store.ptr [%"chk62" + 0] <- %"v526";
    %"v531" : P = Copy $"glibc_dcigettext#str.279";
    call %"v532" : P = $"_nl_find_msg"(P %"v0", P %"v2", P %"v531", W #0, P %"v528");
    %"v540" : L = Ptoi %"v532";
    %"v541" : L = Ptoi %"v526";
    %"v542" : W = (Cmp Eq L) %"v540", %"v541"
    => br %"v542" ? "L533" : "L535" };
  ir_blk{ @"L533":
    (Flight (a "v547") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v547" };
  ir_blk{ @"L535":
    %"v555" : W = (Cmp Ne L) %"v540", %"v31"
    => br %"v555" ? "L549" : "L551" };
  ir_blk{ @"L549":
    %"v558" : P = Copy $"glibc_dcigettext#str.280";
    call %"v559" : P = $"__GI_strstr"(P %"v532", P %"v558");
    %"v564" : L = Ptoi %"v559";
    %"v566" : W = (Cmp Ne L) %"v564", %"v31"
    => br %"v566" ? "L560" : "L551" };
  ir_blk{ @"L560":
    %"v571" : P = Copy $"glibc_dcigettext#str.280";
    call %"v572" : L = $"__GI_strlen"(P %"v571");
    %"v573" = %"v559" +p %"v572";
    %"v575" : P = Copy $"glibc_dcigettext#str.281";
    call %"v576" : L = $"__GI_strcspn"(P %"v573", P %"v575");
    %"v578" : L = Add %"v576", #1;
    %"v579" : P = (Alloc 16) %"v578";
    call %"v583" : P = $"__GI_mempcpy"(P %"v579", P %"v573", L %"v576");
    %"chk63" : A = (Check 0 1 Write 1) %"v583";
    store Wb [%"chk63" + 0] <- #0;
    call %"v588" : P = $"__GI___gconv_create_spec"(P %"v585", P %"v579", P %"v505");
    %"v589" = %"v585" +p #16;
    %"chk64" : A = (Check 0 1 Write 1) %"v589";
    store Wb [%"chk64" + 0] <- #1;
    %"v593" = %"v519" +p #8;
    call %"v594" : W = $"__GI___gconv_open"(P %"v585", P %"v593", W #1);
    call void $"__GI___gconv_destroy_spec"(P %"v585");
    %"v599" : W = (Cmp Ne W) %"v594", #0
    => br %"v599" ? "L595" : "L551" };
  ir_blk{ @"L595":
    %"v606" : W = (Cmp Ne W) %"v594", #(-1)
    => br %"v606" ? "L602" : "L604" };
  ir_blk{ @"L602":
    %"v610" = %"v36" +p #128;
    call %"v611" : W = $"__GI___pthread_rwlock_unlock"(P %"v610");
    call void $"free"(P %"v505")
    => ret #0 };
  ir_blk{ @"L604":
    %"v615" = %"v519" +p #8;
    (Flight (a "v618") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk65" : A = (Renew 0 8 Write 8) %"chk62", %"v615";
    store.ptr [%"chk65" + 0] <- %"v618"
    => goto "L551" };
  ir_blk{ @"L551":
    %"v620" = %"v519" +p #16;
    %"chk66" : A = (HalfCheck Upper 0 8 Write 8) %"chk61", %"v620";
    store.ptr [%"chk66" + 0] <- #0;
    %"v622" = %"v36" +p #120;
    %"chk67" : A = (Renew 0 8 Read 1) %"chk50", %"v622";
    %"v623" : L = (RawLoad LdL 0) %"chk67";
    %"v624" : L = Add %"v623", #1;
    %"chk68" : A = (Renew 0 8 Write 1) %"chk50", %"v622";
    store Wl [%"chk68" + 0] <- %"v624"
    => goto "L460" };
  ir_blk{ @"L460" [%"pr.16" : P = phi("L441" => %"v459", "L551" => %"v519")]:
    %"v626" = %"v36" +p #128;
    call %"v627" : W = $"__GI___pthread_rwlock_unlock"(P %"v626")
    => goto "L421" };
  ir_blk{ @"L421" [%"pr.15" : P = phi("L460" => %"pr.16", "L391" => %"pr.14")]:
    %"v632" = %"pr.15" +p #8;
    %"chk69" : A = (Check 0 8 Read 8) %"v632";
    %"v633" : P = (RawLoadPointer 0 load_effects) %"chk69";
    (Flight (a "v636") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v637" : L = Ptoi %"v633";
    %"v638" : L = Ptoi %"v636";
    %"v639" : W = (Cmp Ne L) %"v637", %"v638"
    => br %"v639" ? "L628" : "L373" };
  ir_blk{ @"L628":
    %"v644" = %"pr.15" +p #16;
    %"chk70" : A = (HalfCheck Upper 0 8 Read 8) %"chk69", %"v644";
    %"v645" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v646" : L = Ptoi %"v645";
    %"v648" : W = (Cmp Eq L) %"v646", %"v31"
    => br %"v648" ? "L640" : "L642" };
  ir_blk{ @"L640":
    %"v652" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk71" : A = (Check 0 4 Write 4) %"v652";
    %"v659" : W = (RawCas (CasNarrow Sw) 0) %"chk71", #0, #1;
    %"v660" : W = (Cmp Eq W) %"v659", #0
    => br %"v660" ? "L662" : "L661" };
  ir_blk{ @"L661":
    => goto "L662" };
  ir_blk{ @"L662":
    %"v663" : W = (Cmp Ne W) %"v659", #0
    => br %"v663" ? "L666" : "L655" };
  ir_blk{ @"L666":
    call void $"__GI___lll_lock_wait_private"(P %"v652")
    => goto "L655" };
  ir_blk{ @"L655":
    %"v680" = %"pr.15" +p #16;
    %"chk72" : A = (Renew 0 8 Read 8) %"chk70", %"v680";
    %"v681" : P = (RawLoadPointer 0 load_effects) %"chk72";
    %"v682" : L = Ptoi %"v681";
    %"v684" : W = (Cmp Eq L) %"v682", %"v31"
    => br %"v684" ? "L676" : "L678" };
  ir_blk{ @"L676":
    %"v686" = %"pr.15" +p #16;
    %"v689" = %"v36" +p #64;
    %"chk73" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v689";
    %"v690" : W = (RawLoad (LdNarrow Uw) 0) %"chk73";
    %"v691" : W = Add %"v39", %"v690";
    %"v692" : L = (Ext Uw) %"v691";
    call %"v693" : P = $"calloc"(L %"v692", L #8);
    %"chk74" : A = (Renew 0 8 Write 8) %"chk70", %"v686";
    store.ptr [%"chk74" + 0] <- %"v693";
    %"chk75" : A = (Renew 0 8 Read 8) %"chk70", %"v686";
    %"v699" : P = (RawLoadPointer 0 load_effects) %"chk75";
    %"v700" : L = Ptoi %"v699";
    %"v702" : W = (Cmp Ne L) %"v700", %"v31"
    => br %"v702" ? "L703" : "L696" };
  ir_blk{ @"L696":
    %"v706" = %"pr.15" +p #16;
    (Flight (a "v709") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk76" : A = (Renew 0 8 Write 8) %"chk70", %"v706";
    store.ptr [%"chk76" + 0] <- %"v709"
    => goto "L678" };
  ir_blk{ @"L678":
    %"v711" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk77" : A = (Check 0 4 Read 1) %"v711";
    %"v715" : W = (RawLoad (LdNarrow Sw) 0) %"chk77"
    => goto "L716" };
  ir_blk{ @"L716" [%"v718" : W = phi("L678" => %"v715", "L716" => %"v719")]:
    %"chk78" : A = (HalfCheck Lower 0 4 Write 4) %"chk77", %"v711";
    %"v719" : W = (RawCas (CasNarrow Sw) 0) %"chk78", %"v718", #0;
    %"v720" : W = (Cmp Eq W) %"v719", %"v718"
    => br %"v720" ? "L717" : poll "L716" };
  ir_blk{ @"L717":
    %"v725" : W = (Cmp Sgt W) %"v718", #1
    => br %"v725" ? "L728" : "L642" };
  ir_blk{ @"L728":
    call void $"__GI___lll_lock_wake_private"(P %"v711")
    => goto "L642" };
  ir_blk{ @"L642":
    %"v743" = %"pr.15" +p #16;
    %"chk79" : A = (Renew 0 8 Read 8) %"chk70", %"v743";
    %"v744" : P = (RawLoadPointer 0 load_effects) %"chk79";
    (Flight (a "v747") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v748" : L = Ptoi %"v744";
    %"v749" : L = Ptoi %"v747";
    %"v750" : W = (Cmp Eq L) %"v748", %"v749"
    => br %"v750" ? "L739" : "L741" };
  ir_blk{ @"L739":
    (Flight (a "v755") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v755" };
  ir_blk{ @"L741":
    %"v761" = %"pr.15" +p #16;
    %"v762" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v764" : L = Shl %"pr.1", #3;
    %"v765" = %"v762" +p %"v764";
    %"chk81" : A = (Check 0 8 Read 8) %"v765";
    %"v766" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"v767" : L = Ptoi %"v766";
    %"v769" : W = (Cmp Eq L) %"v767", %"v31"
    => br %"v769" ? "L757" : "L759" };
  ir_blk{ @"L757":
    %"v774" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk82" : A = (Check 0 4 Write 4) %"v774";
    %"v781" : W = (RawCas (CasNarrow Sw) 0) %"chk82", #0, #1;
    %"v782" : W = (Cmp Eq W) %"v781", #0
    => br %"v782" ? "L784" : "L783" };
  ir_blk{ @"L783":
    => goto "L784" };
  ir_blk{ @"L784":
    %"v785" : W = (Cmp Ne W) %"v781", #0
    => br %"v785" ? "L788" : "L703" };
  ir_blk{ @"L788":
    call void $"__GI___lll_lock_wait_private"(P %"v774")
    => goto "L703" };
  ir_blk{ @"L703":
    %"chk83" : A = (Check 0 8 Write 8) %"v770";
    store.ptr [%"chk83" + 0] <- %"pr.2"
    => goto "L799" };
  ir_blk{ @"L799" [%"pr.19" : W = phi("L703" => #0, "L927" => %"pr.20")]:
    %"v806" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk84" : A = (Check 0 8 Read 1) %"v806";
    %"v807" : L = (RawLoad LdL 0) %"chk84";
    %"v808" : W = (Cmp Ult L) %"v807", #8
    => br %"v808" ? "L809" : "L805" };
  ir_blk{ @"L805":
    %"v811" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk85" : A = (Check 0 8 Read 8) %"v811";
    %"v812" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v813" = %"v812" +p #8;
    %"chk86" : A = (Check 0 8 Write 8) %"v771";
    store.ptr [%"chk86" + 0] <- %"v813";
    %"v817" = %"pr.15" +p #8;
    %"chk87" : A = (Renew 0 8 Read 8) %"chk69", %"v817";
    %"v818" : P = (RawLoadPointer 0 load_effects) %"chk87";
    %"chk88" : A = (Renew 0 8 Read 8) %"chk83", %"v770";
    %"v819" : P = (RawLoadPointer 0 load_effects) %"chk88";
    %"v821" = %"v819" +p %"pr.5";
    %"chk89" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v822" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"v823" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk90" : A = (Check 0 8 Read 1) %"v823";
    %"v824" : L = (RawLoad LdL 0) %"chk90";
    %"v825" = %"v822" +p %"v824";
    (Flight (a "v826") Sub [(FAddress (t "v825")); (FValue (Const 8))] (LowerOf (t "v825")));
    call %"v827" : W = $"__gconv"(P %"v818", P %"v770", P %"v821", P %"v771", P %"v826", P %"v814");
    %"v832" : W = (Cmp Eq W) %"v827", #0
    => br %"v832" ? "L834" : "L833" };
  ir_blk{ @"L833":
    %"v836" : W = (Cmp Eq W) %"v827", #4
    => goto "L834" };
  ir_blk{ @"L834" [%"v838" : W = phi("L805" => #1, "L833" => %"v836")]:
    => br %"v838" ? "L801" : "L830" };
  ir_blk{ @"L830":
    %"v844" : W = (Cmp Ne W) %"v827", #5
    => br %"v844" ? "L840" : "L842" };
  ir_blk{ @"L840":
    %"v846" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk91" : A = (Check 0 4 Read 1) %"v846";
    %"v850" : W = (RawLoad (LdNarrow Sw) 0) %"chk91"
    => goto "L851" };
  ir_blk{ @"L851" [%"v853" : W = phi("L840" => %"v850", "L851" => %"v854")]:
    %"chk92" : A = (HalfCheck Lower 0 4 Write 4) %"chk91", %"v846";
    %"v854" : W = (RawCas (CasNarrow Sw) 0) %"chk92", %"v853", #0;
    %"v855" : W = (Cmp Eq W) %"v854", %"v853"
    => br %"v855" ? "L852" : poll "L851" };
  ir_blk{ @"L852":
    %"v860" : W = (Cmp Sgt W) %"v853", #1
    => br %"v860" ? "L863" : "L858" };
  ir_blk{ @"L863":
    call void $"__GI___lll_lock_wake_private"(P %"v846")
    => goto "L858" };
  ir_blk{ @"L858":
    => ret #0 };
  ir_blk{ @"L842":
    %"chk93" : A = (Renew 0 8 Write 8) %"chk83", %"v770";
    store.ptr [%"chk93" + 0] <- %"pr.2"
    => goto "L809" };
  ir_blk{ @"L809":
    %"v880" : W = (Cmp Sgt W) %"pr.19", #0
    => br %"v880" ? "L876" : "L877" };
  ir_blk{ @"L876":
    %"v882" : W = Add %"pr.19", #1;
    %"v883" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"v885" : W = Mul %"v882", #4080;
    %"v886" : L = (Ext Sw) %"v885";
    %"chk94" : A = (Check 0 8 Write 1) %"v883";
    store Wl [%"chk94" + 0] <- %"v886";
    %"v887" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk95" : A = (Check 0 8 Read 8) %"v887";
    %"v888" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v889" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk96" : A = (Check 0 8 Read 1) %"v889";
    %"v890" : L = (RawLoad LdL 0) %"chk96";
    call %"v891" : P = $"realloc"(P %"v888", L %"v890");
    %"v896" : L = Ptoi %"v891";
    %"v898" : W = (Cmp Ne L) %"v896", %"v31"
    => br %"v898" ? "L892" : "L893" };
  ir_blk{ @"L892":
    %"v899" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk97" : A = (Check 0 8 Write 8) %"v899";
    store.ptr [%"chk97" + 0] <- %"v891"
    => goto "L878" };
  ir_blk{ @"L893":
    %"v902" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk98" : A = (Check 0 8 Read 8) %"v902";
    %"v903" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"v904" : P = Copy $"glibc_dcigettext#transmem_list";
    %"v905" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk99" : A = (Check 0 8 Read 8) %"v905";
    %"v906" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"chk100" : A = (Check 0 8 Read 8) %"v906";
    %"v907" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"chk101" : A = (Check 0 8 Write 8) %"v904";
    store.ptr [%"chk101" + 0] <- %"v907";
    call void $"free"(P %"v903")
    => goto "L878" };
  ir_blk{ @"L877":
    %"v909" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk102" : A = (Check 0 8 Write 1) %"v909";
    store Wl [%"chk102" + 0] <- #4080;
    %"v910" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk103" : A = (Check 0 8 Read 1) %"v910";
    %"v911" : L = (RawLoad LdL 0) %"chk103";
    call %"v912" : P = $"malloc"(L %"v911");
    %"v917" : L = Ptoi %"v912";
    %"v919" : W = (Cmp Ne L) %"v917", %"v31"
    => br %"v919" ? "L913" : "L878" };
  ir_blk{ @"L913":
    %"v921" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk104" : A = (Check 0 8 Read 8) %"v921";
    %"v922" : P = (RawLoadPointer 0 load_effects) %"chk104";
    %"chk105" : A = (Check 0 8 Write 8) %"v912";
    store.ptr [%"chk105" + 0] <- %"v922";
    %"v923" : P = Copy $"glibc_dcigettext#transmem_list";
    %"chk106" : A = (Check 0 8 Write 8) %"v923";
    store.ptr [%"chk106" + 0] <- %"v912"
    => goto "L878" };
  ir_blk{ @"L878" [%"pr.21" : P = phi("L892" => %"v891", "L893" => %"v891", "L913" => %"v912", "L877" => %"v912"); %"pr.20" : W = phi("L892" => %"v882", "L893" => %"v882", "L913" => #1, "L877" => #1)]:
    %"v929" : L = Ptoi %"pr.21";
    %"v931" : W = (Cmp Eq L) %"v929", %"v31"
    => br %"v931" ? "L925" : "L927" };
  ir_blk{ @"L925":
    %"v934" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk107" : A = (Check 0 8 Write 8) %"v934";
    store.ptr [%"chk107" + 0] <- #0;
    %"v935" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk108" : A = (Check 0 8 Write 1) %"v935";
    store Wl [%"chk108" + 0] <- #0;
    %"v937" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk109" : A = (Check 0 4 Read 1) %"v937";
    %"v941" : W = (RawLoad (LdNarrow Sw) 0) %"chk109"
    => goto "L942" };
  ir_blk{ @"L942" [%"v944" : W = phi("L925" => %"v941", "L942" => %"v945")]:
    %"chk110" : A = (HalfCheck Lower 0 4 Write 4) %"chk109", %"v937";
    %"v945" : W = (RawCas (CasNarrow Sw) 0) %"chk110", %"v944", #0;
    %"v946" : W = (Cmp Eq W) %"v945", %"v944"
    => br %"v946" ? "L943" : poll "L942" };
  ir_blk{ @"L943":
    %"v951" : W = (Cmp Sgt W) %"v944", #1
    => br %"v951" ? "L954" : "L949" };
  ir_blk{ @"L954":
    call void $"__GI___lll_lock_wake_private"(P %"v937")
    => goto "L949" };
  ir_blk{ @"L949":
    (Flight (a "v967") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v967" };
  ir_blk{ @"L927":
    %"v969" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"v971" = %"pr.21" +p #8;
    %"chk111" : A = (Check 0 8 Write 8) %"v969";
    store.ptr [%"chk111" + 0] <- %"v971";
    %"v972" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk112" : A = (Check 0 8 Read 1) %"v972";
    %"v973" : L = (RawLoad LdL 0) %"chk112";
    %"v974" : L = Sub %"v973", #8;
    %"chk113" : A = (Renew 0 8 Write 1) %"chk112", %"v972";
    store Wl [%"chk113" + 0] <- %"v974"
    => goto poll "L799" };
  ir_blk{ @"L801":
    %"v975" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk114" : A = (Check 0 8 Read 8) %"v975";
    %"v976" : P = (RawLoadPointer 0 load_effects) %"chk114";
    %"chk115" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v977" : P = (RawLoadPointer 0 load_effects) %"chk115";
    %"v978" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk116" : A = (Check 0 8 Read 8) %"v978";
    %"v979" : P = (RawLoadPointer 0 load_effects) %"chk116";
    %"v980" : L = Ptoi %"v977";
    %"v981" : L = Ptoi %"v979";
    %"v982" : L = Sub %"v980", %"v981";
    %"v983" : L = Sub %"v982", #8;
    %"chk117" : A = (Check 0 8 Write 1) %"v976";
    store Wl [%"chk117" + 0] <- %"v983";
    %"v985" = %"pr.15" +p #16;
    %"chk118" : A = (Renew 0 8 Read 8) %"chk70", %"v985";
    %"v986" : P = (RawLoadPointer 0 load_effects) %"chk118";
    %"v988" : L = Shl %"pr.1", #3;
    %"v989" = %"v986" +p %"v988";
    %"v990" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk119" : A = (Check 0 8 Read 8) %"v990";
    %"v991" : P = (RawLoadPointer 0 load_effects) %"chk119";
    %"chk120" : A = (Check 0 8 Write 8) %"v989";
    store.ptr [%"chk120" + 0] <- %"v991";
    %"v992" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk121" : A = (Check 0 8 Read 1) %"v992";
    %"v993" : L = (RawLoad LdL 0) %"chk121";
    %"chk122" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v994" : P = (RawLoadPointer 0 load_effects) %"chk122";
    %"v995" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk123" : A = (Check 0 8 Read 8) %"v995";
    %"v996" : P = (RawLoadPointer 0 load_effects) %"chk123";
    %"v997" : L = Ptoi %"v994";
    %"v998" : L = Ptoi %"v996";
    %"v999" : L = Sub %"v997", %"v998";
    %"v1000" : L = Sub %"v993", %"v999";
    %"chk124" : A = (Renew 0 8 Write 1) %"chk121", %"v992";
    store Wl [%"chk124" + 0] <- %"v1000";
    %"v1001" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk125" : A = (Renew 0 8 Read 8) %"chk86", %"v771";
    %"v1002" : P = (RawLoadPointer 0 load_effects) %"chk125";
    %"chk126" : A = (Check 0 8 Write 8) %"v1001";
    store.ptr [%"chk126" + 0] <- %"v1002";
    %"v1003" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem.283";
    %"chk127" : A = (Check 0 8 Read 8) %"v1003";
    %"v1004" : P = (RawLoadPointer 0 load_effects) %"chk127";
    %"v1005" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk128" : A = (Check 0 8 Read 1) %"v1005";
    %"v1006" : L = (RawLoad LdL 0) %"chk128";
    %"v1008" : L = And %"v1006", #7;
    %"v1009" = %"v1004" +p %"v1008";
    %"chk129" : A = (Renew 0 8 Write 8) %"chk127", %"v1003";
    store.ptr [%"chk129" + 0] <- %"v1009";
    %"v1010" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"v1011" : P = Copy $"glibc_dcigettext#_nl_find_msg.freemem_size.284";
    %"chk130" : A = (Check 0 8 Read 1) %"v1011";
    %"v1012" : L = (RawLoad LdL 0) %"chk130";
    %"v1015" : L = And %"v1012", #18446744073709551608;
    %"chk131" : A = (Check 0 8 Write 1) %"v1010";
    store Wl [%"chk131" + 0] <- %"v1015";
    %"v1017" : P = Copy $"glibc_dcigettext#_nl_find_msg.lock.282";
    %"chk132" : A = (Check 0 4 Read 1) %"v1017";
    %"v1021" : W = (RawLoad (LdNarrow Sw) 0) %"chk132"
    => goto "L1022" };
  ir_blk{ @"L1022" [%"v1024" : W = phi("L801" => %"v1021", "L1022" => %"v1025")]:
    %"chk133" : A = (HalfCheck Lower 0 4 Write 4) %"chk132", %"v1017";
    %"v1025" : W = (RawCas (CasNarrow Sw) 0) %"chk133", %"v1024", #0;
    %"v1026" : W = (Cmp Eq W) %"v1025", %"v1024"
    => br %"v1026" ? "L1023" : poll "L1022" };
  ir_blk{ @"L1023":
    %"v1031" : W = (Cmp Sgt W) %"v1024", #1
    => br %"v1031" ? "L1034" : "L759" };
  ir_blk{ @"L1034":
    call void $"__GI___lll_lock_wake_private"(P %"v1017")
    => goto "L759" };
  ir_blk{ @"L759":
    %"v1046" = %"pr.15" +p #16;
    %"chk134" : A = (Renew 0 8 Read 8) %"chk70", %"v1046";
    %"v1047" : P = (RawLoadPointer 0 load_effects) %"chk134";
    %"v1049" : L = Shl %"pr.1", #3;
    %"v1050" = %"v1047" +p %"v1049";
    %"chk135" : A = (Check 0 8 Read 8) %"v1050";
    %"v1051" : P = (RawLoadPointer 0 load_effects) %"chk135";
    %"v1052" = %"v1051" +p #8;
    %"v1055" : P = (RawLoadPointer 0 load_effects) %"chk134";
    %"v1058" = %"v1055" +p %"v1049";
    %"chk137" : A = (Check 0 8 Read 8) %"v1058";
    %"v1059" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk138" : A = (Check 0 8 Read 1) %"v1059";
    %"v1060" : L = (RawLoad LdL 0) %"chk138"
    => goto "L373" };
  ir_blk{ @"L373" [%"pr.6" : L = phi("L759" => %"v1060", "L421" => %"pr.5", "L293" => %"pr.5"); %"pr.3" : P = phi("L759" => %"v1052", "L421" => %"pr.2", "L293" => %"pr.2")]:
    %"chk139" : A = (Check 0 8 Write 1) %"v8";
    store Wl [%"chk139" + 0] <- %"pr.6"
    => ret %"pr.3" }])) }.

Definition hello_image_fn__nl_explode_name : func :=
  ir_fn{ "export" "_nl_explode_name"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk1" + 0] <- #0;
    %"chk2" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk2" + 0] <- #0;
    %"chk3" : A = (Check 0 8 Write 8) %"v10";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk4" + 0] <- %"v0";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk4", %"v2";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto "iw_1.L2";
  @"iw_1.L2" [%"iw_1.pr.1" : P = phi("iw_1.L3" => %"iw_1.v34", "start" => %"v21")]:
    %"chk6" : A = (Check 0 1 Read 1) %"iw_1.pr.1";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v8" : W = (Cmp Ne W) %"iw_1.v7", #0
    => br %"iw_1.v8" ? "iw_1.L9" : "iw_1.L10";
  @"iw_1.L9":
    %"iw_1.v13" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v14" : W = (Cmp Ne W) %"iw_1.v13", #95
    => goto "iw_1.L10";
  @"iw_1.L10" [%"iw_1.v16" : W = phi("iw_1.L2" => #0, "iw_1.L9" => %"iw_1.v14")]:
    => br %"iw_1.v16" ? "iw_1.L17" : "iw_1.L18";
  @"iw_1.L17":
    %"iw_1.v21" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v21", #64
    => goto "iw_1.L18";
  @"iw_1.L18" [%"iw_1.v24" : W = phi("iw_1.L10" => #0, "iw_1.L17" => %"iw_1.v22")]:
    => br %"iw_1.v24" ? "iw_1.L25" : "iw_1.L26";
  @"iw_1.L25":
    %"iw_1.v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v30" : W = (Cmp Ne W) %"iw_1.v29", #46
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.v32" : W = phi("iw_1.L18" => #0, "iw_1.L25" => %"iw_1.v30")]:
    => br %"iw_1.v32" ? "iw_1.L3" : "iw_1.join";
  @"iw_1.L3":
    %"iw_1.v34" = %"iw_1.pr.1" +p #1
    => goto poll "iw_1.L2";
  @"iw_1.join":
    %"chk10" : A = (Renew 0 8 Read 8) %"chk4", %"v2";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v29" : L = Ptoi %"v27";
    %"v30" : L = Ptoi %"iw_1.pr.1";
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => br %"v31" ? "L23" : "L24";
  @"L23":
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk10";
    call %"v34" : P = $"__GI_strchr"(P %"v33", W #0)
    => goto "L25";
  @"L24":
    %"v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v41" : W = (Cmp Eq W) %"v40", #95
    => br %"v41" ? "L35" : "L37";
  @"L35":
    %"chk13" : A = (Renew 0 1 Write 1) %"chk6", %"iw_1.pr.1";
    store Wb [%"chk13" + 0] <- #0;
    %"v46" = %"iw_1.pr.1" +p #1;
    %"chk14" : A = (Renew 0 8 Write 8) %"chk1", %"v6";
    store.ptr [%"chk14" + 0] <- %"v46"
    => goto "L47";
  @"L47" [%"pr.3" : P = phi("L35" => %"v46", "L48" => %"v71")]:
    %"chk15" : A = (Check 0 1 Read 1) %"pr.3";
    %"v52" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"v53" : W = (Cmp Ne W) %"v52", #0
    => br %"v53" ? "L54" : "L55";
  @"L54":
    %"v58" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"v59" : W = (Cmp Ne W) %"v58", #46
    => goto "L55";
  @"L55" [%"v61" : W = phi("L47" => #0, "L54" => %"v59")]:
    => br %"v61" ? "L62" : "L63";
  @"L62":
    %"v66" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"v67" : W = (Cmp Ne W) %"v66", #64
    => goto "L63";
  @"L63" [%"v69" : W = phi("L55" => #0, "L62" => %"v67")]:
    => br %"v69" ? "L48" : "L37";
  @"L48":
    %"v71" = %"pr.3" +p #1
    => goto poll "L47";
  @"L37" [%"pr.13" : W = phi("L63" => #4, "L24" => #0); %"pr.2" : P = phi("L63" => %"pr.3", "L24" => %"iw_1.pr.1")]:
    %"chk18" : A = (Check 0 1 Read 1) %"pr.2";
    %"v79" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"v80" : W = (Cmp Eq W) %"v79", #46
    => br %"v80" ? "L74" : "L25";
  @"L74":
    %"chk19" : A = (Renew 0 1 Write 1) %"chk18", %"pr.2";
    store Wb [%"chk19" + 0] <- #0;
    %"v85" = %"pr.2" +p #1;
    %"chk20" : A = (Renew 0 8 Write 8) %"chk2", %"v8";
    store.ptr [%"chk20" + 0] <- %"v85"
    => goto "L86";
  @"L86" [%"pr.5" : P = phi("L74" => %"v85", "L87" => %"v102")]:
    %"chk21" : A = (Check 0 1 Read 1) %"pr.5";
    %"v91" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v92" : W = (Cmp Ne W) %"v91", #0
    => br %"v92" ? "L93" : "L94";
  @"L93":
    %"v97" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v98" : W = (Cmp Ne W) %"v97", #64
    => goto "L94";
  @"L94" [%"v100" : W = phi("L86" => #0, "L93" => %"v98")]:
    => br %"v100" ? "L87" : "L88";
  @"L87":
    %"v102" = %"pr.5" +p #1
    => goto poll "L86";
  @"L88":
    %"v104" : W = Or %"pr.13", #2;
    %"chk23" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v111" : L = Ptoi %"v109";
    %"v112" : L = Ptoi %"pr.5";
    %"v113" : W = (Cmp Ne L) %"v111", %"v112"
    => br %"v113" ? "L114" : "L115";
  @"L114":
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk25" : A = (Check 0 1 Read 1) %"v117";
    %"v119" : W = (RawLoad (LdNarrow Sb) 0) %"chk25";
    %"v120" : W = (Cmp Ne W) %"v119", #0
    => goto "L115";
  @"L115" [%"v122" : W = phi("L88" => #0, "L114" => %"v120")]:
    => br %"v122" ? "L105" : "L25";
  @"L105":
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v130" : L = Ptoi %"v128";
    %"v131" : L = Sub %"v112", %"v130";
    call %"v132" : P = $"_nl_normalize_codeset"(P %"v125", L %"v131");
    %"chk28" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk28" + 0] <- %"v132";
    %"chk29" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v138" : L = Ptoi %"v137";
    %"v139" : L = Ptoi #0;
    %"v140" : W = (Cmp Eq L) %"v138", %"v139"
    => br %"v140" ? "L133" : "L134";
  @"L133":
    => ret #4294967295;
  @"L134":
    %"chk30" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk29";
    call %"v150" : W = $"__GI_strcmp"(P %"v147", P %"v149");
    %"v151" : W = (Cmp Eq W) %"v150", #0
    => br %"v151" ? "L143" : "L144";
  @"L143":
    %"chk32" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk32";
    call void $"free"(P %"v153")
    => goto "L145";
  @"L144":
    %"v155" : W = Or %"v104", #1
    => goto "L145";
  @"L145" [%"pr.7" : W = phi("L143" => %"v104", "L144" => %"v155")]:
    => goto "L25";
  @"L25" [%"pr.12" : W = phi("L23" => #0, "L145" => %"pr.7", "L115" => %"v104", "L37" => %"pr.13"); %"pr.1" : P = phi("L23" => %"v34", "L145" => %"pr.5", "L115" => %"pr.5", "L37" => %"pr.2")]:
    %"chk33" : A = (Check 0 1 Read 1) %"pr.1";
    %"v161" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v162" : W = (Cmp Eq W) %"v161", #64
    => br %"v162" ? "L156" : "L158";
  @"L156":
    %"chk34" : A = (Renew 0 1 Write 1) %"chk33", %"pr.1";
    store Wb [%"chk34" + 0] <- #0;
    %"v167" = %"pr.1" +p #1;
    %"chk35" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk35" + 0] <- %"v167";
    %"chk36" : A = (HalfCheck Upper 0 1 Read 1) %"chk33", %"v167";
    %"v173" : W = (RawLoad (LdNarrow Sb) 0) %"chk36";
    %"v174" : W = (Cmp Ne W) %"v173", #0
    => br %"v174" ? "L168" : "L158";
  @"L168":
    %"v176" : W = Or %"pr.12", #8
    => goto "L158";
  @"L158" [%"pr.8" : W = phi("L168" => %"v176", "L156" => %"pr.12", "L25" => %"pr.12")]:
    %"chk37" : A = (Renew 0 8 Read 8) %"chk1", %"v6";
    %"v181" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v182" : L = Ptoi %"v181";
    %"v183" : L = Ptoi #0;
    %"v184" : W = (Cmp Ne L) %"v182", %"v183"
    => br %"v184" ? "L185" : "L186";
  @"L185":
    %"v188" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"chk39" : A = (Check 0 1 Read 1) %"v188";
    %"v190" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    %"v191" : W = (Cmp Eq W) %"v190", #0
    => goto "L186";
  @"L186" [%"v193" : W = phi("L158" => #0, "L185" => %"v191")]:
    => br %"v193" ? "L177" : "L179";
  @"L177":
    %"v196" : W = And %"pr.8", #4294967291
    => goto "L179";
  @"L179" [%"pr.10" : W = phi("L177" => %"v196", "L186" => %"pr.8")]:
    %"chk40" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v201" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v202" : L = Ptoi %"v201";
    %"v204" : W = (Cmp Ne L) %"v202", %"v183"
    => br %"v204" ? "L205" : "L206";
  @"L205":
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk42" : A = (Check 0 1 Read 1) %"v208";
    %"v210" : W = (RawLoad (LdNarrow Sb) 0) %"chk42";
    %"v211" : W = (Cmp Eq W) %"v210", #0
    => goto "L206";
  @"L206" [%"v213" : W = phi("L179" => #0, "L205" => %"v211")]:
    => br %"v213" ? "L197" : "L199";
  @"L197":
    %"v216" : W = And %"pr.10", #4294967293
    => goto "L199";
  @"L199" [%"pr.11" : W = phi("L197" => %"v216", "L206" => %"pr.10")]:
    => ret %"pr.11"
} }.

Definition hello_image_fn__nl_find_domain : func :=
  ir_fn{ "export" "_nl_find_domain"(P %"v0", P %"v2", P %"v4", P %"v6") -> (RClass P) {
  @"start":
    %"v9" : P = (Alloc 8) #8;
    %"v10" : P = (Alloc 8) #8;
    %"v11" : P = (Alloc 8) #8;
    %"v12" : P = (Alloc 8) #8;
    %"v13" : P = (Alloc 8) #8;
    %"v16" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v17" : W = $"__GI___pthread_rwlock_rdlock"(P %"v16");
    %"v18" : P = Copy $"glibc_finddomain#_nl_loaded_domains";
    call %"v21" : L = $"__GI_strlen"(P %"v0");
    %"v22" : L = Add %"v21", #1;
    call %"v25" : P = $"_nl_make_l10nflist"(P %"v18", P %"v0", L %"v22", W #0, P %"v2", P #0, P #0, P #0, P #0, P %"v4", W #0);
    %"v26" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v27" : W = $"__GI___pthread_rwlock_unlock"(P %"v26");
    %"v32" : L = Ptoi %"v25";
    %"v33" : L = Ptoi #0;
    %"v34" : W = (Cmp Ne L) %"v32", %"v33"
    => br %"v34" ? "L28" : "L30";
  @"L28":
    %"v40" = %"v25" +p #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v40";
    %"v41" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v42" : W = (Cmp Sle W) %"v41", #0
    => br %"v42" ? "L36" : "L38";
  @"L36":
    call void $"_nl_load_domain"(P %"v25", P %"v6")
    => goto "L38";
  @"L38":
    %"v49" = %"v25" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v51" : L = Ptoi %"v50";
    %"v53" : W = (Cmp Ne L) %"v51", %"v33"
    => br %"v53" ? "L45" : "L56";
  @"L45":
    => ret %"v25";
  @"L56" [%"pr.3" : W = phi("L58" => %"v108", "L38" => #0)]:
    %"v61" = %"v25" +p #32;
    %"v63" : L = (Ext Sw) %"pr.3";
    %"v64" : L = Shl %"v63", #3;
    %"v65" = %"v61" +p %"v64";
    %"chk2" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v67" : L = Ptoi %"v66";
    %"v69" : W = (Cmp Ne L) %"v67", %"v33"
    => br %"v69" ? "L57" : "L59";
  @"L57":
    %"v74" = %"v25" +p #32;
    %"v78" = %"v74" +p %"v64";
    %"chk3" : A = (Check 0 8 Read 8) %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v80" = %"v79" +p #8;
    %"chk4" : A = (Check 0 4 Read 1) %"v80";
    %"v81" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v82" : W = (Cmp Sle W) %"v81", #0
    => br %"v82" ? "L70" : "L72";
  @"L70":
    %"v84" = %"v25" +p #32;
    %"v88" = %"v84" +p %"v64";
    %"chk5" : A = (Check 0 8 Read 8) %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call void $"_nl_load_domain"(P %"v89", P %"v6")
    => goto "L72";
  @"L72":
    %"v95" = %"v25" +p #32;
    %"v99" = %"v95" +p %"v64";
    %"chk6" : A = (Check 0 8 Read 8) %"v99";
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v101" = %"v100" +p #16;
    %"chk7" : A = (Check 0 8 Read 8) %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v103" : L = Ptoi %"v102";
    %"v105" : W = (Cmp Ne L) %"v103", %"v33"
    => br %"v105" ? "L59" : "L58";
  @"L58":
    %"v108" : W = Add %"pr.3", #1
    => goto poll "L56";
  @"L59":
    => ret %"v25";
  @"L30":
    call %"v112" : P = $"_nl_expand_alias"(P %"v2");
    %"v117" : L = Ptoi %"v112";
    %"v119" : W = (Cmp Ne L) %"v117", %"v33"
    => br %"v119" ? "L113" : "L115";
  @"L113":
    call %"v122" : L = $"__GI_strlen"(P %"v112");
    %"v123" : L = Add %"v122", #1;
    call %"v125" : P = $"malloc"(L %"v123");
    %"v130" : L = Ptoi %"v125";
    %"v132" : W = (Cmp Eq L) %"v130", %"v33"
    => br %"v132" ? "L126" : "L128";
  @"L126":
    => ret #0;
  @"L128":
    call %"v137" : P = $"__GI_memcpy"(P %"v125", P %"v112", L %"v123")
    => goto "L115";
  @"L115" [%"pr.1" : P = phi("L128" => %"v125", "L30" => %"v2")]:
    call %"v139" : W = $"_nl_explode_name"(P %"pr.1", P %"v9", P %"v10", P %"v11", P %"v12", P %"v13");
    %"v145" : W = (Cmp Ne W) %"v139", #4294967295
    => br %"v145" ? "L140" : "L142";
  @"L140":
    %"v146" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v147" : W = $"__GI___pthread_rwlock_wrlock"(P %"v146");
    %"v148" : P = Copy $"glibc_finddomain#_nl_loaded_domains";
    call %"v151" : L = $"__GI_strlen"(P %"v0");
    %"v152" : L = Add %"v151", #1;
    %"chk8" : A = (Check 0 8 Read 8) %"v9";
    %"v154" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"v11";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 8 Read 8) %"v12";
    %"v156" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Read 8) %"v13";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 8 Read 8) %"v10";
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk12";
    call %"v160" : P = $"_nl_make_l10nflist"(P %"v148", P %"v0", L %"v152", W %"v139", P %"v154", P %"v155", P %"v156", P %"v157", P %"v158", P %"v4", W #1);
    %"v161" : P = Copy $"glibc_finddomain#_nl_find_domain.lock.265";
    call %"v162" : W = $"__GI___pthread_rwlock_unlock"(P %"v161");
    %"v167" : L = Ptoi %"v160";
    %"v169" : W = (Cmp Ne L) %"v167", %"v33"
    => br %"v169" ? "L163" : "L165";
  @"L163":
    %"v174" = %"v160" +p #8;
    %"chk13" : A = (Check 0 4 Read 1) %"v174";
    %"v175" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v176" : W = (Cmp Sle W) %"v175", #0
    => br %"v176" ? "L170" : "L172";
  @"L170":
    call void $"_nl_load_domain"(P %"v160", P %"v6")
    => goto "L172";
  @"L172":
    %"v183" = %"v160" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v185" : L = Ptoi %"v184";
    %"v187" : W = (Cmp Eq L) %"v185", %"v33"
    => br %"v187" ? "L189" : "L165";
  @"L189" [%"pr.4" : W = phi("L191" => %"v241", "L172" => #0)]:
    %"v194" = %"v160" +p #32;
    %"v196" : L = (Ext Sw) %"pr.4";
    %"v197" : L = Shl %"v196", #3;
    %"v198" = %"v194" +p %"v197";
    %"chk15" : A = (Check 0 8 Read 8) %"v198";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v200" : L = Ptoi %"v199";
    %"v202" : W = (Cmp Ne L) %"v200", %"v33"
    => br %"v202" ? "L190" : "L165";
  @"L190":
    %"v207" = %"v160" +p #32;
    %"v211" = %"v207" +p %"v197";
    %"chk16" : A = (Check 0 8 Read 8) %"v211";
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v213" = %"v212" +p #8;
    %"chk17" : A = (Check 0 4 Read 1) %"v213";
    %"v214" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v215" : W = (Cmp Sle W) %"v214", #0
    => br %"v215" ? "L203" : "L205";
  @"L203":
    %"v217" = %"v160" +p #32;
    %"v221" = %"v217" +p %"v197";
    %"chk18" : A = (Check 0 8 Read 8) %"v221";
    %"v222" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call void $"_nl_load_domain"(P %"v222", P %"v6")
    => goto "L205";
  @"L205":
    %"v228" = %"v160" +p #32;
    %"v232" = %"v228" +p %"v197";
    %"chk19" : A = (Check 0 8 Read 8) %"v232";
    %"v233" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v234" = %"v233" +p #16;
    %"chk20" : A = (Check 0 8 Read 8) %"v234";
    %"v235" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v236" : L = Ptoi %"v235";
    %"v238" : W = (Cmp Ne L) %"v236", %"v33"
    => br %"v238" ? "L165" : "L191";
  @"L191":
    %"v241" : W = Add %"pr.4", #1
    => goto poll "L189";
  @"L165":
    %"v246" : W = And %"v139", #1
    => br %"v246" ? "L242" : "L142";
  @"L242":
    %"chk21" : A = (Renew 0 8 Read 8) %"chk11", %"v13";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call void $"free"(P %"v247")
    => goto "L142";
  @"L142" [%"pr.2" : P = phi("L242" => %"v160", "L165" => %"v160", "L115" => %"v25")]:
    => br %"v119" ? "L248" : "L250";
  @"L248":
    call void $"free"(P %"pr.1")
    => goto "L250";
  @"L250":
    => ret %"pr.2"
} }.

Definition hello_image_fn__nl_make_l10nflist : func :=
  ir_fn{ "export" "_nl_make_l10nflist"(P %"v0", P %"v2", L %"v4", W %"v6", P %"v8", P %"v10", P %"v12", P %"v14", P %"v16", P %"v18", W %"v20") -> (RClass P) {
  @"start":
    call %"v30" : L = $"__GI_strlen"(P %"v8");
    %"v31" : L = Add %"v4", %"v30";
    %"v36" : W = And %"v6", #4;
    %"v37" : W = (Cmp Ne W) %"v36", #0
    => br %"v37" ? "L32" : "L34";
  @"L32":
    call %"v39" : L = $"__GI_strlen"(P %"v10");
    %"v40" : L = Add %"v39", #1
    => goto "L34";
  @"L34" [%"v41" : L = phi("L32" => %"v40", "start" => #0)]:
    %"v42" : L = Add %"v31", %"v41";
    %"v47" : W = And %"v6", #2;
    %"v48" : W = (Cmp Ne W) %"v47", #0
    => br %"v48" ? "L43" : "L45";
  @"L43":
    call %"v50" : L = $"__GI_strlen"(P %"v12");
    %"v51" : L = Add %"v50", #1
    => goto "L45";
  @"L45" [%"v52" : L = phi("L43" => %"v51", "L34" => #0)]:
    %"v53" : L = Add %"v42", %"v52";
    %"v58" : W = And %"v6", #1
    => br %"v58" ? "L54" : "L56";
  @"L54":
    call %"v61" : L = $"__GI_strlen"(P %"v14");
    %"v62" : L = Add %"v61", #1
    => goto "L56";
  @"L56" [%"v63" : L = phi("L54" => %"v62", "L45" => #0)]:
    %"v64" : L = Add %"v53", %"v63";
    %"v69" : W = And %"v6", #8;
    %"v70" : W = (Cmp Ne W) %"v69", #0
    => br %"v70" ? "L65" : "L67";
  @"L65":
    call %"v72" : L = $"__GI_strlen"(P %"v16");
    %"v73" : L = Add %"v72", #1
    => goto "L67";
  @"L67" [%"v74" : L = phi("L65" => %"v73", "L56" => #0)]:
    %"v75" : L = Add %"v64", %"v74";
    %"v76" : L = Add %"v75", #1;
    call %"v78" : L = $"__GI_strlen"(P %"v18");
    %"v79" : L = Add %"v76", %"v78";
    %"v80" : L = Add %"v79", #1;
    call %"v81" : P = $"malloc"(L %"v80");
    %"v86" : L = Ptoi %"v81";
    %"v87" : L = Ptoi #0;
    %"v88" : W = (Cmp Eq L) %"v86", %"v87"
    => br %"v88" ? "L82" : "L84";
  @"L82":
    => ret #0;
  @"L84":
    call %"v93" : P = $"__GI_memcpy"(P %"v81", P %"v2", L %"v4");
    call void $"glibc_l10nflist#argz_stringify__"(P %"v81", L %"v4", W #58);
    %"v98" : L = Sub %"v4", #1;
    %"v99" = %"v81" +p %"v98";
    %"v101" = %"v99" +p #1;
    %"chk0" : A = (Check 0 1 Write 1) %"v99";
    store Wb [%"chk0" + 0] <- #47;
    call %"v104" : P = $"__GI_stpcpy"(P %"v101", P %"v8")
    => br %"v37" ? "L105" : "L107";
  @"L105":
    %"v112" = %"v104" +p #1;
    %"chk1" : A = (Check 0 1 Write 1) %"v104";
    store Wb [%"chk1" + 0] <- #95;
    call %"v115" : P = $"__GI_stpcpy"(P %"v112", P %"v10")
    => goto "L107";
  @"L107" [%"pr.5" : P = phi("L105" => %"v115", "L84" => %"v104")]:
    => br %"v48" ? "L116" : "L118";
  @"L116":
    %"v123" = %"pr.5" +p #1;
    %"chk2" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk2" + 0] <- #46;
    call %"v126" : P = $"__GI_stpcpy"(P %"v123", P %"v12")
    => goto "L118";
  @"L118" [%"pr.6" : P = phi("L116" => %"v126", "L107" => %"pr.5")]:
    => br %"v58" ? "L127" : "L129";
  @"L127":
    %"v134" = %"pr.6" +p #1;
    %"chk3" : A = (Check 0 1 Write 1) %"pr.6";
    store Wb [%"chk3" + 0] <- #46;
    call %"v137" : P = $"__GI_stpcpy"(P %"v134", P %"v14")
    => goto "L129";
  @"L129" [%"pr.7" : P = phi("L127" => %"v137", "L118" => %"pr.6")]:
    => br %"v70" ? "L138" : "L140";
  @"L138":
    %"v145" = %"pr.7" +p #1;
    %"chk4" : A = (Check 0 1 Write 1) %"pr.7";
    store Wb [%"chk4" + 0] <- #64;
    call %"v148" : P = $"__GI_stpcpy"(P %"v145", P %"v16")
    => goto "L140";
  @"L140" [%"pr.8" : P = phi("L138" => %"v148", "L129" => %"pr.7")]:
    %"v150" = %"pr.8" +p #1;
    %"chk5" : A = (Check 0 1 Write 1) %"pr.8";
    store Wb [%"chk5" + 0] <- #47;
    call %"v153" : P = $"__GI_stpcpy"(P %"v150", P %"v18");
    %"chk6" : A = (Check 0 8 Read 8) %"v0";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk6"
    => goto "L156";
  @"L156" [%"pr.3" : P = phi("L140" => %"v155", "L166" => %"v192"); %"pr.1" : P = phi("L140" => #0, "L166" => %"pr.2")]:
    %"v161" : L = Ptoi %"pr.3";
    %"v163" : W = (Cmp Ne L) %"v161", %"v87"
    => br %"v163" ? "L157" : "L159";
  @"L157":
    %"chk7" : A = (Check 0 8 Read 8) %"pr.3";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v169" : L = Ptoi %"v168";
    %"v171" : W = (Cmp Ne L) %"v169", %"v87"
    => br %"v171" ? "L164" : "L166";
  @"L164":
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call %"v176" : W = $"__GI_strcmp"(P %"v174", P %"v81");
    %"v181" : W = (Cmp Eq W) %"v176", #0
    => br %"v181" ? "L159" : "L179";
  @"L179":
    %"v187" : W = (Cmp Slt W) %"v176", #0
    => br %"v187" ? "L159" : "L166";
  @"L166" [%"pr.2" : P = phi("L179" => %"pr.3", "L157" => %"pr.1")]:
    %"v191" = %"pr.3" +p #24;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"v191";
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk9"
    => goto poll "L156";
  @"L159" [%"pr.4" : P = phi("L156" => %"pr.3", "L164" => %"pr.3", "L179" => #0)]:
    %"v197" : L = Ptoi %"pr.4";
    %"v199" : W = (Cmp Ne L) %"v197", %"v87"
    => br %"v199" ? "L201" : "L200";
  @"L200":
    %"v203" : W = (Cmp Eq W) %"v20", #0
    => goto "L201";
  @"L201" [%"v205" : W = phi("L159" => #1, "L200" => %"v203")]:
    => br %"v205" ? "L193" : "L195";
  @"L193":
    call void $"free"(P %"v81")
    => ret %"pr.4";
  @"L195":
    call %"v211" : L = $"glibc_l10nflist#argz_count__"(P %"v2", L %"v4");
    call %"v213" : W = $"glibc_l10nflist#pop"(W %"v6");
    %"v214" : W = Shl #1, %"v213";
    %"v215" : L = (Ext Sw) %"v214";
    %"v216" : L = Mul %"v211", %"v215";
    %"v217" : L = Shl %"v216", #3;
    %"v218" : L = Add %"v217", #40;
    call %"v219" : P = $"malloc"(L %"v218");
    %"v224" : L = Ptoi %"v219";
    %"v226" : W = (Cmp Eq L) %"v224", %"v87"
    => br %"v226" ? "L220" : "L222";
  @"L220":
    call void $"free"(P %"v81")
    => ret #0;
  @"L222":
    %"chk10" : A = (Check 0 8 Write 8) %"v219";
    store.ptr [%"chk10" + 0] <- %"v81";
    %"v232" = %"v219" +p #8;
    call %"v235" : L = $"glibc_l10nflist#argz_count__"(P %"v2", L %"v4");
    %"v236" : W = (Cmp Ne L) %"v235", #1
    => br %"v236" ? "L238" : "L237";
  @"L237":
    => br %"v48" ? "L242" : "L238";
  @"L242":
    => goto "L238";
  @"L238" [%"v250" : W = phi("L222" => #1, "L237" => #0, "L242" => %"v58")]:
    %"chk11" : A = (HalfCheck Upper 0 4 Write 1) %"chk10", %"v232";
    store Ww [%"chk11" + 0] <- %"v250";
    %"v252" = %"v219" +p #16;
    %"chk12" : A = (HalfCheck Upper 0 8 Write 8) %"chk10", %"v252";
    store.ptr [%"chk12" + 0] <- #0;
    %"v257" : L = Ptoi %"pr.1";
    %"v259" : W = (Cmp Eq L) %"v257", %"v87"
    => br %"v259" ? "L253" : "L254";
  @"L253":
    %"v261" = %"v219" +p #24;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk6", %"v0";
    %"v263" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (HalfCheck Upper 0 8 Write 8) %"chk10", %"v261";
    store.ptr [%"chk14" + 0] <- %"v263";
    %"chk15" : A = (Renew 0 8 Write 8) %"chk6", %"v0";
    store.ptr [%"chk15" + 0] <- %"v219"
    => goto "L255";
  @"L254":
    %"v267" = %"v219" +p #24;
    %"v269" = %"pr.1" +p #24;
    %"chk16" : A = (Check 0 8 Read 8) %"v269";
    %"v270" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk10", %"v267";
    store.ptr [%"chk17" + 0] <- %"v270";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk16", %"v269";
    store.ptr [%"chk18" + 0] <- %"v219"
    => goto "L255";
  @"L255":
    call %"v279" : L = $"glibc_l10nflist#argz_count__"(P %"v2", L %"v4");
    %"v280" : W = (Cmp Eq L) %"v279", #1
    => br %"v280" ? "L274" : "L285";
  @"L274":
    %"v282" : W = Sub %"v6", #1
    => goto "L285";
  @"L285" [%"pr.12" : W = phi("L293" => %"v330", "L274" => %"v282", "L255" => %"v6"); %"pr.9" : L = phi("L293" => %"pr.10", "L274" => #0, "L255" => #0)]:
    %"v290" : W = (Cmp Sge W) %"pr.12", #0
    => br %"v290" ? "L286" : "L288";
  @"L286":
    %"v296" : W = Xor %"v6", #(-1);
    %"v297" : W = And %"pr.12", %"v296";
    %"v298" : W = (Cmp Eq W) %"v297", #0
    => br %"v298" ? "L300" : "L293";
  @"L300" [%"pr.13" : P = phi("L301" => %"v306", "L286" => #0); %"pr.11" : L = phi("L301" => %"v313", "L286" => %"pr.9")]:
    call %"v306" : P = $"__GI___argz_next"(P %"v2", L %"v4", P %"pr.13");
    %"v307" : L = Ptoi %"v306";
    %"v309" : W = (Cmp Ne L) %"v307", %"v87"
    => br %"v309" ? "L301" : "L293";
  @"L301":
    %"v311" = %"v219" +p #32;
    %"v313" : L = Add %"pr.11", #1;
    %"v314" : L = Shl %"pr.11", #3;
    %"v315" = %"v311" +p %"v314";
    call %"v319" : L = $"__GI_strlen"(P %"v306");
    %"v320" : L = Add %"v319", #1;
    call %"v328" : P = $"_nl_make_l10nflist"(P %"v0", P %"v306", L %"v320", W %"pr.12", P %"v8", P %"v10", P %"v12", P %"v14", P %"v16", P %"v18", W #1);
    %"chk19" : A = (Check 0 8 Write 8) %"v315";
    store.ptr [%"chk19" + 0] <- %"v328"
    => goto poll "L300";
  @"L293" [%"pr.10" : L = phi("L300" => %"pr.11", "L286" => %"pr.9")]:
    %"v330" : W = Sub %"pr.12", #1
    => goto poll "L285";
  @"L288":
    %"v332" = %"v219" +p #32;
    %"v334" : L = Shl %"pr.9", #3;
    %"v335" = %"v332" +p %"v334";
    %"chk20" : A = (Check 0 8 Write 8) %"v335";
    store.ptr [%"chk20" + 0] <- #0
    => ret %"v219"
} }.

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

Definition hello_image_fn___GI__IO_wfile_underflow : func :=
  ir_fn{ "export" "__GI__IO_wfile_underflow"(P %"v0") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v61" : P = (Alloc 8) #8;
    %"v437" : P = (Alloc 8) #8;
    %"v438" : P = (Alloc 4) #16;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = And %"v9", #16
    => br %"v10" ? "L5" : "L7" };
  ir_blk{ @"L5":
    => ret #4294967295 };
  ir_blk{ @"L7":
    %"v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v17" : W = And %"v16", #4;
    %"v18" : L = (Ext Sw) %"v17";
    %"v19" : W = (Cmp Ne L) %"v18", #0
    => br %"v19" ? "L12" : "L14" };
  ir_blk{ @"L12":
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v22" : W = Or %"v21", #32;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk3" + 0] <- %"v22";
    %"v23" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v23";
    store Ww [%"chk4" + 0] <- #9
    => ret #4294967295 };
  ir_blk{ @"L14":
    %"v29" = %"v0" +p #160;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v35" = %"v34" +p #8;
    %"chk8" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v37" : L = Ptoi %"v31";
    %"v38" : L = Ptoi %"v36";
    %"v39" : W = (Cmp Ult L) %"v37", %"v38"
    => br %"v39" ? "L25" : "L27" };
  ir_blk{ @"L25":
    %"v41" = %"v0" +p #160;
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk10" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 4 Read 1) %"v43";
    %"v44" : W = (RawLoad (LdNarrow Sw) 0) %"chk11"
    => ret %"v44" };
  ir_blk{ @"L27":
    %"v47" = %"v0" +p #152;
    %"v48" : P = (RawLoadPointer (-8) load_effects) %"chk5";
    %"v53" = %"v0" +p #8;
    %"v54" : P = (RawLoadPointer (-152) load_effects) %"chk5";
    %"v56" = %"v0" +p #16;
    %"v57" : P = (RawLoadPointer (-144) load_effects) %"chk5";
    %"v58" : L = Ptoi %"v54";
    %"v59" : L = Ptoi %"v57";
    %"v60" : W = (Cmp Ult L) %"v58", %"v59"
    => br %"v60" ? "L49" : "L50" };
  ir_blk{ @"L49":
    %"v63" = %"v0" +p #8;
    %"v64" : P = (RawLoadPointer (-152) load_effects) %"chk5";
    %"chk16" : A = (Check 0 8 Write 8) %"v61";
    store.ptr [%"chk16" + 0] <- %"v64";
    %"v66" = %"v0" +p #160;
    %"chk17" : A = (Renew 0 8 Read 8) %"chk5", %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v68" = %"v67" +p #96;
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v72" = %"v71" +p #88;
    %"chk19" : A = (Check 0 8 Read 1) %"v72";
    %"v73" : L = (RawLoad LdL 0) %"chk19";
    %"chk20" : A = (Check 0 8 Write 1) %"v68";
    store Wl [%"chk20" + 0] <- %"v73";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v77" = %"v76" +p #16;
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v84" = %"v83" +p #48;
    %"chk24" : A = (Check 0 8 Read 8) %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk25" : A = (Check 0 8 Write 8) %"v80";
    store.ptr [%"chk25" + 0] <- %"v85";
    %"chk26" : A = (Check 0 8 Write 8) %"v77";
    store.ptr [%"chk26" + 0] <- %"v85";
    %"chk27" : A = (Renew 0 8 Read 8) %"chk5", %"v66";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v90" = %"v89" +p #88;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v63";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v95" = %"v0" +p #16;
    %"v96" : P = (RawLoadPointer 8 load_effects) %"chk28";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk31" : A = (Check 0 8 Read 8) %"v99";
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v104" = %"v103" +p #56;
    %"chk33" : A = (Check 0 8 Read 8) %"v104";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v109" = %"v108" +p #8;
    call %"v110" : W = $"__libio_codecvt_in"(P %"v48", P %"v90", P %"v93", P %"v96", P %"v61", P %"v100", P %"v105", P %"v109");
    %"v112" = %"v0" +p #24;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk28", %"v63";
    %"v115" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v112";
    store.ptr [%"chk36" + 0] <- %"v115";
    %"chk37" : A = (Renew 0 8 Read 8) %"chk16", %"v61";
    %"v118" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"chk38" : A = (Renew 0 8 Write 8) %"chk28", %"v63";
    store.ptr [%"chk38" + 0] <- %"v118";
    %"chk39" : A = (Renew 0 8 Read 8) %"chk5", %"v66";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"chk40" : A = (Check 0 8 Read 8) %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v129" = %"v128" +p #8;
    %"chk42" : A = (Check 0 8 Read 8) %"v129";
    %"v130" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v131" : L = Ptoi %"v125";
    %"v132" : L = Ptoi %"v130";
    %"v133" : W = (Cmp Ult L) %"v131", %"v132"
    => br %"v133" ? "L119" : "L121" };
  ir_blk{ @"L119":
    %"v135" = %"v0" +p #160;
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"chk44" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 4 Read 1) %"v137";
    %"v138" : W = (RawLoad (LdNarrow Sw) 0) %"chk45"
    => ret %"v138" };
  ir_blk{ @"L121":
    %"v144" : W = (Cmp Eq W) %"v110", #2
    => br %"v144" ? "L140" : "L142" };
  ir_blk{ @"L140":
    %"v145" : P = Copy $"__libc_errno";
    %"chk46" : A = (Check 0 4 Write 1) %"v145";
    store Ww [%"chk46" + 0] <- #84;
    %"chk47" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v147" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"v148" : W = Or %"v147", #32;
    %"chk48" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk48" + 0] <- %"v148"
    => ret #4294967295 };
  ir_blk{ @"L142":
    %"v151" = %"v0" +p #56;
    %"chk49" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v151";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v154" = %"v0" +p #8;
    %"chk50" : A = (Renew 0 8 Read 8) %"chk28", %"v154";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v157" = %"v0" +p #16;
    %"v158" : P = (RawLoadPointer 8 load_effects) %"chk50";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v162" : L = Ptoi %"v158";
    %"v163" : L = Ptoi %"v161";
    %"v164" : L = Sub %"v162", %"v163";
    call %"v165" : P = $"__GI_memmove"(P %"v152", P %"v155", L %"v164");
    %"chk53" : A = (Renew 0 8 Read 8) %"chk49", %"v151";
    %"v170" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"chk54" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v157";
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"chk55" : A = (Renew 0 8 Read 8) %"chk28", %"v154";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v177" : L = Ptoi %"v173";
    %"v178" : L = Ptoi %"v176";
    %"v179" : L = Sub %"v177", %"v178";
    %"v180" = %"v170" +p %"v179";
    %"chk56" : A = (Renew 0 8 Write 8) %"chk54", %"v157";
    store.ptr [%"chk56" + 0] <- %"v180";
    %"v182" = %"v0" +p #24;
    %"chk57" : A = (Renew 0 8 Read 8) %"chk49", %"v151";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"chk58" : A = (Renew 0 8 Write 8) %"chk28", %"v154";
    store.ptr [%"chk58" + 0] <- %"v187";
    %"chk59" : A = (Renew 0 8 Write 8) %"chk36", %"v182";
    store.ptr [%"chk59" + 0] <- %"v187"
    => goto "L51" };
  ir_blk{ @"L50":
    %"v189" = %"v0" +p #24;
    %"v191" = %"v0" +p #8;
    %"v193" = %"v0" +p #16;
    %"v195" = %"v0" +p #56;
    %"v196" : P = (RawLoadPointer (-104) load_effects) %"chk5";
    %"chk61" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v193";
    store.ptr [%"chk61" + 0] <- %"v196";
    %"chk62" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v191";
    store.ptr [%"chk62" + 0] <- %"v196";
    %"chk63" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v189";
    store.ptr [%"chk63" + 0] <- %"v196"
    => goto "L51" };
  ir_blk{ @"L51":
    %"v201" = %"v0" +p #56;
    %"chk64" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v203" : L = Ptoi %"v202";
    %"v204" : L = Ptoi #0;
    %"v205" : W = (Cmp Eq L) %"v203", %"v204"
    => br %"v205" ? "L197" : "L199" };
  ir_blk{ @"L197":
    %"v210" = %"v0" +p #72;
    %"chk65" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v210";
    %"v211" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v212" : L = Ptoi %"v211";
    %"v214" : W = (Cmp Ne L) %"v212", %"v204"
    => br %"v214" ? "L206" : "L208" };
  ir_blk{ @"L206":
    %"v217" = %"v0" +p #72;
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v218";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join" };
  ir_blk{ @"iw_1.L4":
    call void $"free"(P %"v218")
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join":
    %"chk67" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v220" : W = (RawLoad (LdNarrow Sw) 0) %"chk67";
    %"v222" : W = And %"v220", #4294967039;
    %"chk68" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk68" + 0] <- %"v222"
    => goto "L208" };
  ir_blk{ @"L208":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v225" = %"v0" +p #24;
    %"v227" = %"v0" +p #8;
    %"v229" = %"v0" +p #16;
    %"v231" = %"v0" +p #56;
    %"chk69" : A = (Renew 0 8 Read 8) %"chk64", %"v231";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"chk70" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v229";
    store.ptr [%"chk70" + 0] <- %"v232";
    %"chk71" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v227";
    store.ptr [%"chk71" + 0] <- %"v232";
    %"chk72" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v225";
    store.ptr [%"chk72" + 0] <- %"v232"
    => goto "L199" };
  ir_blk{ @"L199":
    %"v234" = %"v0" +p #32;
    %"v236" = %"v0" +p #40;
    %"v238" = %"v0" +p #48;
    %"v240" = %"v0" +p #56;
    %"chk73" : A = (Renew 0 8 Read 8) %"chk64", %"v240";
    %"v241" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"chk74" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v238";
    store.ptr [%"chk74" + 0] <- %"v241";
    %"chk75" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v236";
    store.ptr [%"chk75" + 0] <- %"v241";
    %"chk76" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v234";
    store.ptr [%"chk76" + 0] <- %"v241";
    %"v246" = %"v0" +p #160;
    %"chk77" : A = (Renew 0 8 Read 8) %"chk5", %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"v248" = %"v247" +p #48;
    %"chk78" : A = (Check 0 8 Read 8) %"v248";
    %"v249" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v250" : L = Ptoi %"v249";
    %"v252" : W = (Cmp Eq L) %"v250", %"v204"
    => br %"v252" ? "L242" : "L244" };
  ir_blk{ @"L242":
    %"v257" = %"v0" +p #160;
    %"v258" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"v259" = %"v258" +p #64;
    %"chk80" : A = (Check 0 8 Read 8) %"v259";
    %"v260" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"v261" : L = Ptoi %"v260";
    %"v263" : W = (Cmp Ne L) %"v261", %"v204"
    => br %"v263" ? "L253" : "L255" };
  ir_blk{ @"L253":
    %"v265" = %"v0" +p #160;
    %"v266" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"v267" = %"v266" +p #64;
    %"chk82" : A = (Check 0 8 Read 8) %"v267";
    %"v268" : P = (RawLoadPointer 0 load_effects) %"chk82";
    call void $"free"(P %"v268");
    %"chk83" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v270" : W = (RawLoad (LdNarrow Sw) 0) %"chk83";
    %"v272" : W = And %"v270", #4294967039;
    %"chk84" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk84" + 0] <- %"v272"
    => goto "L255" };
  ir_blk{ @"L255":
    call void $"__GI__IO_wdoallocbuf"(P %"v0")
    => goto "L244" };
  ir_blk{ @"L244":
    %"chk85" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v278" : W = (RawLoad (LdNarrow Sw) 0) %"chk85";
    %"v280" : W = And %"v278", #514
    => br %"v280" ? "L281" : "L276" };
  ir_blk{ @"L281":
    %"v285" : P = Copy $"stdout";
    %"chk86" : A = (Check 0 8 Read 8) %"v285";
    %"v286" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"chk87" : A = (Check 0 4 Read 1) %"v286";
    %"v291" : W = (RawLoad (LdNarrow Sw) 0) %"chk87";
    %"v292" : W = And %"v291", #32768;
    %"v293" : W = (Cmp Eq W) %"v292", #0
    => br %"v293" ? "L294" : "L289" };
  ir_blk{ @"L294":
    call %"v298" : P = $"zthread_self_cookie"();
    %"v302" : P = Copy $"__libc_single_threaded_internal";
    %"chk88" : A = (Check 0 1 Read 1) %"v302";
    %"v303" : W = (RawLoad (LdNarrow Sb) 0) %"chk88";
    %"v304" : W = (Cmp Ne W) %"v303", #0
    => br %"v304" ? "L305" : "L306" };
  ir_blk{ @"L305":
    %"v308" = %"v286" +p #136;
    %"chk89" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"v308";
    %"v309" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"v310" = %"v309" +p #8;
    %"chk90" : A = (Check 0 8 Read 8) %"v310";
    %"v311" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"v312" : L = Ptoi %"v311";
    %"v314" : W = (Cmp Eq L) %"v312", %"v204"
    => goto "L306" };
  ir_blk{ @"L306" [%"v316" : W = phi("L294" => #0, "L305" => %"v314")]:
    => br %"v316" ? "L299" : "L300" };
  ir_blk{ @"L299":
    %"v318" = %"v286" +p #136;
    %"chk91" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"v318";
    %"v319" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"chk92" : A = (Check 0 4 Write 1) %"v319";
    store Ww [%"chk92" + 0] <- #1;
    %"v322" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"v323" = %"v322" +p #8;
    %"chk94" : A = (Check 0 8 Write 8) %"v323";
    store.ptr [%"chk94" + 0] <- %"v298"
    => goto "L289" };
  ir_blk{ @"L300":
    %"v329" = %"v286" +p #136;
    %"chk95" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"v329";
    %"v330" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v331" = %"v330" +p #8;
    %"chk96" : A = (Check 0 8 Read 8) %"v331";
    %"v332" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"v334" : L = Ptoi %"v332";
    %"v335" : L = Ptoi %"v298";
    %"v336" : W = (Cmp Ne L) %"v334", %"v335"
    => br %"v336" ? "L325" : "L326" };
  ir_blk{ @"L325":
    %"v339" = %"v286" +p #136;
    %"v340" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"chk98" : A = (Check 0 4 Write 4) %"v340";
    %"v347" : W = (RawCas (CasNarrow Sw) 0) %"chk98", #0, #1;
    %"v348" : W = (Cmp Eq W) %"v347", #0
    => br %"v348" ? "L350" : "L349" };
  ir_blk{ @"L349":
    => goto "L350" };
  ir_blk{ @"L350":
    %"v351" : W = (Cmp Ne W) %"v347", #0
    => br %"v351" ? "L354" : "L343" };
  ir_blk{ @"L354":
    call void $"__GI___lll_lock_wait_private"(P %"v340")
    => goto "L343" };
  ir_blk{ @"L343":
    %"v365" = %"v286" +p #136;
    %"chk99" : A = (Renew 0 8 Read 8) %"chk95", %"v365";
    %"v366" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"v367" = %"v366" +p #8;
    %"chk100" : A = (Check 0 8 Write 8) %"v367";
    store.ptr [%"chk100" + 0] <- %"v298"
    => goto "L289" };
  ir_blk{ @"L326":
    %"v370" = %"v286" +p #136;
    %"v371" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v372" = %"v371" +p #4;
    %"chk102" : A = (Check 0 4 Read 1) %"v372";
    %"v373" : W = (RawLoad (LdNarrow Sw) 0) %"chk102";
    %"v374" : W = Add %"v373", #1;
    %"chk103" : A = (Renew 0 4 Write 1) %"chk102", %"v372";
    store Ww [%"chk103" + 0] <- %"v374"
    => goto "L289" };
  ir_blk{ @"L289":
    %"v378" : P = Copy $"stdout";
    %"chk104" : A = (Check 0 8 Read 8) %"v378";
    %"v379" : P = (RawLoadPointer 0 load_effects) %"chk104";
    %"chk105" : A = (Check 0 4 Read 1) %"v379";
    %"v380" : W = (RawLoad (LdNarrow Sw) 0) %"chk105";
    %"v383" : W = And %"v380", #648;
    %"v385" : W = (Cmp Eq W) %"v383", #640
    => br %"v385" ? "L375" : "iw_3.start" };
  ir_blk{ @"L375":
    %"v386" : P = Copy $"stdout";
    %"chk106" : A = (Check 0 8 Read 8) %"v386";
    %"v387" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"v388" = %"v387" +p #216;
    %"chk107" : A = (Check 0 8 Read 8) %"v388";
    %"v389" : P = (RawLoadPointer 0 load_effects) %"chk107";
    %"iw_2.v4" : L = Ptoi %"v389";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join" };
  ir_blk{ @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"v391" = %"v389" +p #24;
    %"chk108" : A = (Check 0 8 Read 8) %"v391";
    %"v392" : P = (RawLoadPointer 0 load_effects) %"chk108";
    %"v393" : P = Copy $"stdout";
    %"chk109" : A = (Check 0 8 Read 8) %"v393";
    %"v394" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"chk110" : F = CheckFunction %"v392";
    rawcall %"v396" : W = %"chk110"(P %"v394", W #4294967295)
    => goto "iw_3.start" };
  ir_blk{ @"iw_3.start":
    %"chk111" : A = (Renew 0 4 Read 1) %"chk87", %"v286";
    %"iw_3.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk111";
    %"iw_3.v10" : W = And %"iw_3.v9", #32768;
    %"iw_3.v11" : W = (Cmp Eq W) %"iw_3.v10", #0
    => br %"iw_3.v11" ? "iw_3.L5" : "L276" };
  ir_blk{ @"iw_3.L5":
    %"iw_3.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk111";
    %"iw_3.v17" : W = And %"iw_3.v16", #32768;
    %"iw_3.v18" : W = (Cmp Eq W) %"iw_3.v17", #0
    => br %"iw_3.v18" ? "iw_3.L19" : "L276" };
  ir_blk{ @"iw_3.L19":
    %"iw_3.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk113" : A = (Check 0 1 Read 1) %"iw_3.v25";
    %"iw_3.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk113";
    %"iw_3.v27" : W = (Cmp Ne W) %"iw_3.v26", #0
    => br %"iw_3.v27" ? "iw_3.L28" : "iw_3.L29" };
  ir_blk{ @"iw_3.L28":
    %"iw_3.v31" = %"v286" +p #136;
    %"chk114" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"iw_3.v31";
    %"iw_3.v32" : P = (RawLoadPointer 0 load_effects) %"chk114";
    %"iw_3.v33" = %"iw_3.v32" +p #4;
    %"chk115" : A = (Check 0 4 Read 1) %"iw_3.v33";
    %"iw_3.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk115";
    %"iw_3.v35" : W = (Cmp Eq W) %"iw_3.v34", #0
    => goto "iw_3.L29" };
  ir_blk{ @"iw_3.L29" [%"iw_3.v37" : W = phi("iw_3.L19" => #0, "iw_3.L28" => %"iw_3.v35")]:
    => br %"iw_3.v37" ? "iw_3.L22" : "iw_3.L23" }] [ir_blk{ @"iw_3.L22":
    %"iw_3.v39" = %"v286" +p #136;
    %"chk116" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"iw_3.v39";
    %"iw_3.v40" : P = (RawLoadPointer 0 load_effects) %"chk116";
    %"iw_3.v41" = %"iw_3.v40" +p #8;
    %"chk117" : A = (Check 0 8 Write 8) %"iw_3.v41";
    store.ptr [%"chk117" + 0] <- #0;
    %"chk118" : A = (Renew 0 8 Read 8) %"chk116", %"iw_3.v39";
    %"iw_3.v44" : P = (RawLoadPointer 0 load_effects) %"chk118";
    %"chk119" : A = (Check 0 4 Write 1) %"iw_3.v44";
    store Ww [%"chk119" + 0] <- #0
    => goto "L276" };
  ir_blk{ @"iw_3.L23":
    %"iw_3.v49" = %"v286" +p #136;
    %"chk120" : A = (HalfCheck Upper 0 8 Read 8) %"chk87", %"iw_3.v49";
    %"iw_3.v50" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_3.v51" = %"iw_3.v50" +p #4;
    %"chk121" : A = (Check 0 4 Read 1) %"iw_3.v51";
    %"iw_3.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk121";
    %"iw_3.v53" : W = (Cmp Eq W) %"iw_3.v52", #0
    => br %"iw_3.v53" ? "iw_3.L45" : "iw_3.L46" };
  ir_blk{ @"iw_3.L45":
    %"iw_3.v55" = %"v286" +p #136;
    %"iw_3.v56" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_3.v57" = %"iw_3.v56" +p #8;
    %"chk123" : A = (Check 0 8 Write 8) %"iw_3.v57";
    store.ptr [%"chk123" + 0] <- #0;
    %"chk124" : A = (Renew 0 8 Read 8) %"chk120", %"iw_3.v55";
    %"iw_3.v61" : P = (RawLoadPointer 0 load_effects) %"chk124";
    %"chk125" : A = (Check 0 4 Read 1) %"iw_3.v61";
    %"iw_3.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk125"
    => goto "iw_3.L66" };
  ir_blk{ @"iw_3.L66" [%"iw_3.v68" : W = phi("iw_3.L45" => %"iw_3.v65", "iw_3.L66" => %"iw_3.v69")]:
    %"chk126" : A = (HalfCheck Lower 0 4 Write 4) %"chk125", %"iw_3.v61";
    %"iw_3.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk126", %"iw_3.v68", #0;
    %"iw_3.v70" : W = (Cmp Eq W) %"iw_3.v69", %"iw_3.v68"
    => br %"iw_3.v70" ? "iw_3.L67" : poll "iw_3.L66" };
  ir_blk{ @"iw_3.L67":
    %"iw_3.v75" : W = (Cmp Sgt W) %"iw_3.v68", #1
    => br %"iw_3.v75" ? "iw_3.L78" : "L276" };
  ir_blk{ @"iw_3.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_3.v61")
    => goto "L276" };
  ir_blk{ @"iw_3.L46":
    %"iw_3.v90" = %"v286" +p #136;
    %"iw_3.v91" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_3.v92" = %"iw_3.v91" +p #4;
    %"chk128" : A = (Check 0 4 Read 1) %"iw_3.v92";
    %"iw_3.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk128";
    %"iw_3.v94" : W = Sub %"iw_3.v93", #1;
    %"chk129" : A = (Renew 0 4 Write 1) %"chk128", %"iw_3.v92";
    store Ww [%"chk129" + 0] <- %"iw_3.v94"
    => goto "L276" };
  ir_blk{ @"L276":
    call %"v398" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v400" = %"v0" +p #160;
    %"chk130" : A = (Renew 0 8 Read 8) %"chk5", %"v400";
    %"v401" : P = (RawLoadPointer 0 load_effects) %"chk130";
    %"v402" = %"v401" +p #16;
    %"v405" : P = (RawLoadPointer 0 load_effects) %"chk130";
    %"v408" : P = (RawLoadPointer 0 load_effects) %"chk130";
    %"v409" = %"v408" +p #48;
    %"chk133" : A = (Check 0 8 Read 8) %"v409";
    %"v410" : P = (RawLoadPointer 0 load_effects) %"chk133";
    %"chk134" : A = (Check 0 8 Write 8) %"v405";
    store.ptr [%"chk134" + 0] <- %"v410";
    %"chk135" : A = (Check 0 8 Write 8) %"v402";
    store.ptr [%"chk135" + 0] <- %"v410";
    %"chk136" : A = (Renew 0 8 Read 8) %"chk5", %"v400";
    %"v413" : P = (RawLoadPointer 0 load_effects) %"chk136";
    %"v414" = %"v413" +p #8;
    %"v417" : P = (RawLoadPointer 0 load_effects) %"chk136";
    %"v418" = %"v417" +p #48;
    %"chk138" : A = (Check 0 8 Read 8) %"v418";
    %"v419" : P = (RawLoadPointer 0 load_effects) %"chk138";
    %"chk139" : A = (Check 0 8 Write 8) %"v414";
    store.ptr [%"chk139" + 0] <- %"v419";
    %"chk140" : A = (Renew 0 8 Read 8) %"chk5", %"v400";
    %"v422" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v423" = %"v422" +p #24;
    %"v426" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v427" = %"v426" +p #32;
    %"v430" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v431" = %"v430" +p #40;
    %"v434" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"v435" = %"v434" +p #48;
    %"chk144" : A = (Check 0 8 Read 8) %"v435";
    %"v436" : P = (RawLoadPointer 0 load_effects) %"chk144";
    %"chk145" : A = (Check 0 8 Write 8) %"v431";
    store.ptr [%"chk145" + 0] <- %"v436";
    %"chk146" : A = (Check 0 8 Write 8) %"v427";
    store.ptr [%"chk146" + 0] <- %"v436";
    %"chk147" : A = (Check 0 8 Write 8) %"v423";
    store.ptr [%"chk147" + 0] <- %"v436"
    => goto "L440" };
  ir_blk{ @"L440" [%"pr.3" : L = phi("L276" => #0, "L662" => %"pr.5", "L665" => %"pr.4")]:
    %"v442" = %"v0" +p #216;
    %"chk148" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v442";
    %"v443" : P = (RawLoadPointer 0 load_effects) %"chk148";
    %"iw_4.v4" : L = Ptoi %"v443";
    %"iw_4.v7" : P = Copy $"__io_vtables";
    %"iw_4.v8" : L = Ptoi %"iw_4.v7";
    %"iw_4.v9" : L = Sub %"iw_4.v4", %"iw_4.v8";
    %"iw_4.v15" : W = (Cmp Uge L) %"iw_4.v9", #2352
    => br %"iw_4.v15" ? "iw_4.L10" : "iw_4.join" };
  ir_blk{ @"iw_4.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join":
    %"v445" = %"v443" +p #112;
    %"chk149" : A = (Check 0 8 Read 8) %"v445";
    %"v446" : P = (RawLoadPointer 0 load_effects) %"chk149";
    %"v449" = %"v0" +p #16;
    %"chk150" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v449";
    %"v450" : P = (RawLoadPointer 0 load_effects) %"chk150";
    %"v452" = %"v0" +p #64;
    %"chk151" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v452";
    %"v453" : P = (RawLoadPointer 0 load_effects) %"chk151";
    %"v456" : P = (RawLoadPointer 0 load_effects) %"chk150";
    %"v457" : L = Ptoi %"v453";
    %"v458" : L = Ptoi %"v456";
    %"v459" : L = Sub %"v457", %"v458";
    %"chk153" : F = CheckFunction %"v446";
    rawcall %"v460" : L = %"chk153"(P %"v0", P %"v450", L %"v459");
    %"v465" : W = (Cmp Sle L) %"v460", #0
    => br %"v465" ? "L461" : "L463" };
  ir_blk{ @"L461":
    %"v470" : W = (Cmp Eq L) %"v460", #0
    => br %"v470" ? "L471" : "L472" };
  ir_blk{ @"L471":
    %"v474" : W = (Cmp Eq L) %"pr.3", #0
    => goto "L472" };
  ir_blk{ @"L472" [%"v476" : W = phi("L461" => #0, "L471" => %"v474")]:
    => br %"v476" ? "L466" : "L467" };
  ir_blk{ @"L466":
    %"chk154" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v478" : W = (RawLoad (LdNarrow Sw) 0) %"chk154";
    %"v479" : W = Or %"v478", #16;
    %"chk155" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk155" + 0] <- %"v479";
    %"v481" = %"v0" +p #144;
    %"chk156" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v481";
    store Wl [%"chk156" + 0] <- #18446744073709551615
    => goto "L463" };
  ir_blk{ @"L467":
    %"chk157" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v485" : W = (RawLoad (LdNarrow Sw) 0) %"chk157";
    %"v486" : W = Or %"v485", #32;
    %"chk158" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk158" + 0] <- %"v486"
    => goto "L463" };
  ir_blk{ @"L463" [%"pr.1" : L = phi("L466" => %"v460", "L467" => #0, "iw_4.join" => %"v460")]:
    %"v488" = %"v0" +p #16;
    %"chk159" : A = (Renew 0 8 Read 8) %"chk150", %"v488";
    %"v489" : P = (RawLoadPointer 0 load_effects) %"chk159";
    %"v491" = %"v489" +p %"pr.1";
    %"chk160" : A = (Renew 0 8 Write 8) %"chk150", %"v488";
    store.ptr [%"chk160" + 0] <- %"v491";
    %"v496" : W = (Cmp Eq L) %"pr.1", #0
    => br %"v496" ? "L492" : "L494" };
  ir_blk{ @"L492":
    %"v501" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v501" ? "L497" : "L499" };
  ir_blk{ @"L497":
    %"v502" : P = Copy $"__libc_errno";
    %"chk161" : A = (Check 0 4 Write 1) %"v502";
    store Ww [%"chk161" + 0] <- #84
    => goto "L499" };
  ir_blk{ @"L499":
    => ret #4294967295 };
  ir_blk{ @"L494":
    %"v508" = %"v0" +p #144;
    %"chk162" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v508";
    %"v509" : L = (RawLoad LdL 0) %"chk162";
    %"v512" : W = (Cmp Ne L) %"v509", #18446744073709551615
    => br %"v512" ? "L504" : "L506" };
  ir_blk{ @"L504":
    %"v514" = %"v0" +p #144;
    %"v515" : L = (RawLoad LdL 0) %"chk162";
    %"v517" : L = Add %"v515", %"pr.1";
    %"chk164" : A = (Renew 0 8 Write 1) %"chk162", %"v514";
    store Wl [%"chk164" + 0] <- %"v517"
    => goto "L506" };
  ir_blk{ @"L506":
    %"v519" = %"v0" +p #160;
    %"chk165" : A = (Renew 0 8 Read 8) %"chk5", %"v519";
    %"v520" : P = (RawLoadPointer 0 load_effects) %"chk165";
    %"v521" = %"v520" +p #96;
    %"v524" : P = (RawLoadPointer 0 load_effects) %"chk165";
    %"v525" = %"v524" +p #88;
    %"chk167" : A = (Check 0 8 Read 1) %"v525";
    %"v526" : L = (RawLoad LdL 0) %"chk167";
    %"chk168" : A = (Check 0 8 Write 1) %"v521";
    store Wl [%"chk168" + 0] <- %"v526";
    %"v528" = %"v0" +p #24;
    %"v530" = %"v0" +p #8;
    %"chk169" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v530";
    %"v531" : P = (RawLoadPointer 0 load_effects) %"chk169";
    %"chk170" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v528";
    store.ptr [%"chk170" + 0] <- %"v531";
    %"chk171" : A = (Renew 0 8 Read 8) %"chk169", %"v530";
    %"v535" : P = (RawLoadPointer 0 load_effects) %"chk171";
    %"v538" = %"v0" +p #16;
    %"chk172" : A = (Renew 0 8 Read 8) %"chk150", %"v538";
    %"v539" : P = (RawLoadPointer 0 load_effects) %"chk172";
    %"v546" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v546" ? "L542" : "L544" };
  ir_blk{ @"L542":
    %"v553" : L = Sub #16, %"pr.3";
    %"v555" : W = (Cmp Ult L) %"v553", %"pr.1"
    => br %"v555" ? "L551" : "L550" };
  ir_blk{ @"L550":
    => goto "L551" };
  ir_blk{ @"L551" [%"v559" : L = phi("L550" => %"pr.1", "L542" => %"v553")]:
    %"v561" = %"v438" +p %"pr.3";
    call %"v564" : P = $"__GI_mempcpy"(P %"v561", P %"v535", L %"v559");
    %"v567" : L = Add %"pr.3", %"v559"
    => goto "L544" };
  ir_blk{ @"L544" [%"pr.9" : L = phi("L551" => %"v559", "L506" => %"pr.1"); %"pr.8" : P = phi("L551" => %"v564", "L506" => %"v539"); %"pr.7" : P = phi("L551" => %"v438", "L506" => %"v535"); %"pr.4" : L = phi("L551" => %"v567", "L506" => %"pr.3")]:
    %"v570" = %"v0" +p #160;
    %"chk173" : A = (Renew 0 8 Read 8) %"chk5", %"v570";
    %"v571" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v572" = %"v571" +p #88;
    %"v577" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v578" = %"v577" +p #8;
    %"chk175" : A = (Check 0 8 Read 8) %"v578";
    %"v579" : P = (RawLoadPointer 0 load_effects) %"chk175";
    %"v582" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v583" = %"v582" +p #56;
    %"chk177" : A = (Check 0 8 Read 8) %"v583";
    %"v584" : P = (RawLoadPointer 0 load_effects) %"chk177";
    %"v587" : P = (RawLoadPointer 0 load_effects) %"chk173";
    %"v588" = %"v587" +p #8;
    call %"v589" : W = $"__libio_codecvt_in"(P %"v48", P %"v572", P %"pr.7", P %"pr.8", P %"v437", P %"v579", P %"v584", P %"v588");
    %"v594" : W = (Cmp Ne L) %"pr.4", #0
    => br %"v594" ? "L590" : "L591" };
  ir_blk{ @"L590":
    %"v598" = %"v0" +p #8;
    %"chk179" : A = (Renew 0 8 Read 8) %"chk169", %"v598";
    %"v599" : P = (RawLoadPointer 0 load_effects) %"chk179";
    %"chk180" : A = (Check 0 8 Read 8) %"v437";
    %"v603" : P = (RawLoadPointer 0 load_effects) %"chk180";
    %"v606" : L = Sub %"pr.4", %"pr.9";
    %"v607" = %"v438" +p %"v606";
    %"v608" : L = Ptoi %"v603";
    %"v609" : L = Ptoi %"v607";
    %"v610" : L = Sub %"v608", %"v609";
    %"v611" : W = (Cmp Slt L) %"v610", #0
    => br %"v611" ? "L602" : "L601" };
  ir_blk{ @"L601":
    %"v612" : P = (RawLoadPointer 0 load_effects) %"chk180";
    %"v617" : L = Ptoi %"v612";
    %"v619" : L = Sub %"v617", %"v609"
    => goto "L602" };
  ir_blk{ @"L602" [%"v620" : L = phi("L601" => %"v619", "L590" => #0)]:
    %"v621" = %"v599" +p %"v620";
    %"chk182" : A = (Renew 0 8 Write 8) %"chk169", %"v598";
    store.ptr [%"chk182" + 0] <- %"v621"
    => goto "L592" };
  ir_blk{ @"L591":
    %"v623" = %"v0" +p #8;
    %"chk183" : A = (Check 0 8 Read 8) %"v437";
    %"v624" : P = (RawLoadPointer 0 load_effects) %"chk183";
    %"chk184" : A = (Renew 0 8 Write 8) %"chk169", %"v623";
    store.ptr [%"chk184" + 0] <- %"v624"
    => goto "L592" };
  ir_blk{ @"L592":
    %"v629" = %"v0" +p #160;
    %"chk185" : A = (Renew 0 8 Read 8) %"chk5", %"v629";
    %"v630" : P = (RawLoadPointer 0 load_effects) %"chk185";
    %"v631" = %"v630" +p #8;
    %"chk186" : A = (Check 0 8 Read 8) %"v631";
    %"v632" : P = (RawLoadPointer 0 load_effects) %"chk186";
    %"v635" : P = (RawLoadPointer 0 load_effects) %"chk185";
    %"v636" = %"v635" +p #48;
    %"chk188" : A = (Check 0 8 Read 8) %"v636";
    %"v637" : P = (RawLoadPointer 0 load_effects) %"chk188";
    %"v638" : L = Ptoi %"v632";
    %"v639" : L = Ptoi %"v637";
    %"v640" : W = (Cmp Eq L) %"v638", %"v639"
    => br %"v640" ? "L625" : "L627" };
  ir_blk{ @"L625":
    %"v645" : W = (Cmp Eq W) %"v589", #2
    => br %"v645" ? "L646" : "L643" };
  ir_blk{ @"L646":
    %"v647" : P = Copy $"__libc_errno";
    %"chk189" : A = (Check 0 4 Write 1) %"v647";
    store Ww [%"chk189" + 0] <- #84;
    %"chk190" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v649" : W = (RawLoad (LdNarrow Sw) 0) %"chk190";
    %"v650" : W = Or %"v649", #32;
    %"chk191" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk191" + 0] <- %"v650"
    => ret #4294967295 };
  ir_blk{ @"L643":
    %"v656" : W = (Cmp Eq W) %"v589", #1
    => br %"v656" ? "L654" : "L653" };
  ir_blk{ @"L653":
    %"v657" : P = Copy $"glibc_wfileops#str.254";
    %"v658" : P = Copy $"glibc_wfileops#str.255";
    %"v659" : P = Copy $"glibc_wfileops#str.256";
    call void $"__libc_assert_fail"(P %"v657", P %"v658", W #289, P %"v659")
    => goto "L654" };
  ir_blk{ @"L654":
    %"v664" : W = (Cmp Eq L) %"pr.4", #0
    => br %"v664" ? "L660" : "L661" };
  ir_blk{ @"L660":
    %"v669" = %"v0" +p #24;
    %"chk192" : A = (Renew 0 8 Read 8) %"chk170", %"v669";
    %"v670" : P = (RawLoadPointer 0 load_effects) %"chk192";
    %"v672" = %"v0" +p #8;
    %"chk193" : A = (Renew 0 8 Read 8) %"chk169", %"v672";
    %"v673" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"v674" : L = Ptoi %"v670";
    %"v675" : L = Ptoi %"v673";
    %"v676" : W = (Cmp Ult L) %"v674", %"v675"
    => br %"v676" ? "L665" : "L667" };
  ir_blk{ @"L665":
    %"v679" = %"v0" +p #16;
    %"v680" : P = (RawLoadPointer 8 load_effects) %"chk193";
    %"v682" = %"v0" +p #8;
    %"v683" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"v684" : L = Ptoi %"v680";
    %"v685" : L = Ptoi %"v683";
    %"v686" : L = Sub %"v684", %"v685";
    %"v688" = %"v0" +p #24;
    %"v689" : P = (RawLoadPointer 0 load_effects) %"chk192";
    %"v692" : P = (RawLoadPointer 0 load_effects) %"chk193";
    call %"v694" : P = $"__GI_memmove"(P %"v689", P %"v692", L %"v686");
    %"chk198" : A = (Renew 0 8 Read 8) %"chk170", %"v688";
    %"v699" : P = (RawLoadPointer 0 load_effects) %"chk198";
    %"chk199" : A = (Renew 0 8 Write 8) %"chk169", %"v682";
    store.ptr [%"chk199" + 0] <- %"v699";
    %"chk200" : A = (Renew 0 8 Read 8) %"chk150", %"v679";
    %"v702" : P = (RawLoadPointer 0 load_effects) %"chk200";
    (Flight (a "v704") Sub [(FAddress (t "v702")); (FValue (t "v686"))] (LowerOf (t "v702")));
    %"chk201" : A = (Renew 0 8 Write 8) %"chk150", %"v679";
    store.ptr [%"chk201" + 0] <- %"v704"
    => goto poll "L440" };
  ir_blk{ @"L667":
    %"v707" = %"v0" +p #16;
    %"v708" : P = (RawLoadPointer 8 load_effects) %"chk193";
    %"v710" = %"v0" +p #8;
    %"v711" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"v712" : L = Ptoi %"v708";
    %"v713" : L = Ptoi %"v711";
    %"v714" : L = Sub %"v712", %"v713";
    %"v719" : W = (Cmp Uge L) %"v714", #16
    => br %"v719" ? poll "L646" : "L717" };
  ir_blk{ @"L717":
    %"v722" = %"v0" +p #8;
    %"v723" : P = (RawLoadPointer 0 load_effects) %"chk193";
    call %"v725" : P = $"__GI_memcpy"(P %"v438", P %"v723", L %"v714")
    => goto "L662" };
  ir_blk{ @"L661":
    %"chk205" : A = (Check 0 8 Read 8) %"v437";
    %"v727" : P = (RawLoadPointer 0 load_effects) %"chk205";
    %"v728" : L = Ptoi %"v727";
    %"v729" : L = Ptoi %"v438";
    %"v730" : L = Sub %"v728", %"v729";
    %"v735" : W = (Cmp Ugt L) %"v730", #0
    => br %"v735" ? "L731" : "L733" };
  ir_blk{ @"L731":
    %"v736" : P = (RawLoadPointer 0 load_effects) %"chk205";
    %"v739" : L = Sub %"pr.4", %"v730";
    call %"v740" : P = $"__GI_memmove"(P %"v438", P %"v736", L %"v739")
    => goto "L733" };
  ir_blk{ @"L733" [%"pr.6" : L = phi("L731" => %"v739", "L661" => %"pr.4")]:
    %"v748" : W = (Cmp Eq L) %"pr.6", #16
    => br %"v748" ? poll "L646" : "L662" };
  ir_blk{ @"L662" [%"pr.5" : L = phi("L717" => %"v714", "L733" => %"pr.6")]:
    %"v751" = %"v0" +p #8;
    %"v753" = %"v0" +p #16;
    %"v755" = %"v0" +p #24;
    %"chk207" : A = (Renew 0 8 Read 8) %"chk170", %"v755";
    %"v756" : P = (RawLoadPointer 0 load_effects) %"chk207";
    %"chk208" : A = (Renew 0 8 Write 8) %"chk150", %"v753";
    store.ptr [%"chk208" + 0] <- %"v756";
    %"chk209" : A = (Renew 0 8 Write 8) %"chk169", %"v751";
    store.ptr [%"chk209" + 0] <- %"v756"
    => goto poll "L440" };
  ir_blk{ @"L627":
    %"v759" = %"v0" +p #160;
    %"v760" : P = (RawLoadPointer 0 load_effects) %"chk185";
    %"chk211" : A = (Check 0 8 Read 8) %"v760";
    %"v761" : P = (RawLoadPointer 0 load_effects) %"chk211";
    %"chk212" : A = (Check 0 4 Read 1) %"v761";
    %"v762" : W = (RawLoad (LdNarrow Sw) 0) %"chk212"
    => ret %"v762" }])) }.

Definition hello_image_fn__IO_wfile_underflow_mmap : func :=
  ir_fn{ "export" "_IO_wfile_underflow_mmap"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #4;
    %"v10" : L = (Ext Sw) %"v9";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L4" : "L6";
  @"L4":
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v14" : W = Or %"v13", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v14";
    %"v15" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v15";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L6":
    %"v21" = %"v0" +p #160;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" = %"v26" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v29" : L = Ptoi %"v23";
    %"v30" : L = Ptoi %"v28";
    %"v31" : W = (Cmp Ult L) %"v29", %"v30"
    => br %"v31" ? "L17" : "L19";
  @"L17":
    %"v33" = %"v0" +p #160;
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk9" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 4 Read 1) %"v35";
    %"v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk10"
    => ret %"v36";
  @"L19":
    %"v39" = %"v0" +p #152;
    %"v40" : P = (RawLoadPointer (-8) load_effects) %"chk4";
    %"v45" = %"v0" +p #8;
    %"v46" : P = (RawLoadPointer (-152) load_effects) %"chk4";
    %"v48" = %"v0" +p #16;
    %"v49" : P = (RawLoadPointer (-144) load_effects) %"chk4";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Uge L) %"v50", %"v51"
    => br %"v52" ? "L53" : "L54";
  @"L53":
    call %"v56" : W = $"_IO_file_underflow_mmap"(P %"v0");
    %"v58" : W = (Cmp Eq W) %"v56", #4294967295
    => goto "L54";
  @"L54" [%"v60" : W = phi("L19" => #0, "L53" => %"v58")]:
    => br %"v60" ? "L41" : "L43";
  @"L41":
    => ret #4294967295;
  @"L43":
    %"v63" = %"v0" +p #8;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"v3";
    store.ptr [%"chk15" + 0] <- %"v64";
    %"v69" = %"v0" +p #160;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk4", %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v71" = %"v70" +p #48;
    %"chk17" : A = (Check 0 8 Read 8) %"v71";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v73" : L = Ptoi %"v72";
    %"v74" : L = Ptoi #0;
    %"v75" : W = (Cmp Eq L) %"v73", %"v74"
    => br %"v75" ? "L65" : "L67";
  @"L65":
    %"v80" = %"v0" +p #160;
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v82" = %"v81" +p #64;
    %"chk19" : A = (Check 0 8 Read 8) %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v84" : L = Ptoi %"v83";
    %"v86" : W = (Cmp Ne L) %"v84", %"v74"
    => br %"v86" ? "L76" : "L78";
  @"L76":
    %"v88" = %"v0" +p #160;
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v90" = %"v89" +p #64;
    %"chk21" : A = (Check 0 8 Read 8) %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call void $"free"(P %"v91");
    %"chk22" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v95" : W = And %"v93", #4294967039;
    %"chk23" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk23" + 0] <- %"v95"
    => goto "L78";
  @"L78":
    call void $"__GI__IO_wdoallocbuf"(P %"v0")
    => goto "L67";
  @"L67":
    %"v98" = %"v0" +p #160;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk4", %"v98";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v100" = %"v99" +p #96;
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v104" = %"v103" +p #88;
    %"chk26" : A = (Check 0 8 Read 1) %"v104";
    %"v105" : L = (RawLoad LdL 0) %"chk26";
    %"chk27" : A = (Check 0 8 Write 1) %"v100";
    store Wl [%"chk27" + 0] <- %"v105";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v109" = %"v108" +p #16;
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v115" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v116" = %"v115" +p #48;
    %"chk31" : A = (Check 0 8 Read 8) %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Check 0 8 Write 8) %"v112";
    store.ptr [%"chk32" + 0] <- %"v117";
    %"chk33" : A = (Check 0 8 Write 8) %"v109";
    store.ptr [%"chk33" + 0] <- %"v117";
    %"chk34" : A = (Renew 0 8 Read 8) %"chk4", %"v98";
    %"v121" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v122" = %"v121" +p #88;
    %"v124" = %"v0" +p #8;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk14", %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v127" = %"v0" +p #16;
    %"v128" : P = (RawLoadPointer 8 load_effects) %"chk35";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk38" : A = (Check 0 8 Read 8) %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v136" = %"v135" +p #56;
    %"chk40" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v140" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v141" = %"v140" +p #8;
    call %"v142" : W = $"__libio_codecvt_in"(P %"v40", P %"v122", P %"v125", P %"v128", P %"v3", P %"v132", P %"v137", P %"v141");
    %"chk42" : A = (Renew 0 8 Read 8) %"chk15", %"v3";
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : A = (Renew 0 8 Write 8) %"chk14", %"v124";
    store.ptr [%"chk43" + 0] <- %"v145";
    %"chk44" : A = (Renew 0 8 Read 8) %"chk4", %"v98";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 8 Read 8) %"v151";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v156" = %"v155" +p #8;
    %"chk47" : A = (Check 0 8 Read 8) %"v156";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v158" : L = Ptoi %"v152";
    %"v159" : L = Ptoi %"v157";
    %"v160" : W = (Cmp Ult L) %"v158", %"v159"
    => br %"v160" ? "L146" : "L148";
  @"L146":
    %"v162" = %"v0" +p #160;
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk49" : A = (Check 0 8 Read 8) %"v163";
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"chk50" : A = (Check 0 4 Read 1) %"v164";
    %"v165" : W = (RawLoad (LdNarrow Sw) 0) %"chk50"
    => ret %"v165";
  @"L148":
    %"v167" : P = Copy $"__libc_errno";
    %"chk51" : A = (Check 0 4 Write 1) %"v167";
    store Ww [%"chk51" + 0] <- #84;
    %"chk52" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v169" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    %"v170" : W = Or %"v169", #32;
    %"chk53" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk53" + 0] <- %"v170"
    => ret #4294967295
} }.

Definition hello_image_fn__IO_wfile_underflow_maybe_mmap : func :=
  ir_fn{ "export" "_IO_wfile_underflow_maybe_mmap"(P %"v0") -> (RClass W) {
  @"start":
    call %"v6" : W = $"_IO_file_underflow_maybe_mmap"(P %"v0");
    %"v8" : W = (Cmp Eq W) %"v6", #4294967295
    => br %"v8" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v11" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #224;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v15" = %"v14" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v16";
    rawcall %"v18" : W = %"chk3"(P %"v0")
    => ret %"v18"
} }.

Definition hello_image_fn___GI__IO_wfile_overflow : func :=
  ir_fn{ "export" "__GI__IO_wfile_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #8
    => br %"v9" ? "L4" : "L6";
  @"L4":
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Or %"v11", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v12";
    %"v13" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L6":
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v20" : W = And %"v19", #2048;
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => br %"v21" ? "L23" : "L22";
  @"L22":
    %"v25" = %"v0" +p #160;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v27" = %"v26" +p #24;
    %"chk6" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v29" : L = Ptoi %"v28";
    %"v30" : L = Ptoi #0;
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => goto "L23";
  @"L23" [%"v33" : W = phi("L6" => #1, "L22" => %"v31")]:
    => br %"v33" ? "L15" : "L17";
  @"L15":
    %"v38" = %"v0" +p #160;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v40" = %"v39" +p #24;
    %"chk8" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v42" : L = Ptoi %"v41";
    %"v43" : L = Ptoi #0;
    %"v44" : W = (Cmp Eq L) %"v42", %"v43"
    => br %"v44" ? "L34" : "L35";
  @"L34":
    call void $"__GI__IO_wdoallocbuf"(P %"v0");
    call void $"__GI__IO_free_wbackup_area"(P %"v0");
    %"v51" = %"v0" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v53" : L = Ptoi %"v52";
    %"v55" : W = (Cmp Eq L) %"v53", %"v43"
    => br %"v55" ? "L47" : "L49";
  @"L47":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v58" = %"v0" +p #24;
    %"v60" = %"v0" +p #56;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v58";
    store.ptr [%"chk11" + 0] <- %"v61";
    %"v63" = %"v0" +p #8;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk10", %"v60";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v63";
    store.ptr [%"chk13" + 0] <- %"v66";
    %"v68" = %"v0" +p #16;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk10", %"v60";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v68";
    store.ptr [%"chk15" + 0] <- %"v71"
    => goto "L49";
  @"L49":
    %"v73" = %"v0" +p #160;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk7", %"v73";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v75" = %"v74" +p #16;
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v79" = %"v78" +p #48;
    %"chk18" : A = (Check 0 8 Read 8) %"v79";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (Check 0 8 Write 8) %"v75";
    store.ptr [%"chk19" + 0] <- %"v80";
    %"chk20" : A = (Renew 0 8 Read 8) %"chk7", %"v73";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v87" = %"v86" +p #48;
    %"chk22" : A = (Check 0 8 Read 8) %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (Check 0 8 Write 8) %"v83";
    store.ptr [%"chk23" + 0] <- %"v88";
    %"chk24" : A = (Renew 0 8 Read 8) %"chk7", %"v73";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v92" = %"v91" +p #8;
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v96" = %"v95" +p #48;
    %"chk26" : A = (Check 0 8 Read 8) %"v96";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (Check 0 8 Write 8) %"v92";
    store.ptr [%"chk27" + 0] <- %"v97"
    => goto "L36";
  @"L35":
    %"v102" = %"v0" +p #160;
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk29" : A = (Check 0 8 Read 8) %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v107" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v108" = %"v107" +p #56;
    %"chk31" : A = (Check 0 8 Read 8) %"v108";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v110" : L = Ptoi %"v104";
    %"v111" : L = Ptoi %"v109";
    %"v112" : W = (Cmp Eq L) %"v110", %"v111"
    => br %"v112" ? "L98" : "L36";
  @"L98":
    %"v114" = %"v0" +p #16;
    %"v116" = %"v0" +p #8;
    %"v118" = %"v0" +p #56;
    %"v119" : P = (RawLoadPointer (-104) load_effects) %"chk7";
    %"chk33" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v116";
    store.ptr [%"chk33" + 0] <- %"v119";
    %"chk34" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v114";
    store.ptr [%"chk34" + 0] <- %"v119";
    %"v121" = %"v0" +p #160;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk7", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v123" = %"v122" +p #8;
    %"v126" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v130" = %"v129" +p #48;
    %"chk38" : A = (Check 0 8 Read 8) %"v130";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 8 Write 8) %"v126";
    store.ptr [%"chk39" + 0] <- %"v131";
    %"chk40" : A = (Check 0 8 Write 8) %"v123";
    store.ptr [%"chk40" + 0] <- %"v131"
    => goto "L36";
  @"L36":
    code ((app ir[ %"v133" = %"v0" +p #160;
      %"chk41" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v134" : P = (RawLoadPointer 0 load_effects) %"chk41";
      %"v135" = %"v134" +p #32;
      %"v138" : P = (RawLoadPointer 0 load_effects) %"chk41";
      %"chk43" : A = (Check 0 8 Read 8) %"v138";
      %"v139" : P = (RawLoadPointer 0 load_effects) %"chk43";
      %"chk44" : A = (Check 0 8 Write 8) %"v135";
      store.ptr [%"chk44" + 0] <- %"v139";
      %"chk45" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v142" : P = (RawLoadPointer 0 load_effects) %"chk45";
      %"v143" = %"v142" +p #24;
      %"v146" : P = (RawLoadPointer 0 load_effects) %"chk45";
      %"v147" = %"v146" +p #32;
      %"chk47" : A = (Check 0 8 Read 8) %"v147";
      %"v148" : P = (RawLoadPointer 0 load_effects) %"chk47";
      %"chk48" : A = (Check 0 8 Write 8) %"v143";
      store.ptr [%"chk48" + 0] <- %"v148";
      %"chk49" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v151" : P = (RawLoadPointer 0 load_effects) %"chk49";
      %"v152" = %"v151" +p #40;
      %"v155" : P = (RawLoadPointer 0 load_effects) %"chk49";
      %"v156" = %"v155" +p #56;
      %"chk51" : A = (Check 0 8 Read 8) %"v156";
      %"v157" : P = (RawLoadPointer 0 load_effects) %"chk51";
      %"chk52" : A = (Check 0 8 Write 8) %"v152";
      store.ptr [%"chk52" + 0] <- %"v157";
      %"chk53" : A = (Renew 0 8 Read 8) %"chk7", %"v133";
      %"v160" : P = (RawLoadPointer 0 load_effects) %"chk53";
      %"v161" = %"v160" +p #16;
      %"v164" : P = (RawLoadPointer 0 load_effects) %"chk53";
      %"v167" : P = (RawLoadPointer 0 load_effects) %"chk53";
      %"v168" = %"v167" +p #8;
      %"chk56" : A = (Check 0 8 Read 8) %"v168";
      %"v169" : P = (RawLoadPointer 0 load_effects) %"chk56"] ir[ %"chk57" : A = (Check 0 8 Write 8) %"v164";
      store.ptr [%"chk57" + 0] <- %"v169";
      %"chk58" : A = (Check 0 8 Write 8) %"v161";
      store.ptr [%"chk58" + 0] <- %"v169";
      %"v171" = %"v0" +p #40;
      %"v173" = %"v0" +p #8;
      %"chk59" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v173";
      %"v174" : P = (RawLoadPointer 0 load_effects) %"chk59";
      %"chk60" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v171";
      store.ptr [%"chk60" + 0] <- %"v174";
      %"v176" = %"v0" +p #32;
      %"chk61" : A = (Renew 0 8 Read 8) %"chk60", %"v171";
      %"v179" : P = (RawLoadPointer 0 load_effects) %"chk61";
      %"chk62" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v176";
      store.ptr [%"chk62" + 0] <- %"v179";
      %"v181" = %"v0" +p #48;
      %"v183" = %"v0" +p #64;
      %"chk63" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v183";
      %"v184" : P = (RawLoadPointer 0 load_effects) %"chk63";
      %"chk64" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v181";
      store.ptr [%"chk64" + 0] <- %"v184";
      %"v186" = %"v0" +p #24;
      %"v190" = %"v0" +p #16;
      %"chk65" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v190";
      %"v191" : P = (RawLoadPointer 0 load_effects) %"chk65";
      %"chk66" : A = (Renew 0 8 Write 8) %"chk59", %"v173";
      store.ptr [%"chk66" + 0] <- %"v191";
      %"chk67" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v186";
      store.ptr [%"chk67" + 0] <- %"v191";
      %"chk68" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
      %"v193" : W = (RawLoad (LdNarrow Sw) 0) %"chk68";
      %"v194" : W = Or %"v193", #2048;
      %"chk69" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
      store Ww [%"chk69" + 0] <- %"v194";
      %"v199" : W = (RawLoad (LdNarrow Sw) 0) %"chk69";
      %"v201" : W = And %"v199", #514]))
    => br %"v201" ? "L195" : "L17";
  @"L195":
    %"v203" = %"v0" +p #160;
    %"chk71" : A = (Renew 0 8 Read 8) %"chk7", %"v203";
    %"v204" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v205" = %"v204" +p #40;
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v209" = %"v208" +p #32;
    %"chk73" : A = (Check 0 8 Read 8) %"v209";
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"chk74" : A = (Check 0 8 Write 8) %"v205";
    store.ptr [%"chk74" + 0] <- %"v210"
    => goto "L17";
  @"L17":
    %"v215" : W = (Cmp Eq W) %"v2", #4294967295
    => br %"v215" ? "L211" : "L213";
  @"L211":
    %"v220" = %"v0" +p #192;
    %"chk75" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v220";
    %"v221" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"v222" : W = (Cmp Sle W) %"v221", #0
    => br %"v222" ? "L216" : "L217";
  @"L216":
    %"v225" = %"v0" +p #32;
    %"chk76" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v225";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v228" = %"v0" +p #40;
    %"v229" : P = (RawLoadPointer 8 load_effects) %"chk76";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v233" : L = Ptoi %"v229";
    %"v234" : L = Ptoi %"v232";
    %"v235" : L = Sub %"v233", %"v234";
    call %"v236" : W = $"__GI__IO_do_write"(P %"v0", P %"v226", L %"v235")
    => goto "L218";
  @"L217":
    %"v239" = %"v0" +p #160;
    %"chk79" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v239";
    %"v240" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v241" = %"v240" +p #24;
    %"chk80" : A = (Check 0 8 Read 8) %"v241";
    %"v242" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"v245" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v246" = %"v245" +p #32;
    %"chk82" : A = (Check 0 8 Read 8) %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk82";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v251" = %"v250" +p #24;
    %"chk84" : A = (Check 0 8 Read 8) %"v251";
    %"v252" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"v253" : L = Ptoi %"v247";
    %"v254" : L = Ptoi %"v252";
    %"v255" : L = Sub %"v253", %"v254";
    %"v256" : L = Div %"v255", #4;
    call %"v257" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v242", L %"v256")
    => goto "L218";
  @"L218" [%"v258" : W = phi("L216" => %"v236", "L217" => %"v257")]:
    => ret %"v258";
  @"L213":
    %"v264" = %"v0" +p #160;
    %"chk85" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v264";
    %"v265" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v266" = %"v265" +p #32;
    %"chk86" : A = (Check 0 8 Read 8) %"v266";
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"v270" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v271" = %"v270" +p #56;
    %"chk88" : A = (Check 0 8 Read 8) %"v271";
    %"v272" : P = (RawLoadPointer 0 load_effects) %"chk88";
    %"v273" : L = Ptoi %"v267";
    %"v274" : L = Ptoi %"v272";
    %"v275" : W = (Cmp Eq L) %"v273", %"v274"
    => br %"v275" ? "L260" : "L262";
  @"L260":
    %"v283" = %"v0" +p #192;
    %"chk89" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v283";
    %"v284" : W = (RawLoad (LdNarrow Sw) 0) %"chk89";
    %"v285" : W = (Cmp Sle W) %"v284", #0
    => br %"v285" ? "L279" : "L280";
  @"L279":
    %"v288" = %"v0" +p #32;
    %"chk90" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v288";
    %"v289" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"v291" = %"v0" +p #40;
    %"v292" : P = (RawLoadPointer 8 load_effects) %"chk90";
    %"v295" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"v296" : L = Ptoi %"v292";
    %"v297" : L = Ptoi %"v295";
    %"v298" : L = Sub %"v296", %"v297";
    call %"v299" : W = $"__GI__IO_do_write"(P %"v0", P %"v289", L %"v298")
    => goto "L281";
  @"L280":
    %"v302" = %"v0" +p #160;
    %"v303" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v304" = %"v303" +p #24;
    %"chk94" : A = (Check 0 8 Read 8) %"v304";
    %"v305" : P = (RawLoadPointer 0 load_effects) %"chk94";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v309" = %"v308" +p #32;
    %"chk96" : A = (Check 0 8 Read 8) %"v309";
    %"v310" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"v313" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v314" = %"v313" +p #24;
    %"chk98" : A = (Check 0 8 Read 8) %"v314";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"v316" : L = Ptoi %"v310";
    %"v317" : L = Ptoi %"v315";
    %"v318" : L = Sub %"v316", %"v317";
    %"v319" : L = Div %"v318", #4;
    call %"v320" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v305", L %"v319")
    => goto "L281";
  @"L281" [%"v321" : W = phi("L279" => %"v299", "L280" => %"v320")]:
    %"v323" : W = (Cmp Eq W) %"v321", #4294967295
    => br %"v323" ? "L276" : "L262";
  @"L276":
    => ret #4294967295;
  @"L262":
    %"v326" = %"v0" +p #160;
    %"chk99" : A = (Renew 0 8 Read 8) %"chk85", %"v326";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"v328" = %"v327" +p #32;
    %"chk100" : A = (Check 0 8 Read 8) %"v328";
    %"v329" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"v330" = %"v329" +p #4;
    %"chk101" : A = (Renew 0 8 Write 8) %"chk100", %"v328";
    store.ptr [%"chk101" + 0] <- %"v330";
    %"chk102" : A = (Check 0 4 Write 1) %"v329";
    store Ww [%"chk102" + 0] <- %"v2";
    %"chk103" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v336" : W = (RawLoad (LdNarrow Sw) 0) %"chk103";
    %"v337" : W = And %"v336", #2
    => br %"v337" ? "L339" : "L338";
  @"L338":
    %"v341" : W = (RawLoad (LdNarrow Sw) 0) %"chk103";
    %"v342" : W = And %"v341", #512
    => br %"v342" ? "L343" : "L339";
  @"L343":
    %"v346" : W = (Cmp Eq W) %"v2", #10
    => goto "L339";
  @"L339" [%"v350" : W = phi("L262" => #1, "L338" => #0, "L343" => %"v346")]:
    => br %"v350" ? "L332" : "L334";
  @"L332":
    %"v358" = %"v0" +p #192;
    %"chk105" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v358";
    %"v359" : W = (RawLoad (LdNarrow Sw) 0) %"chk105";
    %"v360" : W = (Cmp Sle W) %"v359", #0
    => br %"v360" ? "L354" : "L355";
  @"L354":
    %"v363" = %"v0" +p #32;
    %"chk106" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v363";
    %"v364" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"v366" = %"v0" +p #40;
    %"v367" : P = (RawLoadPointer 8 load_effects) %"chk106";
    %"v370" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"v371" : L = Ptoi %"v367";
    %"v372" : L = Ptoi %"v370";
    %"v373" : L = Sub %"v371", %"v372";
    call %"v374" : W = $"__GI__IO_do_write"(P %"v0", P %"v364", L %"v373")
    => goto "L356";
  @"L355":
    %"v377" = %"v0" +p #160;
    %"chk109" : A = (Renew 0 8 Read 8) %"chk85", %"v377";
    %"v378" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"v379" = %"v378" +p #24;
    %"chk110" : A = (Check 0 8 Read 8) %"v379";
    %"v380" : P = (RawLoadPointer 0 load_effects) %"chk110";
    %"v383" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"v384" = %"v383" +p #32;
    %"chk112" : A = (Check 0 8 Read 8) %"v384";
    %"v385" : P = (RawLoadPointer 0 load_effects) %"chk112";
    %"v388" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"v389" = %"v388" +p #24;
    %"chk114" : A = (Check 0 8 Read 8) %"v389";
    %"v390" : P = (RawLoadPointer 0 load_effects) %"chk114";
    %"v391" : L = Ptoi %"v385";
    %"v392" : L = Ptoi %"v390";
    %"v393" : L = Sub %"v391", %"v392";
    %"v394" : L = Div %"v393", #4;
    call %"v395" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v380", L %"v394")
    => goto "L356";
  @"L356" [%"v396" : W = phi("L354" => %"v374", "L355" => %"v395")]:
    %"v398" : W = (Cmp Eq W) %"v396", #4294967295
    => br %"v398" ? "L351" : "L334";
  @"L351":
    => ret #4294967295;
  @"L334":
    => ret %"v2"
} }.

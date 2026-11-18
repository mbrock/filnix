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

Definition hi_fn___run_exit_handlers : func :=
  ir_fn{ "export" "__run_exit_handlers"(W %"v0", P %"v2", W %"v4", W %"v6") -> RVoid {
  @"start":
    call %"v12" : P = $"zthread_self_cookie"();
    %"v16" : P = Copy $"glibc_exit#__exit_lock";
    %"v17" = %"v16" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v17";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v20" : L = Ptoi %"v18";
    %"v21" : L = Ptoi %"v12";
    %"v22" : W = (Cmp Ne L) %"v20", %"v21"
    => br %"v22" ? "L13" : "L15";
  @"L13":
    %"v24" : P = Copy $"glibc_exit#__exit_lock";
    %"chk1" : A = (Check 0 4 Write 4) %"v24";
    %"v31" : W = (RawCas (CasNarrow Sw) 0) %"chk1", #0, #1;
    %"v32" : W = (Cmp Eq W) %"v31", #0
    => br %"v32" ? "L34" : "L33";
  @"L33":
    => goto "L34";
  @"L34":
    %"v35" : W = (Cmp Ne W) %"v31", #0
    => br %"v35" ? "L38" : "L27";
  @"L38":
    call void $"__GI___lll_lock_wait_private"(P %"v24")
    => goto "L27";
  @"L27":
    %"v48" : P = Copy $"glibc_exit#__exit_lock";
    %"v49" = %"v48" +p #8;
    %"chk2" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk2" + 0] <- %"v12"
    => goto "L15";
  @"L15":
    %"v51" : P = Copy $"glibc_exit#__exit_lock";
    %"v52" = %"v51" +p #4;
    %"chk3" : A = (Check 0 4 Read 1) %"v52";
    %"v53" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v54" : W = Add %"v53", #1;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk3", %"v52";
    store Ww [%"chk4" + 0] <- %"v54";
    %"v58" : W = (Ext Ub) %"v6"
    => br %"v58" ? "L55" : "L57";
  @"L55":
    call void $"__GI___call_tls_dtors"()
    => goto "L57";
  @"L57":
    %"v60" : P = Copy $"__exit_funcs_lock";
    %"chk5" : A = (Check 0 4 Write 4) %"v60";
    %"v67" : W = (RawCas (CasNarrow Sw) 0) %"chk5", #0, #1;
    %"v68" : W = (Cmp Eq W) %"v67", #0
    => br %"v68" ? "L70" : "L69";
  @"L69":
    => goto "L70";
  @"L70":
    %"v71" : W = (Cmp Ne W) %"v67", #0
    => br %"v71" ? "L74" : "L88";
  @"L74":
    call void $"__GI___lll_lock_wait_private"(P %"v60")
    => goto "L88";
  @"L88":
    %"chk6" : A = (Check 0 8 Read 8) %"v2";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v95" : L = Ptoi %"v90";
    %"v96" : L = Ptoi #0;
    %"v97" : W = (Cmp Eq L) %"v95", %"v96"
    => br %"v97" ? "L91" : "L101";
  @"L91":
    %"v98" : P = Copy $"__exit_funcs_done";
    %"chk7" : A = (Check 0 1 Write 1) %"v98";
    store Wb [%"chk7" + 0] <- #1;
    %"v360" : P = Copy $"__exit_funcs_lock";
    %"chk8" : A = (Check 0 4 Read 1) %"v360";
    %"v364" : W = (RawLoad (LdNarrow Sw) 0) %"chk8"
    => goto "L365";
  @"L101":
    %"v105" = %"v90" +p #8;
    %"chk9" : A = (Check 0 8 Read 1) %"v105";
    %"v106" : L = (RawLoad LdL 0) %"chk9";
    %"v107" : W = (Cmp Ugt L) %"v106", #0
    => br %"v107" ? "L102" : "L103";
  @"L102":
    %"v110" = %"v90" +p #16;
    %"v112" = %"v90" +p #8;
    %"v113" : L = (RawLoad LdL 0) %"chk9";
    %"v114" : L = Sub %"v113", #1;
    %"chk11" : A = (Renew 0 8 Write 1) %"chk9", %"v112";
    store Wl [%"chk11" + 0] <- %"v114";
    %"v115" : L = Shl %"v114", #5;
    %"v116" = %"v110" +p %"v115";
    %"v118" : P = Copy $"__new_exitfn_called";
    %"chk12" : A = (Check 0 8 Read 1) %"v118";
    %"v119" : L = (RawLoad LdL 0) %"chk12";
    %"chk13" : A = (Check 0 8 Read 1) %"v116";
    %"v121" : L = (RawLoad LdL 0) %"chk13";
    %"v324" : W = (Cmp Slt L) %"v121", #2
    => br %"v324" ? "L325" : "L326";
  @"L130":
    %"v132" = %"v116" +p #8;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v132";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v136" = %"v132" +p #8;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk14", %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v140" : P = Copy $"__exit_funcs_lock";
    %"chk16" : A = (Check 0 4 Read 1) %"v140";
    %"v144" : W = (RawLoad (LdNarrow Sw) 0) %"chk16"
    => goto "L145";
  @"L145" [%"v147" : W = phi("L130" => %"v144", "L145" => %"v148")]:
    %"chk17" : A = (HalfCheck Lower 0 4 Write 4) %"chk16", %"v140";
    %"v148" : W = (RawCas (CasNarrow Sw) 0) %"chk17", %"v147", #0;
    %"v149" : W = (Cmp Eq W) %"v148", %"v147"
    => br %"v149" ? "L146" : poll "L145";
  @"L146":
    %"v154" : W = (Cmp Sgt W) %"v147", #1
    => br %"v154" ? "L157" : "L152";
  @"L157":
    call void $"__GI___lll_lock_wake_private"(P %"v140")
    => goto "L152";
  @"L152":
    %"chk18" : F = CheckFunction %"v133";
    rawcall void %"chk18"(W %"v0", P %"v137");
    %"v172" : P = Copy $"__exit_funcs_lock";
    %"chk19" : A = (Check 0 4 Write 4) %"v172";
    %"v179" : W = (RawCas (CasNarrow Sw) 0) %"chk19", #0, #1;
    %"v180" : W = (Cmp Eq W) %"v179", #0
    => br %"v180" ? "L182" : "L181";
  @"L181":
    => goto "L182";
  @"L182":
    %"v183" : W = (Cmp Ne W) %"v179", #0
    => br %"v183" ? "L186" : "L123";
  @"L186":
    call void $"__GI___lll_lock_wait_private"(P %"v172")
    => goto "L123";
  @"L196":
    %"v198" = %"v116" +p #8;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v198";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v202" : P = Copy $"__exit_funcs_lock";
    %"chk21" : A = (Check 0 4 Read 1) %"v202";
    %"v206" : W = (RawLoad (LdNarrow Sw) 0) %"chk21"
    => goto "L207";
  @"L207" [%"v209" : W = phi("L196" => %"v206", "L207" => %"v210")]:
    %"chk22" : A = (HalfCheck Lower 0 4 Write 4) %"chk21", %"v202";
    %"v210" : W = (RawCas (CasNarrow Sw) 0) %"chk22", %"v209", #0;
    %"v211" : W = (Cmp Eq W) %"v210", %"v209"
    => br %"v211" ? "L208" : poll "L207";
  @"L208":
    %"v216" : W = (Cmp Sgt W) %"v209", #1
    => br %"v216" ? "L219" : "L214";
  @"L219":
    call void $"__GI___lll_lock_wake_private"(P %"v202")
    => goto "L214";
  @"L214":
    %"chk23" : F = CheckFunction %"v199";
    rawcall void %"chk23"();
    %"v232" : P = Copy $"__exit_funcs_lock";
    %"chk24" : A = (Check 0 4 Write 4) %"v232";
    %"v239" : W = (RawCas (CasNarrow Sw) 0) %"chk24", #0, #1;
    %"v240" : W = (Cmp Eq W) %"v239", #0
    => br %"v240" ? "L242" : "L241";
  @"L241":
    => goto "L242";
  @"L242":
    %"v243" : W = (Cmp Ne W) %"v239", #0
    => br %"v243" ? "L246" : "L123";
  @"L246":
    call void $"__GI___lll_lock_wait_private"(P %"v232")
    => goto "L123";
  @"L256":
    %"chk25" : A = (Renew 0 8 Write 1) %"chk13", %"v116";
    store Wl [%"chk25" + 0] <- #0;
    %"v259" = %"v116" +p #8;
    %"chk26" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v259";
    %"v260" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v263" = %"v259" +p #8;
    %"chk27" : A = (HalfCheck Upper 0 8 Read 8) %"chk26", %"v263";
    %"v264" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v267" : P = Copy $"__exit_funcs_lock";
    %"chk28" : A = (Check 0 4 Read 1) %"v267";
    %"v271" : W = (RawLoad (LdNarrow Sw) 0) %"chk28"
    => goto "L272";
  @"L272" [%"v274" : W = phi("L256" => %"v271", "L272" => %"v275")]:
    %"chk29" : A = (HalfCheck Lower 0 4 Write 4) %"chk28", %"v267";
    %"v275" : W = (RawCas (CasNarrow Sw) 0) %"chk29", %"v274", #0;
    %"v276" : W = (Cmp Eq W) %"v275", %"v274"
    => br %"v276" ? "L273" : poll "L272";
  @"L273":
    %"v281" : W = (Cmp Sgt W) %"v274", #1
    => br %"v281" ? "L284" : "L279";
  @"L284":
    call void $"__GI___lll_lock_wake_private"(P %"v267")
    => goto "L279";
  @"L279":
    %"chk30" : F = CheckFunction %"v260";
    rawcall void %"chk30"(P %"v264", W %"v0");
    %"v299" : P = Copy $"__exit_funcs_lock";
    %"chk31" : A = (Check 0 4 Write 4) %"v299";
    %"v306" : W = (RawCas (CasNarrow Sw) 0) %"chk31", #0, #1;
    %"v307" : W = (Cmp Eq W) %"v306", #0
    => br %"v307" ? "L309" : "L308";
  @"L308":
    => goto "L309";
  @"L309":
    %"v310" : W = (Cmp Ne W) %"v306", #0
    => br %"v310" ? "L313" : "L123";
  @"L313":
    call void $"__GI___lll_lock_wait_private"(P %"v299")
    => goto "L123";
  @"L325":
    %"v327" : W = (Cmp Eq L) %"v121", #0
    => br %"v327" ? "L123" : "L328";
  @"L328":
    %"v329" : W = (Cmp Eq L) %"v121", #1
    => br %"v329" ? "L123" : "L330";
  @"L330":
    => goto "L123";
  @"L326":
    %"v331" : W = (Cmp Eq L) %"v121", #2
    => br %"v331" ? poll "L130" : "L332";
  @"L332":
    %"v333" : W = (Cmp Eq L) %"v121", #3
    => br %"v333" ? poll "L196" : "L334";
  @"L334":
    %"v335" : W = (Cmp Eq L) %"v121", #4
    => br %"v335" ? poll "L256" : "L123";
  @"L123":
    %"v341" : P = Copy $"__new_exitfn_called";
    %"chk32" : A = (Check 0 8 Read 1) %"v341";
    %"v342" : L = (RawLoad LdL 0) %"chk32";
    %"v343" : W = (Cmp Ne L) %"v119", %"v342"
    => br %"v343" ? poll "L88" : poll "L101";
  @"L103":
    %"chk33" : A = (HalfCheck Lower 0 8 Read 8) %"chk9", %"v90";
    %"v349" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (Renew 0 8 Write 8) %"chk6", %"v2";
    store.ptr [%"chk34" + 0] <- %"v349";
    %"chk35" : A = (Renew 0 8 Read 8) %"chk6", %"v2";
    %"v354" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v355" : L = Ptoi %"v354";
    %"v357" : W = (Cmp Ne L) %"v355", %"v96"
    => br %"v357" ? "L350" : poll "L88";
  @"L350":
    call void $"free"(P %"v90")
    => goto poll "L88";
  @"L365" [%"v367" : W = phi("L91" => %"v364", "L365" => %"v368")]:
    %"chk36" : A = (HalfCheck Lower 0 4 Write 4) %"chk8", %"v360";
    %"v368" : W = (RawCas (CasNarrow Sw) 0) %"chk36", %"v367", #0;
    %"v369" : W = (Cmp Eq W) %"v368", %"v367"
    => br %"v369" ? "L366" : poll "L365";
  @"L366":
    %"v374" : W = (Cmp Sgt W) %"v367", #1
    => br %"v374" ? "L377" : "L372";
  @"L377":
    call void $"__GI___lll_lock_wake_private"(P %"v360")
    => goto "L372";
  @"L372":
    %"v391" : W = (Ext Ub) %"v4"
    => br %"v391" ? "L388" : "L390";
  @"L388":
    call %"v392" : W = $"_IO_cleanup"()
    => goto "L390";
  @"L390":
    call void $"zsys_exit_soft"(W %"v0")
    => ret void
} }.

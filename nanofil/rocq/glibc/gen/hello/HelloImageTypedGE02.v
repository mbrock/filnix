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

Definition hello_image_fn___GI___getdelim : func :=
  ir_fn{ "export" "__GI___getdelim"(P %"v0", P %"v2", W %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v23" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v24" : W = And %"v23", #32768;
    %"v25" : W = (Cmp Eq W) %"v24", #0
    => br %"v25" ? "L26" : "L21";
  @"L26":
    call %"v30" : P = $"zthread_self_cookie"();
    %"v34" : P = Copy $"__libc_single_threaded_internal";
    %"chk1" : A = (Check 0 1 Read 1) %"v34";
    %"v35" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v36" : W = (Cmp Ne W) %"v35", #0
    => br %"v36" ? "L37" : "L38";
  @"L37":
    %"v40" = %"v6" +p #136;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v42" = %"v41" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v44" : L = Ptoi %"v43";
    %"v45" : L = Ptoi #0;
    %"v46" : W = (Cmp Eq L) %"v44", %"v45"
    => goto "L38";
  @"L38" [%"v48" : W = phi("L26" => #0, "L37" => %"v46")]:
    => br %"v48" ? "L31" : "L32";
  @"L31":
    %"v50" = %"v6" +p #136;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v51";
    store Ww [%"chk5" + 0] <- #1;
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v55" = %"v54" +p #8;
    %"chk7" : A = (Check 0 8 Write 8) %"v55";
    store.ptr [%"chk7" + 0] <- %"v30"
    => goto "L21";
  @"L32":
    %"v61" = %"v6" +p #136;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v63" = %"v62" +p #8;
    %"chk9" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v66" : L = Ptoi %"v64";
    %"v67" : L = Ptoi %"v30";
    %"v68" : W = (Cmp Ne L) %"v66", %"v67"
    => br %"v68" ? "L57" : "L58";
  @"L57":
    %"v71" = %"v6" +p #136;
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk11" : A = (Check 0 4 Write 4) %"v72";
    %"v79" : W = (RawCas (CasNarrow Sw) 0) %"chk11", #0, #1;
    %"v80" : W = (Cmp Eq W) %"v79", #0
    => br %"v80" ? "L82" : "L81";
  @"L81":
    => goto "L82";
  @"L82":
    %"v83" : W = (Cmp Ne W) %"v79", #0
    => br %"v83" ? "L86" : "L75";
  @"L86":
    call void $"__GI___lll_lock_wait_private"(P %"v72")
    => goto "L75";
  @"L75":
    %"v97" = %"v6" +p #136;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk8", %"v97";
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v99" = %"v98" +p #8;
    %"chk13" : A = (Check 0 8 Write 8) %"v99";
    store.ptr [%"chk13" + 0] <- %"v30"
    => goto "L21";
  @"L58":
    %"v102" = %"v6" +p #136;
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v104" = %"v103" +p #4;
    %"chk15" : A = (Check 0 4 Read 1) %"v104";
    %"v105" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v106" : W = Add %"v105", #1;
    %"chk16" : A = (Renew 0 4 Write 1) %"chk15", %"v104";
    store Ww [%"chk16" + 0] <- %"v106"
    => goto "L21";
  @"L21":
    %"chk17" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"v111" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v112" : W = And %"v111", #32;
    %"v113" : W = (Cmp Ne W) %"v112", #0
    => br %"v113" ? "L116" : "L109";
  @"L109":
    %"v123" : L = Ptoi %"v0";
    %"v124" : L = Ptoi #0;
    %"v125" : W = (Cmp Eq L) %"v123", %"v124"
    => br %"v125" ? "L127" : "L126";
  @"L126":
    %"v129" : L = Ptoi %"v2";
    %"v131" : W = (Cmp Eq L) %"v129", %"v124"
    => goto "L127";
  @"L127" [%"v133" : W = phi("L109" => #1, "L126" => %"v131")]:
    => br %"v133" ? "L119" : "L121";
  @"L119":
    %"v134" : P = Copy $"__libc_errno";
    %"chk18" : A = (Check 0 4 Write 1) %"v134";
    store Ww [%"chk18" + 0] <- #22;
    %"chk19" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"iw_1.v3" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"iw_1.v4" : W = Or %"iw_1.v3", #32;
    %"chk20" : A = (Renew 0 4 Write 1) %"chk0", %"v6";
    store Ww [%"chk20" + 0] <- %"iw_1.v4"
    => goto "L116";
  @"L121":
    %"chk21" : A = (Check 0 8 Read 8) %"v0";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v145" : L = Ptoi %"v144";
    %"v147" : W = (Cmp Eq L) %"v145", %"v124"
    => br %"v147" ? "L149" : "L148";
  @"L148":
    %"chk22" : A = (Check 0 8 Read 1) %"v2";
    %"v151" : L = (RawLoad LdL 0) %"chk22";
    %"v152" : W = (Cmp Eq L) %"v151", #0
    => goto "L149";
  @"L149" [%"v154" : W = phi("L121" => #1, "L148" => %"v152")]:
    => br %"v154" ? "L140" : "L142";
  @"L140":
    %"chk23" : A = (Check 0 8 Write 1) %"v2";
    store Wl [%"chk23" + 0] <- #120;
    %"v158" : L = (RawLoad LdL 0) %"chk23";
    call %"v159" : P = $"malloc"(L %"v158");
    %"chk25" : A = (Renew 0 8 Write 8) %"chk21", %"v0";
    store.ptr [%"chk25" + 0] <- %"v159";
    %"chk26" : A = (Renew 0 8 Read 8) %"chk21", %"v0";
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v165" : L = Ptoi %"v164";
    %"v167" : W = (Cmp Ne L) %"v165", %"v124"
    => br %"v167" ? "L160" : "iw_2.start";
  @"L160":
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk28" : A = (Check 0 1 Write 1) %"v169";
    store Wb [%"chk28" + 0] <- #0
    => goto "L142";
  @"iw_2.start":
    %"chk29" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"iw_2.v3" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"iw_2.v4" : W = Or %"iw_2.v3", #32;
    %"chk30" : A = (Renew 0 4 Write 1) %"chk0", %"v6";
    store Ww [%"chk30" + 0] <- %"iw_2.v4"
    => goto "L116";
  @"L142":
    %"v176" = %"v6" +p #16;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v176";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v179" = %"v6" +p #8;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v179";
    %"v180" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v181" : L = Ptoi %"v177";
    %"v182" : L = Ptoi %"v180";
    %"v183" : L = Sub %"v181", %"v182";
    %"v188" : W = (Cmp Sle L) %"v183", #0
    => br %"v188" ? "L184" : "L209";
  @"L184":
    call %"v193" : W = $"__GI___underflow"(P %"v6");
    %"v195" : W = (Cmp Eq W) %"v193", #4294967295
    => br %"v195" ? "L116" : "L191";
  @"L191":
    %"v201" = %"v6" +p #16;
    %"chk33" : A = (Renew 0 8 Read 8) %"chk31", %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v204" = %"v6" +p #8;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk32", %"v204";
    %"v205" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v206" : L = Ptoi %"v202";
    %"v207" : L = Ptoi %"v205";
    %"v208" : L = Sub %"v206", %"v207"
    => goto "L209";
  @"L209" [%"pr.6" : L = phi("L191" => %"v208", "L142" => %"v183", "L313" => %"v335"); %"pr.4" : L = phi("L191" => #0, "L142" => #0, "L313" => %"v253")]:
    %"v216" = %"v6" +p #8;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk32", %"v216";
    %"v217" : P = (RawLoadPointer 0 load_effects) %"chk35";
    call %"v220" : P = $"__GI_memchr"(P %"v217", W %"v4", L %"pr.6");
    %"v225" : L = Ptoi %"v220";
    %"v227" : W = (Cmp Ne L) %"v225", %"v124"
    => br %"v227" ? "L221" : "L223";
  @"L221":
    %"v230" = %"v6" +p #8;
    %"chk36" : A = (Renew 0 8 Read 8) %"chk32", %"v230";
    %"v231" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v233" : L = Ptoi %"v231";
    %"v234" : L = Sub %"v225", %"v233";
    %"v235" : L = Add %"v234", #1
    => goto "L223";
  @"L223" [%"pr.7" : L = phi("L221" => %"v235", "L209" => %"pr.6")]:
    %"v241" : L = Sub #9223372036854775807, %"pr.4";
    %"v242" : W = (Cmp Sge L) %"pr.7", %"v241"
    => br %"v242" ? "L236" : "L238";
  @"L236":
    %"v245" : P = Copy $"__libc_errno";
    %"chk37" : A = (Check 0 4 Write 1) %"v245";
    store Ww [%"chk37" + 0] <- #75;
    %"chk38" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"iw_3.v3" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"iw_3.v4" : W = Or %"iw_3.v3", #32;
    %"chk39" : A = (Renew 0 4 Write 1) %"chk0", %"v6";
    store Ww [%"chk39" + 0] <- %"iw_3.v4"
    => goto "L116";
  @"L238":
    %"v253" : L = Add %"pr.4", %"pr.7";
    %"v254" : L = Add %"v253", #1;
    %"chk40" : A = (Check 0 8 Read 1) %"v2";
    %"v260" : L = (RawLoad LdL 0) %"chk40";
    %"v261" : W = (Cmp Ugt L) %"v254", %"v260"
    => br %"v261" ? "L255" : "L257";
  @"L255":
    %"v268" : L = (RawLoad LdL 0) %"chk40";
    %"v269" : L = Shl %"v268", #1;
    %"v270" : W = (Cmp Ult L) %"v254", %"v269"
    => br %"v270" ? "L263" : "L265";
  @"L263":
    %"v272" : L = (RawLoad LdL 0) %"chk40";
    %"v273" : L = Shl %"v272", #1
    => goto "L265";
  @"L265" [%"pr.8" : L = phi("L263" => %"v273", "L255" => %"v254")]:
    %"chk43" : A = (Renew 0 8 Read 8) %"chk21", %"v0";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk43";
    call %"v277" : P = $"realloc"(P %"v275", L %"pr.8");
    %"v282" : L = Ptoi %"v277";
    %"v284" : W = (Cmp Eq L) %"v282", %"v124"
    => br %"v284" ? "iw_4.start" : "L280";
  @"iw_4.start":
    %"chk44" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"iw_4.v3" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"iw_4.v4" : W = Or %"iw_4.v3", #32;
    %"chk45" : A = (Renew 0 4 Write 1) %"chk0", %"v6";
    store Ww [%"chk45" + 0] <- %"iw_4.v4"
    => goto "L116";
  @"L280":
    %"chk46" : A = (Renew 0 8 Write 8) %"chk21", %"v0";
    store.ptr [%"chk46" + 0] <- %"v277";
    %"chk47" : A = (Renew 0 8 Write 1) %"chk40", %"v2";
    store Wl [%"chk47" + 0] <- %"pr.8"
    => goto "L257";
  @"L257":
    %"chk48" : A = (Renew 0 8 Read 8) %"chk21", %"v0";
    %"v295" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v297" = %"v295" +p %"pr.4";
    %"v299" = %"v6" +p #8;
    %"chk49" : A = (Renew 0 8 Read 8) %"chk32", %"v299";
    %"v300" : P = (RawLoadPointer 0 load_effects) %"chk49";
    call %"v302" : P = $"__GI_memcpy"(P %"v297", P %"v300", L %"pr.7");
    %"chk50" : A = (Renew 0 8 Read 8) %"chk32", %"v299";
    %"v305" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v307" = %"v305" +p %"pr.7";
    %"chk51" : A = (Renew 0 8 Write 8) %"chk32", %"v299";
    store.ptr [%"chk51" + 0] <- %"v307"
    => br %"v227" ? "L319" : "L318";
  @"L318":
    call %"v321" : W = $"__GI___underflow"(P %"v6");
    %"v323" : W = (Cmp Eq W) %"v321", #4294967295
    => goto "L319";
  @"L319" [%"v325" : W = phi("L257" => #1, "L318" => %"v323")]:
    => br %"v325" ? "L212" : "L313";
  @"L313":
    %"v328" = %"v6" +p #16;
    %"chk52" : A = (Renew 0 8 Read 8) %"chk31", %"v328";
    %"v329" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"v331" = %"v6" +p #8;
    %"chk53" : A = (Renew 0 8 Read 8) %"chk32", %"v331";
    %"v332" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v333" : L = Ptoi %"v329";
    %"v334" : L = Ptoi %"v332";
    %"v335" : L = Sub %"v333", %"v334"
    => goto poll "L209";
  @"L212":
    %"chk54" : A = (Renew 0 8 Read 8) %"chk21", %"v0";
    %"v337" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v339" = %"v337" +p %"v253";
    %"chk55" : A = (Check 0 1 Write 1) %"v339";
    store Wb [%"chk55" + 0] <- #0
    => goto "L116";
  @"L116" [%"pr.1" : L = phi("L212" => %"v253", "iw_4.start" => #18446744073709551615, "L236" => #18446744073709551615, "L184" => #18446744073709551615, "iw_2.start" => #18446744073709551615, "L119" => #18446744073709551615, "L21" => #18446744073709551615)]:
    %"chk56" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"iw_5.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"iw_5.v10" : W = And %"iw_5.v9", #32768;
    %"iw_5.v11" : W = (Cmp Eq W) %"iw_5.v10", #0
    => br %"iw_5.v11" ? "iw_5.L5" : "L16";
  @"iw_5.L5":
    %"iw_5.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"iw_5.v17" : W = And %"iw_5.v16", #32768;
    %"iw_5.v18" : W = (Cmp Eq W) %"iw_5.v17", #0
    => br %"iw_5.v18" ? "iw_5.L19" : "L16";
  @"iw_5.L19":
    %"iw_5.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk58" : A = (Check 0 1 Read 1) %"iw_5.v25";
    %"iw_5.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk58";
    %"iw_5.v27" : W = (Cmp Ne W) %"iw_5.v26", #0
    => br %"iw_5.v27" ? "iw_5.L28" : "iw_5.L29";
  @"iw_5.L28":
    %"iw_5.v31" = %"v6" +p #136;
    %"chk59" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_5.v31";
    %"iw_5.v32" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"iw_5.v33" = %"iw_5.v32" +p #4;
    %"chk60" : A = (Check 0 4 Read 1) %"iw_5.v33";
    %"iw_5.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk60";
    %"iw_5.v35" : W = (Cmp Eq W) %"iw_5.v34", #0
    => goto "iw_5.L29";
  @"iw_5.L29" [%"iw_5.v37" : W = phi("iw_5.L19" => #0, "iw_5.L28" => %"iw_5.v35")]:
    => br %"iw_5.v37" ? "iw_5.L22" : "iw_5.L23";
  @"iw_5.L22":
    %"iw_5.v39" = %"v6" +p #136;
    %"chk61" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_5.v39";
    %"iw_5.v40" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"iw_5.v41" = %"iw_5.v40" +p #8;
    %"chk62" : A = (Check 0 8 Write 8) %"iw_5.v41";
    store.ptr [%"chk62" + 0] <- #0;
    %"chk63" : A = (Renew 0 8 Read 8) %"chk61", %"iw_5.v39";
    %"iw_5.v44" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"chk64" : A = (Check 0 4 Write 1) %"iw_5.v44";
    store Ww [%"chk64" + 0] <- #0
    => goto "L16";
  @"iw_5.L23":
    %"iw_5.v49" = %"v6" +p #136;
    %"chk65" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_5.v49";
    %"iw_5.v50" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"iw_5.v51" = %"iw_5.v50" +p #4;
    %"chk66" : A = (Check 0 4 Read 1) %"iw_5.v51";
    %"iw_5.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk66";
    %"iw_5.v53" : W = (Cmp Eq W) %"iw_5.v52", #0
    => br %"iw_5.v53" ? "iw_5.L45" : "iw_5.L46";
  @"iw_5.L45":
    %"iw_5.v55" = %"v6" +p #136;
    %"iw_5.v56" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"iw_5.v57" = %"iw_5.v56" +p #8;
    %"chk68" : A = (Check 0 8 Write 8) %"iw_5.v57";
    store.ptr [%"chk68" + 0] <- #0;
    %"chk69" : A = (Renew 0 8 Read 8) %"chk65", %"iw_5.v55";
    %"iw_5.v61" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"chk70" : A = (Check 0 4 Read 1) %"iw_5.v61";
    %"iw_5.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk70"
    => goto "iw_5.L66";
  @"iw_5.L66" [%"iw_5.v68" : W = phi("iw_5.L45" => %"iw_5.v65", "iw_5.L66" => %"iw_5.v69")]:
    %"chk71" : A = (HalfCheck Lower 0 4 Write 4) %"chk70", %"iw_5.v61";
    %"iw_5.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk71", %"iw_5.v68", #0;
    %"iw_5.v70" : W = (Cmp Eq W) %"iw_5.v69", %"iw_5.v68"
    => br %"iw_5.v70" ? "iw_5.L67" : poll "iw_5.L66";
  @"iw_5.L67":
    %"iw_5.v75" : W = (Cmp Sgt W) %"iw_5.v68", #1
    => br %"iw_5.v75" ? "iw_5.L78" : "L16";
  @"iw_5.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_5.v61")
    => goto "L16";
  @"iw_5.L46":
    %"iw_5.v90" = %"v6" +p #136;
    %"iw_5.v91" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"iw_5.v92" = %"iw_5.v91" +p #4;
    %"chk73" : A = (Check 0 4 Read 1) %"iw_5.v92";
    %"iw_5.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk73";
    %"iw_5.v94" : W = Sub %"iw_5.v93", #1;
    %"chk74" : A = (Renew 0 4 Write 1) %"chk73", %"iw_5.v92";
    store Ww [%"chk74" + 0] <- %"iw_5.v94"
    => goto "L16";
  @"L16":
    => ret %"pr.1"
} }.

Definition hello_image_fn___getclktck : func :=
  ir_fn{ "export" "__getclktck"() -> (RClass W) {
  @"start":
    %"v0" : P = Copy $"_dl_clktck";
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v1" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => br %"v1" ? "L4" : "L3";
  @"L3":
    => goto "L4";
  @"L4" [%"v5" : W = phi("L3" => #100, "start" => %"v1")]:
    => ret %"v5"
} }.

Definition hello_image_fn___getdtablesize : func :=
  ir_fn{ "export" "__getdtablesize"() -> (RClass W) {
  @"start":
    %"v0" : P = (Alloc 8) #16;
    call %"v4" : W = $"__GI___getrlimit"(W #7, P %"v0");
    %"v5" : W = (Cmp Slt W) %"v4", #0
    => br %"v5" ? "L3" : "L2";
  @"L2":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v6" : L = (RawLoad LdL 0) %"chk0"
    => goto "L3";
  @"L3" [%"v7" : L = phi("L2" => %"v6", "start" => #256)]:
    => ret %"v7"
} }.

Definition hello_image_fn___GI___getpagesize : func :=
  ir_fn{ "export" "__GI___getpagesize"() -> (RClass W) {
  @"start":
    %"v3" : P = Copy $"_dl_pagesize";
    %"chk0" : A = (Check 0 8 Read 1) %"v3";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v5" : W = (Cmp Ne L) %"v4", #0
    => br %"v5" ? "L2" : "L1";
  @"L1":
    %"v6" : P = Copy $"glibc_getpagesize#str.279";
    %"v7" : P = Copy $"glibc_getpagesize#str.280";
    %"v8" : P = Copy $"glibc_getpagesize#str.281";
    call void $"__libc_assert_fail"(P %"v6", P %"v7", W #28, P %"v8")
    => goto "L2";
  @"L2":
    %"v9" : P = Copy $"_dl_pagesize";
    %"chk1" : A = (Check 0 8 Read 1) %"v9";
    %"v10" : L = (RawLoad LdL 0) %"chk1"
    => ret %"v10"
} }.

Definition hello_image_fn___GI___get_nprocs : func :=
  ir_fn{ "export" "__GI___get_nprocs"() -> (RClass W) {
  @"start":
    %"v1" : P = Copy $"glibc_getsysstats#str.316";
    %"iw_1.v2" : P = (Alloc 4) #1024;
    %"iw_1.v5" : P = (Alloc 8) #8;
    %"iw_1.v7" : P = (Alloc 8) #8;
    %"iw_1.v36" : P = (Alloc 8) #8;
    %"iw_1.v4" = %"iw_1.v2" +p #1024;
    %"chk0" : A = (Check 0 8 Write 8) %"iw_1.v5";
    store.ptr [%"chk0" + 0] <- %"iw_1.v4";
    %"chk1" : A = (Check 0 8 Write 8) %"iw_1.v7";
    store.ptr [%"chk1" + 0] <- %"iw_1.v4";
    call %"iw_1.v14" : W = $"__GI___open_nocancel"(P %"v1", W #524288);
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v14", #4294967295
    => br %"iw_1.v22" ? "iw_1.L17" : "iw_1.L19";
  @"iw_1.L17":
    call %"iw_1.v25" : P = $"glibc_getsysstats#next_line"(W %"iw_1.v14", P %"iw_1.v2", P %"iw_1.v5", P %"iw_1.v7", P %"iw_1.v4");
    %"iw_1.v30" : L = Ptoi %"iw_1.v25";
    %"iw_1.v31" : L = Ptoi #0;
    %"iw_1.v32" : W = (Cmp Ne L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L33" : "iw_1.L28";
  @"iw_1.L33" [%"iw_1.pr.5" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L17" => #0); %"iw_1.pr.1" : P = phi("iw_1.L107" => %"iw_1.pr.2", "iw_1.L17" => %"iw_1.v25")]:
    call %"iw_1.v39" : L = $"__GI___isoc23_strtoul"(P %"iw_1.pr.1", P %"iw_1.v36", W #10);
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v36";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v45" : L = Ptoi %"iw_1.pr.1";
    %"iw_1.v46" : L = Ptoi %"iw_1.v44";
    %"iw_1.v47" : W = (Cmp Eq L) %"iw_1.v45", %"iw_1.v46"
    => br %"iw_1.v47" ? "iw_1.L28" : "iw_1.L42";
  @"iw_1.L42":
    %"iw_1.v54" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk4" : A = (Check 0 1 Read 1) %"iw_1.v54";
    %"iw_1.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_1.v56" : W = (Cmp Eq W) %"iw_1.v55", #45
    => br %"iw_1.v56" ? "iw_1.L51" : "iw_1.L53";
  @"iw_1.L51":
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v58" = %"iw_1.v57" +p #1;
    call %"iw_1.v60" : L = $"__GI___isoc23_strtoul"(P %"iw_1.v58", P %"iw_1.v36", W #10);
    %"chk6" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v65" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v66" : L = Ptoi %"iw_1.v58";
    %"iw_1.v67" : L = Ptoi %"iw_1.v65";
    %"iw_1.v68" : W = (Cmp Eq L) %"iw_1.v66", %"iw_1.v67"
    => br %"iw_1.v68" ? "iw_1.L28" : "iw_1.L53";
  @"iw_1.L53" [%"iw_1.pr.8" : L = phi("iw_1.L51" => %"iw_1.v60", "iw_1.L42" => %"iw_1.v39")]:
    %"iw_1.v75" : W = (Cmp Uge L) %"iw_1.pr.8", %"iw_1.v39"
    => br %"iw_1.v75" ? "iw_1.L70" : "iw_1.L72";
  @"iw_1.L70":
    %"iw_1.v79" : L = Sub %"iw_1.pr.8", %"iw_1.v39";
    %"iw_1.v80" : L = Add %"iw_1.v79", #1;
    %"iw_1.v81" : L = (Ext Sw) %"iw_1.pr.5";
    %"iw_1.v82" : L = Add %"iw_1.v81", %"iw_1.v80"
    => goto "iw_1.L72";
  @"iw_1.L72" [%"iw_1.pr.7" : W = phi("iw_1.L70" => %"iw_1.v82", "iw_1.L53" => %"iw_1.pr.5")]:
    %"chk7" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v83" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v7";
    %"iw_1.v88" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v89" : L = Ptoi %"iw_1.v83";
    %"iw_1.v90" : L = Ptoi %"iw_1.v88";
    %"iw_1.v91" : W = (Cmp Ult L) %"iw_1.v89", %"iw_1.v90"
    => br %"iw_1.v91" ? "iw_1.L92" : "iw_1.L93";
  @"iw_1.L92":
    %"chk9" : A = (Check 0 1 Read 1) %"iw_1.v83";
    %"iw_1.v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"iw_1.v96" : W = (Cmp Eq W) %"iw_1.v95", #44
    => goto "iw_1.L93";
  @"iw_1.L93" [%"iw_1.v98" : W = phi("iw_1.L72" => #0, "iw_1.L92" => %"iw_1.v96")]:
    => br %"iw_1.v98" ? "iw_1.L84" : "iw_1.L86";
  @"iw_1.L84":
    %"iw_1.v100" = %"iw_1.v83" +p #1
    => goto "iw_1.L86";
  @"iw_1.L86" [%"iw_1.pr.2" : P = phi("iw_1.L84" => %"iw_1.v100", "iw_1.L93" => %"iw_1.v83")]:
    %"iw_1.v102" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v103" : L = Ptoi %"iw_1.pr.2";
    %"iw_1.v104" : L = Ptoi %"iw_1.v102";
    %"iw_1.v105" : W = (Cmp Ult L) %"iw_1.v103", %"iw_1.v104"
    => br %"iw_1.v105" ? "iw_1.L106" : "iw_1.L107";
  @"iw_1.L106":
    %"chk11" : A = (Check 0 1 Read 1) %"iw_1.pr.2";
    %"iw_1.v109" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"iw_1.v110" : W = (Cmp Ne W) %"iw_1.v109", #10
    => goto "iw_1.L107";
  @"iw_1.L107" [%"iw_1.v112" : W = phi("iw_1.L86" => #0, "iw_1.L106" => %"iw_1.v110")]:
    => br %"iw_1.v112" ? poll "iw_1.L33" : "iw_1.L28";
  @"iw_1.L28" [%"iw_1.pr.4" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L33" => #0, "iw_1.L51" => #0, "iw_1.L17" => #0)]:
    call void $"__GI___close_nocancel_nostatus"(W %"iw_1.v14")
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.pr.3" : W = phi("iw_1.L28" => %"iw_1.pr.4", "start" => #0)]:
    %"v7" : W = (Cmp Ne W) %"iw_1.pr.3", #0
    => br %"v7" ? "L3" : "iw_2.start";
  @"L3":
    => ret %"iw_1.pr.3";
  @"iw_2.start":
    %"iw_2.iw_1.v0" : P = (Alloc 4) #1024;
    %"iw_2.iw_1.v3" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v5" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v2" = %"iw_2.iw_1.v0" +p #1024;
    %"chk12" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v3";
    store.ptr [%"chk12" + 0] <- %"iw_2.iw_1.v2";
    %"chk13" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v5";
    store.ptr [%"chk13" + 0] <- %"iw_2.iw_1.v2";
    %"iw_2.iw_1.v11" : P = Copy $"glibc_getsysstats#str.314";
    call %"iw_2.iw_1.v13" : W = $"__GI___open_nocancel"(P %"iw_2.iw_1.v11", W #524288);
    %"iw_2.iw_1.v19" : W = (Cmp Ne W) %"iw_2.iw_1.v13", #4294967295
    => br %"iw_2.iw_1.v19" ? "iw_2.iw_1.L21" : "iw_2.iw_1.L16";
  @"iw_2.iw_1.L21" [%"iw_2.iw_1.pr.2" : W = phi("iw_2.start" => #0, "iw_2.iw_1.L48" => %"iw_2.iw_1.pr.2", "iw_2.iw_1.L38" => %"iw_2.iw_1.v54")]:
    call %"iw_2.iw_1.v26" : P = $"glibc_getsysstats#next_line"(W %"iw_2.iw_1.v13", P %"iw_2.iw_1.v0", P %"iw_2.iw_1.v3", P %"iw_2.iw_1.v5", P %"iw_2.iw_1.v2");
    %"iw_2.iw_1.v27" : L = Ptoi %"iw_2.iw_1.v26";
    %"iw_2.iw_1.v28" : L = Ptoi #0;
    %"iw_2.iw_1.v29" : W = (Cmp Ne L) %"iw_2.iw_1.v27", %"iw_2.iw_1.v28"
    => br %"iw_2.iw_1.v29" ? "iw_2.iw_1.L22" : "iw_2.iw_1.L23";
  @"iw_2.iw_1.L22":
    %"iw_2.iw_1.v34" : P = Copy $"glibc_getsysstats#str.315";
    call %"iw_2.iw_1.v35" : W = $"__GI_strncmp"(P %"iw_2.iw_1.v26", P %"iw_2.iw_1.v34", L #3);
    %"iw_2.iw_1.v36" : W = (Cmp Ne W) %"iw_2.iw_1.v35", #0
    => br %"iw_2.iw_1.v36" ? "iw_2.iw_1.L23" : "iw_2.iw_1.L31";
  @"iw_2.iw_1.L31":
    %"iw_2.iw_1.v43" = %"iw_2.iw_1.v26" +p #3;
    %"chk14" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v43";
    %"iw_2.iw_1.v44" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.iw_1.v46" : W = (Cmp Sge W) %"iw_2.iw_1.v44", #48
    => br %"iw_2.iw_1.v46" ? "iw_2.iw_1.L47" : "iw_2.iw_1.L48";
  @"iw_2.iw_1.L47":
    %"iw_2.iw_1.v50" : W = (Cmp Sle W) %"iw_2.iw_1.v44", #57
    => goto "iw_2.iw_1.L48";
  @"iw_2.iw_1.L48" [%"iw_2.iw_1.v52" : W = phi("iw_2.iw_1.L31" => #0, "iw_2.iw_1.L47" => %"iw_2.iw_1.v50")]:
    => br %"iw_2.iw_1.v52" ? "iw_2.iw_1.L38" : poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L38":
    %"iw_2.iw_1.v54" : W = Add %"iw_2.iw_1.pr.2", #1
    => goto poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L23":
    call void $"__GI___close_nocancel_nostatus"(W %"iw_2.iw_1.v13")
    => goto "iw_2.iw_1.L16";
  @"iw_2.iw_1.L16" [%"iw_2.iw_1.pr.1" : W = phi("iw_2.iw_1.L23" => %"iw_2.iw_1.pr.2", "iw_2.start" => #0)]:
    %"iw_2.v6" : W = (Cmp Ne W) %"iw_2.iw_1.pr.1", #0
    => br %"iw_2.v6" ? "iw_2.join" : "iw_2.iw_2.start";
  @"iw_2.iw_2.start":
    %"iw_2.iw_2.v0" : P = (Alloc 8) #4096;
    call %"iw_2.iw_2.v2" : W = $"zsys_sched_getaffinity"(W #0, L #4096, P %"iw_2.iw_2.v0");
    %"iw_2.iw_2.v7" : W = (Cmp Sgt W) %"iw_2.iw_2.v2", #0
    => br %"iw_2.iw_2.v7" ? "iw_2.iw_2.L3" : "iw_2.iw_2.L4";
  @"iw_2.iw_2.L3":
    %"iw_2.iw_2.v9" : L = (Ext Sw) %"iw_2.iw_2.v2";
    call %"iw_2.iw_2.v10" : W = $"__GI___sched_cpucount"(L %"iw_2.iw_2.v9", P %"iw_2.iw_2.v0")
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.L4":
    %"iw_2.iw_2.v17" : W = (Cmp Eq W) %"iw_2.iw_2.v2", #4294967274
    => br %"iw_2.iw_2.v17" ? "iw_2.iw_2.join" : "iw_2.iw_2.L5";
  @"iw_2.iw_2.L5":
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.join" [%"iw_2.v9" : W = phi("iw_2.iw_2.L3" => %"iw_2.iw_2.v10", "iw_2.iw_2.L5" => #0, "iw_2.iw_2.L4" => #32768)]:
    %"iw_2.v14" : W = (Cmp Ne W) %"iw_2.v9", #0
    => br %"iw_2.v14" ? "iw_2.join" : "iw_2.L12";
  @"iw_2.L12":
    => goto "iw_2.join";
  @"iw_2.join" [%"v10" : W = phi("iw_2.L12" => #2, "iw_2.iw_1.L16" => %"iw_2.iw_1.pr.1", "iw_2.iw_2.join" => %"iw_2.v9")]:
    => ret %"v10"
} }.

Definition hello_image_fn___GI___get_nprocs_conf : func :=
  ir_fn{ "export" "__GI___get_nprocs_conf"() -> (RClass W) {
  @"start":
    %"v1" : P = Copy $"glibc_getsysstats#str.317";
    %"iw_1.v2" : P = (Alloc 4) #1024;
    %"iw_1.v5" : P = (Alloc 8) #8;
    %"iw_1.v7" : P = (Alloc 8) #8;
    %"iw_1.v36" : P = (Alloc 8) #8;
    %"iw_1.v4" = %"iw_1.v2" +p #1024;
    %"chk0" : A = (Check 0 8 Write 8) %"iw_1.v5";
    store.ptr [%"chk0" + 0] <- %"iw_1.v4";
    %"chk1" : A = (Check 0 8 Write 8) %"iw_1.v7";
    store.ptr [%"chk1" + 0] <- %"iw_1.v4";
    call %"iw_1.v14" : W = $"__GI___open_nocancel"(P %"v1", W #524288);
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v14", #4294967295
    => br %"iw_1.v22" ? "iw_1.L17" : "iw_1.L19";
  @"iw_1.L17":
    call %"iw_1.v25" : P = $"glibc_getsysstats#next_line"(W %"iw_1.v14", P %"iw_1.v2", P %"iw_1.v5", P %"iw_1.v7", P %"iw_1.v4");
    %"iw_1.v30" : L = Ptoi %"iw_1.v25";
    %"iw_1.v31" : L = Ptoi #0;
    %"iw_1.v32" : W = (Cmp Ne L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L33" : "iw_1.L28";
  @"iw_1.L33" [%"iw_1.pr.5" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L17" => #0); %"iw_1.pr.1" : P = phi("iw_1.L107" => %"iw_1.pr.2", "iw_1.L17" => %"iw_1.v25")]:
    call %"iw_1.v39" : L = $"__GI___isoc23_strtoul"(P %"iw_1.pr.1", P %"iw_1.v36", W #10);
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v36";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v45" : L = Ptoi %"iw_1.pr.1";
    %"iw_1.v46" : L = Ptoi %"iw_1.v44";
    %"iw_1.v47" : W = (Cmp Eq L) %"iw_1.v45", %"iw_1.v46"
    => br %"iw_1.v47" ? "iw_1.L28" : "iw_1.L42";
  @"iw_1.L42":
    %"iw_1.v54" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk4" : A = (Check 0 1 Read 1) %"iw_1.v54";
    %"iw_1.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_1.v56" : W = (Cmp Eq W) %"iw_1.v55", #45
    => br %"iw_1.v56" ? "iw_1.L51" : "iw_1.L53";
  @"iw_1.L51":
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v58" = %"iw_1.v57" +p #1;
    call %"iw_1.v60" : L = $"__GI___isoc23_strtoul"(P %"iw_1.v58", P %"iw_1.v36", W #10);
    %"chk6" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v65" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v66" : L = Ptoi %"iw_1.v58";
    %"iw_1.v67" : L = Ptoi %"iw_1.v65";
    %"iw_1.v68" : W = (Cmp Eq L) %"iw_1.v66", %"iw_1.v67"
    => br %"iw_1.v68" ? "iw_1.L28" : "iw_1.L53";
  @"iw_1.L53" [%"iw_1.pr.8" : L = phi("iw_1.L51" => %"iw_1.v60", "iw_1.L42" => %"iw_1.v39")]:
    %"iw_1.v75" : W = (Cmp Uge L) %"iw_1.pr.8", %"iw_1.v39"
    => br %"iw_1.v75" ? "iw_1.L70" : "iw_1.L72";
  @"iw_1.L70":
    %"iw_1.v79" : L = Sub %"iw_1.pr.8", %"iw_1.v39";
    %"iw_1.v80" : L = Add %"iw_1.v79", #1;
    %"iw_1.v81" : L = (Ext Sw) %"iw_1.pr.5";
    %"iw_1.v82" : L = Add %"iw_1.v81", %"iw_1.v80"
    => goto "iw_1.L72";
  @"iw_1.L72" [%"iw_1.pr.7" : W = phi("iw_1.L70" => %"iw_1.v82", "iw_1.L53" => %"iw_1.pr.5")]:
    %"chk7" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v83" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v7";
    %"iw_1.v88" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v89" : L = Ptoi %"iw_1.v83";
    %"iw_1.v90" : L = Ptoi %"iw_1.v88";
    %"iw_1.v91" : W = (Cmp Ult L) %"iw_1.v89", %"iw_1.v90"
    => br %"iw_1.v91" ? "iw_1.L92" : "iw_1.L93";
  @"iw_1.L92":
    %"chk9" : A = (Check 0 1 Read 1) %"iw_1.v83";
    %"iw_1.v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"iw_1.v96" : W = (Cmp Eq W) %"iw_1.v95", #44
    => goto "iw_1.L93";
  @"iw_1.L93" [%"iw_1.v98" : W = phi("iw_1.L72" => #0, "iw_1.L92" => %"iw_1.v96")]:
    => br %"iw_1.v98" ? "iw_1.L84" : "iw_1.L86";
  @"iw_1.L84":
    %"iw_1.v100" = %"iw_1.v83" +p #1
    => goto "iw_1.L86";
  @"iw_1.L86" [%"iw_1.pr.2" : P = phi("iw_1.L84" => %"iw_1.v100", "iw_1.L93" => %"iw_1.v83")]:
    %"iw_1.v102" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v103" : L = Ptoi %"iw_1.pr.2";
    %"iw_1.v104" : L = Ptoi %"iw_1.v102";
    %"iw_1.v105" : W = (Cmp Ult L) %"iw_1.v103", %"iw_1.v104"
    => br %"iw_1.v105" ? "iw_1.L106" : "iw_1.L107";
  @"iw_1.L106":
    %"chk11" : A = (Check 0 1 Read 1) %"iw_1.pr.2";
    %"iw_1.v109" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"iw_1.v110" : W = (Cmp Ne W) %"iw_1.v109", #10
    => goto "iw_1.L107";
  @"iw_1.L107" [%"iw_1.v112" : W = phi("iw_1.L86" => #0, "iw_1.L106" => %"iw_1.v110")]:
    => br %"iw_1.v112" ? poll "iw_1.L33" : "iw_1.L28";
  @"iw_1.L28" [%"iw_1.pr.4" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L33" => #0, "iw_1.L51" => #0, "iw_1.L17" => #0)]:
    call void $"__GI___close_nocancel_nostatus"(W %"iw_1.v14")
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.pr.3" : W = phi("iw_1.L28" => %"iw_1.pr.4", "start" => #0)]:
    %"v7" : W = (Cmp Ne W) %"iw_1.pr.3", #0
    => br %"v7" ? "L3" : "iw_2.start";
  @"L3":
    => ret %"iw_1.pr.3";
  @"iw_2.start":
    %"iw_2.iw_1.v0" : P = (Alloc 4) #1024;
    %"iw_2.iw_1.v3" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v5" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v2" = %"iw_2.iw_1.v0" +p #1024;
    %"chk12" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v3";
    store.ptr [%"chk12" + 0] <- %"iw_2.iw_1.v2";
    %"chk13" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v5";
    store.ptr [%"chk13" + 0] <- %"iw_2.iw_1.v2";
    %"iw_2.iw_1.v11" : P = Copy $"glibc_getsysstats#str.314";
    call %"iw_2.iw_1.v13" : W = $"__GI___open_nocancel"(P %"iw_2.iw_1.v11", W #524288);
    %"iw_2.iw_1.v19" : W = (Cmp Ne W) %"iw_2.iw_1.v13", #4294967295
    => br %"iw_2.iw_1.v19" ? "iw_2.iw_1.L21" : "iw_2.iw_1.L16";
  @"iw_2.iw_1.L21" [%"iw_2.iw_1.pr.2" : W = phi("iw_2.start" => #0, "iw_2.iw_1.L48" => %"iw_2.iw_1.pr.2", "iw_2.iw_1.L38" => %"iw_2.iw_1.v54")]:
    call %"iw_2.iw_1.v26" : P = $"glibc_getsysstats#next_line"(W %"iw_2.iw_1.v13", P %"iw_2.iw_1.v0", P %"iw_2.iw_1.v3", P %"iw_2.iw_1.v5", P %"iw_2.iw_1.v2");
    %"iw_2.iw_1.v27" : L = Ptoi %"iw_2.iw_1.v26";
    %"iw_2.iw_1.v28" : L = Ptoi #0;
    %"iw_2.iw_1.v29" : W = (Cmp Ne L) %"iw_2.iw_1.v27", %"iw_2.iw_1.v28"
    => br %"iw_2.iw_1.v29" ? "iw_2.iw_1.L22" : "iw_2.iw_1.L23";
  @"iw_2.iw_1.L22":
    %"iw_2.iw_1.v34" : P = Copy $"glibc_getsysstats#str.315";
    call %"iw_2.iw_1.v35" : W = $"__GI_strncmp"(P %"iw_2.iw_1.v26", P %"iw_2.iw_1.v34", L #3);
    %"iw_2.iw_1.v36" : W = (Cmp Ne W) %"iw_2.iw_1.v35", #0
    => br %"iw_2.iw_1.v36" ? "iw_2.iw_1.L23" : "iw_2.iw_1.L31";
  @"iw_2.iw_1.L31":
    %"iw_2.iw_1.v43" = %"iw_2.iw_1.v26" +p #3;
    %"chk14" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v43";
    %"iw_2.iw_1.v44" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.iw_1.v46" : W = (Cmp Sge W) %"iw_2.iw_1.v44", #48
    => br %"iw_2.iw_1.v46" ? "iw_2.iw_1.L47" : "iw_2.iw_1.L48";
  @"iw_2.iw_1.L47":
    %"iw_2.iw_1.v50" : W = (Cmp Sle W) %"iw_2.iw_1.v44", #57
    => goto "iw_2.iw_1.L48";
  @"iw_2.iw_1.L48" [%"iw_2.iw_1.v52" : W = phi("iw_2.iw_1.L31" => #0, "iw_2.iw_1.L47" => %"iw_2.iw_1.v50")]:
    => br %"iw_2.iw_1.v52" ? "iw_2.iw_1.L38" : poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L38":
    %"iw_2.iw_1.v54" : W = Add %"iw_2.iw_1.pr.2", #1
    => goto poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L23":
    call void $"__GI___close_nocancel_nostatus"(W %"iw_2.iw_1.v13")
    => goto "iw_2.iw_1.L16";
  @"iw_2.iw_1.L16" [%"iw_2.iw_1.pr.1" : W = phi("iw_2.iw_1.L23" => %"iw_2.iw_1.pr.2", "iw_2.start" => #0)]:
    %"iw_2.v6" : W = (Cmp Ne W) %"iw_2.iw_1.pr.1", #0
    => br %"iw_2.v6" ? "iw_2.join" : "iw_2.iw_2.start";
  @"iw_2.iw_2.start":
    %"iw_2.iw_2.v0" : P = (Alloc 8) #4096;
    call %"iw_2.iw_2.v2" : W = $"zsys_sched_getaffinity"(W #0, L #4096, P %"iw_2.iw_2.v0");
    %"iw_2.iw_2.v7" : W = (Cmp Sgt W) %"iw_2.iw_2.v2", #0
    => br %"iw_2.iw_2.v7" ? "iw_2.iw_2.L3" : "iw_2.iw_2.L4";
  @"iw_2.iw_2.L3":
    %"iw_2.iw_2.v9" : L = (Ext Sw) %"iw_2.iw_2.v2";
    call %"iw_2.iw_2.v10" : W = $"__GI___sched_cpucount"(L %"iw_2.iw_2.v9", P %"iw_2.iw_2.v0")
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.L4":
    %"iw_2.iw_2.v17" : W = (Cmp Eq W) %"iw_2.iw_2.v2", #4294967274
    => br %"iw_2.iw_2.v17" ? "iw_2.iw_2.join" : "iw_2.iw_2.L5";
  @"iw_2.iw_2.L5":
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.join" [%"iw_2.v9" : W = phi("iw_2.iw_2.L3" => %"iw_2.iw_2.v10", "iw_2.iw_2.L5" => #0, "iw_2.iw_2.L4" => #32768)]:
    %"iw_2.v14" : W = (Cmp Ne W) %"iw_2.v9", #0
    => br %"iw_2.v14" ? "iw_2.join" : "iw_2.L12";
  @"iw_2.L12":
    => goto "iw_2.join";
  @"iw_2.join" [%"v10" : W = phi("iw_2.L12" => #2, "iw_2.iw_1.L16" => %"iw_2.iw_1.pr.1", "iw_2.iw_2.join" => %"iw_2.v9")]:
    => ret %"v10"
} }.

Definition hello_image_fn___GI___get_phys_pages : func :=
  ir_fn{ "export" "__GI___get_phys_pages"() -> (RClass L) {
  @"start":
    %"v0" : P = (Alloc 8) #112;
    call %"v1" : W = $"__sysinfo"(P %"v0");
    %"v2" = %"v0" +p #32;
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v3" : L = (RawLoad LdL 0) %"chk0";
    %"v4" = %"v0" +p #104;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v4";
    %"v5" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    call %"iw_1.v5" : W = $"__GI___getpagesize"();
    %"iw_1.v6" : L = (Ext Sw) %"iw_1.v5"
    => goto "iw_1.L7";
  @"iw_1.L7" [%"iw_1.pr.4" : L = phi("iw_1.L8" => %"iw_1.v21", "start" => %"iw_1.v6"); %"iw_1.pr.2" : W = phi("iw_1.L8" => %"iw_1.v19", "start" => %"v5")]:
    %"iw_1.v11" : W = (Cmp Ugt W) %"iw_1.pr.2", #1
    => br %"iw_1.v11" ? "iw_1.L12" : "iw_1.L13";
  @"iw_1.L12":
    %"iw_1.v15" : W = (Cmp Ugt L) %"iw_1.pr.4", #1
    => goto "iw_1.L13";
  @"iw_1.L13" [%"iw_1.v17" : W = phi("iw_1.L7" => #0, "iw_1.L12" => %"iw_1.v15")]:
    => br %"iw_1.v17" ? "iw_1.L8" : "iw_1.L9";
  @"iw_1.L8":
    %"iw_1.v19" : W = Shr %"iw_1.pr.2", #1;
    %"iw_1.v21" : L = Shr %"iw_1.pr.4", #1
    => goto poll "iw_1.L7";
  @"iw_1.L9":
    %"iw_1.v24" : L = (Ext Uw) %"iw_1.pr.2";
    %"iw_1.v25" : L = Mul %"v3", %"iw_1.v24"
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.pr.3" : L = phi("iw_1.L27" => %"iw_1.v32", "iw_1.L9" => %"iw_1.pr.4"); %"iw_1.pr.1" : L = phi("iw_1.L27" => %"iw_1.v34", "iw_1.L9" => %"iw_1.v25")]:
    %"iw_1.v30" : W = (Cmp Ugt L) %"iw_1.pr.3", #1
    => br %"iw_1.v30" ? "iw_1.L27" : "iw_1.join";
  @"iw_1.L27":
    %"iw_1.v32" : L = Shr %"iw_1.pr.3", #1;
    %"iw_1.v34" : L = Shr %"iw_1.pr.1", #1
    => goto poll "iw_1.L26";
  @"iw_1.join":
    => ret %"iw_1.pr.1"
} }.

Definition hello_image_fn___GI___get_avphys_pages : func :=
  ir_fn{ "export" "__GI___get_avphys_pages"() -> (RClass L) {
  @"start":
    %"v0" : P = (Alloc 8) #112;
    call %"v1" : W = $"__sysinfo"(P %"v0");
    %"v2" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v3" : L = (RawLoad LdL 0) %"chk0";
    %"v4" = %"v0" +p #104;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v4";
    %"v5" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    call %"iw_1.v5" : W = $"__GI___getpagesize"();
    %"iw_1.v6" : L = (Ext Sw) %"iw_1.v5"
    => goto "iw_1.L7";
  @"iw_1.L7" [%"iw_1.pr.4" : L = phi("iw_1.L8" => %"iw_1.v21", "start" => %"iw_1.v6"); %"iw_1.pr.2" : W = phi("iw_1.L8" => %"iw_1.v19", "start" => %"v5")]:
    %"iw_1.v11" : W = (Cmp Ugt W) %"iw_1.pr.2", #1
    => br %"iw_1.v11" ? "iw_1.L12" : "iw_1.L13";
  @"iw_1.L12":
    %"iw_1.v15" : W = (Cmp Ugt L) %"iw_1.pr.4", #1
    => goto "iw_1.L13";
  @"iw_1.L13" [%"iw_1.v17" : W = phi("iw_1.L7" => #0, "iw_1.L12" => %"iw_1.v15")]:
    => br %"iw_1.v17" ? "iw_1.L8" : "iw_1.L9";
  @"iw_1.L8":
    %"iw_1.v19" : W = Shr %"iw_1.pr.2", #1;
    %"iw_1.v21" : L = Shr %"iw_1.pr.4", #1
    => goto poll "iw_1.L7";
  @"iw_1.L9":
    %"iw_1.v24" : L = (Ext Uw) %"iw_1.pr.2";
    %"iw_1.v25" : L = Mul %"v3", %"iw_1.v24"
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.pr.3" : L = phi("iw_1.L27" => %"iw_1.v32", "iw_1.L9" => %"iw_1.pr.4"); %"iw_1.pr.1" : L = phi("iw_1.L27" => %"iw_1.v34", "iw_1.L9" => %"iw_1.v25")]:
    %"iw_1.v30" : W = (Cmp Ugt L) %"iw_1.pr.3", #1
    => br %"iw_1.v30" ? "iw_1.L27" : "iw_1.join";
  @"iw_1.L27":
    %"iw_1.v32" : L = Shr %"iw_1.pr.3", #1;
    %"iw_1.v34" : L = Shr %"iw_1.pr.1", #1
    => goto poll "iw_1.L26";
  @"iw_1.join":
    => ret %"iw_1.pr.1"
} }.

Definition hello_image_fn___get_child_max : func :=
  ir_fn{ "export" "__get_child_max"() -> (RClass L) {
  @"start":
    %"v0" : P = (Alloc 8) #16;
    call %"v4" : W = $"__GI___getrlimit"(W #6, P %"v0");
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => br %"v5" ? "L6" : "L7";
  @"L6":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v8" : L = (RawLoad LdL 0) %"chk0";
    %"v11" : W = (Cmp Ne L) %"v8", #18446744073709551615
    => goto "L7";
  @"L7" [%"v13" : W = phi("start" => #0, "L6" => %"v11")]:
    => br %"v13" ? "L1" : "L3";
  @"L1":
    %"chk1" : A = (Check 0 8 Read 1) %"v0";
    %"v14" : L = (RawLoad LdL 0) %"chk1"
    => ret %"v14";
  @"L3":
    => ret #18446744073709551615
} }.

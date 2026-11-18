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

Definition hello_image_fn___gconv_find_shlib : func :=
  ir_fn{ "export" "__gconv_find_shlib"(P %"v0") -> (RClass P) {
  @"start":
    %"v1" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v1";
    store.ptr [%"chk0" + 0] <- %"v0";
    %"v4" : P = Copy $"glibc_gconv_dl#loaded";
    %"v5" : P = Copy $"glibc_gconv_dl#known_compare";
    call %"v6" : P = $"__GI___tfind"(P %"v1", P %"v4", P %"v5");
    %"v11" : L = Ptoi %"v6";
    %"v12" : L = Ptoi #0;
    %"v13" : W = (Cmp Eq L) %"v11", %"v12"
    => br %"v13" ? "L7" : "L8";
  @"L7":
    %"chk1" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v16" : L = $"__GI_strlen"(P %"v15");
    %"v17" : L = Add %"v16", #1;
    %"v19" : L = Add %"v17", #48;
    call %"v20" : P = $"malloc"(L %"v19");
    %"v25" : L = Ptoi %"v20";
    %"v27" : W = (Cmp Ne L) %"v25", %"v12"
    => br %"v27" ? "L21" : "L9";
  @"L21":
    %"v30" = %"v20" +p #48;
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v1";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v33" : P = $"__GI_memcpy"(P %"v30", P %"v31", L %"v17");
    %"chk3" : A = (Check 0 8 Write 8) %"v20";
    store.ptr [%"chk3" + 0] <- %"v33";
    %"v35" = %"v20" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk3", %"v35";
    store Ww [%"chk4" + 0] <- #4294967293;
    %"v39" = %"v20" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v39";
    store.ptr [%"chk5" + 0] <- #0;
    %"v44" : P = Copy $"glibc_gconv_dl#loaded";
    %"v45" : P = Copy $"glibc_gconv_dl#known_compare";
    call %"v46" : P = $"__GI___tsearch"(P %"v20", P %"v44", P %"v45");
    %"v47" : L = Ptoi %"v46";
    %"v49" : W = (Cmp Eq L) %"v47", %"v12"
    => br %"v49" ? "L40" : "L9";
  @"L40":
    call void $"free"(P %"v20")
    => goto "L9";
  @"L8":
    %"chk6" : A = (Check 0 8 Read 8) %"v6";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk6"
    => goto "L9";
  @"L9" [%"pr.7" : P = phi("L8" => %"v54", "L40" => #0, "L21" => %"v20", "L7" => %"v20")]:
    %"v59" : L = Ptoi %"pr.7";
    %"v61" : W = (Cmp Ne L) %"v59", %"v12"
    => br %"v61" ? "L55" : "L57";
  @"L55":
    %"v66" = %"pr.7" +p #8;
    %"chk7" : A = (Check 0 4 Read 1) %"v66";
    %"v67" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v69" : W = (Cmp Slt W) %"v67", #4294967294
    => br %"v69" ? "L62" : "L63";
  @"L62":
    %"v74" = %"pr.7" +p #16;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v76" : L = Ptoi %"v75";
    %"v78" : W = (Cmp Eq L) %"v76", %"v12"
    => br %"v78" ? "L72" : "L71";
  @"L71":
    %"v79" : P = Copy $"glibc_gconv_dl#str.274";
    %"v80" : P = Copy $"glibc_gconv_dl#str.275";
    %"v81" : P = Copy $"glibc_gconv_dl#str.276";
    call void $"__libc_assert_fail"(P %"v79", P %"v80", W #113, P %"v81")
    => goto "L72";
  @"L72":
    %"v83" = %"pr.7" +p #16;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk7", %"pr.7";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call %"v86" : P = $"__libc_dlopen_mode"(P %"v85", W #2);
    %"chk10" : A = (Renew 0 8 Write 8) %"chk8", %"v83";
    store.ptr [%"chk10" + 0] <- %"v86";
    %"chk11" : A = (Renew 0 8 Read 8) %"chk8", %"v83";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v93" : L = Ptoi %"v92";
    %"v95" : W = (Cmp Ne L) %"v93", %"v12"
    => br %"v95" ? "L87" : "L57";
  @"L87":
    %"v97" = %"pr.7" +p #24;
    %"v99" = %"pr.7" +p #16;
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v101" : P = Copy $"glibc_gconv_dl#str.277";
    call %"v102" : P = $"__libc_dlsym"(P %"v100", P %"v101");
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v97";
    store.ptr [%"chk13" + 0] <- %"v102";
    %"chk14" : A = (Renew 0 8 Read 8) %"chk13", %"v97";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v109" : L = Ptoi %"v108";
    %"v111" : W = (Cmp Eq L) %"v109", %"v12"
    => br %"v111" ? "L103" : "L104";
  @"L103":
    call void $"__gconv_release_shlib"(P %"pr.7")
    => goto "L57";
  @"L104":
    %"v114" = %"pr.7" +p #32;
    %"v116" = %"pr.7" +p #16;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk8", %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v118" : P = Copy $"glibc_gconv_dl#str.278";
    call %"v119" : P = $"__libc_dlsym"(P %"v117", P %"v118");
    %"chk16" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v114";
    store.ptr [%"chk16" + 0] <- %"v119";
    %"v121" = %"pr.7" +p #40;
    %"chk17" : A = (Renew 0 8 Read 8) %"chk8", %"v116";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v125" : P = Copy $"glibc_gconv_dl#str.279";
    call %"v126" : P = $"__libc_dlsym"(P %"v124", P %"v125");
    %"chk18" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v121";
    store.ptr [%"chk18" + 0] <- %"v126";
    %"v128" = %"pr.7" +p #24;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk13", %"v128";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Renew 0 8 Read 8) %"chk16", %"v114";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Renew 0 8 Read 8) %"chk18", %"v121";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v137" = %"pr.7" +p #8;
    %"chk22" : A = (Renew 0 4 Write 1) %"chk7", %"v137";
    store Ww [%"chk22" + 0] <- #1
    => goto "L57";
  @"L63":
    %"v142" = %"pr.7" +p #16;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"v142";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v144" : L = Ptoi %"v143";
    %"v146" : W = (Cmp Ne L) %"v144", %"v12"
    => br %"v146" ? "L138" : "L57";
  @"L138":
    %"v148" = %"pr.7" +p #8;
    %"v154" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v155" : W = Add %"v154", #1;
    %"v156" : W = (Cmp Sgt W) %"v155", #1
    => br %"v156" ? "L149" : "L151";
  @"L149":
    %"v158" = %"pr.7" +p #8;
    %"v159" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v160" : W = Add %"v159", #1
    => goto "L151";
  @"L151" [%"v161" : W = phi("L149" => %"v160", "L138" => #1)]:
    %"chk26" : A = (Renew 0 4 Write 1) %"chk7", %"v148";
    store Ww [%"chk26" + 0] <- %"v161"
    => goto "L57";
  @"L57" [%"pr.4" : P = phi("L103" => #0, "L104" => %"pr.7", "L72" => #0, "L151" => %"pr.7", "L63" => %"pr.7", "L9" => %"pr.7")]:
    => ret %"pr.4"
} }.

Definition hello_image_fn___gconv_release_shlib : func :=
  ir_fn{ "export" "__gconv_release_shlib"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_gconv_dl#loaded";
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v3" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v4" : P = Copy $"glibc_gconv_dl#do_release_shlib";
    call void $"__GI___twalk_r"(P %"v3", P %"v4", P %"v0")
    => ret void
} }.

Definition hello_image_fn___GI___gconv_open : func :=
  ir_fn{ "export" "__GI___gconv_open"(P %"v0", P %"v2", W %"v4") -> (RClass W) {
  @"start":
    %"v6" : P = (Alloc 8) #8;
    %"v7" : P = (Alloc 8) #8;
    %"v17" = %"v0" +p #16;
    %"chk0" : A = (Check 0 1 Read 1) %"v17";
    %"v18" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"v23" = %"v0" +p #17;
    %"chk1" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v23";
    %"v24" : W = (RawLoad (LdNarrow Ub) 0) %"chk1"
    => br %"v24" ? "L21" : "L20";
  @"L20":
    => goto "L21";
  @"L21" [%"pr.14" : W = phi("L20" => #0, "start" => #2)]:
    %"v28" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v36" : P = Copy $"glibc_gconv_open#str.243";
    call %"v37" : W = $"__GI_strcmp"(P %"v29", P %"v36");
    %"v38" : W = (Cmp Eq W) %"v37", #0
    => br %"v38" ? "L32" : "L34";
  @"L32":
    %"v40" : P = Copy $"__libc_tsd_LOCALE";
    %"chk4" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v41";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v44" = %"v43" +p #56;
    %"v48" = %"v44" +p #112;
    %"chk6" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v52" : L = $"__GI_strlen"(P %"v49");
    %"v55" : L = Add %"v52", #3;
    %"v56" : P = (Alloc 16) %"v55";
    call %"v60" : P = $"__GI_mempcpy"(P %"v56", P %"v49", L %"v52");
    %"v61" : P = Copy $"glibc_gconv_open#str.243";
    call %"v62" : P = $"__GI_memcpy"(P %"v60", P %"v61", L #3)
    => goto "L34";
  @"L34" [%"pr.15" : P = phi("L32" => %"v56", "L21" => %"v29")]:
    %"v67" : P = Copy $"glibc_gconv_open#str.243";
    call %"v68" : W = $"__GI_strcmp"(P %"v31", P %"v67");
    %"v69" : W = (Cmp Eq W) %"v68", #0
    => br %"v69" ? "L63" : "L65";
  @"L63":
    %"v71" : P = Copy $"__libc_tsd_LOCALE";
    %"chk7" : A = (Check 0 8 Read 8) %"v71";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"v72";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v75" = %"v74" +p #56;
    %"v79" = %"v75" +p #112;
    %"chk9" : A = (Check 0 8 Read 8) %"v79";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call %"v83" : L = $"__GI_strlen"(P %"v80");
    %"v86" : L = Add %"v83", #3;
    %"v87" : P = (Alloc 16) %"v86";
    call %"v91" : P = $"__GI_mempcpy"(P %"v87", P %"v80", L %"v83");
    %"v92" : P = Copy $"glibc_gconv_open#str.243";
    call %"v93" : P = $"__GI_memcpy"(P %"v91", P %"v92", L #3)
    => goto "L65";
  @"L65" [%"pr.16" : P = phi("L63" => %"v87", "L34" => %"v31")]:
    call %"v97" : W = $"__gconv_find_transform"(P %"pr.15", P %"pr.16", P %"v6", P %"v7", W %"v4");
    %"v102" : W = (Cmp Eq W) %"v97", #0
    => br %"v102" ? "L98" : "L100";
  @"L98":
    %"chk10" : A = (Check 0 8 Read 1) %"v7";
    %"v103" : L = (RawLoad LdL 0) %"chk10";
    %"v104" : L = Mul %"v103", #48;
    %"v105" : L = Add %"v104", #16;
    call %"v106" : P = $"malloc"(L %"v105");
    %"v111" : L = Ptoi %"v106";
    %"v112" : L = Ptoi #0;
    %"v113" : W = (Cmp Eq L) %"v111", %"v112"
    => br %"v113" ? "L109" : "L108";
  @"L108":
    %"v115" = %"v106" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"v6";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 8 Write 8) %"v115";
    store.ptr [%"chk12" + 0] <- %"v116";
    %"chk13" : A = (Renew 0 8 Read 1) %"chk10", %"v7";
    %"v118" : L = (RawLoad LdL 0) %"chk13";
    %"chk14" : A = (HalfCheck Lower 0 8 Write 1) %"chk12", %"v106";
    store Wl [%"chk14" + 0] <- %"v118";
    %"v120" = %"v106" +p #16;
    %"v121" : L = (RawLoad LdL 0) %"chk13";
    %"v122" : L = Mul %"v121", #48;
    call %"v123" : P = $"__GI_memset"(P %"v120", W #0, L %"v122")
    => goto "L124";
  @"L124" [%"pr.12" : W = phi("L108" => %"pr.14", "L195" => %"pr.13"); %"pr.5" : L = phi("L108" => #0, "L195" => %"v230")]:
    %"chk16" : A = (Renew 0 8 Read 1) %"chk10", %"v7";
    %"v129" : L = (RawLoad LdL 0) %"chk16";
    %"v130" : W = (Cmp Ult L) %"pr.5", %"v129"
    => br %"v130" ? "L125" : "L109";
  @"L125":
    %"v133" = %"v106" +p #16;
    %"v135" : L = Mul %"pr.5", #48;
    %"v136" = %"v133" +p %"v135";
    %"v137" = %"v136" +p #32;
    %"v143" = %"v136" +p #40;
    %"chk17" : A = (Check 0 8 Write 8) %"v137";
    store.ptr [%"chk17" + 0] <- %"v143"
    => br %"v18" ? "L148" : "L149";
  @"L148":
    %"chk18" : A = (Renew 0 8 Read 8) %"chk11", %"v6";
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v152" : L = Mul %"pr.5", #104;
    %"v153" = %"v150" +p %"v152";
    %"v154" = %"v153" +p #24;
    %"chk19" : A = (Check 0 8 Read 8) %"v154";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v156" : P = Copy $"glibc_gconv_open#str.244";
    %"v157" : P = Copy $"_nl_C_locobj";
    call %"v158" : W = $"__GI___strcasecmp_l"(P %"v155", P %"v156", P %"v157");
    %"v159" : W = (Cmp Eq W) %"v158", #0
    => goto "L149";
  @"L149" [%"v161" : W = phi("L125" => #0, "L148" => %"v159")]:
    => br %"v161" ? "L144" : "L146";
  @"L144":
    %"v163" : W = Or %"pr.12", #8
    => goto "L146";
  @"L146" [%"pr.13" : W = phi("L144" => %"v163", "L149" => %"pr.12")]:
    %"chk20" : A = (Renew 0 8 Read 1) %"chk10", %"v7";
    %"v168" : L = (RawLoad LdL 0) %"chk20";
    %"v169" : L = Sub %"v168", #1;
    %"v170" : W = (Cmp Ult L) %"pr.5", %"v169"
    => br %"v170" ? "L164" : "L165";
  @"L164":
    %"v172" = %"v106" +p #16;
    %"v175" = %"v172" +p %"v135";
    %"v176" = %"v175" +p #16;
    %"chk21" : A = (Check 0 4 Write 1) %"v176";
    store Ww [%"chk21" + 0] <- %"pr.13";
    %"chk22" : A = (Renew 0 8 Read 8) %"chk11", %"v6";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v180" : L = Mul %"pr.5", #104;
    %"v181" = %"v178" +p %"v180";
    %"v182" = %"v181" +p #84;
    %"chk23" : A = (Check 0 4 Read 1) %"v182";
    %"v183" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v184" : W = Mul %"v183", #8160;
    %"v185" : L = (Ext Sw) %"v184";
    call %"v192" : P = $"malloc"(L %"v185");
    %"chk24" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v175";
    store.ptr [%"chk24" + 0] <- %"v192";
    %"chk25" : A = (Renew 0 8 Read 8) %"chk24", %"v175";
    %"v201" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v202" : L = Ptoi %"v201";
    %"v204" : W = (Cmp Eq L) %"v202", %"v112"
    => br %"v204" ? "L205" : "L195";
  @"L195":
    %"v208" = %"v106" +p #16;
    %"v211" = %"v208" +p %"v135";
    %"v212" = %"v211" +p #8;
    %"chk26" : A = (Check 0 8 Read 8) %"v211";
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v220" = %"v218" +p %"v185";
    %"chk27" : A = (HalfCheck Upper 0 8 Write 8) %"chk26", %"v212";
    store.ptr [%"chk27" + 0] <- %"v220";
    %"v230" : L = Add %"pr.5", #1
    => goto poll "L124";
  @"L165":
    %"v222" = %"v106" +p #16;
    %"v225" = %"v222" +p %"v135";
    %"v226" = %"v225" +p #16;
    %"v228" : W = Or %"pr.13", #1;
    %"chk28" : A = (Check 0 4 Write 1) %"v226";
    store Ww [%"chk28" + 0] <- %"v228"
    => goto "L109";
  @"L109" [%"pr.9" : W = phi("L98" => #3, "L124" => %"v97", "L165" => %"v97"); %"pr.4" : L = phi("L98" => #0, "L124" => %"pr.5", "L165" => %"pr.5")]:
    %"v235" : W = (Cmp Ne W) %"pr.9", #0
    => br %"v235" ? "L205" : "L100";
  @"L205" [%"pr.10" : W = phi("L164" => #3, "L109" => %"pr.9"); %"pr.6" : L = phi("L164" => %"pr.5", "L109" => %"pr.4")]:
    %"v237" : P = Copy $"__libc_errno";
    %"chk29" : A = (Check 0 4 Read 1) %"v237";
    %"v238" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"v245" : W = (Cmp Ne L) %"v111", %"v112"
    => br %"v245" ? "L246" : "L241";
  @"L246" [%"pr.7" : L = phi("L247" => %"v250", "L205" => %"pr.6")]:
    %"v250" : L = Sub %"pr.7", #1;
    %"v251" : W = (Cmp Ugt L) %"pr.7", #0
    => br %"v251" ? "L247" : "L248";
  @"L247":
    %"v253" = %"v106" +p #16;
    %"v255" : L = Mul %"v250", #48;
    %"v256" = %"v253" +p %"v255";
    %"chk30" : A = (Check 0 8 Read 8) %"v256";
    %"v257" : P = (RawLoadPointer 0 load_effects) %"chk30";
    call void $"free"(P %"v257")
    => goto poll "L246";
  @"L248":
    call void $"free"(P %"v106")
    => goto "L241";
  @"L241" [%"pr.3" : P = phi("L248" => #0, "L205" => %"v106")]:
    %"chk31" : A = (Check 0 8 Read 8) %"v6";
    %"v259" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Renew 0 8 Read 1) %"chk10", %"v7";
    %"v260" : L = (RawLoad LdL 0) %"chk32";
    call %"v261" : W = $"__gconv_close_transform"(P %"v259", L %"v260");
    %"v262" : P = Copy $"__libc_errno";
    %"chk33" : A = (Check 0 4 Write 1) %"v262";
    store Ww [%"chk33" + 0] <- %"v238"
    => goto "L100";
  @"L100" [%"pr.8" : W = phi("L241" => %"pr.10", "L109" => %"pr.9", "L65" => %"v97"); %"pr.1" : P = phi("L241" => %"pr.3", "L109" => %"v106", "L65" => #0)]:
    %"chk34" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk34" + 0] <- %"pr.1"
    => ret %"pr.8"
} }.

Definition hello_image_fn___gconv_btwoc_ascii : func :=
  ir_fn{ "export" "__gconv_btwoc_ascii"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v7" : W = (Ext Ub) %"v2";
    %"v8" : W = (Cmp Slt W) %"v7", #128
    => br %"v8" ? "L4" : "L5";
  @"L4":
    => ret %"v7";
  @"L5":
    => ret #4294967295
} }.

Definition hello_image_fn___gconv_transform_internal_ucs4 : func :=
  ir_fn{ "export" "__gconv_transform_internal_ucs4"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", W %"v12", W %"v14") -> (RClass W) blocks ((app [ir_blk{ @"start":
    alloca "v103" 8;
    %"v273" : P = (Alloc 8) #8;
    %"v18" = %"v0" +p #104;
    %"v21" = %"v2" +p #48;
    %"v28" = %"v2" +p #16;
    %"chk0" : A = (Check 0 4 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v30" : W = And %"v29", #1
    => br %"v30" ? "L26" : "L24" };
  ir_blk{ @"L24":
    %"v33" = %"v18" +p #40;
    %"chk1" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v18";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v40" : L = Ptoi %"v39";
    %"v41" : L = Ptoi #0;
    %"v42" : W = (Cmp Ne L) %"v40", %"v41"
    => br %"v42" ? "L26" : "L36" };
  ir_blk{ @"L36":
    => goto "L26" };
  ir_blk{ @"L26" [%"pr.1" : P = phi("L36" => %"v34", "L24" => %"v34", "start" => #0)]:
    %"v48" : L = (Ext Sw) %"v12";
    %"v49" : W = (Cmp Ne L) %"v48", #0
    => br %"v49" ? "L44" : "L45" };
  ir_blk{ @"L44":
    %"v54" : L = Ptoi %"v8";
    %"v55" : L = Ptoi #0;
    %"v56" : W = (Cmp Eq L) %"v54", %"v55"
    => br %"v56" ? "L52" : "L51" };
  ir_blk{ @"L51":
    %"v57" : P = Copy $"glibc_gconv_simple#str.270";
    %"v58" : P = Copy $"glibc_gconv_simple#str.271";
    %"v59" : P = Copy $"glibc_gconv_simple#str.272";
    call void $"__libc_assert_fail"(P %"v57", P %"v58", W #350, P %"v59")
    => goto "L52" };
  ir_blk{ @"L52":
    %"v61" = %"v2" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"v63" : P = $"__GI_memset"(P %"v62", W #0, L #8);
    %"v68" = %"v2" +p #16;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk0", %"v68";
    %"v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v70" : W = And %"v69", #1
    => br %"v70" ? "L46" : "iw_1.join" };
  ir_blk{ @"iw_1.join":
    %"chk5" : F = CheckFunction %"pr.1";
    rawcall %"v79" : W = %"chk5"(P %"v18", P %"v21", P #0, P #0, P #0, P %"v10", W %"v12", W %"v14")
    => goto "L46" };
  ir_blk{ @"L45":
    %"chk6" : A = (Check 0 8 Read 8) %"v4";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v88" : L = Ptoi %"v8";
    %"v89" : L = Ptoi #0;
    %"v90" : W = (Cmp Eq L) %"v88", %"v89"
    => br %"v90" ? "L84" : "L85" };
  ir_blk{ @"L84":
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk7"
    => goto "L86" };
  ir_blk{ @"L85":
    %"chk8" : A = (Check 0 8 Read 8) %"v8";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk8"
    => goto "L86" };
  ir_blk{ @"L86" [%"v97" : P = phi("L84" => %"v94", "L85" => %"v96")]:
    %"v100" = %"v2" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v100";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (CheckLocal (a "v103") 0 8 Write 1);
    store Wl [%"chk10" + 0] <- #0;
    %"v109" : L = Ptoi %"v10";
    %"v110" : W = (Cmp Ne L) %"v109", #0
    => br %"v110" ? "L140" : "L106" };
  ir_blk{ @"L106":
    => goto "L140" };
  ir_blk{ @"L140":
    %"v143" : W = (Cmp Ne W) %"v14", #0
    => br %"v143" ? "L145" : "L146" };
  ir_blk{ @"L145":
    %"v148" = %"v2" +p #32;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v148";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 4 Read 1) %"v149";
    %"v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v151" : W = And %"v150", #7;
    %"v152" : W = (Cmp Ne W) %"v151", #0
    => goto "L146" };
  ir_blk{ @"L146" [%"v154" : W = phi("L140" => #0, "L145" => %"v152")]:
    => br %"v154" ? "L112" : "L195" };
  ir_blk{ @"L112":
    => br %"v90" ? "iw_2.start" : "L156" };
  ir_blk{ @"L156":
    %"v162" : P = Copy $"glibc_gconv_simple#str.270";
    %"v163" : P = Copy $"glibc_gconv_simple#str.271";
    %"v164" : P = Copy $"glibc_gconv_simple#str.272";
    call void $"__libc_assert_fail"(P %"v162", P %"v163", W #467, P %"v164")
    => goto "iw_2.start" };
  ir_blk{ @"iw_2.start":
    %"iw_2.v16" = %"v2" +p #32;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v16";
    %"iw_2.v17" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 4 Read 1) %"iw_2.v17";
    %"iw_2.v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"iw_2.v21" : W = And %"iw_2.v20", #7;
    %"iw_2.v22" : L = (Ext Sw) %"iw_2.v21"
    => goto "iw_2.L23" };
  ir_blk{ @"iw_2.L23" [%"iw_2.pr.1" : L = phi("iw_2.L24" => %"iw_2.v41", "iw_2.start" => %"iw_2.v22")]:
    %"chk15" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_2.v27" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_2.v29" : L = Ptoi %"iw_2.v27";
    %"iw_2.v30" : L = Ptoi %"v6";
    %"iw_2.v31" : W = (Cmp Ult L) %"iw_2.v29", %"iw_2.v30"
    => br %"iw_2.v31" ? "iw_2.L32" : "iw_2.L33" };
  ir_blk{ @"iw_2.L32":
    %"iw_2.v35" : W = (Cmp Ult L) %"iw_2.pr.1", #4
    => goto "iw_2.L33" };
  ir_blk{ @"iw_2.L33" [%"iw_2.v37" : W = phi("iw_2.L23" => #0, "iw_2.L32" => %"iw_2.v35")]:
    => br %"iw_2.v37" ? "iw_2.L24" : "iw_2.L25" };
  ir_blk{ @"iw_2.L24":
    %"iw_2.v39" = %"iw_2.v17" +p #4;
    %"iw_2.v41" : L = Add %"iw_2.pr.1", #1;
    %"iw_2.v42" = %"iw_2.v39" +p %"iw_2.pr.1";
    %"iw_2.v44" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_2.v45" = %"iw_2.v44" +p #1;
    %"chk17" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk17" + 0] <- %"iw_2.v45";
    %"chk18" : A = (Check 0 1 Read 1) %"iw_2.v44";
    %"iw_2.v46" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"iw_2.v47" : W = (Ext Sb) %"iw_2.v46";
    %"chk19" : A = (Check 0 1 Write 1) %"iw_2.v42";
    store Wb [%"chk19" + 0] <- %"iw_2.v47"
    => goto poll "iw_2.L23" };
  ir_blk{ @"iw_2.L25":
    %"iw_2.v52" : W = (Cmp Ult L) %"iw_2.pr.1", #4
    => br %"iw_2.v52" ? "iw_2.L48" : "iw_2.L50" };
  ir_blk{ @"iw_2.L48":
    %"chk20" : A = (Renew 0 4 Read 1) %"chk14", %"iw_2.v17";
    %"iw_2.v56" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"iw_2.v58" : W = And %"iw_2.v56", #4294967288;
    %"chk21" : A = (Renew 0 4 Write 1) %"chk14", %"iw_2.v17";
    store Ww [%"chk21" + 0] <- %"iw_2.v58";
    %"iw_2.v60" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"iw_2.v62" : L = (Ext Sw) %"iw_2.v60";
    %"iw_2.v63" : L = Or %"iw_2.v62", %"iw_2.pr.1";
    store Ww [%"chk21" + 0] <- %"iw_2.v63"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.L50":
    %"iw_2.v69" = %"iw_2.v17" +p #4;
    %"iw_2.v70" = %"iw_2.v69" +p #3;
    %"chk24" : A = (HalfCheck Upper 0 1 Read 1) %"chk14", %"iw_2.v70";
    %"iw_2.v71" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v72" : W = (Ext Ub) %"iw_2.v71";
    %"chk25" : A = (Check 0 1 Write 1) %"v97";
    store Wb [%"chk25" + 0] <- %"iw_2.v72";
    %"iw_2.v75" = %"v97" +p #1;
    %"iw_2.v78" = %"iw_2.v69" +p #2;
    %"chk26" : A = (HalfCheck Lower 0 1 Read 1) %"chk24", %"iw_2.v78";
    %"iw_2.v79" : W = (RawLoad (LdNarrow Sb) 0) %"chk26";
    %"iw_2.v80" : W = (Ext Ub) %"iw_2.v79";
    %"chk27" : A = (HalfCheck Upper 0 1 Write 1) %"chk25", %"iw_2.v75";
    store Wb [%"chk27" + 0] <- %"iw_2.v80";
    %"iw_2.v83" = %"v97" +p #2;
    %"iw_2.v86" = %"iw_2.v69" +p #1;
    %"chk28" : A = (HalfCheck Lower 0 1 Read 1) %"chk24", %"iw_2.v86";
    %"iw_2.v87" : W = (RawLoad (LdNarrow Sb) 0) %"chk28";
    %"iw_2.v88" : W = (Ext Ub) %"iw_2.v87";
    %"chk29" : A = (HalfCheck Upper 0 1 Write 1) %"chk25", %"iw_2.v83";
    store Wb [%"chk29" + 0] <- %"iw_2.v88";
    %"iw_2.v91" = %"v97" +p #3;
    %"chk30" : A = (HalfCheck Lower 0 1 Read 1) %"chk24", %"iw_2.v69";
    %"iw_2.v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk30";
    %"iw_2.v96" : W = (Ext Ub) %"iw_2.v95";
    %"chk31" : A = (HalfCheck Upper 0 1 Write 1) %"chk25", %"iw_2.v91";
    store Wb [%"chk31" + 0] <- %"iw_2.v96";
    %"iw_2.v99" = %"v97" +p #4;
    %"chk32" : A = (Renew 0 4 Read 1) %"chk14", %"iw_2.v17";
    %"iw_2.v101" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    %"iw_2.v103" : W = And %"iw_2.v101", #4294967288;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk14", %"iw_2.v17";
    store Ww [%"chk33" + 0] <- %"iw_2.v103"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join" [%"v179" : W = phi("iw_2.L48" => #7, "iw_2.L50" => #0); %"pr.17" : P = phi("iw_2.L48" => %"v97", "iw_2.L50" => %"iw_2.v99")]:
    %"v191" : L = (Ext Sw) %"v179";
    %"v192" : W = (Cmp Ne L) %"v191", #0
    => br %"v192" ? "L187" : "L195" };
  ir_blk{ @"L187":
    => ret %"v179" };
  ir_blk{ @"L195" [%"pr.14" : P = phi("L479" => %"v484", "iw_2.join" => %"pr.17", "L146" => %"v97")]:
    %"chk34" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (CheckLocal (a "v103") 0 8 Read 1);
    %"v202" : L = (RawLoad LdL 0) %"chk35"
    => br %"v110" ? "L203" : "L205" };
  ir_blk{ @"L203":
    %"chk36" : A = (Check 0 8 Read 1) %"v10";
    %"v210" : L = (RawLoad LdL 0) %"chk36"
    => goto "L205" };
  ir_blk{ @"L205" [%"v211" : L = phi("L203" => %"v210", "L195" => #0)]:
    %"v212" : L = Add %"v202", %"v211";
    %"iw_4.v16" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_4.v26" : L = Ptoi %"v6";
    %"iw_4.v27" : L = Ptoi %"iw_4.v16";
    %"iw_4.v28" : L = Sub %"iw_4.v26", %"iw_4.v27";
    %"iw_4.v31" : L = Ptoi %"v101";
    %"iw_4.v32" : L = Ptoi %"pr.14";
    %"iw_4.v33" : L = Sub %"iw_4.v31", %"iw_4.v32";
    %"iw_4.v34" : W = (Cmp Slt L) %"iw_4.v28", %"iw_4.v33"
    => br %"iw_4.v34" ? "iw_4.L23" : "iw_4.L22" };
  ir_blk{ @"iw_4.L22":
    => goto "iw_4.L23" };
  ir_blk{ @"iw_4.L23" [%"iw_4.v45" : L = phi("iw_4.L22" => %"iw_4.v33", "L205" => %"iw_4.v28")]:
    %"iw_4.v46" : L = Div %"iw_4.v45", #4
    => goto "iw_4.L49" };
  ir_blk{ @"iw_4.L49" [%"iw_4.pr.5" : L = phi("iw_4.L23" => #0, "iw_4.L50" => %"iw_4.v70"); %"iw_4.pr.2" : P = phi("iw_4.L23" => %"pr.14", "iw_4.L50" => %"iw_4.v74"); %"iw_4.pr.1" : P = phi("iw_4.L23" => %"iw_4.v16", "iw_4.L50" => %"iw_4.v72")]:
    %"iw_4.v55" : W = (Cmp Ult L) %"iw_4.pr.5", %"iw_4.v46"
    => br %"iw_4.v55" ? "iw_4.L50" : "iw_4.L52" };
  ir_blk{ @"iw_4.L50":
    %"chk38" : A = (Check 0 4 Read 1) %"iw_4.pr.1";
    %"iw_4.v60" : W = (RawLoad (LdNarrow Uw) 0) %"chk38";
    %"iw_4.iw_1.v3" : W = And %"iw_4.v60", #4278190080;
    %"iw_4.iw_1.v4" : W = Shr %"iw_4.iw_1.v3", #24;
    %"iw_4.iw_1.v6" : W = And %"iw_4.v60", #16711680;
    %"iw_4.iw_1.v7" : W = Shr %"iw_4.iw_1.v6", #8;
    %"iw_4.iw_1.v8" : W = Or %"iw_4.iw_1.v4", %"iw_4.iw_1.v7";
    %"iw_4.iw_1.v10" : W = And %"iw_4.v60", #65280;
    %"iw_4.iw_1.v11" : W = Shl %"iw_4.iw_1.v10", #8;
    %"iw_4.iw_1.v12" : W = Or %"iw_4.iw_1.v8", %"iw_4.iw_1.v11";
    %"iw_4.iw_1.v14" : W = And %"iw_4.v60", #255;
    %"iw_4.iw_1.v15" : W = Shl %"iw_4.iw_1.v14", #24;
    %"iw_4.iw_1.v16" : W = Or %"iw_4.iw_1.v12", %"iw_4.iw_1.v15";
    %"chk39" : A = (Check 0 4 Write 1) %"iw_4.pr.2";
    store Ww [%"chk39" + 0] <- %"iw_4.iw_1.v16";
    %"iw_4.v70" : L = Add %"iw_4.pr.5", #1;
    %"iw_4.v72" = %"iw_4.pr.1" +p #4;
    %"iw_4.v74" = %"iw_4.pr.2" +p #4
    => goto poll "iw_4.L49" };
  ir_blk{ @"iw_4.L52":
    %"chk40" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk40" + 0] <- %"iw_4.pr.1";
    %"chk41" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_4.v83" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"iw_4.v85" : L = Ptoi %"iw_4.v83";
    %"iw_4.v87" : W = (Cmp Eq L) %"iw_4.v85", %"iw_4.v26"
    => br %"iw_4.v87" ? "iw_4.L81" : "iw_4.L80" };
  ir_blk{ @"iw_4.L80":
    %"iw_4.v93" = %"iw_4.pr.2" +p #4;
    %"iw_4.v95" : L = Ptoi %"iw_4.v93";
    %"iw_4.v97" : W = (Cmp Ugt L) %"iw_4.v95", %"iw_4.v31"
    => br %"iw_4.v97" ? "iw_4.L81" : "iw_4.L89" };
  ir_blk{ @"iw_4.L89":
    => goto "iw_4.L81" }] [ir_blk{ @"iw_4.L81" [%"iw_4.pr.3" : W = phi("iw_4.L52" => #4, "iw_4.L89" => #7, "iw_4.L80" => #5)]:
    %"v236" : W = (Cmp Ne L) %"v88", %"v89"
    => br %"v236" ? "L230" : "L232" };
  ir_blk{ @"L230":
    %"chk42" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk42" + 0] <- %"iw_4.pr.2"
    => ret %"iw_4.pr.3" };
  ir_blk{ @"L232":
    %"v244" = %"v2" +p #20;
    %"chk43" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v244";
    %"v245" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v246" : W = Add %"v245", #1;
    %"chk44" : A = (Renew 0 4 Write 1) %"chk43", %"v244";
    store Ww [%"chk44" + 0] <- %"v246";
    %"v251" = %"v2" +p #16;
    %"chk45" : A = (Renew 0 4 Read 1) %"chk0", %"v251";
    %"v252" : W = (RawLoad (LdNarrow Sw) 0) %"chk45";
    %"v253" : W = And %"v252", #1
    => br %"v253" ? "L247" : "L249" };
  ir_blk{ @"L247":
    %"chk46" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk46" + 0] <- %"iw_4.pr.2";
    %"chk47" : A = (Check 0 8 Read 1) %"v10";
    %"v259" : L = (RawLoad LdL 0) %"chk47";
    %"chk48" : A = (CheckLocal (a "v103") 0 8 Read 1);
    %"v260" : L = (RawLoad LdL 0) %"chk48";
    %"v261" : L = Add %"v259", %"v260";
    %"chk49" : A = (Renew 0 8 Write 1) %"chk47", %"v10";
    store Wl [%"chk49" + 0] <- %"v261"
    => goto "L197" };
  ir_blk{ @"L249":
    %"v268" : L = Ptoi %"iw_4.pr.2";
    %"v270" : W = (Cmp Ugt L) %"v268", %"iw_4.v32"
    => br %"v270" ? "L263" : "L265" };
  ir_blk{ @"L263":
    %"chk50" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"chk51" : A = (Check 0 8 Write 8) %"v273";
    store.ptr [%"chk51" + 0] <- %"v275";
    %"chk52" : F = CheckFunction %"pr.1";
    rawcall %"v284" : W = %"chk52"(P %"v18", P %"v21", P %"v273", P %"iw_4.pr.2", P #0, P %"v10", W #0, W %"v14");
    %"v289" : W = (Cmp Ne W) %"v284", #4
    => br %"v289" ? "L285" : "L286" };
  ir_blk{ @"L285":
    %"chk53" : A = (Renew 0 8 Read 8) %"chk51", %"v273";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v295" : L = Ptoi %"v293";
    %"v297" : W = (Cmp Ne L) %"v295", %"v268"
    => br %"v297" ? "L290" : "L265" };
  ir_blk{ @"L290":
    %"chk54" : A = (CheckLocal (a "v103") 0 8 Read 1);
    %"v304" : L = (RawLoad LdL 0) %"chk54"
    => br %"v110" ? "L305" : "L307" };
  ir_blk{ @"L305":
    %"chk55" : A = (Check 0 8 Read 1) %"v10";
    %"v312" : L = (RawLoad LdL 0) %"chk55"
    => goto "L307" };
  ir_blk{ @"L307" [%"v313" : L = phi("L305" => %"v312", "L290" => #0)]:
    %"v314" : L = Add %"v304", %"v313";
    %"v315" : W = (Cmp Eq L) %"v212", %"v314"
    => br %"v315" ? "L319" : "L302" };
  ir_blk{ @"L319":
    %"chk56" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v329" : L = Ptoi %"v327";
    %"v330" : L = Sub %"v268", %"v329";
    (Flight (a "v334") Sub [(FAddress (t "v325")); (FValue (t "v330"))] (LowerOf (t "v325")));
    %"chk58" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk58" + 0] <- %"v334"
    => goto "L265" };
  ir_blk{ @"L302":
    %"chk59" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk59" + 0] <- %"v199";
    %"chk60" : A = (Renew 0 8 Read 8) %"chk51", %"v273";
    %"v424" : P = (RawLoadPointer 0 load_effects) %"chk60";
    %"chk61" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v16" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"iw_7.v27" : L = Ptoi %"iw_7.v16";
    %"iw_7.v28" : L = Sub %"iw_4.v26", %"iw_7.v27";
    %"iw_7.v31" : L = Ptoi %"v424";
    %"iw_7.v33" : L = Sub %"iw_7.v31", %"iw_4.v32";
    %"iw_7.v34" : W = (Cmp Slt L) %"iw_7.v28", %"iw_7.v33"
    => br %"iw_7.v34" ? "iw_7.L23" : "iw_7.L22" };
  ir_blk{ @"iw_7.L22":
    => goto "iw_7.L23" };
  ir_blk{ @"iw_7.L23" [%"iw_7.v45" : L = phi("iw_7.L22" => %"iw_7.v33", "L302" => %"iw_7.v28")]:
    %"iw_7.v46" : L = Div %"iw_7.v45", #4
    => goto "iw_7.L49" };
  ir_blk{ @"iw_7.L49" [%"iw_7.pr.5" : L = phi("iw_7.L23" => #0, "iw_7.L50" => %"iw_7.v70"); %"iw_7.pr.2" : P = phi("iw_7.L23" => %"pr.14", "iw_7.L50" => %"iw_7.v74"); %"iw_7.pr.1" : P = phi("iw_7.L23" => %"iw_7.v16", "iw_7.L50" => %"iw_7.v72")]:
    %"iw_7.v55" : W = (Cmp Ult L) %"iw_7.pr.5", %"iw_7.v46"
    => br %"iw_7.v55" ? "iw_7.L50" : "iw_7.L52" };
  ir_blk{ @"iw_7.L50":
    %"chk62" : A = (Check 0 4 Read 1) %"iw_7.pr.1";
    %"iw_7.v60" : W = (RawLoad (LdNarrow Uw) 0) %"chk62";
    %"iw_7.iw_1.v3" : W = And %"iw_7.v60", #4278190080;
    %"iw_7.iw_1.v4" : W = Shr %"iw_7.iw_1.v3", #24;
    %"iw_7.iw_1.v6" : W = And %"iw_7.v60", #16711680;
    %"iw_7.iw_1.v7" : W = Shr %"iw_7.iw_1.v6", #8;
    %"iw_7.iw_1.v8" : W = Or %"iw_7.iw_1.v4", %"iw_7.iw_1.v7";
    %"iw_7.iw_1.v10" : W = And %"iw_7.v60", #65280;
    %"iw_7.iw_1.v11" : W = Shl %"iw_7.iw_1.v10", #8;
    %"iw_7.iw_1.v12" : W = Or %"iw_7.iw_1.v8", %"iw_7.iw_1.v11";
    %"iw_7.iw_1.v14" : W = And %"iw_7.v60", #255;
    %"iw_7.iw_1.v15" : W = Shl %"iw_7.iw_1.v14", #24;
    %"iw_7.iw_1.v16" : W = Or %"iw_7.iw_1.v12", %"iw_7.iw_1.v15";
    %"chk63" : A = (Check 0 4 Write 1) %"iw_7.pr.2";
    store Ww [%"chk63" + 0] <- %"iw_7.iw_1.v16";
    %"iw_7.v70" : L = Add %"iw_7.pr.5", #1;
    %"iw_7.v72" = %"iw_7.pr.1" +p #4;
    %"iw_7.v74" = %"iw_7.pr.2" +p #4
    => goto poll "iw_7.L49" };
  ir_blk{ @"iw_7.L52":
    %"chk64" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk64" + 0] <- %"iw_7.pr.1";
    %"chk65" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v83" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"iw_7.v85" : L = Ptoi %"iw_7.v83";
    %"iw_7.v87" : W = (Cmp Eq L) %"iw_7.v85", %"iw_4.v26"
    => br %"iw_7.v87" ? "iw_7.L81" : "iw_7.L80" };
  ir_blk{ @"iw_7.L80":
    %"iw_7.v93" = %"iw_7.pr.2" +p #4;
    %"iw_7.v95" : L = Ptoi %"iw_7.v93";
    %"iw_7.v97" : W = (Cmp Ugt L) %"iw_7.v95", %"iw_7.v31"
    => br %"iw_7.v97" ? "iw_7.L81" : "iw_7.L89" };
  ir_blk{ @"iw_7.L89":
    => goto "iw_7.L81" };
  ir_blk{ @"iw_7.L81" [%"iw_7.pr.3" : W = phi("iw_7.L52" => #4, "iw_7.L89" => #7, "iw_7.L80" => #5)]:
    %"v427" : L = (Ext Sw) %"iw_7.pr.3";
    %"chk66" : A = (Renew 0 8 Read 8) %"chk51", %"v273";
    %"v440" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"v441" : L = Ptoi %"iw_7.pr.2";
    %"v442" : L = Ptoi %"v440";
    %"v443" : W = (Cmp Eq L) %"v441", %"v442"
    => br %"v443" ? "L438" : "L437" };
  ir_blk{ @"L437":
    %"v444" : P = Copy $"glibc_gconv_simple#str.273";
    %"v445" : P = Copy $"glibc_gconv_simple#str.271";
    %"v446" : P = Copy $"glibc_gconv_simple#str.272";
    call void $"__libc_assert_fail"(P %"v444", P %"v445", W #594, P %"v446")
    => goto "L438" };
  ir_blk{ @"L438":
    %"v451" : W = (Cmp Eq L) %"v427", #5
    => br %"v451" ? "L449" : "L448" };
  ir_blk{ @"L448":
    %"v452" : P = Copy $"glibc_gconv_simple#str.274";
    %"v453" : P = Copy $"glibc_gconv_simple#str.271";
    %"v454" : P = Copy $"glibc_gconv_simple#str.272";
    call void $"__libc_assert_fail"(P %"v452", P %"v453", W #595, P %"v454")
    => goto "L449" };
  ir_blk{ @"L449":
    %"v462" : W = (Cmp Eq L) %"v441", %"iw_4.v32"
    => br %"v462" ? "L455" : "L265" };
  ir_blk{ @"L455":
    %"v466" = %"v2" +p #20;
    %"chk67" : A = (Renew 0 4 Read 1) %"chk43", %"v466";
    %"v467" : W = (RawLoad (LdNarrow Sw) 0) %"chk67";
    %"v468" : W = Sub %"v467", #1;
    %"chk68" : A = (Renew 0 4 Write 1) %"chk43", %"v466";
    store Ww [%"chk68" + 0] <- %"v468"
    => goto "L265" };
  ir_blk{ @"L286":
    %"v474" : W = (Cmp Eq W) %"iw_4.pr.3", #5
    => br %"v474" ? "L470" : "L265" };
  ir_blk{ @"L470":
    %"chk69" : A = (Renew 0 8 Read 8) %"chk50", %"v2";
    %"v476" : P = (RawLoadPointer 0 load_effects) %"chk69"
    => goto "L265" };
  ir_blk{ @"L265" [%"pr.7" : W = phi("L319" => %"v284", "L455" => %"v284", "L449" => %"v284", "L285" => %"v284", "L470" => #0, "L286" => %"iw_4.pr.3", "L249" => %"iw_4.pr.3")]:
    %"v481" : W = (Cmp Ne W) %"pr.7", #0
    => br %"v481" ? "L197" : "L479" };
  ir_blk{ @"L479":
    %"chk70" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v484" : P = (RawLoadPointer 0 load_effects) %"chk70"
    => goto poll "L195" };
  ir_blk{ @"L197" [%"pr.5" : W = phi("L247" => %"iw_4.pr.3", "L265" => %"pr.7")]:
    %"v516" : L = (Ext Sw) %"v14";
    %"v517" : W = (Cmp Ne L) %"v516", #0
    => br %"v517" ? "L520" : "L521" };
  ir_blk{ @"L520":
    %"v523" : W = (Cmp Eq W) %"pr.5", #7
    => goto "L521" };
  ir_blk{ @"L521" [%"v525" : W = phi("L197" => #0, "L520" => %"v523")]:
    => br %"v525" ? "L485" : "L46" };
  ir_blk{ @"L485":
    %"chk71" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v529" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v531" : L = Ptoi %"v529";
    %"v532" : L = Sub %"iw_4.v26", %"v531";
    %"v537" : W = (Cmp Ule L) %"v532", #4
    => br %"v537" ? "L542" : "L534" };
  ir_blk{ @"L534":
    %"v538" : P = Copy $"glibc_gconv_simple#str.275";
    %"v539" : P = Copy $"glibc_gconv_simple#str.271";
    %"v540" : P = Copy $"glibc_gconv_simple#str.272";
    call void $"__libc_assert_fail"(P %"v538", P %"v539", W #647, P %"v540")
    => goto "L542" };
  ir_blk{ @"L542" [%"pr.20" : L = phi("L543" => %"v562", "L534" => #0, "L485" => #0)]:
    %"v548" : W = (Cmp Ult L) %"pr.20", %"v532"
    => br %"v548" ? "L543" : "L545" };
  ir_blk{ @"L543":
    %"v550" = %"v2" +p #32;
    %"chk72" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v550";
    %"v551" : P = (RawLoadPointer 0 load_effects) %"chk72";
    %"v552" = %"v551" +p #4;
    %"v554" = %"v552" +p %"pr.20";
    %"chk73" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v556" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"v558" = %"v556" +p %"pr.20";
    %"chk74" : A = (Check 0 1 Read 1) %"v558";
    %"v559" : W = (RawLoad (LdNarrow Ub) 0) %"chk74";
    %"v560" : W = (Ext Sb) %"v559";
    %"chk75" : A = (Check 0 1 Write 1) %"v554";
    store Wb [%"chk75" + 0] <- %"v560";
    %"v562" : L = Add %"pr.20", #1
    => goto poll "L542" };
  ir_blk{ @"L545":
    %"chk76" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk76" + 0] <- %"v6";
    %"v566" = %"v2" +p #32;
    %"chk77" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v566";
    %"v567" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"chk78" : A = (Check 0 4 Read 1) %"v567";
    %"v568" : W = (RawLoad (LdNarrow Sw) 0) %"chk78";
    %"v570" : W = And %"v568", #4294967288;
    %"chk79" : A = (Renew 0 4 Write 1) %"chk78", %"v567";
    store Ww [%"chk79" + 0] <- %"v570";
    %"v573" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"chk81" : A = (Check 0 4 Read 1) %"v573";
    %"v574" : W = (RawLoad (LdNarrow Sw) 0) %"chk81";
    %"v576" : L = (Ext Sw) %"v574";
    %"v577" : L = Or %"v576", %"pr.20";
    %"chk82" : A = (Renew 0 4 Write 1) %"chk81", %"v573";
    store Ww [%"chk82" + 0] <- %"v577"
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.9" : W = phi("iw_1.join" => %"v79", "L52" => #0, "L545" => %"pr.5", "L521" => %"pr.5")]:
    => ret %"pr.9" }])) }.

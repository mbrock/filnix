(** This file defines checked IR from glibc’s `iconv/gconv_open.os` object.
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

Definition fn___GI___gconv_open : func :=
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

Definition item_glibc_gconv_open'23str'2e243 : item :=
  (IData (a "glibc_gconv_open#str.243") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 47); (Item Wb 0)]).

Definition item_glibc_gconv_open'23str'2e244 : item :=
  (IData (a "glibc_gconv_open#str.244") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

(** This file defines checked IR from glibc’s `wcsmbs/mbrtowc.os` object.
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

Definition fn___GI___mbrtowc : func :=
  ir_fn{ "export" "__GI___mbrtowc"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v8" : P = (Alloc 4) #4;
    %"v9" : P = (Alloc 8) #48;
    %"v12" : P = (Alloc 8) #8;
    %"v13" : P = (Alloc 8) #8;
    %"v17" : L = Ptoi %"v0";
    %"v18" : W = (Cmp Ne L) %"v17", #0
    => br %"v18" ? "L21" : "L20";
  @"L20":
    => goto "L21";
  @"L21" [%"v22" : P = phi("L20" => %"v8", "start" => %"v0")]:
    %"v24" = %"v9" +p #20;
    %"chk0" : A = (Check 0 4 Write 1) %"v24";
    store Ww [%"chk0" + 0] <- #0;
    %"v25" = %"v9" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v25";
    store Ww [%"chk1" + 0] <- #1;
    %"v26" = %"v9" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v26";
    store Ww [%"chk2" + 0] <- #1;
    %"v27" = %"v9" +p #32;
    %"v29" : L = Ptoi %"v6";
    %"v30" : W = (Cmp Ne L) %"v29", #0
    => br %"v30" ? "L33" : "L32";
  @"L32":
    %"v34" : P = Copy $"glibc_mbrtowc#state"
    => goto "L33";
  @"L33" [%"v35" : P = phi("L32" => %"v34", "L21" => %"v6")]:
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk3" + 0] <- %"v35";
    %"v40" : L = Ptoi %"v2";
    %"v41" : L = Ptoi #0;
    %"v42" : W = (Cmp Eq L) %"v40", %"v41"
    => br %"v42" ? "L36" : "L38";
  @"L36":
    %"v43" : P = Copy $"glibc_mbrtowc#str.270"
    => goto "L38";
  @"L38" [%"pr.7" : P = phi("L36" => %"v8", "L33" => %"v22"); %"pr.2" : L = phi("L36" => #1, "L33" => %"v4"); %"pr.1" : P = phi("L36" => %"v43", "L33" => %"v2")]:
    %"v48" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v48" ? "L44" : "L46";
  @"L44":
    => ret #18446744073709551614;
  @"L46":
    %"chk4" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v9";
    store.ptr [%"chk4" + 0] <- %"pr.7";
    %"v53" = %"v9" +p #8;
    %"v55" = %"pr.7" +p #4;
    %"chk5" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v53";
    store.ptr [%"chk5" + 0] <- %"v55";
    %"v56" : P = Copy $"__libc_tsd_LOCALE";
    %"chk6" : A = (Check 0 8 Read 8) %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Read 8) %"v57";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v4" = %"v59" +p #32;
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v4";
    %"iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"iw_1.v5";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v13" : W = (Cmp Eq L) %"iw_1.v11", %"v41"
    => br %"iw_1.v13" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    call void $"__wcsmbs_load_conv"(P %"v59")
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"chk10" : A = (Renew 0 8 Read 8) %"chk9", %"iw_1.v5";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk11" + 0] <- %"pr.1";
    %"chk12" : A = (Renew 0 8 Read 8) %"chk11", %"v13";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v64" = %"v62" +p %"pr.2";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v70" : L = Ptoi %"v64";
    %"v71" : L = Ptoi %"v69";
    %"v72" : W = (Cmp Ult L) %"v70", %"v71"
    => br %"v72" ? "L65" : "L67";
  @"L65":
    (Flight (a "v76") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v82" : L = Ptoi %"v76";
    %"v83" : L = Ptoi %"v81";
    %"v84" : W = (Cmp Eq L) %"v82", %"v83"
    => br %"v84" ? "L85" : "L67";
  @"L67" [%"pr.6" : P = phi("L65" => %"v76", "iw_1.L8" => %"v64")]:
    %"chk15" : A = (Check 0 8 Read 8) %"iw_1.v16";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v90" = %"v89" +p #40;
    %"chk16" : A = (Check 0 8 Read 8) %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk18" : A = (Check 0 8 Read 8) %"v96";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v98" : L = Ptoi %"v97";
    %"v100" : W = (Cmp Ne L) %"v98", %"v41"
    => br %"v100" ? "iw_2.join" : "L93";
  @"L93":
    => goto "iw_2.join";
  @"iw_2.join":
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk20" : F = CheckFunction %"v91";
    rawcall %"v107" : W = %"chk20"(P %"v105", P %"v9", P %"v13", P %"pr.6", P #0, P %"v12", W #0, W #1);
    %"v112" : W = (Cmp Eq W) %"v107", #0
    => br %"v112" ? "L114" : "L113";
  @"L113":
    %"v116" : W = (Cmp Eq W) %"v107", #4
    => goto "L114";
  @"L114" [%"v118" : W = phi("iw_2.join" => #1, "L113" => %"v116")]:
    => br %"v118" ? "L120" : "L119";
  @"L119":
    %"v122" : W = (Cmp Eq W) %"v107", #6
    => goto "L120";
  @"L120" [%"v124" : W = phi("L114" => #1, "L119" => %"v122")]:
    => br %"v124" ? "L126" : "L125";
  @"L125":
    %"v128" : W = (Cmp Eq W) %"v107", #7
    => goto "L126";
  @"L126" [%"v130" : W = phi("L120" => #1, "L125" => %"v128")]:
    => br %"v130" ? "L132" : "L131";
  @"L131":
    %"v134" : W = (Cmp Eq W) %"v107", #5
    => goto "L132";
  @"L132" [%"v136" : W = phi("L126" => #1, "L131" => %"v134")]:
    => br %"v136" ? "L110" : "L109";
  @"L109":
    %"v137" : P = Copy $"glibc_mbrtowc#str.271";
    %"v138" : P = Copy $"glibc_mbrtowc#str.272";
    %"v139" : P = Copy $"glibc_mbrtowc#str.273";
    call void $"__libc_assert_fail"(P %"v137", P %"v138", W #93, P %"v139")
    => goto "L110";
  @"L110":
    => br %"v112" ? "L146" : "L145";
  @"L145":
    %"v148" : W = (Cmp Eq W) %"v107", #4
    => goto "L146";
  @"L146" [%"v150" : W = phi("L110" => #1, "L145" => %"v148")]:
    => br %"v150" ? "L152" : "L151";
  @"L151":
    %"v154" : W = (Cmp Eq W) %"v107", #5
    => goto "L152";
  @"L152" [%"v156" : W = phi("L146" => #1, "L151" => %"v154")]:
    => br %"v156" ? "L140" : "L141";
  @"L140":
    %"chk21" : A = (Renew 0 8 Read 8) %"chk4", %"v9";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v162" : L = Ptoi %"v160";
    %"v163" : L = Ptoi %"pr.7";
    %"v164" : W = (Cmp Ne L) %"v162", %"v163"
    => br %"v164" ? "L165" : "L166";
  @"L165":
    %"chk22" : A = (Check 0 4 Read 1) %"pr.7";
    %"v168" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v169" : W = (Cmp Eq W) %"v168", #0
    => goto "L166";
  @"L166" [%"v171" : W = phi("L140" => #0, "L165" => %"v169")]:
    => br %"v171" ? "L157" : "L158";
  @"L157":
    %"v175" = %"v9" +p #32;
    %"chk23" : A = (Renew 0 8 Read 8) %"chk3", %"v175";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Check 0 4 Read 1) %"v176";
    %"v177" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v178" : W = (Cmp Eq W) %"v177", #0
    => br %"v178" ? "L142" : "L173";
  @"L173":
    %"v179" : P = Copy $"glibc_mbrtowc#str.274";
    %"v180" : P = Copy $"glibc_mbrtowc#str.272";
    %"v181" : P = Copy $"glibc_mbrtowc#str.273";
    call void $"__libc_assert_fail"(P %"v179", P %"v180", W #102, P %"v181")
    => goto "L142";
  @"L158":
    %"chk25" : A = (Renew 0 8 Read 8) %"chk11", %"v13";
    %"v182" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v184" : L = Ptoi %"v182";
    %"v185" : L = Ptoi %"pr.1";
    %"v186" : L = Sub %"v184", %"v185"
    => goto "L142";
  @"L141":
    %"v191" : W = (Cmp Eq W) %"v107", #7
    => br %"v191" ? "L142" : "L85";
  @"L85":
    %"v196" : P = Copy $"__libc_errno";
    %"chk26" : A = (Check 0 4 Write 1) %"v196";
    store Ww [%"chk26" + 0] <- #84
    => goto "L142";
  @"L142" [%"pr.3" : L = phi("L158" => %"v186", "L173" => #0, "L157" => #0, "L85" => #18446744073709551615, "L141" => #18446744073709551614)]:
    => ret %"pr.3"
} }.

Definition item___GI_mbrtowc : item :=
  (IAlias (a "__GI_mbrtowc") (a "export") (a "__GI___mbrtowc")).

Definition item_glibc_mbrtowc'23state : item :=
  (IData (a "glibc_mbrtowc#state") LLocal 4 [(Zero 8)]).

Definition item_glibc_mbrtowc'23str'2e270 : item :=
  (IData (a "glibc_mbrtowc#str.270") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_glibc_mbrtowc'23str'2e271 : item :=
  (IData (a "glibc_mbrtowc#str.271") (LRo (a "local")) 1 (app (app [(Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 79); (Item Wb 75); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78)] [(Item Wb 86); (Item Wb 95); (Item Wb 69); (Item Wb 77); (Item Wb 80); (Item Wb 84); (Item Wb 89); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 76); (Item Wb 76); (Item Wb 69); (Item Wb 71)]) (app [(Item Wb 65); (Item Wb 76); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 67); (Item Wb 79); (Item Wb 77); (Item Wb 80); (Item Wb 76); (Item Wb 69); (Item Wb 84); (Item Wb 69)] [(Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 70); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 79); (Item Wb 85); (Item Wb 84); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 0)]))).

Definition item_glibc_mbrtowc'23str'2e272 : item :=
  (IData (a "glibc_mbrtowc#str.272") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 98); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 119); (Item Wb 99); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_mbrtowc'23str'2e273 : item :=
  (IData (a "glibc_mbrtowc#str.273") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 109); (Item Wb 98); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 119); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_mbrtowc'23str'2e274 : item :=
  (IData (a "glibc_mbrtowc#str.274") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 32); (Item Wb 40); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 41); (Item Wb 0)]).

Definition item_mbrtowc : item :=
  (IAlias (a "mbrtowc") (a "weak") (a "__GI___mbrtowc")).

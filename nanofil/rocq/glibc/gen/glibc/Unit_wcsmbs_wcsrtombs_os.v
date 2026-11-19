(** This file defines checked IR from glibc’s `wcsmbs/wcsrtombs.os` object.
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

Definition fn___wcsrtombs : func :=
  ir_fn{ "export" "__wcsrtombs"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v8" : P = (Alloc 8) #48;
    %"v53" : P = (Alloc 4) #8;
    %"v54" : P = (Alloc 4) #256;
    %"v64" : P = (Alloc 8) #8;
    %"v67" : P = (Alloc 8) #8;
    %"v125" : P = (Alloc 8) #8;
    %"v13" = %"v8" +p #20;
    %"chk0" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk0" + 0] <- #0;
    %"v14" = %"v8" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v14";
    store Ww [%"chk1" + 0] <- #1;
    %"v15" = %"v8" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v15";
    store Ww [%"chk2" + 0] <- #1;
    %"v16" = %"v8" +p #32;
    %"v18" : L = Ptoi %"v6";
    %"v19" : W = (Cmp Ne L) %"v18", #0
    => br %"v19" ? "L22" : "L21";
  @"L21":
    %"v23" : P = Copy $"glibc_wcsrtombs#state"
    => goto "L22";
  @"L22" [%"v24" : P = phi("L21" => %"v23", "start" => %"v6")]:
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v16";
    store.ptr [%"chk3" + 0] <- %"v24";
    %"v25" : P = Copy $"__libc_tsd_LOCALE";
    %"chk4" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v26";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v4" = %"v28" +p #32;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v4";
    %"iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.v5";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v12" : L = Ptoi #0;
    %"iw_1.v13" : W = (Cmp Eq L) %"iw_1.v11", %"iw_1.v12"
    => br %"iw_1.v13" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    call void $"__wcsmbs_load_conv"(P %"v28")
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"chk8" : A = (Renew 0 8 Read 8) %"chk7", %"iw_1.v5";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v31" = %"iw_1.v16" +p #16;
    %"chk9" : A = (Check 0 8 Read 8) %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v35" = %"v32" +p #40;
    %"chk10" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk10", %"v32";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v42" : L = Ptoi %"v41";
    %"v44" : W = (Cmp Ne L) %"v42", %"iw_1.v12"
    => br %"v44" ? "L39" : "L38";
  @"L38":
    => goto "L39";
  @"L39":
    %"v50" : L = Ptoi %"v0";
    %"v52" : W = (Cmp Eq L) %"v50", %"iw_1.v12"
    => br %"v52" ? "L46" : "L47";
  @"L46":
    %"chk12" : A = (Check 0 8 Read 8) %"v2";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk12";
    call %"v60" : L = $"__wcslen"(P %"v59");
    %"v61" : L = Shl %"v60", #2;
    %"v62" = %"v57" +p %"v61";
    %"v63" = %"v62" +p #4;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk12", %"v2";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"v64";
    store.ptr [%"chk15" + 0] <- %"v66";
    %"v68" = %"v8" +p #32;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk3", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Read 1) %"v69";
    %"v70" : L = (RawLoad LdL 0) %"chk17";
    %"chk18" : A = (Check 0 8 Write 1) %"v53";
    store Wl [%"chk18" + 0] <- %"v70";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk3", %"v68";
    store.ptr [%"chk19" + 0] <- %"v53";
    %"v72" = %"v8" +p #8;
    %"v73" = %"v54" +p #256;
    %"chk20" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v72";
    store.ptr [%"chk20" + 0] <- %"v73"
    => goto "L74";
  @"L74" [%"pr.5" : L = phi("L46" => #0, "L74" => %"v87")]:
    %"chk21" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v8";
    store.ptr [%"chk21" + 0] <- %"v54";
    %"chk22" : F = CheckFunction %"v36";
    rawcall %"v81" : W = %"chk22"(P %"v32", P %"v8", P %"v64", P %"v63", P #0, P %"v67", W #0, W #1);
    %"chk23" : A = (Renew 0 8 Read 8) %"chk21", %"v8";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v84" : L = Ptoi %"v83";
    %"v85" : L = Ptoi %"v54";
    %"v86" : L = Sub %"v84", %"v85";
    %"v87" : L = Add %"pr.5", %"v86";
    %"v89" : W = (Cmp Eq W) %"v81", #5
    => br %"v89" ? poll "L74" : "L76";
  @"L76":
    %"v94" : W = (Cmp Eq W) %"v81", #0
    => br %"v94" ? "L96" : "L95";
  @"L95":
    %"v98" : W = (Cmp Eq W) %"v81", #4
    => goto "L96";
  @"L96" [%"v100" : W = phi("L76" => #1, "L95" => %"v98")]:
    => br %"v100" ? "L90" : "L48";
  @"L90":
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v107" = %"v104" +p #18446744073709551615;
    %"chk25" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Ub) 0) %"chk25";
    %"v109" : W = (Cmp Eq W) %"v108", #0
    => br %"v109" ? "L103" : "L102";
  @"L102":
    %"v110" : P = Copy $"glibc_wcsrtombs#str.270";
    %"v111" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v112" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v110", P %"v111", W #91, P %"v112")
    => goto "L103";
  @"L103":
    %"v114" : L = Sub %"v87", #1
    => goto "L48";
  @"L47":
    %"chk26" : A = (Check 0 8 Read 8) %"v2";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call %"v121" : L = $"__wcsnlen"(P %"v119", L %"v4");
    %"v122" : L = Shl %"v121", #2;
    %"v123" = %"v117" +p %"v122";
    %"v124" = %"v123" +p #4;
    %"chk28" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v8";
    store.ptr [%"chk28" + 0] <- %"v0";
    %"v127" = %"v8" +p #8;
    %"v130" = %"v0" +p %"v4";
    %"chk29" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v127";
    store.ptr [%"chk29" + 0] <- %"v130";
    %"chk30" : F = CheckFunction %"v36";
    rawcall %"v136" : W = %"chk30"(P %"v32", P %"v8", P %"v2", P %"v124", P #0, P %"v125", W #0, W #1);
    %"chk31" : A = (Renew 0 8 Read 8) %"chk28", %"v8";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v139" : L = Ptoi %"v137";
    %"v141" : L = Sub %"v139", %"v50";
    %"v146" : W = (Cmp Eq W) %"v136", #0
    => br %"v146" ? "L148" : "L147";
  @"L147":
    %"v150" : W = (Cmp Eq W) %"v136", #4
    => goto "L148";
  @"L148" [%"v152" : W = phi("L47" => #1, "L147" => %"v150")]:
    => br %"v152" ? "L153" : "L154";
  @"L153":
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v158" = %"v155" +p #18446744073709551615;
    %"chk33" : A = (Check 0 1 Read 1) %"v158";
    %"v159" : W = (RawLoad (LdNarrow Ub) 0) %"chk33";
    %"v160" : W = (Cmp Eq W) %"v159", #0
    => goto "L154";
  @"L154" [%"v162" : W = phi("L148" => #0, "L153" => %"v160")]:
    => br %"v162" ? "L142" : "L48";
  @"L142":
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v168" : L = Ptoi %"v166";
    %"v170" : W = (Cmp Ne L) %"v168", %"v50"
    => br %"v170" ? "L165" : "L164";
  @"L164":
    %"v171" : P = Copy $"glibc_wcsrtombs#str.273";
    %"v172" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v173" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v171", P %"v172", W #119, P %"v173")
    => goto "L165";
  @"L165":
    %"v177" = %"v8" +p #32;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk3", %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Check 0 4 Read 1) %"v178";
    %"v179" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v180" : W = (Cmp Eq W) %"v179", #0
    => br %"v180" ? "L176" : "L175";
  @"L175":
    %"v181" : P = Copy $"glibc_wcsrtombs#str.274";
    %"v182" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v183" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v181", P %"v182", W #120, P %"v183")
    => goto "L176";
  @"L176":
    %"chk37" : A = (Renew 0 8 Write 8) %"chk26", %"v2";
    store.ptr [%"chk37" + 0] <- #0;
    %"v186" : L = Sub %"v141", #1
    => goto "L48";
  @"L48" [%"pr.4" : L = phi("L103" => %"v114", "L96" => %"v87", "L176" => %"v186", "L154" => %"v141"); %"pr.1" : W = phi("L103" => %"v81", "L96" => %"v81", "L176" => %"v136", "L154" => %"v136")]:
    %"v191" : W = (Cmp Eq W) %"pr.1", #0
    => br %"v191" ? "L193" : "L192";
  @"L192":
    %"v195" : W = (Cmp Eq W) %"pr.1", #4
    => goto "L193";
  @"L193" [%"v197" : W = phi("L48" => #1, "L192" => %"v195")]:
    => br %"v197" ? "L199" : "L198";
  @"L198":
    %"v201" : W = (Cmp Eq W) %"pr.1", #6
    => goto "L199";
  @"L199" [%"v203" : W = phi("L193" => #1, "L198" => %"v201")]:
    => br %"v203" ? "L205" : "L204";
  @"L204":
    %"v207" : W = (Cmp Eq W) %"pr.1", #7
    => goto "L205";
  @"L205" [%"v209" : W = phi("L199" => #1, "L204" => %"v207")]:
    => br %"v209" ? "L211" : "L210";
  @"L210":
    %"v213" : W = (Cmp Eq W) %"pr.1", #5
    => goto "L211";
  @"L211" [%"v215" : W = phi("L205" => #1, "L210" => %"v213")]:
    => br %"v215" ? "L189" : "L188";
  @"L188":
    %"v216" : P = Copy $"glibc_wcsrtombs#str.275";
    %"v217" : P = Copy $"glibc_wcsrtombs#str.271";
    %"v218" : P = Copy $"glibc_wcsrtombs#str.272";
    call void $"__libc_assert_fail"(P %"v216", P %"v217", W #131, P %"v218")
    => goto "L189";
  @"L189":
    %"v223" : W = (Cmp Ne W) %"pr.1", #0
    => br %"v223" ? "L224" : "L225";
  @"L224":
    %"v227" : W = (Cmp Ne W) %"pr.1", #5
    => goto "L225";
  @"L225" [%"v229" : W = phi("L189" => #0, "L224" => %"v227")]:
    => br %"v229" ? "L230" : "L231";
  @"L230":
    %"v233" : W = (Cmp Ne W) %"pr.1", #4
    => goto "L231";
  @"L231" [%"v235" : W = phi("L225" => #0, "L230" => %"v233")]:
    => br %"v235" ? "L219" : "L221";
  @"L219":
    %"v238" : P = Copy $"__libc_errno";
    %"chk38" : A = (Check 0 4 Write 1) %"v238";
    store Ww [%"chk38" + 0] <- #84
    => goto "L221";
  @"L221" [%"pr.3" : L = phi("L219" => #18446744073709551615, "L231" => %"pr.4")]:
    => ret %"pr.3"
} }.

Definition item_glibc_wcsrtombs'23state : item :=
  (IData (a "glibc_wcsrtombs#state") LLocal 4 [(Zero 8)]).

Definition item_glibc_wcsrtombs'23str'2e270 : item :=
  (IData (a "glibc_wcsrtombs#str.270") (LRo (a "local")) 1 [(Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 91); (Item Wb 45); (Item Wb 49); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 39); (Item Wb 92); (Item Wb 48); (Item Wb 39); (Item Wb 0)]).

Definition item_glibc_wcsrtombs'23str'2e271 : item :=
  (IData (a "glibc_wcsrtombs#str.271") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 99); (Item Wb 115); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_wcsrtombs'23str'2e272 : item :=
  (IData (a "glibc_wcsrtombs#str.272") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 99); (Item Wb 115); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 0)]).

Definition item_glibc_wcsrtombs'23str'2e273 : item :=
  (IData (a "glibc_wcsrtombs#str.273") (LRo (a "local")) 1 [(Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 32); (Item Wb 42); (Item Wb 41); (Item Wb 32); (Item Wb 100); (Item Wb 115); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_wcsrtombs'23str'2e274 : item :=
  (IData (a "glibc_wcsrtombs#str.274") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 32); (Item Wb 40); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 41); (Item Wb 0)]).

Definition item_glibc_wcsrtombs'23str'2e275 : item :=
  (IData (a "glibc_wcsrtombs#str.275") (LRo (a "local")) 1 (app (app [(Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 79); (Item Wb 75); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78)] [(Item Wb 86); (Item Wb 95); (Item Wb 69); (Item Wb 77); (Item Wb 80); (Item Wb 84); (Item Wb 89); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 76); (Item Wb 76); (Item Wb 69); (Item Wb 71)]) (app [(Item Wb 65); (Item Wb 76); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 67); (Item Wb 79); (Item Wb 77); (Item Wb 80); (Item Wb 76); (Item Wb 69); (Item Wb 84); (Item Wb 69)] [(Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 70); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 79); (Item Wb 85); (Item Wb 84); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 0)]))).

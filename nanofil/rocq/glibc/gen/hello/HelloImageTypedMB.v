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

Definition hello_image_fn_mbszero : func :=
  ir_fn{ "export" "mbszero"(P %"v0") -> RVoid {
  @"start":
    call %"v3" : P = $"memset"(P %"v0", W #0, L #8)
    => ret void
} }.

Definition hello_image_fn_mbrtoc32 : func :=
  ir_fn{ "export" "mbrtoc32"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v6";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    %"v15" : P = Copy $"glibc_mbrtoc32#state"
    => goto "L10";
  @"L10" [%"pr.1" : P = phi("L8" => %"v15", "start" => %"v6")]:
    call %"v20" : L = $"__GI_mbrtowc"(P %"v0", P %"v2", L %"v4", P %"pr.1")
    => ret %"v20"
} }.

Definition hello_image_fn___GI___mbrtowc : func :=
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

Definition hello_image_fn___mbsinit : func :=
  ir_fn{ "export" "__mbsinit"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" : L = Ptoi %"v0";
    %"v4" : L = Ptoi #0;
    %"v5" : W = (Cmp Eq L) %"v3", %"v4"
    => br %"v5" ? "L7" : "L6";
  @"L6":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => goto "L7";
  @"L7" [%"v12" : W = phi("start" => #1, "L6" => %"v10")]:
    => ret %"v12"
} }.

Definition hello_image_fn___mbsrtowcs : func :=
  ir_fn{ "export" "__mbsrtowcs"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v6";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L16" : "L15";
  @"L15":
    %"v17" : P = Copy $"glibc_mbsrtowcs#state"
    => goto "L16";
  @"L16" [%"v18" : P = phi("L15" => %"v17", "start" => %"v6")]:
    %"v19" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v21" : L = $"__mbsrtowcs_l"(P %"v0", P %"v2", L %"v4", P %"v18", P %"v20")
    => ret %"v21"
} }.

Definition hello_image_fn___mbsrtowcs_l : func :=
  ir_fn{ "export" "__mbsrtowcs_l"(P %"v0", P %"v2", L %"v4", P %"v6", P %"v8") -> (RClass L) {
  @"start":
    %"v10" : P = (Alloc 8) #48;
    %"v14" : P = (Alloc 8) #8;
    %"v47" : P = (Alloc 4) #8;
    %"v48" : P = (Alloc 4) #256;
    %"v49" : P = (Alloc 8) #8;
    %"v108" : P = (Alloc 8) #8;
    %"v16" = %"v10" +p #20;
    %"chk0" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk0" + 0] <- #0;
    %"v17" = %"v10" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v17";
    store Ww [%"chk1" + 0] <- #1;
    %"v18" = %"v10" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v18";
    store Ww [%"chk2" + 0] <- #1;
    %"v19" = %"v10" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v19";
    store.ptr [%"chk3" + 0] <- %"v6";
    %"chk4" : A = (Check 0 8 Read 8) %"v8";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v4" = %"v23" +p #32;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v4";
    %"iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v5";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v12" : L = Ptoi #0;
    %"iw_1.v13" : W = (Cmp Eq L) %"iw_1.v11", %"iw_1.v12"
    => br %"iw_1.v13" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    call void $"__wcsmbs_load_conv"(P %"v23")
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"chk7" : A = (Renew 0 8 Read 8) %"chk6", %"iw_1.v5";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v16";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v29" = %"v26" +p #40;
    %"chk9" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (HalfCheck Lower 0 8 Read 8) %"chk9", %"v26";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v36" : L = Ptoi %"v35";
    %"v38" : W = (Cmp Ne L) %"v36", %"iw_1.v12"
    => br %"v38" ? "L33" : "L32";
  @"L32":
    => goto "L33";
  @"L33":
    %"v44" : L = Ptoi %"v0";
    %"v46" : W = (Cmp Eq L) %"v44", %"iw_1.v12"
    => br %"v46" ? "L40" : "L41";
  @"L40":
    %"chk11" : A = (Check 0 8 Read 8) %"v2";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk12" + 0] <- %"v51";
    %"chk13" : A = (Renew 0 8 Read 8) %"chk12", %"v49";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Renew 0 8 Read 8) %"chk11", %"v2";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk14";
    call %"v56" : L = $"__GI_strlen"(P %"v55");
    %"v57" = %"v53" +p %"v56";
    %"v58" = %"v57" +p #1;
    %"v59" = %"v10" +p #32;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk3", %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Check 0 8 Read 1) %"v60";
    %"v61" : L = (RawLoad LdL 0) %"chk16";
    %"chk17" : A = (Check 0 8 Write 1) %"v47";
    store Wl [%"chk17" + 0] <- %"v61";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk3", %"v59";
    store.ptr [%"chk18" + 0] <- %"v47";
    %"v63" = %"v10" +p #8;
    %"v64" = %"v48" +p #256;
    %"chk19" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v63";
    store.ptr [%"chk19" + 0] <- %"v64"
    => goto "L65";
  @"L65" [%"pr.5" : L = phi("L40" => #0, "L65" => %"v79")]:
    %"chk20" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v10";
    store.ptr [%"chk20" + 0] <- %"v48";
    %"chk21" : F = CheckFunction %"v30";
    rawcall %"v72" : W = %"chk21"(P %"v26", P %"v10", P %"v49", P %"v58", P #0, P %"v14", W #0, W #1);
    %"chk22" : A = (Renew 0 8 Read 8) %"chk20", %"v10";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v75" : L = Ptoi %"v74";
    %"v76" : L = Ptoi %"v48";
    %"v77" : L = Sub %"v75", %"v76";
    %"v78" : L = Div %"v77", #4;
    %"v79" : L = Add %"pr.5", %"v78";
    %"v81" : W = (Cmp Eq W) %"v72", #5
    => br %"v81" ? poll "L65" : "L67";
  @"L67":
    %"v86" : W = (Cmp Eq W) %"v72", #0
    => br %"v86" ? "L88" : "L87";
  @"L87":
    %"v90" : W = (Cmp Eq W) %"v72", #4
    => goto "L88";
  @"L88" [%"v92" : W = phi("L67" => #1, "L87" => %"v90")]:
    => br %"v92" ? "L82" : "L42";
  @"L82":
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v100" = %"v96" +p #18446744073709551612;
    %"chk24" : A = (Check 0 4 Read 1) %"v100";
    %"v101" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v102" : W = (Cmp Eq W) %"v101", #0
    => br %"v102" ? "L95" : "L94";
  @"L94":
    %"v103" : P = Copy $"glibc_mbsrtowcs_l#str.270";
    %"v104" : P = Copy $"glibc_mbsrtowcs_l#str.271";
    %"v105" : P = Copy $"glibc_mbsrtowcs_l#str.272";
    call void $"__libc_assert_fail"(P %"v103", P %"v104", W #91, P %"v105")
    => goto "L95";
  @"L95":
    %"v107" : L = Sub %"v79", #1
    => goto "L42";
  @"L41":
    %"chk25" : A = (Check 0 8 Read 8) %"v2";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Check 0 8 Write 8) %"v108";
    store.ptr [%"chk26" + 0] <- %"v110";
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v10";
    store.ptr [%"chk27" + 0] <- %"v0";
    %"v113" = %"v10" +p #8;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk27", %"v10";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v116" : L = Shl %"v4", #2;
    %"v117" = %"v114" +p %"v116";
    %"chk29" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v113";
    store.ptr [%"chk29" + 0] <- %"v117"
    => goto "L118";
  @"L118" [%"pr.7" : W = phi("L136" => %"v133", "L41" => #5); %"pr.1" : L = phi("L136" => %"v171", "L41" => %"v4")]:
    %"v122" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v122" ? "L119" : "L120";
  @"L119":
    %"chk30" : A = (Renew 0 8 Read 8) %"chk26", %"v108";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk30";
    call %"v126" : L = $"__GI___strnlen"(P %"v124", L %"pr.1");
    %"v127" = %"v123" +p %"v126";
    %"v128" = %"v127" +p #1;
    %"chk32" : F = CheckFunction %"v30";
    rawcall %"v133" : W = %"chk32"(P %"v26", P %"v10", P %"v108", P %"v128", P #0, P %"v14", W #0, W #1);
    %"v138" : W = (Cmp Ne W) %"v133", #4
    => br %"v138" ? "L139" : "L140";
  @"L139":
    %"v142" : W = (Cmp Ne W) %"v133", #7
    => goto "L140";
  @"L140" [%"v144" : W = phi("L119" => #0, "L139" => %"v142")]:
    => br %"v144" ? "L146" : "L145";
  @"L145":
    %"chk33" : A = (Renew 0 8 Read 8) %"chk26", %"v108";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v149" : L = Ptoi %"v147";
    %"v150" : L = Ptoi %"v128";
    %"v151" : W = (Cmp Ne L) %"v149", %"v150"
    => goto "L146";
  @"L146" [%"v153" : W = phi("L140" => #1, "L145" => %"v151")]:
    => br %"v153" ? "L155" : "L154";
  @"L154":
    %"v159" = %"v128" +p #18446744073709551615;
    %"chk34" : A = (Check 0 1 Read 1) %"v159";
    %"v160" : W = (RawLoad (LdNarrow Ub) 0) %"chk34";
    %"v161" : W = (Cmp Eq W) %"v160", #0
    => goto "L155";
  @"L155" [%"v163" : W = phi("L146" => #1, "L154" => %"v161")]:
    => br %"v163" ? "L120" : "L136";
  @"L136":
    %"v165" = %"v10" +p #8;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk29", %"v165";
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Read 8) %"chk27", %"v10";
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v168" : L = Ptoi %"v166";
    %"v169" : L = Ptoi %"v167";
    %"v170" : L = Sub %"v168", %"v169";
    %"v171" : L = Div %"v170", #4
    => goto poll "L118";
  @"L120" [%"pr.8" : W = phi("L118" => %"pr.7", "L155" => %"v133")]:
    %"chk37" : A = (Renew 0 8 Read 8) %"chk26", %"v108";
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"chk38" : A = (Renew 0 8 Write 8) %"chk25", %"v2";
    store.ptr [%"chk38" + 0] <- %"v173";
    %"chk39" : A = (Renew 0 8 Read 8) %"chk27", %"v10";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v176" : L = Ptoi %"v174";
    %"v178" : L = Sub %"v176", %"v44";
    %"v179" : L = Div %"v178", #4;
    %"v184" : W = (Cmp Eq W) %"pr.8", #0
    => br %"v184" ? "L186" : "L185";
  @"L185":
    %"v188" : W = (Cmp Eq W) %"pr.8", #4
    => goto "L186";
  @"L186" [%"v190" : W = phi("L120" => #1, "L185" => %"v188")]:
    => br %"v190" ? "L191" : "L192";
  @"L191":
    %"v195" : L = Sub %"v179", #1;
    %"v196" : L = Shl %"v195", #2;
    %"v197" = %"v0" +p %"v196";
    %"chk40" : A = (Check 0 4 Read 1) %"v197";
    %"v198" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v199" : W = (Cmp Eq W) %"v198", #0
    => goto "L192";
  @"L192" [%"v201" : W = phi("L186" => #0, "L191" => %"v199")]:
    => br %"v201" ? "L180" : "L42";
  @"L180":
    %"v206" : W = (Cmp Ugt L) %"v179", #0
    => br %"v206" ? "L204" : "L203";
  @"L203":
    %"v207" : P = Copy $"glibc_mbsrtowcs_l#str.273";
    %"v208" : P = Copy $"glibc_mbsrtowcs_l#str.271";
    %"v209" : P = Copy $"glibc_mbsrtowcs_l#str.272";
    call void $"__libc_assert_fail"(P %"v207", P %"v208", W #138, P %"v209")
    => goto "L204";
  @"L204":
    %"v213" = %"v10" +p #32;
    %"chk41" : A = (Renew 0 8 Read 8) %"chk3", %"v213";
    %"v214" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"chk42" : A = (Check 0 4 Read 1) %"v214";
    %"v215" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v216" : W = (Cmp Eq W) %"v215", #0
    => br %"v216" ? "L212" : "L211";
  @"L211":
    %"v217" : P = Copy $"glibc_mbsrtowcs_l#str.274";
    %"v218" : P = Copy $"glibc_mbsrtowcs_l#str.271";
    %"v219" : P = Copy $"glibc_mbsrtowcs_l#str.272";
    call void $"__libc_assert_fail"(P %"v217", P %"v218", W #139, P %"v219")
    => goto "L212";
  @"L212":
    %"chk43" : A = (Renew 0 8 Write 8) %"chk25", %"v2";
    store.ptr [%"chk43" + 0] <- #0;
    %"v222" : L = Sub %"v179", #1
    => goto "L42";
  @"L42" [%"pr.9" : W = phi("L95" => %"v72", "L88" => %"v72", "L212" => %"pr.8", "L192" => %"pr.8"); %"pr.4" : L = phi("L95" => %"v107", "L88" => %"v79", "L212" => %"v222", "L192" => %"v179")]:
    %"v227" : W = (Cmp Eq W) %"pr.9", #0
    => br %"v227" ? "L229" : "L228";
  @"L228":
    %"v231" : W = (Cmp Eq W) %"pr.9", #4
    => goto "L229";
  @"L229" [%"v233" : W = phi("L42" => #1, "L228" => %"v231")]:
    => br %"v233" ? "L235" : "L234";
  @"L234":
    %"v237" : W = (Cmp Eq W) %"pr.9", #6
    => goto "L235";
  @"L235" [%"v239" : W = phi("L229" => #1, "L234" => %"v237")]:
    => br %"v239" ? "L241" : "L240";
  @"L240":
    %"v243" : W = (Cmp Eq W) %"pr.9", #7
    => goto "L241";
  @"L241" [%"v245" : W = phi("L235" => #1, "L240" => %"v243")]:
    => br %"v245" ? "L247" : "L246";
  @"L246":
    %"v249" : W = (Cmp Eq W) %"pr.9", #5
    => goto "L247";
  @"L247" [%"v251" : W = phi("L241" => #1, "L246" => %"v249")]:
    => br %"v251" ? "L225" : "L224";
  @"L224":
    %"v252" : P = Copy $"glibc_mbsrtowcs_l#str.275";
    %"v253" : P = Copy $"glibc_mbsrtowcs_l#str.271";
    %"v254" : P = Copy $"glibc_mbsrtowcs_l#str.272";
    call void $"__libc_assert_fail"(P %"v252", P %"v253", W #150, P %"v254")
    => goto "L225";
  @"L225":
    %"v259" : W = (Cmp Ne W) %"pr.9", #0
    => br %"v259" ? "L260" : "L261";
  @"L260":
    %"v263" : W = (Cmp Ne W) %"pr.9", #5
    => goto "L261";
  @"L261" [%"v265" : W = phi("L225" => #0, "L260" => %"v263")]:
    => br %"v265" ? "L266" : "L267";
  @"L266":
    %"v269" : W = (Cmp Ne W) %"pr.9", #4
    => goto "L267";
  @"L267" [%"v271" : W = phi("L261" => #0, "L266" => %"v269")]:
    => br %"v271" ? "L272" : "L273";
  @"L272":
    %"v275" : W = (Cmp Ne W) %"pr.9", #7
    => goto "L273";
  @"L273" [%"v277" : W = phi("L267" => #0, "L272" => %"v275")]:
    => br %"v277" ? "L255" : "L257";
  @"L255":
    %"v280" : P = Copy $"__libc_errno";
    %"chk44" : A = (Check 0 4 Write 1) %"v280";
    store Ww [%"chk44" + 0] <- #84
    => goto "L257";
  @"L257" [%"pr.3" : L = phi("L255" => #18446744073709551615, "L273" => %"pr.4")]:
    => ret %"pr.3"
} }.

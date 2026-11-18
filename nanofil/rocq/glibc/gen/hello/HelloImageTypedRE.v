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

Definition hello_image_fn___readonly_area_fallback : func :=
  ir_fn{ "export" "__readonly_area_fallback"(P %"v0", L %"v2") -> (RClass W) {
  @"start":
    %"v58" : P = (Alloc 8) #8;
    %"v59" : P = (Alloc 8) #8;
    %"v73" : P = (Alloc 8) #8;
    %"v94" : P = (Alloc 8) #8;
    %"v7" = %"v0" +p %"v2";
    %"v9" : P = Copy $"glibc_readonly_area_fallback#str.252";
    %"v10" : P = Copy $"glibc_readonly_area_fallback#str.253";
    call %"v11" : P = $"_IO_new_fopen"(P %"v9", P %"v10");
    %"v16" : L = Ptoi %"v11";
    %"v17" : L = Ptoi #0;
    %"v18" : W = (Cmp Eq L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L14";
  @"L12":
    %"v22" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Read 1) %"v22";
    %"v23" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v24" : W = (Cmp Eq W) %"v23", #2
    => br %"v24" ? "L26" : "L25";
  @"L25":
    %"v27" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Read 1) %"v27";
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v29" : W = (Cmp Eq W) %"v28", #13
    => goto "L26";
  @"L26" [%"v31" : W = phi("L12" => #1, "L25" => %"v29")]:
    => br %"v31" ? "L19" : "L21";
  @"L19":
    => ret #2;
  @"L21":
    => ret #3;
  @"L14":
    %"chk2" : A = (Check 0 4 Read 1) %"v11";
    %"v39" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v40" : W = And %"v39", #32768
    => br %"v40" ? "L42" : "L36";
  @"L36":
    => goto "L42";
  @"L42":
    %"v47" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v49" : W = And %"v47", #4294934527;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk2", %"v11";
    store Ww [%"chk4" + 0] <- %"v49";
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v56" : W = Or %"v55", #32768;
    store Ww [%"chk4" + 0] <- %"v56";
    %"chk7" : A = (Check 0 8 Write 8) %"v58";
    store.ptr [%"chk7" + 0] <- #0;
    %"chk8" : A = (Check 0 8 Write 1) %"v59";
    store Wl [%"chk8" + 0] <- #0
    => goto "L60";
  @"L60" [%"pr.4" : L = phi("L42" => %"v2", "L164" => %"pr.2", "L123" => %"pr.4")]:
    call %"v64" : W = $"__feof_unlocked"(P %"v11");
    %"v65" : W = (Cmp Eq W) %"v64", #0
    => br %"v65" ? "L61" : "L62";
  @"L61":
    call %"v70" : L = $"__GI___getdelim"(P %"v58", P %"v59", W #10, P %"v11");
    %"v71" : W = (Cmp Sle L) %"v70", #0
    => br %"v71" ? "L62" : "L68";
  @"L68":
    %"chk9" : A = (Renew 0 8 Read 8) %"chk7", %"v58";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call %"v76" : L = $"__GI___isoc23_strtoul"(P %"v75", P %"v73", W #16);
    %"chk10" : A = (Check 0 8 Read 8) %"v73";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Renew 0 8 Read 8) %"chk7", %"v58";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v82" : L = Ptoi %"v80";
    %"v83" : L = Ptoi %"v81";
    %"v84" : W = (Cmp Eq L) %"v82", %"v83"
    => br %"v84" ? "L86" : "L85";
  @"L85":
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v88" = %"v87" +p #1;
    %"chk13" : A = (Renew 0 8 Write 8) %"chk10", %"v73";
    store.ptr [%"chk13" + 0] <- %"v88";
    %"chk14" : A = (Check 0 1 Read 1) %"v87";
    %"v89" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v90" : W = (Cmp Ne W) %"v89", #45
    => goto "L86";
  @"L86" [%"v92" : W = phi("L68" => #1, "L85" => %"v90")]:
    => br %"v92" ? "L62" : "L79";
  @"L79":
    %"chk15" : A = (Renew 0 8 Read 8) %"chk10", %"v73";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call %"v97" : L = $"__GI___isoc23_strtoul"(P %"v96", P %"v94", W #16);
    %"chk16" : A = (Check 0 8 Read 8) %"v94";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Renew 0 8 Read 8) %"chk10", %"v73";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v103" : L = Ptoi %"v101";
    %"v104" : L = Ptoi %"v102";
    %"v105" : W = (Cmp Eq L) %"v103", %"v104"
    => br %"v105" ? "L107" : "L106";
  @"L106":
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v109" = %"v108" +p #1;
    %"chk19" : A = (Renew 0 8 Write 8) %"chk16", %"v94";
    store.ptr [%"chk19" + 0] <- %"v109";
    %"chk20" : A = (Check 0 1 Read 1) %"v108";
    %"v110" : W = (RawLoad (LdNarrow Sb) 0) %"chk20";
    %"v111" : W = (Cmp Ne W) %"v110", #32
    => goto "L107";
  @"L107" [%"v113" : W = phi("L79" => #1, "L106" => %"v111")]:
    => br %"v113" ? "L62" : "L100";
  @"L100":
    %"v120" : L = Ptoi %"v7";
    %"v121" : W = (Cmp Ult L) %"v76", %"v120"
    => br %"v121" ? "L122" : "L123";
  @"L122":
    %"v126" : L = Ptoi %"v0";
    %"v127" : W = (Cmp Ugt L) %"v97", %"v126"
    => goto "L123";
  @"L123" [%"v129" : W = phi("L100" => #0, "L122" => %"v127")]:
    => br %"v129" ? "L115" : poll "L60";
  @"L115":
    %"chk21" : A = (Renew 0 8 Read 8) %"chk16", %"v94";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v134" = %"v133" +p #1;
    %"chk22" : A = (Renew 0 8 Write 8) %"chk16", %"v94";
    store.ptr [%"chk22" + 0] <- %"v134";
    %"chk23" : A = (Check 0 1 Read 1) %"v133";
    %"v135" : W = (RawLoad (LdNarrow Sb) 0) %"chk23";
    %"v136" : W = (Cmp Ne W) %"v135", #114
    => br %"v136" ? "L138" : "L137";
  @"L137":
    %"chk24" : A = (Renew 0 8 Read 8) %"chk16", %"v94";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v140" = %"v139" +p #1;
    %"chk25" : A = (Renew 0 8 Write 8) %"chk16", %"v94";
    store.ptr [%"chk25" + 0] <- %"v140";
    %"chk26" : A = (Check 0 1 Read 1) %"v139";
    %"v141" : W = (RawLoad (LdNarrow Sb) 0) %"chk26";
    %"v142" : W = (Cmp Ne W) %"v141", #45
    => goto "L138";
  @"L138" [%"v144" : W = phi("L115" => #1, "L137" => %"v142")]:
    => br %"v144" ? "L62" : "L132";
  @"L132":
    %"v151" : L = Ptoi %"v0";
    %"v152" : W = (Cmp Ule L) %"v76", %"v151"
    => br %"v152" ? "L153" : "L154";
  @"L153":
    %"v158" : W = (Cmp Uge L) %"v97", %"v120"
    => goto "L154";
  @"L154" [%"v160" : W = phi("L132" => #0, "L153" => %"v158")]:
    => br %"v160" ? "L62" : "L147";
  @"L147":
    => br %"v152" ? "L162" : "L163";
  @"L162":
    %"v173" : L = Sub %"v97", %"v151";
    %"v174" : L = Sub %"pr.4", %"v173"
    => goto "L164";
  @"L163":
    %"v181" : W = (Cmp Uge L) %"v97", %"v120"
    => br %"v181" ? "L175" : "L176";
  @"L175":
    %"v186" : L = Sub %"v120", %"v76";
    %"v187" : L = Sub %"pr.4", %"v186"
    => goto "L164";
  @"L176":
    %"v191" : L = Sub %"v97", %"v76";
    %"v192" : L = Sub %"pr.4", %"v191"
    => goto "L164";
  @"L164" [%"pr.2" : L = phi("L162" => %"v174", "L175" => %"v187", "L176" => %"v192")]:
    %"v198" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v198" ? "L62" : poll "L60";
  @"L62" [%"pr.5" : L = phi("L60" => %"pr.4", "L61" => %"pr.4", "L86" => %"pr.4", "L107" => %"pr.4", "L138" => %"pr.4", "L154" => #0, "L164" => %"pr.2")]:
    call %"v201" : W = $"_IO_new_fclose"(P %"v11");
    %"chk27" : A = (Renew 0 8 Read 8) %"chk7", %"v58";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk27";
    call void $"free"(P %"v202");
    %"v207" : W = (Cmp Eq L) %"pr.5", #0
    => br %"v207" ? "L205" : "L204";
  @"L204":
    => goto "L205";
  @"L205" [%"v208" : W = phi("L204" => #1, "L62" => #0)]:
    => ret %"v208"
} }.

Definition hello_image_fn___readonly_area : func :=
  ir_fn{ "export" "__readonly_area"(P %"v0", L %"v2") -> (RClass W) {
  @"start":
    call %"v6" : W = $"__readonly_area_fallback"(P %"v0", L %"v2")
    => ret %"v6"
} }.

Definition hello_image_fn___GI___readdir64 : func :=
  ir_fn{ "export" "__GI___readdir64"(P %"v0") -> (RClass P) {
  @"start":
    %"v4" = %"v0" +p #4;
    %"chk0" : A = (Check 0 4 Write 4) %"v4";
    %"v11" : W = (RawCas (CasNarrow Sw) 0) %"chk0", #0, #1;
    %"v12" : W = (Cmp Eq W) %"v11", #0
    => br %"v12" ? "L14" : "L13";
  @"L13":
    => goto "L14";
  @"L14":
    %"v15" : W = (Cmp Ne W) %"v11", #0
    => br %"v15" ? "L18" : "iw_1.start";
  @"L18":
    call void $"__GI___lll_lock_wait_private"(P %"v4")
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v4" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Read 1) %"iw_1.v4";
    %"iw_1.v5" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"iw_1.v10" = %"v0" +p #24;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v10";
    %"iw_1.v11" : L = (RawLoad LdL 0) %"chk2";
    %"iw_1.v13" = %"v0" +p #16;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v13";
    %"iw_1.v14" : L = (RawLoad LdL 0) %"chk3";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v11", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L6" : "iw_1.L8";
  @"iw_1.L6":
    %"iw_1.v18" = %"v0" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v18";
    %"iw_1.v19" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"iw_1.v24" = %"v0" +p #48;
    call %"iw_1.v26" : L = $"__GI___getdents64"(W %"iw_1.v22", P %"iw_1.v24", L %"iw_1.v19");
    %"iw_1.v31" : W = (Cmp Sle L) %"iw_1.v26", #0
    => br %"iw_1.v31" ? "iw_1.L27" : "iw_1.L29";
  @"iw_1.L27":
    %"iw_1.v36" : W = (Cmp Eq L) %"iw_1.v26", #0
    => br %"iw_1.v36" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v39" : P = Copy $"__libc_errno";
    %"chk6" : A = (Check 0 4 Read 1) %"iw_1.v39";
    %"iw_1.v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"iw_1.v41" : W = (Cmp Eq W) %"iw_1.v40", #2
    => goto "iw_1.L38";
  @"iw_1.L38" [%"iw_1.v43" : W = phi("iw_1.L27" => #1, "iw_1.L37" => %"iw_1.v41")]:
    => br %"iw_1.v43" ? "iw_1.L32" : "iw_1.join";
  @"iw_1.L32":
    %"iw_1.v44" : P = Copy $"__libc_errno";
    %"chk7" : A = (Check 0 4 Write 1) %"iw_1.v44";
    store Ww [%"chk7" + 0] <- %"iw_1.v5"
    => goto "iw_1.join";
  @"iw_1.L29":
    %"iw_1.v48" = %"v0" +p #16;
    %"chk8" : A = (Renew 0 8 Write 1) %"chk3", %"iw_1.v48";
    store Wl [%"chk8" + 0] <- %"iw_1.v26";
    %"iw_1.v51" = %"v0" +p #24;
    %"chk9" : A = (Renew 0 8 Write 1) %"chk2", %"iw_1.v51";
    store Wl [%"chk9" + 0] <- #0
    => goto "iw_1.L8";
  @"iw_1.L8":
    %"iw_1.v53" = %"v0" +p #48;
    %"iw_1.v55" = %"v0" +p #24;
    %"chk10" : A = (Renew 0 8 Read 1) %"chk2", %"iw_1.v55";
    %"iw_1.v56" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v57" = %"iw_1.v53" +p %"iw_1.v56";
    %"iw_1.v60" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v62" = %"iw_1.v57" +p #16;
    %"chk12" : A = (Check 0 2 Read 1) %"iw_1.v62";
    %"iw_1.v63" : W = (RawLoad (LdNarrow Uh) 0) %"chk12";
    %"iw_1.v64" : L = (Ext Uw) %"iw_1.v63";
    %"iw_1.v65" : L = Add %"iw_1.v60", %"iw_1.v64";
    %"chk13" : A = (Renew 0 8 Write 1) %"chk2", %"iw_1.v55";
    store Wl [%"chk13" + 0] <- %"iw_1.v65";
    %"iw_1.v67" = %"v0" +p #32;
    %"iw_1.v69" = %"iw_1.v57" +p #8;
    %"chk14" : A = (HalfCheck Lower 0 8 Read 1) %"chk12", %"iw_1.v69";
    %"iw_1.v70" : L = (RawLoad LdL 0) %"chk14";
    %"chk15" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v67";
    store Wl [%"chk15" + 0] <- %"iw_1.v70"
    => goto "iw_1.join";
  @"iw_1.join" [%"v30" : P = phi("iw_1.L8" => %"iw_1.v57", "iw_1.L38" => #0, "iw_1.L32" => #0)]:
    %"v33" = %"v0" +p #4;
    %"chk16" : A = (Renew 0 4 Read 1) %"chk0", %"v33";
    %"v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk16"
    => goto "L38";
  @"L38" [%"v40" : W = phi("iw_1.join" => %"v37", "L38" => %"v41")]:
    %"chk17" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v33";
    %"v41" : W = (RawCas (CasNarrow Sw) 0) %"chk17", %"v40", #0;
    %"v42" : W = (Cmp Eq W) %"v41", %"v40"
    => br %"v42" ? "L39" : poll "L38";
  @"L39":
    %"v47" : W = (Cmp Sgt W) %"v40", #1
    => br %"v47" ? "L50" : "L45";
  @"L50":
    call void $"__GI___lll_lock_wake_private"(P %"v33")
    => goto "L45";
  @"L45":
    => ret %"v30"
} }.

Definition hello_image_fn_glibc_gconv_conf'23read_conf_file : func :=
  ir_fn{ "local" "glibc_gconv_conf#read_conf_file"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v10" : P = (Alloc 8) #8;
    %"v11" : P = (Alloc 8) #8;
    %"v8" : P = Copy $"glibc_gconv_conf#str.269";
    call %"v9" : P = $"_IO_new_fopen"(P %"v0", P %"v8");
    %"chk0" : A = (Check 0 8 Write 8) %"v10";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (Check 0 8 Write 1) %"v11";
    store Wl [%"chk1" + 0] <- #0;
    %"v16" : L = Ptoi %"v9";
    %"v17" : L = Ptoi #0;
    %"v18" : W = (Cmp Eq L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L14";
  @"L12":
    => ret #0;
  @"L14":
    %"chk2" : A = (Check 0 4 Read 1) %"v9";
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v27" : W = And %"v26", #32768
    => br %"v27" ? "L29" : "L23";
  @"L23":
    => goto "L29";
  @"L29":
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v36" : W = And %"v34", #4294934527;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk2", %"v9";
    store Ww [%"chk4" + 0] <- %"v36";
    %"v42" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v43" : W = Or %"v42", #32768;
    store Ww [%"chk4" + 0] <- %"v43"
    => goto "L45";
  @"L45":
    call %"v49" : W = $"__feof_unlocked"(P %"v9");
    %"v50" : W = (Cmp Eq W) %"v49", #0
    => br %"v50" ? "L46" : "L47";
  @"L46":
    call %"v56" : L = $"__GI___getdelim"(P %"v10", P %"v11", W #10, P %"v9");
    %"v61" : W = (Cmp Slt L) %"v56", #0
    => br %"v61" ? "L47" : "L59";
  @"L59":
    %"chk7" : A = (Renew 0 8 Read 8) %"chk0", %"v10";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call %"v65" : P = $"__GI_strchr"(P %"v63", W #35);
    %"v70" : L = Ptoi %"v65";
    %"v72" : W = (Cmp Ne L) %"v70", %"v17"
    => br %"v72" ? "L66" : "L67";
  @"L66":
    %"chk8" : A = (Check 0 1 Write 1) %"v65";
    store Wb [%"chk8" + 0] <- #0
    => goto "L87";
  @"L67":
    %"v79" : L = Sub %"v56", #1;
    %"v80" = %"v63" +p %"v79";
    %"chk9" : A = (Check 0 1 Read 1) %"v80";
    %"v81" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v82" : W = (Cmp Eq W) %"v81", #10
    => br %"v82" ? "L74" : "L87";
  @"L74":
    %"chk10" : A = (Renew 0 1 Write 1) %"chk9", %"v80";
    store Wb [%"chk10" + 0] <- #0
    => goto "L87";
  @"L87" [%"pr.2" : P = phi("L88" => %"v101", "L66" => %"v63", "L74" => %"v63", "L67" => %"v63")]:
    %"v90" : P = Copy $"_nl_C_locobj";
    %"v91" = %"v90" +p #104;
    %"chk11" : A = (Check 0 8 Read 8) %"v91";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 1 Read 1) %"pr.2";
    %"v94" : W = (RawLoad (LdNarrow Sb) 0) %"chk12";
    %"v95" : L = (Ext Sw) %"v94";
    %"v96" : L = Shl %"v95", #1;
    %"v97" = %"v92" +p %"v96";
    %"chk13" : A = (Check 0 2 Read 1) %"v97";
    %"v98" : W = (RawLoad (LdNarrow Uh) 0) %"chk13";
    %"v99" : W = And %"v98", #8192
    => br %"v99" ? "L88" : "L89";
  @"L88":
    %"v101" = %"pr.2" +p #1
    => goto poll "L87";
  @"L89":
    %"v107" : L = Ptoi %"pr.2";
    %"v109" : W = (Cmp Eq L) %"v107", %"v70"
    => br %"v109" ? poll "L45" : "L112";
  @"L112" [%"pr.1" : P = phi("L113" => %"v134", "L89" => %"pr.2")]:
    %"chk14" : A = (Check 0 1 Read 1) %"pr.1";
    %"v116" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v117" : W = (Cmp Ne W) %"v116", #0
    => br %"v117" ? "L118" : "L119";
  @"L118":
    %"v120" : P = Copy $"_nl_C_locobj";
    %"v121" = %"v120" +p #104;
    %"chk15" : A = (Check 0 8 Read 8) %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Renew 0 1 Read 1) %"chk14", %"pr.1";
    %"v124" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v125" : L = (Ext Sw) %"v124";
    %"v126" : L = Shl %"v125", #1;
    %"v127" = %"v122" +p %"v126";
    %"chk17" : A = (Check 0 2 Read 1) %"v127";
    %"v128" : W = (RawLoad (LdNarrow Uh) 0) %"chk17";
    %"v129" : W = And %"v128", #8192;
    %"v130" : W = (Cmp Eq W) %"v129", #0
    => goto "L119";
  @"L119" [%"v132" : W = phi("L112" => #0, "L118" => %"v130")]:
    => br %"v132" ? "L113" : "L114";
  @"L113":
    %"v134" = %"pr.1" +p #1
    => goto poll "L112";
  @"L114":
    %"v140" : L = Ptoi %"pr.1";
    %"v142" : L = Sub %"v140", %"v107";
    %"v144" : W = (Cmp Eq L) %"v142", #5
    => br %"v144" ? "L145" : "L146";
  @"L145":
    %"v148" : P = Copy $"glibc_gconv_conf#str.271";
    call %"v150" : W = $"__GI_memcmp"(P %"pr.2", P %"v148", L #5);
    %"v151" : W = (Cmp Eq W) %"v150", #0
    => goto "L146";
  @"L146" [%"v153" : W = phi("L114" => #0, "L145" => %"v151")]:
    => br %"v153" ? "iw_1.L5" : "L136";
  @"iw_1.L5" [%"iw_1.pr.7" : P = phi("iw_1.L6" => %"iw_1.v19", "L146" => %"pr.1")]:
    %"iw_1.v8" : P = Copy $"_nl_C_locobj";
    %"iw_1.v9" = %"iw_1.v8" +p #104;
    %"chk18" : A = (Check 0 8 Read 8) %"iw_1.v9";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (Check 0 1 Read 1) %"iw_1.pr.7";
    %"iw_1.v12" : W = (RawLoad (LdNarrow Sb) 0) %"chk19";
    %"iw_1.v13" : L = (Ext Sw) %"iw_1.v12";
    %"iw_1.v14" : L = Shl %"iw_1.v13", #1;
    %"iw_1.v15" = %"iw_1.v10" +p %"iw_1.v14";
    %"chk20" : A = (Check 0 2 Read 1) %"iw_1.v15";
    %"iw_1.v16" : W = (RawLoad (LdNarrow Uh) 0) %"chk20";
    %"iw_1.v17" : W = And %"iw_1.v16", #8192
    => br %"iw_1.v17" ? "iw_1.L6" : "iw_1.L21";
  @"iw_1.L6":
    %"iw_1.v19" = %"iw_1.pr.7" +p #1
    => goto poll "iw_1.L5";
  @"iw_1.L21" [%"iw_1.pr.10" : P = phi("iw_1.L22" => %"iw_1.v43", "iw_1.L5" => %"iw_1.pr.7"); %"iw_1.pr.5" : P = phi("iw_1.L22" => %"iw_1.v87", "iw_1.L5" => %"iw_1.pr.7")]:
    %"chk21" : A = (Check 0 1 Read 1) %"iw_1.pr.5";
    %"iw_1.v25" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"iw_1.v26" : W = (Cmp Ne W) %"iw_1.v25", #0
    => br %"iw_1.v26" ? "iw_1.L27" : "iw_1.L28";
  @"iw_1.L27":
    %"iw_1.v29" : P = Copy $"_nl_C_locobj";
    %"iw_1.v30" = %"iw_1.v29" +p #104;
    %"chk22" : A = (Check 0 8 Read 8) %"iw_1.v30";
    %"iw_1.v31" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (Renew 0 1 Read 1) %"chk21", %"iw_1.pr.5";
    %"iw_1.v33" : W = (RawLoad (LdNarrow Sb) 0) %"chk23";
    %"iw_1.v34" : L = (Ext Sw) %"iw_1.v33";
    %"iw_1.v35" : L = Shl %"iw_1.v34", #1;
    %"iw_1.v36" = %"iw_1.v31" +p %"iw_1.v35";
    %"chk24" : A = (Check 0 2 Read 1) %"iw_1.v36";
    %"iw_1.v37" : W = (RawLoad (LdNarrow Uh) 0) %"chk24";
    %"iw_1.v38" : W = And %"iw_1.v37", #8192;
    %"iw_1.v39" : W = (Cmp Eq W) %"iw_1.v38", #0
    => goto "iw_1.L28";
  @"iw_1.L28" [%"iw_1.v41" : W = phi("iw_1.L21" => #0, "iw_1.L27" => %"iw_1.v39")]:
    => br %"iw_1.v41" ? "iw_1.L22" : "iw_1.L23";
  @"iw_1.L22":
    %"iw_1.v43" = %"iw_1.pr.10" +p #1;
    %"iw_1.v83" : P = Copy $"_nl_C_locobj";
    %"iw_1.v84" = %"iw_1.v83" +p #120;
    %"chk25" : A = (Check 0 8 Read 8) %"iw_1.v84";
    %"iw_1.v85" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v87" = %"iw_1.pr.5" +p #1;
    %"chk26" : A = (Renew 0 1 Read 1) %"chk21", %"iw_1.pr.5";
    %"iw_1.v88" : W = (RawLoad (LdNarrow Sb) 0) %"chk26";
    %"iw_1.v89" : L = (Ext Sw) %"iw_1.v88";
    %"iw_1.v90" : L = Shl %"iw_1.v89", #2;
    %"iw_1.v91" = %"iw_1.v85" +p %"iw_1.v90";
    %"chk27" : A = (Check 0 4 Read 1) %"iw_1.v91";
    %"iw_1.v92" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"iw_1.v94" : W = (Ext Sb) %"iw_1.v92";
    %"chk28" : A = (Check 0 1 Write 1) %"iw_1.pr.10";
    store Wb [%"chk28" + 0] <- %"iw_1.v94"
    => goto poll "iw_1.L21";
  @"iw_1.L23":
    %"chk29" : A = (Renew 0 1 Read 1) %"chk21", %"iw_1.pr.5";
    %"iw_1.v99" : W = (RawLoad (LdNarrow Sb) 0) %"chk29";
    %"iw_1.v100" : W = (Cmp Eq W) %"iw_1.v99", #0
    => br %"iw_1.v100" ? poll "L45" : "iw_1.L97";
  @"iw_1.L97":
    %"iw_1.v103" = %"iw_1.pr.10" +p #1;
    %"chk30" : A = (Check 0 1 Write 1) %"iw_1.pr.10";
    store Wb [%"chk30" + 0] <- #0;
    %"iw_1.v105" = %"iw_1.pr.5" +p #1
    => goto "iw_1.L106";
  @"iw_1.L106" [%"iw_1.pr.1" : P = phi("iw_1.L107" => %"iw_1.v120", "iw_1.L97" => %"iw_1.v105")]:
    %"iw_1.v109" : P = Copy $"_nl_C_locobj";
    %"iw_1.v110" = %"iw_1.v109" +p #104;
    %"chk31" : A = (Check 0 8 Read 8) %"iw_1.v110";
    %"iw_1.v111" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Check 0 1 Read 1) %"iw_1.pr.1";
    %"iw_1.v113" : W = (RawLoad (LdNarrow Sb) 0) %"chk32";
    %"iw_1.v114" : L = (Ext Sw) %"iw_1.v113";
    %"iw_1.v115" : L = Shl %"iw_1.v114", #1;
    %"iw_1.v116" = %"iw_1.v111" +p %"iw_1.v115";
    %"chk33" : A = (Check 0 2 Read 1) %"iw_1.v116";
    %"iw_1.v117" : W = (RawLoad (LdNarrow Uh) 0) %"chk33";
    %"iw_1.v118" : W = And %"iw_1.v117", #8192
    => br %"iw_1.v118" ? "iw_1.L107" : "iw_1.L121";
  @"iw_1.L107":
    %"iw_1.v120" = %"iw_1.pr.1" +p #1
    => goto poll "iw_1.L106";
  @"iw_1.L121" [%"iw_1.pr.9" : P = phi("iw_1.L122" => %"iw_1.v143", "iw_1.L106" => %"iw_1.v103"); %"iw_1.pr.2" : P = phi("iw_1.L122" => %"iw_1.v187", "iw_1.L106" => %"iw_1.pr.1")]:
    %"chk34" : A = (Check 0 1 Read 1) %"iw_1.pr.2";
    %"iw_1.v125" : W = (RawLoad (LdNarrow Sb) 0) %"chk34";
    %"iw_1.v126" : W = (Cmp Ne W) %"iw_1.v125", #0
    => br %"iw_1.v126" ? "iw_1.L127" : "iw_1.L128";
  @"iw_1.L127":
    %"iw_1.v129" : P = Copy $"_nl_C_locobj";
    %"iw_1.v130" = %"iw_1.v129" +p #104;
    %"chk35" : A = (Check 0 8 Read 8) %"iw_1.v130";
    %"iw_1.v131" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 1 Read 1) %"chk34", %"iw_1.pr.2";
    %"iw_1.v133" : W = (RawLoad (LdNarrow Sb) 0) %"chk36";
    %"iw_1.v134" : L = (Ext Sw) %"iw_1.v133";
    %"iw_1.v135" : L = Shl %"iw_1.v134", #1;
    %"iw_1.v136" = %"iw_1.v131" +p %"iw_1.v135";
    %"chk37" : A = (Check 0 2 Read 1) %"iw_1.v136";
    %"iw_1.v137" : W = (RawLoad (LdNarrow Uh) 0) %"chk37";
    %"iw_1.v138" : W = And %"iw_1.v137", #8192;
    %"iw_1.v139" : W = (Cmp Eq W) %"iw_1.v138", #0
    => goto "iw_1.L128";
  @"iw_1.L128" [%"iw_1.v141" : W = phi("iw_1.L121" => #0, "iw_1.L127" => %"iw_1.v139")]:
    => br %"iw_1.v141" ? "iw_1.L122" : "iw_1.L123";
  @"iw_1.L122":
    %"iw_1.v143" = %"iw_1.pr.9" +p #1;
    %"iw_1.v183" : P = Copy $"_nl_C_locobj";
    %"iw_1.v184" = %"iw_1.v183" +p #120;
    %"chk38" : A = (Check 0 8 Read 8) %"iw_1.v184";
    %"iw_1.v185" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"iw_1.v187" = %"iw_1.pr.2" +p #1;
    %"chk39" : A = (Renew 0 1 Read 1) %"chk34", %"iw_1.pr.2";
    %"iw_1.v188" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    %"iw_1.v189" : L = (Ext Sw) %"iw_1.v188";
    %"iw_1.v190" : L = Shl %"iw_1.v189", #2;
    %"iw_1.v191" = %"iw_1.v185" +p %"iw_1.v190";
    %"chk40" : A = (Check 0 4 Read 1) %"iw_1.v191";
    %"iw_1.v192" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"iw_1.v194" : W = (Ext Sb) %"iw_1.v192";
    %"chk41" : A = (Check 0 1 Write 1) %"iw_1.pr.9";
    store Wb [%"chk41" + 0] <- %"iw_1.v194"
    => goto poll "iw_1.L121";
  @"iw_1.L123":
    %"iw_1.v200" : L = Ptoi %"iw_1.v105";
    %"iw_1.v201" : L = Ptoi %"iw_1.pr.9";
    %"iw_1.v202" : W = (Cmp Eq L) %"iw_1.v200", %"iw_1.v201"
    => br %"iw_1.v202" ? poll "L45" : "iw_1.L197";
  @"iw_1.L197":
    %"iw_1.v205" = %"iw_1.pr.9" +p #1;
    %"chk42" : A = (Check 0 1 Write 1) %"iw_1.pr.9";
    store Wb [%"chk42" + 0] <- #0;
    %"iw_1.iw_1.iw_1.v3" : P = Copy $"__gconv_modules_db";
    %"chk43" : A = (Check 0 8 Read 8) %"iw_1.iw_1.iw_1.v3";
    %"iw_1.iw_1.iw_1.v4" : P = (RawLoadPointer 0 load_effects) %"chk43"
    => goto "iw_1.iw_1.iw_1.L5";
  @"iw_1.iw_1.iw_1.L5" [%"iw_1.iw_1.iw_1.pr.2" : P = phi("iw_1.L197" => %"iw_1.iw_1.iw_1.v4", "iw_1.iw_1.iw_1.L23" => %"iw_1.iw_1.iw_1.v30", "iw_1.iw_1.iw_1.L24" => %"iw_1.iw_1.iw_1.v33")]:
    %"iw_1.iw_1.iw_1.v9" : L = Ptoi %"iw_1.iw_1.iw_1.pr.2";
    %"iw_1.iw_1.iw_1.v11" : W = (Cmp Ne L) %"iw_1.iw_1.iw_1.v9", %"v17"
    => br %"iw_1.iw_1.iw_1.v11" ? "iw_1.iw_1.iw_1.L6" : "iw_1.iw_1.iw_1.join";
  @"iw_1.iw_1.iw_1.L6":
    %"chk44" : A = (Check 0 8 Read 8) %"iw_1.iw_1.iw_1.pr.2";
    %"iw_1.iw_1.iw_1.v15" : P = (RawLoadPointer 0 load_effects) %"chk44";
    call %"iw_1.iw_1.iw_1.v16" : W = $"__GI_strcmp"(P %"iw_1.pr.7", P %"iw_1.iw_1.iw_1.v15");
    %"iw_1.iw_1.iw_1.v21" : W = (Cmp Eq W) %"iw_1.iw_1.iw_1.v16", #0
    => br %"iw_1.iw_1.iw_1.v21" ? "iw_1.iw_1.iw_1.join" : "iw_1.iw_1.iw_1.L18";
  @"iw_1.iw_1.iw_1.L18":
    %"iw_1.iw_1.iw_1.v27" : W = (Cmp Slt W) %"iw_1.iw_1.iw_1.v16", #0
    => br %"iw_1.iw_1.iw_1.v27" ? "iw_1.iw_1.iw_1.L23" : "iw_1.iw_1.iw_1.L24";
  @"iw_1.iw_1.iw_1.L23":
    %"iw_1.iw_1.iw_1.v29" = %"iw_1.iw_1.iw_1.pr.2" +p #32;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk44", %"iw_1.iw_1.iw_1.v29";
    %"iw_1.iw_1.iw_1.v30" : P = (RawLoadPointer 0 load_effects) %"chk45"
    => goto poll "iw_1.iw_1.iw_1.L5";
  @"iw_1.iw_1.iw_1.L24":
    %"iw_1.iw_1.iw_1.v32" = %"iw_1.iw_1.iw_1.pr.2" +p #48;
    %"chk46" : A = (HalfCheck Upper 0 8 Read 8) %"chk44", %"iw_1.iw_1.iw_1.v32";
    %"iw_1.iw_1.iw_1.v33" : P = (RawLoadPointer 0 load_effects) %"chk46"
    => goto poll "iw_1.iw_1.iw_1.L5";
  @"iw_1.iw_1.iw_1.join" [%"iw_1.iw_1.v10" : W = phi("iw_1.iw_1.iw_1.L6" => #1, "iw_1.iw_1.iw_1.L5" => %"iw_1.iw_1.iw_1.v11")]:
    => br %"iw_1.iw_1.v10" ? poll "L45" : "iw_1.iw_1.L8";
  @"iw_1.iw_1.L8":
    %"iw_1.iw_1.v15" : L = Ptoi %"iw_1.v205";
    %"iw_1.iw_1.v16" : L = Ptoi %"iw_1.pr.7";
    %"iw_1.iw_1.v17" : L = Sub %"iw_1.iw_1.v15", %"iw_1.iw_1.v16";
    %"iw_1.iw_1.v18" : L = Add %"iw_1.iw_1.v17", #16;
    call %"iw_1.iw_1.v19" : P = $"malloc"(L %"iw_1.iw_1.v18");
    %"iw_1.iw_1.v24" : L = Ptoi %"iw_1.iw_1.v19";
    %"iw_1.iw_1.v26" : W = (Cmp Ne L) %"iw_1.iw_1.v24", %"v17"
    => br %"iw_1.iw_1.v26" ? "iw_1.iw_1.L20" : poll "L45";
  @"iw_1.iw_1.L20":
    %"iw_1.iw_1.v30" = %"iw_1.iw_1.v19" +p #16;
    call %"iw_1.iw_1.v37" : P = $"__GI_memcpy"(P %"iw_1.iw_1.v30", P %"iw_1.pr.7", L %"iw_1.iw_1.v17");
    %"chk47" : A = (Check 0 8 Write 8) %"iw_1.iw_1.v19";
    store.ptr [%"chk47" + 0] <- %"iw_1.iw_1.v37";
    %"iw_1.iw_1.v39" = %"iw_1.iw_1.v19" +p #8;
    %"chk48" : A = (Renew 0 8 Read 8) %"chk47", %"iw_1.iw_1.v19";
    %"iw_1.iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"iw_1.iw_1.v46" : L = Sub %"iw_1.v200", %"iw_1.iw_1.v16";
    %"iw_1.iw_1.v47" = %"iw_1.iw_1.v41" +p %"iw_1.iw_1.v46";
    %"chk49" : A = (HalfCheck Upper 0 8 Write 8) %"chk47", %"iw_1.iw_1.v39";
    store.ptr [%"chk49" + 0] <- %"iw_1.iw_1.v47";
    %"iw_1.iw_1.v49" : P = Copy $"__gconv_alias_db";
    %"iw_1.iw_1.v50" : P = Copy $"__gconv_alias_compare";
    call %"iw_1.iw_1.v51" : P = $"__GI___tsearch"(P %"iw_1.iw_1.v19", P %"iw_1.iw_1.v49", P %"iw_1.iw_1.v50");
    %"iw_1.iw_1.v56" : L = Ptoi %"iw_1.iw_1.v51";
    %"iw_1.iw_1.v58" : W = (Cmp Eq L) %"iw_1.iw_1.v56", %"v17"
    => br %"iw_1.iw_1.v58" ? "iw_1.iw_1.L60" : "iw_1.iw_1.L59";
  @"iw_1.iw_1.L59":
    %"chk50" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v51";
    %"iw_1.iw_1.v62" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"iw_1.iw_1.v64" : L = Ptoi %"iw_1.iw_1.v62";
    %"iw_1.iw_1.v66" : W = (Cmp Ne L) %"iw_1.iw_1.v64", %"iw_1.iw_1.v24"
    => goto "iw_1.iw_1.L60";
  @"iw_1.iw_1.L60" [%"iw_1.iw_1.v68" : W = phi("iw_1.iw_1.L20" => #1, "iw_1.iw_1.L59" => %"iw_1.iw_1.v66")]:
    => br %"iw_1.iw_1.v68" ? "iw_1.iw_1.L52" : poll "L45";
  @"iw_1.iw_1.L52":
    call void $"free"(P %"iw_1.iw_1.v19")
    => goto poll "L45";
  @"L136":
    %"v164" : W = (Cmp Eq L) %"v142", #6
    => br %"v164" ? "L165" : "L166";
  @"L165":
    %"v168" : P = Copy $"glibc_gconv_conf#str.272";
    call %"v170" : W = $"__GI_memcmp"(P %"pr.2", P %"v168", L #6);
    %"v171" : W = (Cmp Eq W) %"v170", #0
    => goto "L166";
  @"L166" [%"v173" : W = phi("L136" => #0, "L165" => %"v171")]:
    => br %"v173" ? "L155" : poll "L45";
  @"L155":
    %"v177" : P = Copy $"glibc_gconv_conf#read_conf_file.modcounter.270";
    %"chk51" : A = (Check 0 4 Read 1) %"v177";
    %"v178" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    %"v179" : W = Add %"v178", #1;
    %"chk52" : A = (Renew 0 4 Write 1) %"chk51", %"v177";
    store Ww [%"chk52" + 0] <- %"v179";
    call void $"glibc_gconv_conf#add_module"(P %"pr.1", P %"v2", L %"v4", W %"v178")
    => goto poll "L45";
  @"L47":
    %"chk53" : A = (Renew 0 8 Read 8) %"chk0", %"v10";
    %"v180" : P = (RawLoadPointer 0 load_effects) %"chk53";
    call void $"free"(P %"v180");
    call %"v182" : W = $"_IO_new_fclose"(P %"v9")
    => ret #1
} }.

Definition hello_image_fn_glibc_localealias'23read_alias_file : func :=
  ir_fn{ "local" "glibc_localealias#read_alias_file"(P %"v0", W %"v2") -> (RClass L) {
  @"start":
    %"v59" : P = (Alloc 4) #400;
    %"v8" : L = (Ext Sw) %"v2";
    %"v9" : L = Add %"v8", #14;
    %"v10" : P = (Alloc 16) %"v9";
    call %"v15" : P = $"__GI_mempcpy"(P %"v10", P %"v0", L %"v8");
    %"v16" : P = Copy $"glibc_localealias#read_alias_file.aliasfile.268";
    call %"v17" : P = $"__GI_mempcpy"(P %"v15", P %"v16", L #14);
    %"v19" : P = Copy $"glibc_localealias#str.269";
    call %"v20" : P = $"_IO_new_fopen"(P %"v10", P %"v19");
    %"v25" : L = Ptoi %"v20";
    %"v26" : L = Ptoi #0;
    %"v27" : W = (Cmp Eq L) %"v25", %"v26"
    => br %"v27" ? "L21" : "L23";
  @"L21":
    => ret #0;
  @"L23":
    %"chk0" : A = (Check 0 4 Read 1) %"v20";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v35" : W = And %"v34", #32768
    => br %"v35" ? "L37" : "L31";
  @"L31":
    => goto "L37";
  @"L37":
    %"v42" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v44" : W = And %"v42", #4294934527;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v20";
    store Ww [%"chk2" + 0] <- %"v44";
    %"v50" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v51" : W = Or %"v50", #32768;
    store Ww [%"chk2" + 0] <- %"v51"
    => goto "L53";
  @"L53" [%"pr.2" : L = phi("L37" => #0, "L389" => %"pr.3", "L388" => %"pr.3", "L95" => %"pr.3")]:
    call %"v57" : W = $"__feof_unlocked"(P %"v20");
    %"v58" : W = (Cmp Eq W) %"v57", #0
    => br %"v58" ? "L54" : "L229";
  @"L54":
    call %"v68" : P = $"__GI___fgets_unlocked"(P %"v59", W #400, P %"v20");
    %"v69" : L = Ptoi %"v68";
    %"v71" : W = (Cmp Eq L) %"v69", %"v26"
    => br %"v71" ? "L229" : "L66";
  @"L66":
    call %"v73" : P = $"__GI_strchr"(P %"v59", W #10);
    %"v74" : L = Ptoi %"v73"
    => goto "L77";
  @"L77" [%"pr.8" : P = phi("L66" => %"v59", "L78" => %"v92")]:
    %"iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 1 Read 1) %"pr.8";
    %"v84" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v85" : W = (Ext Ub) %"v84";
    %"v86" : L = (Ext Sw) %"v85";
    %"v87" : L = Shl %"v86", #1;
    %"v88" = %"v81" +p %"v87";
    %"chk7" : A = (Check 0 2 Read 1) %"v88";
    %"v89" : W = (RawLoad (LdNarrow Uh) 0) %"chk7";
    %"v90" : W = And %"v89", #8192
    => br %"v90" ? "L78" : "L79";
  @"L78":
    %"v92" = %"pr.8" +p #1
    => goto poll "L77";
  @"L79":
    %"v98" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v99" : W = (Cmp Ne W) %"v98", #0
    => br %"v99" ? "L100" : "L101";
  @"L100":
    %"v104" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v105" : W = (Cmp Ne W) %"v104", #35
    => goto "L101";
  @"L101" [%"v107" : W = phi("L79" => #0, "L100" => %"v105")]:
    => br %"v107" ? "L93" : "L95";
  @"L93":
    %"v109" = %"pr.8" +p #1
    => goto "L110";
  @"L110" [%"pr.4" : P = phi("L111" => %"v134", "L93" => %"v109")]:
    %"chk10" : A = (Check 0 1 Read 1) %"pr.4";
    %"v115" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v116" : W = (Cmp Ne W) %"v115", #0
    => br %"v116" ? "iw_2.start" : "L118";
  @"iw_2.start":
    %"iw_2.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_2.v0";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Renew 0 1 Read 1) %"chk10", %"pr.4";
    %"v123" : W = (RawLoad (LdNarrow Sb) 0) %"chk12";
    %"v124" : W = (Ext Ub) %"v123";
    %"v125" : L = (Ext Sw) %"v124";
    %"v126" : L = Shl %"v125", #1;
    %"v127" = %"v120" +p %"v126";
    %"chk13" : A = (Check 0 2 Read 1) %"v127";
    %"v128" : W = (RawLoad (LdNarrow Uh) 0) %"chk13";
    %"v129" : W = And %"v128", #8192;
    %"v130" : W = (Cmp Eq W) %"v129", #0
    => goto "L118";
  @"L118" [%"v132" : W = phi("L110" => #0, "iw_2.start" => %"v130")]:
    => br %"v132" ? "L111" : "L112";
  @"L111":
    %"v134" = %"pr.4" +p #1
    => goto poll "L110";
  @"L112":
    %"chk14" : A = (Renew 0 1 Read 1) %"chk10", %"pr.4";
    %"v140" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v141" : W = (Cmp Ne W) %"v140", #0
    => br %"v141" ? "L135" : "L144";
  @"L135":
    %"v143" = %"pr.4" +p #1;
    %"chk15" : A = (Renew 0 1 Write 1) %"chk10", %"pr.4";
    store Wb [%"chk15" + 0] <- #0
    => goto "L144";
  @"L144" [%"pr.6" : P = phi("L145" => %"v159", "L135" => %"v143", "L112" => %"pr.4")]:
    %"iw_3.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk16" : A = (Check 0 8 Read 8) %"iw_3.v0";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 1 Read 1) %"pr.6";
    %"v151" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v152" : W = (Ext Ub) %"v151";
    %"v153" : L = (Ext Sw) %"v152";
    %"v154" : L = Shl %"v153", #1;
    %"v155" = %"v148" +p %"v154";
    %"chk18" : A = (Check 0 2 Read 1) %"v155";
    %"v156" : W = (RawLoad (LdNarrow Uh) 0) %"chk18";
    %"v157" : W = And %"v156", #8192
    => br %"v157" ? "L145" : "L146";
  @"L145":
    %"v159" = %"pr.6" +p #1
    => goto poll "L144";
  @"L146":
    %"v165" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v166" : W = (Cmp Ne W) %"v165", #0
    => br %"v166" ? "L160" : "L95";
  @"L160":
    %"v168" = %"pr.6" +p #1
    => goto "L169";
  @"L169" [%"pr.7" : P = phi("L160" => %"v168", "L170" => %"v193")]:
    %"chk20" : A = (Check 0 1 Read 1) %"pr.7";
    %"v174" : W = (RawLoad (LdNarrow Sb) 0) %"chk20";
    %"v175" : W = (Cmp Ne W) %"v174", #0
    => br %"v175" ? "iw_4.start" : "L177";
  @"iw_4.start":
    %"iw_4.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk21" : A = (Check 0 8 Read 8) %"iw_4.v0";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (Renew 0 1 Read 1) %"chk20", %"pr.7";
    %"v182" : W = (RawLoad (LdNarrow Sb) 0) %"chk22";
    %"v183" : W = (Ext Ub) %"v182";
    %"v184" : L = (Ext Sw) %"v183";
    %"v185" : L = Shl %"v184", #1;
    %"v186" = %"v179" +p %"v185";
    %"chk23" : A = (Check 0 2 Read 1) %"v186";
    %"v187" : W = (RawLoad (LdNarrow Uh) 0) %"chk23";
    %"v188" : W = And %"v187", #8192;
    %"v189" : W = (Cmp Eq W) %"v188", #0
    => goto "L177";
  @"L177" [%"v191" : W = phi("L169" => #0, "iw_4.start" => %"v189")]:
    => br %"v191" ? "L170" : "L171";
  @"L170":
    %"v193" = %"pr.7" +p #1
    => goto poll "L169";
  @"L171":
    %"chk24" : A = (Renew 0 1 Read 1) %"chk20", %"pr.7";
    %"v199" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"v200" : W = (Cmp Eq W) %"v199", #10
    => br %"v200" ? "L194" : "L195";
  @"L194":
    %"v202" = %"pr.7" +p #1;
    %"chk25" : A = (Renew 0 1 Write 1) %"chk20", %"pr.7";
    store Wb [%"chk25" + 0] <- #0;
    %"chk26" : A = (HalfCheck Upper 0 1 Write 1) %"chk20", %"v202";
    store Wb [%"chk26" + 0] <- #10
    => goto "L196";
  @"L195":
    %"v209" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"v210" : W = (Cmp Ne W) %"v209", #0
    => br %"v210" ? "L204" : "L196";
  @"L204":
    %"chk28" : A = (Renew 0 1 Write 1) %"chk20", %"pr.7";
    store Wb [%"chk28" + 0] <- #0
    => goto "L196";
  @"L196":
    %"v218" : P = Copy $"glibc_localealias#nmap";
    %"chk29" : A = (Check 0 8 Read 1) %"v218";
    %"v219" : L = (RawLoad LdL 0) %"chk29";
    %"v220" : P = Copy $"glibc_localealias#maxmap";
    %"chk30" : A = (Check 0 8 Read 1) %"v220";
    %"v221" : L = (RawLoad LdL 0) %"chk30";
    %"v222" : W = (Cmp Uge L) %"v219", %"v221"
    => br %"v222" ? "iw_5.start" : "L217";
  @"iw_5.start":
    %"iw_5.v5" : P = Copy $"glibc_localealias#maxmap";
    %"chk31" : A = (Check 0 8 Read 1) %"iw_5.v5";
    %"iw_5.v6" : L = (RawLoad LdL 0) %"chk31";
    %"iw_5.v7" : W = (Cmp Eq L) %"iw_5.v6", #0
    => br %"iw_5.v7" ? "iw_5.L4" : "iw_5.L3";
  @"iw_5.L3":
    %"iw_5.v8" : P = Copy $"glibc_localealias#maxmap";
    %"chk32" : A = (Check 0 8 Read 1) %"iw_5.v8";
    %"iw_5.v9" : L = (RawLoad LdL 0) %"chk32";
    %"iw_5.v10" : L = Shl %"iw_5.v9", #1
    => goto "iw_5.L4";
  @"iw_5.L4" [%"iw_5.v11" : L = phi("iw_5.L3" => %"iw_5.v10", "iw_5.start" => #100)]:
    %"iw_5.v12" : P = Copy $"glibc_localealias#map";
    %"chk33" : A = (Check 0 8 Read 8) %"iw_5.v12";
    %"iw_5.v13" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"iw_5.v15" : L = Shl %"iw_5.v11", #4;
    call %"iw_5.v16" : P = $"realloc"(P %"iw_5.v13", L %"iw_5.v15");
    %"iw_5.v21" : L = Ptoi %"iw_5.v16";
    %"iw_5.v23" : W = (Cmp Eq L) %"iw_5.v21", %"v26"
    => br %"iw_5.v23" ? "iw_5.join" : "iw_5.L19";
  @"iw_5.L19":
    %"iw_5.v26" : P = Copy $"glibc_localealias#map";
    %"chk34" : A = (Check 0 8 Write 8) %"iw_5.v26";
    store.ptr [%"chk34" + 0] <- %"iw_5.v16";
    %"iw_5.v28" : P = Copy $"glibc_localealias#maxmap";
    %"chk35" : A = (Check 0 8 Write 1) %"iw_5.v28";
    store Wl [%"chk35" + 0] <- %"iw_5.v11"
    => goto "iw_5.join";
  @"iw_5.join" [%"v226" : W = phi("iw_5.L19" => #0, "iw_5.L4" => #4294967295)]:
    %"v227" : L = (Ext Sw) %"v226";
    %"v228" : W = (Cmp Ne L) %"v227", #0
    => br %"v228" ? "L229" : "L217";
  @"L217":
    call %"v232" : L = $"__GI_strlen"(P %"pr.8");
    %"v233" : L = Add %"v232", #1;
    call %"v235" : L = $"__GI_strlen"(P %"pr.6");
    %"v236" : L = Add %"v235", #1;
    %"v240" : P = Copy $"glibc_localealias#string_space_act";
    %"chk36" : A = (Check 0 8 Read 1) %"v240";
    %"v241" : L = (RawLoad LdL 0) %"chk36";
    %"v243" : L = Add %"v241", %"v233";
    %"v245" : L = Add %"v243", %"v236";
    %"v246" : P = Copy $"glibc_localealias#string_space_max";
    %"chk37" : A = (Check 0 8 Read 1) %"v246";
    %"v247" : L = (RawLoad LdL 0) %"chk37";
    %"v248" : W = (Cmp Ugt L) %"v245", %"v247"
    => br %"v248" ? "L237" : "L239";
  @"L237":
    %"v250" : P = Copy $"glibc_localealias#string_space_max";
    %"chk38" : A = (Check 0 8 Read 1) %"v250";
    %"v251" : L = (RawLoad LdL 0) %"chk38";
    %"v257" : L = Add %"v233", %"v236";
    %"v258" : W = (Cmp Ugt L) %"v257", #1024
    => br %"v258" ? "L254" : "L253";
  @"L253":
    => goto "L254";
  @"L254" [%"v262" : L = phi("L253" => #1024, "L237" => %"v257")]:
    %"v263" : L = Add %"v251", %"v262";
    %"v265" : P = Copy $"glibc_localealias#string_space";
    %"chk39" : A = (Check 0 8 Read 8) %"v265";
    %"v266" : P = (RawLoadPointer 0 load_effects) %"chk39";
    call %"v268" : P = $"realloc"(P %"v266", L %"v263");
    %"v273" : L = Ptoi %"v268";
    %"v275" : W = (Cmp Eq L) %"v273", %"v26"
    => br %"v275" ? "L229" : "L271";
  @"L271":
    %"v280" : P = Copy $"glibc_localealias#string_space";
    %"chk40" : A = (Check 0 8 Read 8) %"v280";
    %"v281" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v283" : L = Ptoi %"v281";
    %"v285" : W = (Cmp Ne L) %"v283", %"v273"
    => br %"v285" ? "L289" : "L279";
  @"L289" [%"pr.9" : L = phi("L290" => %"v336", "L271" => #0)]:
    %"v294" : P = Copy $"glibc_localealias#nmap";
    %"chk41" : A = (Check 0 8 Read 1) %"v294";
    %"v295" : L = (RawLoad LdL 0) %"chk41";
    %"v296" : W = (Cmp Ult L) %"pr.9", %"v295"
    => br %"v296" ? "L290" : "L279";
  @"L290":
    %"v297" : P = Copy $"glibc_localealias#map";
    %"chk42" : A = (Check 0 8 Read 8) %"v297";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v300" : L = Shl %"pr.9", #4;
    %"v301" = %"v298" +p %"v300";
    %"v303" : P = Copy $"glibc_localealias#map";
    %"chk43" : A = (Check 0 8 Read 8) %"v303";
    %"v304" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v307" = %"v304" +p %"v300";
    %"chk44" : A = (Check 0 8 Read 8) %"v307";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v309" : P = Copy $"glibc_localealias#string_space";
    %"chk45" : A = (Check 0 8 Read 8) %"v309";
    %"v310" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v311" : L = Ptoi %"v308";
    %"v312" : L = Ptoi %"v310";
    %"v313" : L = Sub %"v311", %"v312";
    %"v314" = %"v268" +p %"v313";
    %"chk46" : A = (Check 0 8 Write 8) %"v301";
    store.ptr [%"chk46" + 0] <- %"v314";
    %"v315" : P = Copy $"glibc_localealias#map";
    %"chk47" : A = (Check 0 8 Read 8) %"v315";
    %"v316" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v319" = %"v316" +p %"v300";
    %"v320" = %"v319" +p #8;
    %"v322" : P = Copy $"glibc_localealias#map";
    %"chk48" : A = (Check 0 8 Read 8) %"v322";
    %"v323" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v326" = %"v323" +p %"v300";
    %"v327" = %"v326" +p #8;
    %"chk49" : A = (Check 0 8 Read 8) %"v327";
    %"v328" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v329" : P = Copy $"glibc_localealias#string_space";
    %"chk50" : A = (Check 0 8 Read 8) %"v329";
    %"v330" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v331" : L = Ptoi %"v328";
    %"v332" : L = Ptoi %"v330";
    %"v333" : L = Sub %"v331", %"v332";
    %"v334" = %"v268" +p %"v333";
    %"chk51" : A = (Check 0 8 Write 8) %"v320";
    store.ptr [%"chk51" + 0] <- %"v334";
    %"v336" : L = Add %"pr.9", #1
    => goto poll "L289";
  @"L279":
    %"v337" : P = Copy $"glibc_localealias#string_space";
    %"chk52" : A = (Check 0 8 Write 8) %"v337";
    store.ptr [%"chk52" + 0] <- %"v268";
    %"v339" : P = Copy $"glibc_localealias#string_space_max";
    %"chk53" : A = (Check 0 8 Write 1) %"v339";
    store Wl [%"chk53" + 0] <- %"v263"
    => goto "L239";
  @"L239":
    %"v341" : P = Copy $"glibc_localealias#map";
    %"chk54" : A = (Check 0 8 Read 8) %"v341";
    %"v342" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v343" : P = Copy $"glibc_localealias#nmap";
    %"chk55" : A = (Check 0 8 Read 1) %"v343";
    %"v344" : L = (RawLoad LdL 0) %"chk55";
    %"v345" : L = Shl %"v344", #4;
    %"v346" = %"v342" +p %"v345";
    %"v347" : P = Copy $"glibc_localealias#string_space";
    %"chk56" : A = (Check 0 8 Read 8) %"v347";
    %"v348" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v349" : P = Copy $"glibc_localealias#string_space_act";
    %"chk57" : A = (Check 0 8 Read 1) %"v349";
    %"v350" : L = (RawLoad LdL 0) %"chk57";
    %"v351" = %"v348" +p %"v350";
    call %"v354" : P = $"__GI_memcpy"(P %"v351", P %"pr.8", L %"v233");
    %"chk58" : A = (Check 0 8 Write 8) %"v346";
    store.ptr [%"chk58" + 0] <- %"v354";
    %"v355" : P = Copy $"glibc_localealias#string_space_act";
    %"chk59" : A = (Check 0 8 Read 1) %"v355";
    %"v356" : L = (RawLoad LdL 0) %"chk59";
    %"v358" : L = Add %"v356", %"v233";
    %"chk60" : A = (Renew 0 8 Write 1) %"chk59", %"v355";
    store Wl [%"chk60" + 0] <- %"v358";
    %"v359" : P = Copy $"glibc_localealias#map";
    %"chk61" : A = (Check 0 8 Read 8) %"v359";
    %"v360" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v361" : P = Copy $"glibc_localealias#nmap";
    %"chk62" : A = (Check 0 8 Read 1) %"v361";
    %"v362" : L = (RawLoad LdL 0) %"chk62";
    %"v363" : L = Shl %"v362", #4;
    %"v364" = %"v360" +p %"v363";
    %"v365" = %"v364" +p #8;
    %"v366" : P = Copy $"glibc_localealias#string_space";
    %"chk63" : A = (Check 0 8 Read 8) %"v366";
    %"v367" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"v368" : P = Copy $"glibc_localealias#string_space_act";
    %"chk64" : A = (Check 0 8 Read 1) %"v368";
    %"v369" : L = (RawLoad LdL 0) %"chk64";
    %"v370" = %"v367" +p %"v369";
    call %"v373" : P = $"__GI_memcpy"(P %"v370", P %"pr.6", L %"v236");
    %"chk65" : A = (Check 0 8 Write 8) %"v365";
    store.ptr [%"chk65" + 0] <- %"v373";
    %"v374" : P = Copy $"glibc_localealias#string_space_act";
    %"chk66" : A = (Check 0 8 Read 1) %"v374";
    %"v375" : L = (RawLoad LdL 0) %"chk66";
    %"v377" : L = Add %"v375", %"v236";
    %"chk67" : A = (Renew 0 8 Write 1) %"chk66", %"v374";
    store Wl [%"chk67" + 0] <- %"v377";
    %"v378" : P = Copy $"glibc_localealias#nmap";
    %"chk68" : A = (Check 0 8 Read 1) %"v378";
    %"v379" : L = (RawLoad LdL 0) %"chk68";
    %"v380" : L = Add %"v379", #1;
    %"chk69" : A = (Renew 0 8 Write 1) %"chk68", %"v378";
    store Wl [%"chk69" + 0] <- %"v380";
    %"v382" : L = Add %"pr.2", #1
    => goto "L95";
  @"L95" [%"pr.3" : L = phi("L239" => %"v382", "L146" => %"pr.2", "L101" => %"pr.2")]:
    %"v387" : W = (Cmp Eq L) %"v74", %"v26"
    => br %"v387" ? "L388" : poll "L53";
  @"L388":
    call %"v395" : P = $"__GI___fgets_unlocked"(P %"v59", W #400, P %"v20");
    %"v396" : L = Ptoi %"v395";
    %"v398" : W = (Cmp Eq L) %"v396", %"v26"
    => br %"v398" ? poll "L53" : "L389";
  @"L389":
    call %"v400" : P = $"__GI_strchr"(P %"v59", W #10);
    %"v401" : L = Ptoi %"v400";
    %"v403" : W = (Cmp Eq L) %"v401", %"v26"
    => br %"v403" ? poll "L388" : poll "L53";
  @"L229":
    call %"v405" : W = $"_IO_new_fclose"(P %"v20");
    %"v410" : W = (Cmp Ugt L) %"pr.2", #0
    => br %"v410" ? "L406" : "L408";
  @"L406":
    %"v411" : P = Copy $"glibc_localealias#map";
    %"chk70" : A = (Check 0 8 Read 8) %"v411";
    %"v412" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v413" : P = Copy $"glibc_localealias#nmap";
    %"chk71" : A = (Check 0 8 Read 1) %"v413";
    %"v414" : L = (RawLoad LdL 0) %"chk71";
    %"v415" : P = Copy $"glibc_localealias#alias_compare";
    call void $"__GI_qsort"(P %"v412", L %"v414", L #16, P %"v415")
    => goto "L408";
  @"L408":
    => ret %"pr.2"
} }.

Definition hello_image_fn___GI___read_nocancel : func :=
  ir_fn{ "export" "__GI___read_nocancel"(W %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call %"v9" : L = $"zsys_read"(W %"v0", P %"v2", L %"v4")
    => ret %"v9"
} }.

Definition hello_image_fn_glibc_vfprintf_internal'23read_int : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#read_int"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 1 Read 1) %"v4";
    %"v5" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v6" : W = Sub %"v5", #48
    => goto "L7";
  @"L7" [%"pr.4" : W = phi("start" => %"v6", "L16" => #4294967295, "L36" => %"v45", "L22" => #4294967295, "L8" => %"pr.4")]:
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v12" = %"v11" +p #1;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk3" + 0] <- %"v12";
    %"chk4" : A = (Check 0 1 Read 1) %"v12";
    %"v13" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"v14" : W = Sub %"v13", #48;
    %"v15" : W = (Cmp Ult W) %"v14", #10
    => br %"v15" ? "L8" : "L9";
  @"L8":
    %"v20" : W = (Cmp Sge W) %"pr.4", #0
    => br %"v20" ? "L16" : poll "L7";
  @"L16":
    %"v26" : W = (Cmp Sgt W) %"pr.4", #214748364
    => br %"v26" ? poll "L7" : "L22";
  @"L22":
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 1 Read 1) %"v30";
    %"v31" : W = (RawLoad (LdNarrow Ub) 0) %"chk6";
    %"v32" : W = Sub %"v31", #48;
    %"v34" : W = Mul %"pr.4", #10;
    %"v39" : W = Sub #2147483647, %"v32";
    %"v41" : W = (Cmp Slt W) %"v39", %"v34"
    => br %"v41" ? poll "L7" : "L36";
  @"L36":
    %"v45" : W = Add %"v34", %"v32"
    => goto poll "L7";
  @"L9":
    => ret %"pr.4"
} }.

Definition hello_image_fn_glibc_vfwprintf_internal'23read_int : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#read_int"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 4 Read 1) %"v4";
    %"v5" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v6" : W = Sub %"v5", #48
    => goto "L7";
  @"L7" [%"pr.4" : W = phi("start" => %"v6", "L16" => #4294967295, "L36" => %"v45", "L22" => #4294967295, "L8" => %"pr.4")]:
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v12" = %"v11" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk3" + 0] <- %"v12";
    %"chk4" : A = (Check 0 4 Read 1) %"v12";
    %"v13" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v14" : W = Sub %"v13", #48;
    %"v15" : W = (Cmp Ult W) %"v14", #10
    => br %"v15" ? "L8" : "L9";
  @"L8":
    %"v20" : W = (Cmp Sge W) %"pr.4", #0
    => br %"v20" ? "L16" : poll "L7";
  @"L16":
    %"v26" : W = (Cmp Sgt W) %"pr.4", #214748364
    => br %"v26" ? poll "L7" : "L22";
  @"L22":
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 4 Read 1) %"v30";
    %"v31" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v32" : W = Sub %"v31", #48;
    %"v34" : W = Mul %"pr.4", #10;
    %"v39" : W = Sub #2147483647, %"v32";
    %"v41" : W = (Cmp Slt W) %"v39", %"v34"
    => br %"v41" ? poll "L7" : "L36";
  @"L36":
    %"v45" : W = Add %"v34", %"v32"
    => goto poll "L7";
  @"L9":
    => ret %"pr.4"
} }.

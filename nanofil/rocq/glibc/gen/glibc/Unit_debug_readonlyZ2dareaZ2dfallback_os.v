(** This file defines checked IR from glibc’s `debug/readonly-area-fallback.os` object.
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

Definition fn___readonly_area_fallback : func :=
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

Definition item_glibc_readonly_area_fallback'23str'2e252 : item :=
  (IData (a "glibc_readonly_area_fallback#str.252") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 47); (Item Wb 115); (Item Wb 101); (Item Wb 108); (Item Wb 102); (Item Wb 47); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 115); (Item Wb 0)]).

Definition item_glibc_readonly_area_fallback'23str'2e253 : item :=
  (IData (a "glibc_readonly_area_fallback#str.253") (LRo (a "local")) 1 [(Item Wb 114); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

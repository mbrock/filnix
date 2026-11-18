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

Definition hello_image_fn___GI__IO_wfile_sync : func :=
  ir_fn{ "export" "__GI__IO_wfile_sync"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v9" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" = %"v14" +p #24;
    %"chk3" : A = (Check 0 8 Read 8) %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v17" : L = Ptoi %"v11";
    %"v18" : L = Ptoi %"v16";
    %"v19" : W = (Cmp Ugt L) %"v17", %"v18"
    => br %"v19" ? "L4" : "L6";
  @"L4":
    %"v27" = %"v0" +p #192;
    %"chk4" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v27";
    %"v28" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v29" : W = (Cmp Sle W) %"v28", #0
    => br %"v29" ? "L23" : "L24";
  @"L23":
    %"v32" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v35" = %"v0" +p #40;
    %"v36" : P = (RawLoadPointer 8 load_effects) %"chk5";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v40" : L = Ptoi %"v36";
    %"v41" : L = Ptoi %"v39";
    %"v42" : L = Sub %"v40", %"v41";
    call %"v43" : W = $"__GI__IO_do_write"(P %"v0", P %"v33", L %"v42")
    => goto "L25";
  @"L24":
    %"v46" = %"v0" +p #160;
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v48" = %"v47" +p #24;
    %"chk9" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v53" = %"v52" +p #32;
    %"chk11" : A = (Check 0 8 Read 8) %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v58" = %"v57" +p #24;
    %"chk13" : A = (Check 0 8 Read 8) %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v60" : L = Ptoi %"v54";
    %"v61" : L = Ptoi %"v59";
    %"v62" : L = Sub %"v60", %"v61";
    %"v63" : L = Div %"v62", #4;
    call %"v64" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v49", L %"v63")
    => goto "L25";
  @"L25" [%"v65" : W = phi("L23" => %"v43", "L24" => %"v64")]:
    => br %"v65" ? "L20" : "L6";
  @"L20":
    => ret #4294967295;
  @"L6":
    %"v68" = %"v0" +p #160;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Read 8) %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v74" = %"v73" +p #8;
    %"chk17" : A = (Check 0 8 Read 8) %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v76" : L = Ptoi %"v70";
    %"v77" : L = Ptoi %"v75";
    %"v78" : L = Sub %"v76", %"v77";
    %"v79" : L = Div %"v78", #4;
    %"v84" : W = (Cmp Ne L) %"v79", #0
    => br %"v84" ? "L80" : "L82";
  @"L80":
    %"v87" = %"v0" +p #152;
    %"chk18" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call %"v92" : W = $"__libio_codecvt_encoding"(P %"v88");
    %"v97" : W = (Cmp Sgt W) %"v92", #0
    => br %"v97" ? "L93" : "L94";
  @"L93":
    %"v100" : L = (Ext Sw) %"v92";
    %"v101" : L = Mul %"v79", %"v100"
    => goto "L95";
  @"L94":
    %"v105" = %"v0" +p #160;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk0", %"v105";
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 8 Read 8) %"v106";
    %"v107" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v111" = %"v110" +p #16;
    %"chk22" : A = (Check 0 8 Read 8) %"v111";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v113" : L = Ptoi %"v107";
    %"v114" : L = Ptoi %"v112";
    %"v115" : L = Sub %"v113", %"v114";
    %"v116" : L = Div %"v115", #4;
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v120" = %"v119" +p #88;
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v124" = %"v123" +p #96;
    %"chk25" : A = (Check 0 8 Read 1) %"v124";
    %"v125" : L = (RawLoad LdL 0) %"chk25";
    %"chk26" : A = (Check 0 8 Write 1) %"v120";
    store Wl [%"chk26" + 0] <- %"v125";
    %"v129" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v130" = %"v129" +p #88;
    %"v132" = %"v0" +p #24;
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v132";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v135" = %"v0" +p #16;
    %"chk29" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v135";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk29";
    call %"v138" : W = $"__libio_codecvt_length"(P %"v88", P %"v130", P %"v133", P %"v136", L %"v116");
    %"v140" = %"v0" +p #8;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk28", %"v132";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v145" : L = (Ext Sw) %"v138";
    %"v146" = %"v143" +p %"v145";
    %"chk31" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v140";
    store.ptr [%"chk31" + 0] <- %"v146";
    %"chk32" : A = (Renew 0 8 Read 8) %"chk29", %"v135";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Renew 0 8 Read 8) %"chk28", %"v132";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v153" : L = Ptoi %"v149";
    %"v154" : L = Ptoi %"v152";
    %"v155" : L = Sub %"v153", %"v154";
    %"v158" : L = Sub %"v155", %"v145";
    %"v159" : L = Neg %"v158"
    => goto "L95";
  @"L95" [%"pr.1" : L = phi("L93" => %"v101", "L94" => %"v159")]:
    %"v161" = %"v0" +p #216;
    %"chk34" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v161";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_1.v4" : L = Ptoi %"v162";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v164" = %"v162" +p #128;
    %"chk35" : A = (Check 0 8 Read 8) %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : F = CheckFunction %"v165";
    rawcall %"v168" : L = %"chk36"(P %"v0", L %"pr.1", W #1);
    %"v175" : W = (Cmp Ne L) %"v168", #18446744073709551615
    => br %"v175" ? "L169" : "L170";
  @"L169":
    %"v177" = %"v0" +p #160;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk0", %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v179" = %"v178" +p #8;
    %"v182" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"chk39" : A = (Check 0 8 Read 8) %"v182";
    %"v183" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"chk40" : A = (Check 0 8 Write 8) %"v179";
    store.ptr [%"chk40" + 0] <- %"v183";
    %"v185" = %"v0" +p #16;
    %"v187" = %"v0" +p #8;
    %"chk41" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v187";
    %"v188" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"chk42" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v185";
    store.ptr [%"chk42" + 0] <- %"v188"
    => goto "L82";
  @"L170":
    %"v192" : P = Copy $"__libc_errno";
    %"chk43" : A = (Check 0 4 Read 1) %"v192";
    %"v193" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v194" : W = (Cmp Eq W) %"v193", #29
    => br %"v194" ? "L82" : "L190";
  @"L190":
    => goto "L82";
  @"L82" [%"pr.4" : W = phi("L169" => #0, "L190" => #4294967295, "L170" => #0, "L6" => #0)]:
    %"v199" : W = (Cmp Ne W) %"pr.4", #4294967295
    => br %"v199" ? "L195" : "L197";
  @"L195":
    %"v201" = %"v0" +p #144;
    %"chk44" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"v201";
    store Wl [%"chk44" + 0] <- #18446744073709551615
    => goto "L197";
  @"L197":
    => ret %"pr.4"
} }.

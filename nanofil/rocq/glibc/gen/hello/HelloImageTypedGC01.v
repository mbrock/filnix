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

Definition hello_image_fn___gconv : func :=
  ir_fn{ "export" "__gconv"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10") -> (RClass W) {
  @"start":
    (Flight (a "v19") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v20" : L = Ptoi %"v0";
    %"v21" : L = Ptoi %"v19";
    %"v22" : W = (Cmp Eq L) %"v20", %"v21"
    => br %"v22" ? "L14" : "L16";
  @"L14":
    => ret #8;
  @"L16":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"v26" : L = Sub %"v25", #1;
    %"v31" : L = Ptoi %"v10";
    %"v32" : L = Ptoi #0;
    %"v33" : W = (Cmp Ne L) %"v31", %"v32"
    => br %"v33" ? "L29" : "L28";
  @"L28":
    %"v34" : P = Copy $"glibc_gconv#str.269";
    %"v35" : P = Copy $"glibc_gconv#str.270";
    %"v36" : P = Copy $"glibc_gconv#str.271";
    call void $"__libc_assert_fail"(P %"v34", P %"v35", W #42, P %"v36")
    => goto "L29";
  @"L29":
    %"chk1" : A = (Check 0 8 Write 1) %"v10";
    store Wl [%"chk1" + 0] <- #0;
    %"v39" = %"v0" +p #16;
    %"v41" : L = Mul %"v26", #48;
    %"v42" = %"v39" +p %"v41";
    %"v47" : L = Ptoi %"v6";
    %"v49" : W = (Cmp Ne L) %"v47", %"v32"
    => br %"v49" ? "L43" : "L45";
  @"L43":
    %"chk2" : A = (Check 0 8 Read 8) %"v6";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk2"
    => goto "L45";
  @"L45" [%"v52" : P = phi("L43" => %"v51", "L29" => #0)]:
    %"chk3" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk3" + 0] <- %"v52";
    %"v54" = %"v0" +p #16;
    %"v57" = %"v54" +p %"v41";
    %"v58" = %"v57" +p #8;
    %"chk4" : A = (Check 0 8 Write 8) %"v58";
    store.ptr [%"chk4" + 0] <- %"v8";
    %"v62" = %"v0" +p #8;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v62";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v64" = %"v63" +p #40;
    %"chk6" : A = (Check 0 8 Read 8) %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk8" : A = (Check 0 8 Read 8) %"v71";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v73" : L = Ptoi %"v72";
    %"v75" : W = (Cmp Ne L) %"v73", %"v32"
    => br %"v75" ? "L68" : "L67";
  @"L67":
    => goto "L68";
  @"L68":
    %"v81" : L = Ptoi %"v2";
    %"v83" : W = (Cmp Eq L) %"v81", %"v32"
    => br %"v83" ? "L85" : "L84";
  @"L84":
    %"chk9" : A = (Check 0 8 Read 8) %"v2";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v88" : L = Ptoi %"v87";
    %"v90" : W = (Cmp Eq L) %"v88", %"v32"
    => goto "L85";
  @"L85" [%"v92" : W = phi("L68" => #1, "L84" => %"v90")]:
    => br %"v92" ? "iw_1.join" : "L78";
  @"iw_1.join":
    %"v96" = %"v0" +p #8;
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v99" = %"v0" +p #16;
    %"v108" = %"v99" +p %"v41";
    %"chk11" : A = (Check 0 8 Read 8) %"v108";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v110" : L = Ptoi %"v109";
    %"v112" : W = (Cmp Eq L) %"v110", %"v32"
    => br %"v112" ? "L103" : "L102";
  @"L102":
    => goto "L103";
  @"L103" [%"v113" : W = phi("L102" => #1, "iw_1.join" => #2)]:
    %"chk12" : F = CheckFunction %"v65";
    rawcall %"v114" : W = %"chk12"(P %"v97", P %"v99", P #0, P #0, P #0, P %"v10", W %"v113", W #0);
    %"v119" : W = (Cmp Eq W) %"v114", #0
    => br %"v119" ? "L121" : "L79";
  @"L121" [%"pr.2" : L = phi("L122" => %"v135", "L103" => #0)]:
    %"v127" : W = (Cmp Ule L) %"pr.2", %"v26"
    => br %"v127" ? "L122" : "L79";
  @"L122":
    %"v129" = %"v0" +p #16;
    %"v131" : L = Mul %"pr.2", #48;
    %"v132" = %"v129" +p %"v131";
    %"v133" = %"v132" +p #20;
    %"chk13" : A = (Check 0 4 Write 1) %"v133";
    store Ww [%"chk13" + 0] <- #0;
    %"v135" : L = Add %"pr.2", #1
    => goto poll "L121";
  @"L78":
    => br %"v49" ? "L144" : "L145";
  @"L144":
    %"chk14" : A = (Check 0 8 Read 8) %"v6";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v148" : L = Ptoi %"v147";
    %"v150" : W = (Cmp Ne L) %"v148", %"v32"
    => goto "L145";
  @"L145" [%"v152" : W = phi("L78" => #0, "L144" => %"v150")]:
    => br %"v152" ? "L156" : "L138";
  @"L138":
    %"v153" : P = Copy $"glibc_gconv#str.272";
    %"v154" : P = Copy $"glibc_gconv#str.270";
    %"v155" : P = Copy $"glibc_gconv#str.271";
    call void $"__libc_assert_fail"(P %"v153", P %"v154", W #70, P %"v155")
    => goto "L156";
  @"L156":
    %"chk15" : A = (Check 0 8 Read 8) %"v2";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v164" = %"v0" +p #8;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk5", %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v167" = %"v0" +p #16;
    %"chk17" : F = CheckFunction %"v65";
    rawcall %"v171" : W = %"chk17"(P %"v165", P %"v167", P %"v2", P %"v4", P #0, P %"v10", W #0, W #0);
    %"v173" : W = (Cmp Eq W) %"v171", #4
    => br %"v173" ? "L174" : "L175";
  @"L174":
    %"chk18" : A = (Renew 0 8 Read 8) %"chk15", %"v2";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v179" : L = Ptoi %"v160";
    %"v180" : L = Ptoi %"v178";
    %"v181" : W = (Cmp Ne L) %"v179", %"v180"
    => goto "L175";
  @"L175" [%"v183" : W = phi("L156" => #0, "L174" => %"v181")]:
    => br %"v183" ? "L184" : "L185";
  @"L184":
    %"chk19" : A = (Renew 0 8 Read 8) %"chk15", %"v2";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v189" = %"v0" +p #8;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk5", %"v189";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v191" = %"v190" +p #72;
    %"chk21" : A = (Check 0 4 Read 1) %"v191";
    %"v192" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"v193" : L = (Ext Sw) %"v192";
    %"v194" = %"v187" +p %"v193";
    %"v196" : L = Ptoi %"v194";
    %"v197" : L = Ptoi %"v4";
    %"v198" : W = (Cmp Ule L) %"v196", %"v197"
    => goto "L185";
  @"L185" [%"v200" : W = phi("L175" => #0, "L184" => %"v198")]:
    => br %"v200" ? poll "L156" : "L79";
  @"L79" [%"pr.1" : W = phi("L121" => %"v114", "L103" => %"v114", "L185" => %"v171")]:
    => br %"v49" ? "L208" : "L209";
  @"L208":
    %"chk22" : A = (Check 0 8 Read 8) %"v6";
    %"v211" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v212" : L = Ptoi %"v211";
    %"v214" : W = (Cmp Ne L) %"v212", %"v32"
    => goto "L209";
  @"L209" [%"v216" : W = phi("L79" => #0, "L208" => %"v214")]:
    => br %"v216" ? "L201" : "L203";
  @"L201":
    %"v219" = %"v0" +p #16;
    %"v222" = %"v219" +p %"v41";
    %"chk23" : A = (Check 0 8 Read 8) %"v222";
    %"v223" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk24" + 0] <- %"v223"
    => goto "L203";
  @"L203":
    => ret %"pr.1"
} }.

Definition hello_image_fn___gconv_get_builtin_trans : func :=
  ir_fn{ "export" "__gconv_get_builtin_trans"(P %"v0", P %"v2") -> RVoid {
  @"start":
    => goto "L5";
  @"L5" [%"pr.1" : L = phi("L7" => %"v25", "start" => #0)]:
    %"v11" : W = (Cmp Ult L) %"pr.1", #12
    => br %"v11" ? "L6" : "L8";
  @"L6":
    %"v16" : P = Copy $"glibc_gconv_builtin#map";
    %"v18" : L = Shl %"pr.1", #5;
    %"v19" = %"v16" +p %"v18";
    %"chk0" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v21" : W = $"__GI_strcmp"(P %"v0", P %"v20");
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => br %"v22" ? "L8" : "L7";
  @"L7":
    %"v25" : L = Add %"pr.1", #1
    => goto poll "L5";
  @"L8":
    => br %"v11" ? "L28" : "L27";
  @"L27":
    %"v32" : P = Copy $"glibc_gconv_builtin#str.244";
    %"v33" : P = Copy $"glibc_gconv_builtin#str.245";
    %"v34" : P = Copy $"glibc_gconv_builtin#str.246";
    call void $"__libc_assert_fail"(P %"v32", P %"v33", W #69, P %"v34")
    => goto "L28";
  @"L28":
    %"v36" = %"v2" +p #40;
    %"v37" : P = Copy $"glibc_gconv_builtin#map";
    %"v39" : L = Shl %"pr.1", #5;
    %"v40" = %"v37" +p %"v39";
    %"v41" = %"v40" +p #8;
    %"chk1" : A = (Check 0 8 Read 8) %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 8 Write 8) %"v36";
    store.ptr [%"chk2" + 0] <- %"v42";
    %"v44" = %"v2" +p #48;
    %"v45" : P = Copy $"glibc_gconv_builtin#map";
    %"v48" = %"v45" +p %"v39";
    %"v49" = %"v48" +p #16;
    %"chk3" : A = (Check 0 8 Read 8) %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v44";
    store.ptr [%"chk4" + 0] <- %"v50";
    %"v52" = %"v2" +p #56;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v52";
    store.ptr [%"chk5" + 0] <- #0;
    %"v54" = %"v2" +p #64;
    %"chk6" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v54";
    store.ptr [%"chk6" + 0] <- #0;
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"v2";
    store.ptr [%"chk7" + 0] <- #0;
    %"v57" = %"v2" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"v57";
    store.ptr [%"chk8" + 0] <- #0;
    %"v59" = %"v2" +p #72;
    %"v60" : P = Copy $"glibc_gconv_builtin#map";
    %"v63" = %"v60" +p %"v39";
    %"v64" = %"v63" +p #24;
    %"chk9" : A = (Check 0 1 Read 1) %"v64";
    %"v65" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"chk10" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v59";
    store Ww [%"chk10" + 0] <- %"v65";
    %"v67" = %"v2" +p #76;
    %"v68" : P = Copy $"glibc_gconv_builtin#map";
    %"v71" = %"v68" +p %"v39";
    %"v72" = %"v71" +p #25;
    %"chk11" : A = (Check 0 1 Read 1) %"v72";
    %"v73" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"chk12" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v67";
    store Ww [%"chk12" + 0] <- %"v73";
    %"v75" = %"v2" +p #80;
    %"v76" : P = Copy $"glibc_gconv_builtin#map";
    %"v79" = %"v76" +p %"v39";
    %"v80" = %"v79" +p #26;
    %"chk13" : A = (Check 0 1 Read 1) %"v80";
    %"v81" : W = (RawLoad (LdNarrow Sb) 0) %"chk13";
    %"chk14" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v75";
    store Ww [%"chk14" + 0] <- %"v81";
    %"v83" = %"v2" +p #84;
    %"v84" : P = Copy $"glibc_gconv_builtin#map";
    %"v87" = %"v84" +p %"v39";
    %"v88" = %"v87" +p #27;
    %"chk15" : A = (Check 0 1 Read 1) %"v88";
    %"v89" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v83";
    store Ww [%"chk16" + 0] <- %"v89";
    %"v91" = %"v2" +p #88;
    %"chk17" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v91";
    store Ww [%"chk17" + 0] <- #0
    => ret void
} }.

Definition hello_image_fn___gconv_load_cache : func :=
  ir_fn{ "export" "__gconv_load_cache"() -> (RClass W) {
  @"start":
    %"v1" : P = (Alloc 8) #144;
    %"v3" : P = Copy $"__gconv_path_envvar";
    %"v4" : P = Copy $"glibc_gconv_cache#str.281";
    call %"v5" : P = $"__GI_getenv"(P %"v4");
    %"chk0" : A = (Check 0 8 Write 8) %"v3";
    store.ptr [%"chk0" + 0] <- %"v5";
    %"v9" : P = Copy $"__gconv_path_envvar";
    %"chk1" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v10";
    %"v12" : L = Ptoi #0;
    %"v13" : W = (Cmp Ne L) %"v11", %"v12"
    => br %"v13" ? "L6" : "L8";
  @"L6":
    => ret #4294967295;
  @"L8":
    %"v16" : P = Copy $"glibc_gconv_cache#str.282";
    call %"v18" : W = $"__GI___open_nocancel"(P %"v16", W #524288, W #0);
    %"v23" : L = (Ext Sw) %"v18";
    %"v26" : W = (Cmp Eq L) %"v23", #18446744073709551615
    => br %"v26" ? "L19" : "L21";
  @"L19":
    => ret #4294967295;
  @"L21":
    call %"v33" : W = $"__GI___fstat64"(W %"v18", P %"v1");
    %"v34" : W = (Cmp Slt W) %"v33", #0
    => br %"v34" ? "L38" : "L37";
  @"L37":
    %"v39" = %"v1" +p #48;
    %"chk2" : A = (Check 0 8 Read 1) %"v39";
    %"v40" : L = (RawLoad LdL 0) %"chk2";
    %"v41" : W = (Cmp Ult L) %"v40", #16
    => goto "L38";
  @"L38" [%"v43" : W = phi("L21" => #1, "L37" => %"v41")]:
    => br %"v43" ? "L44" : "L31";
  @"L44":
    call void $"__GI___close_nocancel_nostatus"(W %"v18")
    => ret #4294967295;
  @"L31":
    %"v48" : P = Copy $"glibc_gconv_cache#cache_size";
    %"v49" = %"v1" +p #48;
    %"chk3" : A = (Check 0 8 Read 1) %"v49";
    %"v50" : L = (RawLoad LdL 0) %"chk3";
    %"chk4" : A = (Check 0 8 Write 1) %"v48";
    store Wl [%"chk4" + 0] <- %"v50";
    %"v51" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"v52" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk5" : A = (Check 0 8 Read 1) %"v52";
    %"v53" : L = (RawLoad LdL 0) %"chk5";
    call %"v55" : P = $"__GI___mmap"(P #0, L %"v53", W #1, W #1, W %"v18", L #0);
    %"chk6" : A = (Check 0 8 Write 8) %"v51";
    store.ptr [%"chk6" + 0] <- %"v55";
    %"v59" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk7" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk7";
    (Flight (a "v63") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v64" : L = Ptoi %"v60";
    %"v65" : L = Ptoi %"v63";
    %"v66" : W = (Cmp Eq L) %"v64", %"v65"
    => br %"v66" ? "L56" : "L58";
  @"L56":
    %"v70" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"v71" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk8" : A = (Check 0 8 Read 1) %"v71";
    %"v72" : L = (RawLoad LdL 0) %"chk8";
    call %"v73" : P = $"malloc"(L %"v72");
    %"chk9" : A = (Check 0 8 Write 8) %"v70";
    store.ptr [%"chk9" + 0] <- %"v73";
    %"v77" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk10" : A = (Check 0 8 Read 8) %"v77";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v79" : L = Ptoi %"v78";
    %"v81" : W = (Cmp Eq L) %"v79", %"v12"
    => br %"v81" ? poll "L44" : "L83";
  @"L83" [%"pr.1" : L = phi("L99" => %"v110", "L56" => #0)]:
    %"v88" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk11" : A = (Check 0 8 Read 8) %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v91" = %"v89" +p %"pr.1";
    %"v92" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk12" : A = (Check 0 8 Read 1) %"v92";
    %"v93" : L = (RawLoad LdL 0) %"chk12";
    %"v95" : L = Sub %"v93", %"pr.1";
    call %"v96" : L = $"__GI___read"(W %"v18", P %"v91", L %"v95");
    %"v103" : W = (Cmp Eq L) %"v96", #18446744073709551615
    => br %"v103" ? "L97" : "L99";
  @"L97":
    %"v104" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk13" : A = (Check 0 8 Read 8) %"v104";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk13";
    call void $"free"(P %"v105");
    %"v106" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk14" : A = (Check 0 8 Write 8) %"v106";
    store.ptr [%"chk14" + 0] <- #0
    => goto poll "L44";
  @"L99":
    %"v110" : L = Add %"pr.1", %"v96";
    %"v112" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk15" : A = (Check 0 8 Read 1) %"v112";
    %"v113" : L = (RawLoad LdL 0) %"chk15";
    %"v114" : W = (Cmp Ult L) %"v110", %"v113"
    => br %"v114" ? poll "L83" : "L85";
  @"L85":
    %"v115" : P = Copy $"glibc_gconv_cache#cache_malloced";
    %"chk16" : A = (Check 0 4 Write 1) %"v115";
    store Ww [%"chk16" + 0] <- #1
    => goto "L58";
  @"L58":
    call void $"__GI___close_nocancel_nostatus"(W %"v18");
    %"v117" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk17" : A = (Check 0 8 Read 8) %"v117";
    %"v118" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Read 1) %"v118";
    %"v123" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v124" : L = (Ext Uw) %"v123";
    %"v125" : W = (Cmp Ne L) %"v124", #536937252
    => br %"v125" ? "L127" : "L126";
  @"L126":
    %"v129" = %"v118" +p #4;
    %"chk19" : A = (HalfCheck Upper 0 2 Read 1) %"chk18", %"v129";
    %"v130" : W = (RawLoad (LdNarrow Uh) 0) %"chk19";
    %"v131" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk20" : A = (Check 0 8 Read 1) %"v131";
    %"v132" : L = (RawLoad LdL 0) %"chk20";
    %"v133" : L = (Ext Uw) %"v130";
    %"v134" : W = (Cmp Uge L) %"v133", %"v132"
    => goto "L127";
  @"L127" [%"v138" : W = phi("L58" => #1, "L126" => %"v134")]:
    => br %"v138" ? "L140" : "L139";
  @"L139":
    %"v142" = %"v118" +p #6;
    %"chk21" : A = (HalfCheck Upper 0 2 Read 1) %"chk18", %"v142";
    %"v143" : W = (RawLoad (LdNarrow Uh) 0) %"chk21";
    %"v144" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk22" : A = (Check 0 8 Read 1) %"v144";
    %"v145" : L = (RawLoad LdL 0) %"chk22";
    %"v146" : L = (Ext Uw) %"v143";
    %"v147" : W = (Cmp Uge L) %"v146", %"v145"
    => goto "L140";
  @"L140" [%"v151" : W = phi("L127" => #1, "L139" => %"v147")]:
    => br %"v151" ? "L153" : "L152";
  @"L152":
    %"v155" = %"v118" +p #8;
    %"chk23" : A = (HalfCheck Upper 0 2 Read 1) %"chk18", %"v155";
    %"v156" : W = (RawLoad (LdNarrow Uh) 0) %"chk23";
    %"v157" : W = (Cmp Eq W) %"v156", #0
    => goto "L153";
  @"L153" [%"v161" : W = phi("L140" => #1, "L152" => %"v157")]:
    => br %"v161" ? "L163" : "L162";
  @"L162":
    %"v165" = %"v118" +p #6;
    %"chk24" : A = (HalfCheck Upper 0 2 Read 1) %"chk18", %"v165";
    %"v166" : W = (RawLoad (LdNarrow Uh) 0) %"chk24";
    %"v168" = %"v118" +p #8;
    %"chk25" : A = (HalfCheck Upper 0 2 Read 1) %"chk18", %"v168";
    %"v169" : W = (RawLoad (LdNarrow Uh) 0) %"chk25";
    %"v170" : L = (Ext Uw) %"v169";
    %"v171" : L = Shl %"v170", #2;
    %"v172" : L = (Ext Uw) %"v166";
    %"v173" : L = Add %"v172", %"v171";
    %"v174" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk26" : A = (Check 0 8 Read 1) %"v174";
    %"v175" : L = (RawLoad LdL 0) %"chk26";
    %"v176" : W = (Cmp Ugt L) %"v173", %"v175"
    => goto "L163";
  @"L163" [%"v180" : W = phi("L153" => #1, "L162" => %"v176")]:
    => br %"v180" ? "L182" : "L181";
  @"L181":
    %"v184" = %"v118" +p #10;
    %"chk27" : A = (HalfCheck Upper 0 2 Read 1) %"chk18", %"v184";
    %"v185" : W = (RawLoad (LdNarrow Uh) 0) %"chk27";
    %"v186" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk28" : A = (Check 0 8 Read 1) %"v186";
    %"v187" : L = (RawLoad LdL 0) %"chk28";
    %"v188" : L = (Ext Uw) %"v185";
    %"v189" : W = (Cmp Uge L) %"v188", %"v187"
    => goto "L182";
  @"L182" [%"v193" : W = phi("L163" => #1, "L181" => %"v189")]:
    => br %"v193" ? "L195" : "L194";
  @"L194":
    %"v197" = %"v118" +p #12;
    %"chk29" : A = (HalfCheck Upper 0 2 Read 1) %"chk18", %"v197";
    %"v198" : W = (RawLoad (LdNarrow Uh) 0) %"chk29";
    %"v199" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk30" : A = (Check 0 8 Read 1) %"v199";
    %"v200" : L = (RawLoad LdL 0) %"chk30";
    %"v201" : L = (Ext Uw) %"v198";
    %"v202" : W = (Cmp Ugt L) %"v201", %"v200"
    => goto "L195";
  @"L195" [%"v206" : W = phi("L182" => #1, "L194" => %"v202")]:
    => br %"v206" ? "L119" : "L121";
  @"L119":
    %"v210" : P = Copy $"glibc_gconv_cache#cache_malloced";
    %"chk31" : A = (Check 0 4 Read 1) %"v210";
    %"v211" : W = (RawLoad (LdNarrow Sw) 0) %"chk31"
    => br %"v211" ? "L207" : "L208";
  @"L207":
    %"v212" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk32" : A = (Check 0 8 Read 8) %"v212";
    %"v213" : P = (RawLoadPointer 0 load_effects) %"chk32";
    call void $"free"(P %"v213");
    %"v214" : P = Copy $"glibc_gconv_cache#cache_malloced";
    %"chk33" : A = (Check 0 4 Write 1) %"v214";
    store Ww [%"chk33" + 0] <- #0
    => goto "L209";
  @"L208":
    %"v215" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk34" : A = (Check 0 8 Read 8) %"v215";
    %"v216" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v217" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk35" : A = (Check 0 8 Read 1) %"v217";
    %"v218" : L = (RawLoad LdL 0) %"chk35";
    call %"v219" : W = $"__GI___munmap"(P %"v216", L %"v218")
    => goto "L209";
  @"L209":
    %"v220" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk36" : A = (Check 0 8 Write 8) %"v220";
    store.ptr [%"chk36" + 0] <- #0
    => ret #4294967295;
  @"L121":
    => ret #0
} }.

Definition hello_image_fn___gconv_compare_alias_cache : func :=
  ir_fn{ "export" "__gconv_compare_alias_cache"(P %"v0", P %"v2", P %"v4") -> (RClass W) {
  @"start":
    %"v7" : P = (Alloc 8) #8;
    %"v11" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" : L = Ptoi %"v12";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L8" : "iw_1.start";
  @"L8":
    => ret #4294967295;
  @"iw_1.start":
    %"iw_1.v11" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v13" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v13";
    %"iw_1.v14" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v16" = %"iw_1.v12" +p #4;
    %"chk3" : A = (Check 0 2 Read 1) %"iw_1.v16";
    %"iw_1.v17" : W = (RawLoad (LdNarrow Uh) 0) %"chk3";
    %"iw_1.v18" : L = (Ext Uw) %"iw_1.v17";
    %"iw_1.v19" = %"iw_1.v14" +p %"iw_1.v18";
    %"iw_1.v20" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk4" : A = (Check 0 8 Read 8) %"iw_1.v20";
    %"iw_1.v21" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v23" = %"iw_1.v12" +p #6;
    %"chk5" : A = (HalfCheck Upper 0 2 Read 1) %"chk3", %"iw_1.v23";
    %"iw_1.v24" : W = (RawLoad (LdNarrow Uh) 0) %"chk5";
    %"iw_1.v25" : L = (Ext Uw) %"iw_1.v24";
    %"iw_1.v26" = %"iw_1.v21" +p %"iw_1.v25";
    call %"iw_1.v28" : L = $"__hash_string"(P %"v0");
    %"iw_1.v29" : W = Copy %"iw_1.v28";
    %"iw_1.v31" = %"iw_1.v12" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 2 Read 1) %"chk3", %"iw_1.v31";
    %"iw_1.v32" : W = (RawLoad (LdNarrow Uh) 0) %"chk6";
    %"iw_1.v33" : W = Urem %"iw_1.v29", %"iw_1.v32";
    %"iw_1.v34" : W = Copy %"iw_1.v28";
    %"iw_1.v37" : W = (RawLoad (LdNarrow Uh) 0) %"chk6";
    %"iw_1.v38" : W = Sub %"iw_1.v37", #2;
    %"iw_1.v39" : W = Urem %"iw_1.v34", %"iw_1.v38";
    %"iw_1.v40" : W = Add %"iw_1.v39", #1;
    %"iw_1.v41" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk8" : A = (Check 0 8 Read 1) %"iw_1.v41";
    %"iw_1.v42" : L = (RawLoad LdL 0) %"chk8";
    %"chk9" : A = (Renew 0 2 Read 1) %"chk3", %"iw_1.v16";
    %"iw_1.v45" : W = (RawLoad (LdNarrow Uh) 0) %"chk9";
    %"iw_1.v46" : L = (Ext Uw) %"iw_1.v45";
    %"iw_1.v47" : L = Sub %"iw_1.v42", %"iw_1.v46"
    => goto "iw_1.L48";
  @"iw_1.L48" [%"iw_1.pr.1" : W = phi("iw_1.start" => %"iw_1.v33", "iw_1.L59" => %"iw_1.v100", "iw_1.L95" => %"iw_1.v109")]:
    %"iw_1.v53" : L = (Ext Uw) %"iw_1.pr.1";
    %"iw_1.v54" : L = Shl %"iw_1.v53", #2;
    %"iw_1.v55" = %"iw_1.v26" +p %"iw_1.v54";
    %"chk10" : A = (Check 0 2 Read 1) %"iw_1.v55";
    %"iw_1.v56" : W = (RawLoad (LdNarrow Uh) 0) %"chk10";
    %"iw_1.v57" : W = (Cmp Ne W) %"iw_1.v56", #0
    => br %"iw_1.v57" ? "iw_1.L49" : "iw_1.join";
  @"iw_1.L49":
    %"iw_1.v66" : W = (RawLoad (LdNarrow Uh) 0) %"chk10";
    %"iw_1.v67" : W = Copy %"iw_1.v47";
    %"iw_1.v68" : W = (Cmp Ult W) %"iw_1.v66", %"iw_1.v67"
    => br %"iw_1.v68" ? "iw_1.L69" : "iw_1.L70";
  @"iw_1.L69":
    %"iw_1.v78" : W = (RawLoad (LdNarrow Uh) 0) %"chk10";
    %"iw_1.v79" : L = (Ext Uw) %"iw_1.v78";
    %"iw_1.v80" = %"iw_1.v19" +p %"iw_1.v79";
    call %"iw_1.v81" : W = $"__GI_strcmp"(P %"v0", P %"iw_1.v80");
    %"iw_1.v82" : W = (Cmp Eq W) %"iw_1.v81", #0
    => goto "iw_1.L70";
  @"iw_1.L70" [%"iw_1.v84" : W = phi("iw_1.L49" => #0, "iw_1.L69" => %"iw_1.v82")]:
    => br %"iw_1.v84" ? "iw_1.L58" : "iw_1.L59";
  @"iw_1.L58":
    %"iw_1.v91" = %"iw_1.v55" +p #2;
    %"chk13" : A = (HalfCheck Upper 0 2 Read 1) %"chk10", %"iw_1.v91";
    %"iw_1.v92" : W = (RawLoad (LdNarrow Uh) 0) %"chk13";
    %"iw_1.v93" : L = (Ext Uw) %"iw_1.v92"
    => goto "iw_1.join";
  @"iw_1.L59":
    %"iw_1.v100" : W = Add %"iw_1.pr.1", %"iw_1.v40";
    %"iw_1.v102" = %"iw_1.v12" +p #8;
    %"chk14" : A = (Renew 0 2 Read 1) %"chk6", %"iw_1.v102";
    %"iw_1.v103" : W = (RawLoad (LdNarrow Uh) 0) %"chk14";
    %"iw_1.v104" : W = (Cmp Uge W) %"iw_1.v100", %"iw_1.v103"
    => br %"iw_1.v104" ? "iw_1.L95" : poll "iw_1.L48";
  @"iw_1.L95":
    %"iw_1.v107" = %"iw_1.v12" +p #8;
    %"iw_1.v108" : W = (RawLoad (LdNarrow Uh) 0) %"chk14";
    %"iw_1.v109" : W = Sub %"iw_1.v100", %"iw_1.v108"
    => goto poll "iw_1.L48";
  @"iw_1.join" [%"v22" : W = phi("iw_1.L58" => #0, "iw_1.L48" => #4294967295); %"pr.1" : L = phi("iw_1.L58" => %"iw_1.v93", "iw_1.L48" => #0)]:
    %"v23" : W = (Cmp Ne W) %"v22", #0
    => br %"v23" ? "L25" : "L24";
  @"L24":
    call %"v27" : W = $"glibc_gconv_cache#find_module_idx"(P %"v2", P %"v7");
    %"v28" : W = (Cmp Ne W) %"v27", #0
    => goto "L25";
  @"L25" [%"v30" : W = phi("iw_1.join" => #1, "L24" => %"v28")]:
    => br %"v30" ? "L18" : "L19";
  @"L18":
    call %"v34" : W = $"__GI_strcmp"(P %"v0", P %"v2");
    %"chk16" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk16" + 0] <- %"v34"
    => goto "L20";
  @"L19":
    %"chk17" : A = (Check 0 8 Read 1) %"v7";
    %"v37" : L = (RawLoad LdL 0) %"chk17";
    %"v38" : L = Sub %"pr.1", %"v37";
    %"chk18" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk18" + 0] <- %"v38"
    => goto "L20";
  @"L20":
    => ret #0
} }.

Definition hello_image_fn___gconv_lookup_cache : func :=
  ir_fn{ "export" "__gconv_lookup_cache"(P %"v0", P %"v2", P %"v4", P %"v6", W %"v8") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v21" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk0" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v23" : L = Ptoi %"v22";
    %"v24" : L = Ptoi #0;
    %"v25" : W = (Cmp Eq L) %"v23", %"v24"
    => br %"v25" ? "L18" : "L20" };
  ir_blk{ @"L18":
    => ret #2 };
  ir_blk{ @"L20":
    %"v27" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk1" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v29" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk2" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v32" = %"v28" +p #4;
    %"chk3" : A = (Check 0 2 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Uh) 0) %"chk3";
    %"v34" : L = (Ext Uw) %"v33";
    %"v35" = %"v30" +p %"v34";
    %"v36" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk4" : A = (Check 0 8 Read 8) %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v39" = %"v28" +p #10;
    %"chk5" : A = (HalfCheck Upper 0 2 Read 1) %"chk3", %"v39";
    %"v40" : W = (RawLoad (LdNarrow Uh) 0) %"chk5";
    %"v41" : L = (Ext Uw) %"v40";
    %"v42" = %"v37" +p %"v41";
    %"iw_1.v11" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v13" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.v13";
    %"iw_1.v14" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v16" = %"iw_1.v12" +p #4;
    %"chk8" : A = (Check 0 2 Read 1) %"iw_1.v16";
    %"iw_1.v17" : W = (RawLoad (LdNarrow Uh) 0) %"chk8";
    %"iw_1.v18" : L = (Ext Uw) %"iw_1.v17";
    %"iw_1.v19" = %"iw_1.v14" +p %"iw_1.v18";
    %"iw_1.v20" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk9" : A = (Check 0 8 Read 8) %"iw_1.v20";
    %"iw_1.v21" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v23" = %"iw_1.v12" +p #6;
    %"chk10" : A = (HalfCheck Upper 0 2 Read 1) %"chk8", %"iw_1.v23";
    %"iw_1.v24" : W = (RawLoad (LdNarrow Uh) 0) %"chk10";
    %"iw_1.v25" : L = (Ext Uw) %"iw_1.v24";
    %"iw_1.v26" = %"iw_1.v21" +p %"iw_1.v25";
    call %"iw_1.v28" : L = $"__hash_string"(P %"v2");
    %"iw_1.v29" : W = Copy %"iw_1.v28";
    %"iw_1.v31" = %"iw_1.v12" +p #8;
    %"chk11" : A = (HalfCheck Upper 0 2 Read 1) %"chk8", %"iw_1.v31";
    %"iw_1.v32" : W = (RawLoad (LdNarrow Uh) 0) %"chk11";
    %"iw_1.v33" : W = Urem %"iw_1.v29", %"iw_1.v32";
    %"iw_1.v34" : W = Copy %"iw_1.v28";
    %"iw_1.v37" : W = (RawLoad (LdNarrow Uh) 0) %"chk11";
    %"iw_1.v38" : W = Sub %"iw_1.v37", #2;
    %"iw_1.v39" : W = Urem %"iw_1.v34", %"iw_1.v38";
    %"iw_1.v40" : W = Add %"iw_1.v39", #1;
    %"iw_1.v41" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk13" : A = (Check 0 8 Read 1) %"iw_1.v41";
    %"iw_1.v42" : L = (RawLoad LdL 0) %"chk13";
    %"chk14" : A = (Renew 0 2 Read 1) %"chk8", %"iw_1.v16";
    %"iw_1.v45" : W = (RawLoad (LdNarrow Uh) 0) %"chk14";
    %"iw_1.v46" : L = (Ext Uw) %"iw_1.v45";
    %"iw_1.v47" : L = Sub %"iw_1.v42", %"iw_1.v46"
    => goto "iw_1.L48" };
  ir_blk{ @"iw_1.L48" [%"iw_1.pr.1" : W = phi("L20" => %"iw_1.v33", "iw_1.L59" => %"iw_1.v100", "iw_1.L95" => %"iw_1.v109")]:
    %"iw_1.v53" : L = (Ext Uw) %"iw_1.pr.1";
    %"iw_1.v54" : L = Shl %"iw_1.v53", #2;
    %"iw_1.v55" = %"iw_1.v26" +p %"iw_1.v54";
    %"chk15" : A = (Check 0 2 Read 1) %"iw_1.v55";
    %"iw_1.v56" : W = (RawLoad (LdNarrow Uh) 0) %"chk15";
    %"iw_1.v57" : W = (Cmp Ne W) %"iw_1.v56", #0
    => br %"iw_1.v57" ? "iw_1.L49" : "iw_1.join" };
  ir_blk{ @"iw_1.L49":
    %"iw_1.v66" : W = (RawLoad (LdNarrow Uh) 0) %"chk15";
    %"iw_1.v67" : W = Copy %"iw_1.v47";
    %"iw_1.v68" : W = (Cmp Ult W) %"iw_1.v66", %"iw_1.v67"
    => br %"iw_1.v68" ? "iw_1.L69" : "iw_1.L70" };
  ir_blk{ @"iw_1.L69":
    %"iw_1.v78" : W = (RawLoad (LdNarrow Uh) 0) %"chk15";
    %"iw_1.v79" : L = (Ext Uw) %"iw_1.v78";
    %"iw_1.v80" = %"iw_1.v19" +p %"iw_1.v79";
    call %"iw_1.v81" : W = $"__GI_strcmp"(P %"v2", P %"iw_1.v80");
    %"iw_1.v82" : W = (Cmp Eq W) %"iw_1.v81", #0
    => goto "iw_1.L70" };
  ir_blk{ @"iw_1.L70" [%"iw_1.v84" : W = phi("iw_1.L49" => #0, "iw_1.L69" => %"iw_1.v82")]:
    => br %"iw_1.v84" ? "iw_1.L58" : "iw_1.L59" };
  ir_blk{ @"iw_1.L58":
    %"iw_1.v91" = %"iw_1.v55" +p #2;
    %"chk18" : A = (HalfCheck Upper 0 2 Read 1) %"chk15", %"iw_1.v91";
    %"iw_1.v92" : W = (RawLoad (LdNarrow Uh) 0) %"chk18";
    %"iw_1.v93" : L = (Ext Uw) %"iw_1.v92"
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L59":
    %"iw_1.v100" : W = Add %"iw_1.pr.1", %"iw_1.v40";
    %"iw_1.v102" = %"iw_1.v12" +p #8;
    %"chk19" : A = (Renew 0 2 Read 1) %"chk11", %"iw_1.v102";
    %"iw_1.v103" : W = (RawLoad (LdNarrow Uh) 0) %"chk19";
    %"iw_1.v104" : W = (Cmp Uge W) %"iw_1.v100", %"iw_1.v103"
    => br %"iw_1.v104" ? "iw_1.L95" : poll "iw_1.L48" };
  ir_blk{ @"iw_1.L95":
    %"iw_1.v107" = %"iw_1.v12" +p #8;
    %"iw_1.v108" : W = (RawLoad (LdNarrow Uh) 0) %"chk19";
    %"iw_1.v109" : W = Sub %"iw_1.v100", %"iw_1.v108"
    => goto poll "iw_1.L48" };
  ir_blk{ @"iw_1.join" [%"v47" : W = phi("iw_1.L58" => #0, "iw_1.L48" => #4294967295); %"pr.1" : L = phi("iw_1.L58" => %"iw_1.v93", "iw_1.L48" => #0)]:
    %"v48" : W = (Cmp Ne W) %"v47", #0
    => br %"v48" ? "L50" : "L49" };
  ir_blk{ @"L49":
    %"v52" = %"v28" +p #10;
    %"chk21" : A = (Renew 0 2 Read 1) %"chk5", %"v52";
    %"v53" : W = (RawLoad (LdNarrow Uh) 0) %"chk21";
    %"v55" : L = Add %"pr.1", #1;
    %"v56" : L = Mul %"v55", #12;
    %"v57" : L = (Ext Uw) %"v53";
    %"v58" : L = Add %"v57", %"v56";
    %"v59" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk22" : A = (Check 0 8 Read 1) %"v59";
    %"v60" : L = (RawLoad LdL 0) %"chk22";
    %"v61" : W = (Cmp Ugt L) %"v58", %"v60"
    => goto "L50" };
  ir_blk{ @"L50" [%"v63" : W = phi("iw_1.join" => #1, "L49" => %"v61")]:
    => br %"v63" ? "L43" : "L45" };
  ir_blk{ @"L43":
    => ret #1 };
  ir_blk{ @"L45":
    %"v67" : L = Mul %"pr.1", #12;
    %"v68" = %"v42" +p %"v67";
    %"iw_2.v11" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk23" : A = (Check 0 8 Read 8) %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"iw_2.v13" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk24" : A = (Check 0 8 Read 8) %"iw_2.v13";
    %"iw_2.v14" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_2.v16" = %"iw_2.v12" +p #4;
    %"chk25" : A = (Check 0 2 Read 1) %"iw_2.v16";
    %"iw_2.v17" : W = (RawLoad (LdNarrow Uh) 0) %"chk25";
    %"iw_2.v18" : L = (Ext Uw) %"iw_2.v17";
    %"iw_2.v19" = %"iw_2.v14" +p %"iw_2.v18";
    %"iw_2.v20" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk26" : A = (Check 0 8 Read 8) %"iw_2.v20";
    %"iw_2.v21" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"iw_2.v23" = %"iw_2.v12" +p #6;
    %"chk27" : A = (HalfCheck Upper 0 2 Read 1) %"chk25", %"iw_2.v23";
    %"iw_2.v24" : W = (RawLoad (LdNarrow Uh) 0) %"chk27";
    %"iw_2.v25" : L = (Ext Uw) %"iw_2.v24";
    %"iw_2.v26" = %"iw_2.v21" +p %"iw_2.v25";
    call %"iw_2.v28" : L = $"__hash_string"(P %"v0");
    %"iw_2.v29" : W = Copy %"iw_2.v28";
    %"iw_2.v31" = %"iw_2.v12" +p #8;
    %"chk28" : A = (HalfCheck Upper 0 2 Read 1) %"chk25", %"iw_2.v31";
    %"iw_2.v32" : W = (RawLoad (LdNarrow Uh) 0) %"chk28";
    %"iw_2.v33" : W = Urem %"iw_2.v29", %"iw_2.v32";
    %"iw_2.v34" : W = Copy %"iw_2.v28";
    %"iw_2.v37" : W = (RawLoad (LdNarrow Uh) 0) %"chk28";
    %"iw_2.v38" : W = Sub %"iw_2.v37", #2;
    %"iw_2.v39" : W = Urem %"iw_2.v34", %"iw_2.v38";
    %"iw_2.v40" : W = Add %"iw_2.v39", #1;
    %"iw_2.v41" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk30" : A = (Check 0 8 Read 1) %"iw_2.v41";
    %"iw_2.v42" : L = (RawLoad LdL 0) %"chk30";
    %"chk31" : A = (Renew 0 2 Read 1) %"chk25", %"iw_2.v16";
    %"iw_2.v45" : W = (RawLoad (LdNarrow Uh) 0) %"chk31";
    %"iw_2.v46" : L = (Ext Uw) %"iw_2.v45";
    %"iw_2.v47" : L = Sub %"iw_2.v42", %"iw_2.v46"
    => goto "iw_2.L48" };
  ir_blk{ @"iw_2.L48" [%"iw_2.pr.1" : W = phi("L45" => %"iw_2.v33", "iw_2.L59" => %"iw_2.v100", "iw_2.L95" => %"iw_2.v109")]:
    %"iw_2.v53" : L = (Ext Uw) %"iw_2.pr.1";
    %"iw_2.v54" : L = Shl %"iw_2.v53", #2;
    %"iw_2.v55" = %"iw_2.v26" +p %"iw_2.v54";
    %"chk32" : A = (Check 0 2 Read 1) %"iw_2.v55";
    %"iw_2.v56" : W = (RawLoad (LdNarrow Uh) 0) %"chk32";
    %"iw_2.v57" : W = (Cmp Ne W) %"iw_2.v56", #0
    => br %"iw_2.v57" ? "iw_2.L49" : "iw_2.join" };
  ir_blk{ @"iw_2.L49":
    %"iw_2.v66" : W = (RawLoad (LdNarrow Uh) 0) %"chk32";
    %"iw_2.v67" : W = Copy %"iw_2.v47";
    %"iw_2.v68" : W = (Cmp Ult W) %"iw_2.v66", %"iw_2.v67"
    => br %"iw_2.v68" ? "iw_2.L69" : "iw_2.L70" };
  ir_blk{ @"iw_2.L69":
    %"iw_2.v78" : W = (RawLoad (LdNarrow Uh) 0) %"chk32";
    %"iw_2.v79" : L = (Ext Uw) %"iw_2.v78";
    %"iw_2.v80" = %"iw_2.v19" +p %"iw_2.v79";
    call %"iw_2.v81" : W = $"__GI_strcmp"(P %"v0", P %"iw_2.v80");
    %"iw_2.v82" : W = (Cmp Eq W) %"iw_2.v81", #0
    => goto "iw_2.L70" };
  ir_blk{ @"iw_2.L70" [%"iw_2.v84" : W = phi("iw_2.L49" => #0, "iw_2.L69" => %"iw_2.v82")]:
    => br %"iw_2.v84" ? "iw_2.L58" : "iw_2.L59" };
  ir_blk{ @"iw_2.L58":
    %"iw_2.v91" = %"iw_2.v55" +p #2;
    %"chk35" : A = (HalfCheck Upper 0 2 Read 1) %"chk32", %"iw_2.v91";
    %"iw_2.v92" : W = (RawLoad (LdNarrow Uh) 0) %"chk35";
    %"iw_2.v93" : L = (Ext Uw) %"iw_2.v92"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.L59":
    %"iw_2.v100" : W = Add %"iw_2.pr.1", %"iw_2.v40";
    %"iw_2.v102" = %"iw_2.v12" +p #8;
    %"chk36" : A = (Renew 0 2 Read 1) %"chk28", %"iw_2.v102";
    %"iw_2.v103" : W = (RawLoad (LdNarrow Uh) 0) %"chk36";
    %"iw_2.v104" : W = (Cmp Uge W) %"iw_2.v100", %"iw_2.v103"
    => br %"iw_2.v104" ? "iw_2.L95" : poll "iw_2.L48" };
  ir_blk{ @"iw_2.L95":
    %"iw_2.v107" = %"iw_2.v12" +p #8;
    %"iw_2.v108" : W = (RawLoad (LdNarrow Uh) 0) %"chk36";
    %"iw_2.v109" : W = Sub %"iw_2.v100", %"iw_2.v108"
    => goto poll "iw_2.L48" };
  ir_blk{ @"iw_2.join" [%"v73" : W = phi("iw_2.L58" => #0, "iw_2.L48" => #4294967295); %"pr.2" : L = phi("iw_2.L58" => %"iw_2.v93", "iw_2.L48" => #0)]:
    %"v74" : W = (Cmp Ne W) %"v73", #0
    => br %"v74" ? "L76" : "L75" };
  ir_blk{ @"L75":
    %"v78" = %"v28" +p #10;
    %"chk38" : A = (Renew 0 2 Read 1) %"chk5", %"v78";
    %"v79" : W = (RawLoad (LdNarrow Uh) 0) %"chk38";
    %"v81" : L = Add %"pr.2", #1;
    %"v82" : L = Mul %"v81", #12;
    %"v83" : L = (Ext Uw) %"v79";
    %"v84" : L = Add %"v83", %"v82";
    %"v85" : P = Copy $"glibc_gconv_cache#cache_size";
    %"chk39" : A = (Check 0 8 Read 1) %"v85";
    %"v86" : L = (RawLoad LdL 0) %"chk39";
    %"v87" : W = (Cmp Ugt L) %"v84", %"v86"
    => goto "L76" };
  ir_blk{ @"L76" [%"v89" : W = phi("iw_2.join" => #1, "L75" => %"v87")]:
    => br %"v89" ? "L69" : "L71" };
  ir_blk{ @"L69":
    => ret #1 };
  ir_blk{ @"L71":
    %"v93" : L = Mul %"pr.2", #12;
    %"v94" = %"v42" +p %"v93";
    %"v99" : W = And %"v8", #1
    => br %"v99" ? "L102" : "L103" };
  ir_blk{ @"L102":
    %"v106" : W = (Cmp Eq L) %"pr.1", %"pr.2"
    => goto "L103" };
  ir_blk{ @"L103" [%"v108" : W = phi("L71" => #0, "L102" => %"v106")]:
    => br %"v108" ? "L95" : "L97" };
  ir_blk{ @"L95":
    => ret #(-1) };
  ir_blk{ @"L97":
    %"v114" : W = (Cmp Ne L) %"pr.1", #0
    => br %"v114" ? "L115" : "L116" };
  ir_blk{ @"L115":
    %"v118" : W = (Cmp Ne L) %"pr.2", #0
    => goto "L116" };
  ir_blk{ @"L116" [%"v120" : W = phi("L97" => #0, "L115" => %"v118")]:
    => br %"v120" ? "L121" : "L122" };
  ir_blk{ @"L121":
    %"v124" = %"v68" +p #10;
    %"chk40" : A = (Check 0 2 Read 1) %"v124";
    %"v125" : W = (RawLoad (LdNarrow Uh) 0) %"chk40";
    %"v126" : L = (Ext Uw) %"v125";
    %"v127" : W = (Cmp Ne L) %"v126", #0
    => goto "L122" };
  ir_blk{ @"L122" [%"v129" : W = phi("L116" => #0, "L121" => %"v127")]:
    => br %"v129" ? "L110" : "L299" };
  ir_blk{ @"L110":
    %"v131" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk41" : A = (Check 0 8 Read 8) %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v134" = %"v28" +p #12;
    %"chk42" : A = (HalfCheck Upper 0 2 Read 1) %"chk3", %"v134";
    %"v135" : W = (RawLoad (LdNarrow Uh) 0) %"chk42";
    %"v136" : L = (Ext Uw) %"v135";
    %"v137" = %"v132" +p %"v136";
    %"v139" = %"v68" +p #10;
    %"chk43" : A = (Check 0 2 Read 1) %"v139";
    %"v140" : W = (RawLoad (LdNarrow Uh) 0) %"chk43";
    %"v141" : L = (Ext Uw) %"v140";
    %"v142" = %"v137" +p %"v141";
    (Flight (a "v143") Sub [(FAddress (t "v142")); (FValue (Const 1))] (LowerOf (t "v142")))
    => goto "L144" };
  ir_blk{ @"L144" [%"pr.3" : P = phi("L110" => %"v143", "L145" => %"v172")]:
    %"chk44" : A = (Check 0 2 Read 1) %"pr.3";
    %"v148" : W = (RawLoad (LdNarrow Uh) 0) %"chk44";
    %"v149" : W = (Cmp Ne W) %"v148", #0
    => br %"v149" ? "L150" : "L151" };
  ir_blk{ @"L150":
    %"v153" = %"pr.3" +p #2;
    %"v155" : W = (RawLoad (LdNarrow Uh) 0) %"chk44";
    %"v156" : W = Sub %"v155", #1;
    %"v157" : L = (Ext Sw) %"v156";
    %"v158" : L = Mul %"v157", #6;
    %"v159" = %"v153" +p %"v158";
    %"chk46" : A = (Check 0 2 Read 1) %"v159";
    %"v160" : W = (RawLoad (LdNarrow Uh) 0) %"chk46";
    %"v162" : L = (Ext Uw) %"v160";
    %"v163" : W = (Cmp Ne L) %"v162", %"pr.2"
    => goto "L151" }] [ir_blk{ @"L151" [%"v165" : W = phi("L144" => #0, "L150" => %"v163")]:
    => br %"v165" ? "L145" : "L146" };
  ir_blk{ @"L145":
    %"v167" = %"pr.3" +p #2;
    %"v169" : W = (RawLoad (LdNarrow Uh) 0) %"chk44";
    %"v170" : L = (Ext Uw) %"v169";
    %"v171" : L = Mul %"v170", #6;
    %"v172" = %"v167" +p %"v171"
    => goto poll "L144" };
  ir_blk{ @"L146":
    %"v177" : W = (RawLoad (LdNarrow Uh) 0) %"chk44";
    %"v178" : W = (Cmp Ne W) %"v177", #0
    => br %"v178" ? "L173" : "L299" };
  ir_blk{ @"L173":
    %"v183" : W = (RawLoad (LdNarrow Uh) 0) %"chk44";
    %"v184" : L = (Ext Uw) %"v183";
    %"chk50" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk50" + 0] <- %"v184";
    %"v187" : W = (RawLoad (LdNarrow Uh) 0) %"chk44";
    %"v188" : L = (Ext Uw) %"v187";
    %"v189" : L = Mul %"v188", #104;
    call %"v190" : P = $"malloc"(L %"v189");
    %"chk52" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk52" + 0] <- %"v190";
    %"v195" : L = Ptoi %"v190";
    %"v197" : W = (Cmp Eq L) %"v195", %"v24"
    => br %"v197" ? "L191" : "L193" };
  ir_blk{ @"L191":
    => ret #3 };
  ir_blk{ @"L193":
    %"chk53" : A = (HalfCheck Lower 0 2 Read 1) %"chk43", %"v68";
    %"v201" : W = (RawLoad (LdNarrow Uh) 0) %"chk53";
    %"v202" : L = (Ext Uw) %"v201";
    %"v203" = %"v35" +p %"v202"
    => goto "L204" };
  ir_blk{ @"L204" [%"pr.5" : W = phi("L193" => #0, "L205" => %"v318"); %"pr.4" : P = phi("L193" => %"v203", "L205" => %"v234")]:
    %"v209" : L = (Ext Sw) %"pr.5";
    %"v210" : L = Mul %"v209", #104;
    %"v211" = %"v190" +p %"v210";
    %"v212" = %"v211" +p #24;
    %"chk54" : A = (Check 0 8 Write 8) %"v212";
    store.ptr [%"chk54" + 0] <- %"pr.4";
    %"v219" = %"v211" +p #32;
    %"v223" = %"pr.3" +p #2;
    %"v226" : L = Mul %"v209", #6;
    %"v227" = %"v223" +p %"v226";
    %"chk55" : A = (Check 0 2 Read 1) %"v227";
    %"v228" : W = (RawLoad (LdNarrow Uh) 0) %"chk55";
    %"v229" : L = (Ext Uw) %"v228";
    %"v230" : L = Mul %"v229", #12;
    %"v231" = %"v42" +p %"v230";
    %"chk56" : A = (Check 0 2 Read 1) %"v231";
    %"v232" : W = (RawLoad (LdNarrow Uh) 0) %"chk56";
    %"v233" : L = (Ext Uw) %"v232";
    %"v234" = %"v35" +p %"v233";
    %"chk57" : A = (HalfCheck Upper 0 8 Write 8) %"chk54", %"v219";
    store.ptr [%"chk57" + 0] <- %"v234";
    %"v240" = %"v211" +p #16;
    %"chk58" : A = (HalfCheck Lower 0 4 Write 1) %"chk54", %"v240";
    store Ww [%"chk58" + 0] <- #1;
    %"v246" = %"v211" +p #96;
    %"chk59" : A = (HalfCheck Upper 0 8 Write 8) %"chk54", %"v246";
    store.ptr [%"chk59" + 0] <- #0;
    %"v257" = %"v227" +p #2;
    %"chk60" : A = (HalfCheck Upper 0 2 Read 1) %"chk55", %"v257";
    %"v258" : W = (RawLoad (LdNarrow Uh) 0) %"chk60";
    %"v259" : L = (Ext Uw) %"v258";
    %"v260" = %"v35" +p %"v259";
    %"chk61" : A = (Check 0 1 Read 1) %"v260";
    %"v261" : W = (RawLoad (LdNarrow Sb) 0) %"chk61";
    %"v262" : W = (Cmp Ne W) %"v261", #0
    => br %"v262" ? "L247" : "L248" };
  ir_blk{ @"L247":
    %"v266" = %"pr.3" +p #2;
    %"v270" = %"v266" +p %"v226";
    %"v271" = %"v270" +p #2;
    %"chk62" : A = (Check 0 2 Read 1) %"v271";
    %"v272" : W = (RawLoad (LdNarrow Uh) 0) %"chk62";
    %"v273" : L = (Ext Uw) %"v272";
    %"v274" = %"v35" +p %"v273";
    %"v282" = %"v270" +p #4;
    %"chk63" : A = (HalfCheck Upper 0 2 Read 1) %"chk62", %"v282";
    %"v283" : W = (RawLoad (LdNarrow Uh) 0) %"chk63";
    %"v284" : L = (Ext Uw) %"v283";
    %"v285" = %"v35" +p %"v284";
    call %"v291" : W = $"glibc_gconv_cache#find_module"(P %"v274", P %"v285", P %"v211");
    %"v296" : L = (Ext Sw) %"v291";
    %"v297" : W = (Cmp Ne L) %"v296", #0
    => br %"v297" ? "L292" : "L205" };
  ir_blk{ @"L292":
    call void $"free"(P %"v190")
    => goto "L299" };
  ir_blk{ @"L248":
    %"v303" = %"pr.3" +p #2;
    %"v307" = %"v303" +p %"v226";
    %"v308" = %"v307" +p #4;
    %"chk64" : A = (Check 0 2 Read 1) %"v308";
    %"v309" : W = (RawLoad (LdNarrow Uh) 0) %"chk64";
    %"v310" : L = (Ext Uw) %"v309";
    %"v311" = %"v35" +p %"v310";
    call void $"__gconv_get_builtin_trans"(P %"v311", P %"v211")
    => goto "L205" };
  ir_blk{ @"L205":
    %"v318" : W = Add %"pr.5", #1;
    %"chk65" : A = (Renew 0 2 Read 1) %"chk44", %"pr.3";
    %"v320" : W = (RawLoad (LdNarrow Uh) 0) %"chk65";
    %"v321" : W = (Cmp Slt W) %"v318", %"v320"
    => br %"v321" ? poll "L204" : "L206" };
  ir_blk{ @"L206":
    => ret #0 };
  ir_blk{ @"L299":
    => br %"v114" ? "L328" : "L329" };
  ir_blk{ @"L328":
    %"v331" = %"v68" +p #4;
    %"chk66" : A = (Check 0 2 Read 1) %"v331";
    %"v332" : W = (RawLoad (LdNarrow Uh) 0) %"chk66";
    %"v333" : L = (Ext Uw) %"v332";
    %"v334" : W = (Cmp Eq L) %"v333", #0
    => goto "L329" };
  ir_blk{ @"L329" [%"v336" : W = phi("L299" => #0, "L328" => %"v334")]:
    => br %"v336" ? "L338" : "L337" };
  ir_blk{ @"L337":
    %"v340" : W = (Cmp Ne L) %"pr.2", #0
    => br %"v340" ? "L341" : "L338" };
  ir_blk{ @"L341":
    %"v344" = %"v94" +p #8;
    %"chk67" : A = (Check 0 2 Read 1) %"v344";
    %"v345" : W = (RawLoad (LdNarrow Uh) 0) %"chk67";
    %"v346" : L = (Ext Uw) %"v345";
    %"v347" : W = (Cmp Eq L) %"v346", #0
    => goto "L338" };
  ir_blk{ @"L338" [%"v351" : W = phi("L329" => #1, "L337" => #0, "L341" => %"v347")]:
    => br %"v351" ? "L353" : "L352" };
  ir_blk{ @"L352":
    %"v355" : W = (Cmp Eq L) %"pr.1", #0
    => br %"v355" ? "L356" : "L353" };
  ir_blk{ @"L356":
    %"v359" : W = (Cmp Eq L) %"pr.2", #0
    => goto "L353" };
  ir_blk{ @"L353" [%"v363" : W = phi("L338" => #1, "L352" => #0, "L356" => %"v359")]:
    => br %"v363" ? "L323" : "L325" };
  ir_blk{ @"L323":
    => ret #1 };
  ir_blk{ @"L325":
    call %"v366" : P = $"malloc"(L #208);
    %"v371" : L = Ptoi %"v366";
    %"v373" : W = (Cmp Eq L) %"v371", %"v24"
    => br %"v373" ? "L367" : "L369" };
  ir_blk{ @"L367":
    => ret #3 };
  ir_blk{ @"L369":
    %"chk68" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk68" + 0] <- %"v366";
    %"chk69" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk69" + 0] <- #0
    => br %"v114" ? "L378" : "L380" };
  ir_blk{ @"L378":
    %"v385" = %"v366" +p #24;
    %"chk70" : A = (Check 0 2 Read 1) %"v68";
    %"v388" : W = (RawLoad (LdNarrow Uh) 0) %"chk70";
    %"v389" : L = (Ext Uw) %"v388";
    %"v390" = %"v35" +p %"v389";
    %"chk71" : A = (Check 0 8 Write 8) %"v385";
    store.ptr [%"chk71" + 0] <- %"v390";
    %"v393" = %"v366" +p #32;
    %"v394" : P = Copy $"glibc_gconv_cache#str.284";
    %"chk72" : A = (HalfCheck Upper 0 8 Write 8) %"chk71", %"v393";
    store.ptr [%"chk72" + 0] <- %"v394";
    %"v397" = %"v366" +p #16;
    %"chk73" : A = (HalfCheck Lower 0 4 Write 1) %"chk71", %"v397";
    store Ww [%"chk73" + 0] <- #1;
    %"v400" = %"v366" +p #96;
    %"chk74" : A = (HalfCheck Upper 0 8 Write 8) %"chk71", %"v400";
    store.ptr [%"chk74" + 0] <- #0;
    %"v406" = %"v68" +p #6;
    %"chk75" : A = (HalfCheck Upper 0 2 Read 1) %"chk70", %"v406";
    %"v407" : W = (RawLoad (LdNarrow Uh) 0) %"chk75";
    %"v408" : L = (Ext Uw) %"v407";
    %"v409" = %"v35" +p %"v408";
    %"chk76" : A = (Check 0 1 Read 1) %"v409";
    %"v410" : W = (RawLoad (LdNarrow Sb) 0) %"chk76";
    %"v411" : W = (Cmp Ne W) %"v410", #0
    => br %"v411" ? "L401" : "L402" };
  ir_blk{ @"L401":
    %"v415" = %"v68" +p #6;
    %"v416" : W = (RawLoad (LdNarrow Uh) 0) %"chk75";
    %"v417" : L = (Ext Uw) %"v416";
    %"v418" = %"v35" +p %"v417";
    %"v421" = %"v68" +p #8;
    %"chk78" : A = (HalfCheck Upper 0 2 Read 1) %"chk70", %"v421";
    %"v422" : W = (RawLoad (LdNarrow Uh) 0) %"chk78";
    %"v423" : L = (Ext Uw) %"v422";
    %"v424" = %"v35" +p %"v423";
    call %"v427" : W = $"glibc_gconv_cache#find_module"(P %"v418", P %"v424", P %"v366");
    %"v432" : L = (Ext Sw) %"v427";
    %"v433" : W = (Cmp Ne L) %"v432", #0
    => br %"v433" ? "L428" : "L403" };
  ir_blk{ @"L428":
    call void $"free"(P %"v366")
    => ret %"v427" };
  ir_blk{ @"L402":
    %"v439" = %"v68" +p #8;
    %"chk79" : A = (HalfCheck Upper 0 2 Read 1) %"chk70", %"v439";
    %"v440" : W = (RawLoad (LdNarrow Uh) 0) %"chk79";
    %"v441" : L = (Ext Uw) %"v440";
    %"v442" = %"v35" +p %"v441";
    call void $"__gconv_get_builtin_trans"(P %"v442", P %"v366")
    => goto "L403" };
  ir_blk{ @"L403":
    %"chk80" : A = (Renew 0 8 Read 1) %"chk69", %"v6";
    %"v446" : L = (RawLoad LdL 0) %"chk80";
    %"v447" : L = Add %"v446", #1;
    %"chk81" : A = (Renew 0 8 Write 1) %"chk69", %"v6";
    store Wl [%"chk81" + 0] <- %"v447"
    => goto "L380" };
  ir_blk{ @"L380":
    %"v452" : W = (Cmp Ne L) %"pr.2", #0
    => br %"v452" ? "L448" : "L450" };
  ir_blk{ @"L448":
    %"chk82" : A = (Renew 0 8 Read 1) %"chk69", %"v6";
    %"v455" : L = (RawLoad LdL 0) %"chk82";
    %"v457" : W = Copy %"v455";
    %"v458" : L = (Ext Sw) %"v457";
    %"v459" : L = Mul %"v458", #104;
    %"v460" = %"v366" +p %"v459";
    %"v461" = %"v460" +p #24;
    %"v462" : P = Copy $"glibc_gconv_cache#str.284";
    %"chk83" : A = (Check 0 8 Write 8) %"v461";
    store.ptr [%"chk83" + 0] <- %"v462";
    %"v464" : W = Copy %"v455";
    %"v465" : L = (Ext Sw) %"v464";
    %"v466" : L = Mul %"v465", #104;
    %"v467" = %"v366" +p %"v466";
    %"v468" = %"v467" +p #32;
    %"chk84" : A = (Check 0 2 Read 1) %"v94";
    %"v471" : W = (RawLoad (LdNarrow Uh) 0) %"chk84";
    %"v472" : L = (Ext Uw) %"v471";
    %"v473" = %"v35" +p %"v472";
    %"chk85" : A = (Check 0 8 Write 8) %"v468";
    store.ptr [%"chk85" + 0] <- %"v473";
    %"v475" : W = Copy %"v455";
    %"v476" : L = (Ext Sw) %"v475";
    %"v477" : L = Mul %"v476", #104;
    %"v478" = %"v366" +p %"v477";
    %"v479" = %"v478" +p #16;
    %"chk86" : A = (Check 0 4 Write 1) %"v479";
    store Ww [%"chk86" + 0] <- #1;
    %"v481" : W = Copy %"v455";
    %"v482" : L = (Ext Sw) %"v481";
    %"v483" : L = Mul %"v482", #104;
    %"v484" = %"v366" +p %"v483";
    %"v485" = %"v484" +p #96;
    %"chk87" : A = (Check 0 8 Write 8) %"v485";
    store.ptr [%"chk87" + 0] <- #0;
    %"v491" = %"v94" +p #2;
    %"chk88" : A = (HalfCheck Upper 0 2 Read 1) %"chk84", %"v491";
    %"v492" : W = (RawLoad (LdNarrow Uh) 0) %"chk88";
    %"v493" : L = (Ext Uw) %"v492";
    %"v494" = %"v35" +p %"v493";
    %"chk89" : A = (Check 0 1 Read 1) %"v494";
    %"v495" : W = (RawLoad (LdNarrow Sb) 0) %"chk89";
    %"v496" : W = (Cmp Ne W) %"v495", #0
    => br %"v496" ? "L486" : "L487" };
  ir_blk{ @"L486":
    %"v500" = %"v94" +p #2;
    %"v501" : W = (RawLoad (LdNarrow Uh) 0) %"chk88";
    %"v502" : L = (Ext Uw) %"v501";
    %"v503" = %"v35" +p %"v502";
    %"v506" = %"v94" +p #4;
    %"chk91" : A = (HalfCheck Upper 0 2 Read 1) %"chk84", %"v506";
    %"v507" : W = (RawLoad (LdNarrow Uh) 0) %"chk91";
    %"v508" : L = (Ext Uw) %"v507";
    %"v509" = %"v35" +p %"v508";
    %"v511" : W = Copy %"v455";
    %"v512" : L = (Ext Sw) %"v511";
    %"v513" : L = Mul %"v512", #104;
    %"v514" = %"v366" +p %"v513";
    call %"v515" : W = $"glibc_gconv_cache#find_module"(P %"v503", P %"v509", P %"v514");
    %"v520" : L = (Ext Sw) %"v515";
    %"v521" : W = (Cmp Ne L) %"v520", #0
    => br %"v521" ? "L516" : "L488" };
  ir_blk{ @"L516":
    %"v525" : W = Copy %"v455";
    %"v526" : W = (Cmp Ne W) %"v525", #0
    => br %"v526" ? "L522" : "L524" };
  ir_blk{ @"L522":
    call void $"__gconv_release_step"(P %"v366")
    => goto "L524" };
  ir_blk{ @"L524":
    call void $"free"(P %"v366")
    => ret %"v515" };
  ir_blk{ @"L487":
    %"v534" = %"v94" +p #4;
    %"chk92" : A = (HalfCheck Upper 0 2 Read 1) %"chk84", %"v534";
    %"v535" : W = (RawLoad (LdNarrow Uh) 0) %"chk92";
    %"v536" : L = (Ext Uw) %"v535";
    %"v537" = %"v35" +p %"v536";
    %"v539" : W = Copy %"v455";
    %"v540" : L = (Ext Sw) %"v539";
    %"v541" : L = Mul %"v540", #104;
    %"v542" = %"v366" +p %"v541";
    call void $"__gconv_get_builtin_trans"(P %"v537", P %"v542")
    => goto "L488" };
  ir_blk{ @"L488":
    %"chk93" : A = (Renew 0 8 Read 1) %"chk69", %"v6";
    %"v544" : L = (RawLoad LdL 0) %"chk93";
    %"v545" : L = Add %"v544", #1;
    %"chk94" : A = (Renew 0 8 Write 1) %"chk69", %"v6";
    store Wl [%"chk94" + 0] <- %"v545"
    => goto "L450" };
  ir_blk{ @"L450":
    => ret #0 }])) }.

Definition hello_image_fn___gconv_release_cache : func :=
  ir_fn{ "export" "__gconv_release_cache"(P %"v0", L %"v2") -> RVoid {
  @"start":
    %"v7" : P = Copy $"glibc_gconv_cache#gconv_cache";
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" : L = Ptoi %"v8";
    %"v10" : L = Ptoi #0;
    %"v11" : W = (Cmp Ne L) %"v9", %"v10"
    => br %"v11" ? "L4" : "L6";
  @"L4":
    call void $"free"(P %"v0")
    => goto "L6";
  @"L6":
    => ret void
} }.

Definition hello_image_fn_glibc_gconv_charset'23gconv_parse_code : func :=
  ir_fn{ "local" "glibc_gconv_charset#gconv_parse_code"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #8;
    %"chk0" : A = (Check 0 1 Write 1) %"v3";
    store Wb [%"chk0" + 0] <- #0;
    %"v6" = %"v0" +p #9;
    %"chk1" : A = (HalfCheck Upper 0 1 Write 1) %"chk0", %"v6";
    store Wb [%"chk1" + 0] <- #0
    => goto "L9";
  @"L9":
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v14" : L = $"__GI_strlen"(P %"v13")
    => goto "L15";
  @"L15" [%"pr.1" : L = phi("L16" => %"v60", "L9" => %"v14")]:
    %"v19" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v19" ? "iw_1.start" : "L21";
  @"iw_1.start":
    %"iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v0";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" : L = Sub %"pr.1", #1;
    %"v28" = %"v25" +p %"v27";
    %"chk5" : A = (Check 0 1 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v30" : L = (Ext Sw) %"v29";
    %"v31" : L = Shl %"v30", #1;
    %"v32" = %"v23" +p %"v31";
    %"chk6" : A = (Check 0 2 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Uh) 0) %"chk6";
    %"v34" : W = And %"v33", #8192
    => br %"v34" ? "L36" : "L35";
  @"L35":
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v41" = %"v38" +p %"v27";
    %"chk8" : A = (Check 0 1 Read 1) %"v41";
    %"v42" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v43" : W = (Cmp Eq W) %"v42", #44
    => goto "L36";
  @"L36" [%"v45" : W = phi("iw_1.start" => #1, "L35" => %"v43")]:
    => br %"v45" ? "L21" : "L46";
  @"L46":
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v52" = %"v49" +p %"v27";
    %"chk10" : A = (Check 0 1 Read 1) %"v52";
    %"v53" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v54" : W = (Cmp Eq W) %"v53", #47
    => goto "L21";
  @"L21" [%"v58" : W = phi("L15" => #0, "L36" => #1, "L46" => %"v54")]:
    => br %"v58" ? "L16" : "L17";
  @"L16":
    %"v60" : L = Sub %"pr.1", #1
    => goto poll "L15";
  @"L17":
    %"chk11" : A = (Renew 0 8 Read 8) %"chk2", %"v0";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v64" = %"v62" +p %"pr.1";
    %"chk12" : A = (Check 0 1 Write 1) %"v64";
    store Wb [%"chk12" + 0] <- #0;
    %"v69" : W = (Cmp Eq L) %"pr.1", #0
    => br %"v69" ? "L65" : "L67";
  @"L65":
    => ret void;
  @"L67":
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "iw_2.L5";
  @"iw_2.L5" [%"iw_2.pr.6" : W = phi("iw_2.L21" => %"iw_2.v35", "L67" => #0); %"iw_2.pr.5" : P = phi("iw_2.L21" => %"iw_2.pr.4", "L67" => #0); %"iw_2.pr.3" : W = phi("iw_2.L21" => %"iw_2.pr.1", "L67" => #0)]:
    %"iw_2.v11" : L = (Ext Sw) %"iw_2.pr.6";
    %"iw_2.v12" = %"v73" +p %"iw_2.v11";
    %"chk14" : A = (Check 0 1 Read 1) %"iw_2.v12";
    %"iw_2.v13" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.v14" : W = (Cmp Ne W) %"iw_2.v13", #0
    => br %"iw_2.v14" ? "iw_2.L6" : "iw_2.L8";
  @"iw_2.L6":
    %"iw_2.v19" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.v30" : W = (Cmp Eq W) %"iw_2.v19", #47
    => br %"iw_2.v30" ? "iw_2.L22" : "iw_2.L31";
  @"iw_2.L22":
    %"iw_2.v24" : W = Add %"iw_2.pr.3", #1
    => goto "iw_2.L21";
  @"iw_2.L31":
    %"iw_2.v32" : W = (Cmp Eq W) %"iw_2.v19", #44
    => br %"iw_2.v32" ? "iw_2.L21" : "iw_2.L33";
  @"iw_2.L33":
    => goto "iw_2.L21";
  @"iw_2.L21" [%"iw_2.pr.4" : P = phi("iw_2.L33" => %"iw_2.pr.5", "iw_2.L22" => %"iw_2.v12", "iw_2.L31" => %"iw_2.v12"); %"iw_2.pr.1" : W = phi("iw_2.L33" => %"iw_2.pr.3", "iw_2.L22" => %"iw_2.v24", "iw_2.L31" => %"iw_2.pr.3")]:
    %"iw_2.v35" : W = Add %"iw_2.pr.6", #1
    => goto poll "iw_2.L5";
  @"iw_2.L8":
    %"iw_2.v40" : W = (Cmp Sge W) %"iw_2.pr.3", #2
    => br %"iw_2.v40" ? "iw_2.join" : "iw_2.L38";
  @"iw_2.L38":
    => goto "iw_2.join";
  @"iw_2.join" [%"v74" : P = phi("iw_2.L38" => #0, "iw_2.L8" => %"iw_2.pr.5")]:
    %"v79" : L = Ptoi %"v74";
    %"v80" : L = Ptoi #0;
    %"v81" : W = (Cmp Eq L) %"v79", %"v80"
    => br %"v81" ? "L75" : "L76";
  @"L75":
    => ret void;
  @"L76":
    %"v87" : P = Copy $"glibc_gconv_charset#str.244";
    %"v88" : P = Copy $"_nl_C_locobj";
    call %"v89" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v87", P %"v88");
    %"v90" : W = (Cmp Eq W) %"v89", #0
    => br %"v90" ? "L92" : "L91";
  @"L91":
    %"v94" : P = Copy $"glibc_gconv_charset#str.245";
    %"v95" : P = Copy $"_nl_C_locobj";
    call %"v96" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v94", P %"v95");
    %"v97" : W = (Cmp Eq W) %"v96", #0
    => goto "L92";
  @"L92" [%"v99" : W = phi("L76" => #1, "L91" => %"v97")]:
    => br %"v99" ? "L83" : "L85";
  @"L83":
    %"v101" = %"v0" +p #8;
    %"chk16" : A = (Renew 0 1 Write 1) %"chk0", %"v101";
    store Wb [%"chk16" + 0] <- #1
    => goto "L85";
  @"L85":
    %"v107" : P = Copy $"glibc_gconv_charset#str.246";
    %"v108" : P = Copy $"_nl_C_locobj";
    call %"v109" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v107", P %"v108");
    %"v110" : W = (Cmp Eq W) %"v109", #0
    => br %"v110" ? "L112" : "L111";
  @"L111":
    %"v114" : P = Copy $"glibc_gconv_charset#str.247";
    %"v115" : P = Copy $"_nl_C_locobj";
    call %"v116" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v114", P %"v115");
    %"v117" : W = (Cmp Eq W) %"v116", #0
    => goto "L112";
  @"L112" [%"v119" : W = phi("L85" => #1, "L111" => %"v117")]:
    => br %"v119" ? "L103" : "L105";
  @"L103":
    %"v121" = %"v0" +p #9;
    %"chk17" : A = (Renew 0 1 Write 1) %"chk1", %"v121";
    store Wb [%"chk17" + 0] <- #1
    => goto "L105";
  @"L105":
    %"chk18" : A = (Check 0 1 Write 1) %"v74";
    store Wb [%"chk18" + 0] <- #0
    => goto poll "L9"
} }.

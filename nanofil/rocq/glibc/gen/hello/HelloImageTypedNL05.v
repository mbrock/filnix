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

Definition hello_image_fn__nl_load_locale_from_archive : func :=
  ir_fn{ "export" "_nl_load_locale_from_archive"(W %"v0", P %"v2") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v7" : P = (Alloc 8) #208;
    alloca "v17" 288;
    alloca "v819" 144;
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v21" : L = $"__GI___sysconf"(W #30);
    %"v24" : P = Copy $"glibc_loadarchive#archloaded";
    %"chk1" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L26" };
  ir_blk{ @"L26" [%"pr.3" : P = phi("L28" => %"v67", "start" => %"v25")]:
    %"v31" : L = Ptoi %"pr.3";
    %"v32" : L = Ptoi #0;
    %"v33" : W = (Cmp Ne L) %"v31", %"v32"
    => br %"v33" ? "L27" : "L29" };
  ir_blk{ @"L27":
    %"v39" = %"pr.3" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v41" : L = Ptoi %"v6";
    %"v42" : L = Ptoi %"v40";
    %"v43" : W = (Cmp Eq L) %"v41", %"v42"
    => br %"v43" ? "L45" : "L44" };
  ir_blk{ @"L44":
    %"v48" = %"pr.3" +p #8;
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v50" : W = $"__GI_strcmp"(P %"v6", P %"v49");
    %"v51" : W = (Cmp Eq W) %"v50", #0
    => goto "L45" };
  ir_blk{ @"L45" [%"v53" : W = phi("L27" => #1, "L44" => %"v51")]:
    => br %"v53" ? "L34" : "L28" };
  ir_blk{ @"L34":
    %"v56" = %"pr.3" +p #8;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Renew 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk5" + 0] <- %"v57";
    %"v59" = %"pr.3" +p #16;
    %"v61" : L = (Ext Sw) %"v0";
    %"v62" : L = Shl %"v61", #3;
    %"v63" = %"v59" +p %"v62";
    %"chk6" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk6"
    => ret %"v64" };
  ir_blk{ @"L28":
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"pr.3";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk7"
    => goto poll "L26" };
  ir_blk{ @"L29":
    call %"v70" : P = $"__GI_strchr"(P %"v6", W #46);
    %"v75" : L = Ptoi %"v70";
    %"v77" : W = (Cmp Ne L) %"v75", %"v32"
    => br %"v77" ? "L78" : "L79" };
  ir_blk{ @"L78":
    %"v81" = %"v70" +p #1;
    %"chk8" : A = (Check 0 1 Read 1) %"v81";
    %"v82" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v83" : W = (Cmp Ne W) %"v82", #64
    => goto "L79" };
  ir_blk{ @"L79" [%"v85" : W = phi("L29" => #0, "L78" => %"v83")]:
    => br %"v85" ? "L86" : "L87" };
  ir_blk{ @"L86":
    %"v89" = %"v70" +p #1;
    %"chk9" : A = (Check 0 1 Read 1) %"v89";
    %"v90" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v91" : W = (Cmp Ne W) %"v90", #0
    => goto "L87" };
  ir_blk{ @"L87" [%"v93" : W = phi("L79" => #0, "L86" => %"v91")]:
    => br %"v93" ? "L71" : "L73" };
  ir_blk{ @"L71":
    %"v96" = %"v70" +p #1;
    call %"v97" : P = $"__GI___strchrnul"(P %"v96", W #64);
    %"v102" : L = Ptoi %"v97";
    %"v103" : L = Ptoi %"v96";
    %"v104" : L = Sub %"v102", %"v103";
    call %"v105" : P = $"_nl_normalize_codeset"(P %"v96", L %"v104");
    %"v110" : L = Ptoi %"v105";
    %"v112" : W = (Cmp Eq L) %"v110", %"v32"
    => br %"v112" ? "L106" : "L108" };
  ir_blk{ @"L106":
    => ret #0 };
  ir_blk{ @"L108":
    call %"v124" : W = $"__GI_strncmp"(P %"v105", P %"v96", L %"v104");
    %"v125" : W = (Cmp Ne W) %"v124", #0
    => br %"v125" ? "L127" : "L126" };
  ir_blk{ @"L126":
    %"v134" = %"v105" +p %"v104";
    %"chk10" : A = (Check 0 1 Read 1) %"v134";
    %"v135" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v136" : W = (Cmp Ne W) %"v135", #0
    => goto "L127" };
  ir_blk{ @"L127" [%"v138" : W = phi("L108" => #1, "L126" => %"v136")]:
    => br %"v138" ? "L114" : "L116" };
  ir_blk{ @"L114":
    call %"v141" : L = $"__GI_strlen"(P %"v105");
    call %"v144" : L = $"__GI_strlen"(P %"v97");
    %"v145" : L = Add %"v144", #1;
    %"v150" : L = Ptoi %"v6";
    %"v151" : L = Sub %"v103", %"v150";
    %"v153" : L = Add %"v151", %"v141";
    %"v155" : L = Add %"v153", %"v145";
    %"v156" : P = (Alloc 16) %"v155";
    call %"v164" : P = $"__GI_mempcpy"(P %"v156", P %"v6", L %"v151");
    call %"v167" : P = $"__GI_mempcpy"(P %"v164", P %"v105", L %"v141");
    call %"v170" : P = $"__GI_memcpy"(P %"v167", P %"v97", L %"v145")
    => goto "L116" };
  ir_blk{ @"L116" [%"pr.1" : P = phi("L114" => %"v156", "L127" => %"v6")]:
    call void $"free"(P %"v105")
    => goto "L73" };
  ir_blk{ @"L73" [%"pr.2" : P = phi("L116" => %"pr.1", "L87" => %"v6")]:
    %"v176" : P = Copy $"glibc_loadarchive#archmapped";
    %"chk11" : A = (Check 0 8 Read 8) %"v176";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v178" : L = Ptoi %"v177";
    %"v180" : W = (Cmp Eq L) %"v178", %"v32"
    => br %"v180" ? "L173" : "L175" };
  ir_blk{ @"L173":
    %"v184" : P = Copy $"glibc_loadarchive#archmapped";
    %"v185" : P = Copy $"glibc_loadarchive#headmap";
    %"chk12" : A = (Check 0 8 Write 8) %"v184";
    store.ptr [%"chk12" + 0] <- %"v185";
    %"iw_1.v3" : P = Copy $"glibc_loadarchive#str.249";
    call %"iw_1.v4" : P = $"secure_getenv"(P %"iw_1.v3");
    %"iw_1.v6" : P = Copy $"glibc_loadarchive#str.250";
    call %"iw_1.v7" : P = $"secure_getenv"(P %"iw_1.v6");
    %"iw_1.v12" : L = Ptoi %"iw_1.v4";
    %"iw_1.v13" : W = (Cmp Ne L) %"iw_1.v12", #0
    => br %"iw_1.v13" ? "iw_1.L8" : "iw_1.L10" };
  ir_blk{ @"iw_1.L8":
    call %"iw_1.v17" : W = $"__GI___open_nocancel"(P %"iw_1.v4", W #524288)
    => goto "iw_1.L10" };
  ir_blk{ @"iw_1.L10" [%"iw_1.pr.1" : W = phi("iw_1.L8" => %"iw_1.v17", "L173" => #4294967295)]:
    %"iw_1.v22" : L = Ptoi %"iw_1.v7";
    %"iw_1.v23" : W = (Cmp Ne L) %"iw_1.v22", #0
    => br %"iw_1.v23" ? "iw_1.L24" : "iw_1.L25" };
  ir_blk{ @"iw_1.L24":
    %"iw_1.v27" : W = (Cmp Slt W) %"iw_1.pr.1", #0
    => goto "iw_1.L25" };
  ir_blk{ @"iw_1.L25" [%"iw_1.v29" : W = phi("iw_1.L10" => #0, "iw_1.L24" => %"iw_1.v27")]:
    => br %"iw_1.v29" ? "iw_1.L18" : "iw_1.L20" };
  ir_blk{ @"iw_1.L18":
    call %"iw_1.v33" : W = $"__GI___open_nocancel"(P %"iw_1.v7", W #524288)
    => goto "iw_1.L20" };
  ir_blk{ @"iw_1.L20" [%"iw_1.pr.2" : W = phi("iw_1.L18" => %"iw_1.v33", "iw_1.L25" => %"iw_1.pr.1")]:
    %"iw_1.v38" : W = (Cmp Slt W) %"iw_1.pr.2", #0
    => br %"iw_1.v38" ? "iw_1.L34" : "iw_1.L36" };
  ir_blk{ @"iw_1.L34":
    %"iw_1.v39" : P = Copy $"glibc_loadarchive#str.251";
    call %"iw_1.v42" : W = $"__GI___open_nocancel"(P %"iw_1.v39", W #524288)
    => goto "iw_1.L36" };
  ir_blk{ @"iw_1.L36" [%"iw_1.pr.3" : W = phi("iw_1.L34" => %"iw_1.v42", "iw_1.L20" => %"iw_1.pr.2")]:
    %"iw_1.v47" : W = (Cmp Slt W) %"iw_1.pr.3", #0
    => br %"iw_1.v47" ? "iw_1.L43" : "iw_1.L45" };
  ir_blk{ @"iw_1.L43":
    %"iw_1.v48" : P = Copy $"glibc_loadarchive#str.252";
    call %"iw_1.v51" : W = $"__GI___open_nocancel"(P %"iw_1.v48", W #524288)
    => goto "iw_1.L45" };
  ir_blk{ @"iw_1.L45" [%"iw_1.pr.4" : W = phi("iw_1.L43" => %"iw_1.v51", "iw_1.L36" => %"iw_1.pr.3")]:
    %"iw_1.v56" : W = (Cmp Slt W) %"iw_1.pr.4", #0
    => br %"iw_1.v56" ? "iw_1.L52" : "iw_1.L54" };
  ir_blk{ @"iw_1.L52":
    %"iw_1.v57" : P = Copy $"glibc_loadarchive#archfname";
    call %"iw_1.v60" : W = $"__GI___open_nocancel"(P %"iw_1.v57", W #524288)
    => goto "iw_1.L54" };
  ir_blk{ @"iw_1.L54" [%"iw_1.pr.5" : W = phi("iw_1.L52" => %"iw_1.v60", "iw_1.L45" => %"iw_1.pr.4")]:
    %"v191" : W = (Cmp Slt W) %"iw_1.pr.5", #0
    => br %"v191" ? "L187" : "L189" };
  ir_blk{ @"L187":
    => ret #0 };
  ir_blk{ @"L189":
    %"v197" : P = Copy $"glibc_loadarchive#archive_stat";
    call %"v198" : W = $"__GI___fstat64"(W %"iw_1.pr.5", P %"v197");
    %"v200" : W = (Cmp Eq W) %"v198", #4294967295
    => br %"v200" ? "L201" : "L209" };
  ir_blk{ @"L201" [%"pr.20" : W = phi("L189" => %"iw_1.pr.5", "L209" => %"iw_1.pr.5", "L251" => %"iw_1.pr.5", "L175" => #4294967295, "iw_3.L29" => #4294967295, "L365" => #4294967295, "L367" => #4294967295, "L471" => #4294967295)]:
    %"v206" : W = (Cmp Sge W) %"pr.20", #0
    => br %"v206" ? "L202" : "L204" };
  ir_blk{ @"L202":
    call void $"__GI___close_nocancel_nostatus"(W %"pr.20")
    => goto "L204" };
  ir_blk{ @"L204":
    => ret #0 };
  ir_blk{ @"L209":
    %"v213" : P = Copy $"glibc_loadarchive#archive_stat";
    %"v214" = %"v213" +p #48;
    %"chk13" : A = (Check 0 8 Read 1) %"v214";
    %"v215" : L = (RawLoad LdL 0) %"chk13";
    call %"v237" : P = $"__GI___mmap64"(P #0, L %"v215", W #1, W #2, W %"iw_1.pr.5", L #0);
    (Flight (a "v244") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v245" : L = Ptoi %"v237";
    %"v246" : L = Ptoi %"v244";
    %"v247" : W = (Cmp Eq L) %"v245", %"v246"
    => br %"v247" ? poll "L201" : "iw_2.start" };
  ir_blk{ @"iw_2.start":
    %"iw_2.v4" = %"v237" +p #8;
    %"chk14" : A = (Check 0 4 Read 1) %"iw_2.v4";
    %"iw_2.v5" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"iw_2.v7" = %"v237" +p #16;
    %"chk15" : A = (HalfCheck Upper 0 4 Read 1) %"chk14", %"iw_2.v7";
    %"iw_2.v8" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"iw_2.v9" : L = (Ext Uw) %"iw_2.v8";
    %"iw_2.v10" : L = Mul %"iw_2.v9", #12;
    %"iw_2.v11" : L = (Ext Uw) %"iw_2.v5";
    %"iw_2.v12" : L = Add %"iw_2.v11", %"iw_2.v10";
    %"iw_2.v15" = %"v237" +p #20;
    %"chk16" : A = (HalfCheck Upper 0 4 Read 1) %"chk14", %"iw_2.v15";
    %"iw_2.v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"iw_2.v18" = %"v237" +p #24;
    %"chk17" : A = (HalfCheck Upper 0 4 Read 1) %"chk14", %"iw_2.v18";
    %"iw_2.v19" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"iw_2.v20" : W = Add %"iw_2.v16", %"iw_2.v19";
    %"iw_2.v21" : L = (Ext Uw) %"iw_2.v20";
    %"iw_2.v24" = %"v237" +p #32;
    %"chk18" : A = (HalfCheck Upper 0 4 Read 1) %"chk14", %"iw_2.v24";
    %"iw_2.v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"iw_2.v27" = %"v237" +p #36;
    %"chk19" : A = (HalfCheck Upper 0 4 Read 1) %"chk14", %"iw_2.v27";
    %"iw_2.v28" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"iw_2.v29" : L = (Ext Uw) %"iw_2.v28";
    %"iw_2.v30" : L = Mul %"iw_2.v29", #108;
    %"iw_2.v31" : L = (Ext Uw) %"iw_2.v25";
    %"iw_2.v32" : L = Add %"iw_2.v31", %"iw_2.v30";
    %"iw_2.v42" : W = (Cmp Sgt L) %"iw_2.v21", %"iw_2.v32"
    => br %"iw_2.v42" ? "iw_2.L39" : "iw_2.L38" }] [ir_blk{ @"iw_2.L38":
    => goto "iw_2.L39" };
  ir_blk{ @"iw_2.L39" [%"iw_2.v45" : L = phi("iw_2.L38" => %"iw_2.v32", "iw_2.start" => %"iw_2.v21")]:
    %"iw_2.v46" : W = (Cmp Sgt L) %"iw_2.v12", %"iw_2.v45"
    => br %"iw_2.v46" ? "iw_2.L35" : "iw_2.L34" };
  ir_blk{ @"iw_2.L34":
    => br %"iw_2.v42" ? "iw_2.L35" : "iw_2.L49" };
  ir_blk{ @"iw_2.L49":
    => goto "iw_2.L35" };
  ir_blk{ @"iw_2.L35" [%"iw_2.v57" : L = phi("iw_2.L39" => %"iw_2.v12", "iw_2.L49" => %"iw_2.v32", "iw_2.L34" => %"iw_2.v21")]:
    %"v256" : W = (Cmp Ugt L) %"iw_2.v57", %"v215"
    => br %"v256" ? "L251" : "L297" };
  ir_blk{ @"L251":
    call %"v259" : W = $"__GI___munmap"(P %"v237", L %"v215")
    => goto poll "L201" };
  ir_blk{ @"L297":
    call void $"__GI___close_nocancel_nostatus"(W %"iw_1.pr.5");
    %"v312" : P = Copy $"glibc_loadarchive#headmap";
    %"chk20" : A = (Check 0 8 Write 8) %"v312";
    store.ptr [%"chk20" + 0] <- %"v237";
    %"v314" : P = Copy $"glibc_loadarchive#headmap";
    %"v315" = %"v314" +p #12;
    %"chk21" : A = (Check 0 4 Write 1) %"v315";
    store Ww [%"chk21" + 0] <- %"v215"
    => goto "L175" };
  ir_blk{ @"L175":
    %"v320" : P = Copy $"glibc_loadarchive#headmap";
    %"chk22" : A = (Check 0 8 Read 8) %"v320";
    %"v321" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v322" : L = Ptoi %"v321";
    %"v324" : W = (Cmp Eq L) %"v322", %"v32"
    => br %"v324" ? poll "L201" : "L319" };
  ir_blk{ @"L319":
    call %"v330" : L = $"__GI_strlen"(P %"pr.2")
    => goto "iw_3.L7" };
  ir_blk{ @"iw_3.L7" [%"iw_3.pr.2" : W = phi("iw_3.L8" => %"iw_3.v26", "L319" => %"v330"); %"iw_3.pr.1" : L = phi("iw_3.L8" => %"iw_3.v23", "L319" => #0)]:
    %"iw_3.v12" : W = (Cmp Ult L) %"iw_3.pr.1", %"v330"
    => br %"iw_3.v12" ? "iw_3.L8" : "iw_3.L9" };
  ir_blk{ @"iw_3.L8":
    %"iw_3.v14" : W = Shl %"iw_3.pr.2", #9;
    %"iw_3.v18" : W = Shr %"iw_3.pr.2", #23;
    %"iw_3.v19" : W = Or %"iw_3.v14", %"iw_3.v18";
    %"iw_3.v23" : L = Add %"iw_3.pr.1", #1;
    %"iw_3.v24" = %"pr.2" +p %"iw_3.pr.1";
    %"chk23" : A = (Check 0 1 Read 1) %"iw_3.v24";
    %"iw_3.v25" : W = (RawLoad (LdNarrow Ub) 0) %"chk23";
    %"iw_3.v26" : W = Add %"iw_3.v19", %"iw_3.v25"
    => goto poll "iw_3.L7" };
  ir_blk{ @"iw_3.L9":
    %"iw_3.v31" : W = (Cmp Ne W) %"iw_3.pr.2", #0
    => br %"iw_3.v31" ? "iw_3.L29" : "iw_3.L28" };
  ir_blk{ @"iw_3.L28":
    => goto "iw_3.L29" };
  ir_blk{ @"iw_3.L29" [%"iw_3.v34" : W = phi("iw_3.L28" => #4294967295, "iw_3.L9" => %"iw_3.pr.2")]:
    %"v332" : L = (Ext Uw) %"iw_3.v34";
    %"v333" : P = Copy $"glibc_loadarchive#headmap";
    %"chk24" : A = (Check 0 8 Read 8) %"v333";
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v337" = %"v334" +p #8;
    %"chk25" : A = (Check 0 4 Read 1) %"v337";
    %"v338" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v339" : L = (Ext Uw) %"v338";
    %"v340" = %"v334" +p %"v339";
    %"v345" = %"v334" +p #16;
    %"chk26" : A = (HalfCheck Upper 0 4 Read 1) %"chk25", %"v345";
    %"v346" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v347" : W = (Cmp Ule W) %"v346", #2
    => br %"v347" ? poll "L201" : "L343" };
  ir_blk{ @"L343":
    %"v353" = %"v334" +p #16;
    %"v354" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v355" : L = (Ext Uw) %"v354";
    %"v356" : L = Urem %"v332", %"v355";
    %"v360" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v361" : W = Sub %"v360", #2;
    %"v362" : L = (Ext Uw) %"v361";
    %"v363" : L = Urem %"v332", %"v362";
    %"v364" : L = Add %"v363", #1
    => goto "L365" };
  ir_blk{ @"L365" [%"pr.9" : L = phi("L343" => %"v356", "L411" => %"v425", "L381" => %"v410")]:
    %"v373" : L = Mul %"pr.9", #12;
    %"v374" = %"v340" +p %"v373";
    %"v375" = %"v374" +p #4;
    %"chk29" : A = (Check 0 4 Read 1) %"v375";
    %"v376" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v377" : W = (Cmp Eq W) %"v376", #0
    => br %"v377" ? poll "L201" : "L370" };
  ir_blk{ @"L370":
    %"chk30" : A = (HalfCheck Lower 0 4 Read 1) %"chk29", %"v374";
    %"v386" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v388" : L = (Ext Uw) %"v386";
    %"v389" : W = (Cmp Eq L) %"v388", %"v332"
    => br %"v389" ? "L390" : "L391" };
  ir_blk{ @"L390":
    %"v393" : P = Copy $"glibc_loadarchive#headmap";
    %"chk31" : A = (Check 0 8 Read 8) %"v393";
    %"v394" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v399" = %"v374" +p #4;
    %"chk32" : A = (Renew 0 4 Read 1) %"chk29", %"v399";
    %"v400" : W = (RawLoad (LdNarrow Uw) 0) %"chk32";
    %"v401" : L = (Ext Uw) %"v400";
    %"v402" = %"v394" +p %"v401";
    call %"v403" : W = $"__GI_strcmp"(P %"pr.2", P %"v402");
    %"v404" : W = (Cmp Eq W) %"v403", #0
    => goto "L391" };
  ir_blk{ @"L391" [%"v406" : W = phi("L370" => #0, "L390" => %"v404")]:
    => br %"v406" ? "L367" : "L381" };
  ir_blk{ @"L381":
    %"v410" : L = Add %"pr.9", %"v364";
    %"v416" = %"v334" +p #16;
    %"chk33" : A = (Renew 0 4 Read 1) %"chk26", %"v416";
    %"v417" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v418" : L = (Ext Uw) %"v417";
    %"v419" : W = (Cmp Uge L) %"v410", %"v418"
    => br %"v419" ? "L411" : poll "L365" };
  ir_blk{ @"L411":
    %"v422" = %"v334" +p #16;
    %"v423" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v424" : L = (Ext Uw) %"v423";
    %"v425" : L = Sub %"v410", %"v424"
    => goto poll "L365" };
  ir_blk{ @"L367":
    %"v433" = %"v374" +p #8;
    %"chk35" : A = (HalfCheck Upper 0 4 Read 1) %"chk29", %"v433";
    %"v434" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v435" : W = (Cmp Eq W) %"v434", #0
    => br %"v435" ? poll "L201" : "L428" };
  ir_blk{ @"L428":
    %"v437" : P = Copy $"glibc_loadarchive#headmap";
    %"chk36" : A = (Check 0 8 Read 8) %"v437";
    %"v438" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v443" = %"v374" +p #8;
    %"chk37" : A = (Renew 0 4 Read 1) %"chk35", %"v443";
    %"v444" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v445" : L = (Ext Uw) %"v444";
    %"v446" = %"v438" +p %"v445";
    %"v454" : P = Copy $"glibc_loadarchive#headmap";
    %"v455" = %"v454" +p #12;
    %"chk38" : A = (Check 0 4 Read 1) %"v455";
    %"v456" : W = (RawLoad (LdNarrow Uw) 0) %"chk38";
    %"v457" : P = Copy $"glibc_loadarchive#archive_stat";
    %"v458" = %"v457" +p #48;
    %"chk39" : A = (Check 0 8 Read 1) %"v458";
    %"v459" : L = (RawLoad LdL 0) %"chk39";
    %"v460" : L = (Ext Uw) %"v456";
    %"v461" : W = (Cmp Eq L) %"v460", %"v459"
    => br %"v461" ? "L465" : "L452" };
  ir_blk{ @"L452":
    %"v462" : P = Copy $"glibc_loadarchive#str.254";
    %"v463" : P = Copy $"glibc_loadarchive#str.255";
    %"v464" : P = Copy $"glibc_loadarchive#str.256";
    call void $"__libc_assert_fail"(P %"v462", P %"v463", W #329, P %"v464")
    => goto "L465" };
  ir_blk{ @"L465" [%"pr.14" : W = phi("L467" => %"v530", "L452" => #0, "L428" => #0)]:
    %"v470" : W = (Cmp Slt W) %"pr.14", #13
    => br %"v470" ? "L466" : "L998" };
  ir_blk{ @"L466":
    %"v475" : W = (Cmp Ne W) %"pr.14", #6
    => br %"v475" ? "L471" : "L467" };
  ir_blk{ @"L471":
    %"v480" = %"v446" +p #4;
    %"v482" : L = (Ext Sw) %"pr.14";
    %"v483" : L = Shl %"v482", #3;
    %"v484" = %"v480" +p %"v483";
    %"chk40" : A = (Check 0 4 Read 1) %"v484";
    %"v485" : W = (RawLoad (LdNarrow Uw) 0) %"chk40";
    %"v492" = %"v484" +p #4;
    %"chk41" : A = (HalfCheck Upper 0 4 Read 1) %"chk40", %"v492";
    %"v493" : W = (RawLoad (LdNarrow Uw) 0) %"chk41";
    %"v494" : W = Add %"v485", %"v493";
    %"v495" : P = Copy $"glibc_loadarchive#headmap";
    %"v496" = %"v495" +p #12;
    %"chk42" : A = (Check 0 4 Read 1) %"v496";
    %"v497" : W = (RawLoad (LdNarrow Uw) 0) %"chk42";
    %"v498" : W = (Cmp Ugt W) %"v494", %"v497"
    => br %"v498" ? poll "L201" : "L478" };
  ir_blk{ @"L478":
    %"v502" : L = Shl %"v482", #4;
    %"v503" = %"v7" +p %"v502";
    %"v504" : P = Copy $"glibc_loadarchive#headmap";
    %"chk43" : A = (Check 0 8 Read 8) %"v504";
    %"v505" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v507" = %"v446" +p #4;
    %"v511" = %"v507" +p %"v483";
    %"chk44" : A = (Check 0 4 Read 1) %"v511";
    %"v512" : W = (RawLoad (LdNarrow Uw) 0) %"chk44";
    %"v513" : L = (Ext Uw) %"v512";
    %"v514" = %"v505" +p %"v513";
    %"chk45" : A = (Check 0 8 Write 8) %"v503";
    store.ptr [%"chk45" + 0] <- %"v514";
    %"v519" = %"v503" +p #8;
    %"v526" = %"v511" +p #4;
    %"chk46" : A = (HalfCheck Upper 0 4 Read 1) %"chk44", %"v526";
    %"v527" : W = (RawLoad (LdNarrow Uw) 0) %"chk46";
    %"v528" : L = (Ext Uw) %"v527";
    %"chk47" : A = (HalfCheck Upper 0 8 Write 1) %"chk45", %"v519";
    store Wl [%"chk47" + 0] <- %"v528"
    => goto "L467" };
  ir_blk{ @"L467":
    %"v530" : W = Add %"pr.14", #1
    => goto poll "L465" };
  ir_blk{ @"L998":
    call %"v1003" : P = $"malloc"(L #120);
    %"v1008" : L = Ptoi %"v1003";
    %"v1010" : W = (Cmp Eq L) %"v1008", %"v32"
    => br %"v1010" ? "L1004" : "L1006" };
  ir_blk{ @"L1004":
    => ret #0 };
  ir_blk{ @"L1006":
    %"v1015" = %"v1003" +p #8;
    %"chk48" : A = (Renew 0 8 Read 8) %"chk0", %"v2";
    %"v1017" : P = (RawLoadPointer 0 load_effects) %"chk48";
    call %"v1018" : P = $"__GI___strdup"(P %"v1017");
    %"chk49" : A = (Check 0 8 Write 8) %"v1015";
    store.ptr [%"chk49" + 0] <- %"v1018";
    %"chk50" : A = (Renew 0 8 Read 8) %"chk49", %"v1015";
    %"v1024" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v1025" : L = Ptoi %"v1024";
    %"v1027" : W = (Cmp Eq L) %"v1025", %"v32"
    => br %"v1027" ? "L1019" : "L1021" };
  ir_blk{ @"L1019":
    call void $"free"(P %"v1003")
    => ret #0 };
  ir_blk{ @"L1021":
    %"v1033" : P = Copy $"glibc_loadarchive#archloaded";
    %"chk51" : A = (Check 0 8 Read 8) %"v1033";
    %"v1034" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"chk52" : A = (HalfCheck Lower 0 8 Write 8) %"chk49", %"v1003";
    store.ptr [%"chk52" + 0] <- %"v1034";
    %"v1035" : P = Copy $"glibc_loadarchive#archloaded";
    %"chk53" : A = (Check 0 8 Write 8) %"v1035";
    store.ptr [%"chk53" + 0] <- %"v1003"
    => goto "L1037" };
  ir_blk{ @"L1037" [%"pr.13" : W = phi("L1021" => #0, "L1039" => %"v1111")]:
    %"v1042" : W = (Cmp Slt W) %"pr.13", #13
    => br %"v1042" ? "L1038" : "L1040" };
  ir_blk{ @"L1038":
    %"v1047" : W = (Cmp Ne W) %"pr.13", #6
    => br %"v1047" ? "L1043" : "L1039" };
  ir_blk{ @"L1043":
    %"v1049" = %"v1003" +p #16;
    %"v1051" : L = (Ext Sw) %"pr.13";
    %"v1052" : L = Shl %"v1051", #3;
    %"v1053" = %"v1049" +p %"v1052";
    %"v1057" : L = Shl %"v1051", #4;
    %"v1058" = %"v7" +p %"v1057";
    %"chk54" : A = (Check 0 8 Read 8) %"v1058";
    %"v1059" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v1064" = %"v1058" +p #8;
    %"chk55" : A = (HalfCheck Upper 0 8 Read 1) %"chk54", %"v1064";
    %"v1065" : L = (RawLoad LdL 0) %"chk55";
    call %"v1066" : P = $"_nl_intern_locale_data"(W %"pr.13", P %"v1059", L %"v1065");
    %"chk56" : A = (Check 0 8 Write 8) %"v1053";
    store.ptr [%"chk56" + 0] <- %"v1066";
    %"chk57" : A = (Renew 0 8 Read 8) %"chk56", %"v1053";
    %"v1076" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"v1077" : L = Ptoi %"v1076";
    %"v1079" : W = (Cmp Ne L) %"v1077", %"v32"
    => br %"v1079" ? "L1067" : "L1039" };
  ir_blk{ @"L1067":
    %"v1083" = %"v1003" +p #16;
    %"v1087" = %"v1083" +p %"v1052";
    %"chk58" : A = (Check 0 8 Read 8) %"v1087";
    %"v1088" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v1089" = %"v1088" +p #24;
    %"chk59" : A = (Check 0 4 Write 1) %"v1089";
    store Ww [%"chk59" + 0] <- #2;
    %"v1096" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v1098" = %"v1003" +p #8;
    %"chk61" : A = (Renew 0 8 Read 8) %"chk49", %"v1098";
    %"v1099" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"chk62" : A = (Check 0 8 Write 8) %"v1096";
    store.ptr [%"chk62" + 0] <- %"v1099";
    %"chk63" : A = (Renew 0 8 Read 8) %"chk58", %"v1087";
    %"v1106" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"v1107" = %"v1106" +p #40;
    %"chk64" : A = (Check 0 4 Write 1) %"v1107";
    store Ww [%"chk64" + 0] <- #4294967295
    => goto "L1039" };
  ir_blk{ @"L1039":
    %"v1111" : W = Add %"pr.13", #1
    => goto poll "L1037" };
  ir_blk{ @"L1040":
    %"v1114" = %"v1003" +p #8;
    %"chk65" : A = (Renew 0 8 Read 8) %"chk49", %"v1114";
    %"v1115" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Renew 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk66" + 0] <- %"v1115";
    %"v1117" = %"v1003" +p #16;
    %"v1119" : L = (Ext Sw) %"v0";
    %"v1120" : L = Shl %"v1119", #3;
    %"v1121" = %"v1117" +p %"v1120";
    %"chk67" : A = (Check 0 8 Read 8) %"v1121";
    %"v1122" : P = (RawLoadPointer 0 load_effects) %"chk67"
    => ret %"v1122" }])) }.

Definition hello_image_fn__nl_intern_locale_data : func :=
  ir_fn{ "export" "_nl_intern_locale_data"(W %"v0", P %"v2", L %"v4") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v14" : W = (Cmp Ult L) %"v4", #8
    => br %"v14" ? "L18" : "L17" };
  ir_blk{ @"L17":
    %"chk0" : A = (Check 0 4 Read 1) %"v2";
    %"v20" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v25" : W = (Cmp Eq W) %"v0", #3
    => br %"v25" ? "L21" : "L22" };
  ir_blk{ @"L21":
    %"v27" : W = Xor %"v0", #537202708
    => goto "L23" };
  ir_blk{ @"L22":
    %"v32" : W = (Cmp Eq W) %"v0", #0
    => br %"v32" ? "L28" : "L29" };
  ir_blk{ @"L28":
    %"v34" : W = Xor %"v0", #537462560
    => goto "L23" };
  ir_blk{ @"L29":
    %"v36" : W = Xor %"v0", #537071893
    => goto "L23" };
  ir_blk{ @"L23" [%"v38" : W = phi("L21" => %"v27", "L28" => %"v34", "L29" => %"v36")]:
    %"v39" : W = (Cmp Ne W) %"v20", %"v38"
    => goto "L18" };
  ir_blk{ @"L18" [%"v43" : W = phi("start" => #1, "L23" => %"v39")]:
    => br %"v43" ? "L10" : "L12" };
  ir_blk{ @"L10":
    %"v44" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"v44";
    store Ww [%"chk1" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L12":
    %"v50" = %"v2" +p #4;
    %"chk2" : A = (Check 0 4 Read 1) %"v50";
    %"v51" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v52" : P = Copy $"glibc_loadlocale#_nl_category_num_items";
    %"v54" : L = (Ext Sw) %"v0";
    %"v55" : L = Shl %"v54", #3;
    %"v56" = %"v52" +p %"v55";
    %"chk3" : A = (Check 0 8 Read 1) %"v56";
    %"v57" : L = (RawLoad LdL 0) %"chk3";
    %"v58" : L = (Ext Uw) %"v51";
    %"v59" : W = (Cmp Ult L) %"v58", %"v57"
    => br %"v59" ? "L63" : "L62" };
  ir_blk{ @"L62":
    %"v65" = %"v2" +p #4;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk2", %"v65";
    %"v66" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v67" : L = (Ext Uw) %"v66";
    %"v68" : L = Shl %"v67", #2;
    %"v69" : L = Add %"v68", #8;
    %"v71" : W = (Cmp Uge L) %"v69", %"v4"
    => goto "L63" };
  ir_blk{ @"L63" [%"v75" : W = phi("L12" => #1, "L62" => %"v71")]:
    => br %"v75" ? "L46" : "L48" };
  ir_blk{ @"L46":
    %"v76" : P = Copy $"__libc_errno";
    %"chk5" : A = (Check 0 4 Write 1) %"v76";
    store Ww [%"chk5" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L48":
    %"v80" = %"v2" +p #4;
    %"chk6" : A = (Renew 0 4 Read 1) %"chk2", %"v80";
    %"v81" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v82" : L = (Ext Uw) %"v81";
    %"v83" : L = Shl %"v82", #3;
    %"v84" : L = Add %"v83", #56;
    %"iw_1.v8" : W = (Cmp Eq W) %"v0", #0
    => br %"iw_1.v8" ? "iw_1.join" : "iw_1.L6" };
  ir_blk{ @"iw_1.L6":
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v87" : L = phi("iw_1.L6" => #0, "L48" => #24)]:
    %"v90" : L = Add %"v84", %"v87";
    call %"v91" : P = $"malloc"(L %"v90");
    %"v96" : L = Ptoi %"v91";
    %"v97" : L = Ptoi #0;
    %"v98" : W = (Cmp Eq L) %"v96", %"v97"
    => br %"v98" ? "L92" : "L94" };
  ir_blk{ @"L92":
    => ret #0 };
  ir_blk{ @"L94":
    %"v101" = %"v91" +p #8;
    %"chk7" : A = (Check 0 8 Write 8) %"v101";
    store.ptr [%"chk7" + 0] <- %"v2";
    %"v104" = %"v91" +p #16;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 1) %"chk7", %"v104";
    store Wl [%"chk8" + 0] <- %"v4";
    %"v110" : W = (Cmp Eq L) %"v87", #0
    => br %"v110" ? "L106" : "L107" };
  ir_blk{ @"L106":
    %"v112" = %"v91" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v112";
    store.ptr [%"chk9" + 0] <- #0
    => goto "L108" };
  ir_blk{ @"L107":
    %"v114" = %"v91" +p #32;
    %"v117" = %"v91" +p %"v84";
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk7", %"v114";
    store.ptr [%"chk10" + 0] <- %"v117";
    %"chk11" : A = (Renew 0 8 Read 8) %"chk10", %"v114";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk11";
    call %"v122" : P = $"__GI_memset"(P %"v120", W #0, L %"v87")
    => goto "L108" };
  ir_blk{ @"L108":
    %"v124" = %"v91" +p #40;
    %"chk12" : A = (HalfCheck Upper 0 4 Write 1) %"chk7", %"v124";
    store Ww [%"chk12" + 0] <- #0;
    %"v126" = %"v91" +p #44;
    %"chk13" : A = (HalfCheck Upper 0 4 Write 1) %"chk7", %"v126";
    store Ww [%"chk13" + 0] <- #0;
    %"v128" = %"v91" +p #48;
    %"v130" = %"v2" +p #4;
    %"chk14" : A = (Renew 0 4 Read 1) %"chk2", %"v130";
    %"v131" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"chk15" : A = (HalfCheck Upper 0 4 Write 1) %"chk7", %"v128";
    store Ww [%"chk15" + 0] <- %"v131"
    => goto "L132" };
  ir_blk{ @"L132" [%"pr.1" : L = phi("L108" => #0, "L134" => %"v356")]:
    %"v138" = %"v91" +p #48;
    %"chk16" : A = (Renew 0 4 Read 1) %"chk15", %"v138";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"v140" : L = (Ext Uw) %"v139";
    %"v141" : W = (Cmp Ult L) %"pr.1", %"v140"
    => br %"v141" ? "L133" : "L135" };
  ir_blk{ @"L133":
    %"v144" = %"v2" +p #8;
    %"v146" : L = Shl %"pr.1", #2;
    %"v147" = %"v144" +p %"v146";
    %"chk17" : A = (Check 0 4 Read 1) %"v147";
    %"v148" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v149" : L = (Ext Uw) %"v148";
    %"v155" = %"v91" +p #16;
    %"chk18" : A = (Renew 0 8 Read 1) %"chk8", %"v155";
    %"v156" : L = (RawLoad LdL 0) %"chk18";
    %"v157" : W = (Cmp Ugt L) %"v149", %"v156"
    => br %"v157" ? "L160" : "L165" };
  ir_blk{ @"L160":
    call void $"free"(P %"v91");
    %"v162" : P = Copy $"__libc_errno";
    %"chk19" : A = (Check 0 4 Write 1) %"v162";
    store Ww [%"chk19" + 0] <- #22
    => ret #0 };
  ir_blk{ @"L167":
    %"v173" : W = (Cmp Uge L) %"pr.1", #6
    => br %"v173" ? poll "L160" : "L166" };
  ir_blk{ @"L175":
    %"v181" : W = (Cmp Uge L) %"pr.1", #159
    => br %"v181" ? poll "L160" : "L166" };
  ir_blk{ @"L183":
    %"v189" : W = (Cmp Uge L) %"pr.1", #19
    => br %"v189" ? poll "L160" : "L166" };
  ir_blk{ @"L191":
    %"v197" : W = (Cmp Uge L) %"pr.1", #46
    => br %"v197" ? poll "L160" : "L166" };
  ir_blk{ @"L199":
    %"v205" : W = (Cmp Uge L) %"pr.1", #5
    => br %"v205" ? poll "L160" : "L166" };
  ir_blk{ @"L207":
    %"v213" : W = (Cmp Uge L) %"pr.1", #3
    => br %"v213" ? poll "L160" : "L166" };
  ir_blk{ @"L215":
    %"v221" : W = (Cmp Uge L) %"pr.1", #7
    => br %"v221" ? poll "L160" : "L166" };
  ir_blk{ @"L223":
    %"v229" : W = (Cmp Uge L) %"pr.1", #13
    => br %"v229" ? poll "L160" : "L166" };
  ir_blk{ @"L231":
    %"v237" : W = (Cmp Uge L) %"pr.1", #5
    => br %"v237" ? poll "L160" : "L166" };
  ir_blk{ @"L239":
    %"v245" : W = (Cmp Uge L) %"pr.1", #2
    => br %"v245" ? poll "L160" : "L166" };
  ir_blk{ @"L247":
    %"v253" : W = (Cmp Uge L) %"pr.1", #16
    => br %"v253" ? poll "L160" : "L166" };
  ir_blk{ @"L255":
    => br %"iw_1.v8" ? "L166" : "L257" };
  ir_blk{ @"L257":
    %"v261" : P = Copy $"glibc_loadlocale#str.240";
    %"v262" : P = Copy $"glibc_loadlocale#str.241";
    %"v263" : P = Copy $"glibc_loadlocale#str.242";
    call void $"__libc_assert_fail"(P %"v261", P %"v262", W #206, P %"v263")
    => goto "L166" }] [ir_blk{ @"L165":
    %"v265" : W = (Cmp Slt W) %"v0", #7
    => br %"v265" ? "L266" : "L267" };
  ir_blk{ @"L266":
    %"v268" : W = (Cmp Slt W) %"v0", #3
    => br %"v268" ? "L269" : "L270" };
  ir_blk{ @"L269":
    %"v271" : W = (Cmp Eq W) %"v0", #1
    => br %"v271" ? poll "L167" : "L272" };
  ir_blk{ @"L272":
    %"v273" : W = (Cmp Eq W) %"v0", #2
    => br %"v273" ? poll "L175" : poll "L255" };
  ir_blk{ @"L270":
    %"v275" : W = (Cmp Eq W) %"v0", #3
    => br %"v275" ? poll "L183" : "L276" };
  ir_blk{ @"L276":
    %"v277" : W = (Cmp Eq W) %"v0", #4
    => br %"v277" ? poll "L191" : "L278" };
  ir_blk{ @"L278":
    %"v279" : W = (Cmp Eq W) %"v0", #5
    => br %"v279" ? poll "L199" : poll "L255" };
  ir_blk{ @"L267":
    %"v281" : W = (Cmp Slt W) %"v0", #10
    => br %"v281" ? "L282" : "L283" };
  ir_blk{ @"L282":
    %"v284" : W = (Cmp Eq W) %"v0", #7
    => br %"v284" ? poll "L207" : "L285" };
  ir_blk{ @"L285":
    %"v286" : W = (Cmp Eq W) %"v0", #8
    => br %"v286" ? poll "L215" : "L287" };
  ir_blk{ @"L287":
    %"v288" : W = (Cmp Eq W) %"v0", #9
    => br %"v288" ? poll "L223" : poll "L255" };
  ir_blk{ @"L283":
    %"v290" : W = (Cmp Eq W) %"v0", #10
    => br %"v290" ? poll "L231" : "L291" };
  ir_blk{ @"L291":
    %"v292" : W = (Cmp Eq W) %"v0", #11
    => br %"v292" ? poll "L239" : "L293" };
  ir_blk{ @"L293":
    %"v294" : W = (Cmp Eq W) %"v0", #12
    => br %"v294" ? poll "L247" : poll "L255" };
  ir_blk{ @"L166":
    => br %"iw_1.v8" ? "L301" : "L302" };
  ir_blk{ @"L301":
    %"v305" : W = (Cmp Uge L) %"pr.1", #86
    => goto "L302" };
  ir_blk{ @"L302" [%"v307" : W = phi("L166" => #0, "L301" => %"v305")]:
    => br %"v307" ? "L309" : "L308" };
  ir_blk{ @"L308":
    %"v310" : P = Copy $"glibc_loadlocale#_nl_value_types";
    %"v314" = %"v310" +p %"v55";
    %"chk20" : A = (Check 0 8 Read 8) %"v314";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v318" = %"v315" +p %"v146";
    %"chk21" : A = (Check 0 4 Read 1) %"v318";
    %"v319" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v320" : W = (Cmp Ne W) %"v319", #5
    => goto "L309" };
  ir_blk{ @"L309" [%"v324" : W = phi("L302" => #1, "L308" => %"v320")]:
    => br %"v324" ? "L296" : "L297" };
  ir_blk{ @"L296":
    %"v326" = %"v91" +p #56;
    %"v328" : L = Shl %"pr.1", #3;
    %"v329" = %"v326" +p %"v328";
    %"v331" = %"v91" +p #8;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk7", %"v331";
    %"v332" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v334" = %"v332" +p %"v149";
    %"chk23" : A = (Check 0 8 Write 8) %"v329";
    store.ptr [%"chk23" + 0] <- %"v334"
    => goto "L134" };
  ir_blk{ @"L297":
    %"v340" : L = And %"v149", #3;
    %"v342" : W = (Cmp Ne L) %"v340", #0
    => br %"v342" ? poll "L160" : "L337" };
  ir_blk{ @"L337":
    %"v345" = %"v91" +p #56;
    %"v347" : L = Shl %"pr.1", #3;
    %"v348" = %"v345" +p %"v347";
    %"v350" = %"v91" +p #8;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk7", %"v350";
    %"v351" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v353" = %"v351" +p %"v149";
    %"chk25" : A = (Check 0 4 Read 1) %"v353";
    %"v354" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"chk26" : A = (Check 0 4 Write 1) %"v348";
    store Ww [%"chk26" + 0] <- %"v354"
    => goto "L134" };
  ir_blk{ @"L134":
    %"v356" : L = Add %"pr.1", #1
    => goto poll "L132" };
  ir_blk{ @"L135":
    %"v361" : W = (Cmp Ugt L) %"v87", #0
    => br %"v361" ? "iw_2.start" : "L359" };
  ir_blk{ @"iw_2.start":
    => br %"iw_1.v8" ? "iw_2.iw_1.start" : "L359" };
  ir_blk{ @"iw_2.iw_1.start":
    %"iw_2.iw_1.v4" = %"v91" +p #32;
    %"chk27" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"iw_2.iw_1.v4";
    %"iw_2.iw_1.v5" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"iw_2.iw_1.v7" = %"iw_2.iw_1.v5" +p #9;
    call %"iw_2.iw_1.v8" : P = $"__GI_memset"(P %"iw_2.iw_1.v7", W #1, L #10)
    => goto "iw_2.iw_1.L10" };
  ir_blk{ @"iw_2.iw_1.L10" [%"iw_2.iw_1.pr.1" : W = phi("iw_2.iw_1.L12" => %"iw_2.iw_1.v83", "iw_2.iw_1.start" => #0)]:
    %"iw_2.iw_1.v15" : W = (Cmp Sle W) %"iw_2.iw_1.pr.1", #9
    => br %"iw_2.iw_1.v15" ? "iw_2.iw_1.L11" : "L359" };
  ir_blk{ @"iw_2.iw_1.L11":
    %"iw_2.iw_1.v18" = %"v91" +p #56;
    %"iw_2.iw_1.v20" : W = Add %"iw_2.iw_1.pr.1", #41;
    %"iw_2.iw_1.v21" : W = And %"iw_2.iw_1.v20", #65535;
    %"iw_2.iw_1.v22" : L = (Ext Sw) %"iw_2.iw_1.v21";
    %"iw_2.iw_1.v23" : L = Shl %"iw_2.iw_1.v22", #3;
    %"iw_2.iw_1.v24" = %"iw_2.iw_1.v18" +p %"iw_2.iw_1.v23";
    %"chk28" : A = (Check 0 8 Read 8) %"iw_2.iw_1.v24";
    %"iw_2.iw_1.v25" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"chk29" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v25";
    %"iw_2.iw_1.v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk29";
    %"iw_2.iw_1.v34" : W = Add %"iw_2.iw_1.pr.1", #48;
    %"iw_2.iw_1.v35" : W = (Cmp Ne W) %"iw_2.iw_1.v32", %"iw_2.iw_1.v34"
    => br %"iw_2.iw_1.v35" ? "iw_2.iw_1.L37" : "iw_2.iw_1.L36" };
  ir_blk{ @"iw_2.iw_1.L36":
    %"iw_2.iw_1.v39" = %"iw_2.iw_1.v25" +p #1;
    %"chk30" : A = (HalfCheck Upper 0 1 Read 1) %"chk29", %"iw_2.iw_1.v39";
    %"iw_2.iw_1.v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk30";
    %"iw_2.iw_1.v41" : W = (Cmp Ne W) %"iw_2.iw_1.v40", #0
    => goto "iw_2.iw_1.L37" };
  ir_blk{ @"iw_2.iw_1.L37" [%"iw_2.iw_1.v43" : W = phi("iw_2.iw_1.L11" => #1, "iw_2.iw_1.L36" => %"iw_2.iw_1.v41")]:
    => br %"iw_2.iw_1.v43" ? "iw_2.iw_1.L27" : "iw_2.iw_1.L29" };
  ir_blk{ @"iw_2.iw_1.L27":
    %"iw_2.iw_1.v45" = %"iw_2.iw_1.v5" +p #8;
    %"chk31" : A = (Check 0 1 Write 1) %"iw_2.iw_1.v45";
    store Wb [%"chk31" + 0] <- #1;
    %"iw_2.iw_1.v48" = %"v91" +p #56;
    %"iw_2.iw_1.v54" = %"iw_2.iw_1.v48" +p %"iw_2.iw_1.v23";
    %"chk32" : A = (Check 0 8 Read 8) %"iw_2.iw_1.v54";
    %"iw_2.iw_1.v55" : P = (RawLoadPointer 0 load_effects) %"chk32";
    call %"iw_2.iw_1.v56" : L = $"__GI_strlen"(P %"iw_2.iw_1.v55");
    %"iw_2.iw_1.v57" : W = (Ext Ub) %"iw_2.iw_1.v56"
    => goto "iw_2.iw_1.L29" };
  ir_blk{ @"iw_2.iw_1.L29" [%"iw_2.iw_1.pr.2" : W = phi("iw_2.iw_1.L27" => %"iw_2.iw_1.v57", "iw_2.iw_1.L37" => #1)]:
    %"iw_2.iw_1.v59" = %"iw_2.iw_1.v5" +p #9;
    %"iw_2.iw_1.v61" : L = (Ext Sw) %"iw_2.iw_1.pr.1";
    %"iw_2.iw_1.v62" = %"iw_2.iw_1.v59" +p %"iw_2.iw_1.v61";
    %"iw_2.iw_1.v63" : W = (Ext Ub) %"iw_2.iw_1.pr.2";
    %"chk33" : A = (Check 0 1 Write 1) %"iw_2.iw_1.v62";
    store Wb [%"chk33" + 0] <- %"iw_2.iw_1.v63";
    %"iw_2.iw_1.v68" : W = (Cmp Eq W) %"iw_2.iw_1.pr.1", #0
    => br %"iw_2.iw_1.v68" ? "iw_2.iw_1.L64" : "iw_2.iw_1.L65" };
  ir_blk{ @"iw_2.iw_1.L64":
    %"iw_2.iw_1.v70" = %"iw_2.iw_1.v5" +p #19;
    %"chk34" : A = (Check 0 1 Write 1) %"iw_2.iw_1.v70";
    store Wb [%"chk34" + 0] <- %"iw_2.iw_1.v63"
    => goto "iw_2.iw_1.L12" };
  ir_blk{ @"iw_2.iw_1.L65":
    %"iw_2.iw_1.v76" = %"iw_2.iw_1.v5" +p #19;
    %"chk35" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v76";
    %"iw_2.iw_1.v77" : W = (RawLoad (LdNarrow Ub) 0) %"chk35";
    %"iw_2.iw_1.v79" : W = (Cmp Ne W) %"iw_2.iw_1.v77", %"iw_2.iw_1.v63"
    => br %"iw_2.iw_1.v79" ? "iw_2.iw_1.L72" : "iw_2.iw_1.L12" };
  ir_blk{ @"iw_2.iw_1.L72":
    %"iw_2.iw_1.v81" = %"iw_2.iw_1.v5" +p #19;
    %"chk36" : A = (Renew 0 1 Write 1) %"chk35", %"iw_2.iw_1.v81";
    store Wb [%"chk36" + 0] <- #0
    => goto "iw_2.iw_1.L12" };
  ir_blk{ @"iw_2.iw_1.L12":
    %"iw_2.iw_1.v83" : W = Add %"iw_2.iw_1.pr.1", #1
    => goto poll "iw_2.iw_1.L10" };
  ir_blk{ @"L359":
    => ret %"v91" }])) }.

Definition hello_image_fn__nl_load_locale : func :=
  ir_fn{ "export" "_nl_load_locale"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v6" : P = (Alloc 8) #144;
    %"v11" = %"v0" +p #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v11";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v15" : W = $"__GI___open_nocancel"(P %"v13", W #524288);
    %"v20" : L = (Ext Sw) %"v15";
    %"v21" : W = (Cmp Slt L) %"v20", #0
    => br %"v21" ? "L16" : "L18";
  @"L16":
    => ret void;
  @"L18":
    call %"v27" : W = $"__GI___fstat64"(W %"v15", P %"v6");
    %"v28" : W = (Cmp Slt W) %"v27", #0
    => br %"v28" ? "L31" : "L25";
  @"L31" [%"pr.1" : W = phi("L18" => %"v15", "L82" => %"v79", "L153" => %"pr.2", "L147" => %"pr.2")]:
    call void $"__GI___close_nocancel_nostatus"(W %"pr.1")
    => ret void;
  @"L25":
    %"v37" = %"v6" +p #24;
    %"chk2" : A = (Check 0 4 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v39" : W = And %"v38", #61440;
    %"v40" : W = (Cmp Eq W) %"v39", #16384
    => br %"v40" ? "L34" : "L36";
  @"L34":
    call void $"__GI___close_nocancel_nostatus"(W %"v15");
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"v48" : L = $"__GI_strlen"(P %"v47");
    %"v50" : L = Add %"v48", #5;
    %"v51" : P = Copy $"_nl_category_name_sizes";
    %"v53" : L = (Ext Sw) %"v2";
    %"v54" = %"v51" +p %"v53";
    %"chk4" : A = (Check 0 1 Read 1) %"v54";
    %"v55" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"v56" : L = (Ext Uw) %"v55";
    %"v57" : L = Add %"v50", %"v56";
    %"v58" : L = Add %"v57", #1;
    %"v59" : P = (Alloc 16) %"v58";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v64" : P = $"__GI_mempcpy"(P %"v59", P %"v62", L %"v48");
    %"v65" : P = Copy $"glibc_loadlocale#str.243";
    call %"v66" : P = $"__GI_mempcpy"(P %"v64", P %"v65", L #5);
    %"iw_1.v2" : P = Copy $"_nl_category_names";
    %"iw_1.v3" : P = Copy $"_nl_category_name_idxs";
    %"iw_1.v6" = %"iw_1.v3" +p %"v53";
    %"chk6" : A = (Check 0 1 Read 1) %"iw_1.v6";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk6";
    %"iw_1.v8" : L = (Ext Uw) %"iw_1.v7";
    %"iw_1.v9" = %"iw_1.v2" +p %"iw_1.v8";
    %"v69" : P = Copy $"_nl_category_name_sizes";
    %"v72" = %"v69" +p %"v53";
    %"chk7" : A = (Check 0 1 Read 1) %"v72";
    %"v73" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v74" : W = Add %"v73", #1;
    %"v75" : L = (Ext Sw) %"v74";
    call %"v76" : P = $"__GI_mempcpy"(P %"v66", P %"iw_1.v9", L %"v75");
    call %"v79" : W = $"__GI___open_nocancel"(P %"v59", W #524288);
    %"v84" : L = (Ext Sw) %"v79";
    %"v85" : W = (Cmp Slt L) %"v84", #0
    => br %"v85" ? "L80" : "L82";
  @"L80":
    => ret void;
  @"L82":
    call %"v91" : W = $"__GI___fstat64"(W %"v79", P %"v6");
    %"v92" : W = (Cmp Slt W) %"v91", #0
    => br %"v92" ? poll "L31" : "L36";
  @"L36" [%"pr.2" : W = phi("L82" => %"v79", "L25" => %"v15")]:
    %"v96" : P = Copy $"__libc_errno";
    %"chk8" : A = (Check 0 4 Read 1) %"v96";
    %"v97" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v98" = %"v6" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v98";
    %"v99" : L = (RawLoad LdL 0) %"chk9";
    call %"v102" : P = $"__GI___mmap"(P #0, L %"v99", W #1, W #2, W %"pr.2", L #0);
    (Flight (a "v109") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v110" : L = Ptoi %"v102";
    %"v111" : L = Ptoi %"v109";
    %"v112" : W = (Cmp Eq L) %"v110", %"v111"
    => br %"v112" ? "L103" : "L105";
  @"L103":
    %"v118" : P = Copy $"__libc_errno";
    %"chk10" : A = (Check 0 4 Read 1) %"v118";
    %"v119" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v120" : L = (Ext Sw) %"v119";
    %"v121" : W = (Cmp Eq L) %"v120", #38
    => br %"v121" ? "L115" : "L105";
  @"L115":
    %"v122" = %"v6" +p #48;
    %"chk11" : A = (Renew 0 8 Read 1) %"chk9", %"v122";
    %"v123" : L = (RawLoad LdL 0) %"chk11";
    call %"v124" : P = $"malloc"(L %"v123");
    %"v129" : L = Ptoi %"v124";
    %"v130" : L = Ptoi #0;
    %"v131" : W = (Cmp Ne L) %"v129", %"v130"
    => br %"v131" ? "L125" : "L105";
  @"L125":
    %"v133" = %"v6" +p #48;
    %"chk12" : A = (Renew 0 8 Read 1) %"chk9", %"v133";
    %"v134" : L = (RawLoad LdL 0) %"chk12"
    => goto "L138";
  @"L138" [%"pr.8" : P = phi("L125" => %"v124", "L149" => %"v162"); %"pr.7" : L = phi("L125" => %"v134", "L149" => %"v165")]:
    %"v142" : W = (Cmp Sgt L) %"pr.7", #0
    => br %"v142" ? "L139" : "L140";
  @"L139":
    call %"v146" : L = $"__GI___read_nocancel"(W %"pr.2", P %"pr.8", L %"pr.7");
    %"v151" : W = (Cmp Sle L) %"v146", #0
    => br %"v151" ? "L147" : "L149";
  @"L147":
    call void $"free"(P %"v124");
    %"v157" : W = (Cmp Eq L) %"v146", #0
    => br %"v157" ? "L153" : poll "L31";
  @"L153":
    %"v158" : P = Copy $"__libc_errno";
    %"chk13" : A = (Check 0 4 Write 1) %"v158";
    store Ww [%"chk13" + 0] <- #22
    => goto poll "L31";
  @"L149":
    %"v162" = %"pr.8" +p %"v146";
    %"v165" : L = Sub %"pr.7", %"v146"
    => goto poll "L138";
  @"L140":
    %"v166" : P = Copy $"__libc_errno";
    %"chk14" : A = (Check 0 4 Write 1) %"v166";
    store Ww [%"chk14" + 0] <- %"v97"
    => goto "L105";
  @"L105" [%"pr.5" : W = phi("L140" => #0, "L115" => #0, "L103" => #1, "L36" => #1); %"pr.3" : P = phi("L140" => %"v124", "L115" => %"v124", "L103" => #0, "L36" => %"v102")]:
    call void $"__GI___close_nocancel_nostatus"(W %"pr.2");
    %"v173" : L = Ptoi %"pr.3";
    %"v174" : L = Ptoi #0;
    %"v175" : W = (Cmp Eq L) %"v173", %"v174"
    => br %"v175" ? "L169" : "L171";
  @"L169":
    => ret void;
  @"L171":
    %"v181" = %"v6" +p #48;
    %"chk15" : A = (Renew 0 8 Read 1) %"chk9", %"v181";
    %"v182" : L = (RawLoad LdL 0) %"chk15";
    call %"v183" : P = $"_nl_intern_locale_data"(W %"v2", P %"pr.3", L %"v182");
    %"v188" : L = Ptoi %"v183";
    %"v190" : W = (Cmp Eq L) %"v188", %"v174"
    => br %"v190" ? "L184" : "L186";
  @"L184":
    => br %"pr.5" ? "L193" : "L195";
  @"L193":
    %"v199" = %"v6" +p #48;
    %"chk16" : A = (Renew 0 8 Read 1) %"chk9", %"v199";
    %"v200" : L = (RawLoad LdL 0) %"chk16";
    call %"v201" : W = $"__GI___munmap"(P %"pr.3", L %"v200")
    => goto "L195";
  @"L195":
    => ret void;
  @"L186":
    %"chk17" : A = (Check 0 8 Write 8) %"v183";
    store.ptr [%"chk17" + 0] <- #0;
    %"v205" = %"v183" +p #24;
    %"chk18" : A = (HalfCheck Upper 0 4 Write 1) %"chk17", %"v205";
    store Ww [%"chk18" + 0] <- %"pr.5";
    %"v208" = %"v0" +p #16;
    %"chk19" : A = (Renew 0 8 Write 8) %"chk0", %"v208";
    store.ptr [%"chk19" + 0] <- %"v183";
    %"v211" = %"v0" +p #8;
    %"chk20" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v211";
    store Ww [%"chk20" + 0] <- #1
    => ret void
} }.

(** This file defines checked IR from glibc’s `iconv/gconv.os` object.
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

Definition fn___gconv : func :=
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

Definition item_glibc_gconv'23str'2e269 : item :=
  (IData (a "glibc_gconv#str.269") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 114); (Item Wb 114); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv'23str'2e270 : item :=
  (IData (a "glibc_gconv#str.270") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_gconv'23str'2e271 : item :=
  (IData (a "glibc_gconv#str.271") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 0)]).

Definition item_glibc_gconv'23str'2e272 : item :=
  (IData (a "glibc_gconv#str.272") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 42); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

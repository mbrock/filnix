(** This file defines checked IR from glibc’s `libio/iogetline.os` object.
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

Definition fn___GI__IO_getline : func :=
  ir_fn{ "export" "__GI__IO_getline"(P %"v0", P %"v2", L %"v4", W %"v6", W %"v8") -> (RClass L) {
  @"start":
    call %"v15" : L = $"__GI__IO_getline_info"(P %"v0", P %"v2", L %"v4", W %"v6", W %"v8", P #0)
    => ret %"v15"
} }.

Definition fn___GI__IO_getline_info : func :=
  ir_fn{ "export" "__GI__IO_getline_info"(P %"v0", P %"v2", L %"v4", W %"v6", W %"v8", P %"v10") -> (RClass L) {
  @"start":
    %"v18" : L = Ptoi %"v10";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Ne L) %"v18", %"v19"
    => br %"v20" ? "L14" : "L16";
  @"L14":
    %"chk0" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk0" + 0] <- #0
    => goto "L16";
  @"L16":
    %"v26" = %"v0" +p #192;
    %"chk1" : A = (Check 0 4 Read 1) %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v29" : L = (Ext Sw) %"v27";
    %"v30" : W = (Cmp Eq L) %"v29", #0
    => br %"v30" ? "L33" : "L77";
  @"L33":
    %"v47" = %"v0" +p #192;
    %"v48" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v49" : W = (Cmp Eq W) %"v48", #0
    => br %"v49" ? "L43" : "L45";
  @"L43":
    %"v51" = %"v0" +p #192;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk1", %"v51";
    store Ww [%"chk3" + 0] <- #4294967295
    => goto "L45";
  @"L45":
    %"v54" = %"v0" +p #192;
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L77";
  @"L77" [%"pr.4" : P = phi("L45" => %"v2", "L16" => %"v2", "L117" => %"v152", "L173" => %"v231"); %"pr.1" : L = phi("L45" => %"v4", "L16" => %"v4", "L117" => %"v156", "L173" => %"v234")]:
    %"v81" : W = (Cmp Ne L) %"pr.1", #0
    => br %"v81" ? "L78" : "L79";
  @"L78":
    %"v84" = %"v0" +p #16;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v87" = %"v0" +p #8;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v89" : L = Ptoi %"v85";
    %"v90" : L = Ptoi %"v88";
    %"v91" : L = Sub %"v89", %"v90";
    %"v96" : W = (Cmp Sle L) %"v91", #0
    => br %"v96" ? "L92" : "L93";
  @"L92":
    call %"v99" : W = $"__GI___uflow"(P %"v0");
    %"v105" : W = (Cmp Eq W) %"v99", #4294967295
    => br %"v105" ? "L100" : "L102";
  @"L100":
    %"v111" : W = (Cmp Ne L) %"v18", #0
    => br %"v111" ? "L106" : "L79";
  @"L106":
    %"chk7" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk7" + 0] <- %"v99"
    => goto "L79";
  @"L102":
    %"v120" : W = (Cmp Eq W) %"v99", %"v6"
    => br %"v120" ? "L115" : "L117";
  @"L115":
    %"v125" : W = (Cmp Sgt W) %"v8", #0
    => br %"v125" ? "L121" : "L122";
  @"L121":
    %"v127" = %"pr.4" +p #1;
    %"v129" : W = (Ext Sb) %"v99";
    %"chk8" : A = (Check 0 1 Write 1) %"pr.4";
    store Wb [%"chk8" + 0] <- %"v129"
    => goto "L123";
  @"L122":
    %"v134" : W = (Cmp Slt W) %"v8", #0
    => br %"v134" ? "L130" : "L123";
  @"L130":
    call %"v137" : W = $"__GI__IO_sputbackc"(P %"v0", W %"v99")
    => goto "L123";
  @"L123" [%"pr.3" : P = phi("L121" => %"v127", "L130" => %"pr.4", "L122" => %"pr.4")]:
    => br %"v125" ? "L140" : "L139";
  @"L139":
    => goto "L140";
  @"L140":
    %"v147" : L = Ptoi %"pr.3";
    %"v148" : L = Ptoi %"v2";
    %"v149" : L = Sub %"v147", %"v148"
    => ret %"v149";
  @"L117":
    %"v152" = %"pr.4" +p #1;
    %"v154" : W = (Ext Sb) %"v99";
    %"chk9" : A = (Check 0 1 Write 1) %"pr.4";
    store Wb [%"chk9" + 0] <- %"v154";
    %"v156" : L = Sub %"pr.1", #1
    => goto poll "L77";
  @"L93":
    %"v163" : W = (Cmp Uge L) %"v91", %"pr.1"
    => br %"v163" ? "L160" : "L159";
  @"L159":
    => goto "L160";
  @"L160" [%"pr.8" : L = phi("L159" => %"v91", "L93" => %"pr.1")]:
    %"v166" = %"v0" +p #8;
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v170" : P = $"__GI_memchr"(P %"v167", W %"v6", L %"pr.8");
    %"v175" : L = Ptoi %"v170";
    %"v177" : W = (Cmp Ne L) %"v175", %"v19"
    => br %"v177" ? "L171" : "L173";
  @"L171":
    %"v181" : L = Ptoi %"pr.4";
    %"v182" : L = Ptoi %"v2";
    %"v183" : L = Sub %"v181", %"v182";
    %"v186" = %"v0" +p #8;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk6", %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v189" : L = Ptoi %"v187";
    %"v190" : L = Sub %"v175", %"v189";
    %"v195" : W = (Cmp Sge W) %"v8", #0
    => br %"v195" ? "L191" : "L193";
  @"L191":
    %"v197" = %"v170" +p #1;
    %"v202" : W = (Cmp Sgt W) %"v8", #0
    => br %"v202" ? "L198" : "L193";
  @"L198":
    %"v204" : L = Add %"v190", #1
    => goto "L193";
  @"L193" [%"pr.11" : P = phi("L198" => %"v197", "L191" => %"v197", "L171" => %"v170"); %"pr.9" : L = phi("L198" => %"v204", "L191" => %"v190", "L171" => %"v190")]:
    %"v207" = %"v0" +p #8;
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk11";
    call %"v210" : P = $"__GI_memcpy"(P %"pr.4", P %"v208", L %"pr.9");
    %"chk13" : A = (Renew 0 8 Write 8) %"chk6", %"v207";
    store.ptr [%"chk13" + 0] <- %"pr.11";
    %"v216" : L = Add %"v183", %"pr.9"
    => ret %"v216";
  @"L173":
    %"v220" = %"v0" +p #8;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk6", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk14";
    call %"v223" : P = $"__GI_memcpy"(P %"pr.4", P %"v221", L %"pr.8");
    %"chk15" : A = (Renew 0 8 Read 8) %"chk6", %"v220";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v228" = %"v226" +p %"pr.8";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk6", %"v220";
    store.ptr [%"chk16" + 0] <- %"v228";
    %"v231" = %"pr.4" +p %"pr.8";
    %"v234" : L = Sub %"pr.1", %"pr.8"
    => goto poll "L77";
  @"L79":
    %"v237" : L = Ptoi %"pr.4";
    %"v238" : L = Ptoi %"v2";
    %"v239" : L = Sub %"v237", %"v238"
    => ret %"v239"
} }.

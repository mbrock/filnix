(** This file defines checked IR from glibc’s `malloc/obstack.os` object.
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

Definition fn___GI__obstack_newchunk : func :=
  ir_fn{ "export" "__GI__obstack_newchunk"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v12" = %"v0" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v15" = %"v0" +p #16;
    %"v16" : P = (RawLoadPointer (-8) load_effects) %"chk1";
    %"v17" : L = Ptoi %"v13";
    %"v18" : L = Ptoi %"v16";
    %"v19" : L = Sub %"v17", %"v18";
    %"v27" : W = (Cmp Ne L) %"v19", #0
    => br %"v27" ? "L23" : "L24";
  @"L23":
    %"v30" : L = (Ext Sw) %"v2";
    %"v31" : L = Add %"v19", %"v30";
    %"v32" : L = Shl %"v31", #1
    => goto "L25";
  @"L24":
    %"v34" : L = (Ext Sw) %"v2"
    => goto "L25";
  @"L25" [%"pr.1" : L = phi("L23" => %"v32", "L24" => %"v34")]:
    %"v37" = %"v0" +p #48;
    %"chk3" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v39" : L = (Ext Sw) %"v38";
    %"v40" : L = Add %"v39", #24;
    %"v41" : L = Add %"pr.1", %"v40";
    %"v46" = %"v0" +p #80;
    %"chk4" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v46";
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v48" : W = Shl %"v47", #31;
    %"v49" : W = Shr %"v48", #31
    => br %"v49" ? "L42" : "L43";
  @"L42":
    %"v51" = %"v0" +p #56;
    %"v52" : P = (RawLoadPointer 32 load_effects) %"chk1";
    %"v54" = %"v0" +p #72;
    %"v55" : P = (RawLoadPointer 48 load_effects) %"chk1";
    %"chk7" : F = CheckFunction %"v52";
    rawcall %"v57" : P = %"chk7"(P %"v55", L %"v41")
    => goto "L44";
  @"L43":
    %"v59" = %"v0" +p #56;
    %"v60" : P = (RawLoadPointer 32 load_effects) %"chk1";
    %"chk9" : F = CheckFunction %"v60";
    rawcall %"v62" : P = %"chk9"(L %"v41")
    => goto "L44";
  @"L44" [%"v63" : P = phi("L42" => %"v57", "L43" => %"v62")]:
    %"v68" : L = Ptoi %"v63";
    %"v70" : W = (Cmp Eq L) %"v68", #0
    => br %"v70" ? "L64" : "L66";
  @"L64":
    %"v71" : P = Copy $"obstack_alloc_failed_handler";
    %"chk10" : A = (Check 0 8 Read 8) %"v71";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : F = CheckFunction %"v72";
    rawcall void %"chk11"()
    => goto "L66";
  @"L66":
    %"v74" = %"v0" +p #8;
    %"chk12" : A = (Renew 0 8 Write 8) %"chk0", %"v74";
    store.ptr [%"chk12" + 0] <- %"v63";
    %"v77" = %"v63" +p #8;
    %"chk13" : A = (Check 0 8 Write 8) %"v77";
    store.ptr [%"chk13" + 0] <- %"v7";
    %"v81" = %"v0" +p #32;
    %"v84" = %"v63" +p %"v41";
    %"chk14" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v81";
    store.ptr [%"chk14" + 0] <- %"v84";
    %"chk15" : A = (HalfCheck Lower 0 8 Write 8) %"chk13", %"v63";
    store.ptr [%"chk15" + 0] <- %"v84";
    %"v87" = %"v63" +p #16
    => goto "L91";
  @"L91" [%"v94" : P = phi("L66" => #0)]:
    => goto "L98";
  @"L98" [%"v101" : P = phi("L91" => #0)]:
    %"v102" : L = Ptoi %"v87";
    %"v103" : L = Ptoi %"v101";
    %"v104" : L = Sub %"v102", %"v103";
    %"v106" = %"v0" +p #48;
    %"chk16" : A = (Renew 0 4 Read 1) %"chk3", %"v106";
    %"v107" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v108" : L = (Ext Sw) %"v107";
    %"v109" : L = Add %"v104", %"v108";
    %"v112" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v113" : W = Xor %"v112", #(-1);
    %"v114" : L = (Ext Sw) %"v113";
    %"v115" : L = And %"v109", %"v114";
    %"v116" = %"v94" +p %"v115";
    %"v117" : L = Ptoi %"v116";
    (Flight (a "iw_1.v9") Sub [(FAddress (t "v87")); (FValue (t "v102"))] (LowerOf (t "v87")));
    %"iw_1.v12" = %"iw_1.v9" +p %"v117";
    %"v123" = %"v0" +p #48;
    %"v124" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v125" : W = Add %"v124", #1;
    %"v126" : W = (Cmp Sge W) %"v125", #16
    => br %"v126" ? "L119" : "L153";
  @"L119":
    %"v128" : L = Shr %"v19", #2;
    %"v129" : L = Sub %"v128", #1
    => goto "L130";
  @"L130" [%"pr.2" : L = phi("L119" => %"v129", "L131" => %"v148")]:
    %"v135" : W = (Cmp Sge L) %"pr.2", #0
    => br %"v135" ? "L131" : "L133";
  @"L131":
    %"v138" : L = Shl %"pr.2", #2;
    %"v139" = %"iw_1.v12" +p %"v138";
    %"v141" = %"v0" +p #16;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v141";
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v145" = %"v142" +p %"v138";
    %"chk20" : A = (Check 0 4 Read 1) %"v145";
    %"v146" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"chk21" : A = (Check 0 4 Write 1) %"v139";
    store Ww [%"chk21" + 0] <- %"v146";
    %"v148" : L = Sub %"pr.2", #1
    => goto poll "L130";
  @"L133":
    %"v151" : L = Shl %"v128", #2
    => goto "L153";
  @"L153" [%"pr.3" : L = phi("L154" => %"v170", "L133" => %"v151", "L98" => #0)]:
    %"v159" : W = (Cmp Slt L) %"pr.3", %"v19"
    => br %"v159" ? "L154" : "L156";
  @"L154":
    %"v162" = %"iw_1.v12" +p %"pr.3";
    %"v164" = %"v0" +p #16;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v167" = %"v165" +p %"pr.3";
    %"chk23" : A = (Check 0 1 Read 1) %"v167";
    %"v168" : W = (RawLoad (LdNarrow Sb) 0) %"chk23";
    %"chk24" : A = (Check 0 1 Write 1) %"v162";
    store Wb [%"chk24" + 0] <- %"v168";
    %"v170" : L = Add %"pr.3", #1
    => goto poll "L153";
  @"L156":
    %"v175" = %"v0" +p #80;
    %"chk25" : A = (Renew 0 4 Read 1) %"chk4", %"v175";
    %"v176" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v177" : W = Shl %"v176", #30;
    %"v178" : W = Shr %"v177", #31;
    %"v179" : W = (Cmp Eq W) %"v178", #0
    => br %"v179" ? "L180" : "L181";
  @"L180":
    %"v183" = %"v0" +p #16;
    %"chk26" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v187" = %"v7" +p #16
    => goto "L191";
  @"L191" [%"v194" : P = phi("L180" => #0)]:
    => goto "L198";
  @"L198" [%"v201" : P = phi("L191" => #0)]:
    %"v202" : L = Ptoi %"v187";
    %"v203" : L = Ptoi %"v201";
    %"v204" : L = Sub %"v202", %"v203";
    %"v206" = %"v0" +p #48;
    %"v207" : W = (RawLoad (LdNarrow Sw) 32) %"chk26";
    %"v208" : L = (Ext Sw) %"v207";
    %"v209" : L = Add %"v204", %"v208";
    %"v212" : W = (RawLoad (LdNarrow Sw) 32) %"chk26";
    %"v213" : W = Xor %"v212", #(-1);
    %"v214" : L = (Ext Sw) %"v213";
    %"v215" : L = And %"v209", %"v214";
    %"v216" = %"v194" +p %"v215";
    %"v217" : L = Ptoi %"v216";
    (Flight (a "iw_2.v9") Sub [(FAddress (t "v187")); (FValue (t "v202"))] (LowerOf (t "v187")));
    %"iw_2.v12" = %"iw_2.v9" +p %"v217";
    %"v219" : L = Ptoi %"v184";
    %"v220" : L = Ptoi %"iw_2.v12";
    %"v221" : W = (Cmp Eq L) %"v219", %"v220"
    => goto "L181";
  @"L181" [%"v223" : W = phi("L156" => #0, "L198" => %"v221")]:
    => br %"v223" ? "L171" : "L173";
  @"L171":
    %"v225" = %"v63" +p #8;
    %"v227" = %"v7" +p #8;
    %"chk29" : A = (Check 0 8 Read 8) %"v227";
    %"v228" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk13", %"v225";
    store.ptr [%"chk30" + 0] <- %"v228";
    %"v236" = %"v0" +p #80;
    %"chk31" : A = (Renew 0 4 Read 1) %"chk4", %"v236";
    %"v237" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v238" : W = Shl %"v237", #31;
    %"v239" : W = Shr %"v238", #31
    => br %"v239" ? "L232" : "L233";
  @"L232":
    %"v241" = %"v0" +p #64;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v241";
    %"v242" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v244" = %"v0" +p #72;
    %"v245" : P = (RawLoadPointer 8 load_effects) %"chk32";
    %"chk34" : F = CheckFunction %"v242";
    rawcall void %"chk34"(P %"v245", P %"v7")
    => goto "L173";
  @"L233":
    %"v248" = %"v0" +p #64;
    %"chk35" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v248";
    %"v249" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : F = CheckFunction %"v249";
    rawcall void %"chk36"(P %"v7")
    => goto "L173";
  @"L173":
    %"v252" = %"v0" +p #16;
    %"chk37" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v252";
    store.ptr [%"chk37" + 0] <- %"iw_1.v12";
    %"v255" = %"v0" +p #24;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk37", %"v252";
    %"v258" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v260" = %"v258" +p %"v19";
    %"chk39" : A = (Renew 0 8 Write 8) %"chk1", %"v255";
    store.ptr [%"chk39" + 0] <- %"v260";
    %"v262" = %"v0" +p #80;
    %"chk40" : A = (Renew 0 4 Read 1) %"chk4", %"v262";
    %"v263" : W = (RawLoad (LdNarrow Uw) 0) %"chk40";
    %"v264" : W = And %"v263", #4294967293;
    %"chk41" : A = (Renew 0 4 Write 1) %"chk4", %"v262";
    store Ww [%"chk41" + 0] <- %"v264"
    => ret void
} }.

Definition fn_glibc_obstack'23print_and_abort : func :=
  ir_fn{ "local" "glibc_obstack#print_and_abort"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_obstack#str.148";
    %"v1" : P = Copy $"__GI__libc_intl_domainname";
    %"v2" : P = Copy $"glibc_obstack#str.149";
    call %"v3" : P = $"__GI___dcgettext"(P %"v1", P %"v2", W #5);
    call %"v4" : W = $"__fxprintf"(P #0, P %"v0", P %"v3");
    %"v5" : P = Copy $"obstack_exit_failure";
    %"chk0" : A = (Check 0 4 Read 1) %"v5";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call void $"__GI_exit"(W %"v6")
    => ret void
} }.

Definition item_glibc_obstack'23str'2e148 : item :=
  (IData (a "glibc_obstack#str.148") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_obstack'23str'2e149 : item :=
  (IData (a "glibc_obstack#str.149") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 104); (Item Wb 97); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition item_obstack_alloc_failed_handler : item :=
  (IData (a "obstack_alloc_failed_handler") LExport 8 [(Sym (a "glibc_obstack#print_and_abort") 0)]).

Definition item_obstack_exit_failure : item :=
  (IData (a "obstack_exit_failure") LExport 4 [(Item Ww 1)]).

(** This file defines checked IR from glibc’s `intl/l10nflist.os` object.
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

Definition fn__nl_make_l10nflist : func :=
  ir_fn{ "export" "_nl_make_l10nflist"(P %"v0", P %"v2", L %"v4", W %"v6", P %"v8", P %"v10", P %"v12", P %"v14", P %"v16", P %"v18", W %"v20") -> (RClass P) {
  @"start":
    call %"v30" : L = $"__GI_strlen"(P %"v8");
    %"v31" : L = Add %"v4", %"v30";
    %"v36" : W = And %"v6", #4;
    %"v37" : W = (Cmp Ne W) %"v36", #0
    => br %"v37" ? "L32" : "L34";
  @"L32":
    call %"v39" : L = $"__GI_strlen"(P %"v10");
    %"v40" : L = Add %"v39", #1
    => goto "L34";
  @"L34" [%"v41" : L = phi("L32" => %"v40", "start" => #0)]:
    %"v42" : L = Add %"v31", %"v41";
    %"v47" : W = And %"v6", #2;
    %"v48" : W = (Cmp Ne W) %"v47", #0
    => br %"v48" ? "L43" : "L45";
  @"L43":
    call %"v50" : L = $"__GI_strlen"(P %"v12");
    %"v51" : L = Add %"v50", #1
    => goto "L45";
  @"L45" [%"v52" : L = phi("L43" => %"v51", "L34" => #0)]:
    %"v53" : L = Add %"v42", %"v52";
    %"v58" : W = And %"v6", #1
    => br %"v58" ? "L54" : "L56";
  @"L54":
    call %"v61" : L = $"__GI_strlen"(P %"v14");
    %"v62" : L = Add %"v61", #1
    => goto "L56";
  @"L56" [%"v63" : L = phi("L54" => %"v62", "L45" => #0)]:
    %"v64" : L = Add %"v53", %"v63";
    %"v69" : W = And %"v6", #8;
    %"v70" : W = (Cmp Ne W) %"v69", #0
    => br %"v70" ? "L65" : "L67";
  @"L65":
    call %"v72" : L = $"__GI_strlen"(P %"v16");
    %"v73" : L = Add %"v72", #1
    => goto "L67";
  @"L67" [%"v74" : L = phi("L65" => %"v73", "L56" => #0)]:
    %"v75" : L = Add %"v64", %"v74";
    %"v76" : L = Add %"v75", #1;
    call %"v78" : L = $"__GI_strlen"(P %"v18");
    %"v79" : L = Add %"v76", %"v78";
    %"v80" : L = Add %"v79", #1;
    call %"v81" : P = $"malloc"(L %"v80");
    %"v86" : L = Ptoi %"v81";
    %"v87" : L = Ptoi #0;
    %"v88" : W = (Cmp Eq L) %"v86", %"v87"
    => br %"v88" ? "L82" : "L84";
  @"L82":
    => ret #0;
  @"L84":
    call %"v93" : P = $"__GI_memcpy"(P %"v81", P %"v2", L %"v4");
    call void $"glibc_l10nflist#argz_stringify__"(P %"v81", L %"v4", W #58);
    %"v98" : L = Sub %"v4", #1;
    %"v99" = %"v81" +p %"v98";
    %"v101" = %"v99" +p #1;
    %"chk0" : A = (Check 0 1 Write 1) %"v99";
    store Wb [%"chk0" + 0] <- #47;
    call %"v104" : P = $"__GI_stpcpy"(P %"v101", P %"v8")
    => br %"v37" ? "L105" : "L107";
  @"L105":
    %"v112" = %"v104" +p #1;
    %"chk1" : A = (Check 0 1 Write 1) %"v104";
    store Wb [%"chk1" + 0] <- #95;
    call %"v115" : P = $"__GI_stpcpy"(P %"v112", P %"v10")
    => goto "L107";
  @"L107" [%"pr.5" : P = phi("L105" => %"v115", "L84" => %"v104")]:
    => br %"v48" ? "L116" : "L118";
  @"L116":
    %"v123" = %"pr.5" +p #1;
    %"chk2" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk2" + 0] <- #46;
    call %"v126" : P = $"__GI_stpcpy"(P %"v123", P %"v12")
    => goto "L118";
  @"L118" [%"pr.6" : P = phi("L116" => %"v126", "L107" => %"pr.5")]:
    => br %"v58" ? "L127" : "L129";
  @"L127":
    %"v134" = %"pr.6" +p #1;
    %"chk3" : A = (Check 0 1 Write 1) %"pr.6";
    store Wb [%"chk3" + 0] <- #46;
    call %"v137" : P = $"__GI_stpcpy"(P %"v134", P %"v14")
    => goto "L129";
  @"L129" [%"pr.7" : P = phi("L127" => %"v137", "L118" => %"pr.6")]:
    => br %"v70" ? "L138" : "L140";
  @"L138":
    %"v145" = %"pr.7" +p #1;
    %"chk4" : A = (Check 0 1 Write 1) %"pr.7";
    store Wb [%"chk4" + 0] <- #64;
    call %"v148" : P = $"__GI_stpcpy"(P %"v145", P %"v16")
    => goto "L140";
  @"L140" [%"pr.8" : P = phi("L138" => %"v148", "L129" => %"pr.7")]:
    %"v150" = %"pr.8" +p #1;
    %"chk5" : A = (Check 0 1 Write 1) %"pr.8";
    store Wb [%"chk5" + 0] <- #47;
    call %"v153" : P = $"__GI_stpcpy"(P %"v150", P %"v18");
    %"chk6" : A = (Check 0 8 Read 8) %"v0";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk6"
    => goto "L156";
  @"L156" [%"pr.3" : P = phi("L140" => %"v155", "L166" => %"v192"); %"pr.1" : P = phi("L140" => #0, "L166" => %"pr.2")]:
    %"v161" : L = Ptoi %"pr.3";
    %"v163" : W = (Cmp Ne L) %"v161", %"v87"
    => br %"v163" ? "L157" : "L159";
  @"L157":
    %"chk7" : A = (Check 0 8 Read 8) %"pr.3";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v169" : L = Ptoi %"v168";
    %"v171" : W = (Cmp Ne L) %"v169", %"v87"
    => br %"v171" ? "L164" : "L166";
  @"L164":
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call %"v176" : W = $"__GI_strcmp"(P %"v174", P %"v81");
    %"v181" : W = (Cmp Eq W) %"v176", #0
    => br %"v181" ? "L159" : "L179";
  @"L179":
    %"v187" : W = (Cmp Slt W) %"v176", #0
    => br %"v187" ? "L159" : "L166";
  @"L166" [%"pr.2" : P = phi("L179" => %"pr.3", "L157" => %"pr.1")]:
    %"v191" = %"pr.3" +p #24;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"v191";
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk9"
    => goto poll "L156";
  @"L159" [%"pr.4" : P = phi("L156" => %"pr.3", "L164" => %"pr.3", "L179" => #0)]:
    %"v197" : L = Ptoi %"pr.4";
    %"v199" : W = (Cmp Ne L) %"v197", %"v87"
    => br %"v199" ? "L201" : "L200";
  @"L200":
    %"v203" : W = (Cmp Eq W) %"v20", #0
    => goto "L201";
  @"L201" [%"v205" : W = phi("L159" => #1, "L200" => %"v203")]:
    => br %"v205" ? "L193" : "L195";
  @"L193":
    call void $"free"(P %"v81")
    => ret %"pr.4";
  @"L195":
    call %"v211" : L = $"glibc_l10nflist#argz_count__"(P %"v2", L %"v4");
    call %"v213" : W = $"glibc_l10nflist#pop"(W %"v6");
    %"v214" : W = Shl #1, %"v213";
    %"v215" : L = (Ext Sw) %"v214";
    %"v216" : L = Mul %"v211", %"v215";
    %"v217" : L = Shl %"v216", #3;
    %"v218" : L = Add %"v217", #40;
    call %"v219" : P = $"malloc"(L %"v218");
    %"v224" : L = Ptoi %"v219";
    %"v226" : W = (Cmp Eq L) %"v224", %"v87"
    => br %"v226" ? "L220" : "L222";
  @"L220":
    call void $"free"(P %"v81")
    => ret #0;
  @"L222":
    %"chk10" : A = (Check 0 8 Write 8) %"v219";
    store.ptr [%"chk10" + 0] <- %"v81";
    %"v232" = %"v219" +p #8;
    call %"v235" : L = $"glibc_l10nflist#argz_count__"(P %"v2", L %"v4");
    %"v236" : W = (Cmp Ne L) %"v235", #1
    => br %"v236" ? "L238" : "L237";
  @"L237":
    => br %"v48" ? "L242" : "L238";
  @"L242":
    => goto "L238";
  @"L238" [%"v250" : W = phi("L222" => #1, "L237" => #0, "L242" => %"v58")]:
    %"chk11" : A = (HalfCheck Upper 0 4 Write 1) %"chk10", %"v232";
    store Ww [%"chk11" + 0] <- %"v250";
    %"v252" = %"v219" +p #16;
    %"chk12" : A = (HalfCheck Upper 0 8 Write 8) %"chk10", %"v252";
    store.ptr [%"chk12" + 0] <- #0;
    %"v257" : L = Ptoi %"pr.1";
    %"v259" : W = (Cmp Eq L) %"v257", %"v87"
    => br %"v259" ? "L253" : "L254";
  @"L253":
    %"v261" = %"v219" +p #24;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk6", %"v0";
    %"v263" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (HalfCheck Upper 0 8 Write 8) %"chk10", %"v261";
    store.ptr [%"chk14" + 0] <- %"v263";
    %"chk15" : A = (Renew 0 8 Write 8) %"chk6", %"v0";
    store.ptr [%"chk15" + 0] <- %"v219"
    => goto "L255";
  @"L254":
    %"v267" = %"v219" +p #24;
    %"v269" = %"pr.1" +p #24;
    %"chk16" : A = (Check 0 8 Read 8) %"v269";
    %"v270" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk10", %"v267";
    store.ptr [%"chk17" + 0] <- %"v270";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk16", %"v269";
    store.ptr [%"chk18" + 0] <- %"v219"
    => goto "L255";
  @"L255":
    call %"v279" : L = $"glibc_l10nflist#argz_count__"(P %"v2", L %"v4");
    %"v280" : W = (Cmp Eq L) %"v279", #1
    => br %"v280" ? "L274" : "L285";
  @"L274":
    %"v282" : W = Sub %"v6", #1
    => goto "L285";
  @"L285" [%"pr.12" : W = phi("L293" => %"v330", "L274" => %"v282", "L255" => %"v6"); %"pr.9" : L = phi("L293" => %"pr.10", "L274" => #0, "L255" => #0)]:
    %"v290" : W = (Cmp Sge W) %"pr.12", #0
    => br %"v290" ? "L286" : "L288";
  @"L286":
    %"v296" : W = Xor %"v6", #(-1);
    %"v297" : W = And %"pr.12", %"v296";
    %"v298" : W = (Cmp Eq W) %"v297", #0
    => br %"v298" ? "L300" : "L293";
  @"L300" [%"pr.13" : P = phi("L301" => %"v306", "L286" => #0); %"pr.11" : L = phi("L301" => %"v313", "L286" => %"pr.9")]:
    call %"v306" : P = $"__GI___argz_next"(P %"v2", L %"v4", P %"pr.13");
    %"v307" : L = Ptoi %"v306";
    %"v309" : W = (Cmp Ne L) %"v307", %"v87"
    => br %"v309" ? "L301" : "L293";
  @"L301":
    %"v311" = %"v219" +p #32;
    %"v313" : L = Add %"pr.11", #1;
    %"v314" : L = Shl %"pr.11", #3;
    %"v315" = %"v311" +p %"v314";
    call %"v319" : L = $"__GI_strlen"(P %"v306");
    %"v320" : L = Add %"v319", #1;
    call %"v328" : P = $"_nl_make_l10nflist"(P %"v0", P %"v306", L %"v320", W %"pr.12", P %"v8", P %"v10", P %"v12", P %"v14", P %"v16", P %"v18", W #1);
    %"chk19" : A = (Check 0 8 Write 8) %"v315";
    store.ptr [%"chk19" + 0] <- %"v328"
    => goto poll "L300";
  @"L293" [%"pr.10" : L = phi("L300" => %"pr.11", "L286" => %"pr.9")]:
    %"v330" : W = Sub %"pr.12", #1
    => goto poll "L285";
  @"L288":
    %"v332" = %"v219" +p #32;
    %"v334" : L = Shl %"pr.9", #3;
    %"v335" = %"v332" +p %"v334";
    %"chk20" : A = (Check 0 8 Write 8) %"v335";
    store.ptr [%"chk20" + 0] <- #0
    => ret %"v219"
} }.

Definition fn__nl_normalize_codeset : func :=
  ir_fn{ "export" "_nl_normalize_codeset"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    => goto "L9";
  @"L9" [%"pr.11" : L = phi("L18" => %"v53", "start" => #0); %"pr.5" : W = phi("L18" => %"pr.3", "start" => #1); %"pr.2" : L = phi("L18" => %"pr.1", "start" => #0)]:
    %"v15" : W = (Cmp Ult L) %"pr.11", %"v2"
    => br %"v15" ? "L10" : "L12";
  @"L10":
    %"v19" : P = Copy $"_nl_C_locobj";
    %"v20" = %"v19" +p #104;
    %"chk0" : A = (Check 0 8 Read 8) %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v24" = %"v0" +p %"pr.11";
    %"chk1" : A = (Check 0 1 Read 1) %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v26" : W = (Ext Ub) %"v25";
    %"v27" : L = (Ext Sw) %"v26";
    %"v28" : L = Shl %"v27", #1;
    %"v29" = %"v21" +p %"v28";
    %"chk2" : A = (Check 0 2 Read 1) %"v29";
    %"v30" : W = (RawLoad (LdNarrow Uh) 0) %"chk2";
    %"v31" : W = And %"v30", #8
    => br %"v31" ? "L16" : "L18";
  @"L16":
    %"v33" : L = Add %"pr.2", #1;
    %"v41" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v42" : W = (Ext Ub) %"v41";
    %"v44" : W = (Cmp Sge W) %"v42", #48
    => br %"v44" ? "L45" : "L46";
  @"L45":
    %"v48" : W = (Cmp Sle W) %"v42", #57
    => goto "L46";
  @"L46" [%"v50" : W = phi("L16" => #0, "L45" => %"v48")]:
    => br %"v50" ? "L35" : "L18";
  @"L35":
    => goto "L18";
  @"L18" [%"pr.3" : W = phi("L35" => %"pr.5", "L46" => #0, "L10" => %"pr.5"); %"pr.1" : L = phi("L35" => %"v33", "L46" => %"v33", "L10" => %"pr.2")]:
    %"v53" : L = Add %"pr.11", #1
    => goto poll "L9";
  @"L12":
    => br %"pr.5" ? "L56" : "L55";
  @"L55":
    => goto "L56";
  @"L56" [%"v58" : W = phi("L55" => #0, "L12" => #3)]:
    %"v60" : L = (Ext Sw) %"v58";
    %"v61" : L = Add %"v60", %"pr.2";
    %"v62" : L = Add %"v61", #1;
    call %"v63" : P = $"malloc"(L %"v62");
    %"v68" : L = Ptoi %"v63";
    %"v69" : L = Ptoi #0;
    %"v70" : W = (Cmp Ne L) %"v68", %"v69"
    => br %"v70" ? "L64" : "L66";
  @"L64":
    => br %"pr.5" ? "L71" : "L79";
  @"L71":
    %"v76" : P = Copy $"glibc_l10nflist#str.130";
    call %"v77" : P = $"__GI_stpcpy"(P %"v63", P %"v76")
    => goto "L79";
  @"L79" [%"pr.10" : L = phi("L88" => %"v185", "L71" => #0, "L64" => #0); %"pr.8" : P = phi("L88" => %"pr.9", "L71" => %"v77", "L64" => %"v63")]:
    %"v85" : W = (Cmp Ult L) %"pr.10", %"v2"
    => br %"v85" ? "L80" : "L82";
  @"L80":
    %"v89" : P = Copy $"_nl_C_locobj";
    %"v90" = %"v89" +p #104;
    %"chk4" : A = (Check 0 8 Read 8) %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v94" = %"v0" +p %"pr.10";
    %"chk5" : A = (Check 0 1 Read 1) %"v94";
    %"v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v96" : W = (Ext Ub) %"v95";
    %"v97" : L = (Ext Sw) %"v96";
    %"v98" : L = Shl %"v97", #1;
    %"v99" = %"v91" +p %"v98";
    %"chk6" : A = (Check 0 2 Read 1) %"v99";
    %"v100" : W = (RawLoad (LdNarrow Uh) 0) %"chk6";
    %"v101" : W = And %"v100", #1024
    => br %"v101" ? "L86" : "L87";
  @"L86":
    %"v103" = %"pr.8" +p #1;
    %"v147" : P = Copy $"_nl_C_locobj";
    %"v148" = %"v147" +p #112;
    %"chk7" : A = (Check 0 8 Read 8) %"v148";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 1 Read 1) %"chk5", %"v94";
    %"v153" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v154" : W = (Ext Ub) %"v153";
    %"v155" : L = (Ext Sw) %"v154";
    %"v156" : L = Shl %"v155", #2;
    %"v157" = %"v149" +p %"v156";
    %"chk9" : A = (Check 0 4 Read 1) %"v157";
    %"v158" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v160" : W = (Ext Sb) %"v158";
    %"chk10" : A = (Check 0 1 Write 1) %"pr.8";
    store Wb [%"chk10" + 0] <- %"v160"
    => goto "L88";
  @"L87":
    %"v168" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v169" : W = (Ext Ub) %"v168";
    %"v171" : W = (Cmp Sge W) %"v169", #48
    => br %"v171" ? "L172" : "L173";
  @"L172":
    %"v175" : W = (Cmp Sle W) %"v169", #57
    => goto "L173";
  @"L173" [%"v177" : W = phi("L87" => #0, "L172" => %"v175")]:
    => br %"v177" ? "L161" : "L88";
  @"L161":
    %"v179" = %"pr.8" +p #1;
    %"v183" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"chk13" : A = (Check 0 1 Write 1) %"pr.8";
    store Wb [%"chk13" + 0] <- %"v183"
    => goto "L88";
  @"L88" [%"pr.9" : P = phi("L86" => %"v103", "L161" => %"v179", "L173" => %"pr.8")]:
    %"v185" : L = Add %"pr.10", #1
    => goto poll "L79";
  @"L82":
    %"chk14" : A = (Check 0 1 Write 1) %"pr.8";
    store Wb [%"chk14" + 0] <- #0
    => goto "L66";
  @"L66":
    => ret %"v63"
} }.

Definition fn_glibc_l10nflist'23argz_count__ : func :=
  ir_fn{ "local" "glibc_l10nflist#argz_count__"(P %"v0", L %"v2") -> (RClass L) {
  @"start":
    => goto "L5";
  @"L5" [%"pr.3" : L = phi("L6" => %"v22", "start" => #0); %"pr.2" : L = phi("L6" => %"v20", "start" => %"v2"); %"pr.1" : P = phi("L6" => %"v16", "start" => %"v0")]:
    %"v9" : W = (Cmp Ugt L) %"pr.2", #0
    => br %"v9" ? "L6" : "L7";
  @"L6":
    call %"v12" : L = $"__GI_strlen"(P %"pr.1");
    %"v15" : L = Add %"v12", #1;
    %"v16" = %"pr.1" +p %"v15";
    %"v20" : L = Sub %"pr.2", %"v15";
    %"v22" : L = Add %"pr.3", #1
    => goto poll "L5";
  @"L7":
    => ret %"pr.3"
} }.

Definition fn_glibc_l10nflist'23argz_stringify__ : func :=
  ir_fn{ "local" "glibc_l10nflist#argz_stringify__"(P %"v0", L %"v2", W %"v4") -> RVoid {
  @"start":
    => goto "L6";
  @"L6" [%"pr.3" : L = phi("start" => %"v2", "L21" => %"v20", "L7" => %"v20"); %"pr.2" : P = phi("start" => %"v0", "L21" => %"v27", "L7" => %"v16")]:
    %"v10" : W = (Cmp Ugt L) %"pr.3", #0
    => br %"v10" ? "L7" : "L8";
  @"L7":
    call %"v13" : L = $"__GI_strlen"(P %"pr.2");
    %"v16" = %"pr.2" +p %"v13";
    %"v19" : L = Add %"v13", #1;
    %"v20" : L = Sub %"pr.3", %"v19";
    %"v25" : W = (Cmp Ugt L) %"v20", #0
    => br %"v25" ? "L21" : poll "L6";
  @"L21":
    %"v27" = %"v16" +p #1;
    %"v29" : W = (Ext Sb) %"v4";
    %"chk0" : A = (Check 0 1 Write 1) %"v16";
    store Wb [%"chk0" + 0] <- %"v29"
    => goto poll "L6";
  @"L8":
    => ret void
} }.

Definition fn_glibc_l10nflist'23pop : func :=
  ir_fn{ "local" "glibc_l10nflist#pop"(W %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" : L = (Ext Uw) %"v0";
    %"iw_1.v4" : L = Shr %"iw_1.v3", #1;
    %"iw_1.v5" : L = And %"iw_1.v4", #6148914691236517205;
    %"iw_1.v6" : L = Sub %"iw_1.v3", %"iw_1.v5";
    %"iw_1.v7" : L = And %"iw_1.v6", #3689348814741910323;
    %"iw_1.v8" : L = Shr %"iw_1.v6", #2;
    %"iw_1.v9" : L = And %"iw_1.v8", #3689348814741910323;
    %"iw_1.v10" : L = Add %"iw_1.v7", %"iw_1.v9";
    %"iw_1.v11" : L = Shr %"iw_1.v10", #4;
    %"iw_1.v12" : L = Add %"iw_1.v10", %"iw_1.v11";
    %"iw_1.v13" : L = And %"iw_1.v12", #1085102592571150095;
    %"iw_1.v14" : L = Mul %"iw_1.v13", #72340172838076673;
    %"iw_1.v15" : L = Shr %"iw_1.v14", #56
    => goto "iw_1.join";
  @"iw_1.join" [%"v3" : W = phi("start" => %"iw_1.v15")]:
    => ret %"v3"
} }.

Definition item_glibc_l10nflist'23str'2e130 : item :=
  (IData (a "glibc_l10nflist#str.130") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 115); (Item Wb 111); (Item Wb 0)]).

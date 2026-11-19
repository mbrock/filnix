(** This file defines checked IR from glibc’s `stdlib/mul_n.os` object.
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

Definition fn___mpn_impn_mul_n : func :=
  ir_fn{ "export" "__mpn_impn_mul_n"(P %"v0", P %"v2", P %"v4", L %"v6", P %"v8") -> RVoid {
  @"start":
    %"v14" : L = And %"v6", #1;
    %"v15" : W = (Cmp Ne L) %"v14", #0
    => br %"v15" ? "L10" : "L11";
  @"L10":
    %"v18" : L = Sub %"v6", #1;
    %"v27" : W = (Cmp Slt L) %"v18", #32
    => br %"v27" ? "L23" : "L24";
  @"L23":
    call void $"__mpn_impn_mul_n_basecase"(P %"v0", P %"v2", P %"v4", L %"v18")
    => goto "L22";
  @"L24":
    call void $"__mpn_impn_mul_n"(P %"v0", P %"v2", P %"v4", L %"v18", P %"v8")
    => goto "L22";
  @"L22":
    %"v39" : L = Shl %"v18", #3;
    %"v40" = %"v0" +p %"v39";
    %"v46" = %"v4" +p %"v39";
    %"chk0" : A = (Check 0 8 Read 1) %"v46";
    %"v47" : L = (RawLoad LdL 0) %"chk0";
    call %"v48" : L = $"__mpn_addmul_1"(P %"v40", P %"v2", L %"v18", L %"v47");
    %"v52" : L = Add %"v18", %"v18";
    %"v53" : L = Shl %"v52", #3;
    %"v54" = %"v0" +p %"v53";
    %"chk1" : A = (Check 0 8 Write 1) %"v54";
    store Wl [%"chk1" + 0] <- %"v48";
    %"v65" = %"v2" +p %"v39";
    %"chk2" : A = (Check 0 8 Read 1) %"v65";
    %"v66" : L = (RawLoad LdL 0) %"chk2";
    call %"v67" : L = $"__mpn_addmul_1"(P %"v40", P %"v4", L %"v6", L %"v66");
    %"v71" : L = Add %"v18", %"v6";
    %"v72" : L = Shl %"v71", #3;
    %"v73" = %"v0" +p %"v72";
    %"chk3" : A = (Check 0 8 Write 1) %"v73";
    store Wl [%"chk3" + 0] <- %"v67"
    => goto "L12";
  @"L11":
    %"v77" : L = Sar %"v6", #1;
    %"v87" : W = (Cmp Slt L) %"v77", #32
    => br %"v87" ? "L83" : "L84";
  @"L83":
    %"v90" : L = Shl %"v6", #3;
    %"v91" = %"v0" +p %"v90";
    %"v94" : L = Shl %"v77", #3;
    %"v95" = %"v2" +p %"v94";
    %"v99" = %"v4" +p %"v94";
    call void $"__mpn_impn_mul_n_basecase"(P %"v91", P %"v95", P %"v99", L %"v77")
    => goto "L82";
  @"L84":
    %"v103" : L = Shl %"v6", #3;
    %"v104" = %"v0" +p %"v103";
    %"v107" : L = Shl %"v77", #3;
    %"v108" = %"v2" +p %"v107";
    %"v112" = %"v4" +p %"v107";
    call void $"__mpn_impn_mul_n"(P %"v104", P %"v108", P %"v112", L %"v77", P %"v8")
    => goto "L82";
  @"L82":
    %"v120" : L = Shl %"v77", #3;
    %"v121" = %"v2" +p %"v120";
    call %"v124" : W = $"__mpn_cmp"(P %"v121", P %"v2", L %"v77");
    %"v125" : W = (Cmp Sge W) %"v124", #0
    => br %"v125" ? "L115" : "L116";
  @"L115":
    call %"v133" : L = $"__mpn_sub_n"(P %"v0", P %"v121", P %"v2", L %"v77")
    => goto "L117";
  @"L116":
    call %"v141" : L = $"__mpn_sub_n"(P %"v0", P %"v2", P %"v121", L %"v77")
    => goto "L117";
  @"L117" [%"pr.2" : W = phi("L115" => #0, "L116" => #1)]:
    %"v148" = %"v4" +p %"v120";
    call %"v151" : W = $"__mpn_cmp"(P %"v148", P %"v4", L %"v77");
    %"v152" : W = (Cmp Sge W) %"v151", #0
    => br %"v152" ? "L142" : "L143";
  @"L142":
    %"v156" = %"v0" +p %"v120";
    call %"v163" : L = $"__mpn_sub_n"(P %"v156", P %"v148", P %"v4", L %"v77");
    %"v165" : W = Xor %"pr.2", #1
    => goto "L144";
  @"L143":
    %"v169" = %"v0" +p %"v120";
    call %"v176" : L = $"__mpn_sub_n"(P %"v169", P %"v4", P %"v148", L %"v77")
    => goto "L144";
  @"L144" [%"pr.3" : W = phi("L142" => %"v165", "L143" => %"pr.2")]:
    => br %"v87" ? "L180" : "L181";
  @"L180":
    %"v190" = %"v0" +p %"v120";
    call void $"__mpn_impn_mul_n_basecase"(P %"v8", P %"v0", P %"v190", L %"v77")
    => goto "L207";
  @"L181":
    %"v197" = %"v0" +p %"v120";
    %"v201" : L = Shl %"v6", #3;
    %"v202" = %"v8" +p %"v201";
    call void $"__mpn_impn_mul_n"(P %"v8", P %"v0", P %"v197", L %"v77", P %"v202")
    => goto "L207";
  @"L207" [%"pr.4" : L = phi("L208" => %"v230", "L180" => #0, "L181" => #0)]:
    %"v213" : W = (Cmp Slt L) %"pr.4", %"v77"
    => br %"v213" ? "L208" : "L205";
  @"L208":
    %"v217" = %"v0" +p %"v120";
    %"v219" : L = Shl %"pr.4", #3;
    %"v220" = %"v217" +p %"v219";
    %"v223" : L = Shl %"v6", #3;
    %"v224" = %"v0" +p %"v223";
    %"v227" = %"v224" +p %"v219";
    %"chk4" : A = (Check 0 8 Read 1) %"v227";
    %"v228" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (Check 0 8 Write 1) %"v220";
    store Wl [%"chk5" + 0] <- %"v228";
    %"v230" : L = Add %"pr.4", #1
    => goto poll "L207";
  @"L205":
    %"v233" : L = Shl %"v6", #3;
    %"v234" = %"v0" +p %"v233";
    %"v245" = %"v234" +p %"v120";
    call %"v247" : L = $"__mpn_add_n"(P %"v234", P %"v234", P %"v245", L %"v77")
    => br %"pr.3" ? "L248" : "L249";
  @"L248":
    %"v256" = %"v0" +p %"v120";
    call %"v263" : L = $"__mpn_sub_n"(P %"v256", P %"v256", P %"v8", L %"v6");
    %"v264" : L = Sub %"v247", %"v263"
    => goto "L250";
  @"L249":
    %"v269" = %"v0" +p %"v120";
    call %"v276" : L = $"__mpn_add_n"(P %"v269", P %"v269", P %"v8", L %"v6");
    %"v277" : L = Add %"v247", %"v276"
    => goto "L250";
  @"L250" [%"pr.1" : L = phi("L248" => %"v264", "L249" => %"v277")]:
    => br %"v87" ? "L281" : "L282";
  @"L281":
    call void $"__mpn_impn_mul_n_basecase"(P %"v8", P %"v2", P %"v4", L %"v77")
    => goto "L280";
  @"L282":
    %"v297" = %"v8" +p %"v233";
    call void $"__mpn_impn_mul_n"(P %"v8", P %"v2", P %"v4", L %"v77", P %"v297")
    => goto "L280";
  @"L280":
    %"v302" = %"v0" +p %"v120";
    call %"v309" : L = $"__mpn_add_n"(P %"v302", P %"v302", P %"v8", L %"v6");
    %"v310" : L = Add %"pr.1", %"v309";
    %"v315" : W = (Cmp Ne L) %"v310", #0
    => br %"v315" ? "L311" : "L337";
  @"L311":
    %"v322" = %"v302" +p %"v233";
    call %"v332" : L = $"glibc_mul_n#__mpn_add_1.gnu_inline"(P %"v322", P %"v322", L %"v77", L %"v310")
    => goto "L337";
  @"L337" [%"pr.5" : L = phi("L338" => %"v354", "L311" => #0, "L280" => #0)]:
    %"v343" : W = (Cmp Slt L) %"pr.5", %"v77"
    => br %"v343" ? "L338" : "L335";
  @"L338":
    %"v346" : L = Shl %"pr.5", #3;
    %"v347" = %"v0" +p %"v346";
    %"v351" = %"v8" +p %"v346";
    %"chk6" : A = (Check 0 8 Read 1) %"v351";
    %"v352" : L = (RawLoad LdL 0) %"chk6";
    %"chk7" : A = (Check 0 8 Write 1) %"v347";
    store Wl [%"chk7" + 0] <- %"v352";
    %"v354" : L = Add %"pr.5", #1
    => goto poll "L337";
  @"L335":
    %"v366" = %"v8" +p %"v120";
    call %"v368" : L = $"__mpn_add_n"(P %"v302", P %"v302", P %"v366", L %"v77");
    %"v373" : W = (Cmp Ne L) %"v368", #0
    => br %"v373" ? "L369" : "L12";
  @"L369":
    call %"v383" : L = $"glibc_mul_n#__mpn_add_1.gnu_inline"(P %"v234", P %"v234", L %"v6", L #1)
    => goto "L12";
  @"L12":
    => ret void
} }.

Definition fn___mpn_impn_mul_n_basecase : func :=
  ir_fn{ "export" "__mpn_impn_mul_n_basecase"(P %"v0", P %"v2", P %"v4", L %"v6") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v4";
    %"v13" : L = (RawLoad LdL 0) %"chk0";
    %"v18" : W = (Cmp Ule L) %"v13", #1
    => br %"v18" ? "L14" : "L15";
  @"L14":
    %"v23" : W = (Cmp Eq L) %"v13", #1
    => br %"v23" ? "L28" : "L50";
  @"L28" [%"pr.6" : L = phi("L29" => %"v45", "L14" => #0)]:
    %"v34" : W = (Cmp Slt L) %"pr.6", %"v6"
    => br %"v34" ? "L29" : "L16";
  @"L29":
    %"v37" : L = Shl %"pr.6", #3;
    %"v38" = %"v0" +p %"v37";
    %"v42" = %"v2" +p %"v37";
    %"chk1" : A = (Check 0 8 Read 1) %"v42";
    %"v43" : L = (RawLoad LdL 0) %"chk1";
    %"chk2" : A = (Check 0 8 Write 1) %"v38";
    store Wl [%"chk2" + 0] <- %"v43";
    %"v45" : L = Add %"pr.6", #1
    => goto poll "L28";
  @"L50" [%"pr.7" : L = phi("L51" => %"v62", "L14" => #0)]:
    %"v56" : W = (Cmp Slt L) %"pr.7", %"v6"
    => br %"v56" ? "L51" : "L16";
  @"L51":
    %"v59" : L = Shl %"pr.7", #3;
    %"v60" = %"v0" +p %"v59";
    %"chk3" : A = (Check 0 8 Write 1) %"v60";
    store Wl [%"chk3" + 0] <- #0;
    %"v62" : L = Add %"pr.7", #1
    => goto poll "L50";
  @"L15":
    call %"v67" : L = $"__mpn_mul_1"(P %"v0", P %"v2", L %"v6", L %"v13")
    => goto "L16";
  @"L16" [%"pr.3" : L = phi("L15" => %"v67", "L28" => #0, "L50" => #0)]:
    %"v70" : L = Shl %"v6", #3;
    %"v71" = %"v0" +p %"v70";
    %"chk4" : A = (Check 0 8 Write 1) %"v71";
    store Wl [%"chk4" + 0] <- %"pr.3";
    %"v74" = %"v0" +p #8
    => goto "L75";
  @"L75" [%"pr.2" : L = phi("L16" => #1, "L89" => %"v115"); %"pr.1" : P = phi("L16" => %"v74", "L89" => %"v113")]:
    %"v81" : W = (Cmp Slt L) %"pr.2", %"v6"
    => br %"v81" ? "L76" : "L78";
  @"L76":
    %"v84" : L = Shl %"pr.2", #3;
    %"v85" = %"v4" +p %"v84";
    %"chk5" : A = (Check 0 8 Read 1) %"v85";
    %"v86" : L = (RawLoad LdL 0) %"chk5";
    %"v91" : W = (Cmp Ule L) %"v86", #1
    => br %"v91" ? "L87" : "L88";
  @"L87":
    %"v96" : W = (Cmp Eq L) %"v86", #1
    => br %"v96" ? "L92" : "L89";
  @"L92":
    call %"v101" : L = $"__mpn_add_n"(P %"pr.1", P %"pr.1", P %"v2", L %"v6")
    => goto "L89";
  @"L88":
    call %"v106" : L = $"__mpn_addmul_1"(P %"pr.1", P %"v2", L %"v6", L %"v86")
    => goto "L89";
  @"L89" [%"pr.4" : L = phi("L88" => %"v106", "L92" => %"v101", "L87" => #0)]:
    %"v110" = %"pr.1" +p %"v70";
    %"chk6" : A = (Check 0 8 Write 1) %"v110";
    store Wl [%"chk6" + 0] <- %"pr.4";
    %"v113" = %"pr.1" +p #8;
    %"v115" : L = Add %"pr.2", #1
    => goto poll "L75";
  @"L78":
    => ret void
} }.

Definition fn_glibc_mul_n'23__mpn_add_1'2egnu_inline : func :=
  ir_fn{ "local" "glibc_mul_n#__mpn_add_1.gnu_inline"(P %"v0", P %"v2", L %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v10" = %"v2" +p #8;
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v11" : L = (RawLoad LdL 0) %"chk0";
    %"v14" : L = Add %"v11", %"v6";
    %"v16" = %"v0" +p #8;
    %"chk1" : A = (Check 0 8 Write 1) %"v0";
    store Wl [%"chk1" + 0] <- %"v14";
    %"v23" : W = (Cmp Ult L) %"v14", %"v11"
    => br %"v23" ? "L24" : "L42";
  @"L24" [%"pr.5" : L = phi("start" => %"v4", "L25" => %"v28"); %"pr.3" : P = phi("start" => %"v10", "L25" => %"v31"); %"pr.1" : P = phi("start" => %"v16", "L25" => %"v35")]:
    %"v28" : L = Sub %"pr.5", #1;
    %"v29" : W = (Cmp Ne L) %"v28", #0
    => br %"v29" ? "L25" : "L26";
  @"L25":
    %"v31" = %"pr.3" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"pr.3";
    %"v32" : L = (RawLoad LdL 0) %"chk2";
    %"v33" : L = Add %"v32", #1;
    %"v35" = %"pr.1" +p #8;
    %"chk3" : A = (Check 0 8 Write 1) %"pr.1";
    store Wl [%"chk3" + 0] <- %"v33";
    %"v41" : W = (Cmp Ne L) %"v33", #0
    => br %"v41" ? "L42" : poll "L24";
  @"L26":
    => ret #1;
  @"L42" [%"pr.6" : L = phi("L25" => %"v28", "start" => %"v4"); %"pr.4" : P = phi("L25" => %"v31", "start" => %"v10"); %"pr.2" : P = phi("L25" => %"v35", "start" => %"v16")]:
    %"v50" : L = Ptoi %"pr.2";
    %"v51" : L = Ptoi %"pr.4";
    %"v52" : W = (Cmp Ne L) %"v50", %"v51"
    => br %"v52" ? "L54" : "L47";
  @"L54" [%"pr.7" : L = phi("L55" => %"v72", "L42" => #0)]:
    %"v60" : L = Sub %"pr.6", #1;
    %"v61" : W = (Cmp Slt L) %"pr.7", %"v60"
    => br %"v61" ? "L55" : "L47";
  @"L55":
    %"v64" : L = Shl %"pr.7", #3;
    %"v65" = %"pr.2" +p %"v64";
    %"v69" = %"pr.4" +p %"v64";
    %"chk4" : A = (Check 0 8 Read 1) %"v69";
    %"v70" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (Check 0 8 Write 1) %"v65";
    store Wl [%"chk5" + 0] <- %"v70";
    %"v72" : L = Add %"pr.7", #1
    => goto poll "L54";
  @"L47":
    => ret #0
} }.

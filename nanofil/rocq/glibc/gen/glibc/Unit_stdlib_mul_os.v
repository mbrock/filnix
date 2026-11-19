(** This file defines checked IR from glibc’s `stdlib/mul.os` object.
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

Definition fn___mpn_mul : func :=
  ir_fn{ "export" "__mpn_mul"(P %"v0", P %"v2", L %"v4", P %"v6", L %"v8") -> (RClass L) {
  @"start":
    %"v13" : L = Shl %"v4", #3;
    %"v14" = %"v0" +p %"v13";
    %"v16" : L = Shl %"v8", #3;
    %"v17" = %"v14" +p %"v16";
    (Flight (a "v18") Sub [(FAddress (t "v17")); (FValue (Const 8))] (LowerOf (t "v17")));
    %"v25" : W = (Cmp Slt L) %"v8", #32
    => br %"v25" ? "L21" : "L23";
  @"L21":
    %"v33" : W = (Cmp Eq L) %"v8", #0
    => br %"v33" ? "L29" : "L31";
  @"L29":
    => ret #0;
  @"L31":
    %"chk0" : A = (Check 0 8 Read 1) %"v6";
    %"v37" : L = (RawLoad LdL 0) %"chk0";
    %"v42" : W = (Cmp Ule L) %"v37", #1
    => br %"v42" ? "L38" : "L39";
  @"L38":
    %"v47" : W = (Cmp Eq L) %"v37", #1
    => br %"v47" ? "L52" : "L74";
  @"L52" [%"pr.13" : L = phi("L53" => %"v69", "L38" => #0)]:
    %"v58" : W = (Cmp Slt L) %"pr.13", %"v4"
    => br %"v58" ? "L53" : "L40";
  @"L53":
    %"v61" : L = Shl %"pr.13", #3;
    %"v62" = %"v0" +p %"v61";
    %"v66" = %"v2" +p %"v61";
    %"chk1" : A = (Check 0 8 Read 1) %"v66";
    %"v67" : L = (RawLoad LdL 0) %"chk1";
    %"chk2" : A = (Check 0 8 Write 1) %"v62";
    store Wl [%"chk2" + 0] <- %"v67";
    %"v69" : L = Add %"pr.13", #1
    => goto poll "L52";
  @"L74" [%"pr.14" : L = phi("L75" => %"v86", "L38" => #0)]:
    %"v80" : W = (Cmp Slt L) %"pr.14", %"v4"
    => br %"v80" ? "L75" : "L40";
  @"L75":
    %"v83" : L = Shl %"pr.14", #3;
    %"v84" = %"v0" +p %"v83";
    %"chk3" : A = (Check 0 8 Write 1) %"v84";
    store Wl [%"chk3" + 0] <- #0;
    %"v86" : L = Add %"pr.14", #1
    => goto poll "L74";
  @"L39":
    call %"v91" : L = $"__mpn_mul_1"(P %"v0", P %"v2", L %"v4", L %"v37")
    => goto "L40";
  @"L40" [%"pr.11" : L = phi("L39" => %"v91", "L52" => #0, "L74" => #0)]:
    %"chk4" : A = (Check 0 8 Write 1) %"v14";
    store Wl [%"chk4" + 0] <- %"pr.11";
    %"v98" = %"v0" +p #8
    => goto "L99";
  @"L99" [%"pr.12" : L = phi("L113" => %"pr.9", "L40" => %"pr.11"); %"pr.8" : L = phi("L113" => %"v139", "L40" => #1); %"pr.3" : P = phi("L113" => %"v137", "L40" => %"v98")]:
    %"v105" : W = (Cmp Slt L) %"pr.8", %"v8"
    => br %"v105" ? "L100" : "L102";
  @"L100":
    %"v108" : L = Shl %"pr.8", #3;
    %"v109" = %"v6" +p %"v108";
    %"chk5" : A = (Check 0 8 Read 1) %"v109";
    %"v110" : L = (RawLoad LdL 0) %"chk5";
    %"v115" : W = (Cmp Ule L) %"v110", #1
    => br %"v115" ? "L111" : "L112";
  @"L111":
    %"v120" : W = (Cmp Eq L) %"v110", #1
    => br %"v120" ? "L116" : "L113";
  @"L116":
    call %"v125" : L = $"__mpn_add_n"(P %"pr.3", P %"pr.3", P %"v2", L %"v4")
    => goto "L113";
  @"L112":
    call %"v130" : L = $"__mpn_addmul_1"(P %"pr.3", P %"v2", L %"v4", L %"v110")
    => goto "L113";
  @"L113" [%"pr.9" : L = phi("L112" => %"v130", "L116" => %"v125", "L111" => #0)]:
    %"v134" = %"pr.3" +p %"v13";
    %"chk6" : A = (Check 0 8 Write 1) %"v134";
    store Wl [%"chk6" + 0] <- %"pr.9";
    %"v137" = %"pr.3" +p #8;
    %"v139" : L = Add %"pr.8", #1
    => goto poll "L99";
  @"L102":
    => ret %"pr.12";
  @"L23":
    %"v143" : L = Shl %"v8", #1;
    %"v146" : L = Shl %"v143", #3;
    %"v147" : P = (Alloc 16) %"v146"
    => br %"v25" ? "L151" : "L152";
  @"L151":
    call void $"__mpn_impn_mul_n_basecase"(P %"v0", P %"v2", P %"v6", L %"v8")
    => goto "L150";
  @"L152":
    call void $"__mpn_impn_mul_n"(P %"v0", P %"v2", P %"v6", L %"v8", P %"v147")
    => goto "L150";
  @"L150":
    %"v168" = %"v0" +p %"v16";
    %"v172" = %"v2" +p %"v16";
    %"v175" : L = Sub %"v4", %"v8";
    %"v181" : W = (Cmp Sge L) %"v175", %"v8"
    => br %"v181" ? "L176" : "L178";
  @"L176":
    %"v188" : P = (Alloc 16) %"v146"
    => goto "L189";
  @"L189" [%"pr.7" : L = phi("L176" => %"v175", "L194" => %"v235"); %"pr.5" : P = phi("L176" => %"v172", "L194" => %"v232"); %"pr.2" : P = phi("L176" => %"v168", "L194" => %"v217")]:
    => br %"v25" ? "L195" : "L196";
  @"L195":
    call void $"__mpn_impn_mul_n_basecase"(P %"v188", P %"pr.5", P %"v6", L %"v8")
    => goto "L194";
  @"L196":
    call void $"__mpn_impn_mul_n"(P %"v188", P %"pr.5", P %"v6", L %"v8", P %"v147")
    => goto "L194";
  @"L194":
    call %"v213" : L = $"__mpn_add_n"(P %"pr.2", P %"pr.2", P %"v188", L %"v8");
    %"v217" = %"pr.2" +p %"v16";
    %"v221" = %"v188" +p %"v16";
    call %"v224" : L = $"glibc_mul#__mpn_add_1.gnu_inline"(P %"v217", P %"v221", L %"v8", L %"v213");
    %"v232" = %"pr.5" +p %"v16";
    %"v235" : L = Sub %"pr.7", %"v8";
    %"v238" : W = (Cmp Sge L) %"v235", %"v8"
    => br %"v238" ? poll "L189" : "L178";
  @"L178" [%"pr.6" : L = phi("L194" => %"v235", "L150" => %"v175"); %"pr.4" : P = phi("L194" => %"v232", "L150" => %"v172"); %"pr.1" : P = phi("L194" => %"v217", "L150" => %"v168")]:
    %"v243" : W = (Cmp Ne L) %"pr.6", #0
    => br %"v243" ? "L239" : "L241";
  @"L239":
    call %"v249" : L = $"__mpn_mul"(P %"v147", P %"v6", L %"v8", P %"pr.4", L %"pr.6");
    call %"v254" : L = $"__mpn_add_n"(P %"pr.1", P %"pr.1", P %"v147", L %"v8");
    %"v258" = %"pr.1" +p %"v16";
    %"v262" = %"v147" +p %"v16";
    call %"v265" : L = $"glibc_mul#__mpn_add_1.gnu_inline"(P %"v258", P %"v262", L %"pr.6", L %"v254")
    => goto "L241";
  @"L241":
    %"chk7" : A = (Check 0 8 Read 1) %"v18";
    %"v267" : L = (RawLoad LdL 0) %"chk7"
    => ret %"v267"
} }.

Definition fn_glibc_mul'23__mpn_add_1'2egnu_inline : func :=
  ir_fn{ "local" "glibc_mul#__mpn_add_1.gnu_inline"(P %"v0", P %"v2", L %"v4", L %"v6") -> (RClass L) {
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

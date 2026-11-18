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

Definition hello_image_fn___mpn_add_n : func :=
  ir_fn{ "export" "__mpn_add_n"(P %"v0", P %"v2", P %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v13" : L = Neg %"v6";
    %"v16" : L = Shl %"v13", #3;
    (Flight (a "v17") Sub [(FAddress (t "v2")); (FValue (t "v16"))] (LowerOf (t "v2")));
    (Flight (a "v21") Sub [(FAddress (t "v4")); (FValue (t "v16"))] (LowerOf (t "v4")));
    (Flight (a "v25") Sub [(FAddress (t "v0")); (FValue (t "v16"))] (LowerOf (t "v0")))
    => goto "L26";
  @"L26" [%"pr.2" : L = phi("L26" => %"v61", "start" => %"v13"); %"pr.1" : L = phi("L26" => %"v54", "start" => #0)]:
    %"v31" : L = Shl %"pr.2", #3;
    %"v32" = %"v21" +p %"v31";
    %"chk0" : A = (Check 0 8 Read 1) %"v32";
    %"v33" : L = (RawLoad LdL 0) %"chk0";
    %"v37" = %"v17" +p %"v31";
    %"chk1" : A = (Check 0 8 Read 1) %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk1";
    %"v41" : L = Add %"v33", %"pr.1";
    %"v44" : W = (Cmp Ult L) %"v41", %"pr.1";
    %"v45" : L = (Ext Sw) %"v44";
    %"v48" : L = Add %"v38", %"v41";
    %"v51" : W = (Cmp Ult L) %"v48", %"v38";
    %"v53" : L = (Ext Sw) %"v51";
    %"v54" : L = Add %"v53", %"v45";
    %"v58" = %"v25" +p %"v31";
    %"chk2" : A = (Check 0 8 Write 1) %"v58";
    store Wl [%"chk2" + 0] <- %"v48";
    %"v61" : L = Add %"pr.2", #1;
    %"v62" : W = (Cmp Ne L) %"v61", #0
    => br %"v62" ? poll "L26" : "L28";
  @"L28":
    => ret %"v54"
} }.

Definition hello_image_fn___mpn_addmul_1 : func :=
  ir_fn{ "export" "__mpn_addmul_1"(P %"v0", P %"v2", L %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v14" : L = Neg %"v4";
    %"v17" : L = Shl %"v14", #3;
    (Flight (a "v18") Sub [(FAddress (t "v0")); (FValue (t "v17"))] (LowerOf (t "v0")));
    (Flight (a "v22") Sub [(FAddress (t "v2")); (FValue (t "v17"))] (LowerOf (t "v2")))
    => goto "L23";
  @"L23" [%"pr.2" : L = phi("L23" => %"v65", "start" => %"v14"); %"pr.1" : L = phi("L23" => %"v58", "start" => #0)]:
    %"v30" : L = Shl %"pr.2", #3;
    %"v31" = %"v22" +p %"v30";
    %"chk0" : A = (Check 0 8 Read 1) %"v31";
    %"v32" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.iw_1.v23" : L = And %"v32", #4294967295;
    %"iw_1.iw_1.v26" : L = Shr %"v32", #32;
    %"iw_1.iw_1.v29" : L = And %"v6", #4294967295;
    %"iw_1.iw_1.v32" : L = Shr %"v6", #32;
    %"iw_1.iw_1.v38" : L = Mul %"iw_1.iw_1.v23", %"iw_1.iw_1.v29";
    %"iw_1.iw_1.v44" : L = Mul %"iw_1.iw_1.v23", %"iw_1.iw_1.v32";
    %"iw_1.iw_1.v50" : L = Mul %"iw_1.iw_1.v26", %"iw_1.iw_1.v29";
    %"iw_1.iw_1.v56" : L = Mul %"iw_1.iw_1.v26", %"iw_1.iw_1.v32";
    %"iw_1.iw_1.iw_1.v11" : L = Add %"iw_1.iw_1.v44", %"iw_1.iw_1.v50";
    %"iw_1.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_1.iw_1.iw_1.v11", %"iw_1.iw_1.v44";
    %"iw_1.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_1.iw_1.iw_1.v13";
    (Call (CTuple [((a "iw_1.iw_1.v74"), L); ((a "iw_1.iw_1.v75"), L)]) (Global (a "glibc_addmul_1#u128_lshift")) [(Arg L (t "iw_1.iw_1.iw_1.v11")); (Arg L (t "iw_1.iw_1.iw_1.v24")); (Arg W (Const 32))]);
    %"iw_1.iw_1.iw_2.v11" : L = Add %"iw_1.iw_1.v38", %"iw_1.iw_1.v74";
    %"iw_1.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_1.iw_1.iw_2.v11", %"iw_1.iw_1.v38";
    %"iw_1.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_1.iw_1.iw_2.v13";
    %"iw_1.iw_1.iw_2.v25" : L = Add %"iw_1.iw_1.v75", %"iw_1.iw_1.iw_2.v24";
    %"iw_1.iw_1.iw_3.v22" : L = Add %"iw_1.iw_1.iw_2.v25", %"iw_1.iw_1.v56";
    %"v38" : L = Add %"iw_1.iw_1.iw_2.v11", %"pr.1";
    %"v41" : W = (Cmp Ult L) %"v38", %"pr.1";
    %"v43" : L = (Ext Sw) %"v41";
    %"v44" : L = Add %"v43", %"iw_1.iw_1.iw_3.v22";
    %"v48" = %"v18" +p %"v30";
    %"chk1" : A = (Check 0 8 Read 1) %"v48";
    %"v49" : L = (RawLoad LdL 0) %"chk1";
    %"v52" : L = Add %"v49", %"v38";
    %"v56" : W = (Cmp Ult L) %"v52", %"v49";
    %"v57" : L = (Ext Sw) %"v56";
    %"v58" : L = Add %"v44", %"v57";
    %"chk2" : A = (Renew 0 8 Write 1) %"chk1", %"v48";
    store Wl [%"chk2" + 0] <- %"v52";
    %"v65" : L = Add %"pr.2", #1;
    %"v66" : W = (Cmp Ne L) %"v65", #0
    => br %"v66" ? poll "L23" : "L25";
  @"L25":
    => ret %"v58"
} }.

Definition hello_image_fn___mpn_cmp : func :=
  ir_fn{ "export" "__mpn_cmp"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v10" : L = Sub %"v4", #1
    => goto "L11";
  @"L11" [%"pr.1" : L = phi("L13" => %"v36", "start" => %"v10")]:
    %"v16" : W = (Cmp Sge L) %"pr.1", #0
    => br %"v16" ? "L12" : "L14";
  @"L12":
    %"v19" : L = Shl %"pr.1", #3;
    %"v20" = %"v0" +p %"v19";
    %"chk0" : A = (Check 0 8 Read 1) %"v20";
    %"v21" : L = (RawLoad LdL 0) %"chk0";
    %"v25" = %"v2" +p %"v19";
    %"chk1" : A = (Check 0 8 Read 1) %"v25";
    %"v26" : L = (RawLoad LdL 0) %"chk1";
    %"v32" : W = (Cmp Ne L) %"v21", %"v26"
    => br %"v32" ? "L33" : "L13";
  @"L13":
    %"v36" : L = Sub %"pr.1", #1
    => goto poll "L11";
  @"L14":
    => ret #0;
  @"L33":
    %"v42" : W = (Cmp Ugt L) %"v21", %"v26"
    => br %"v42" ? "L39" : "L38";
  @"L38":
    => goto "L39";
  @"L39" [%"v44" : W = phi("L38" => #4294967295, "L33" => #1)]:
    => ret %"v44"
} }.

Definition hello_image_fn___mpn_lshift : func :=
  ir_fn{ "export" "__mpn_lshift"(P %"v0", P %"v2", L %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v16" = %"v0" +p #8;
    %"v18" : W = Sub #64, %"v6";
    %"v20" : L = Sub %"v4", #1;
    %"v23" : L = Shl %"v20", #3;
    %"v24" = %"v2" +p %"v23";
    %"chk0" : A = (Check 0 8 Read 1) %"v24";
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"v28" : L = Shr %"v25", %"v18"
    => goto "L30";
  @"L30" [%"pr.2" : L = phi("L31" => %"v34", "start" => %"v20"); %"pr.1" : L = phi("L31" => %"v40", "start" => %"v25")]:
    %"v34" : L = Sub %"pr.2", #1;
    %"v35" : W = (Cmp Sge L) %"v34", #0
    => br %"v35" ? "L31" : "L32";
  @"L31":
    %"v38" : L = Shl %"v34", #3;
    %"v39" = %"v2" +p %"v38";
    %"chk1" : A = (Check 0 8 Read 1) %"v39";
    %"v40" : L = (RawLoad LdL 0) %"chk1";
    %"v44" = %"v16" +p %"v38";
    %"v47" : L = Shl %"pr.1", %"v6";
    %"v50" : L = Shr %"v40", %"v18";
    %"v51" : L = Or %"v47", %"v50";
    %"chk2" : A = (Check 0 8 Write 1) %"v44";
    store Wl [%"chk2" + 0] <- %"v51"
    => goto poll "L30";
  @"L32":
    %"v55" : L = Shl %"v34", #3;
    %"v56" = %"v16" +p %"v55";
    %"v59" : L = Shl %"pr.1", %"v6";
    %"chk3" : A = (Check 0 8 Write 1) %"v56";
    store Wl [%"chk3" + 0] <- %"v59"
    => ret %"v28"
} }.

Definition hello_image_fn___mpn_mul : func :=
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

Definition hello_image_fn_glibc_mul'23__mpn_add_1'2egnu_inline : func :=
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

Definition hello_image_fn___mpn_mul_1 : func :=
  ir_fn{ "export" "__mpn_mul_1"(P %"v0", P %"v2", L %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v13" : L = Neg %"v4";
    %"v16" : L = Shl %"v13", #3;
    (Flight (a "v17") Sub [(FAddress (t "v2")); (FValue (t "v16"))] (LowerOf (t "v2")));
    (Flight (a "v21") Sub [(FAddress (t "v0")); (FValue (t "v16"))] (LowerOf (t "v0")))
    => goto "L22";
  @"L22" [%"pr.2" : L = phi("L22" => %"v50", "start" => %"v13"); %"pr.1" : L = phi("L22" => %"v43", "start" => #0)]:
    %"v29" : L = Shl %"pr.2", #3;
    %"v30" = %"v17" +p %"v29";
    %"chk0" : A = (Check 0 8 Read 1) %"v30";
    %"v31" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.iw_1.v23" : L = And %"v31", #4294967295;
    %"iw_1.iw_1.v26" : L = Shr %"v31", #32;
    %"iw_1.iw_1.v29" : L = And %"v6", #4294967295;
    %"iw_1.iw_1.v32" : L = Shr %"v6", #32;
    %"iw_1.iw_1.v38" : L = Mul %"iw_1.iw_1.v23", %"iw_1.iw_1.v29";
    %"iw_1.iw_1.v44" : L = Mul %"iw_1.iw_1.v23", %"iw_1.iw_1.v32";
    %"iw_1.iw_1.v50" : L = Mul %"iw_1.iw_1.v26", %"iw_1.iw_1.v29";
    %"iw_1.iw_1.v56" : L = Mul %"iw_1.iw_1.v26", %"iw_1.iw_1.v32";
    %"iw_1.iw_1.iw_1.v11" : L = Add %"iw_1.iw_1.v44", %"iw_1.iw_1.v50";
    %"iw_1.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_1.iw_1.iw_1.v11", %"iw_1.iw_1.v44";
    %"iw_1.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_1.iw_1.iw_1.v13";
    (Call (CTuple [((a "iw_1.iw_1.v74"), L); ((a "iw_1.iw_1.v75"), L)]) (Global (a "glibc_mul_1#u128_lshift")) [(Arg L (t "iw_1.iw_1.iw_1.v11")); (Arg L (t "iw_1.iw_1.iw_1.v24")); (Arg W (Const 32))]);
    %"iw_1.iw_1.iw_2.v11" : L = Add %"iw_1.iw_1.v38", %"iw_1.iw_1.v74";
    %"iw_1.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_1.iw_1.iw_2.v11", %"iw_1.iw_1.v38";
    %"iw_1.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_1.iw_1.iw_2.v13";
    %"iw_1.iw_1.iw_2.v25" : L = Add %"iw_1.iw_1.v75", %"iw_1.iw_1.iw_2.v24";
    %"iw_1.iw_1.iw_3.v22" : L = Add %"iw_1.iw_1.iw_2.v25", %"iw_1.iw_1.v56";
    %"v37" : L = Add %"iw_1.iw_1.iw_2.v11", %"pr.1";
    %"v40" : W = (Cmp Ult L) %"v37", %"pr.1";
    %"v42" : L = (Ext Sw) %"v40";
    %"v43" : L = Add %"v42", %"iw_1.iw_1.iw_3.v22";
    %"v47" = %"v21" +p %"v29";
    %"chk1" : A = (Check 0 8 Write 1) %"v47";
    store Wl [%"chk1" + 0] <- %"v37";
    %"v50" : L = Add %"pr.2", #1;
    %"v51" : W = (Cmp Ne L) %"v50", #0
    => br %"v51" ? poll "L22" : "L24";
  @"L24":
    => ret %"v43"
} }.

Definition hello_image_fn___mpn_impn_mul_n_basecase : func :=
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

Definition hello_image_fn___mpn_impn_mul_n : func :=
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

Definition hello_image_fn_glibc_mul_n'23__mpn_add_1'2egnu_inline : func :=
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

Definition hello_image_fn___mpn_rshift : func :=
  ir_fn{ "export" "__mpn_rshift"(P %"v0", P %"v2", L %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v18" : W = (Cmp Ne L) %"v4", #0
    => br %"v18" ? "L19" : "L20";
  @"L19":
    %"v22" : W = (Cmp Ne W) %"v6", #0
    => goto "L20";
  @"L20" [%"v24" : W = phi("start" => #0, "L19" => %"v22")]:
    => br %"v24" ? "L16" : "L15";
  @"L15":
    %"v25" : P = Copy $"glibc_rshift#str.62";
    %"v26" : P = Copy $"glibc_rshift#str.63";
    %"v27" : P = Copy $"glibc_rshift#str.64";
    call void $"__libc_assert_fail"(P %"v25", P %"v26", W #45, P %"v27")
    => goto "L16";
  @"L16":
    (Flight (a "v30") Sub [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
    %"v32" : W = Sub #64, %"v6";
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v35" : L = (RawLoad LdL 0) %"chk0";
    %"v38" : L = Shl %"v35", %"v32"
    => goto "L40";
  @"L40" [%"pr.2" : L = phi("L16" => #1, "L41" => %"v65"); %"pr.1" : L = phi("L16" => %"v35", "L41" => %"v51")]:
    %"v46" : W = (Cmp Slt L) %"pr.2", %"v4"
    => br %"v46" ? "L41" : "L43";
  @"L41":
    %"v49" : L = Shl %"pr.2", #3;
    %"v50" = %"v2" +p %"v49";
    %"chk1" : A = (Check 0 8 Read 1) %"v50";
    %"v51" : L = (RawLoad LdL 0) %"chk1";
    %"v55" = %"v30" +p %"v49";
    %"v58" : L = Shr %"pr.1", %"v6";
    %"v61" : L = Shl %"v51", %"v32";
    %"v62" : L = Or %"v58", %"v61";
    %"chk2" : A = (Check 0 8 Write 1) %"v55";
    store Wl [%"chk2" + 0] <- %"v62";
    %"v65" : L = Add %"pr.2", #1
    => goto poll "L40";
  @"L43":
    %"v68" : L = Shl %"pr.2", #3;
    %"v69" = %"v30" +p %"v68";
    %"v72" : L = Shr %"pr.1", %"v6";
    %"chk3" : A = (Check 0 8 Write 1) %"v69";
    store Wl [%"chk3" + 0] <- %"v72"
    => ret %"v38"
} }.

Definition hello_image_fn___mpn_sub_n : func :=
  ir_fn{ "export" "__mpn_sub_n"(P %"v0", P %"v2", P %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v13" : L = Neg %"v6";
    %"v16" : L = Shl %"v13", #3;
    (Flight (a "v17") Sub [(FAddress (t "v2")); (FValue (t "v16"))] (LowerOf (t "v2")));
    (Flight (a "v21") Sub [(FAddress (t "v4")); (FValue (t "v16"))] (LowerOf (t "v4")));
    (Flight (a "v25") Sub [(FAddress (t "v0")); (FValue (t "v16"))] (LowerOf (t "v0")))
    => goto "L26";
  @"L26" [%"pr.2" : L = phi("L26" => %"v61", "start" => %"v13"); %"pr.1" : L = phi("L26" => %"v54", "start" => #0)]:
    %"v31" : L = Shl %"pr.2", #3;
    %"v32" = %"v21" +p %"v31";
    %"chk0" : A = (Check 0 8 Read 1) %"v32";
    %"v33" : L = (RawLoad LdL 0) %"chk0";
    %"v37" = %"v17" +p %"v31";
    %"chk1" : A = (Check 0 8 Read 1) %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk1";
    %"v41" : L = Add %"v33", %"pr.1";
    %"v44" : W = (Cmp Ult L) %"v41", %"pr.1";
    %"v45" : L = (Ext Sw) %"v44";
    %"v48" : L = Sub %"v38", %"v41";
    %"v51" : W = (Cmp Ugt L) %"v48", %"v38";
    %"v53" : L = (Ext Sw) %"v51";
    %"v54" : L = Add %"v53", %"v45";
    %"v58" = %"v25" +p %"v31";
    %"chk2" : A = (Check 0 8 Write 1) %"v58";
    store Wl [%"chk2" + 0] <- %"v48";
    %"v61" : L = Add %"pr.2", #1;
    %"v62" : W = (Cmp Ne L) %"v61", #0
    => br %"v62" ? poll "L26" : "L28";
  @"L28":
    => ret %"v54"
} }.

Definition hello_image_fn___mpn_submul_1 : func :=
  ir_fn{ "export" "__mpn_submul_1"(P %"v0", P %"v2", L %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v14" : L = Neg %"v4";
    %"v17" : L = Shl %"v14", #3;
    (Flight (a "v18") Sub [(FAddress (t "v0")); (FValue (t "v17"))] (LowerOf (t "v0")));
    (Flight (a "v22") Sub [(FAddress (t "v2")); (FValue (t "v17"))] (LowerOf (t "v2")))
    => goto "L23";
  @"L23" [%"pr.2" : L = phi("L23" => %"v65", "start" => %"v14"); %"pr.1" : L = phi("L23" => %"v58", "start" => #0)]:
    %"v30" : L = Shl %"pr.2", #3;
    %"v31" = %"v22" +p %"v30";
    %"chk0" : A = (Check 0 8 Read 1) %"v31";
    %"v32" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.iw_1.v23" : L = And %"v32", #4294967295;
    %"iw_1.iw_1.v26" : L = Shr %"v32", #32;
    %"iw_1.iw_1.v29" : L = And %"v6", #4294967295;
    %"iw_1.iw_1.v32" : L = Shr %"v6", #32;
    %"iw_1.iw_1.v38" : L = Mul %"iw_1.iw_1.v23", %"iw_1.iw_1.v29";
    %"iw_1.iw_1.v44" : L = Mul %"iw_1.iw_1.v23", %"iw_1.iw_1.v32";
    %"iw_1.iw_1.v50" : L = Mul %"iw_1.iw_1.v26", %"iw_1.iw_1.v29";
    %"iw_1.iw_1.v56" : L = Mul %"iw_1.iw_1.v26", %"iw_1.iw_1.v32";
    %"iw_1.iw_1.iw_1.v11" : L = Add %"iw_1.iw_1.v44", %"iw_1.iw_1.v50";
    %"iw_1.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_1.iw_1.iw_1.v11", %"iw_1.iw_1.v44";
    %"iw_1.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_1.iw_1.iw_1.v13";
    (Call (CTuple [((a "iw_1.iw_1.v74"), L); ((a "iw_1.iw_1.v75"), L)]) (Global (a "glibc_submul_1#u128_lshift")) [(Arg L (t "iw_1.iw_1.iw_1.v11")); (Arg L (t "iw_1.iw_1.iw_1.v24")); (Arg W (Const 32))]);
    %"iw_1.iw_1.iw_2.v11" : L = Add %"iw_1.iw_1.v38", %"iw_1.iw_1.v74";
    %"iw_1.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_1.iw_1.iw_2.v11", %"iw_1.iw_1.v38";
    %"iw_1.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_1.iw_1.iw_2.v13";
    %"iw_1.iw_1.iw_2.v25" : L = Add %"iw_1.iw_1.v75", %"iw_1.iw_1.iw_2.v24";
    %"iw_1.iw_1.iw_3.v22" : L = Add %"iw_1.iw_1.iw_2.v25", %"iw_1.iw_1.v56";
    %"v38" : L = Add %"iw_1.iw_1.iw_2.v11", %"pr.1";
    %"v41" : W = (Cmp Ult L) %"v38", %"pr.1";
    %"v43" : L = (Ext Sw) %"v41";
    %"v44" : L = Add %"v43", %"iw_1.iw_1.iw_3.v22";
    %"v48" = %"v18" +p %"v30";
    %"chk1" : A = (Check 0 8 Read 1) %"v48";
    %"v49" : L = (RawLoad LdL 0) %"chk1";
    %"v52" : L = Sub %"v49", %"v38";
    %"v56" : W = (Cmp Ugt L) %"v52", %"v49";
    %"v57" : L = (Ext Sw) %"v56";
    %"v58" : L = Add %"v44", %"v57";
    %"chk2" : A = (Renew 0 8 Write 1) %"chk1", %"v48";
    store Wl [%"chk2" + 0] <- %"v52";
    %"v65" : L = Add %"pr.2", #1;
    %"v66" : W = (Cmp Ne L) %"v65", #0
    => br %"v66" ? poll "L23" : "L25";
  @"L25":
    => ret %"v58"
} }.

Definition hello_image_fn___mpn_extract_double : func :=
  ir_fn{ "export" "__mpn_extract_double"(P %"v0", L %"v2", P %"v4", P %"v6", Double %"v8") -> (RClass L) {
  @"start":
    alloca "v10" 8;
    %"chk0" : A = (CheckLocal (a "v10") 0 8 Write 1);
    store Wd [%"chk0" + 0] <- %"v8";
    %"chk1" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v15" : W = Shr %"v14", #31;
    %"chk2" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk2" + 0] <- %"v15";
    %"chk3" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v19" : W = Shl %"v18", #1;
    %"v20" : W = Shr %"v19", #21;
    %"v21" : W = Sub %"v20", #1023;
    %"chk4" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk4" + 0] <- %"v21";
    %"chk5" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v26" : W = Shl %"v25", #12;
    %"v27" : W = Shr %"v26", #12;
    %"v28" : L = (Ext Sw) %"v27";
    %"v29" : L = Shl %"v28", #32;
    %"chk6" : A = (CheckLocal (a "v10") 0 4 Read 1);
    %"v30" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v31" : L = (Ext Uw) %"v30";
    %"v32" : L = Or %"v29", %"v31";
    %"chk7" : A = (Check 0 8 Write 1) %"v0";
    store Wl [%"chk7" + 0] <- %"v32";
    %"chk8" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v37" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v38" : W = Shl %"v37", #1;
    %"v39" : W = Shr %"v38", #21;
    %"v40" : W = (Cmp Eq W) %"v39", #0
    => br %"v40" ? "L33" : "L34";
  @"L33":
    %"v46" : L = (RawLoad LdL 0) %"chk7";
    %"v47" : W = (Cmp Eq L) %"v46", #0
    => br %"v47" ? "L48" : "L49";
  @"L48":
    %"v55" : L = (RawLoad LdL 0) %"chk7";
    %"v56" : W = (Cmp Eq L) %"v55", #0
    => goto "L49";
  @"L49" [%"v58" : W = phi("L33" => #0, "L48" => %"v56")]:
    => br %"v58" ? "L41" : "L42";
  @"L41":
    store Ww [%"chk4" + 0] <- #0
    => goto "L35";
  @"L42":
    %"v69" : L = (RawLoad LdL 0) %"chk7";
    %"v70" : W = (Cmp Ne L) %"v69", #0
    => br %"v70" ? "L61" : "L62";
  @"L61":
    %"v76" : L = (RawLoad LdL 0) %"chk7";
    %"iw_1.v6" : W = (Cmp Eq L) %"v76", #0
    => br %"iw_1.v6" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v8" : L = Shr %"v76", #1;
    %"iw_1.v9" : L = Or %"v76", %"iw_1.v8";
    %"iw_1.v10" : L = Shr %"iw_1.v9", #2;
    %"iw_1.v11" : L = Or %"iw_1.v9", %"iw_1.v10";
    %"iw_1.v12" : L = Shr %"iw_1.v11", #4;
    %"iw_1.v13" : L = Or %"iw_1.v11", %"iw_1.v12";
    %"iw_1.v14" : L = Shr %"iw_1.v13", #8;
    %"iw_1.v15" : L = Or %"iw_1.v13", %"iw_1.v14";
    %"iw_1.v16" : L = Shr %"iw_1.v15", #16;
    %"iw_1.v17" : L = Or %"iw_1.v15", %"iw_1.v16";
    %"iw_1.v18" : L = Shr %"iw_1.v17", #32;
    %"iw_1.v19" : L = Or %"iw_1.v17", %"iw_1.v18";
    %"iw_1.v20" : L = Shr %"iw_1.v19", #1;
    %"iw_1.v21" : L = And %"iw_1.v20", #6148914691236517205;
    %"iw_1.v22" : L = Sub %"iw_1.v19", %"iw_1.v21";
    %"iw_1.v23" : L = And %"iw_1.v22", #3689348814741910323;
    %"iw_1.v24" : L = Shr %"iw_1.v22", #2;
    %"iw_1.v25" : L = And %"iw_1.v24", #3689348814741910323;
    %"iw_1.v26" : L = Add %"iw_1.v23", %"iw_1.v25";
    %"iw_1.v27" : L = Shr %"iw_1.v26", #4;
    %"iw_1.v28" : L = Add %"iw_1.v26", %"iw_1.v27";
    %"iw_1.v29" : L = And %"iw_1.v28", #1085102592571150095;
    %"iw_1.v30" : L = Mul %"iw_1.v29", #72340172838076673;
    %"iw_1.v31" : L = Shr %"iw_1.v30", #56;
    %"iw_1.v32" : L = Sub %"iw_1.v31", #64;
    %"iw_1.v33" : L = Neg %"iw_1.v32"
    => goto "iw_1.L4";
  @"iw_1.L4" [%"iw_1.v34" : W = phi("iw_1.L3" => %"iw_1.v33", "L61" => #64)]:
    %"v86" : W = Sub %"iw_1.v34", #11;
    %"v92" : L = (RawLoad LdL 0) %"chk7";
    %"v94" : L = Shl %"v92", %"v86";
    store Wl [%"chk7" + 0] <- %"v94";
    %"v99" : W = Sub #4294966274, %"v86";
    store Ww [%"chk4" + 0] <- %"v99"
    => goto "L35";
  @"L62":
    %"v102" : L = (RawLoad LdL 0) %"chk7";
    %"iw_2.v6" : W = (Cmp Eq L) %"v102", #0
    => br %"iw_2.v6" ? "iw_2.L4" : "iw_2.L3";
  @"iw_2.L3":
    %"iw_2.v8" : L = Shr %"v102", #1;
    %"iw_2.v9" : L = Or %"v102", %"iw_2.v8";
    %"iw_2.v10" : L = Shr %"iw_2.v9", #2;
    %"iw_2.v11" : L = Or %"iw_2.v9", %"iw_2.v10";
    %"iw_2.v12" : L = Shr %"iw_2.v11", #4;
    %"iw_2.v13" : L = Or %"iw_2.v11", %"iw_2.v12";
    %"iw_2.v14" : L = Shr %"iw_2.v13", #8;
    %"iw_2.v15" : L = Or %"iw_2.v13", %"iw_2.v14";
    %"iw_2.v16" : L = Shr %"iw_2.v15", #16;
    %"iw_2.v17" : L = Or %"iw_2.v15", %"iw_2.v16";
    %"iw_2.v18" : L = Shr %"iw_2.v17", #32;
    %"iw_2.v19" : L = Or %"iw_2.v17", %"iw_2.v18";
    %"iw_2.v20" : L = Shr %"iw_2.v19", #1;
    %"iw_2.v21" : L = And %"iw_2.v20", #6148914691236517205;
    %"iw_2.v22" : L = Sub %"iw_2.v19", %"iw_2.v21";
    %"iw_2.v23" : L = And %"iw_2.v22", #3689348814741910323;
    %"iw_2.v24" : L = Shr %"iw_2.v22", #2;
    %"iw_2.v25" : L = And %"iw_2.v24", #3689348814741910323;
    %"iw_2.v26" : L = Add %"iw_2.v23", %"iw_2.v25";
    %"iw_2.v27" : L = Shr %"iw_2.v26", #4;
    %"iw_2.v28" : L = Add %"iw_2.v26", %"iw_2.v27";
    %"iw_2.v29" : L = And %"iw_2.v28", #1085102592571150095;
    %"iw_2.v30" : L = Mul %"iw_2.v29", #72340172838076673;
    %"iw_2.v31" : L = Shr %"iw_2.v30", #56;
    %"iw_2.v32" : L = Sub %"iw_2.v31", #64;
    %"iw_2.v33" : L = Neg %"iw_2.v32"
    => goto "iw_2.L4";
  @"iw_2.L4" [%"iw_2.v34" : W = phi("iw_2.L3" => %"iw_2.v33", "L62" => #64)]:
    %"v115" : W = (Cmp Sge W) %"iw_2.v34", #11
    => br %"v115" ? "L107" : "L108";
  @"L107":
    %"v123" : L = (RawLoad LdL 0) %"chk7";
    %"v129" : W = Sub %"iw_2.v34", #11;
    %"v130" : L = Shl %"v123", %"v129";
    store Wl [%"chk7" + 0] <- %"v130";
    store Wl [%"chk7" + 0] <- #0
    => goto "L109";
  @"L108":
    %"v140" : L = (RawLoad LdL 0) %"chk7";
    %"v146" : W = Sub #11, %"iw_2.v34";
    %"v147" : L = Shr %"v140", %"v146";
    store Wl [%"chk7" + 0] <- %"v147";
    %"v150" : L = (RawLoad LdL 0) %"chk7";
    %"v157" : W = Sub #64, %"v146";
    %"v158" : L = Shl %"v150", %"v157";
    store Wl [%"chk7" + 0] <- %"v158"
    => goto "L109";
  @"L109":
    %"v169" : W = Sub #4294966221, %"iw_2.v34";
    store Ww [%"chk4" + 0] <- %"v169"
    => goto "L35";
  @"L34":
    %"v175" : L = (RawLoad LdL 0) %"chk7";
    %"v181" : L = Or %"v175", #4503599627370496;
    store Wl [%"chk7" + 0] <- %"v181"
    => goto "L35";
  @"L35":
    => ret #1
} }.

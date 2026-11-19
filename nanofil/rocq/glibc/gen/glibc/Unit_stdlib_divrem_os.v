(** This file defines checked IR from glibc’s `stdlib/divrem.os` object.
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

Definition fn___mpn_divrem : func :=
  ir_fn{ "export" "__mpn_divrem"(P %"v0", L %"v2", P %"v4", L %"v6", P %"v8", L %"v10") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v483" : W = (Cmp Eq L) %"v10", #0
    => br %"v483" ? "L16" : "L484" };
  ir_blk{ @"L16":
    %"v18" : L = Div #1, %"v10"
    => ret %"v18" };
  ir_blk{ @"L19":
    %"chk0" : A = (Check 0 8 Read 1) %"v8";
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"v28" : L = Sub %"v6", #1;
    %"v29" : L = Shl %"v28", #3;
    %"v30" = %"v4" +p %"v29";
    %"chk1" : A = (Check 0 8 Read 1) %"v30";
    %"v31" : L = (RawLoad LdL 0) %"chk1";
    %"v37" : W = (Cmp Uge L) %"v31", %"v25"
    => br %"v37" ? "L32" : "L34" };
  ir_blk{ @"L32":
    %"v40" : L = Sub %"v31", %"v25"
    => goto "L34" };
  ir_blk{ @"L34" [%"pr.12" : L = phi("L32" => %"v40", "L19" => %"v31"); %"pr.9" : L = phi("L32" => #1, "L19" => #0)]:
    %"v43" : L = Shl %"v2", #3;
    %"v44" = %"v0" +p %"v43";
    %"v46" : L = Sub %"v6", #2
    => goto "L47" };
  ir_blk{ @"L47" [%"pr.13" : L = phi("L34" => %"pr.12", "iw_1.L86" => %"iw_1.v114"); %"pr.10" : L = phi("L34" => %"v46", "iw_1.L86" => %"v65")]:
    %"v52" : W = (Cmp Sge L) %"pr.10", #0
    => br %"v52" ? "L48" : "L50" };
  ir_blk{ @"L48":
    %"v55" : L = Shl %"pr.10", #3;
    %"v56" = %"v44" +p %"v55";
    %"v61" = %"v4" +p %"v55";
    %"chk2" : A = (Check 0 8 Read 1) %"v61";
    %"v62" : L = (RawLoad LdL 0) %"chk2";
    %"iw_1.iw_1.v4" : L = Shr %"v25", #32;
    %"iw_1.iw_2.v6" : L = And %"v25", #4294967295;
    %"iw_1.v23" : L = Urem %"pr.13", %"iw_1.iw_1.v4";
    %"iw_1.v26" : L = Udiv %"pr.13", %"iw_1.iw_1.v4";
    %"iw_1.v29" : L = Mul %"iw_1.v26", %"iw_1.iw_2.v6";
    %"iw_1.v33" : L = Shl %"iw_1.v23", #32;
    %"iw_1.iw_3.v4" : L = Shr %"v62", #32;
    %"iw_1.v36" : L = Or %"iw_1.v33", %"iw_1.iw_3.v4";
    %"iw_1.v42" : W = (Cmp Ult L) %"iw_1.v36", %"iw_1.v29"
    => br %"iw_1.v42" ? "iw_1.L37" : "iw_1.L39" };
  ir_blk{ @"iw_1.L37":
    %"iw_1.v44" : L = Sub %"iw_1.v26", #1;
    %"iw_1.v47" : L = Add %"iw_1.v36", %"v25";
    %"iw_1.v53" : W = (Cmp Uge L) %"iw_1.v47", %"v25"
    => br %"iw_1.v53" ? "iw_1.L48" : "iw_1.L39" };
  ir_blk{ @"iw_1.L48":
    %"iw_1.v59" : W = (Cmp Ult L) %"iw_1.v47", %"iw_1.v29"
    => br %"iw_1.v59" ? "iw_1.L54" : "iw_1.L39" };
  ir_blk{ @"iw_1.L54":
    %"iw_1.v61" : L = Sub %"iw_1.v44", #1;
    %"iw_1.v64" : L = Add %"iw_1.v47", %"v25"
    => goto "iw_1.L39" };
  ir_blk{ @"iw_1.L39" [%"iw_1.pr.7" : L = phi("iw_1.L54" => %"iw_1.v64", "iw_1.L48" => %"iw_1.v47", "iw_1.L37" => %"iw_1.v47", "L48" => %"iw_1.v36"); %"iw_1.pr.1" : L = phi("iw_1.L54" => %"iw_1.v61", "iw_1.L48" => %"iw_1.v44", "iw_1.L37" => %"iw_1.v44", "L48" => %"iw_1.v26")]:
    %"iw_1.v67" : L = Sub %"iw_1.pr.7", %"iw_1.v29";
    %"iw_1.v70" : L = Urem %"iw_1.v67", %"iw_1.iw_1.v4";
    %"iw_1.v73" : L = Udiv %"iw_1.v67", %"iw_1.iw_1.v4";
    %"iw_1.v76" : L = Mul %"iw_1.v73", %"iw_1.iw_2.v6";
    %"iw_1.v80" : L = Shl %"iw_1.v70", #32;
    %"iw_1.iw_4.v6" : L = And %"v62", #4294967295;
    %"iw_1.v83" : L = Or %"iw_1.v80", %"iw_1.iw_4.v6";
    %"iw_1.v89" : W = (Cmp Ult L) %"iw_1.v83", %"iw_1.v76"
    => br %"iw_1.v89" ? "iw_1.L84" : "iw_1.L86" };
  ir_blk{ @"iw_1.L84":
    %"iw_1.v91" : L = Sub %"iw_1.v73", #1;
    %"iw_1.v94" : L = Add %"iw_1.v83", %"v25";
    %"iw_1.v100" : W = (Cmp Uge L) %"iw_1.v94", %"v25"
    => br %"iw_1.v100" ? "iw_1.L95" : "iw_1.L86" };
  ir_blk{ @"iw_1.L95":
    %"iw_1.v106" : W = (Cmp Ult L) %"iw_1.v94", %"iw_1.v76"
    => br %"iw_1.v106" ? "iw_1.L101" : "iw_1.L86" };
  ir_blk{ @"iw_1.L101":
    %"iw_1.v108" : L = Sub %"iw_1.v91", #1;
    %"iw_1.v111" : L = Add %"iw_1.v94", %"v25"
    => goto "iw_1.L86" };
  ir_blk{ @"iw_1.L86" [%"iw_1.pr.11" : L = phi("iw_1.L101" => %"iw_1.v111", "iw_1.L95" => %"iw_1.v94", "iw_1.L84" => %"iw_1.v94", "iw_1.L39" => %"iw_1.v83"); %"iw_1.pr.5" : L = phi("iw_1.L101" => %"iw_1.v108", "iw_1.L95" => %"iw_1.v91", "iw_1.L84" => %"iw_1.v91", "iw_1.L39" => %"iw_1.v73")]:
    %"iw_1.v114" : L = Sub %"iw_1.pr.11", %"iw_1.v76";
    %"iw_1.v119" : L = Shl %"iw_1.pr.1", #32;
    %"iw_1.v121" : L = Or %"iw_1.v119", %"iw_1.pr.5";
    %"chk3" : A = (Check 0 8 Write 1) %"v56";
    store Wl [%"chk3" + 0] <- %"iw_1.v121";
    %"v65" : L = Sub %"pr.10", #1
    => goto poll "L47" };
  ir_blk{ @"L50":
    (Flight (a "v69") Sub [(FAddress (t "v44")); (FValue (t "v43"))] (LowerOf (t "v44")));
    %"v71" : L = Sub %"v2", #1
    => goto "L72" };
  ir_blk{ @"L72" [%"pr.14" : L = phi("L50" => %"pr.13", "iw_2.L86" => %"iw_2.v114"); %"pr.11" : L = phi("L50" => %"v71", "iw_2.L86" => %"v85")]:
    %"v77" : W = (Cmp Sge L) %"pr.11", #0
    => br %"v77" ? "L73" : "L75" };
  ir_blk{ @"L73":
    %"v80" : L = Shl %"pr.11", #3;
    %"v81" = %"v69" +p %"v80";
    %"iw_2.iw_1.v4" : L = Shr %"v25", #32;
    %"iw_2.iw_2.v6" : L = And %"v25", #4294967295;
    %"iw_2.v23" : L = Urem %"pr.14", %"iw_2.iw_1.v4";
    %"iw_2.v26" : L = Udiv %"pr.14", %"iw_2.iw_1.v4";
    %"iw_2.v29" : L = Mul %"iw_2.v26", %"iw_2.iw_2.v6";
    %"iw_2.v33" : L = Shl %"iw_2.v23", #32;
    %"iw_2.v42" : W = (Cmp Ult L) %"iw_2.v33", %"iw_2.v29"
    => br %"iw_2.v42" ? "iw_2.L37" : "iw_2.L39" };
  ir_blk{ @"iw_2.L37":
    %"iw_2.v44" : L = Sub %"iw_2.v26", #1;
    %"iw_2.v47" : L = Add %"iw_2.v33", %"v25";
    %"iw_2.v53" : W = (Cmp Uge L) %"iw_2.v47", %"v25"
    => br %"iw_2.v53" ? "iw_2.L48" : "iw_2.L39" };
  ir_blk{ @"iw_2.L48":
    %"iw_2.v59" : W = (Cmp Ult L) %"iw_2.v47", %"iw_2.v29"
    => br %"iw_2.v59" ? "iw_2.L54" : "iw_2.L39" };
  ir_blk{ @"iw_2.L54":
    %"iw_2.v61" : L = Sub %"iw_2.v44", #1;
    %"iw_2.v64" : L = Add %"iw_2.v47", %"v25"
    => goto "iw_2.L39" };
  ir_blk{ @"iw_2.L39" [%"iw_2.pr.7" : L = phi("iw_2.L54" => %"iw_2.v64", "iw_2.L48" => %"iw_2.v47", "iw_2.L37" => %"iw_2.v47", "L73" => %"iw_2.v33"); %"iw_2.pr.1" : L = phi("iw_2.L54" => %"iw_2.v61", "iw_2.L48" => %"iw_2.v44", "iw_2.L37" => %"iw_2.v44", "L73" => %"iw_2.v26")]:
    %"iw_2.v67" : L = Sub %"iw_2.pr.7", %"iw_2.v29";
    %"iw_2.v70" : L = Urem %"iw_2.v67", %"iw_2.iw_1.v4";
    %"iw_2.v73" : L = Udiv %"iw_2.v67", %"iw_2.iw_1.v4";
    %"iw_2.v76" : L = Mul %"iw_2.v73", %"iw_2.iw_2.v6";
    %"iw_2.v80" : L = Shl %"iw_2.v70", #32;
    %"iw_2.v89" : W = (Cmp Ult L) %"iw_2.v80", %"iw_2.v76"
    => br %"iw_2.v89" ? "iw_2.L84" : "iw_2.L86" };
  ir_blk{ @"iw_2.L84":
    %"iw_2.v91" : L = Sub %"iw_2.v73", #1;
    %"iw_2.v94" : L = Add %"iw_2.v80", %"v25";
    %"iw_2.v100" : W = (Cmp Uge L) %"iw_2.v94", %"v25"
    => br %"iw_2.v100" ? "iw_2.L95" : "iw_2.L86" };
  ir_blk{ @"iw_2.L95":
    %"iw_2.v106" : W = (Cmp Ult L) %"iw_2.v94", %"iw_2.v76"
    => br %"iw_2.v106" ? "iw_2.L101" : "iw_2.L86" };
  ir_blk{ @"iw_2.L101":
    %"iw_2.v108" : L = Sub %"iw_2.v91", #1;
    %"iw_2.v111" : L = Add %"iw_2.v94", %"v25"
    => goto "iw_2.L86" };
  ir_blk{ @"iw_2.L86" [%"iw_2.pr.11" : L = phi("iw_2.L101" => %"iw_2.v111", "iw_2.L95" => %"iw_2.v94", "iw_2.L84" => %"iw_2.v94", "iw_2.L39" => %"iw_2.v80"); %"iw_2.pr.5" : L = phi("iw_2.L101" => %"iw_2.v108", "iw_2.L95" => %"iw_2.v91", "iw_2.L84" => %"iw_2.v91", "iw_2.L39" => %"iw_2.v73")]:
    %"iw_2.v114" : L = Sub %"iw_2.pr.11", %"iw_2.v76";
    %"iw_2.v119" : L = Shl %"iw_2.pr.1", #32;
    %"iw_2.v121" : L = Or %"iw_2.v119", %"iw_2.pr.5";
    %"chk4" : A = (Check 0 8 Write 1) %"v81";
    store Wl [%"chk4" + 0] <- %"iw_2.v121";
    %"v85" : L = Sub %"pr.11", #1
    => goto poll "L72" };
  ir_blk{ @"L75":
    %"chk5" : A = (Check 0 8 Write 1) %"v4";
    store Wl [%"chk5" + 0] <- %"pr.14"
    => goto "L15" };
  ir_blk{ @"L89":
    %"v98" : L = Sub %"v6", #2;
    %"v99" : L = Shl %"v98", #3;
    %"v100" = %"v4" +p %"v99";
    %"v102" = %"v8" +p #8;
    %"chk6" : A = (Check 0 8 Read 1) %"v102";
    %"v103" : L = (RawLoad LdL 0) %"chk6";
    %"chk7" : A = (HalfCheck Lower 0 8 Read 1) %"chk6", %"v8";
    %"v106" : L = (RawLoad LdL 0) %"chk7";
    %"v108" = %"v100" +p #8;
    %"chk8" : A = (Check 0 8 Read 1) %"v108";
    %"v109" : L = (RawLoad LdL 0) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Read 1) %"chk8", %"v100";
    %"v112" : L = (RawLoad LdL 0) %"chk9";
    %"v118" : W = (Cmp Uge L) %"v109", %"v103"
    => br %"v118" ? "L119" : "L120" };
  ir_blk{ @"L119":
    %"v123" : W = (Cmp Ugt L) %"v109", %"v103"
    => br %"v123" ? "L120" : "L124" };
  ir_blk{ @"L124":
    %"v128" : W = (Cmp Uge L) %"v112", %"v106"
    => goto "L120" };
  ir_blk{ @"L120" [%"v132" : W = phi("L89" => #0, "L119" => #1, "L124" => %"v128")]:
    => br %"v132" ? "iw_3.start" : "L115" };
  ir_blk{ @"iw_3.start":
    %"iw_3.iw_1.iw_1.v8" : L = Xor %"v106", #(-1);
    %"iw_3.iw_1.iw_1.v12" : L = Xor %"v103", #(-1);
    %"iw_3.iw_1.iw_1.iw_1.v11" : L = Add %"iw_3.iw_1.iw_1.v8", #1;
    %"iw_3.iw_1.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_3.iw_1.iw_1.iw_1.v11", %"iw_3.iw_1.iw_1.v8";
    %"iw_3.iw_1.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_3.iw_1.iw_1.iw_1.v13";
    %"iw_3.iw_1.iw_1.iw_1.v25" : L = Add %"iw_3.iw_1.iw_1.v12", %"iw_3.iw_1.iw_1.iw_1.v24";
    %"iw_3.iw_1.iw_2.v11" : L = Add %"v112", %"iw_3.iw_1.iw_1.iw_1.v11";
    %"iw_3.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_3.iw_1.iw_2.v11", %"v112";
    %"iw_3.iw_1.iw_2.v22" : L = Add %"v109", %"iw_3.iw_1.iw_1.iw_1.v25";
    %"iw_3.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_3.iw_1.iw_2.v13";
    %"iw_3.iw_1.iw_2.v25" : L = Add %"iw_3.iw_1.iw_2.v22", %"iw_3.iw_1.iw_2.v24"
    => goto "L115" };
  ir_blk{ @"L115" [%"pr.22" : L = phi("iw_3.start" => %"iw_3.iw_1.iw_2.v11", "L120" => %"v112"); %"pr.16" : L = phi("iw_3.start" => %"iw_3.iw_1.iw_2.v25", "L120" => %"v109"); %"pr.5" : L = phi("iw_3.start" => #1, "L120" => #0)]:
    %"v139" : L = Add %"v2", %"v6";
    %"v140" : L = Sub %"v139", #2;
    %"v141" : L = Sub %"v140", #1
    => goto "L142" };
  ir_blk{ @"L142" [%"pr.23" : L = phi("L115" => %"pr.22", "L144" => %"pr.24"); %"pr.17" : L = phi("L115" => %"pr.16", "L144" => %"pr.18"); %"pr.15" : L = phi("L115" => %"v141", "L144" => %"v254"); %"pr.1" : P = phi("L115" => %"v100", "L144" => %"pr.2")]:
    %"v147" : W = (Cmp Sge L) %"pr.15", #0
    => br %"v147" ? "L143" : "L145" };
  ir_blk{ @"L143":
    %"v155" : W = (Cmp Sge L) %"pr.15", %"v2"
    => br %"v155" ? "L150" : "L151" };
  ir_blk{ @"L150":
    (Flight (a "v157") Sub [(FAddress (t "pr.1")); (FValue (Const 8))] (LowerOf (t "pr.1")))
    => goto "L152" };
  ir_blk{ @"L151":
    %"chk10" : A = (Check 0 8 Write 1) %"pr.1";
    store Wl [%"chk10" + 0] <- #0
    => goto "L152" };
  ir_blk{ @"L152" [%"pr.2" : P = phi("L150" => %"v157", "L151" => %"pr.1")]:
    %"v165" : W = (Cmp Eq L) %"pr.17", %"v103"
    => br %"v165" ? "L160" : "iw_5.start" };
  ir_blk{ @"L160":
    %"v169" : L = Add %"pr.23", %"v103";
    %"v175" : W = (Cmp Ult L) %"v169", %"v103"
    => br %"v175" ? "L170" : "L172" };
  ir_blk{ @"L170":
    %"v178" : L = Sub %"v169", %"v106";
    %"chk11" : A = (Check 0 8 Read 1) %"pr.2";
    %"v181" : L = (RawLoad LdL 0) %"chk11";
    %"iw_4.iw_1.v11" : L = Add %"v181", %"v106";
    %"iw_4.iw_1.v13" : W = (Cmp Ult L) %"iw_4.iw_1.v11", %"v181";
    %"iw_4.iw_1.v24" : L = (Ext Uw) %"iw_4.iw_1.v13";
    %"iw_4.iw_1.v25" : L = Add %"v178", %"iw_4.iw_1.v24";
    %"v185" : L = Shl %"pr.15", #3;
    %"v186" = %"v0" +p %"v185";
    %"chk12" : A = (Check 0 8 Write 1) %"v186";
    store Wl [%"chk12" + 0] <- #18446744073709551615
    => goto "L144" };
  ir_blk{ @"L172":
    %"v191" : W = (Cmp Ne L) %"v106", #0;
    %"v192" : L = (Ext Sw) %"v191";
    %"v193" : L = Sub %"v106", %"v192";
    %"v195" : L = Neg %"v106"
    => goto "L162" };
  ir_blk{ @"iw_5.start":
    %"iw_5.iw_1.v4" : L = Shr %"v103", #32;
    %"iw_5.iw_2.v6" : L = And %"v103", #4294967295;
    %"iw_5.v23" : L = Urem %"pr.17", %"iw_5.iw_1.v4";
    %"iw_5.v26" : L = Udiv %"pr.17", %"iw_5.iw_1.v4";
    %"iw_5.v29" : L = Mul %"iw_5.v26", %"iw_5.iw_2.v6";
    %"iw_5.v33" : L = Shl %"iw_5.v23", #32;
    %"iw_5.iw_3.v4" : L = Shr %"pr.23", #32;
    %"iw_5.v36" : L = Or %"iw_5.v33", %"iw_5.iw_3.v4";
    %"iw_5.v42" : W = (Cmp Ult L) %"iw_5.v36", %"iw_5.v29"
    => br %"iw_5.v42" ? "iw_5.L37" : "iw_5.L39" };
  ir_blk{ @"iw_5.L37":
    %"iw_5.v44" : L = Sub %"iw_5.v26", #1;
    %"iw_5.v47" : L = Add %"iw_5.v36", %"v103";
    %"iw_5.v53" : W = (Cmp Uge L) %"iw_5.v47", %"v103"
    => br %"iw_5.v53" ? "iw_5.L48" : "iw_5.L39" };
  ir_blk{ @"iw_5.L48":
    %"iw_5.v59" : W = (Cmp Ult L) %"iw_5.v47", %"iw_5.v29"
    => br %"iw_5.v59" ? "iw_5.L54" : "iw_5.L39" };
  ir_blk{ @"iw_5.L54":
    %"iw_5.v61" : L = Sub %"iw_5.v44", #1;
    %"iw_5.v64" : L = Add %"iw_5.v47", %"v103"
    => goto "iw_5.L39" };
  ir_blk{ @"iw_5.L39" [%"iw_5.pr.7" : L = phi("iw_5.L54" => %"iw_5.v64", "iw_5.L48" => %"iw_5.v47", "iw_5.L37" => %"iw_5.v47", "iw_5.start" => %"iw_5.v36"); %"iw_5.pr.1" : L = phi("iw_5.L54" => %"iw_5.v61", "iw_5.L48" => %"iw_5.v44", "iw_5.L37" => %"iw_5.v44", "iw_5.start" => %"iw_5.v26")]:
    %"iw_5.v67" : L = Sub %"iw_5.pr.7", %"iw_5.v29";
    %"iw_5.v70" : L = Urem %"iw_5.v67", %"iw_5.iw_1.v4";
    %"iw_5.v73" : L = Udiv %"iw_5.v67", %"iw_5.iw_1.v4";
    %"iw_5.v76" : L = Mul %"iw_5.v73", %"iw_5.iw_2.v6";
    %"iw_5.v80" : L = Shl %"iw_5.v70", #32;
    %"iw_5.iw_4.v6" : L = And %"pr.23", #4294967295;
    %"iw_5.v83" : L = Or %"iw_5.v80", %"iw_5.iw_4.v6";
    %"iw_5.v89" : W = (Cmp Ult L) %"iw_5.v83", %"iw_5.v76"
    => br %"iw_5.v89" ? "iw_5.L84" : "iw_5.L86" };
  ir_blk{ @"iw_5.L84":
    %"iw_5.v91" : L = Sub %"iw_5.v73", #1;
    %"iw_5.v94" : L = Add %"iw_5.v83", %"v103";
    %"iw_5.v100" : W = (Cmp Uge L) %"iw_5.v94", %"v103"
    => br %"iw_5.v100" ? "iw_5.L95" : "iw_5.L86" }] [ir_blk{ @"iw_5.L95":
    %"iw_5.v106" : W = (Cmp Ult L) %"iw_5.v94", %"iw_5.v76"
    => br %"iw_5.v106" ? "iw_5.L101" : "iw_5.L86" };
  ir_blk{ @"iw_5.L101":
    %"iw_5.v108" : L = Sub %"iw_5.v91", #1;
    %"iw_5.v111" : L = Add %"iw_5.v94", %"v103"
    => goto "iw_5.L86" };
  ir_blk{ @"iw_5.L86" [%"iw_5.pr.11" : L = phi("iw_5.L101" => %"iw_5.v111", "iw_5.L95" => %"iw_5.v94", "iw_5.L84" => %"iw_5.v94", "iw_5.L39" => %"iw_5.v83"); %"iw_5.pr.5" : L = phi("iw_5.L101" => %"iw_5.v108", "iw_5.L95" => %"iw_5.v91", "iw_5.L84" => %"iw_5.v91", "iw_5.L39" => %"iw_5.v73")]:
    %"iw_5.v114" : L = Sub %"iw_5.pr.11", %"iw_5.v76";
    %"iw_5.v119" : L = Shl %"iw_5.pr.1", #32;
    %"iw_5.v121" : L = Or %"iw_5.v119", %"iw_5.pr.5";
    %"iw_6.iw_1.v23" : L = And %"v106", #4294967295;
    %"iw_6.iw_1.v26" : L = Shr %"v106", #32;
    %"iw_6.iw_1.v29" : L = And %"iw_5.v121", #4294967295;
    %"iw_6.iw_1.v32" : L = Shr %"iw_5.v121", #32;
    %"iw_6.iw_1.v38" : L = Mul %"iw_6.iw_1.v23", %"iw_6.iw_1.v29";
    %"iw_6.iw_1.v44" : L = Mul %"iw_6.iw_1.v23", %"iw_6.iw_1.v32";
    %"iw_6.iw_1.v50" : L = Mul %"iw_6.iw_1.v26", %"iw_6.iw_1.v29";
    %"iw_6.iw_1.v56" : L = Mul %"iw_6.iw_1.v26", %"iw_6.iw_1.v32";
    %"iw_6.iw_1.iw_1.v11" : L = Add %"iw_6.iw_1.v44", %"iw_6.iw_1.v50";
    %"iw_6.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_6.iw_1.iw_1.v11", %"iw_6.iw_1.v44";
    %"iw_6.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_6.iw_1.iw_1.v13";
    (Call (CTuple [((a "iw_6.iw_1.v74"), L); ((a "iw_6.iw_1.v75"), L)]) (Global (a "glibc_divrem#u128_lshift")) [(Arg L (t "iw_6.iw_1.iw_1.v11")); (Arg L (t "iw_6.iw_1.iw_1.v24")); (Arg W (Const 32))]);
    %"iw_6.iw_1.iw_2.v11" : L = Add %"iw_6.iw_1.v38", %"iw_6.iw_1.v74";
    %"iw_6.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_6.iw_1.iw_2.v11", %"iw_6.iw_1.v38";
    %"iw_6.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_6.iw_1.iw_2.v13";
    %"iw_6.iw_1.iw_2.v25" : L = Add %"iw_6.iw_1.v75", %"iw_6.iw_1.iw_2.v24";
    %"iw_6.iw_1.iw_3.v22" : L = Add %"iw_6.iw_1.iw_2.v25", %"iw_6.iw_1.v56"
    => goto "L162" };
  ir_blk{ @"L162" [%"pr.31" : L = phi("L172" => %"v169", "iw_5.L86" => %"iw_5.v114"); %"pr.28" : L = phi("L172" => #18446744073709551615, "iw_5.L86" => %"iw_5.v121"); %"pr.25" : L = phi("L172" => %"v195", "iw_5.L86" => %"iw_6.iw_1.iw_2.v11"); %"pr.19" : L = phi("L172" => %"v193", "iw_5.L86" => %"iw_6.iw_1.iw_3.v22")]:
    %"chk13" : A = (Check 0 8 Read 1) %"pr.2";
    %"v207" : L = (RawLoad LdL 0) %"chk13"
    => goto "L208" };
  ir_blk{ @"L208" [%"pr.32" : L = phi("L162" => %"pr.31", "L209" => %"v236"); %"pr.29" : L = phi("L162" => %"pr.28", "L209" => %"v230"); %"pr.26" : L = phi("L162" => %"pr.25", "L209" => %"iw_7.iw_1.iw_2.v11"); %"pr.20" : L = phi("L162" => %"pr.19", "L209" => %"iw_7.iw_1.iw_2.v25")]:
    %"v214" : W = (Cmp Ugt L) %"pr.20", %"pr.32"
    => br %"v214" ? "L216" : "L215" };
  ir_blk{ @"L215":
    %"v219" : W = (Cmp Eq L) %"pr.20", %"pr.32"
    => br %"v219" ? "L220" : "L216" };
  ir_blk{ @"L220":
    %"v224" : W = (Cmp Ugt L) %"pr.26", %"v207"
    => goto "L216" };
  ir_blk{ @"L216" [%"v228" : W = phi("L208" => #1, "L215" => #0, "L220" => %"v224")]:
    => br %"v228" ? "L209" : "L211" };
  ir_blk{ @"L209":
    %"v230" : L = Sub %"pr.29", #1;
    %"iw_7.iw_1.iw_1.v8" : L = Xor %"v106", #(-1);
    %"iw_7.iw_1.iw_1.iw_1.v11" : L = Add %"iw_7.iw_1.iw_1.v8", #1;
    %"iw_7.iw_1.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_7.iw_1.iw_1.iw_1.v11", %"iw_7.iw_1.iw_1.v8";
    %"iw_7.iw_1.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_7.iw_1.iw_1.iw_1.v13";
    %"iw_7.iw_1.iw_1.iw_1.v25" : L = Add %"iw_7.iw_1.iw_1.iw_1.v24", #18446744073709551615;
    %"iw_7.iw_1.iw_2.v11" : L = Add %"pr.26", %"iw_7.iw_1.iw_1.iw_1.v11";
    %"iw_7.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_7.iw_1.iw_2.v11", %"pr.26";
    %"iw_7.iw_1.iw_2.v22" : L = Add %"pr.20", %"iw_7.iw_1.iw_1.iw_1.v25";
    %"iw_7.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_7.iw_1.iw_2.v13";
    %"iw_7.iw_1.iw_2.v25" : L = Add %"iw_7.iw_1.iw_2.v22", %"iw_7.iw_1.iw_2.v24";
    %"v236" : L = Add %"pr.32", %"v103";
    %"v242" : W = (Cmp Uge L) %"v236", %"v103"
    => br %"v242" ? poll "L208" : "L211" };
  ir_blk{ @"L211" [%"pr.33" : L = phi("L209" => %"v236", "L216" => %"pr.32"); %"pr.30" : L = phi("L209" => %"v230", "L216" => %"pr.29"); %"pr.27" : L = phi("L209" => %"iw_7.iw_1.iw_2.v11", "L216" => %"pr.26"); %"pr.21" : L = phi("L209" => %"iw_7.iw_1.iw_2.v25", "L216" => %"pr.20")]:
    %"v246" : L = Shl %"pr.15", #3;
    %"v247" = %"v0" +p %"v246";
    %"chk14" : A = (Check 0 8 Write 1) %"v247";
    store Wl [%"chk14" + 0] <- %"pr.30";
    %"iw_8.iw_1.iw_1.v8" : L = Xor %"pr.27", #(-1);
    %"iw_8.iw_1.iw_1.v12" : L = Xor %"pr.21", #(-1);
    %"iw_8.iw_1.iw_1.iw_1.v11" : L = Add %"iw_8.iw_1.iw_1.v8", #1;
    %"iw_8.iw_1.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_8.iw_1.iw_1.iw_1.v11", %"iw_8.iw_1.iw_1.v8";
    %"iw_8.iw_1.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_8.iw_1.iw_1.iw_1.v13";
    %"iw_8.iw_1.iw_1.iw_1.v25" : L = Add %"iw_8.iw_1.iw_1.v12", %"iw_8.iw_1.iw_1.iw_1.v24";
    %"iw_8.iw_1.iw_2.v11" : L = Add %"v207", %"iw_8.iw_1.iw_1.iw_1.v11";
    %"iw_8.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_8.iw_1.iw_2.v11", %"v207";
    %"iw_8.iw_1.iw_2.v22" : L = Add %"pr.33", %"iw_8.iw_1.iw_1.iw_1.v25";
    %"iw_8.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_8.iw_1.iw_2.v13";
    %"iw_8.iw_1.iw_2.v25" : L = Add %"iw_8.iw_1.iw_2.v22", %"iw_8.iw_1.iw_2.v24"
    => goto "L144" };
  ir_blk{ @"L144" [%"pr.24" : L = phi("L170" => %"iw_4.iw_1.v11", "L211" => %"iw_8.iw_1.iw_2.v11"); %"pr.18" : L = phi("L170" => %"iw_4.iw_1.v25", "L211" => %"iw_8.iw_1.iw_2.v25")]:
    %"v254" : L = Sub %"pr.15", #1
    => goto poll "L142" };
  ir_blk{ @"L145":
    %"v256" = %"pr.1" +p #8;
    %"chk15" : A = (Check 0 8 Write 1) %"v256";
    store Wl [%"chk15" + 0] <- %"pr.17";
    %"chk16" : A = (HalfCheck Lower 0 8 Write 1) %"chk15", %"pr.1";
    store Wl [%"chk16" + 0] <- %"pr.23"
    => goto "L15" };
  ir_blk{ @"L261":
    %"v269" : L = Sub %"v6", %"v10";
    %"v270" : L = Shl %"v269", #3;
    %"v271" = %"v4" +p %"v270";
    %"v274" : L = Sub %"v10", #1;
    %"v275" : L = Shl %"v274", #3;
    %"v276" = %"v8" +p %"v275";
    %"chk17" : A = (Check 0 8 Read 1) %"v276";
    %"v277" : L = (RawLoad LdL 0) %"chk17";
    %"v280" : L = Sub %"v10", #2;
    %"v281" : L = Shl %"v280", #3;
    (Flight (a "v282") Sub [(FAddress (t "v276")); (FValue (Const 8))] (LowerOf (t "v276")));
    %"chk18" : A = (HalfCheck Lower 0 8 Read 1) %"chk17", %"v282";
    %"v283" : L = (RawLoad LdL 0) %"chk18";
    %"v288" = %"v271" +p %"v275";
    %"chk19" : A = (Check 0 8 Read 1) %"v288";
    %"v289" : L = (RawLoad LdL 0) %"chk19";
    %"v295" : W = (Cmp Uge L) %"v289", %"v277"
    => br %"v295" ? "L290" : "L292" };
  ir_blk{ @"L290":
    %"v301" : W = (Cmp Ugt L) %"v289", %"v277"
    => br %"v301" ? "L303" : "L302" };
  ir_blk{ @"L302":
    call %"v308" : W = $"__mpn_cmp"(P %"v271", P %"v8", L %"v274");
    %"v309" : W = (Cmp Sge W) %"v308", #0
    => goto "L303" };
  ir_blk{ @"L303" [%"v311" : W = phi("L290" => #1, "L302" => %"v309")]:
    => br %"v311" ? "L296" : "L292" };
  ir_blk{ @"L296":
    call %"v316" : L = $"__mpn_sub_n"(P %"v271", P %"v271", P %"v8", L %"v10");
    %"chk20" : A = (Renew 0 8 Read 1) %"chk19", %"v288";
    %"v322" : L = (RawLoad LdL 0) %"chk20"
    => goto "L292" };
  ir_blk{ @"L292" [%"pr.35" : L = phi("L296" => %"v322", "L303" => %"v289", "L261" => %"v289"); %"pr.7" : L = phi("L296" => #1, "L303" => #0, "L261" => #0)]:
    %"v325" : L = Add %"v2", %"v6";
    %"v327" : L = Sub %"v325", %"v10";
    %"v328" : L = Sub %"v327", #1
    => goto "L329" };
  ir_blk{ @"L329" [%"pr.37" : L = phi("L292" => %"pr.35", "L459" => %"v480"); %"pr.34" : L = phi("L292" => %"v328", "L459" => %"v482"); %"pr.3" : P = phi("L292" => %"v271", "L459" => %"pr.4")]:
    %"v334" : W = (Cmp Sge L) %"pr.34", #0
    => br %"v334" ? "L330" : "L15" };
  ir_blk{ @"L330":
    %"v344" : W = (Cmp Sge L) %"pr.34", %"v2"
    => br %"v344" ? "L339" : "L340" };
  ir_blk{ @"L339":
    (Flight (a "v346") Sub [(FAddress (t "pr.3")); (FValue (Const 8))] (LowerOf (t "pr.3")));
    %"v349" : L = Shl %"v10", #3;
    %"v350" = %"v346" +p %"v349";
    %"chk21" : A = (Check 0 8 Read 1) %"v350";
    %"v351" : L = (RawLoad LdL 0) %"chk21"
    => goto "L341" };
  ir_blk{ @"L340":
    %"v356" = %"pr.3" +p %"v275";
    %"chk22" : A = (Check 0 8 Read 1) %"v356";
    %"v357" : L = (RawLoad LdL 0) %"chk22"
    => goto "L364" };
  ir_blk{ @"L364" [%"pr.45" : L = phi("L365" => %"v381", "L340" => %"v274")]:
    %"v369" : W = (Cmp Sge L) %"pr.45", #0
    => br %"v369" ? "L365" : "L360" };
  ir_blk{ @"L365":
    %"v371" = %"pr.3" +p #8;
    %"v373" : L = Shl %"pr.45", #3;
    %"v374" = %"v371" +p %"v373";
    %"v378" = %"pr.3" +p %"v373";
    %"chk23" : A = (Check 0 8 Read 1) %"v378";
    %"v379" : L = (RawLoad LdL 0) %"chk23";
    %"chk24" : A = (Check 0 8 Write 1) %"v374";
    store Wl [%"chk24" + 0] <- %"v379";
    %"v381" : L = Sub %"pr.45", #1
    => goto poll "L364" };
  ir_blk{ @"L360":
    %"chk25" : A = (Check 0 8 Write 1) %"pr.3";
    store Wl [%"chk25" + 0] <- #0
    => goto "L341" };
  ir_blk{ @"L341" [%"pr.44" : L = phi("L339" => %"v351", "L360" => %"v357"); %"pr.4" : P = phi("L339" => %"v346", "L360" => %"pr.3")]:
    %"v389" : W = (Cmp Eq L) %"pr.37", %"v277"
    => br %"v389" ? "L386" : "L385" };
  ir_blk{ @"L385":
    %"v397" = %"pr.4" +p %"v275";
    %"chk26" : A = (Check 0 8 Read 1) %"v397";
    %"v398" : L = (RawLoad LdL 0) %"chk26";
    %"iw_9.iw_1.v4" : L = Shr %"v277", #32;
    %"iw_9.iw_2.v6" : L = And %"v277", #4294967295;
    %"iw_9.v23" : L = Urem %"pr.37", %"iw_9.iw_1.v4";
    %"iw_9.v26" : L = Udiv %"pr.37", %"iw_9.iw_1.v4";
    %"iw_9.v29" : L = Mul %"iw_9.v26", %"iw_9.iw_2.v6";
    %"iw_9.v33" : L = Shl %"iw_9.v23", #32;
    %"iw_9.iw_3.v4" : L = Shr %"v398", #32;
    %"iw_9.v36" : L = Or %"iw_9.v33", %"iw_9.iw_3.v4";
    %"iw_9.v42" : W = (Cmp Ult L) %"iw_9.v36", %"iw_9.v29"
    => br %"iw_9.v42" ? "iw_9.L37" : "iw_9.L39" };
  ir_blk{ @"iw_9.L37":
    %"iw_9.v44" : L = Sub %"iw_9.v26", #1;
    %"iw_9.v47" : L = Add %"iw_9.v36", %"v277";
    %"iw_9.v53" : W = (Cmp Uge L) %"iw_9.v47", %"v277"
    => br %"iw_9.v53" ? "iw_9.L48" : "iw_9.L39" };
  ir_blk{ @"iw_9.L48":
    %"iw_9.v59" : W = (Cmp Ult L) %"iw_9.v47", %"iw_9.v29"
    => br %"iw_9.v59" ? "iw_9.L54" : "iw_9.L39" };
  ir_blk{ @"iw_9.L54":
    %"iw_9.v61" : L = Sub %"iw_9.v44", #1;
    %"iw_9.v64" : L = Add %"iw_9.v47", %"v277"
    => goto "iw_9.L39" };
  ir_blk{ @"iw_9.L39" [%"iw_9.pr.7" : L = phi("iw_9.L54" => %"iw_9.v64", "iw_9.L48" => %"iw_9.v47", "iw_9.L37" => %"iw_9.v47", "L385" => %"iw_9.v36"); %"iw_9.pr.1" : L = phi("iw_9.L54" => %"iw_9.v61", "iw_9.L48" => %"iw_9.v44", "iw_9.L37" => %"iw_9.v44", "L385" => %"iw_9.v26")]:
    %"iw_9.v67" : L = Sub %"iw_9.pr.7", %"iw_9.v29";
    %"iw_9.v70" : L = Urem %"iw_9.v67", %"iw_9.iw_1.v4";
    %"iw_9.v73" : L = Udiv %"iw_9.v67", %"iw_9.iw_1.v4";
    %"iw_9.v76" : L = Mul %"iw_9.v73", %"iw_9.iw_2.v6";
    %"iw_9.v80" : L = Shl %"iw_9.v70", #32;
    %"iw_9.iw_4.v6" : L = And %"v398", #4294967295;
    %"iw_9.v83" : L = Or %"iw_9.v80", %"iw_9.iw_4.v6";
    %"iw_9.v89" : W = (Cmp Ult L) %"iw_9.v83", %"iw_9.v76"
    => br %"iw_9.v89" ? "iw_9.L84" : "iw_9.L86" };
  ir_blk{ @"iw_9.L84":
    %"iw_9.v91" : L = Sub %"iw_9.v73", #1;
    %"iw_9.v94" : L = Add %"iw_9.v83", %"v277";
    %"iw_9.v100" : W = (Cmp Uge L) %"iw_9.v94", %"v277"
    => br %"iw_9.v100" ? "iw_9.L95" : "iw_9.L86" };
  ir_blk{ @"iw_9.L95":
    %"iw_9.v106" : W = (Cmp Ult L) %"iw_9.v94", %"iw_9.v76"
    => br %"iw_9.v106" ? "iw_9.L101" : "iw_9.L86" };
  ir_blk{ @"iw_9.L101":
    %"iw_9.v108" : L = Sub %"iw_9.v91", #1;
    %"iw_9.v111" : L = Add %"iw_9.v94", %"v277"
    => goto "iw_9.L86" };
  ir_blk{ @"iw_9.L86" [%"iw_9.pr.11" : L = phi("iw_9.L101" => %"iw_9.v111", "iw_9.L95" => %"iw_9.v94", "iw_9.L84" => %"iw_9.v94", "iw_9.L39" => %"iw_9.v83"); %"iw_9.pr.5" : L = phi("iw_9.L101" => %"iw_9.v108", "iw_9.L95" => %"iw_9.v91", "iw_9.L84" => %"iw_9.v91", "iw_9.L39" => %"iw_9.v73")]:
    %"iw_9.v114" : L = Sub %"iw_9.pr.11", %"iw_9.v76";
    %"iw_9.v119" : L = Shl %"iw_9.pr.1", #32;
    %"iw_9.v121" : L = Or %"iw_9.v119", %"iw_9.pr.5";
    %"iw_10.iw_1.v23" : L = And %"v283", #4294967295;
    %"iw_10.iw_1.v26" : L = Shr %"v283", #32;
    %"iw_10.iw_1.v29" : L = And %"iw_9.v121", #4294967295;
    %"iw_10.iw_1.v32" : L = Shr %"iw_9.v121", #32;
    %"iw_10.iw_1.v38" : L = Mul %"iw_10.iw_1.v23", %"iw_10.iw_1.v29";
    %"iw_10.iw_1.v44" : L = Mul %"iw_10.iw_1.v23", %"iw_10.iw_1.v32";
    %"iw_10.iw_1.v50" : L = Mul %"iw_10.iw_1.v26", %"iw_10.iw_1.v29";
    %"iw_10.iw_1.v56" : L = Mul %"iw_10.iw_1.v26", %"iw_10.iw_1.v32";
    %"iw_10.iw_1.iw_1.v11" : L = Add %"iw_10.iw_1.v44", %"iw_10.iw_1.v50";
    %"iw_10.iw_1.iw_1.v13" : W = (Cmp Ult L) %"iw_10.iw_1.iw_1.v11", %"iw_10.iw_1.v44";
    %"iw_10.iw_1.iw_1.v24" : L = (Ext Uw) %"iw_10.iw_1.iw_1.v13";
    (Call (CTuple [((a "iw_10.iw_1.v74"), L); ((a "iw_10.iw_1.v75"), L)]) (Global (a "glibc_divrem#u128_lshift")) [(Arg L (t "iw_10.iw_1.iw_1.v11")); (Arg L (t "iw_10.iw_1.iw_1.v24")); (Arg W (Const 32))]);
    %"iw_10.iw_1.iw_2.v11" : L = Add %"iw_10.iw_1.v38", %"iw_10.iw_1.v74";
    %"iw_10.iw_1.iw_2.v13" : W = (Cmp Ult L) %"iw_10.iw_1.iw_2.v11", %"iw_10.iw_1.v38";
    %"iw_10.iw_1.iw_2.v24" : L = (Ext Uw) %"iw_10.iw_1.iw_2.v13";
    %"iw_10.iw_1.iw_2.v25" : L = Add %"iw_10.iw_1.v75", %"iw_10.iw_1.iw_2.v24";
    %"iw_10.iw_1.iw_3.v22" : L = Add %"iw_10.iw_1.iw_2.v25", %"iw_10.iw_1.v56"
    => goto "L406" };
  ir_blk{ @"L406" [%"pr.46" : L = phi("L438" => %"v435", "iw_9.L86" => %"iw_9.v114"); %"pr.43" : L = phi("L438" => %"v448", "iw_9.L86" => %"iw_10.iw_1.iw_3.v22"); %"pr.40" : L = phi("L438" => %"v432", "iw_9.L86" => %"iw_9.v121"); %"pr.38" : L = phi("L438" => %"v451", "iw_9.L86" => %"iw_10.iw_1.iw_2.v11")]:
    %"v411" : W = (Cmp Ugt L) %"pr.43", %"pr.46"
    => br %"v411" ? "L413" : "L412" };
  ir_blk{ @"L412":
    %"v416" : W = (Cmp Eq L) %"pr.43", %"pr.46"
    => br %"v416" ? "L417" : "L413" };
  ir_blk{ @"L417":
    %"v424" = %"pr.4" +p %"v281";
    %"chk27" : A = (Check 0 8 Read 1) %"v424";
    %"v425" : L = (RawLoad LdL 0) %"chk27";
    %"v426" : W = (Cmp Ugt L) %"pr.38", %"v425"
    => goto "L413" };
  ir_blk{ @"L413" [%"v430" : W = phi("L406" => #1, "L412" => #0, "L417" => %"v426")]:
    => br %"v430" ? "L407" : "L386" };
  ir_blk{ @"L407":
    %"v432" : L = Sub %"pr.40", #1;
    %"v435" : L = Add %"pr.46", %"v277";
    %"v441" : W = (Cmp Ult L) %"v435", %"v277"
    => br %"v441" ? "L386" : "L438" };
  ir_blk{ @"L438":
    %"v446" : W = (Cmp Ult L) %"pr.38", %"v283";
    %"v447" : L = (Ext Sw) %"v446";
    %"v448" : L = Sub %"pr.43", %"v447";
    %"v451" : L = Sub %"pr.38", %"v283"
    => goto poll "L406" };
  ir_blk{ @"L386" [%"pr.39" : L = phi("L341" => #18446744073709551615, "L413" => %"pr.40", "L407" => %"v432")]:
    call %"v456" : L = $"__mpn_submul_1"(P %"pr.4", P %"v8", L %"v10", L %"pr.39");
    %"v462" : W = (Cmp Ne L) %"pr.44", %"v456"
    => br %"v462" ? "L457" : "L459" };
  ir_blk{ @"L457":
    call %"v467" : L = $"__mpn_add_n"(P %"pr.4", P %"pr.4", P %"v8", L %"v10");
    %"v469" : L = Sub %"pr.39", #1
    => goto "L459" };
  ir_blk{ @"L459" [%"pr.42" : L = phi("L457" => %"v469", "L386" => %"pr.39")]:
    %"v472" : L = Shl %"pr.34", #3;
    %"v473" = %"v0" +p %"v472";
    %"chk28" : A = (Check 0 8 Write 1) %"v473";
    store Wl [%"chk28" + 0] <- %"pr.42";
    %"v479" = %"pr.4" +p %"v275";
    %"chk29" : A = (Check 0 8 Read 1) %"v479";
    %"v480" : L = (RawLoad LdL 0) %"chk29";
    %"v482" : L = Sub %"pr.34", #1
    => goto poll "L329" };
  ir_blk{ @"L484":
    %"v485" : W = (Cmp Eq L) %"v10", #1
    => br %"v485" ? poll "L19" : "L486" };
  ir_blk{ @"L486":
    %"v487" : W = (Cmp Eq L) %"v10", #2
    => br %"v487" ? poll "L89" : poll "L261" };
  ir_blk{ @"L15" [%"pr.6" : L = phi("L145" => %"pr.5", "L75" => %"pr.9", "L329" => %"pr.7")]:
    => ret %"pr.6" }])) }.

Definition fn_glibc_divrem'23u128_lshift : func :=
  ir_fn{ "local" "glibc_divrem#u128_lshift"(L %"v0", L %"v1", W %"v4") -> (RTuple [L; L]) blocks ((app (app [ir_blk{ @"start":
    %"v51" : W = (Cmp Ult W) %"v4", #64
    => br %"v51" ? "L52" : "L53" };
  ir_blk{ @"L9":
    => (JRets [(t "v0"); (t "v1")]) };
  ir_blk{ @"L13":
    %"v20" : L = Shl %"v1", %"v4";
    %"v23" : W = Sub #64, %"v4";
    %"v24" : L = Shr %"v0", %"v23";
    %"v25" : L = Or %"v20", %"v24";
    %"v28" : L = Shl %"v0", %"v4"
    => (JRets [(t "v28"); (t "v25")]) };
  ir_blk{ @"L32":
    %"v38" : W = Sub %"v4", #64;
    %"v39" : L = Shl %"v0", %"v38"
    => (JRets [(Const 0); (t "v39")]) };
  ir_blk{ @"L43":
    => (JRets [(Const 0); (Const 0)]) };
  ir_blk{ @"L52":
    %"v54" : W = (Cmp Ult W) %"v4", #32
    => br %"v54" ? "L55" : "L56" };
  ir_blk{ @"L55":
    %"v57" : W = (Cmp Ult W) %"v4", #16
    => br %"v57" ? "L58" : "L59" };
  ir_blk{ @"L58":
    %"v60" : W = (Cmp Ult W) %"v4", #8
    => br %"v60" ? "L61" : "L62" };
  ir_blk{ @"L61":
    %"v63" : W = (Cmp Ult W) %"v4", #4
    => br %"v63" ? "L64" : "L65" };
  ir_blk{ @"L64":
    %"v66" : W = (Cmp Eq W) %"v4", #0
    => br %"v66" ? poll "L9" : "L67" };
  ir_blk{ @"L67":
    %"v68" : W = (Cmp Eq W) %"v4", #1
    => br %"v68" ? poll "L13" : "L69" };
  ir_blk{ @"L69":
    %"v70" : W = (Cmp Eq W) %"v4", #2
    => br %"v70" ? poll "L13" : "L71" };
  ir_blk{ @"L71":
    %"v72" : W = (Cmp Eq W) %"v4", #3
    => br %"v72" ? poll "L13" : poll "L43" };
  ir_blk{ @"L65":
    %"v74" : W = (Cmp Eq W) %"v4", #4
    => br %"v74" ? poll "L13" : "L75" };
  ir_blk{ @"L75":
    %"v76" : W = (Cmp Eq W) %"v4", #5
    => br %"v76" ? poll "L13" : "L77" };
  ir_blk{ @"L77":
    %"v78" : W = (Cmp Eq W) %"v4", #6
    => br %"v78" ? poll "L13" : "L79" };
  ir_blk{ @"L79":
    %"v80" : W = (Cmp Eq W) %"v4", #7
    => br %"v80" ? poll "L13" : poll "L43" };
  ir_blk{ @"L62":
    %"v82" : W = (Cmp Ult W) %"v4", #12
    => br %"v82" ? "L83" : "L84" };
  ir_blk{ @"L83":
    %"v85" : W = (Cmp Eq W) %"v4", #8
    => br %"v85" ? poll "L13" : "L86" };
  ir_blk{ @"L86":
    %"v87" : W = (Cmp Eq W) %"v4", #9
    => br %"v87" ? poll "L13" : "L88" };
  ir_blk{ @"L88":
    %"v89" : W = (Cmp Eq W) %"v4", #10
    => br %"v89" ? poll "L13" : "L90" };
  ir_blk{ @"L90":
    %"v91" : W = (Cmp Eq W) %"v4", #11
    => br %"v91" ? poll "L13" : poll "L43" };
  ir_blk{ @"L84":
    %"v93" : W = (Cmp Eq W) %"v4", #12
    => br %"v93" ? poll "L13" : "L94" };
  ir_blk{ @"L94":
    %"v95" : W = (Cmp Eq W) %"v4", #13
    => br %"v95" ? poll "L13" : "L96" };
  ir_blk{ @"L96":
    %"v97" : W = (Cmp Eq W) %"v4", #14
    => br %"v97" ? poll "L13" : "L98" };
  ir_blk{ @"L98":
    %"v99" : W = (Cmp Eq W) %"v4", #15
    => br %"v99" ? poll "L13" : poll "L43" };
  ir_blk{ @"L59":
    %"v101" : W = (Cmp Ult W) %"v4", #24
    => br %"v101" ? "L102" : "L103" };
  ir_blk{ @"L102":
    %"v104" : W = (Cmp Ult W) %"v4", #20
    => br %"v104" ? "L105" : "L106" };
  ir_blk{ @"L105":
    %"v107" : W = (Cmp Eq W) %"v4", #16
    => br %"v107" ? poll "L13" : "L108" };
  ir_blk{ @"L108":
    %"v109" : W = (Cmp Eq W) %"v4", #17
    => br %"v109" ? poll "L13" : "L110" };
  ir_blk{ @"L110":
    %"v111" : W = (Cmp Eq W) %"v4", #18
    => br %"v111" ? poll "L13" : "L112" };
  ir_blk{ @"L112":
    %"v113" : W = (Cmp Eq W) %"v4", #19
    => br %"v113" ? poll "L13" : poll "L43" };
  ir_blk{ @"L106":
    %"v115" : W = (Cmp Eq W) %"v4", #20
    => br %"v115" ? poll "L13" : "L116" };
  ir_blk{ @"L116":
    %"v117" : W = (Cmp Eq W) %"v4", #21
    => br %"v117" ? poll "L13" : "L118" };
  ir_blk{ @"L118":
    %"v119" : W = (Cmp Eq W) %"v4", #22
    => br %"v119" ? poll "L13" : "L120" };
  ir_blk{ @"L120":
    %"v121" : W = (Cmp Eq W) %"v4", #23
    => br %"v121" ? poll "L13" : poll "L43" };
  ir_blk{ @"L103":
    %"v123" : W = (Cmp Ult W) %"v4", #28
    => br %"v123" ? "L124" : "L125" };
  ir_blk{ @"L124":
    %"v126" : W = (Cmp Eq W) %"v4", #24
    => br %"v126" ? poll "L13" : "L127" };
  ir_blk{ @"L127":
    %"v128" : W = (Cmp Eq W) %"v4", #25
    => br %"v128" ? poll "L13" : "L129" };
  ir_blk{ @"L129":
    %"v130" : W = (Cmp Eq W) %"v4", #26
    => br %"v130" ? poll "L13" : "L131" }] [ir_blk{ @"L131":
    %"v132" : W = (Cmp Eq W) %"v4", #27
    => br %"v132" ? poll "L13" : poll "L43" };
  ir_blk{ @"L125":
    %"v134" : W = (Cmp Eq W) %"v4", #28
    => br %"v134" ? poll "L13" : "L135" };
  ir_blk{ @"L135":
    %"v136" : W = (Cmp Eq W) %"v4", #29
    => br %"v136" ? poll "L13" : "L137" };
  ir_blk{ @"L137":
    %"v138" : W = (Cmp Eq W) %"v4", #30
    => br %"v138" ? poll "L13" : "L139" };
  ir_blk{ @"L139":
    %"v140" : W = (Cmp Eq W) %"v4", #31
    => br %"v140" ? poll "L13" : poll "L43" };
  ir_blk{ @"L56":
    %"v142" : W = (Cmp Ult W) %"v4", #48
    => br %"v142" ? "L143" : "L144" };
  ir_blk{ @"L143":
    %"v145" : W = (Cmp Ult W) %"v4", #40
    => br %"v145" ? "L146" : "L147" };
  ir_blk{ @"L146":
    %"v148" : W = (Cmp Ult W) %"v4", #36
    => br %"v148" ? "L149" : "L150" };
  ir_blk{ @"L149":
    %"v151" : W = (Cmp Eq W) %"v4", #32
    => br %"v151" ? poll "L13" : "L152" };
  ir_blk{ @"L152":
    %"v153" : W = (Cmp Eq W) %"v4", #33
    => br %"v153" ? poll "L13" : "L154" };
  ir_blk{ @"L154":
    %"v155" : W = (Cmp Eq W) %"v4", #34
    => br %"v155" ? poll "L13" : "L156" };
  ir_blk{ @"L156":
    %"v157" : W = (Cmp Eq W) %"v4", #35
    => br %"v157" ? poll "L13" : poll "L43" };
  ir_blk{ @"L150":
    %"v159" : W = (Cmp Eq W) %"v4", #36
    => br %"v159" ? poll "L13" : "L160" };
  ir_blk{ @"L160":
    %"v161" : W = (Cmp Eq W) %"v4", #37
    => br %"v161" ? poll "L13" : "L162" };
  ir_blk{ @"L162":
    %"v163" : W = (Cmp Eq W) %"v4", #38
    => br %"v163" ? poll "L13" : "L164" };
  ir_blk{ @"L164":
    %"v165" : W = (Cmp Eq W) %"v4", #39
    => br %"v165" ? poll "L13" : poll "L43" };
  ir_blk{ @"L147":
    %"v167" : W = (Cmp Ult W) %"v4", #44
    => br %"v167" ? "L168" : "L169" };
  ir_blk{ @"L168":
    %"v170" : W = (Cmp Eq W) %"v4", #40
    => br %"v170" ? poll "L13" : "L171" };
  ir_blk{ @"L171":
    %"v172" : W = (Cmp Eq W) %"v4", #41
    => br %"v172" ? poll "L13" : "L173" };
  ir_blk{ @"L173":
    %"v174" : W = (Cmp Eq W) %"v4", #42
    => br %"v174" ? poll "L13" : "L175" };
  ir_blk{ @"L175":
    %"v176" : W = (Cmp Eq W) %"v4", #43
    => br %"v176" ? poll "L13" : poll "L43" };
  ir_blk{ @"L169":
    %"v178" : W = (Cmp Eq W) %"v4", #44
    => br %"v178" ? poll "L13" : "L179" };
  ir_blk{ @"L179":
    %"v180" : W = (Cmp Eq W) %"v4", #45
    => br %"v180" ? poll "L13" : "L181" };
  ir_blk{ @"L181":
    %"v182" : W = (Cmp Eq W) %"v4", #46
    => br %"v182" ? poll "L13" : "L183" };
  ir_blk{ @"L183":
    %"v184" : W = (Cmp Eq W) %"v4", #47
    => br %"v184" ? poll "L13" : poll "L43" };
  ir_blk{ @"L144":
    %"v186" : W = (Cmp Ult W) %"v4", #56
    => br %"v186" ? "L187" : "L188" };
  ir_blk{ @"L187":
    %"v189" : W = (Cmp Ult W) %"v4", #52
    => br %"v189" ? "L190" : "L191" };
  ir_blk{ @"L190":
    %"v192" : W = (Cmp Eq W) %"v4", #48
    => br %"v192" ? poll "L13" : "L193" };
  ir_blk{ @"L193":
    %"v194" : W = (Cmp Eq W) %"v4", #49
    => br %"v194" ? poll "L13" : "L195" };
  ir_blk{ @"L195":
    %"v196" : W = (Cmp Eq W) %"v4", #50
    => br %"v196" ? poll "L13" : "L197" };
  ir_blk{ @"L197":
    %"v198" : W = (Cmp Eq W) %"v4", #51
    => br %"v198" ? poll "L13" : poll "L43" };
  ir_blk{ @"L191":
    %"v200" : W = (Cmp Eq W) %"v4", #52
    => br %"v200" ? poll "L13" : "L201" };
  ir_blk{ @"L201":
    %"v202" : W = (Cmp Eq W) %"v4", #53
    => br %"v202" ? poll "L13" : "L203" };
  ir_blk{ @"L203":
    %"v204" : W = (Cmp Eq W) %"v4", #54
    => br %"v204" ? poll "L13" : "L205" };
  ir_blk{ @"L205":
    %"v206" : W = (Cmp Eq W) %"v4", #55
    => br %"v206" ? poll "L13" : poll "L43" };
  ir_blk{ @"L188":
    %"v208" : W = (Cmp Ult W) %"v4", #60
    => br %"v208" ? "L209" : "L210" };
  ir_blk{ @"L209":
    %"v211" : W = (Cmp Eq W) %"v4", #56
    => br %"v211" ? poll "L13" : "L212" };
  ir_blk{ @"L212":
    %"v213" : W = (Cmp Eq W) %"v4", #57
    => br %"v213" ? poll "L13" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v4", #58
    => br %"v215" ? poll "L13" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v4", #59
    => br %"v217" ? poll "L13" : poll "L43" };
  ir_blk{ @"L210":
    %"v219" : W = (Cmp Eq W) %"v4", #60
    => br %"v219" ? poll "L13" : "L220" }]) (app [ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v4", #61
    => br %"v221" ? poll "L13" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v4", #62
    => br %"v223" ? poll "L13" : "L224" };
  ir_blk{ @"L224":
    %"v225" : W = (Cmp Eq W) %"v4", #63
    => br %"v225" ? poll "L13" : poll "L43" };
  ir_blk{ @"L53":
    %"v227" : W = (Cmp Ult W) %"v4", #96
    => br %"v227" ? "L228" : "L229" };
  ir_blk{ @"L228":
    %"v230" : W = (Cmp Ult W) %"v4", #80
    => br %"v230" ? "L231" : "L232" };
  ir_blk{ @"L231":
    %"v233" : W = (Cmp Ult W) %"v4", #72
    => br %"v233" ? "L234" : "L235" };
  ir_blk{ @"L234":
    %"v236" : W = (Cmp Ult W) %"v4", #68
    => br %"v236" ? "L237" : "L238" };
  ir_blk{ @"L237":
    %"v239" : W = (Cmp Eq W) %"v4", #64
    => br %"v239" ? poll "L32" : "L240" };
  ir_blk{ @"L240":
    %"v241" : W = (Cmp Eq W) %"v4", #65
    => br %"v241" ? poll "L32" : "L242" };
  ir_blk{ @"L242":
    %"v243" : W = (Cmp Eq W) %"v4", #66
    => br %"v243" ? poll "L32" : "L244" };
  ir_blk{ @"L244":
    %"v245" : W = (Cmp Eq W) %"v4", #67
    => br %"v245" ? poll "L32" : poll "L43" };
  ir_blk{ @"L238":
    %"v247" : W = (Cmp Eq W) %"v4", #68
    => br %"v247" ? poll "L32" : "L248" };
  ir_blk{ @"L248":
    %"v249" : W = (Cmp Eq W) %"v4", #69
    => br %"v249" ? poll "L32" : "L250" };
  ir_blk{ @"L250":
    %"v251" : W = (Cmp Eq W) %"v4", #70
    => br %"v251" ? poll "L32" : "L252" };
  ir_blk{ @"L252":
    %"v253" : W = (Cmp Eq W) %"v4", #71
    => br %"v253" ? poll "L32" : poll "L43" };
  ir_blk{ @"L235":
    %"v255" : W = (Cmp Ult W) %"v4", #76
    => br %"v255" ? "L256" : "L257" };
  ir_blk{ @"L256":
    %"v258" : W = (Cmp Eq W) %"v4", #72
    => br %"v258" ? poll "L32" : "L259" };
  ir_blk{ @"L259":
    %"v260" : W = (Cmp Eq W) %"v4", #73
    => br %"v260" ? poll "L32" : "L261" };
  ir_blk{ @"L261":
    %"v262" : W = (Cmp Eq W) %"v4", #74
    => br %"v262" ? poll "L32" : "L263" };
  ir_blk{ @"L263":
    %"v264" : W = (Cmp Eq W) %"v4", #75
    => br %"v264" ? poll "L32" : poll "L43" };
  ir_blk{ @"L257":
    %"v266" : W = (Cmp Eq W) %"v4", #76
    => br %"v266" ? poll "L32" : "L267" };
  ir_blk{ @"L267":
    %"v268" : W = (Cmp Eq W) %"v4", #77
    => br %"v268" ? poll "L32" : "L269" };
  ir_blk{ @"L269":
    %"v270" : W = (Cmp Eq W) %"v4", #78
    => br %"v270" ? poll "L32" : "L271" };
  ir_blk{ @"L271":
    %"v272" : W = (Cmp Eq W) %"v4", #79
    => br %"v272" ? poll "L32" : poll "L43" };
  ir_blk{ @"L232":
    %"v274" : W = (Cmp Ult W) %"v4", #88
    => br %"v274" ? "L275" : "L276" };
  ir_blk{ @"L275":
    %"v277" : W = (Cmp Ult W) %"v4", #84
    => br %"v277" ? "L278" : "L279" };
  ir_blk{ @"L278":
    %"v280" : W = (Cmp Eq W) %"v4", #80
    => br %"v280" ? poll "L32" : "L281" };
  ir_blk{ @"L281":
    %"v282" : W = (Cmp Eq W) %"v4", #81
    => br %"v282" ? poll "L32" : "L283" };
  ir_blk{ @"L283":
    %"v284" : W = (Cmp Eq W) %"v4", #82
    => br %"v284" ? poll "L32" : "L285" };
  ir_blk{ @"L285":
    %"v286" : W = (Cmp Eq W) %"v4", #83
    => br %"v286" ? poll "L32" : poll "L43" };
  ir_blk{ @"L279":
    %"v288" : W = (Cmp Eq W) %"v4", #84
    => br %"v288" ? poll "L32" : "L289" };
  ir_blk{ @"L289":
    %"v290" : W = (Cmp Eq W) %"v4", #85
    => br %"v290" ? poll "L32" : "L291" };
  ir_blk{ @"L291":
    %"v292" : W = (Cmp Eq W) %"v4", #86
    => br %"v292" ? poll "L32" : "L293" };
  ir_blk{ @"L293":
    %"v294" : W = (Cmp Eq W) %"v4", #87
    => br %"v294" ? poll "L32" : poll "L43" };
  ir_blk{ @"L276":
    %"v296" : W = (Cmp Ult W) %"v4", #92
    => br %"v296" ? "L297" : "L298" };
  ir_blk{ @"L297":
    %"v299" : W = (Cmp Eq W) %"v4", #88
    => br %"v299" ? poll "L32" : "L300" };
  ir_blk{ @"L300":
    %"v301" : W = (Cmp Eq W) %"v4", #89
    => br %"v301" ? poll "L32" : "L302" };
  ir_blk{ @"L302":
    %"v303" : W = (Cmp Eq W) %"v4", #90
    => br %"v303" ? poll "L32" : "L304" };
  ir_blk{ @"L304":
    %"v305" : W = (Cmp Eq W) %"v4", #91
    => br %"v305" ? poll "L32" : poll "L43" };
  ir_blk{ @"L298":
    %"v307" : W = (Cmp Eq W) %"v4", #92
    => br %"v307" ? poll "L32" : "L308" };
  ir_blk{ @"L308":
    %"v309" : W = (Cmp Eq W) %"v4", #93
    => br %"v309" ? poll "L32" : "L310" }] [ir_blk{ @"L310":
    %"v311" : W = (Cmp Eq W) %"v4", #94
    => br %"v311" ? poll "L32" : "L312" };
  ir_blk{ @"L312":
    %"v313" : W = (Cmp Eq W) %"v4", #95
    => br %"v313" ? poll "L32" : poll "L43" };
  ir_blk{ @"L229":
    %"v315" : W = (Cmp Ult W) %"v4", #112
    => br %"v315" ? "L316" : "L317" };
  ir_blk{ @"L316":
    %"v318" : W = (Cmp Ult W) %"v4", #104
    => br %"v318" ? "L319" : "L320" };
  ir_blk{ @"L319":
    %"v321" : W = (Cmp Ult W) %"v4", #100
    => br %"v321" ? "L322" : "L323" };
  ir_blk{ @"L322":
    %"v324" : W = (Cmp Eq W) %"v4", #96
    => br %"v324" ? poll "L32" : "L325" };
  ir_blk{ @"L325":
    %"v326" : W = (Cmp Eq W) %"v4", #97
    => br %"v326" ? poll "L32" : "L327" };
  ir_blk{ @"L327":
    %"v328" : W = (Cmp Eq W) %"v4", #98
    => br %"v328" ? poll "L32" : "L329" };
  ir_blk{ @"L329":
    %"v330" : W = (Cmp Eq W) %"v4", #99
    => br %"v330" ? poll "L32" : poll "L43" };
  ir_blk{ @"L323":
    %"v332" : W = (Cmp Eq W) %"v4", #100
    => br %"v332" ? poll "L32" : "L333" };
  ir_blk{ @"L333":
    %"v334" : W = (Cmp Eq W) %"v4", #101
    => br %"v334" ? poll "L32" : "L335" };
  ir_blk{ @"L335":
    %"v336" : W = (Cmp Eq W) %"v4", #102
    => br %"v336" ? poll "L32" : "L337" };
  ir_blk{ @"L337":
    %"v338" : W = (Cmp Eq W) %"v4", #103
    => br %"v338" ? poll "L32" : poll "L43" };
  ir_blk{ @"L320":
    %"v340" : W = (Cmp Ult W) %"v4", #108
    => br %"v340" ? "L341" : "L342" };
  ir_blk{ @"L341":
    %"v343" : W = (Cmp Eq W) %"v4", #104
    => br %"v343" ? poll "L32" : "L344" };
  ir_blk{ @"L344":
    %"v345" : W = (Cmp Eq W) %"v4", #105
    => br %"v345" ? poll "L32" : "L346" };
  ir_blk{ @"L346":
    %"v347" : W = (Cmp Eq W) %"v4", #106
    => br %"v347" ? poll "L32" : "L348" };
  ir_blk{ @"L348":
    %"v349" : W = (Cmp Eq W) %"v4", #107
    => br %"v349" ? poll "L32" : poll "L43" };
  ir_blk{ @"L342":
    %"v351" : W = (Cmp Eq W) %"v4", #108
    => br %"v351" ? poll "L32" : "L352" };
  ir_blk{ @"L352":
    %"v353" : W = (Cmp Eq W) %"v4", #109
    => br %"v353" ? poll "L32" : "L354" };
  ir_blk{ @"L354":
    %"v355" : W = (Cmp Eq W) %"v4", #110
    => br %"v355" ? poll "L32" : "L356" };
  ir_blk{ @"L356":
    %"v357" : W = (Cmp Eq W) %"v4", #111
    => br %"v357" ? poll "L32" : poll "L43" };
  ir_blk{ @"L317":
    %"v359" : W = (Cmp Ult W) %"v4", #120
    => br %"v359" ? "L360" : "L361" };
  ir_blk{ @"L360":
    %"v362" : W = (Cmp Ult W) %"v4", #116
    => br %"v362" ? "L363" : "L364" };
  ir_blk{ @"L363":
    %"v365" : W = (Cmp Eq W) %"v4", #112
    => br %"v365" ? poll "L32" : "L366" };
  ir_blk{ @"L366":
    %"v367" : W = (Cmp Eq W) %"v4", #113
    => br %"v367" ? poll "L32" : "L368" };
  ir_blk{ @"L368":
    %"v369" : W = (Cmp Eq W) %"v4", #114
    => br %"v369" ? poll "L32" : "L370" };
  ir_blk{ @"L370":
    %"v371" : W = (Cmp Eq W) %"v4", #115
    => br %"v371" ? poll "L32" : poll "L43" };
  ir_blk{ @"L364":
    %"v373" : W = (Cmp Eq W) %"v4", #116
    => br %"v373" ? poll "L32" : "L374" };
  ir_blk{ @"L374":
    %"v375" : W = (Cmp Eq W) %"v4", #117
    => br %"v375" ? poll "L32" : "L376" };
  ir_blk{ @"L376":
    %"v377" : W = (Cmp Eq W) %"v4", #118
    => br %"v377" ? poll "L32" : "L378" };
  ir_blk{ @"L378":
    %"v379" : W = (Cmp Eq W) %"v4", #119
    => br %"v379" ? poll "L32" : poll "L43" };
  ir_blk{ @"L361":
    %"v381" : W = (Cmp Ult W) %"v4", #124
    => br %"v381" ? "L382" : "L383" };
  ir_blk{ @"L382":
    %"v384" : W = (Cmp Eq W) %"v4", #120
    => br %"v384" ? poll "L32" : "L385" };
  ir_blk{ @"L385":
    %"v386" : W = (Cmp Eq W) %"v4", #121
    => br %"v386" ? poll "L32" : "L387" };
  ir_blk{ @"L387":
    %"v388" : W = (Cmp Eq W) %"v4", #122
    => br %"v388" ? poll "L32" : "L389" };
  ir_blk{ @"L389":
    %"v390" : W = (Cmp Eq W) %"v4", #123
    => br %"v390" ? poll "L32" : poll "L43" };
  ir_blk{ @"L383":
    %"v392" : W = (Cmp Eq W) %"v4", #124
    => br %"v392" ? poll "L32" : "L393" };
  ir_blk{ @"L393":
    %"v394" : W = (Cmp Eq W) %"v4", #125
    => br %"v394" ? poll "L32" : "L395" };
  ir_blk{ @"L395":
    %"v396" : W = (Cmp Eq W) %"v4", #126
    => br %"v396" ? poll "L32" : "L397" };
  ir_blk{ @"L397":
    %"v398" : W = (Cmp Eq W) %"v4", #127
    => br %"v398" ? poll "L32" : poll "L43" }]))) }.

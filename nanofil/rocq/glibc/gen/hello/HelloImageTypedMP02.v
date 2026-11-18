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

Definition hello_image_fn___mpn_divrem : func :=
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

Definition hello_image_fn___mpn_extract_long_double : func :=
  ir_fn{ "export" "__mpn_extract_long_double"(P %"v0", L %"v2", P %"v4", P %"v6", L %"v8", L %"v9") -> (RClass L) {
  @"start":
    %"v10" : P = (Alloc 16) #16;
    alloca "v12" 16;
    %"chk0" : A = (Check 0 8 Write 1) %"v10";
    store Wl [%"chk0" + 0] <- %"v8";
    %"v11" = %"v10" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v11";
    store Wl [%"chk1" + 0] <- %"v9";
    %"va_args" : P = VaArgs #48;
    %"chk2" : A = (HalfCheck Upper 0 10 Read 8) %"chk0", %"v10";
    %"v13" : Extended = (RawLoad LdX 0) %"chk2";
    %"chk3" : A = (CheckLocal (a "v12") 0 10 Write 8);
    store Wx [%"chk3" + 0] <- %"v13";
    %"chk4" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v17" : W = Shl %"v16", #16;
    %"v18" : W = Shr %"v17", #31;
    %"chk5" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk5" + 0] <- %"v18";
    %"chk6" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v21" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v22" : W = Shl %"v21", #17;
    %"v23" : W = Shr %"v22", #17;
    %"v24" : W = Sub %"v23", #16383;
    %"chk7" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk7" + 0] <- %"v24";
    %"chk8" : A = (CheckLocal (a "v12") 4 4 Read 1);
    %"v28" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v29" : L = (Ext Uw) %"v28";
    %"v30" : L = Shl %"v29", #32;
    %"chk9" : A = (CheckLocal (a "v12") 0 4 Read 1);
    %"v31" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"v32" : L = (Ext Uw) %"v31";
    %"v33" : L = Or %"v30", %"v32";
    %"chk10" : A = (Check 0 8 Write 1) %"v0";
    store Wl [%"chk10" + 0] <- %"v33";
    %"chk11" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v39" : W = Shl %"v38", #17;
    %"v40" : W = Shr %"v39", #17;
    %"v41" : W = (Cmp Eq W) %"v40", #0
    => br %"v41" ? "L34" : "L35";
  @"L34":
    %"v47" : L = (RawLoad LdL 0) %"chk10";
    %"v48" : W = (Cmp Eq L) %"v47", #0
    => br %"v48" ? "L49" : "L50";
  @"L49":
    %"v56" : L = (RawLoad LdL 0) %"chk10";
    %"v57" : W = (Cmp Eq L) %"v56", #0
    => goto "L50";
  @"L50" [%"v59" : W = phi("L34" => #0, "L49" => %"v57")]:
    => br %"v59" ? "L42" : "L43";
  @"L42":
    store Ww [%"chk7" + 0] <- #0
    => goto "L36";
  @"L43":
    %"v67" : L = (RawLoad LdL 0) %"chk10";
    %"v72" : L = And %"v67", #9223372036854775807;
    store Wl [%"chk10" + 0] <- %"v72";
    %"v81" : L = (RawLoad LdL 0) %"chk10";
    %"v82" : W = (Cmp Ne L) %"v81", #0
    => br %"v82" ? "L73" : "L74";
  @"L73":
    %"v88" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v6" : W = (Cmp Eq L) %"v88", #0
    => br %"iw_1.v6" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v8" : L = Shr %"v88", #1;
    %"iw_1.v9" : L = Or %"v88", %"iw_1.v8";
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
  @"iw_1.L4" [%"iw_1.v34" : W = phi("iw_1.L3" => %"iw_1.v33", "L73" => #64)]:
    %"v97" : W = (Cmp Ne W) %"iw_1.v34", #0
    => br %"v97" ? "L93" : "L95";
  @"L93":
    %"v103" : L = (RawLoad LdL 0) %"chk10";
    %"v105" : L = Shl %"v103", %"iw_1.v34";
    store Wl [%"chk10" + 0] <- %"v105"
    => goto "L95";
  @"L95":
    %"v110" : W = Sub #4294950914, %"iw_1.v34";
    store Ww [%"chk7" + 0] <- %"v110"
    => goto "L36";
  @"L74":
    %"v116" : L = (RawLoad LdL 0) %"chk10";
    %"v117" : W = (Cmp Ne L) %"v116", #0
    => br %"v117" ? "L111" : "L112";
  @"L111":
    %"v120" : L = (RawLoad LdL 0) %"chk10";
    %"iw_2.v6" : W = (Cmp Eq L) %"v120", #0
    => br %"iw_2.v6" ? "iw_2.L4" : "iw_2.L3";
  @"iw_2.L3":
    %"iw_2.v8" : L = Shr %"v120", #1;
    %"iw_2.v9" : L = Or %"v120", %"iw_2.v8";
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
  @"iw_2.L4" [%"iw_2.v34" : W = phi("iw_2.L3" => %"iw_2.v33", "L111" => #64)]:
    %"v132" : L = (RawLoad LdL 0) %"chk10";
    %"v134" : L = Shl %"v132", %"iw_2.v34";
    store Wl [%"chk10" + 0] <- %"v134";
    store Wl [%"chk10" + 0] <- #0;
    %"v142" : W = Sub #4294950850, %"iw_2.v34";
    store Ww [%"chk7" + 0] <- %"v142"
    => goto "L36";
  @"L112":
    store Wl [%"chk10" + 0] <- #9223372036854775808;
    store Ww [%"chk7" + 0] <- #4294950914
    => goto "L36";
  @"L35":
    %"chk30" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v152" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v153" : W = Shl %"v152", #17;
    %"v154" : W = Shr %"v153", #17;
    %"v155" : W = (Cmp Slt W) %"v154", #32767
    => br %"v155" ? "L156" : "L157";
  @"L156":
    %"v163" : L = (RawLoad LdL 0) %"chk10";
    %"v164" : W = (Cmp Eq L) %"v163", #0
    => goto "L157";
  @"L157" [%"v166" : W = phi("L35" => #0, "L156" => %"v164")]:
    => br %"v166" ? "L148" : "L36";
  @"L148":
    store Ww [%"chk7" + 0] <- #0
    => goto "L36";
  @"L36":
    => ret #1
} }.

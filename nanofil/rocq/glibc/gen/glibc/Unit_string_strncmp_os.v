(** This file defines checked IR from glibc’s `string/strncmp.os` object.
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

Definition fn___GI_strncmp : func :=
  ir_fn{ "export" "__GI_strncmp"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v11" : L = Ptoi %"v0";
    %"v12" : L = Neg %"v11";
    %"v13" : L = And %"v12", #7;
    %"v15" : W = (Cmp Ult L) %"v13", %"v4"
    => br %"v15" ? "L9" : "L8";
  @"L8":
    => goto "L9";
  @"L9" [%"v21" : L = phi("L8" => %"v4", "start" => %"v13")]:
    => goto "L24";
  @"L24" [%"pr.3" : W = phi("L26" => %"v59", "L9" => #0); %"pr.2" : P = phi("L26" => %"v39", "L9" => %"v2"); %"pr.1" : P = phi("L26" => %"v34", "L9" => %"v0")]:
    %"v30" : L = (Ext Sw) %"pr.3";
    %"v31" : W = (Cmp Ult L) %"v30", %"v21"
    => br %"v31" ? "L25" : "L27";
  @"L25":
    %"v34" = %"pr.1" +p #1;
    %"chk0" : A = (Check 0 1 Read 1) %"pr.1";
    %"v35" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v36" : W = (Ext Ub) %"v35";
    %"v39" = %"pr.2" +p #1;
    %"chk1" : A = (Check 0 1 Read 1) %"pr.2";
    %"v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v41" : W = (Ext Ub) %"v40";
    %"v44" : W = Sub %"v36", %"v41";
    %"v49" : W = (Cmp Eq W) %"v36", #0
    => br %"v49" ? "L51" : "L50";
  @"L50":
    %"v53" : W = (Cmp Ne W) %"v44", #0
    => goto "L51";
  @"L51" [%"v55" : W = phi("L25" => #1, "L50" => %"v53")]:
    => br %"v55" ? "L45" : "L26";
  @"L45":
    => ret %"v44";
  @"L26":
    %"v59" : W = Add %"pr.3", #1
    => goto poll "L24";
  @"L27":
    %"v65" : W = (Cmp Eq L) %"v21", %"v4"
    => br %"v65" ? "L60" : "L62";
  @"L60":
    => ret #0;
  @"L62":
    %"v71" = %"pr.1" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"pr.1";
    %"v72" : L = (RawLoad LdL 0) %"chk2";
    %"v75" : L = Ptoi %"pr.2";
    %"v76" : L = And %"v75", #7;
    %"v81" : W = (Cmp Eq L) %"v76", #0
    => br %"v81" ? "L77" : "L78";
  @"L77":
    %"v87" : L = Sub %"v4", %"v21";
    %"iw_1.v10" = %"pr.2" +p #8;
    %"chk3" : A = (Check 0 8 Read 1) %"pr.2";
    %"iw_1.v11" : L = (RawLoad LdL 0) %"chk3"
    => goto "iw_1.L12";
  @"iw_1.L12" [%"iw_1.pr.5" : L = phi("iw_1.L28" => %"iw_1.v38", "L77" => %"iw_1.v11"); %"iw_1.pr.4" : L = phi("iw_1.L28" => %"iw_1.v25", "L77" => %"v87"); %"iw_1.pr.3" : L = phi("iw_1.L28" => %"iw_1.v35", "L77" => %"v72"); %"iw_1.pr.2" : P = phi("iw_1.L28" => %"iw_1.v37", "L77" => %"iw_1.v10"); %"iw_1.pr.1" : P = phi("iw_1.L28" => %"iw_1.v34", "L77" => %"v71")]:
    %"iw_1.v17" : W = (Cmp Eq L) %"iw_1.pr.3", %"iw_1.pr.5"
    => br %"iw_1.v17" ? "iw_1.L13" : "iw_1.iw_2.start";
  @"iw_1.L13":
    %"iw_1.v22" : W = (Cmp Ule L) %"iw_1.pr.4", #8
    => br %"iw_1.v22" ? "iw_1.iw_2.start" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v25" : L = Sub %"iw_1.pr.4", #8;
    %"iw_1.iw_1.iw_1.v8" : L = Sub %"iw_1.pr.3", #72340172838076673;
    %"iw_1.iw_1.iw_1.v10" : L = Xor %"iw_1.pr.3", #(-1);
    %"iw_1.iw_1.iw_1.v11" : L = And %"iw_1.iw_1.iw_1.v8", %"iw_1.iw_1.iw_1.v10";
    %"iw_1.iw_1.iw_1.v13" : L = And %"iw_1.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_1.iw_1.v4" : W = (Cmp Ne L) %"iw_1.iw_1.iw_1.v13", #0
    => br %"iw_1.iw_1.v4" ? "L79" : "iw_1.L28";
  @"iw_1.L28":
    %"iw_1.v34" = %"iw_1.pr.1" +p #8;
    %"chk4" : A = (Check 0 8 Read 1) %"iw_1.pr.1";
    %"iw_1.v35" : L = (RawLoad LdL 0) %"chk4";
    %"iw_1.v37" = %"iw_1.pr.2" +p #8;
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.pr.2";
    %"iw_1.v38" : L = (RawLoad LdL 0) %"chk5"
    => goto poll "iw_1.L12";
  @"iw_1.iw_2.start":
    %"iw_1.iw_2.iw_1.iw_1.v9" : L = Xor %"iw_1.pr.3", %"iw_1.pr.5";
    %"iw_1.iw_2.iw_1.iw_1.v13" : L = And %"iw_1.pr.3", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v15" : L = Add %"iw_1.iw_2.iw_1.iw_1.v13", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v17" : L = Or %"iw_1.iw_2.iw_1.iw_1.v15", %"iw_1.pr.3";
    %"iw_1.iw_2.iw_1.iw_1.v21" : L = And %"iw_1.iw_2.iw_1.iw_1.v9", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v23" : L = Add %"iw_1.iw_2.iw_1.iw_1.v21", #9187201950435737471;
    %"iw_1.iw_2.iw_1.iw_1.v25" : L = Or %"iw_1.iw_2.iw_1.iw_1.v23", %"iw_1.iw_2.iw_1.iw_1.v9";
    %"iw_1.iw_2.iw_1.iw_1.v28" : L = Xor %"iw_1.iw_2.iw_1.iw_1.v17", #(-1);
    %"iw_1.iw_2.iw_1.iw_1.v29" : L = Or %"iw_1.iw_2.iw_1.iw_1.v25", %"iw_1.iw_2.iw_1.iw_1.v28";
    %"iw_1.iw_2.iw_1.iw_1.v32" : L = And %"iw_1.iw_2.iw_1.iw_1.v29", #9259542123273814144;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_1.iw_2.iw_1.iw_1.v32", #0
    => br %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v6" ? "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4" : "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v8" : L = Neg %"iw_1.iw_2.iw_1.iw_1.v32";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v9" : L = And %"iw_1.iw_2.iw_1.iw_1.v32", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v10" : L = Sub %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v9", #1;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v11" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v10", #1;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v12" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v13" : L = Sub %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v10", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v14" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v15" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #2;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v16" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v17" : L = Add %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v14", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v17", #4;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v19" : L = Add %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v17", %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v20" : L = And %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v21" : L = Mul %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v20", #72340172838076673;
    %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v22" : L = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v21", #56
    => goto "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4" [%"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v23" : W = phi("iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3" => %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v22", "iw_1.iw_2.start" => #64)]:
    %"iw_1.iw_2.iw_1.iw_2.iw_1.v27" : W = Shr %"iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v23", #3;
    %"iw_1.iw_2.v15" : L = (Ext Uw) %"iw_1.iw_2.iw_1.iw_2.iw_1.v27";
    %"iw_1.iw_2.v16" : W = (Cmp Ule L) %"iw_1.pr.4", %"iw_1.iw_2.v15"
    => br %"iw_1.iw_2.v16" ? "L79" : "iw_1.iw_2.iw_2.start";
  @"iw_1.iw_2.iw_2.start":
    %"iw_1.iw_2.iw_2.v10" : W = Shl %"iw_1.iw_2.iw_1.iw_2.iw_1.v27", #3;
    %"iw_1.iw_2.iw_2.v11" : L = Shr %"iw_1.pr.3", %"iw_1.iw_2.iw_2.v10";
    %"iw_1.iw_2.iw_2.v12" : W = (Ext Ub) %"iw_1.iw_2.iw_2.v11";
    %"iw_1.iw_2.iw_3.v11" : L = Shr %"iw_1.pr.5", %"iw_1.iw_2.iw_2.v10";
    %"iw_1.iw_2.iw_3.v12" : W = (Ext Ub) %"iw_1.iw_2.iw_3.v11";
    %"iw_1.iw_2.v26" : W = Sub %"iw_1.iw_2.iw_2.v12", %"iw_1.iw_2.iw_3.v12"
    => goto "L79";
  @"L78":
    (Flight (a "v92") Sub [(FAddress (t "pr.2")); (FValue (t "v76"))] (LowerOf (t "pr.2")));
    %"v97" : L = Sub %"v4", %"v21";
    %"iw_2.v12" = %"v92" +p #8;
    %"chk6" : A = (Check 0 8 Read 1) %"v92";
    %"iw_2.v13" : L = (RawLoad LdL 0) %"chk6";
    %"iw_2.v16" : L = Shl %"v76", #3;
    %"iw_2.v20" : L = Sub #64, %"iw_2.v16";
    %"iw_2.v24" : L = Shr %"iw_2.v13", %"iw_2.v16";
    %"iw_2.v28" : L = Shl #18446744073709551615, %"iw_2.v20";
    %"iw_2.v29" : L = Or %"iw_2.v24", %"iw_2.v28";
    %"iw_2.iw_1.iw_1.v8" : L = Sub %"iw_2.v29", #72340172838076673;
    %"iw_2.iw_1.iw_1.v10" : L = Xor %"iw_2.v29", #(-1);
    %"iw_2.iw_1.iw_1.v11" : L = And %"iw_2.iw_1.iw_1.v8", %"iw_2.iw_1.iw_1.v10";
    %"iw_2.iw_1.iw_1.v13" : L = And %"iw_2.iw_1.iw_1.v11", #9259542123273814144;
    %"iw_2.v36" : W = (Cmp Eq L) %"iw_2.iw_1.iw_1.v13", #0
    => br %"iw_2.v36" ? "iw_2.L37" : "iw_2.L38";
  @"iw_2.L37":
    %"iw_2.v41" : L = Sub #8, %"v76";
    %"iw_2.v42" : W = (Cmp Ugt L) %"v97", %"iw_2.v41"
    => goto "iw_2.L38";
  @"iw_2.L38" [%"iw_2.v44" : W = phi("L78" => #0, "iw_2.L37" => %"iw_2.v42")]:
    => br %"iw_2.v44" ? "iw_2.L46" : "iw_2.L32";
  @"iw_2.L46" [%"iw_2.pr.8" : L = phi("iw_2.L80" => %"iw_2.v51", "iw_2.L38" => %"iw_2.v13"); %"iw_2.pr.6" : L = phi("iw_2.L80" => %"iw_2.v77", "iw_2.L38" => %"v97"); %"iw_2.pr.4" : L = phi("iw_2.L80" => %"iw_2.v95", "iw_2.L38" => %"v72"); %"iw_2.pr.2" : P = phi("iw_2.L80" => %"iw_2.v50", "iw_2.L38" => %"iw_2.v12"); %"iw_2.pr.1" : P = phi("iw_2.L80" => %"iw_2.v94", "iw_2.L38" => %"v71")]:
    %"iw_2.v50" = %"iw_2.pr.2" +p #8;
    %"chk7" : A = (Check 0 8 Read 1) %"iw_2.pr.2";
    %"iw_2.v51" : L = (RawLoad LdL 0) %"chk7";
    %"iw_2.v54" : L = Shr %"iw_2.pr.8", %"iw_2.v16";
    %"iw_2.v57" : L = Shl %"iw_2.v51", %"iw_2.v20";
    %"iw_2.v58" : L = Or %"iw_2.v54", %"iw_2.v57";
    %"iw_2.v63" : W = (Cmp Ule L) %"iw_2.pr.6", #8
    => br %"iw_2.v63" ? "iw_2.L65" : "iw_2.L64";
  @"iw_2.L64":
    %"iw_2.v68" : W = (Cmp Ne L) %"iw_2.pr.4", %"iw_2.v58"
    => goto "iw_2.L65";
  @"iw_2.L65" [%"iw_2.v70" : W = phi("iw_2.L46" => #1, "iw_2.L64" => %"iw_2.v68")]:
    => br %"iw_2.v70" ? "iw_2.iw_2.start" : "iw_2.L61";
  @"iw_2.iw_2.start":
    %"iw_2.iw_2.iw_1.iw_1.v9" : L = Xor %"iw_2.pr.4", %"iw_2.v58";
    %"iw_2.iw_2.iw_1.iw_1.v13" : L = And %"iw_2.pr.4", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v15" : L = Add %"iw_2.iw_2.iw_1.iw_1.v13", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v17" : L = Or %"iw_2.iw_2.iw_1.iw_1.v15", %"iw_2.pr.4";
    %"iw_2.iw_2.iw_1.iw_1.v21" : L = And %"iw_2.iw_2.iw_1.iw_1.v9", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v23" : L = Add %"iw_2.iw_2.iw_1.iw_1.v21", #9187201950435737471;
    %"iw_2.iw_2.iw_1.iw_1.v25" : L = Or %"iw_2.iw_2.iw_1.iw_1.v23", %"iw_2.iw_2.iw_1.iw_1.v9";
    %"iw_2.iw_2.iw_1.iw_1.v28" : L = Xor %"iw_2.iw_2.iw_1.iw_1.v17", #(-1);
    %"iw_2.iw_2.iw_1.iw_1.v29" : L = Or %"iw_2.iw_2.iw_1.iw_1.v25", %"iw_2.iw_2.iw_1.iw_1.v28";
    %"iw_2.iw_2.iw_1.iw_1.v32" : L = And %"iw_2.iw_2.iw_1.iw_1.v29", #9259542123273814144;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_2.iw_2.iw_1.iw_1.v32", #0
    => br %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v6" ? "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4" : "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v8" : L = Neg %"iw_2.iw_2.iw_1.iw_1.v32";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v9" : L = And %"iw_2.iw_2.iw_1.iw_1.v32", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v10" : L = Sub %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v9", #1;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v11" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v10", #1;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v12" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v13" : L = Sub %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v10", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v14" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v15" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v13", #2;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v16" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v17" : L = Add %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v14", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v17", #4;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v19" : L = Add %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v17", %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v20" : L = And %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v21" : L = Mul %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v20", #72340172838076673;
    %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v22" : L = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v21", #56
    => goto "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4" [%"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v23" : W = phi("iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3" => %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v22", "iw_2.iw_2.start" => #64)]:
    %"iw_2.iw_2.iw_1.iw_2.iw_1.v27" : W = Shr %"iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v23", #3;
    %"iw_2.iw_2.v15" : L = (Ext Uw) %"iw_2.iw_2.iw_1.iw_2.iw_1.v27";
    %"iw_2.iw_2.v16" : W = (Cmp Ule L) %"iw_2.pr.6", %"iw_2.iw_2.v15"
    => br %"iw_2.iw_2.v16" ? "L79" : "iw_2.iw_2.iw_2.start";
  @"iw_2.iw_2.iw_2.start":
    %"iw_2.iw_2.iw_2.v10" : W = Shl %"iw_2.iw_2.iw_1.iw_2.iw_1.v27", #3;
    %"iw_2.iw_2.iw_2.v11" : L = Shr %"iw_2.pr.4", %"iw_2.iw_2.iw_2.v10";
    %"iw_2.iw_2.iw_2.v12" : W = (Ext Ub) %"iw_2.iw_2.iw_2.v11";
    %"iw_2.iw_2.iw_3.v11" : L = Shr %"iw_2.v58", %"iw_2.iw_2.iw_2.v10";
    %"iw_2.iw_2.iw_3.v12" : W = (Ext Ub) %"iw_2.iw_2.iw_3.v11";
    %"iw_2.iw_2.v26" : W = Sub %"iw_2.iw_2.iw_2.v12", %"iw_2.iw_2.iw_3.v12"
    => goto "L79";
  @"iw_2.L61":
    %"iw_2.v77" : L = Sub %"iw_2.pr.6", #8;
    %"iw_2.iw_3.iw_1.v8" : L = Sub %"iw_2.v51", #72340172838076673;
    %"iw_2.iw_3.iw_1.v10" : L = Xor %"iw_2.v51", #(-1);
    %"iw_2.iw_3.iw_1.v11" : L = And %"iw_2.iw_3.iw_1.v8", %"iw_2.iw_3.iw_1.v10";
    %"iw_2.iw_3.iw_1.v13" : L = And %"iw_2.iw_3.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_3.v4" : W = (Cmp Ne L) %"iw_2.iw_3.iw_1.v13", #0
    => br %"iw_2.iw_3.v4" ? "iw_2.L85" : "iw_2.L84";
  @"iw_2.L84":
    %"iw_2.v88" : L = Sub #8, %"v76";
    %"iw_2.v89" : W = (Cmp Ule L) %"iw_2.v77", %"iw_2.v88"
    => goto "iw_2.L85";
  @"iw_2.L85" [%"iw_2.v91" : W = phi("iw_2.L61" => #1, "iw_2.L84" => %"iw_2.v89")]:
    => br %"iw_2.v91" ? "iw_2.iw_4.start" : "iw_2.L80";
  @"iw_2.L80":
    %"iw_2.v94" = %"iw_2.pr.1" +p #8;
    %"chk8" : A = (Check 0 8 Read 1) %"iw_2.pr.1";
    %"iw_2.v95" : L = (RawLoad LdL 0) %"chk8"
    => goto poll "iw_2.L46";
  @"iw_2.iw_4.start":
    %"iw_2.iw_4.iw_1.v8" : L = Sub %"iw_2.pr.4", #72340172838076673;
    %"iw_2.iw_4.iw_1.v10" : L = Xor %"iw_2.pr.4", #(-1);
    %"iw_2.iw_4.iw_1.v11" : L = And %"iw_2.iw_4.iw_1.v8", %"iw_2.iw_4.iw_1.v10";
    %"iw_2.iw_4.iw_1.v13" : L = And %"iw_2.iw_4.iw_1.v11", #9259542123273814144;
    %"iw_2.iw_4.v4" : W = (Cmp Ne L) %"iw_2.iw_4.iw_1.v13", #0
    => br %"iw_2.iw_4.v4" ? "L79" : "iw_2.L99";
  @"iw_2.L99":
    %"chk9" : A = (Check 0 8 Read 1) %"iw_2.pr.1";
    %"iw_2.v106" : L = (RawLoad LdL 0) %"chk9";
    %"iw_2.v109" : L = Shr %"iw_2.v51", %"iw_2.v16";
    %"iw_2.v111" : W = Shl #0, %"iw_2.v20";
    %"iw_2.v112" : L = (Ext Sw) %"iw_2.v111";
    %"iw_2.v113" : L = Or %"iw_2.v109", %"iw_2.v112"
    => goto "iw_2.L32";
  @"iw_2.L32" [%"iw_2.pr.9" : L = phi("iw_2.L99" => %"iw_2.v113", "iw_2.L38" => %"iw_2.v29"); %"iw_2.pr.5" : L = phi("iw_2.L99" => %"iw_2.v77", "iw_2.L38" => %"v97"); %"iw_2.pr.3" : L = phi("iw_2.L99" => %"iw_2.v106", "iw_2.L38" => %"v72")]:
    %"iw_2.iw_5.iw_1.iw_1.v9" : L = Xor %"iw_2.pr.3", %"iw_2.pr.9";
    %"iw_2.iw_5.iw_1.iw_1.v13" : L = And %"iw_2.pr.3", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v15" : L = Add %"iw_2.iw_5.iw_1.iw_1.v13", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v17" : L = Or %"iw_2.iw_5.iw_1.iw_1.v15", %"iw_2.pr.3";
    %"iw_2.iw_5.iw_1.iw_1.v21" : L = And %"iw_2.iw_5.iw_1.iw_1.v9", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v23" : L = Add %"iw_2.iw_5.iw_1.iw_1.v21", #9187201950435737471;
    %"iw_2.iw_5.iw_1.iw_1.v25" : L = Or %"iw_2.iw_5.iw_1.iw_1.v23", %"iw_2.iw_5.iw_1.iw_1.v9";
    %"iw_2.iw_5.iw_1.iw_1.v28" : L = Xor %"iw_2.iw_5.iw_1.iw_1.v17", #(-1);
    %"iw_2.iw_5.iw_1.iw_1.v29" : L = Or %"iw_2.iw_5.iw_1.iw_1.v25", %"iw_2.iw_5.iw_1.iw_1.v28";
    %"iw_2.iw_5.iw_1.iw_1.v32" : L = And %"iw_2.iw_5.iw_1.iw_1.v29", #9259542123273814144;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_2.iw_5.iw_1.iw_1.v32", #0
    => br %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v6" ? "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" : "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v8" : L = Neg %"iw_2.iw_5.iw_1.iw_1.v32";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v9" : L = And %"iw_2.iw_5.iw_1.iw_1.v32", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v10" : L = Sub %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v9", #1;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v11" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v10", #1;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v12" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v11", #6148914691236517205;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v13" : L = Sub %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v10", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v14" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v13", #3689348814741910323;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v15" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v13", #2;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v16" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v15", #3689348814741910323;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v17" : L = Add %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v14", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v17", #4;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v19" : L = Add %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v17", %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v20" : L = And %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v19", #1085102592571150095;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v21" : L = Mul %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v20", #72340172838076673;
    %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v22" : L = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v21", #56
    => goto "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" [%"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v23" : W = phi("iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3" => %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v22", "iw_2.L32" => #64)]:
    %"iw_2.iw_5.iw_1.iw_2.iw_1.v27" : W = Shr %"iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v23", #3;
    %"iw_2.iw_5.v15" : L = (Ext Uw) %"iw_2.iw_5.iw_1.iw_2.iw_1.v27";
    %"iw_2.iw_5.v16" : W = (Cmp Ule L) %"iw_2.pr.5", %"iw_2.iw_5.v15"
    => br %"iw_2.iw_5.v16" ? "L79" : "iw_2.iw_5.iw_2.start";
  @"iw_2.iw_5.iw_2.start":
    %"iw_2.iw_5.iw_2.v10" : W = Shl %"iw_2.iw_5.iw_1.iw_2.iw_1.v27", #3;
    %"iw_2.iw_5.iw_2.v11" : L = Shr %"iw_2.pr.3", %"iw_2.iw_5.iw_2.v10";
    %"iw_2.iw_5.iw_2.v12" : W = (Ext Ub) %"iw_2.iw_5.iw_2.v11";
    %"iw_2.iw_5.iw_3.v11" : L = Shr %"iw_2.pr.9", %"iw_2.iw_5.iw_2.v10";
    %"iw_2.iw_5.iw_3.v12" : W = (Ext Ub) %"iw_2.iw_5.iw_3.v11";
    %"iw_2.iw_5.v26" : W = Sub %"iw_2.iw_5.iw_2.v12", %"iw_2.iw_5.iw_3.v12"
    => goto "L79";
  @"L79" [%"v99" : W = phi("iw_1.L20" => #0, "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4" => #0, "iw_1.iw_2.iw_2.start" => %"iw_1.iw_2.v26", "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4" => #0, "iw_2.iw_2.iw_2.start" => %"iw_2.iw_2.v26", "iw_2.iw_4.start" => #0, "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4" => #0, "iw_2.iw_5.iw_2.start" => %"iw_2.iw_5.v26")]:
    => ret %"v99"
} }.

Definition item_strncmp : item :=
  (IAlias (a "strncmp") (a "export") (a "__GI_strncmp")).

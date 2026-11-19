(** This file defines checked IR from the `xmalloc` object of HelloImage.
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

Definition fn_xcharalloc : func :=
  ir_fn{ "export" "xcharalloc"(L %"v0") -> (RClass P) {
  @"start":
    call %"v7" : P = $"xmalloc"(L %"v0")
    => ret %"v7"
} }.

Definition fn_xmalloc : func :=
  ir_fn{ "export" "xmalloc"(L %"v0") -> (RClass P) {
  @"start":
    call %"v3" : P = $"malloc"(L %"v0");
    %"iw_1.v6" : L = Ptoi %"v3";
    %"iw_1.v8" : W = (Cmp Eq L) %"iw_1.v6", #0
    => br %"iw_1.v8" ? "iw_1.L2" : "iw_1.join";
  @"iw_1.L2":
    call void $"xalloc_die"()
    => goto "iw_1.join";
  @"iw_1.join":
    => ret %"v3"
} }.

Definition fn_xpalloc : func :=
  ir_fn{ "export" "xpalloc"(P %"v0", P %"v2", L %"v4", L %"v6", L %"v8") -> (RClass P) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v12" : L = (RawLoad LdL 0) %"chk0";
    %"v19" : L = Sar %"v12", #1;
    %"v20" : L = Sar %"v12", #63;
    %"v21" : L = Sar %"v19", #63;
    %"v22" : L = Add %"v12", %"v19";
    %"v23" : W = (Cmp Ult L) %"v22", %"v12";
    %"v24" : L = (Ext Uw) %"v23";
    %"v25" : L = Add %"v20", %"v21";
    %"v26" : L = Add %"v25", %"v24";
    %"v27" : L = Sar %"v22", #63;
    %"v29" : W = (Cmp Ne L) %"v26", %"v27"
    => br %"v29" ? "L16" : "L15";
  @"L15":
    => goto "L16";
  @"L16" [%"pr.2" : L = phi("L15" => %"v22", "start" => #9223372036854775807)]:
    %"v35" : W = (Cmp Sge L) %"v6", #0
    => br %"v35" ? "L36" : "L37";
  @"L36":
    %"v40" : W = (Cmp Slt L) %"v6", %"pr.2"
    => goto "L37";
  @"L37" [%"v42" : W = phi("L16" => #0, "L36" => %"v40")]:
    => br %"v42" ? "L33" : "L32";
  @"L32":
    => goto "L33";
  @"L33" [%"pr.3" : L = phi("L32" => %"pr.2", "L37" => %"v6")]:
    %"v51" : L = Sar %"pr.3", #63;
    %"v52" : L = Sar %"v8", #63;
    %"v53" : L = Mul %"pr.3", %"v8";
    %"v54" : L = And %"pr.3", #4294967295;
    %"v55" : L = Shr %"pr.3", #32;
    %"v56" : L = And %"v8", #4294967295;
    %"v57" : L = Shr %"v8", #32;
    %"v58" : L = Mul %"v54", %"v56";
    %"v59" : L = Mul %"v55", %"v56";
    %"v60" : L = Mul %"v54", %"v57";
    %"v61" : L = Mul %"v55", %"v57";
    %"v62" : L = Shr %"v58", #32;
    %"v63" : L = And %"v59", #4294967295;
    %"v64" : L = And %"v60", #4294967295;
    %"v65" : L = Add %"v62", %"v63";
    %"v66" : L = Add %"v65", %"v64";
    %"v67" : L = Shr %"v66", #32;
    %"v68" : L = Shr %"v59", #32;
    %"v69" : L = Shr %"v60", #32;
    %"v70" : L = Add %"v61", %"v68";
    %"v71" : L = Add %"v70", %"v69";
    %"v72" : L = Add %"v71", %"v67";
    %"v73" : L = And %"v51", %"v8";
    %"v74" : L = And %"v52", %"pr.3";
    %"v75" : L = Sub %"v72", %"v73";
    %"v76" : L = Sub %"v75", %"v74";
    %"v77" : L = Sar %"v53", #63;
    %"v79" : W = (Cmp Ne L) %"v76", %"v77"
    => br %"v79" ? "L48" : "L47";
  @"L47":
    %"v90" : W = (Cmp Slt L) %"v53", #128
    => br %"v90" ? "L88" : "L87";
  @"L87":
    => goto "L88";
  @"L88" [%"v91" : W = phi("L87" => #0, "L47" => #128)]:
    %"v92" : L = (Ext Sw) %"v91"
    => goto "L48";
  @"L48" [%"v93" : L = phi("L88" => %"v92", "L33" => #9223372036854775807)]:
    %"v98" : W = (Cmp Ne L) %"v93", #0
    => br %"v98" ? "L94" : "L96";
  @"L94":
    %"v101" : L = Div %"v93", %"v8";
    %"v105" : L = Rem %"v93", %"v8";
    %"v106" : L = Sub %"v93", %"v105"
    => goto "L96";
  @"L96" [%"pr.7" : L = phi("L94" => %"v106", "L48" => %"v53"); %"pr.4" : L = phi("L94" => %"v101", "L48" => %"pr.3")]:
    %"v111" : L = Ptoi %"v0";
    %"v113" : W = (Cmp Eq L) %"v111", #0
    => br %"v113" ? "L107" : "L109";
  @"L107":
    %"chk1" : A = (Renew 0 8 Write 1) %"chk0", %"v2";
    store Wl [%"chk1" + 0] <- #0
    => goto "L109";
  @"L109":
    %"v120" : L = Sub %"pr.4", %"v12";
    %"v122" : W = (Cmp Slt L) %"v120", %"v4"
    => br %"v122" ? "L123" : "L124";
  @"L123":
    %"v128" : L = Sar %"v4", #63;
    %"v129" : L = Add %"v12", %"v4";
    %"v130" : W = (Cmp Ult L) %"v129", %"v12";
    %"v131" : L = (Ext Uw) %"v130";
    %"v132" : L = Add %"v20", %"v128";
    %"v133" : L = Add %"v132", %"v131";
    %"v134" : L = Sar %"v129", #63;
    %"v136" : W = (Cmp Ne L) %"v133", %"v134"
    => br %"v136" ? "L139" : "L138";
  @"L138":
    => br %"v35" ? "L142" : "L139";
  @"L142":
    %"v146" : W = (Cmp Slt L) %"v6", %"v129"
    => goto "L139";
  @"L139" [%"v150" : W = phi("L123" => #1, "L138" => #0, "L142" => %"v146")]:
    => br %"v150" ? "L124" : "L151";
  @"L151":
    %"v157" : L = Mul %"v129", %"v8";
    %"v158" : L = And %"v129", #4294967295;
    %"v159" : L = Shr %"v129", #32;
    %"v162" : L = Mul %"v158", %"v56";
    %"v163" : L = Mul %"v159", %"v56";
    %"v164" : L = Mul %"v158", %"v57";
    %"v165" : L = Mul %"v159", %"v57";
    %"v166" : L = Shr %"v162", #32;
    %"v167" : L = And %"v163", #4294967295;
    %"v168" : L = And %"v164", #4294967295;
    %"v169" : L = Add %"v166", %"v167";
    %"v170" : L = Add %"v169", %"v168";
    %"v171" : L = Shr %"v170", #32;
    %"v172" : L = Shr %"v163", #32;
    %"v173" : L = Shr %"v164", #32;
    %"v174" : L = Add %"v165", %"v172";
    %"v175" : L = Add %"v174", %"v173";
    %"v176" : L = Add %"v175", %"v171";
    %"v177" : L = And %"v134", %"v8";
    %"v178" : L = And %"v52", %"v129";
    %"v179" : L = Sub %"v176", %"v177";
    %"v180" : L = Sub %"v179", %"v178";
    %"v181" : L = Sar %"v157", #63;
    %"v183" : W = (Cmp Ne L) %"v180", %"v181"
    => goto "L124";
  @"L124" [%"v188" : W = phi("L109" => #0, "L139" => #1, "L151" => %"v183"); %"pr.5" : L = phi("L109" => %"pr.7", "L139" => %"pr.7", "L151" => %"v157"); %"pr.1" : L = phi("L109" => %"pr.4", "L139" => %"v129", "L151" => %"v129")]:
    => br %"v188" ? "L115" : "L117";
  @"L115":
    call void $"xalloc_die"()
    => goto "L117";
  @"L117":
    call %"v191" : P = $"xrealloc"(P %"v0", L %"pr.5");
    %"chk2" : A = (Renew 0 8 Write 1) %"chk0", %"v2";
    store Wl [%"chk2" + 0] <- %"pr.1"
    => ret %"v191"
} }.

Definition fn_xrealloc : func :=
  ir_fn{ "export" "xrealloc"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"realloc"(P %"v0", L %"v2");
    %"iw_1.v6" : L = Ptoi %"v6";
    %"iw_1.v8" : W = (Cmp Eq L) %"iw_1.v6", #0
    => br %"iw_1.v8" ? "iw_1.L2" : "iw_1.join";
  @"iw_1.L2":
    call void $"xalloc_die"()
    => goto "iw_1.join";
  @"iw_1.join":
    => ret %"v6"
} }.

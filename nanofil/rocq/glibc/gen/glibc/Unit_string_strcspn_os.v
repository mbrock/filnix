(** This file defines checked IR from glibc’s `string/strcspn.os` object.
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

Definition fn___GI_strcspn : func :=
  ir_fn{ "export" "__GI_strcspn"(P %"v0", P %"v2") -> (RClass L) {
  @"start":
    %"v33" : P = (Alloc 4) #256;
    %"chk0" : A = (Check 0 1 Read 1) %"v2";
    %"v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L14" : "L13";
  @"L13":
    %"v16" = %"v2" +p #1;
    %"chk1" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => goto "L14";
  @"L14" [%"v22" : W = phi("start" => #1, "L13" => %"v18")]:
    => br %"v22" ? "L4" : "L6";
  @"L4":
    %"v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    call %"v27" : P = $"__GI___strchrnul"(P %"v0", W %"v26");
    %"v29" : L = Ptoi %"v27";
    %"v30" : L = Ptoi %"v0";
    %"v31" : L = Sub %"v29", %"v30"
    => ret %"v31";
  @"L6":
    call %"v35" : P = $"__GI_memset"(P %"v33", W #0, L #64);
    %"v37" = %"v35" +p #64;
    call %"v38" : P = $"__GI_memset"(P %"v37", W #0, L #64);
    %"v40" = %"v35" +p #128;
    call %"v41" : P = $"__GI_memset"(P %"v40", W #0, L #64);
    %"v43" = %"v35" +p #192;
    call %"v44" : P = $"__GI_memset"(P %"v43", W #0, L #64)
    => goto "L48";
  @"L48" [%"pr.2" : P = phi("L48" => %"v53", "L6" => %"v2")]:
    %"v53" = %"pr.2" +p #1;
    %"chk3" : A = (Check 0 1 Read 1) %"pr.2";
    %"v54" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"v55" : L = (Ext Uw) %"v54";
    %"v56" = %"v35" +p %"v55";
    %"chk4" : A = (Check 0 1 Write 1) %"v56";
    store Wb [%"chk4" + 0] <- #1
    => br %"v54" ? poll "L48" : "L50";
  @"L50":
    %"chk5" : A = (Check 0 1 Read 1) %"v0";
    %"v65" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"v66" : L = (Ext Uw) %"v65";
    %"v67" = %"v35" +p %"v66";
    %"chk6" : A = (Check 0 1 Read 1) %"v67";
    %"v68" : W = (RawLoad (LdNarrow Ub) 0) %"chk6"
    => br %"v68" ? "L59" : "L61";
  @"L59":
    => ret #0;
  @"L61":
    %"v75" = %"v0" +p #1;
    %"chk7" : A = (HalfCheck Upper 0 1 Read 1) %"chk5", %"v75";
    %"v76" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v77" : L = (Ext Uw) %"v76";
    %"v78" = %"v35" +p %"v77";
    %"chk8" : A = (Check 0 1 Read 1) %"v78";
    %"v79" : W = (RawLoad (LdNarrow Ub) 0) %"chk8"
    => br %"v79" ? "L70" : "L72";
  @"L70":
    => ret #1;
  @"L72":
    %"v86" = %"v0" +p #2;
    %"chk9" : A = (HalfCheck Upper 0 1 Read 1) %"chk5", %"v86";
    %"v87" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v88" : L = (Ext Uw) %"v87";
    %"v89" = %"v35" +p %"v88";
    %"chk10" : A = (Check 0 1 Read 1) %"v89";
    %"v90" : W = (RawLoad (LdNarrow Ub) 0) %"chk10"
    => br %"v90" ? "L81" : "L83";
  @"L81":
    => ret #2;
  @"L83":
    %"v97" = %"v0" +p #3;
    %"chk11" : A = (HalfCheck Upper 0 1 Read 1) %"chk5", %"v97";
    %"v98" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"v99" : L = (Ext Uw) %"v98";
    %"v100" = %"v35" +p %"v99";
    %"chk12" : A = (Check 0 1 Read 1) %"v100";
    %"v101" : W = (RawLoad (LdNarrow Ub) 0) %"chk12"
    => br %"v101" ? "L92" : "L94";
  @"L92":
    => ret #3;
  @"L94":
    %"v104" : L = Ptoi %"v0";
    %"v106" : L = And %"v104", #18446744073709551612;
    %"lc.2" : L = Sub %"v106", %"v104";
    %"v107" = %"v0" +p %"lc.2"
    => goto "L112";
  @"L112" [%"pr.1" : P = phi("L112" => %"v116", "L94" => %"v107")]:
    %"v116" = %"pr.1" +p #4;
    %"chk13" : A = (Check 0 1 Read 1) %"v116";
    %"v120" : W = (RawLoad (LdNarrow Ub) 0) %"chk13";
    %"v121" : L = (Ext Uw) %"v120";
    %"v122" = %"v35" +p %"v121";
    %"chk14" : A = (Check 0 1 Read 1) %"v122";
    %"v123" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"v126" = %"v116" +p #1;
    %"chk15" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v126";
    %"v127" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v128" : L = (Ext Uw) %"v127";
    %"v129" = %"v35" +p %"v128";
    %"chk16" : A = (Check 0 1 Read 1) %"v129";
    %"v130" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v133" = %"v116" +p #2;
    %"chk17" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v133";
    %"v134" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v135" : L = (Ext Uw) %"v134";
    %"v136" = %"v35" +p %"v135";
    %"chk18" : A = (Check 0 1 Read 1) %"v136";
    %"v137" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v140" = %"v116" +p #3;
    %"chk19" : A = (HalfCheck Upper 0 1 Read 1) %"chk13", %"v140";
    %"v141" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v142" : L = (Ext Uw) %"v141";
    %"v143" = %"v35" +p %"v142";
    %"chk20" : A = (Check 0 1 Read 1) %"v143";
    %"v144" : W = (RawLoad (LdNarrow Ub) 0) %"chk20";
    %"v147" : W = Or %"v123", %"v130";
    %"v149" : W = Or %"v147", %"v137";
    %"v151" : W = Or %"v149", %"v144";
    %"v152" : W = (Cmp Eq W) %"v151", #0
    => br %"v152" ? poll "L112" : "L114";
  @"L114":
    %"v156" : L = Ptoi %"v116";
    %"v158" : L = Sub %"v156", %"v104";
    %"v165" : W = (Cmp Ne W) %"v147", #0
    => br %"v165" ? "L159" : "L160";
  @"L159":
    %"v168" : L = (Ext Uw) %"v123";
    %"v169" : L = Sub %"v158", %"v168";
    %"v170" : L = Add %"v169", #1
    => goto "L161";
  @"L160":
    %"v173" : L = (Ext Uw) %"v137";
    %"v174" : L = Sub %"v158", %"v173";
    %"v175" : L = Add %"v174", #3
    => goto "L161";
  @"L161" [%"v176" : L = phi("L159" => %"v170", "L160" => %"v175")]:
    => ret %"v176"
} }.

(** This file defines checked IR from glibc’s `string/strspn.os` object.
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

Definition fn___GI_strspn : func :=
  ir_fn{ "export" "__GI_strspn"(P %"v0", P %"v2") -> (RClass L) {
  @"start":
    %"v40" : P = (Alloc 4) #256;
    %"chk0" : A = (Check 0 1 Read 1) %"v2";
    %"v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L4" : "L6";
  @"L4":
    => ret #0;
  @"L6":
    %"v16" = %"v2" +p #1;
    %"chk1" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => br %"v18" ? "L23" : "L14";
  @"L23" [%"pr.1" : P = phi("L25" => %"v33", "L6" => %"v0")]:
    %"chk2" : A = (Check 0 1 Read 1) %"pr.1";
    %"v28" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"chk3" : A = (Renew 0 1 Read 1) %"chk0", %"v2";
    %"v30" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v31" : W = (Cmp Eq W) %"v28", %"v30"
    => br %"v31" ? "L25" : "L26";
  @"L25":
    %"v33" = %"pr.1" +p #1
    => goto poll "L23";
  @"L26":
    %"v36" : L = Ptoi %"pr.1";
    %"v37" : L = Ptoi %"v0";
    %"v38" : L = Sub %"v36", %"v37"
    => ret %"v38";
  @"L14":
    call %"v42" : P = $"__GI_memset"(P %"v40", W #0, L #64);
    %"v44" = %"v42" +p #64;
    call %"v45" : P = $"__GI_memset"(P %"v44", W #0, L #64);
    %"v47" = %"v42" +p #128;
    call %"v48" : P = $"__GI_memset"(P %"v47", W #0, L #64);
    %"v50" = %"v42" +p #192;
    call %"v51" : P = $"__GI_memset"(P %"v50", W #0, L #64)
    => goto "L54";
  @"L54" [%"pr.3" : P = phi("L14" => %"v2", "L54" => %"v59")]:
    %"v59" = %"pr.3" +p #1;
    %"chk4" : A = (Check 0 1 Read 1) %"pr.3";
    %"v60" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"v61" : L = (Ext Uw) %"v60";
    %"v62" = %"v42" +p %"v61";
    %"chk5" : A = (Check 0 1 Write 1) %"v62";
    store Wb [%"chk5" + 0] <- #1;
    %"chk6" : A = (HalfCheck Upper 0 1 Read 1) %"chk4", %"v59";
    %"v64" : W = (RawLoad (LdNarrow Ub) 0) %"chk6"
    => br %"v64" ? poll "L54" : "L56";
  @"L56":
    %"chk7" : A = (Check 0 1 Read 1) %"v0";
    %"v72" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v73" : L = (Ext Uw) %"v72";
    %"v74" = %"v42" +p %"v73";
    %"chk8" : A = (Check 0 1 Read 1) %"v74";
    %"v75" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v76" : W = (Cmp Eq W) %"v75", #0
    => br %"v76" ? "L66" : "L68";
  @"L66":
    => ret #0;
  @"L68":
    %"v83" = %"v0" +p #1;
    %"chk9" : A = (HalfCheck Upper 0 1 Read 1) %"chk7", %"v83";
    %"v84" : W = (RawLoad (LdNarrow Ub) 0) %"chk9";
    %"v85" : L = (Ext Uw) %"v84";
    %"v86" = %"v42" +p %"v85";
    %"chk10" : A = (Check 0 1 Read 1) %"v86";
    %"v87" : W = (RawLoad (LdNarrow Ub) 0) %"chk10";
    %"v88" : W = (Cmp Eq W) %"v87", #0
    => br %"v88" ? "L78" : "L80";
  @"L78":
    => ret #1;
  @"L80":
    %"v95" = %"v0" +p #2;
    %"chk11" : A = (HalfCheck Upper 0 1 Read 1) %"chk7", %"v95";
    %"v96" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"v97" : L = (Ext Uw) %"v96";
    %"v98" = %"v42" +p %"v97";
    %"chk12" : A = (Check 0 1 Read 1) %"v98";
    %"v99" : W = (RawLoad (LdNarrow Ub) 0) %"chk12";
    %"v100" : W = (Cmp Eq W) %"v99", #0
    => br %"v100" ? "L90" : "L92";
  @"L90":
    => ret #2;
  @"L92":
    %"v107" = %"v0" +p #3;
    %"chk13" : A = (HalfCheck Upper 0 1 Read 1) %"chk7", %"v107";
    %"v108" : W = (RawLoad (LdNarrow Ub) 0) %"chk13";
    %"v109" : L = (Ext Uw) %"v108";
    %"v110" = %"v42" +p %"v109";
    %"chk14" : A = (Check 0 1 Read 1) %"v110";
    %"v111" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"v112" : W = (Cmp Eq W) %"v111", #0
    => br %"v112" ? "L102" : "L104";
  @"L102":
    => ret #3;
  @"L104":
    %"v115" : L = Ptoi %"v0";
    %"v117" : L = And %"v115", #18446744073709551612;
    %"lc.2" : L = Sub %"v117", %"v115";
    %"v118" = %"v0" +p %"lc.2"
    => goto "L123";
  @"L123" [%"pr.2" : P = phi("L104" => %"v118", "L123" => %"v127")]:
    %"v127" = %"pr.2" +p #4;
    %"chk15" : A = (Check 0 1 Read 1) %"v127";
    %"v131" : W = (RawLoad (LdNarrow Ub) 0) %"chk15";
    %"v132" : L = (Ext Uw) %"v131";
    %"v133" = %"v42" +p %"v132";
    %"chk16" : A = (Check 0 1 Read 1) %"v133";
    %"v134" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v137" = %"v127" +p #1;
    %"chk17" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"v137";
    %"v138" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v139" : L = (Ext Uw) %"v138";
    %"v140" = %"v42" +p %"v139";
    %"chk18" : A = (Check 0 1 Read 1) %"v140";
    %"v141" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"v144" = %"v127" +p #2;
    %"chk19" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"v144";
    %"v145" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v146" : L = (Ext Uw) %"v145";
    %"v147" = %"v42" +p %"v146";
    %"chk20" : A = (Check 0 1 Read 1) %"v147";
    %"v148" : W = (RawLoad (LdNarrow Ub) 0) %"chk20";
    %"v151" = %"v127" +p #3;
    %"chk21" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"v151";
    %"v152" : W = (RawLoad (LdNarrow Ub) 0) %"chk21";
    %"v153" : L = (Ext Uw) %"v152";
    %"v154" = %"v42" +p %"v153";
    %"chk22" : A = (Check 0 1 Read 1) %"v154";
    %"v155" : W = (RawLoad (LdNarrow Ub) 0) %"chk22";
    %"v158" : W = And %"v134", %"v141";
    %"v160" : W = And %"v158", %"v148";
    %"v162" : W = And %"v160", %"v155";
    %"v163" : W = (Cmp Ne W) %"v162", #0
    => br %"v163" ? poll "L123" : "L125";
  @"L125":
    %"v167" : L = Ptoi %"v127";
    %"v169" : L = Sub %"v167", %"v115";
    %"v176" : W = (Cmp Eq W) %"v158", #0
    => br %"v176" ? "L170" : "L171";
  @"L170":
    %"v179" : L = (Ext Uw) %"v134";
    %"v180" : L = Add %"v169", %"v179"
    => goto "L172";
  @"L171":
    %"v183" : L = (Ext Uw) %"v148";
    %"v184" : L = Add %"v169", %"v183";
    %"v185" : L = Add %"v184", #2
    => goto "L172";
  @"L172" [%"v186" : L = phi("L170" => %"v180", "L171" => %"v185")]:
    => ret %"v186"
} }.

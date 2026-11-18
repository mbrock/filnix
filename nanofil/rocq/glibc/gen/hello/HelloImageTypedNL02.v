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

Definition hello_image_fn__nl_normalize_codeset : func :=
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

(** This file defines checked IR from glibc’s `nptl/nptl_deallocate_tsd.os` object.
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

Definition fn___GI___nptl_deallocate_tsd : func :=
  ir_fn{ "export" "__GI___nptl_deallocate_tsd"() -> RVoid {
  @"start":
    call %"v1" : P = $"zthread_self_cookie"();
    %"v6" = %"v1" +p #1568;
    %"chk0" : A = (Check 0 1 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk0"
    => br %"v7" ? "L10" : "L4";
  @"L10" [%"pr.1" : L = phi("L11" => %"v123", "start" => #0)]:
    %"v15" = %"v1" +p #1568;
    %"chk1" : A = (Renew 0 1 Write 1) %"chk0", %"v15";
    store Wb [%"chk1" + 0] <- #0
    => goto "L17";
  @"L17" [%"pr.4" : L = phi("L10" => #0, "L36" => %"pr.5"); %"pr.3" : L = phi("L10" => #0, "L36" => %"v112")]:
    %"v26" : W = (Cmp Ult L) %"pr.3", #32
    => br %"v26" ? "L18" : "L20";
  @"L18":
    %"v29" = %"v1" +p #1312;
    %"v31" : L = Shl %"pr.3", #3;
    %"v32" = %"v29" +p %"v31";
    %"chk2" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v38" : L = Ptoi %"v33";
    %"v39" : L = Ptoi #0;
    %"v40" : W = (Cmp Ne L) %"v38", %"v39"
    => br %"v40" ? "L42" : "L35";
  @"L42" [%"pr.7" : L = phi("L44" => %"v102", "L18" => #0); %"pr.6" : L = phi("L44" => %"v104", "L18" => %"pr.4")]:
    %"v47" : W = (Cmp Ult L) %"pr.7", #32
    => br %"v47" ? "L43" : "L36";
  @"L43":
    %"v51" : L = Shl %"pr.7", #4;
    %"v52" = %"v33" +p %"v51";
    %"v53" = %"v52" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v59" : L = Ptoi %"v54";
    %"v61" : W = (Cmp Ne L) %"v59", %"v39"
    => br %"v61" ? "L55" : "L44";
  @"L55":
    %"v66" = %"v52" +p #8;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk3", %"v66";
    store.ptr [%"chk4" + 0] <- #0;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 1) %"chk3", %"v52";
    %"v74" : L = (RawLoad LdL 0) %"chk5";
    %"v75" : P = Copy $"__GI___pthread_keys";
    %"v77" : L = Shl %"pr.6", #4;
    %"v78" = %"v75" +p %"v77";
    %"chk6" : A = (Check 0 8 Read 1) %"v78";
    %"v79" : L = (RawLoad LdL 0) %"chk6";
    %"v80" : W = (Cmp Eq L) %"v74", %"v79"
    => br %"v80" ? "L81" : "L82";
  @"L81":
    %"v83" : P = Copy $"__GI___pthread_keys";
    %"v86" = %"v83" +p %"v77";
    %"v87" = %"v86" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v89" : L = Ptoi %"v88";
    %"v91" : W = (Cmp Ne L) %"v89", %"v39"
    => goto "L82";
  @"L82" [%"v93" : W = phi("L55" => #0, "L81" => %"v91")]:
    => br %"v93" ? "L67" : "L44";
  @"L67":
    %"v94" : P = Copy $"__GI___pthread_keys";
    %"v97" = %"v94" +p %"v77";
    %"v98" = %"v97" +p #8;
    %"chk8" : A = (Check 0 8 Read 8) %"v98";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : F = CheckFunction %"v99";
    rawcall void %"chk9"(P %"v54")
    => goto "L44";
  @"L44":
    %"v102" : L = Add %"pr.7", #1;
    %"v104" : L = Add %"pr.6", #1
    => goto poll "L42";
  @"L35":
    %"v110" : L = Add %"pr.4", #32
    => goto "L36";
  @"L36" [%"pr.5" : L = phi("L35" => %"v110", "L42" => %"pr.6")]:
    %"v112" : L = Add %"pr.3", #1
    => goto poll "L17";
  @"L20":
    %"v117" = %"v1" +p #1568;
    %"chk10" : A = (Renew 0 1 Read 1) %"chk0", %"v117";
    %"v118" : W = (RawLoad (LdNarrow Ub) 0) %"chk10";
    %"v119" : W = (Cmp Eq W) %"v118", #0
    => br %"v119" ? "L130" : "L11";
  @"L11":
    %"v123" : L = Add %"pr.1", #1;
    %"v124" : W = (Cmp Ult L) %"v123", #4
    => br %"v124" ? poll "L10" : "L12";
  @"L12":
    call %"v127" : P = $"zthread_self_cookie"();
    %"v128" = %"v127" +p #800;
    call %"v129" : P = $"__GI_memset"(P %"v128", W #0, L #512)
    => goto "L130";
  @"L130" [%"pr.2" : L = phi("L132" => %"v161", "L12" => #1, "L20" => #1)]:
    %"v139" : W = (Cmp Ult L) %"pr.2", #32
    => br %"v139" ? "L131" : "L133";
  @"L131":
    %"v142" = %"v1" +p #1312;
    %"v144" : L = Shl %"pr.2", #3;
    %"v145" = %"v142" +p %"v144";
    %"chk11" : A = (Check 0 8 Read 8) %"v145";
    %"v146" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v151" : L = Ptoi %"v146";
    %"v152" : L = Ptoi #0;
    %"v153" : W = (Cmp Ne L) %"v151", %"v152"
    => br %"v153" ? "L147" : "L132";
  @"L147":
    call void $"free"(P %"v146");
    %"v156" = %"v1" +p #1312;
    %"v159" = %"v156" +p %"v144";
    %"chk12" : A = (Check 0 8 Write 8) %"v159";
    store.ptr [%"chk12" + 0] <- #0
    => goto "L132";
  @"L132":
    %"v161" : L = Add %"pr.2", #1
    => goto poll "L130";
  @"L133":
    %"v163" = %"v1" +p #1568;
    %"chk13" : A = (Renew 0 1 Write 1) %"chk0", %"v163";
    store Wb [%"chk13" + 0] <- #0
    => goto "L4";
  @"L4":
    => ret void
} }.

(** This file defines checked IR from glibc’s `misc/getsysstats.os` object.
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

Definition fn___GI___get_avphys_pages : func :=
  ir_fn{ "export" "__GI___get_avphys_pages"() -> (RClass L) {
  @"start":
    %"v0" : P = (Alloc 8) #112;
    call %"v1" : W = $"__sysinfo"(P %"v0");
    %"v2" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v3" : L = (RawLoad LdL 0) %"chk0";
    %"v4" = %"v0" +p #104;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v4";
    %"v5" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    call %"iw_1.v5" : W = $"__GI___getpagesize"();
    %"iw_1.v6" : L = (Ext Sw) %"iw_1.v5"
    => goto "iw_1.L7";
  @"iw_1.L7" [%"iw_1.pr.4" : L = phi("iw_1.L8" => %"iw_1.v21", "start" => %"iw_1.v6"); %"iw_1.pr.2" : W = phi("iw_1.L8" => %"iw_1.v19", "start" => %"v5")]:
    %"iw_1.v11" : W = (Cmp Ugt W) %"iw_1.pr.2", #1
    => br %"iw_1.v11" ? "iw_1.L12" : "iw_1.L13";
  @"iw_1.L12":
    %"iw_1.v15" : W = (Cmp Ugt L) %"iw_1.pr.4", #1
    => goto "iw_1.L13";
  @"iw_1.L13" [%"iw_1.v17" : W = phi("iw_1.L7" => #0, "iw_1.L12" => %"iw_1.v15")]:
    => br %"iw_1.v17" ? "iw_1.L8" : "iw_1.L9";
  @"iw_1.L8":
    %"iw_1.v19" : W = Shr %"iw_1.pr.2", #1;
    %"iw_1.v21" : L = Shr %"iw_1.pr.4", #1
    => goto poll "iw_1.L7";
  @"iw_1.L9":
    %"iw_1.v24" : L = (Ext Uw) %"iw_1.pr.2";
    %"iw_1.v25" : L = Mul %"v3", %"iw_1.v24"
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.pr.3" : L = phi("iw_1.L27" => %"iw_1.v32", "iw_1.L9" => %"iw_1.pr.4"); %"iw_1.pr.1" : L = phi("iw_1.L27" => %"iw_1.v34", "iw_1.L9" => %"iw_1.v25")]:
    %"iw_1.v30" : W = (Cmp Ugt L) %"iw_1.pr.3", #1
    => br %"iw_1.v30" ? "iw_1.L27" : "iw_1.join";
  @"iw_1.L27":
    %"iw_1.v32" : L = Shr %"iw_1.pr.3", #1;
    %"iw_1.v34" : L = Shr %"iw_1.pr.1", #1
    => goto poll "iw_1.L26";
  @"iw_1.join":
    => ret %"iw_1.pr.1"
} }.

Definition fn___GI___get_nprocs : func :=
  ir_fn{ "export" "__GI___get_nprocs"() -> (RClass W) {
  @"start":
    %"v1" : P = Copy $"glibc_getsysstats#str.316";
    %"iw_1.v2" : P = (Alloc 4) #1024;
    %"iw_1.v5" : P = (Alloc 8) #8;
    %"iw_1.v7" : P = (Alloc 8) #8;
    %"iw_1.v36" : P = (Alloc 8) #8;
    %"iw_1.v4" = %"iw_1.v2" +p #1024;
    %"chk0" : A = (Check 0 8 Write 8) %"iw_1.v5";
    store.ptr [%"chk0" + 0] <- %"iw_1.v4";
    %"chk1" : A = (Check 0 8 Write 8) %"iw_1.v7";
    store.ptr [%"chk1" + 0] <- %"iw_1.v4";
    call %"iw_1.v14" : W = $"__GI___open_nocancel"(P %"v1", W #524288);
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v14", #4294967295
    => br %"iw_1.v22" ? "iw_1.L17" : "iw_1.L19";
  @"iw_1.L17":
    call %"iw_1.v25" : P = $"glibc_getsysstats#next_line"(W %"iw_1.v14", P %"iw_1.v2", P %"iw_1.v5", P %"iw_1.v7", P %"iw_1.v4");
    %"iw_1.v30" : L = Ptoi %"iw_1.v25";
    %"iw_1.v31" : L = Ptoi #0;
    %"iw_1.v32" : W = (Cmp Ne L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L33" : "iw_1.L28";
  @"iw_1.L33" [%"iw_1.pr.5" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L17" => #0); %"iw_1.pr.1" : P = phi("iw_1.L107" => %"iw_1.pr.2", "iw_1.L17" => %"iw_1.v25")]:
    call %"iw_1.v39" : L = $"__GI___isoc23_strtoul"(P %"iw_1.pr.1", P %"iw_1.v36", W #10);
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v36";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v45" : L = Ptoi %"iw_1.pr.1";
    %"iw_1.v46" : L = Ptoi %"iw_1.v44";
    %"iw_1.v47" : W = (Cmp Eq L) %"iw_1.v45", %"iw_1.v46"
    => br %"iw_1.v47" ? "iw_1.L28" : "iw_1.L42";
  @"iw_1.L42":
    %"iw_1.v54" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk4" : A = (Check 0 1 Read 1) %"iw_1.v54";
    %"iw_1.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_1.v56" : W = (Cmp Eq W) %"iw_1.v55", #45
    => br %"iw_1.v56" ? "iw_1.L51" : "iw_1.L53";
  @"iw_1.L51":
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v58" = %"iw_1.v57" +p #1;
    call %"iw_1.v60" : L = $"__GI___isoc23_strtoul"(P %"iw_1.v58", P %"iw_1.v36", W #10);
    %"chk6" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v65" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v66" : L = Ptoi %"iw_1.v58";
    %"iw_1.v67" : L = Ptoi %"iw_1.v65";
    %"iw_1.v68" : W = (Cmp Eq L) %"iw_1.v66", %"iw_1.v67"
    => br %"iw_1.v68" ? "iw_1.L28" : "iw_1.L53";
  @"iw_1.L53" [%"iw_1.pr.8" : L = phi("iw_1.L51" => %"iw_1.v60", "iw_1.L42" => %"iw_1.v39")]:
    %"iw_1.v75" : W = (Cmp Uge L) %"iw_1.pr.8", %"iw_1.v39"
    => br %"iw_1.v75" ? "iw_1.L70" : "iw_1.L72";
  @"iw_1.L70":
    %"iw_1.v79" : L = Sub %"iw_1.pr.8", %"iw_1.v39";
    %"iw_1.v80" : L = Add %"iw_1.v79", #1;
    %"iw_1.v81" : L = (Ext Sw) %"iw_1.pr.5";
    %"iw_1.v82" : L = Add %"iw_1.v81", %"iw_1.v80"
    => goto "iw_1.L72";
  @"iw_1.L72" [%"iw_1.pr.7" : W = phi("iw_1.L70" => %"iw_1.v82", "iw_1.L53" => %"iw_1.pr.5")]:
    %"chk7" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v83" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v7";
    %"iw_1.v88" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v89" : L = Ptoi %"iw_1.v83";
    %"iw_1.v90" : L = Ptoi %"iw_1.v88";
    %"iw_1.v91" : W = (Cmp Ult L) %"iw_1.v89", %"iw_1.v90"
    => br %"iw_1.v91" ? "iw_1.L92" : "iw_1.L93";
  @"iw_1.L92":
    %"chk9" : A = (Check 0 1 Read 1) %"iw_1.v83";
    %"iw_1.v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"iw_1.v96" : W = (Cmp Eq W) %"iw_1.v95", #44
    => goto "iw_1.L93";
  @"iw_1.L93" [%"iw_1.v98" : W = phi("iw_1.L72" => #0, "iw_1.L92" => %"iw_1.v96")]:
    => br %"iw_1.v98" ? "iw_1.L84" : "iw_1.L86";
  @"iw_1.L84":
    %"iw_1.v100" = %"iw_1.v83" +p #1
    => goto "iw_1.L86";
  @"iw_1.L86" [%"iw_1.pr.2" : P = phi("iw_1.L84" => %"iw_1.v100", "iw_1.L93" => %"iw_1.v83")]:
    %"iw_1.v102" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v103" : L = Ptoi %"iw_1.pr.2";
    %"iw_1.v104" : L = Ptoi %"iw_1.v102";
    %"iw_1.v105" : W = (Cmp Ult L) %"iw_1.v103", %"iw_1.v104"
    => br %"iw_1.v105" ? "iw_1.L106" : "iw_1.L107";
  @"iw_1.L106":
    %"chk11" : A = (Check 0 1 Read 1) %"iw_1.pr.2";
    %"iw_1.v109" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"iw_1.v110" : W = (Cmp Ne W) %"iw_1.v109", #10
    => goto "iw_1.L107";
  @"iw_1.L107" [%"iw_1.v112" : W = phi("iw_1.L86" => #0, "iw_1.L106" => %"iw_1.v110")]:
    => br %"iw_1.v112" ? poll "iw_1.L33" : "iw_1.L28";
  @"iw_1.L28" [%"iw_1.pr.4" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L33" => #0, "iw_1.L51" => #0, "iw_1.L17" => #0)]:
    call void $"__GI___close_nocancel_nostatus"(W %"iw_1.v14")
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.pr.3" : W = phi("iw_1.L28" => %"iw_1.pr.4", "start" => #0)]:
    %"v7" : W = (Cmp Ne W) %"iw_1.pr.3", #0
    => br %"v7" ? "L3" : "iw_2.start";
  @"L3":
    => ret %"iw_1.pr.3";
  @"iw_2.start":
    %"iw_2.iw_1.v0" : P = (Alloc 4) #1024;
    %"iw_2.iw_1.v3" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v5" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v2" = %"iw_2.iw_1.v0" +p #1024;
    %"chk12" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v3";
    store.ptr [%"chk12" + 0] <- %"iw_2.iw_1.v2";
    %"chk13" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v5";
    store.ptr [%"chk13" + 0] <- %"iw_2.iw_1.v2";
    %"iw_2.iw_1.v11" : P = Copy $"glibc_getsysstats#str.314";
    call %"iw_2.iw_1.v13" : W = $"__GI___open_nocancel"(P %"iw_2.iw_1.v11", W #524288);
    %"iw_2.iw_1.v19" : W = (Cmp Ne W) %"iw_2.iw_1.v13", #4294967295
    => br %"iw_2.iw_1.v19" ? "iw_2.iw_1.L21" : "iw_2.iw_1.L16";
  @"iw_2.iw_1.L21" [%"iw_2.iw_1.pr.2" : W = phi("iw_2.start" => #0, "iw_2.iw_1.L48" => %"iw_2.iw_1.pr.2", "iw_2.iw_1.L38" => %"iw_2.iw_1.v54")]:
    call %"iw_2.iw_1.v26" : P = $"glibc_getsysstats#next_line"(W %"iw_2.iw_1.v13", P %"iw_2.iw_1.v0", P %"iw_2.iw_1.v3", P %"iw_2.iw_1.v5", P %"iw_2.iw_1.v2");
    %"iw_2.iw_1.v27" : L = Ptoi %"iw_2.iw_1.v26";
    %"iw_2.iw_1.v28" : L = Ptoi #0;
    %"iw_2.iw_1.v29" : W = (Cmp Ne L) %"iw_2.iw_1.v27", %"iw_2.iw_1.v28"
    => br %"iw_2.iw_1.v29" ? "iw_2.iw_1.L22" : "iw_2.iw_1.L23";
  @"iw_2.iw_1.L22":
    %"iw_2.iw_1.v34" : P = Copy $"glibc_getsysstats#str.315";
    call %"iw_2.iw_1.v35" : W = $"__GI_strncmp"(P %"iw_2.iw_1.v26", P %"iw_2.iw_1.v34", L #3);
    %"iw_2.iw_1.v36" : W = (Cmp Ne W) %"iw_2.iw_1.v35", #0
    => br %"iw_2.iw_1.v36" ? "iw_2.iw_1.L23" : "iw_2.iw_1.L31";
  @"iw_2.iw_1.L31":
    %"iw_2.iw_1.v43" = %"iw_2.iw_1.v26" +p #3;
    %"chk14" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v43";
    %"iw_2.iw_1.v44" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.iw_1.v46" : W = (Cmp Sge W) %"iw_2.iw_1.v44", #48
    => br %"iw_2.iw_1.v46" ? "iw_2.iw_1.L47" : "iw_2.iw_1.L48";
  @"iw_2.iw_1.L47":
    %"iw_2.iw_1.v50" : W = (Cmp Sle W) %"iw_2.iw_1.v44", #57
    => goto "iw_2.iw_1.L48";
  @"iw_2.iw_1.L48" [%"iw_2.iw_1.v52" : W = phi("iw_2.iw_1.L31" => #0, "iw_2.iw_1.L47" => %"iw_2.iw_1.v50")]:
    => br %"iw_2.iw_1.v52" ? "iw_2.iw_1.L38" : poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L38":
    %"iw_2.iw_1.v54" : W = Add %"iw_2.iw_1.pr.2", #1
    => goto poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L23":
    call void $"__GI___close_nocancel_nostatus"(W %"iw_2.iw_1.v13")
    => goto "iw_2.iw_1.L16";
  @"iw_2.iw_1.L16" [%"iw_2.iw_1.pr.1" : W = phi("iw_2.iw_1.L23" => %"iw_2.iw_1.pr.2", "iw_2.start" => #0)]:
    %"iw_2.v6" : W = (Cmp Ne W) %"iw_2.iw_1.pr.1", #0
    => br %"iw_2.v6" ? "iw_2.join" : "iw_2.iw_2.start";
  @"iw_2.iw_2.start":
    %"iw_2.iw_2.v0" : P = (Alloc 8) #4096;
    call %"iw_2.iw_2.v2" : W = $"zsys_sched_getaffinity"(W #0, L #4096, P %"iw_2.iw_2.v0");
    %"iw_2.iw_2.v7" : W = (Cmp Sgt W) %"iw_2.iw_2.v2", #0
    => br %"iw_2.iw_2.v7" ? "iw_2.iw_2.L3" : "iw_2.iw_2.L4";
  @"iw_2.iw_2.L3":
    %"iw_2.iw_2.v9" : L = (Ext Sw) %"iw_2.iw_2.v2";
    call %"iw_2.iw_2.v10" : W = $"__GI___sched_cpucount"(L %"iw_2.iw_2.v9", P %"iw_2.iw_2.v0")
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.L4":
    %"iw_2.iw_2.v17" : W = (Cmp Eq W) %"iw_2.iw_2.v2", #4294967274
    => br %"iw_2.iw_2.v17" ? "iw_2.iw_2.join" : "iw_2.iw_2.L5";
  @"iw_2.iw_2.L5":
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.join" [%"iw_2.v9" : W = phi("iw_2.iw_2.L3" => %"iw_2.iw_2.v10", "iw_2.iw_2.L5" => #0, "iw_2.iw_2.L4" => #32768)]:
    %"iw_2.v14" : W = (Cmp Ne W) %"iw_2.v9", #0
    => br %"iw_2.v14" ? "iw_2.join" : "iw_2.L12";
  @"iw_2.L12":
    => goto "iw_2.join";
  @"iw_2.join" [%"v10" : W = phi("iw_2.L12" => #2, "iw_2.iw_1.L16" => %"iw_2.iw_1.pr.1", "iw_2.iw_2.join" => %"iw_2.v9")]:
    => ret %"v10"
} }.

Definition fn___GI___get_nprocs_conf : func :=
  ir_fn{ "export" "__GI___get_nprocs_conf"() -> (RClass W) {
  @"start":
    %"v1" : P = Copy $"glibc_getsysstats#str.317";
    %"iw_1.v2" : P = (Alloc 4) #1024;
    %"iw_1.v5" : P = (Alloc 8) #8;
    %"iw_1.v7" : P = (Alloc 8) #8;
    %"iw_1.v36" : P = (Alloc 8) #8;
    %"iw_1.v4" = %"iw_1.v2" +p #1024;
    %"chk0" : A = (Check 0 8 Write 8) %"iw_1.v5";
    store.ptr [%"chk0" + 0] <- %"iw_1.v4";
    %"chk1" : A = (Check 0 8 Write 8) %"iw_1.v7";
    store.ptr [%"chk1" + 0] <- %"iw_1.v4";
    call %"iw_1.v14" : W = $"__GI___open_nocancel"(P %"v1", W #524288);
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v14", #4294967295
    => br %"iw_1.v22" ? "iw_1.L17" : "iw_1.L19";
  @"iw_1.L17":
    call %"iw_1.v25" : P = $"glibc_getsysstats#next_line"(W %"iw_1.v14", P %"iw_1.v2", P %"iw_1.v5", P %"iw_1.v7", P %"iw_1.v4");
    %"iw_1.v30" : L = Ptoi %"iw_1.v25";
    %"iw_1.v31" : L = Ptoi #0;
    %"iw_1.v32" : W = (Cmp Ne L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L33" : "iw_1.L28";
  @"iw_1.L33" [%"iw_1.pr.5" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L17" => #0); %"iw_1.pr.1" : P = phi("iw_1.L107" => %"iw_1.pr.2", "iw_1.L17" => %"iw_1.v25")]:
    call %"iw_1.v39" : L = $"__GI___isoc23_strtoul"(P %"iw_1.pr.1", P %"iw_1.v36", W #10);
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v36";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v45" : L = Ptoi %"iw_1.pr.1";
    %"iw_1.v46" : L = Ptoi %"iw_1.v44";
    %"iw_1.v47" : W = (Cmp Eq L) %"iw_1.v45", %"iw_1.v46"
    => br %"iw_1.v47" ? "iw_1.L28" : "iw_1.L42";
  @"iw_1.L42":
    %"iw_1.v54" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk4" : A = (Check 0 1 Read 1) %"iw_1.v54";
    %"iw_1.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_1.v56" : W = (Cmp Eq W) %"iw_1.v55", #45
    => br %"iw_1.v56" ? "iw_1.L51" : "iw_1.L53";
  @"iw_1.L51":
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v58" = %"iw_1.v57" +p #1;
    call %"iw_1.v60" : L = $"__GI___isoc23_strtoul"(P %"iw_1.v58", P %"iw_1.v36", W #10);
    %"chk6" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v65" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v66" : L = Ptoi %"iw_1.v58";
    %"iw_1.v67" : L = Ptoi %"iw_1.v65";
    %"iw_1.v68" : W = (Cmp Eq L) %"iw_1.v66", %"iw_1.v67"
    => br %"iw_1.v68" ? "iw_1.L28" : "iw_1.L53";
  @"iw_1.L53" [%"iw_1.pr.8" : L = phi("iw_1.L51" => %"iw_1.v60", "iw_1.L42" => %"iw_1.v39")]:
    %"iw_1.v75" : W = (Cmp Uge L) %"iw_1.pr.8", %"iw_1.v39"
    => br %"iw_1.v75" ? "iw_1.L70" : "iw_1.L72";
  @"iw_1.L70":
    %"iw_1.v79" : L = Sub %"iw_1.pr.8", %"iw_1.v39";
    %"iw_1.v80" : L = Add %"iw_1.v79", #1;
    %"iw_1.v81" : L = (Ext Sw) %"iw_1.pr.5";
    %"iw_1.v82" : L = Add %"iw_1.v81", %"iw_1.v80"
    => goto "iw_1.L72";
  @"iw_1.L72" [%"iw_1.pr.7" : W = phi("iw_1.L70" => %"iw_1.v82", "iw_1.L53" => %"iw_1.pr.5")]:
    %"chk7" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v36";
    %"iw_1.v83" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v7";
    %"iw_1.v88" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v89" : L = Ptoi %"iw_1.v83";
    %"iw_1.v90" : L = Ptoi %"iw_1.v88";
    %"iw_1.v91" : W = (Cmp Ult L) %"iw_1.v89", %"iw_1.v90"
    => br %"iw_1.v91" ? "iw_1.L92" : "iw_1.L93";
  @"iw_1.L92":
    %"chk9" : A = (Check 0 1 Read 1) %"iw_1.v83";
    %"iw_1.v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"iw_1.v96" : W = (Cmp Eq W) %"iw_1.v95", #44
    => goto "iw_1.L93";
  @"iw_1.L93" [%"iw_1.v98" : W = phi("iw_1.L72" => #0, "iw_1.L92" => %"iw_1.v96")]:
    => br %"iw_1.v98" ? "iw_1.L84" : "iw_1.L86";
  @"iw_1.L84":
    %"iw_1.v100" = %"iw_1.v83" +p #1
    => goto "iw_1.L86";
  @"iw_1.L86" [%"iw_1.pr.2" : P = phi("iw_1.L84" => %"iw_1.v100", "iw_1.L93" => %"iw_1.v83")]:
    %"iw_1.v102" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v103" : L = Ptoi %"iw_1.pr.2";
    %"iw_1.v104" : L = Ptoi %"iw_1.v102";
    %"iw_1.v105" : W = (Cmp Ult L) %"iw_1.v103", %"iw_1.v104"
    => br %"iw_1.v105" ? "iw_1.L106" : "iw_1.L107";
  @"iw_1.L106":
    %"chk11" : A = (Check 0 1 Read 1) %"iw_1.pr.2";
    %"iw_1.v109" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"iw_1.v110" : W = (Cmp Ne W) %"iw_1.v109", #10
    => goto "iw_1.L107";
  @"iw_1.L107" [%"iw_1.v112" : W = phi("iw_1.L86" => #0, "iw_1.L106" => %"iw_1.v110")]:
    => br %"iw_1.v112" ? poll "iw_1.L33" : "iw_1.L28";
  @"iw_1.L28" [%"iw_1.pr.4" : W = phi("iw_1.L107" => %"iw_1.pr.7", "iw_1.L33" => #0, "iw_1.L51" => #0, "iw_1.L17" => #0)]:
    call void $"__GI___close_nocancel_nostatus"(W %"iw_1.v14")
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.pr.3" : W = phi("iw_1.L28" => %"iw_1.pr.4", "start" => #0)]:
    %"v7" : W = (Cmp Ne W) %"iw_1.pr.3", #0
    => br %"v7" ? "L3" : "iw_2.start";
  @"L3":
    => ret %"iw_1.pr.3";
  @"iw_2.start":
    %"iw_2.iw_1.v0" : P = (Alloc 4) #1024;
    %"iw_2.iw_1.v3" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v5" : P = (Alloc 8) #8;
    %"iw_2.iw_1.v2" = %"iw_2.iw_1.v0" +p #1024;
    %"chk12" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v3";
    store.ptr [%"chk12" + 0] <- %"iw_2.iw_1.v2";
    %"chk13" : A = (Check 0 8 Write 8) %"iw_2.iw_1.v5";
    store.ptr [%"chk13" + 0] <- %"iw_2.iw_1.v2";
    %"iw_2.iw_1.v11" : P = Copy $"glibc_getsysstats#str.314";
    call %"iw_2.iw_1.v13" : W = $"__GI___open_nocancel"(P %"iw_2.iw_1.v11", W #524288);
    %"iw_2.iw_1.v19" : W = (Cmp Ne W) %"iw_2.iw_1.v13", #4294967295
    => br %"iw_2.iw_1.v19" ? "iw_2.iw_1.L21" : "iw_2.iw_1.L16";
  @"iw_2.iw_1.L21" [%"iw_2.iw_1.pr.2" : W = phi("iw_2.start" => #0, "iw_2.iw_1.L48" => %"iw_2.iw_1.pr.2", "iw_2.iw_1.L38" => %"iw_2.iw_1.v54")]:
    call %"iw_2.iw_1.v26" : P = $"glibc_getsysstats#next_line"(W %"iw_2.iw_1.v13", P %"iw_2.iw_1.v0", P %"iw_2.iw_1.v3", P %"iw_2.iw_1.v5", P %"iw_2.iw_1.v2");
    %"iw_2.iw_1.v27" : L = Ptoi %"iw_2.iw_1.v26";
    %"iw_2.iw_1.v28" : L = Ptoi #0;
    %"iw_2.iw_1.v29" : W = (Cmp Ne L) %"iw_2.iw_1.v27", %"iw_2.iw_1.v28"
    => br %"iw_2.iw_1.v29" ? "iw_2.iw_1.L22" : "iw_2.iw_1.L23";
  @"iw_2.iw_1.L22":
    %"iw_2.iw_1.v34" : P = Copy $"glibc_getsysstats#str.315";
    call %"iw_2.iw_1.v35" : W = $"__GI_strncmp"(P %"iw_2.iw_1.v26", P %"iw_2.iw_1.v34", L #3);
    %"iw_2.iw_1.v36" : W = (Cmp Ne W) %"iw_2.iw_1.v35", #0
    => br %"iw_2.iw_1.v36" ? "iw_2.iw_1.L23" : "iw_2.iw_1.L31";
  @"iw_2.iw_1.L31":
    %"iw_2.iw_1.v43" = %"iw_2.iw_1.v26" +p #3;
    %"chk14" : A = (Check 0 1 Read 1) %"iw_2.iw_1.v43";
    %"iw_2.iw_1.v44" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.iw_1.v46" : W = (Cmp Sge W) %"iw_2.iw_1.v44", #48
    => br %"iw_2.iw_1.v46" ? "iw_2.iw_1.L47" : "iw_2.iw_1.L48";
  @"iw_2.iw_1.L47":
    %"iw_2.iw_1.v50" : W = (Cmp Sle W) %"iw_2.iw_1.v44", #57
    => goto "iw_2.iw_1.L48";
  @"iw_2.iw_1.L48" [%"iw_2.iw_1.v52" : W = phi("iw_2.iw_1.L31" => #0, "iw_2.iw_1.L47" => %"iw_2.iw_1.v50")]:
    => br %"iw_2.iw_1.v52" ? "iw_2.iw_1.L38" : poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L38":
    %"iw_2.iw_1.v54" : W = Add %"iw_2.iw_1.pr.2", #1
    => goto poll "iw_2.iw_1.L21";
  @"iw_2.iw_1.L23":
    call void $"__GI___close_nocancel_nostatus"(W %"iw_2.iw_1.v13")
    => goto "iw_2.iw_1.L16";
  @"iw_2.iw_1.L16" [%"iw_2.iw_1.pr.1" : W = phi("iw_2.iw_1.L23" => %"iw_2.iw_1.pr.2", "iw_2.start" => #0)]:
    %"iw_2.v6" : W = (Cmp Ne W) %"iw_2.iw_1.pr.1", #0
    => br %"iw_2.v6" ? "iw_2.join" : "iw_2.iw_2.start";
  @"iw_2.iw_2.start":
    %"iw_2.iw_2.v0" : P = (Alloc 8) #4096;
    call %"iw_2.iw_2.v2" : W = $"zsys_sched_getaffinity"(W #0, L #4096, P %"iw_2.iw_2.v0");
    %"iw_2.iw_2.v7" : W = (Cmp Sgt W) %"iw_2.iw_2.v2", #0
    => br %"iw_2.iw_2.v7" ? "iw_2.iw_2.L3" : "iw_2.iw_2.L4";
  @"iw_2.iw_2.L3":
    %"iw_2.iw_2.v9" : L = (Ext Sw) %"iw_2.iw_2.v2";
    call %"iw_2.iw_2.v10" : W = $"__GI___sched_cpucount"(L %"iw_2.iw_2.v9", P %"iw_2.iw_2.v0")
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.L4":
    %"iw_2.iw_2.v17" : W = (Cmp Eq W) %"iw_2.iw_2.v2", #4294967274
    => br %"iw_2.iw_2.v17" ? "iw_2.iw_2.join" : "iw_2.iw_2.L5";
  @"iw_2.iw_2.L5":
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.join" [%"iw_2.v9" : W = phi("iw_2.iw_2.L3" => %"iw_2.iw_2.v10", "iw_2.iw_2.L5" => #0, "iw_2.iw_2.L4" => #32768)]:
    %"iw_2.v14" : W = (Cmp Ne W) %"iw_2.v9", #0
    => br %"iw_2.v14" ? "iw_2.join" : "iw_2.L12";
  @"iw_2.L12":
    => goto "iw_2.join";
  @"iw_2.join" [%"v10" : W = phi("iw_2.L12" => #2, "iw_2.iw_1.L16" => %"iw_2.iw_1.pr.1", "iw_2.iw_2.join" => %"iw_2.v9")]:
    => ret %"v10"
} }.

Definition fn___GI___get_phys_pages : func :=
  ir_fn{ "export" "__GI___get_phys_pages"() -> (RClass L) {
  @"start":
    %"v0" : P = (Alloc 8) #112;
    call %"v1" : W = $"__sysinfo"(P %"v0");
    %"v2" = %"v0" +p #32;
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v3" : L = (RawLoad LdL 0) %"chk0";
    %"v4" = %"v0" +p #104;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v4";
    %"v5" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    call %"iw_1.v5" : W = $"__GI___getpagesize"();
    %"iw_1.v6" : L = (Ext Sw) %"iw_1.v5"
    => goto "iw_1.L7";
  @"iw_1.L7" [%"iw_1.pr.4" : L = phi("iw_1.L8" => %"iw_1.v21", "start" => %"iw_1.v6"); %"iw_1.pr.2" : W = phi("iw_1.L8" => %"iw_1.v19", "start" => %"v5")]:
    %"iw_1.v11" : W = (Cmp Ugt W) %"iw_1.pr.2", #1
    => br %"iw_1.v11" ? "iw_1.L12" : "iw_1.L13";
  @"iw_1.L12":
    %"iw_1.v15" : W = (Cmp Ugt L) %"iw_1.pr.4", #1
    => goto "iw_1.L13";
  @"iw_1.L13" [%"iw_1.v17" : W = phi("iw_1.L7" => #0, "iw_1.L12" => %"iw_1.v15")]:
    => br %"iw_1.v17" ? "iw_1.L8" : "iw_1.L9";
  @"iw_1.L8":
    %"iw_1.v19" : W = Shr %"iw_1.pr.2", #1;
    %"iw_1.v21" : L = Shr %"iw_1.pr.4", #1
    => goto poll "iw_1.L7";
  @"iw_1.L9":
    %"iw_1.v24" : L = (Ext Uw) %"iw_1.pr.2";
    %"iw_1.v25" : L = Mul %"v3", %"iw_1.v24"
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.pr.3" : L = phi("iw_1.L27" => %"iw_1.v32", "iw_1.L9" => %"iw_1.pr.4"); %"iw_1.pr.1" : L = phi("iw_1.L27" => %"iw_1.v34", "iw_1.L9" => %"iw_1.v25")]:
    %"iw_1.v30" : W = (Cmp Ugt L) %"iw_1.pr.3", #1
    => br %"iw_1.v30" ? "iw_1.L27" : "iw_1.join";
  @"iw_1.L27":
    %"iw_1.v32" : L = Shr %"iw_1.pr.3", #1;
    %"iw_1.v34" : L = Shr %"iw_1.pr.1", #1
    => goto poll "iw_1.L26";
  @"iw_1.join":
    => ret %"iw_1.pr.1"
} }.

Definition fn_glibc_getsysstats'23next_line : func :=
  ir_fn{ "local" "glibc_getsysstats#next_line"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8") -> (RClass P) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk2" : A = (Check 0 8 Read 8) %"v6";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v20" : L = Ptoi %"v17";
    %"v21" : L = Ptoi %"v19";
    %"v22" : L = Sub %"v20", %"v21";
    call %"v23" : P = $"__GI_memchr"(P %"v15", W #10, L %"v22");
    %"v28" : L = Ptoi %"v23";
    %"v29" : L = Ptoi #0;
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => br %"v30" ? "L24" : "L26";
  @"L24":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v37" : L = Ptoi %"v35";
    %"v38" : L = Ptoi %"v2";
    %"v39" : W = (Cmp Ne L) %"v37", %"v38"
    => br %"v39" ? "L31" : "L33";
  @"L31":
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v46" : L = Ptoi %"v44";
    %"v47" : L = Ptoi %"v8";
    %"v48" : W = (Cmp Eq L) %"v46", %"v47"
    => br %"v48" ? "L40" : "L41";
  @"L40":
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v56" : L = Ptoi %"v53";
    %"v57" : L = Ptoi %"v55";
    %"v58" : L = Sub %"v56", %"v57";
    call %"v59" : P = $"__GI_memmove"(P %"v2", P %"v51", L %"v58");
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v66" : L = Ptoi %"v63";
    %"v67" : L = Ptoi %"v65";
    %"v68" : L = Sub %"v66", %"v67";
    %"v69" = %"v2" +p %"v68";
    %"chk11" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk11" + 0] <- %"v69";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk12" + 0] <- %"v2";
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v80" : L = Ptoi %"v78";
    %"v81" : L = Sub %"v47", %"v80";
    call %"v82" : L = $"__GI___read_nocancel"(W %"v0", P %"v75", L %"v81");
    %"v87" : W = (Cmp Slt L) %"v82", #0
    => br %"v87" ? "L83" : "L85";
  @"L83":
    => ret #0;
  @"L85":
    %"chk15" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v92" = %"v90" +p %"v82";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk16" + 0] <- %"v92";
    %"chk17" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v99" : L = Ptoi %"v96";
    %"v100" : L = Ptoi %"v98";
    %"v101" : L = Sub %"v99", %"v100";
    call %"v102" : P = $"__GI_memchr"(P %"v94", W #10, L %"v101")
    => goto "L103";
  @"L103" [%"pr.3" : P = phi("L142" => %"v149", "L85" => %"v102")]:
    %"v107" : L = Ptoi %"pr.3";
    %"v109" : W = (Cmp Eq L) %"v107", %"v29"
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"chk20" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v115" : L = Ptoi %"v113";
    %"v117" : W = (Cmp Eq L) %"v115", %"v47"
    => goto "L111";
  @"L111" [%"v119" : W = phi("L103" => #0, "L110" => %"v117")]:
    => br %"v119" ? "L104" : "L42";
  @"L104":
    %"v126" : L = Sub %"v47", %"v38";
    %"v127" : L = Mul %"v126", #3;
    %"v128" : L = Div %"v127", #4;
    %"v129" = %"v2" +p %"v128";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk21" + 0] <- %"v129";
    %"chk22" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v137" : L = Ptoi %"v135";
    %"v138" : L = Sub %"v47", %"v137";
    call %"v139" : L = $"__GI___read_nocancel"(W %"v0", P %"v132", L %"v138");
    %"v144" : W = (Cmp Slt L) %"v139", #0
    => br %"v144" ? "L140" : "L142";
  @"L140":
    => ret #0;
  @"L142":
    %"chk24" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"v149" : P = $"__GI_memchr"(P %"v147", W #10, L %"v139");
    %"chk25" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Check 0 1 Write 1) %"v151";
    store Wb [%"chk26" + 0] <- #10;
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v155" = %"v153" +p %"v139";
    %"chk28" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk28" + 0] <- %"v155"
    => goto poll "L103";
  @"L41":
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v159" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v162" : L = Ptoi %"v159";
    %"v163" : L = Ptoi %"v161";
    %"v164" : L = Sub %"v162", %"v163";
    call %"v165" : P = $"__GI_memchr"(P %"v157", W #10, L %"v164")
    => goto "L42";
  @"L42" [%"pr.7" : P = phi("L41" => %"v165", "L111" => %"pr.3")]:
    %"chk32" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk32"
    => goto "L33";
  @"L33" [%"pr.6" : P = phi("L42" => %"pr.7", "L24" => %"v23"); %"pr.2" : P = phi("L42" => %"v167", "L24" => %"v12")]:
    %"v172" : L = Ptoi %"pr.6";
    %"v174" : W = (Cmp Eq L) %"v172", %"v29"
    => br %"v174" ? "L168" : "L26";
  @"L168":
    %"chk33" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk33";
    (Flight (a "v177") Sub [(FAddress (t "v176")); (FValue (Const 1))] (LowerOf (t "v176")))
    => goto "L26";
  @"L26" [%"pr.5" : P = phi("L168" => %"v177", "L33" => %"pr.6", "start" => %"v23"); %"pr.1" : P = phi("L168" => %"pr.2", "L33" => %"pr.2", "start" => %"v12")]:
    %"v180" = %"pr.5" +p #1;
    %"chk34" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk34" + 0] <- %"v180";
    %"chk35" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v185" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v188" : L = Ptoi %"v185";
    %"v189" : L = Ptoi %"v187";
    %"v190" : W = (Cmp Ule L) %"v188", %"v189"
    => br %"v190" ? "L183" : "L182";
  @"L182":
    %"v191" : P = Copy $"glibc_getsysstats#str.311";
    %"v192" : P = Copy $"glibc_getsysstats#str.312";
    %"v193" : P = Copy $"glibc_getsysstats#str.313";
    call void $"__libc_assert_fail"(P %"v191", P %"v192", W #103, P %"v193")
    => goto "L183";
  @"L183":
    %"chk37" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v200" : L = Ptoi %"pr.1";
    %"v201" : L = Ptoi %"v199";
    %"v202" : W = (Cmp Eq L) %"v200", %"v201"
    => br %"v202" ? "L196" : "L195";
  @"L195":
    => goto "L196";
  @"L196" [%"v204" : P = phi("L195" => %"pr.1", "L183" => #0)]:
    => ret %"v204"
} }.

Definition item_glibc_getsysstats'23str'2e311 : item :=
  (IData (a "glibc_getsysstats#str.311") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 99); (Item Wb 112); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 42); (Item Wb 114); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_getsysstats'23str'2e312 : item :=
  (IData (a "glibc_getsysstats#str.312") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_getsysstats'23str'2e313 : item :=
  (IData (a "glibc_getsysstats#str.313") (LRo (a "local")) 1 [(Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 95); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_getsysstats'23str'2e314 : item :=
  (IData (a "glibc_getsysstats#str.314") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 47); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_getsysstats'23str'2e315 : item :=
  (IData (a "glibc_getsysstats#str.315") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 112); (Item Wb 117); (Item Wb 0)]).

Definition item_glibc_getsysstats'23str'2e316 : item :=
  (IData (a "glibc_getsysstats#str.316") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 47); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 47); (Item Wb 99); (Item Wb 112); (Item Wb 117); (Item Wb 47); (Item Wb 111); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_getsysstats'23str'2e317 : item :=
  (IData (a "glibc_getsysstats#str.317") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 47); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 47); (Item Wb 99); (Item Wb 112); (Item Wb 117); (Item Wb 47); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

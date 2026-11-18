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

Definition hello_image_fn_main : func :=
  ir_fn{ "export" "main"(W %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #8;
    %"v6" : P = (Alloc 4) #8;
    call void $"mbszero"(P %"v6");
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"set_program_name"(P %"v10");
    %"v11" : P = Copy $"hello#str.80";
    call %"v12" : P = $"setlocale"(W #6, P %"v11");
    %"v13" : P = Copy $"hello#str.81";
    %"chk1" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk1" + 0] <- %"v13";
    %"v14" : P = Copy $"close_stdout";
    call %"v15" : W = $"atexit"(P %"v14")
    => goto "iw_1.L8";
  @"iw_1.L8" [%"iw_1.pr.2" : W = phi("iw_1.L35" => %"iw_1.pr.2", "iw_1.L42" => %"iw_1.pr.2", "iw_1.L52" => #1, "start" => #0)]:
    %"iw_1.v13" : P = Copy $"hello#str.69";
    %"iw_1.v14" : P = Copy $"hello#parse_options.longopts.64";
    call %"iw_1.v15" : W = $"getopt_long"(W %"v0", P %"v2", P %"iw_1.v13", P %"iw_1.v14", P #0);
    %"iw_1.v17" : W = (Cmp Ne W) %"iw_1.v15", #4294967295
    => br %"iw_1.v17" ? "iw_1.L19" : "iw_1.L10";
  @"iw_1.L21":
    %"iw_1.v22" : P = Copy $"stdout";
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v22";
    %"iw_1.v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v24" : P = Copy $"hello#str.70";
    %"iw_1.v25" : P = Copy $"hello#str.63";
    %"iw_1.v26" : P = Copy $"hello#str.71";
    %"iw_1.v27" : P = Copy $"hello#str.72";
    call %"iw_1.v28" : P = $"proper_name"(P %"iw_1.v27");
    %"iw_1.v29" : P = Copy $"hello#str.73";
    call %"iw_1.v30" : P = $"proper_name"(P %"iw_1.v29");
    %"iw_1.v31" : P = Copy $"hello#str.74";
    call %"iw_1.v32" : P = $"proper_name"(P %"iw_1.v31");
    %"iw_1.v33" : P = Copy $"hello#str.75";
    call %"iw_1.v34" : P = $"proper_name"(P %"iw_1.v33");
    call void $"version_etc"(P %"iw_1.v23", P %"iw_1.v24", P %"iw_1.v25", P %"iw_1.v26", P %"iw_1.v28", P %"iw_1.v30", P %"iw_1.v32", P %"iw_1.v34", P #0);
    call void $"exit"(W #0)
    => goto "iw_1.L35";
  @"iw_1.L35":
    %"iw_1.v37" : P = Copy $"optarg";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v37";
    %"iw_1.v38" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk1", %"v4";
    store.ptr [%"chk4" + 0] <- %"iw_1.v38"
    => goto poll "iw_1.L8";
  @"iw_1.L39":
    %"iw_1.v40" : P = Copy $"stdout";
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"iw_1.iw_1.v3" : P = $"setlocale"(W #5, P #0);
    %"iw_1.iw_1.v5" : P = Copy $"hello#str.54";
    %"iw_1.iw_1.v6" : P = Copy $"program_name";
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v6";
    %"iw_1.iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"iw_1.iw_1.v8" : W = $"fprintf"(P %"iw_1.v41", P %"iw_1.iw_1.v5", P %"iw_1.iw_1.v7");
    %"iw_1.iw_1.v9" : P = Copy $"hello#str.55";
    call %"iw_1.iw_1.v11" : W = $"fputs"(P %"iw_1.iw_1.v9", P %"iw_1.v41");
    %"iw_1.iw_1.v12" : P = Copy $"hello#str.56";
    call %"iw_1.iw_1.v14" : W = $"fputs"(P %"iw_1.iw_1.v12", P %"iw_1.v41");
    %"iw_1.iw_1.v15" : P = Copy $"hello#str.57";
    call %"iw_1.iw_1.v17" : W = $"fputs"(P %"iw_1.iw_1.v15", P %"iw_1.v41");
    %"iw_1.iw_1.v18" : P = Copy $"hello#str.58";
    call %"iw_1.iw_1.v20" : W = $"fputs"(P %"iw_1.iw_1.v18", P %"iw_1.v41");
    %"iw_1.iw_1.v21" : P = Copy $"hello#str.56";
    call %"iw_1.iw_1.v23" : W = $"fputs"(P %"iw_1.iw_1.v21", P %"iw_1.v41");
    %"iw_1.iw_1.v24" : P = Copy $"hello#str.59";
    call %"iw_1.iw_1.v26" : W = $"fputs"(P %"iw_1.iw_1.v24", P %"iw_1.v41");
    %"iw_1.iw_1.v27" : P = Copy $"hello#str.60";
    call %"iw_1.iw_1.v29" : W = $"fputs"(P %"iw_1.iw_1.v27", P %"iw_1.v41");
    call void $"emit_bug_reporting_address"();
    %"iw_1.iw_1.v34" : L = Ptoi %"iw_1.iw_1.v3";
    %"iw_1.iw_1.v35" : W = (Cmp Ne L) %"iw_1.iw_1.v34", #0
    => br %"iw_1.iw_1.v35" ? "iw_1.iw_1.L36" : "iw_1.iw_1.L37";
  @"iw_1.iw_1.L36":
    %"iw_1.iw_1.v39" : P = Copy $"hello#str.61";
    call %"iw_1.iw_1.v41" : W = $"strncmp"(P %"iw_1.iw_1.v3", P %"iw_1.iw_1.v39", L #3);
    %"iw_1.iw_1.v42" : W = (Cmp Ne W) %"iw_1.iw_1.v41", #0
    => goto "iw_1.iw_1.L37";
  @"iw_1.iw_1.L37" [%"iw_1.iw_1.v43" : W = phi("iw_1.L39" => #0, "iw_1.iw_1.L36" => %"iw_1.iw_1.v42")]:
    => br %"iw_1.iw_1.v43" ? "iw_1.iw_1.L30" : "iw_1.iw_1.L32";
  @"iw_1.iw_1.L30":
    %"iw_1.iw_1.v45" : P = Copy $"hello#str.62";
    %"iw_1.iw_1.v46" : P = Copy $"hello#str.63";
    call %"iw_1.iw_1.v47" : W = $"fprintf"(P %"iw_1.v41", P %"iw_1.iw_1.v45", P %"iw_1.iw_1.v46")
    => goto "iw_1.iw_1.L32";
  @"iw_1.iw_1.L32":
    %"iw_1.iw_1.v52" : P = Copy $"stderr";
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v52";
    %"iw_1.iw_1.v53" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.iw_1.v54" : L = Ptoi %"iw_1.v41";
    %"iw_1.iw_1.v55" : L = Ptoi %"iw_1.iw_1.v53";
    %"iw_1.iw_1.v56" : W = (Cmp Eq L) %"iw_1.iw_1.v54", %"iw_1.iw_1.v55"
    => br %"iw_1.iw_1.v56" ? "iw_1.iw_1.L50" : "iw_1.iw_1.L49";
  @"iw_1.iw_1.L49":
    => goto "iw_1.iw_1.L50";
  @"iw_1.iw_1.L50" [%"iw_1.iw_1.v57" : W = phi("iw_1.iw_1.L49" => #0, "iw_1.iw_1.L32" => #1)]:
    call void $"exit"(W %"iw_1.iw_1.v57")
    => goto "iw_1.L42";
  @"iw_1.L42":
    %"iw_1.v44" : P = Copy $"hello#str.76";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk1", %"v4";
    store.ptr [%"chk8" + 0] <- %"iw_1.v44"
    => goto poll "iw_1.L8";
  @"iw_1.L19":
    %"iw_1.v47" : W = (Cmp Eq W) %"iw_1.v15", #129
    => br %"iw_1.v47" ? poll "iw_1.L21" : "iw_1.L48";
  @"iw_1.L48":
    %"iw_1.v49" : W = (Cmp Eq W) %"iw_1.v15", #103
    => br %"iw_1.v49" ? poll "iw_1.L35" : "iw_1.L50";
  @"iw_1.L50":
    %"iw_1.v51" : W = (Cmp Eq W) %"iw_1.v15", #128
    => br %"iw_1.v51" ? poll "iw_1.L39" : "iw_1.L52";
  @"iw_1.L52":
    %"iw_1.v53" : W = (Cmp Eq W) %"iw_1.v15", #116
    => br %"iw_1.v53" ? poll "iw_1.L42" : poll "iw_1.L8";
  @"iw_1.L10":
    => br %"iw_1.pr.2" ? "iw_1.L60" : "iw_1.L59";
  @"iw_1.L59":
    %"iw_1.v61" : P = Copy $"optind";
    %"chk9" : A = (Check 0 4 Read 1) %"iw_1.v61";
    %"iw_1.v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"iw_1.v64" : W = (Cmp Slt W) %"iw_1.v62", %"v0"
    => goto "iw_1.L60";
  @"iw_1.L60" [%"iw_1.v66" : W = phi("iw_1.L10" => #1, "iw_1.L59" => %"iw_1.v64")]:
    => br %"iw_1.v66" ? "iw_1.L55" : "iw_1.join";
  @"iw_1.L55":
    %"iw_1.v71" : P = Copy $"optind";
    %"chk10" : A = (Check 0 4 Read 1) %"iw_1.v71";
    %"iw_1.v72" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"iw_1.v73" : L = (Ext Sw) %"iw_1.v72";
    %"iw_1.v74" : L = Shl %"iw_1.v73", #3;
    %"iw_1.v75" = %"v2" +p %"iw_1.v74";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v75";
    %"iw_1.v76" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v77" : L = Ptoi %"iw_1.v76";
    %"iw_1.v78" : W = (Cmp Ne L) %"iw_1.v77", #0
    => br %"iw_1.v78" ? "iw_1.L79" : "iw_1.L113";
  @"iw_1.L79":
    %"iw_1.v82" : P = Copy $"hello#str.77";
    %"iw_1.v83" : P = Copy $"hello#str.78";
    %"iw_1.v85" : P = Copy $"optind";
    %"chk12" : A = (Check 0 4 Read 1) %"iw_1.v85";
    %"iw_1.v86" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"iw_1.v87" : L = (Ext Sw) %"iw_1.v86";
    %"iw_1.v88" : L = Shl %"iw_1.v87", #3;
    %"iw_1.v89" = %"v2" +p %"iw_1.v88";
    %"chk13" : A = (Check 0 8 Read 8) %"iw_1.v89";
    %"iw_1.v90" : P = (RawLoadPointer 0 load_effects) %"chk13";
    call void $"error"(W #0, W #0, P %"iw_1.v82", P %"iw_1.v83", P %"iw_1.v90")
    => goto "iw_1.L113";
  @"iw_1.L113":
    %"iw_1.v116" : P = Copy $"stderr";
    %"chk14" : A = (Check 0 8 Read 8) %"iw_1.v116";
    %"iw_1.v117" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"iw_1.v118" : P = Copy $"hello#str.79";
    %"iw_1.v119" : P = Copy $"program_name";
    %"chk15" : A = (Check 0 8 Read 8) %"iw_1.v119";
    %"iw_1.v120" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call %"iw_1.v121" : W = $"fprintf"(P %"iw_1.v117", P %"iw_1.v118", P %"iw_1.v120");
    call void $"exit"(W #1)
    => goto "iw_1.join";
  @"iw_1.join":
    %"chk16" : A = (Renew 0 8 Read 8) %"chk1", %"v4";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk16";
    call %"v19" : L = $"strlen"(P %"v18");
    %"v20" : L = Add %"v19", #1;
    %"v22" : L = Shl %"v20", #2;
    call %"v23" : P = $"xmalloc"(L %"v22");
    call %"v26" : L = $"rpl_mbsrtowcs"(P %"v23", P %"v4", L %"v20", P %"v6");
    %"v33" : W = (Cmp Eq L) %"v26", #18446744073709551615
    => br %"v33" ? "L34" : "L29";
  @"L34":
    call %"v37" : P = $"__errno_location"();
    %"chk17" : A = (Check 0 4 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v39" : P = Copy $"hello#str.82";
    call void $"error"(W #1, W %"v38", P %"v39")
    => unreachable;
  @"L29":
    %"v56" : P = Copy $"hello#str.83";
    call %"v58" : W = $"wprintf"(P %"v56", P %"v23");
    call void $"free"(P %"v23");
    call void $"exit"(W #0)
    => ret #0
} }.

Definition hello_image_fn_glibc_malloc'23malloc_printerr : func :=
  ir_fn{ "local" "glibc_malloc#malloc_printerr"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_malloc#str.407";
    %"v3" : P = Copy $"glibc_malloc#str.408";
    call void $"__libc_message_impl"(P %"v2", P %"v3", P %"v0")
    => unreachable
} }.

Definition hello_image_fn_glibc_tsearch'23maybe_split_for_insert : func :=
  ir_fn{ "local" "glibc_tsearch#maybe_split_for_insert"(P %"v0", P %"v2", P %"v4", W %"v6", W %"v8", W %"v10") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v20" = %"v14" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v20";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" = %"v14" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v25";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v33" : W = (Cmp Eq W) %"v10", #1
    => br %"v33" ? "L35" : "L34";
  @"L34":
    %"v37" : L = Ptoi %"v23";
    %"v38" : L = Ptoi #0;
    %"v39" : W = (Cmp Ne L) %"v37", %"v38"
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v43" : L = Ptoi %"v28";
    %"v45" : W = (Cmp Ne L) %"v43", %"v38"
    => goto "L41";
  @"L41" [%"v47" : W = phi("L34" => #0, "L40" => %"v45")]:
    => br %"v47" ? "L48" : "L49";
  @"L48":
    %"v51" = %"v23" +p #24;
    %"chk3" : A = (Check 0 4 Read 1) %"v51";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v53" : W = Shl %"v52", #31;
    %"v54" : W = Shr %"v53", #31;
    %"v55" : W = (Cmp Ne W) %"v54", #0
    => goto "L49";
  @"L49" [%"v56" : W = phi("L41" => #0, "L48" => %"v55")]:
    => br %"v56" ? "L57" : "L35";
  @"L57":
    %"v60" = %"v28" +p #24;
    %"chk4" : A = (Check 0 4 Read 1) %"v60";
    %"v61" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v62" : W = Shl %"v61", #31;
    %"v63" : W = Shr %"v62", #31;
    %"v64" : W = (Cmp Ne W) %"v63", #0
    => goto "L35";
  @"L35" [%"v67" : W = phi("start" => #1, "L49" => #0, "L57" => %"v64")]:
    => br %"v67" ? "L29" : "L31";
  @"L29":
    %"v69" = %"v14" +p #24;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"v69";
    %"v70" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v71" : W = And %"v70", #4294967294;
    %"v73" : W = Or %"v71", #1;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v69";
    store Ww [%"chk6" + 0] <- %"v73";
    %"v80" : L = Ptoi %"v23";
    %"v81" : W = (Cmp Ne L) %"v80", #0
    => br %"v81" ? "L76" : "L78";
  @"L76":
    %"v83" = %"v23" +p #24;
    %"chk7" : A = (Check 0 4 Read 1) %"v83";
    %"v84" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v85" : W = And %"v84", #4294967294;
    %"chk8" : A = (Renew 0 4 Write 1) %"chk7", %"v83";
    store Ww [%"chk8" + 0] <- %"v85"
    => goto "L78";
  @"L78":
    %"v94" : L = Ptoi %"v28";
    %"v95" : W = (Cmp Ne L) %"v94", #0
    => br %"v95" ? "L90" : "L92";
  @"L90":
    %"v97" = %"v28" +p #24;
    %"chk9" : A = (Check 0 4 Read 1) %"v97";
    %"v98" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"v99" : W = And %"v98", #4294967294;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"v97";
    store Ww [%"chk10" + 0] <- %"v99"
    => goto "L92";
  @"L92":
    %"v108" : L = Ptoi %"v2";
    %"v109" : L = Ptoi #0;
    %"v110" : W = (Cmp Ne L) %"v108", %"v109"
    => br %"v110" ? "L111" : "L112";
  @"L111":
    %"chk11" : A = (Check 0 8 Read 8) %"v2";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v115" = %"v114" +p #24;
    %"chk12" : A = (Check 0 4 Read 1) %"v115";
    %"v116" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"v117" : W = Shl %"v116", #31;
    %"v118" : W = Shr %"v117", #31;
    %"v119" : W = (Cmp Ne W) %"v118", #0
    => goto "L112";
  @"L112" [%"v120" : W = phi("L92" => #0, "L111" => %"v119")]:
    => br %"v120" ? "L104" : "L31";
  @"L104":
    %"chk13" : A = (Check 0 8 Read 8) %"v4";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Read 8) %"v2";
    %"v126" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v131" : W = (Cmp Sgt W) %"v6", #0;
    %"v133" : W = (Cmp Sgt W) %"v8", #0;
    %"v134" : W = (Cmp Ne W) %"v131", %"v133"
    => br %"v134" ? "L127" : "L128";
  @"L127":
    %"v136" = %"v126" +p #24;
    %"chk15" : A = (Check 0 4 Read 1) %"v136";
    %"v137" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"v138" : W = And %"v137", #4294967294;
    %"v140" : W = Or %"v138", #1;
    %"chk16" : A = (Renew 0 4 Write 1) %"chk15", %"v136";
    store Ww [%"chk16" + 0] <- %"v140";
    %"v144" = %"v123" +p #24;
    %"chk17" : A = (Check 0 4 Read 1) %"v144";
    %"v145" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v146" : W = And %"v145", #4294967294;
    %"v148" : W = Or %"v146", #1;
    %"chk18" : A = (Renew 0 4 Write 1) %"chk17", %"v144";
    store Ww [%"chk18" + 0] <- %"v148";
    %"v152" = %"v14" +p #24;
    %"v153" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v154" : W = And %"v153", #4294967294;
    store Ww [%"chk6" + 0] <- %"v154";
    %"v163" : W = (Cmp Slt W) %"v6", #0
    => br %"v163" ? "L159" : "L160";
  @"L159":
    %"v165" = %"v126" +p #8;
    %"chk21" : A = (HalfCheck Lower 0 8 Write 8) %"chk15", %"v165";
    store.ptr [%"chk21" + 0] <- %"v23";
    %"chk22" : A = (Renew 0 8 Write 8) %"chk1", %"v20";
    store.ptr [%"chk22" + 0] <- %"v126";
    %"v170" = %"v123" +p #16;
    %"chk23" : A = (HalfCheck Lower 0 8 Write 8) %"chk17", %"v170";
    store.ptr [%"chk23" + 0] <- %"v28";
    %"chk24" : A = (Renew 0 8 Write 8) %"chk2", %"v25";
    store.ptr [%"chk24" + 0] <- %"v123"
    => goto "L161";
  @"L160":
    %"v175" = %"v126" +p #16;
    %"chk25" : A = (HalfCheck Lower 0 8 Write 8) %"chk15", %"v175";
    store.ptr [%"chk25" + 0] <- %"v28";
    %"chk26" : A = (Renew 0 8 Write 8) %"chk2", %"v25";
    store.ptr [%"chk26" + 0] <- %"v126";
    %"v180" = %"v123" +p #8;
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk17", %"v180";
    store.ptr [%"chk27" + 0] <- %"v23";
    %"chk28" : A = (Renew 0 8 Write 8) %"chk1", %"v20";
    store.ptr [%"chk28" + 0] <- %"v123"
    => goto "L161";
  @"L161":
    %"chk29" : A = (Renew 0 8 Write 8) %"chk13", %"v4";
    store.ptr [%"chk29" + 0] <- %"v14"
    => goto "L31";
  @"L128":
    %"chk30" : A = (Renew 0 8 Write 8) %"chk13", %"v4";
    store.ptr [%"chk30" + 0] <- %"v126";
    %"v189" = %"v126" +p #24;
    %"chk31" : A = (Check 0 4 Read 1) %"v189";
    %"v190" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v191" : W = And %"v190", #4294967294;
    %"chk32" : A = (Renew 0 4 Write 1) %"chk31", %"v189";
    store Ww [%"chk32" + 0] <- %"v191";
    %"v197" = %"v123" +p #24;
    %"chk33" : A = (Check 0 4 Read 1) %"v197";
    %"v198" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v199" : W = And %"v198", #4294967294;
    %"v201" : W = Or %"v199", #1;
    %"chk34" : A = (Renew 0 4 Write 1) %"chk33", %"v197";
    store Ww [%"chk34" + 0] <- %"v201";
    %"v208" : W = (Cmp Slt W) %"v6", #0
    => br %"v208" ? "L204" : "L205";
  @"L204":
    %"v210" = %"v123" +p #8;
    %"v212" = %"v126" +p #16;
    %"chk35" : A = (HalfCheck Lower 0 8 Read 8) %"chk31", %"v212";
    %"v213" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (HalfCheck Lower 0 8 Write 8) %"chk33", %"v210";
    store.ptr [%"chk36" + 0] <- %"v213";
    %"chk37" : A = (Renew 0 8 Write 8) %"chk35", %"v212";
    store.ptr [%"chk37" + 0] <- %"v123"
    => goto "L31";
  @"L205":
    %"v218" = %"v123" +p #16;
    %"v220" = %"v126" +p #8;
    %"chk38" : A = (HalfCheck Lower 0 8 Read 8) %"chk31", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (HalfCheck Lower 0 8 Write 8) %"chk33", %"v218";
    store.ptr [%"chk39" + 0] <- %"v221";
    %"chk40" : A = (Renew 0 8 Write 8) %"chk38", %"v220";
    store.ptr [%"chk40" + 0] <- %"v123"
    => goto "L31";
  @"L31":
    => ret void
} }.

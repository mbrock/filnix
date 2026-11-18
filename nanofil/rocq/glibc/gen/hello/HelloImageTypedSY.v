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

Definition hello_image_fn___GI___sysconf : func :=
  ir_fn{ "export" "__GI___sysconf"(W %"v0") -> (RClass L) {
  @"start":
    %"v6" : W = (Cmp Sge W) %"v0", #185
    => br %"v6" ? "L7" : "L8";
  @"L7":
    %"v10" : W = (Cmp Sle W) %"v0", #199
    => goto "L8";
  @"L8" [%"v12" : W = phi("start" => #0, "L7" => %"v10")]:
    => br %"v12" ? "L2" : "iw_1.start";
  @"L2":
    call %"v14" : L = $"__cache_sysconf"(W %"v0")
    => ret %"v14";
  @"iw_1.start":
    %"iw_1.v10" : P = (Alloc 8) #16;
    %"iw_1.v43" : P = (Alloc 8) #16;
    %"iw_1.v104" : P = (Alloc 4) #32;
    %"iw_1.v132" : P = (Alloc 8) #8;
    %"iw_1.v68" : W = (Cmp Slt W) %"v0", #139
    => br %"iw_1.v68" ? "iw_1.L69" : "iw_1.L70";
  @"iw_1.L9":
    call %"iw_1.v14" : W = $"__GI___getrlimit"(W #3, P %"iw_1.v10");
    %"iw_1.v15" : W = (Cmp Eq W) %"iw_1.v14", #0
    => br %"iw_1.v15" ? "iw_1.L11" : "iw_1.join";
  @"iw_1.L11":
    %"chk0" : A = (Check 0 8 Read 1) %"iw_1.v10";
    %"iw_1.v20" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v21" : L = Shr %"iw_1.v20", #2;
    %"iw_1.v22" : W = (Cmp Ult L) %"iw_1.v21", #131072
    => br %"iw_1.v22" ? "iw_1.L19" : "iw_1.L18";
  @"iw_1.L18":
    %"iw_1.v23" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v24" : L = Shr %"iw_1.v23", #2
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.v25" : L = phi("iw_1.L18" => %"iw_1.v24", "iw_1.L11" => #131072)]:
    %"iw_1.v33" : W = (Cmp Slt L) %"iw_1.v25", #6291456
    => br %"iw_1.v33" ? "iw_1.join" : "iw_1.L27";
  @"iw_1.L27":
    => goto "iw_1.join";
  @"iw_1.L40":
    %"iw_1.v41" : P = Copy $"glibc_sysconf#str.305"
    => goto "iw_1.L5";
  @"iw_1.L42":
    call %"iw_1.v47" : W = $"__GI___getrlimit"(W #11, P %"iw_1.v43");
    %"iw_1.v48" : W = (Cmp Eq W) %"iw_1.v47", #0
    => br %"iw_1.v48" ? "iw_1.L44" : "iw_1.L46";
  @"iw_1.L44":
    %"chk2" : A = (Check 0 8 Read 1) %"iw_1.v43";
    %"iw_1.v49" : L = (RawLoad LdL 0) %"chk2"
    => goto "iw_1.join";
  @"iw_1.L46":
    %"iw_1.v51" : P = Copy $"glibc_sysconf#str.306"
    => goto "iw_1.L5";
  @"iw_1.L52":
    %"iw_1.v56" : P = Copy $"_dl_minsigstacksize";
    %"chk3" : A = (Check 0 8 Read 1) %"iw_1.v56";
    %"iw_1.v57" : L = (RawLoad LdL 0) %"chk3";
    %"iw_1.v58" : W = (Cmp Ne L) %"iw_1.v57", #0
    => br %"iw_1.v58" ? "iw_1.L55" : "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v59" : P = Copy $"glibc_sysconf#str.307";
    %"iw_1.v60" : P = Copy $"glibc_sysconf#str.308";
    %"iw_1.v61" : P = Copy $"glibc_sysconf#str.309";
    call void $"__libc_assert_fail"(P %"iw_1.v59", P %"iw_1.v60", W #87, P %"iw_1.v61")
    => goto "iw_1.L55";
  @"iw_1.L55":
    %"iw_1.v62" : P = Copy $"_dl_minsigstacksize";
    %"chk4" : A = (Check 0 8 Read 1) %"iw_1.v62";
    %"iw_1.v63" : L = (RawLoad LdL 0) %"chk4"
    => goto "iw_1.join";
  @"iw_1.iw_1.start":
    %"iw_1.iw_1.v1" : P = Copy $"_dl_minsigstacksize";
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.iw_1.v1";
    %"iw_1.iw_1.v2" : L = (RawLoad LdL 0) %"chk5";
    %"iw_1.iw_1.v7" : W = (Cmp Ne L) %"iw_1.iw_1.v2", #0
    => br %"iw_1.iw_1.v7" ? "iw_1.iw_1.L5" : "iw_1.iw_1.L4";
  @"iw_1.iw_1.L4":
    %"iw_1.iw_1.v8" : P = Copy $"glibc_sysconf#str.302";
    %"iw_1.iw_1.v9" : P = Copy $"glibc_sysconf#str.303";
    %"iw_1.iw_1.v10" : P = Copy $"glibc_sysconf#str.304";
    call void $"__libc_assert_fail"(P %"iw_1.iw_1.v8", P %"iw_1.iw_1.v9", W #25, P %"iw_1.iw_1.v10")
    => goto "iw_1.iw_1.L5";
  @"iw_1.iw_1.L5":
    %"iw_1.iw_1.v15" : W = (Cmp Slt L) %"iw_1.iw_1.v2", #2048
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L13" : "iw_1.iw_1.L12";
  @"iw_1.iw_1.L12":
    => goto "iw_1.iw_1.L13";
  @"iw_1.iw_1.L13" [%"iw_1.iw_1.pr.1" : L = phi("iw_1.iw_1.L12" => %"iw_1.iw_1.v2", "iw_1.iw_1.L5" => #2048)]:
    %"iw_1.iw_1.v18" : L = Shl %"iw_1.iw_1.pr.1", #2;
    %"iw_1.iw_1.v23" : W = (Cmp Slt L) %"iw_1.iw_1.v18", #8192
    => br %"iw_1.iw_1.v23" ? "iw_1.join" : "iw_1.iw_1.L20";
  @"iw_1.iw_1.L20":
    => goto "iw_1.join";
  @"iw_1.L69":
    %"iw_1.v71" : W = (Cmp Eq W) %"v0", #0
    => br %"iw_1.v71" ? poll "iw_1.L9" : "iw_1.L72";
  @"iw_1.L72":
    %"iw_1.v73" : W = (Cmp Eq W) %"v0", #3
    => br %"iw_1.v73" ? poll "iw_1.L40" : "iw_1.L74";
  @"iw_1.L74":
    %"iw_1.v75" : W = (Cmp Eq W) %"v0", #34
    => br %"iw_1.v75" ? poll "iw_1.L42" : "iw_1.L76";
  @"iw_1.L76":
    %"iw_1.v77" : W = (Cmp Eq W) %"v0", #138
    => br %"iw_1.v77" ? "iw_1.join" : "iw_1.L5";
  @"iw_1.L70":
    %"iw_1.v79" : W = (Cmp Eq W) %"v0", #139
    => br %"iw_1.v79" ? "iw_1.join" : "iw_1.L80";
  @"iw_1.L80":
    %"iw_1.v81" : W = (Cmp Eq W) %"v0", #149
    => br %"iw_1.v81" ? "iw_1.join" : "iw_1.L82";
  @"iw_1.L82":
    %"iw_1.v83" : W = (Cmp Eq W) %"v0", #249
    => br %"iw_1.v83" ? poll "iw_1.L52" : "iw_1.L84";
  @"iw_1.L84":
    %"iw_1.v85" : W = (Cmp Eq W) %"v0", #250
    => br %"iw_1.v85" ? poll "iw_1.iw_1.start" : "iw_1.L5";
  @"iw_1.L5" [%"iw_1.pr.1" : P = phi("iw_1.L40" => %"iw_1.v41", "iw_1.L46" => %"iw_1.v51", "iw_1.L76" => #0, "iw_1.L84" => #0)]:
    %"iw_1.v91" : L = Ptoi %"iw_1.pr.1";
    %"iw_1.v92" : L = Ptoi #0;
    %"iw_1.v93" : W = (Cmp Ne L) %"iw_1.v91", %"iw_1.v92"
    => br %"iw_1.v93" ? "iw_1.L87" : "iw_1.L89";
  @"iw_1.L87":
    call %"iw_1.v97" : W = $"__GI___open_nocancel"(P %"iw_1.pr.1", W #524288);
    %"iw_1.v103" : W = (Cmp Ne W) %"iw_1.v97", #4294967295
    => br %"iw_1.v103" ? "iw_1.L107" : "iw_1.L89";
  @"iw_1.L107":
    call %"iw_1.v112" : L = $"__GI___read_nocancel"(W %"iw_1.v97", P %"iw_1.v104", L #31);
    %"iw_1.v115" : W = (Cmp Eq L) %"iw_1.v112", #18446744073709551615
    => br %"iw_1.v115" ? "iw_1.L116" : "iw_1.L117";
  @"iw_1.L116":
    %"iw_1.v118" : P = Copy $"__libc_errno";
    %"chk6" : A = (Check 0 4 Read 1) %"iw_1.v118";
    %"iw_1.v119" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"iw_1.v120" : W = (Cmp Eq W) %"iw_1.v119", #4
    => goto "iw_1.L117";
  @"iw_1.L117" [%"iw_1.v122" : W = phi("iw_1.L107" => #0, "iw_1.L116" => %"iw_1.v120")]:
    => br %"iw_1.v122" ? poll "iw_1.L107" : "iw_1.L109";
  @"iw_1.L109":
    call void $"__GI___close_nocancel_nostatus"(W %"iw_1.v97");
    %"iw_1.v129" : W = (Cmp Sgt L) %"iw_1.v112", #0
    => br %"iw_1.v129" ? "iw_1.L125" : "iw_1.L89";
  @"iw_1.L125":
    %"iw_1.v131" = %"iw_1.v104" +p %"iw_1.v112";
    %"chk7" : A = (Check 0 1 Write 1) %"iw_1.v131";
    store Wb [%"chk7" + 0] <- #0;
    call %"iw_1.v134" : L = $"__GI___isoc23_strtol"(P %"iw_1.v104", P %"iw_1.v132", W #10);
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v132";
    %"iw_1.v138" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v139" : L = Ptoi %"iw_1.v138";
    %"iw_1.v140" : L = Ptoi %"iw_1.v104";
    %"iw_1.v141" : W = (Cmp Ne L) %"iw_1.v139", %"iw_1.v140"
    => br %"iw_1.v141" ? "iw_1.L142" : "iw_1.L143";
  @"iw_1.L142":
    %"iw_1.v144" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk10" : A = (Check 0 1 Read 1) %"iw_1.v144";
    %"iw_1.v145" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"iw_1.v146" : W = (Cmp Eq W) %"iw_1.v145", #0
    => br %"iw_1.v146" ? "iw_1.L143" : "iw_1.L147";
  @"iw_1.L147":
    %"iw_1.v149" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk12" : A = (Check 0 1 Read 1) %"iw_1.v149";
    %"iw_1.v150" : W = (RawLoad (LdNarrow Sb) 0) %"chk12";
    %"iw_1.v151" : W = (Cmp Eq W) %"iw_1.v150", #10
    => goto "iw_1.L143";
  @"iw_1.L143" [%"iw_1.v155" : W = phi("iw_1.L125" => #0, "iw_1.L142" => #1, "iw_1.L147" => %"iw_1.v151")]:
    => br %"iw_1.v155" ? "iw_1.join" : "iw_1.L89";
  @"iw_1.L89":
    call %"iw_1.v159" : L = $"glibc_sysconf#posix_sysconf"(W %"v0")
    => goto "iw_1.join";
  @"iw_1.join" [%"v17" : L = phi("iw_1.L44" => %"iw_1.v49", "iw_1.L55" => %"iw_1.v63", "iw_1.L89" => %"iw_1.v159", "iw_1.L76" => #200809, "iw_1.L70" => #200809, "iw_1.L80" => #200809, "iw_1.L19" => %"iw_1.v25", "iw_1.L27" => #6291456, "iw_1.L9" => #131072, "iw_1.iw_1.L13" => #8192, "iw_1.iw_1.L20" => %"iw_1.iw_1.v18", "iw_1.L143" => %"iw_1.v134")]:
    => ret %"v17"
} }.

Definition hello_image_fn_glibc_sysconf'23__sysconf_check_spec : func :=
  ir_fn{ "local" "glibc_sysconf#__sysconf_check_spec"(P %"v0") -> (RClass L) {
  @"start":
    %"v36" : P = (Alloc 8) #144;
    %"v3" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v6" : P = Copy $"glibc_sysconf#str.350";
    call %"v7" : P = $"__GI___libc_secure_getenv"(P %"v6");
    %"v8" : L = Ptoi %"v7";
    %"v9" : W = (Cmp Ne L) %"v8", #0
    => br %"v9" ? "L12" : "L11";
  @"L11":
    %"v13" : P = Copy $"glibc_sysconf#str.351"
    => goto "L12";
  @"L12" [%"v14" : P = phi("L11" => %"v13", "start" => %"v7")]:
    call %"v17" : L = $"__GI_strlen"(P %"v14");
    call %"v20" : L = $"__GI_strlen"(P %"v0");
    %"v22" : L = Add %"v17", #11;
    %"v24" : L = Add %"v22", %"v20";
    %"v25" : P = (Alloc 4) %"v24";
    call %"v28" : P = $"__GI_mempcpy"(P %"v25", P %"v14", L %"v17");
    %"v29" : P = Copy $"glibc_sysconf#str.353";
    call %"v31" : P = $"__GI_mempcpy"(P %"v28", P %"v29", L #10);
    %"v34" : L = Add %"v20", #1;
    call %"v35" : P = $"__GI_memcpy"(P %"v31", P %"v0", L %"v34");
    call %"v41" : W = $"__GI___stat64"(P %"v25", P %"v36");
    %"v42" : W = (Cmp Sge W) %"v41", #0
    => br %"v42" ? "L40" : "L39";
  @"L39":
    => goto "L40";
  @"L40" [%"v44" : W = phi("L39" => #4294967295, "L12" => #1)]:
    %"v45" : L = (Ext Sw) %"v44";
    %"v46" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"v46";
    store Ww [%"chk1" + 0] <- %"v4"
    => ret %"v45"
} }.

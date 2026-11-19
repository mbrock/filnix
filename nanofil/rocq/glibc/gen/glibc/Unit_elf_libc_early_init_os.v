(** This file defines checked IR from glibc’s `elf/libc_early_init.os` object.
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

Definition fn___libc_early_init : func :=
  ir_fn{ "export" "__libc_early_init"(W %"v0") -> RVoid {
  @"start":
    call void $"__GI___ctype_init"();
    %"v2" : P = Copy $"__libc_single_threaded";
    %"v3" : W = (Ext Ub) %"v0";
    %"v4" : W = (Ext Sb) %"v3";
    %"chk0" : A = (Check 0 1 Write 1) %"v2";
    store Wb [%"chk0" + 0] <- %"v4";
    %"v5" : P = Copy $"__libc_single_threaded_internal";
    %"v6" : P = Copy $"__libc_initial";
    %"chk1" : A = (Check 0 1 Write 1) %"v6";
    store Wb [%"chk1" + 0] <- %"v3";
    %"chk2" : A = (Check 0 1 Write 1) %"v5";
    store Wb [%"chk2" + 0] <- %"v4";
    %"iw_1.v0" : P = (Alloc 8) #16;
    call %"iw_1.v4" : W = $"__GI___getrlimit"(W #3, P %"iw_1.v0");
    %"iw_1.v5" : W = (Cmp Ne W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "iw_1.L7" : "iw_1.L6";
  @"iw_1.L6":
    %"chk3" : A = (Check 0 8 Read 1) %"iw_1.v0";
    %"iw_1.v8" : L = (RawLoad LdL 0) %"chk3";
    %"iw_1.v11" : W = (Cmp Eq L) %"iw_1.v8", #18446744073709551615
    => goto "iw_1.L7";
  @"iw_1.L7" [%"iw_1.v13" : W = phi("start" => #1, "iw_1.L6" => %"iw_1.v11")]:
    => br %"iw_1.v13" ? "iw_1.L1" : "iw_1.L2";
  @"iw_1.L1":
    %"chk4" : A = (Check 0 8 Write 1) %"iw_1.v0";
    store Wl [%"chk4" + 0] <- #2097152
    => goto "iw_1.L3";
  @"iw_1.L2":
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.v0";
    %"iw_1.v20" : L = (RawLoad LdL 0) %"chk5";
    %"iw_1.v21" : W = (Cmp Ult L) %"iw_1.v20", #16384
    => br %"iw_1.v21" ? "iw_1.L17" : "iw_1.L3";
  @"iw_1.L17":
    %"chk6" : A = (Renew 0 8 Write 1) %"chk5", %"iw_1.v0";
    store Wl [%"chk6" + 0] <- #16384
    => goto "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v23" : P = Copy $"_dl_pagesize";
    %"chk7" : A = (Check 0 8 Read 1) %"iw_1.v23";
    %"iw_1.v24" : L = (RawLoad LdL 0) %"chk7";
    %"iw_1.v29" : L = Add %"iw_1.v24", #2048;
    %"chk8" : A = (Check 0 8 Read 1) %"iw_1.v0";
    %"iw_1.v33" : L = (RawLoad LdL 0) %"chk8";
    %"iw_1.v35" : W = (Cmp Ult L) %"iw_1.v33", %"iw_1.v29"
    => br %"iw_1.v35" ? "iw_1.L30" : "iw_1.L32";
  @"iw_1.L30":
    %"chk9" : A = (Renew 0 8 Write 1) %"chk8", %"iw_1.v0";
    store Wl [%"chk9" + 0] <- %"iw_1.v29"
    => goto "iw_1.L32";
  @"iw_1.L32":
    %"iw_1.v37" : L = (RawLoad LdL 0) %"chk8";
    %"iw_1.v39" : L = Add %"iw_1.v37", %"iw_1.v24";
    %"iw_1.v40" : L = Sub %"iw_1.v39", #1;
    %"iw_1.v42" : L = Neg %"iw_1.v24";
    %"iw_1.v43" : L = And %"iw_1.v40", %"iw_1.v42";
    %"chk11" : A = (Renew 0 8 Write 1) %"chk8", %"iw_1.v0";
    store Wl [%"chk11" + 0] <- %"iw_1.v43";
    %"iw_1.v44" : P = Copy $"__GI___default_pthread_attr";
    %"iw_1.v45" = %"iw_1.v44" +p #32;
    %"chk12" : A = (Renew 0 8 Read 1) %"chk8", %"iw_1.v0";
    %"iw_1.v46" : L = (RawLoad LdL 0) %"chk12";
    %"chk13" : A = (Check 0 8 Write 1) %"iw_1.v45";
    store Wl [%"chk13" + 0] <- %"iw_1.v46";
    %"iw_1.v47" : P = Copy $"__GI___default_pthread_attr";
    %"iw_1.v48" = %"iw_1.v47" +p #16;
    %"iw_1.v49" : P = Copy $"_dl_pagesize";
    %"chk14" : A = (Check 0 8 Read 1) %"iw_1.v49";
    %"iw_1.v50" : L = (RawLoad LdL 0) %"chk14";
    %"chk15" : A = (Check 0 8 Write 1) %"iw_1.v48";
    store Wl [%"chk15" + 0] <- %"iw_1.v50";
    call void $"__pthread_tunables_init"();
    call void $"__getrandom_early_init"(W %"v3");
    call void $"__ptmalloc_init"()
    => ret void
} }.

Definition item___libc_initial : item :=
  (IData (a "__libc_initial") LExport 1 [(Zero 1)]).

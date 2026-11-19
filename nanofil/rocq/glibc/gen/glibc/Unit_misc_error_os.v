(** This file defines checked IR from glibc’s `misc/error.os` object.
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

Definition fn___error : func :=
  ir_fn{ "export" "__error"(W %"v0", W %"v2", P %"v4") -> RVoid {
  @"start":
    %"v6" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #24;
    %"chk0" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk0" + 0] <- %"va_args";
    call void $"__error_internal"(W %"v0", W %"v2", P %"v4", P %"v6", W #0)
    => ret void
} }.

Definition fn___error_internal : func :=
  ir_fn{ "export" "__error_internal"(W %"v0", W %"v2", P %"v4", P %"v6", W %"v8") -> RVoid {
  @"start":
    %"v10" : P = (Alloc 4) #4;
    %"chk0" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk0" + 0] <- #0;
    call %"v11" : W = $"__GI___pthread_setcancelstate"(W #1, P %"v10");
    %"iw_1.v0" : P = Copy $"stdout";
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"iw_1.v1" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"iw_1.v2" : W = $"__GI__IO_fflush"(P %"iw_1.v1");
    %"v15" : P = Copy $"error_print_progname";
    %"chk2" : A = (Check 0 8 Read 8) %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v17" : L = Ptoi %"v16";
    %"v18" : W = (Cmp Ne L) %"v17", #0
    => br %"v18" ? "L12" : "L13";
  @"L12":
    %"v19" : P = Copy $"error_print_progname";
    %"chk3" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v20";
    rawcall void %"chk4"()
    => goto "iw_2.start";
  @"L13":
    %"v21" : P = Copy $"glibc_error#str.255";
    %"v22" : P = Copy $"program_invocation_name";
    %"chk5" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v24" : W = $"__fxprintf"(P #0, P %"v21", P %"v23")
    => goto "iw_2.start";
  @"iw_2.start":
    %"iw_2.v11" : P = Copy $"stderr";
    %"chk6" : A = (Check 0 8 Read 8) %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"iw_2.v16" : W = $"__vfxprintf"(P %"iw_2.v12", P %"v4", P %"v6", W %"v8");
    %"iw_2.v21" : W = (Cmp Slt W) %"iw_2.v16", #0
    => br %"iw_2.v21" ? "iw_2.L22" : "iw_2.L23";
  @"iw_2.L22":
    %"iw_2.v24" : P = Copy $"__libc_errno";
    %"chk7" : A = (Check 0 4 Read 1) %"iw_2.v24";
    %"iw_2.v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"iw_2.v26" : W = (Cmp Eq W) %"iw_2.v25", #12
    => goto "iw_2.L23";
  @"iw_2.L23" [%"iw_2.v28" : W = phi("iw_2.start" => #0, "iw_2.L22" => %"iw_2.v26")]:
    => br %"iw_2.v28" ? "iw_2.L67" : "iw_2.L30";
  @"iw_2.L67":
    %"iw_2.v70" : P = Copy $"stderr";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_2.v70";
    %"iw_2.v71" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_2.v72" = %"iw_2.v71" +p #192;
    %"chk9" : A = (Check 0 4 Read 1) %"iw_2.v72";
    %"iw_2.v73" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"iw_2.v80" : W = (Cmp Sgt W) %"iw_2.v73", #0
    => goto "iw_2.L30";
  @"iw_2.L30" [%"iw_2.v82" : W = phi("iw_2.L23" => #0, "iw_2.L67" => %"iw_2.v80")]:
    => br %"iw_2.v82" ? "iw_2.L17" : "iw_2.L19";
  @"iw_2.L17":
    %"iw_2.v83" : P = Copy $"glibc_error#str.253";
    %"iw_2.v84" : P = Copy $"stderr";
    %"chk10" : A = (Check 0 8 Read 8) %"iw_2.v84";
    %"iw_2.v85" : P = (RawLoadPointer 0 load_effects) %"chk10";
    call %"iw_2.v86" : W = $"__GI_fputws_unlocked"(P %"iw_2.v83", P %"iw_2.v85")
    => goto "iw_2.L19";
  @"iw_2.L19":
    %"iw_2.v87" : P = Copy $"error_message_count";
    %"chk11" : A = (Check 0 4 Read 1) %"iw_2.v87";
    %"iw_2.v88" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"iw_2.v89" : W = Add %"iw_2.v88", #1;
    %"chk12" : A = (Renew 0 4 Write 1) %"chk11", %"iw_2.v87";
    store Ww [%"chk12" + 0] <- %"iw_2.v89"
    => br %"v2" ? "iw_2.iw_1.start" : "iw_2.L92";
  @"iw_2.iw_1.start":
    %"iw_2.iw_1.v3" : P = (Alloc 4) #1024;
    call %"iw_2.iw_1.v5" : P = $"__GI___strerror_r"(W %"v2", P %"iw_2.iw_1.v3", L #1024);
    %"iw_2.iw_1.v6" : P = Copy $"glibc_error#str.252";
    call %"iw_2.iw_1.v8" : W = $"__fxprintf"(P #0, P %"iw_2.iw_1.v6", P %"iw_2.iw_1.v5")
    => goto "iw_2.L92";
  @"iw_2.L92":
    %"iw_2.v95" : P = Copy $"glibc_error#str.254";
    call %"iw_2.v96" : W = $"__fxprintf"(P #0, P %"iw_2.v95");
    %"iw_2.v97" : P = Copy $"stderr";
    %"chk13" : A = (Check 0 8 Read 8) %"iw_2.v97";
    %"iw_2.v98" : P = (RawLoadPointer 0 load_effects) %"chk13";
    call %"iw_2.v99" : W = $"__GI__IO_fflush"(P %"iw_2.v98")
    => br %"v0" ? "iw_2.L100" : "iw_2.join";
  @"iw_2.L100":
    call void $"__GI_exit"(W %"v0")
    => goto "iw_2.join";
  @"iw_2.join":
    %"chk14" : A = (Renew 0 4 Read 1) %"chk0", %"v10";
    %"v30" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    call %"v31" : W = $"__GI___pthread_setcancelstate"(W %"v30", P #0)
    => ret void
} }.

Definition item_error : item :=
  (IAlias (a "error") (a "weak") (a "__error")).

Definition item_error_message_count : item :=
  (IData (a "error_message_count") LExport 4 [(Zero 4)]).

Definition item_error_print_progname : item :=
  (IData (a "error_print_progname") LExport 8 [(Zero 8)]).

Definition item_glibc_error'23str'2e252 : item :=
  (IData (a "glibc_error#str.252") (LRo (a "local")) 1 [(Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition item_glibc_error'23str'2e253 : item :=
  (IData (a "glibc_error#str.253") (LRo (a "local")) 4 [(Item Ww 111); (Item Ww 117); (Item Ww 116); (Item Ww 32); (Item Ww 111); (Item Ww 102); (Item Ww 32); (Item Ww 109); (Item Ww 101); (Item Ww 109); (Item Ww 111); (Item Ww 114); (Item Ww 121); (Item Ww 10); (Item Ww 0)]).

Definition item_glibc_error'23str'2e254 : item :=
  (IData (a "glibc_error#str.254") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition item_glibc_error'23str'2e255 : item :=
  (IData (a "glibc_error#str.255") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 0)]).

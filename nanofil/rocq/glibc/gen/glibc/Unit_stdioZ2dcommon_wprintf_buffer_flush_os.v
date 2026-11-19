(** This file defines checked IR from glibc’s `stdio-common/wprintf_buffer_flush.os` object.
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

Definition fn___wprintf_buffer_flush : func :=
  ir_fn{ "export" "__wprintf_buffer_flush"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "iw_2.start";
  @"L2":
    => ret #0;
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"iw_2.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_2.v21" : W = (Cmp Eq W) %"iw_2.v4", #0
    => br %"iw_2.v21" ? "iw_3.start" : "iw_2.L22";
  @"iw_2.L8":
    call void $"__wprintf_buffer_flush_to_file"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L10":
    %"iw_2.v12" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_2.v12";
    %"iw_2.v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_2.v17" = %"iw_2.v13" +p #18446744073709551612;
    %"chk3" : A = (Check 0 4 Write 1) %"iw_2.v17";
    store Ww [%"chk3" + 0] <- #0;
    %"iw_2.v18" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_2.v18";
    store Ww [%"chk4" + 0] <- #7;
    %"iw_2.iw_1.v3" = %"v0" +p #32;
    %"chk5" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk5" + 0] <- #0
    => goto "iw_3.start";
  @"iw_2.L22":
    %"iw_2.v23" : W = (Cmp Eq W) %"iw_2.v4", #2
    => br %"iw_2.v23" ? poll "iw_2.L8" : "iw_2.L24";
  @"iw_2.L24":
    %"iw_2.v25" : W = (Cmp Eq W) %"iw_2.v4", #1
    => br %"iw_2.v25" ? poll "iw_2.L10" : "iw_2.L6";
  @"iw_2.L6":
    => unreachable;
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk6" : A = (Renew 0 4 Read 1) %"chk0", %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L13" : "L15";
  @"L13":
    => ret #0;
  @"L15":
    %"v25" = %"v0" +p #8;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v28" = %"v0" +p #16;
    %"v29" : P = (RawLoadPointer 8 load_effects) %"chk7";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L22";
  @"L22":
    %"v33" : P = Copy $"glibc_wprintf_buffer_flush#str.39";
    %"v34" : P = Copy $"glibc_wprintf_buffer_flush#str.40";
    %"v35" : P = Copy $"glibc_wprintf_buffer_flush#str.41";
    call void $"__libc_assert_fail"(P %"v33", P %"v34", W #70, P %"v35")
    => goto "L23";
  @"L23":
    => ret #1
} }.

Definition item_glibc_wprintf_buffer_flush'23str'2e39 : item :=
  (IData (a "glibc_wprintf_buffer_flush#str.39") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_wprintf_buffer_flush'23str'2e40 : item :=
  (IData (a "glibc_wprintf_buffer_flush#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_wprintf_buffer_flush'23str'2e41 : item :=
  (IData (a "glibc_wprintf_buffer_flush#str.41") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 0)]).

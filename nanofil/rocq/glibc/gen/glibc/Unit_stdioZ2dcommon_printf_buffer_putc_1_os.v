(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_putc_1.os` object.
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

Definition fn___printf_buffer_putc_1 : func :=
  ir_fn{ "export" "__printf_buffer_putc_1"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L13" : "L12";
  @"L12":
    call %"v15" : W = $"__printf_buffer_flush"(P %"v0");
    %"v16" : W = (Ext Ub) %"v15";
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => goto "L13";
  @"L13" [%"v19" : W = phi("start" => #1, "L12" => %"v17")]:
    => br %"v19" ? "L4" : "L6";
  @"L4":
    => ret void;
  @"L6":
    %"v25" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v28" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ult L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L22";
  @"L22":
    %"v33" : P = Copy $"glibc_printf_buffer_putc_1#str.39";
    %"v34" : P = Copy $"glibc_printf_buffer_putc_1#str.40";
    %"v35" : P = Copy $"glibc_printf_buffer_putc_1#str.41";
    call void $"__libc_assert_fail"(P %"v33", P %"v34", W #27, P %"v35")
    => goto "L23";
  @"L23":
    %"v37" = %"v0" +p #8;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v39" = %"v38" +p #1;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk1", %"v37";
    store.ptr [%"chk4" + 0] <- %"v39";
    %"v40" : W = (Ext Sb) %"v2";
    %"chk5" : A = (Check 0 1 Write 1) %"v38";
    store Wb [%"chk5" + 0] <- %"v40"
    => ret void
} }.

Definition item_glibc_printf_buffer_putc_1'23str'2e39 : item :=
  (IData (a "glibc_printf_buffer_putc_1#str.39") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_printf_buffer_putc_1'23str'2e40 : item :=
  (IData (a "glibc_printf_buffer_putc_1#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 99); (Item Wb 95); (Item Wb 49); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_buffer_putc_1'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_putc_1#str.41") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 99); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

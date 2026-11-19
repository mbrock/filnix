(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_flush.os` object.
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

Definition fn___printf_buffer_flush : func :=
  ir_fn{ "export" "__printf_buffer_flush"(P %"v0") -> (RClass W) {
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
    %"iw_2.v30" : W = (Cmp Ult W) %"iw_2.v4", #6
    => br %"iw_2.v30" ? "iw_2.L31" : "iw_2.L32";
  @"iw_2.L9":
    call void $"__printf_buffer_flush_snprintf"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L11":
    call void $"__GI___chk_fail"()
    => goto "iw_2.L6";
  @"iw_2.L12":
    call void $"__printf_buffer_flush_to_file"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L14":
    call void $"__printf_buffer_flush_asprintf"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L16":
    call void $"__printf_buffer_flush_dprintf"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L18":
    %"iw_2.v19" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Write 1) %"iw_2.v19";
    store Ww [%"chk2" + 0] <- #7;
    %"iw_2.iw_1.v3" = %"v0" +p #32;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk3" + 0] <- #0
    => goto "iw_3.start";
  @"iw_2.L21":
    call void $"__printf_buffer_flush_fp"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L23":
    call void $"__printf_buffer_flush_fp_to_wide"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L25":
    call void $"__printf_buffer_flush_fphex_to_wide"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L27":
    call void $"__printf_buffer_flush_obstack"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L31":
    %"iw_2.v33" : W = (Cmp Ult W) %"iw_2.v4", #3
    => br %"iw_2.v33" ? "iw_2.L34" : "iw_2.L35";
  @"iw_2.L34":
    %"iw_2.v36" : W = (Cmp Eq W) %"iw_2.v4", #0
    => br %"iw_2.v36" ? "iw_3.start" : "iw_2.L37";
  @"iw_2.L37":
    %"iw_2.v38" : W = (Cmp Eq W) %"iw_2.v4", #1
    => br %"iw_2.v38" ? "iw_3.start" : "iw_2.L39";
  @"iw_2.L39":
    %"iw_2.v40" : W = (Cmp Eq W) %"iw_2.v4", #2
    => br %"iw_2.v40" ? poll "iw_2.L9" : "iw_2.L6";
  @"iw_2.L35":
    %"iw_2.v42" : W = (Cmp Eq W) %"iw_2.v4", #3
    => br %"iw_2.v42" ? poll "iw_2.L11" : "iw_2.L43";
  @"iw_2.L43":
    %"iw_2.v44" : W = (Cmp Eq W) %"iw_2.v4", #4
    => br %"iw_2.v44" ? poll "iw_2.L12" : "iw_2.L45";
  @"iw_2.L45":
    %"iw_2.v46" : W = (Cmp Eq W) %"iw_2.v4", #5
    => br %"iw_2.v46" ? poll "iw_2.L14" : "iw_2.L6";
  @"iw_2.L32":
    %"iw_2.v48" : W = (Cmp Ult W) %"iw_2.v4", #9
    => br %"iw_2.v48" ? "iw_2.L49" : "iw_2.L50";
  @"iw_2.L49":
    %"iw_2.v51" : W = (Cmp Eq W) %"iw_2.v4", #6
    => br %"iw_2.v51" ? poll "iw_2.L16" : "iw_2.L52";
  @"iw_2.L52":
    %"iw_2.v53" : W = (Cmp Eq W) %"iw_2.v4", #7
    => br %"iw_2.v53" ? poll "iw_2.L18" : "iw_2.L54";
  @"iw_2.L54":
    %"iw_2.v55" : W = (Cmp Eq W) %"iw_2.v4", #8
    => br %"iw_2.v55" ? poll "iw_2.L21" : "iw_2.L6";
  @"iw_2.L50":
    %"iw_2.v57" : W = (Cmp Eq W) %"iw_2.v4", #9
    => br %"iw_2.v57" ? poll "iw_2.L23" : "iw_2.L58";
  @"iw_2.L58":
    %"iw_2.v59" : W = (Cmp Eq W) %"iw_2.v4", #10
    => br %"iw_2.v59" ? poll "iw_2.L25" : "iw_2.L60";
  @"iw_2.L60":
    %"iw_2.v61" : W = (Cmp Eq W) %"iw_2.v4", #11
    => br %"iw_2.v61" ? poll "iw_2.L27" : "iw_2.L6";
  @"iw_2.L6":
    => unreachable;
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk0", %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L13" : "L15";
  @"L13":
    => ret #0;
  @"L15":
    %"v25" = %"v0" +p #8;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v28" = %"v0" +p #16;
    %"v29" : P = (RawLoadPointer 8 load_effects) %"chk5";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L22";
  @"L22":
    %"v33" : P = Copy $"glibc_printf_buffer_flush#str.39";
    %"v34" : P = Copy $"glibc_printf_buffer_flush#str.40";
    %"v35" : P = Copy $"glibc_printf_buffer_flush#str.41";
    call void $"__libc_assert_fail"(P %"v33", P %"v34", W #70, P %"v35")
    => goto "L23";
  @"L23":
    => ret #1
} }.

Definition item_glibc_printf_buffer_flush'23str'2e39 : item :=
  (IData (a "glibc_printf_buffer_flush#str.39") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_printf_buffer_flush'23str'2e40 : item :=
  (IData (a "glibc_printf_buffer_flush#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_buffer_flush'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_flush#str.41") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 0)]).

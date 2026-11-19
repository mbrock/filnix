(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_pad_1.os` object.
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

Definition fn___printf_buffer_pad_1 : func :=
  ir_fn{ "export" "__printf_buffer_pad_1"(P %"v0", W %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L6" : "L15";
  @"L6":
    => ret void;
  @"L15" [%"pr.1" : L = phi("L66" => %"v84", "start" => %"v4")]:
    %"v22" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v27" : L = Ptoi %"v23";
    %"v28" : L = Ptoi %"v26";
    %"v29" : W = (Cmp Eq L) %"v27", %"v28"
    => br %"v29" ? "L30" : "L31";
  @"L30":
    call %"v33" : W = $"__printf_buffer_flush"(P %"v0");
    %"v34" : W = (Ext Ub) %"v33";
    %"v35" : W = (Cmp Eq W) %"v34", #0
    => goto "L31";
  @"L31" [%"v37" : W = phi("L15" => #0, "L30" => %"v35")]:
    => br %"v37" ? "L18" : "L20";
  @"L18":
    => ret void;
  @"L20":
    %"v43" = %"v0" +p #8;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v46" = %"v0" +p #16;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v48" : L = Ptoi %"v44";
    %"v49" : L = Ptoi %"v47";
    %"v50" : W = (Cmp Ne L) %"v48", %"v49"
    => br %"v50" ? "L41" : "L40";
  @"L40":
    %"v51" : P = Copy $"glibc_printf_buffer_pad_1#str.41";
    %"v52" : P = Copy $"glibc_printf_buffer_pad_1#str.42";
    %"v53" : P = Copy $"glibc_printf_buffer_pad_1#str.43";
    call void $"__libc_assert_fail"(P %"v51", P %"v52", W #35, P %"v53")
    => goto "L41";
  @"L41":
    %"v56" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v59" = %"v0" +p #8;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v61" : L = Ptoi %"v57";
    %"v62" : L = Ptoi %"v60";
    %"v63" : L = Sub %"v61", %"v62";
    %"v69" : W = (Cmp Ugt L) %"v63", %"pr.1"
    => br %"v69" ? "L66" : "L65";
  @"L65":
    => goto "L66";
  @"L66" [%"pr.2" : L = phi("L65" => %"v63", "L41" => %"pr.1")]:
    %"v72" = %"v0" +p #8;
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v74" : W = (Ext Sb) %"v2";
    call %"v76" : P = $"__GI_memset"(P %"v73", W %"v74", L %"pr.2");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v72";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v81" = %"v79" +p %"pr.2";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk1", %"v72";
    store.ptr [%"chk9" + 0] <- %"v81";
    %"v84" : L = Sub %"pr.1", %"pr.2";
    %"v86" : W = (Cmp Ugt L) %"v84", #0
    => br %"v86" ? poll "L15" : "L17";
  @"L17":
    => ret void
} }.

Definition item_glibc_printf_buffer_pad_1'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_pad_1#str.41") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_printf_buffer_pad_1'23str'2e42 : item :=
  (IData (a "glibc_printf_buffer_pad_1#str.42") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 49); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_buffer_pad_1'23str'2e43 : item :=
  (IData (a "glibc_printf_buffer_pad_1#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

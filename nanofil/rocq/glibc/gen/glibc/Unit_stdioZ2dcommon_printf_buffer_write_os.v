(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_write.os` object.
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

Definition fn___printf_buffer_write : func :=
  ir_fn{ "export" "__printf_buffer_write"(P %"v0", P %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L6" : "L15";
  @"L6":
    => ret void;
  @"L15" [%"pr.2" : L = phi("L68" => %"v89", "start" => %"v4"); %"pr.1" : P = phi("L68" => %"v86", "start" => %"v2")]:
    %"v19" : W = (Cmp Ugt L) %"pr.2", #0
    => br %"v19" ? "L16" : "L17";
  @"L16":
    %"v24" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v27" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v29" : L = Ptoi %"v25";
    %"v30" : L = Ptoi %"v28";
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => br %"v31" ? "L32" : "L33";
  @"L32":
    call %"v35" : W = $"__printf_buffer_flush"(P %"v0");
    %"v36" : W = (Ext Ub) %"v35";
    %"v37" : W = (Cmp Eq W) %"v36", #0
    => goto "L33";
  @"L33" [%"v39" : W = phi("L16" => #0, "L32" => %"v37")]:
    => br %"v39" ? "L20" : "L22";
  @"L20":
    => ret void;
  @"L22":
    %"v45" = %"v0" +p #8;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v48" = %"v0" +p #16;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Ne L) %"v50", %"v51"
    => br %"v52" ? "L43" : "L42";
  @"L42":
    %"v53" : P = Copy $"glibc_printf_buffer_write#str.41";
    %"v54" : P = Copy $"glibc_printf_buffer_write#str.42";
    %"v55" : P = Copy $"glibc_printf_buffer_write#str.43";
    call void $"__libc_assert_fail"(P %"v53", P %"v54", W #35, P %"v55")
    => goto "L43";
  @"L43":
    %"v58" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v61" = %"v0" +p #8;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v63" : L = Ptoi %"v59";
    %"v64" : L = Ptoi %"v62";
    %"v65" : L = Sub %"v63", %"v64";
    %"v71" : W = (Cmp Ugt L) %"v65", %"pr.2"
    => br %"v71" ? "L68" : "L67";
  @"L67":
    => goto "L68";
  @"L68" [%"pr.3" : L = phi("L67" => %"v65", "L43" => %"pr.2")]:
    %"v74" = %"v0" +p #8;
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v78" : P = $"__GI_memcpy"(P %"v75", P %"pr.1", L %"pr.3");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v74";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v83" = %"v81" +p %"pr.3";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk1", %"v74";
    store.ptr [%"chk9" + 0] <- %"v83";
    %"v86" = %"pr.1" +p %"pr.3";
    %"v89" : L = Sub %"pr.2", %"pr.3"
    => goto poll "L15";
  @"L17":
    => ret void
} }.

Definition item_glibc_printf_buffer_write'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_write#str.41") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_printf_buffer_write'23str'2e42 : item :=
  (IData (a "glibc_printf_buffer_write#str.42") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_buffer_write'23str'2e43 : item :=
  (IData (a "glibc_printf_buffer_write#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 0)]).

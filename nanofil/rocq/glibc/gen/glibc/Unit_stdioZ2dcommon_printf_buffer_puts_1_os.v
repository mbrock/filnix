(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_puts_1.os` object.
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

Definition fn___printf_buffer_puts_1 : func :=
  ir_fn{ "export" "__printf_buffer_puts_1"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L4" : "L13";
  @"L4":
    => ret void;
  @"L13" [%"pr.1" : P = phi("L42" => %"v80", "start" => %"v2")]:
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v18" : W = (Cmp Ne W) %"v17", #0
    => br %"v18" ? "L14" : "L15";
  @"L14":
    %"v23" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v26" = %"v0" +p #16;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v28" : L = Ptoi %"v24";
    %"v29" : L = Ptoi %"v27";
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => br %"v30" ? "L31" : "L32";
  @"L31":
    call %"v34" : W = $"__printf_buffer_flush"(P %"v0");
    %"v35" : W = (Ext Ub) %"v34";
    %"v36" : W = (Cmp Eq W) %"v35", #0
    => goto "L32";
  @"L32" [%"v38" : W = phi("L14" => #0, "L31" => %"v36")]:
    => br %"v38" ? "L19" : "L21";
  @"L19":
    => ret void;
  @"L21":
    %"v44" = %"v0" +p #8;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v47" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk3", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v49" : L = Ptoi %"v45";
    %"v50" : L = Ptoi %"v48";
    %"v51" : W = (Cmp Ne L) %"v49", %"v50"
    => br %"v51" ? "L42" : "L41";
  @"L41":
    %"v52" : P = Copy $"glibc_printf_buffer_puts_1#str.41";
    %"v53" : P = Copy $"glibc_printf_buffer_puts_1#str.42";
    %"v54" : P = Copy $"glibc_printf_buffer_puts_1#str.43";
    call void $"__libc_assert_fail"(P %"v52", P %"v53", W #32, P %"v54")
    => goto "L42";
  @"L42":
    %"v58" = %"v0" +p #16;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk3", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v61" = %"v0" +p #8;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk2", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v63" : L = Ptoi %"v59";
    %"v64" : L = Ptoi %"v62";
    %"v65" : L = Sub %"v63", %"v64";
    call %"v66" : L = $"__GI___strnlen"(P %"pr.1", L %"v65");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"v61";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk8";
    call %"v72" : P = $"__GI_memcpy"(P %"v69", P %"pr.1", L %"v66");
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"v61";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v77" = %"v75" +p %"v66";
    %"chk10" : A = (Renew 0 8 Write 8) %"chk2", %"v61";
    store.ptr [%"chk10" + 0] <- %"v77";
    %"v80" = %"pr.1" +p %"v66"
    => goto poll "L13";
  @"L15":
    => ret void
} }.

Definition item_glibc_printf_buffer_puts_1'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_puts_1#str.41") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_printf_buffer_puts_1'23str'2e42 : item :=
  (IData (a "glibc_printf_buffer_puts_1#str.42") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 115); (Item Wb 95); (Item Wb 49); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_buffer_puts_1'23str'2e43 : item :=
  (IData (a "glibc_printf_buffer_puts_1#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 115); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

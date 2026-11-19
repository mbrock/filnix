(** This file defines checked IR from glibc’s `stdio-common/translated_number_width.os` object.
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

Definition fn___translated_number_width : func :=
  ir_fn{ "export" "__translated_number_width"(P %"v0", P %"v2", P %"v4") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v9" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" = %"v11" +p #19;
    %"chk2" : A = (Check 0 1 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"v18" : W = (Cmp Sgt W) %"v17", #0
    => br %"v18" ? "L12" : "L33";
  @"L12":
    %"v21" : L = Ptoi %"v4";
    %"v22" : L = Ptoi %"v2";
    %"v23" : L = Sub %"v21", %"v22";
    %"v25" = %"v11" +p #19;
    %"v26" : W = (RawLoad (LdNarrow Ub) 0) %"chk2";
    %"v27" : L = (Ext Uw) %"v26";
    %"v28" : L = Mul %"v23", %"v27"
    => ret %"v28";
  @"L33" [%"pr.2" : P = phi("L44" => %"v69", "start" => %"v2"); %"pr.1" : W = phi("L44" => %"v67", "start" => #0)]:
    %"v39" : L = Ptoi %"pr.2";
    %"v40" : L = Ptoi %"v4";
    %"v41" : W = (Cmp Ult L) %"v39", %"v40"
    => br %"v41" ? "L34" : "L36";
  @"L34":
    %"chk4" : A = (Check 0 1 Read 1) %"pr.2";
    %"v46" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v47" : W = (Cmp Sge W) %"v46", #48
    => br %"v47" ? "L48" : "L49";
  @"L48":
    %"v51" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v52" : W = (Cmp Sle W) %"v51", #57
    => goto "L49";
  @"L49" [%"v54" : W = phi("L34" => #0, "L48" => %"v52")]:
    => br %"v54" ? "L44" : "L43";
  @"L43":
    %"v55" : P = Copy $"glibc_translated_number_width#str.45";
    %"v56" : P = Copy $"glibc_translated_number_width#str.46";
    %"v57" : P = Copy $"glibc_translated_number_width#str.47";
    call void $"__libc_assert_fail"(P %"v55", P %"v56", W #37, P %"v57")
    => goto "L44";
  @"L44":
    %"v60" = %"v11" +p #9;
    %"chk6" : A = (Renew 0 1 Read 1) %"chk4", %"pr.2";
    %"v62" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v63" : W = Sub %"v62", #48;
    %"v64" : L = (Ext Sw) %"v63";
    %"v65" = %"v60" +p %"v64";
    %"chk7" : A = (Check 0 1 Read 1) %"v65";
    %"v66" : W = (RawLoad (LdNarrow Ub) 0) %"chk7";
    %"v67" : W = Add %"pr.1", %"v66";
    %"v69" = %"pr.2" +p #1
    => goto poll "L33";
  @"L36":
    => ret %"pr.1"
} }.

Definition item_glibc_translated_number_width'23str'2e45 : item :=
  (IData (a "glibc_translated_number_width#str.45") (LRo (a "local")) 1 [(Item Wb 39); (Item Wb 48); (Item Wb 39); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 42); (Item Wb 112); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 42); (Item Wb 112); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 39); (Item Wb 57); (Item Wb 39); (Item Wb 0)]).

Definition item_glibc_translated_number_width'23str'2e46 : item :=
  (IData (a "glibc_translated_number_width#str.46") (LRo (a "local")) 1 [(Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 95); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 116); (Item Wb 104); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_translated_number_width'23str'2e47 : item :=
  (IData (a "glibc_translated_number_width#str.47") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 95); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 116); (Item Wb 104); (Item Wb 0)]).

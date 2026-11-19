(** This file defines checked IR from glibc’s `stdio-common/grouping_iterator.os` object.
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

Definition fn___grouping_iterator_init : func :=
  ir_fn{ "export" "__grouping_iterator_init"(P %"v0", W %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    %"v12" : W = (Cmp Ule W) %"v6", #1
    => br %"v12" ? "L8" : "iw_1.start";
  @"L8":
    call %"v15" : W = $"__grouping_iterator_init_none"(P %"v0", W %"v6");
    %"v16" : W = (Ext Ub) %"v15"
    => ret %"v16";
  @"iw_1.start":
    %"iw_1.v10" : W = (Cmp Eq W) %"v2", #4
    => br %"iw_1.v10" ? "iw_1.L8" : "iw_1.L7";
  @"iw_1.L7":
    => goto "iw_1.L8";
  @"iw_1.L8" [%"iw_1.v11" : W = phi("iw_1.L7" => #65538, "iw_1.start" => #262148)]:
    %"iw_1.iw_1.v8" : L = (Ext Sw) %"v2";
    %"iw_1.iw_1.v9" : L = Shl %"iw_1.iw_1.v8", #3;
    %"iw_1.iw_1.v10" = %"v4" +p %"iw_1.iw_1.v9";
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v10";
    %"iw_1.iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.iw_1.v12" = %"iw_1.iw_1.v11" +p #56;
    %"iw_1.iw_1.v14" : W = And %"iw_1.v11", #65535;
    %"iw_1.iw_1.v15" : L = (Ext Sw) %"iw_1.iw_1.v14";
    %"iw_1.iw_1.v16" : L = Shl %"iw_1.iw_1.v15", #3;
    %"iw_1.iw_1.v17" = %"iw_1.iw_1.v12" +p %"iw_1.iw_1.v16";
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v17";
    %"iw_1.iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 1 Read 1) %"iw_1.iw_1.v18";
    %"iw_2.v10" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"iw_2.v11" : W = (Cmp Eq W) %"iw_2.v10", #127
    => br %"iw_2.v11" ? "iw_2.L13" : "iw_2.L12";
  @"iw_2.L12":
    %"iw_2.v15" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"iw_2.v16" : W = (Cmp Sle W) %"iw_2.v15", #0
    => goto "iw_2.L13";
  @"iw_2.L13" [%"iw_2.v18" : W = phi("iw_1.L8" => #1, "iw_2.L12" => %"iw_2.v16")]:
    => br %"iw_2.v18" ? "iw_2.L6" : "iw_2.L28";
  @"iw_2.L6":
    call %"iw_2.v21" : W = $"__grouping_iterator_init_none"(P %"v0", W %"v6");
    %"iw_2.v22" : W = (Ext Ub) %"iw_2.v21"
    => goto "iw_2.join";
  @"iw_2.L28" [%"iw_2.pr.7" : W = phi("iw_2.L13" => #0, "iw_2.L51" => %"iw_2.v44"); %"iw_2.pr.5" : W = phi("iw_2.L13" => #0, "iw_2.L51" => %"iw_2.v34"); %"iw_2.pr.3" : W = phi("iw_2.L13" => %"v6", "iw_2.L51" => %"iw_2.v49"); %"iw_2.pr.1" : P = phi("iw_2.L13" => %"iw_1.iw_1.v18", "iw_2.L51" => %"iw_2.v47")]:
    %"chk4" : A = (Check 0 1 Read 1) %"iw_2.pr.1";
    %"iw_2.v33" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v34" : W = Add %"iw_2.pr.5", %"iw_2.v33";
    %"iw_2.v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v41" : W = (Cmp Ule W) %"iw_2.pr.3", %"iw_2.v40"
    => br %"iw_2.v41" ? "iw_2.L30" : "iw_2.L37";
  @"iw_2.L37":
    %"iw_2.v44" : W = Add %"iw_2.pr.7", #1;
    %"iw_2.v47" = %"iw_2.pr.1" +p #1;
    %"iw_2.v48" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v49" : W = Sub %"iw_2.pr.3", %"iw_2.v48";
    %"chk7" : A = (HalfCheck Upper 0 1 Read 1) %"chk4", %"iw_2.v47";
    %"iw_2.v54" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"iw_2.v55" : W = (Cmp Eq W) %"iw_2.v54", #127
    => br %"iw_2.v55" ? "iw_2.L57" : "iw_2.L56";
  @"iw_2.L56":
    %"iw_2.v59" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"iw_2.v60" : W = (Cmp Slt W) %"iw_2.v59", #0
    => goto "iw_2.L57";
  @"iw_2.L57" [%"iw_2.v62" : W = phi("iw_2.L37" => #1, "iw_2.L56" => %"iw_2.v60")]:
    => br %"iw_2.v62" ? "iw_2.L30" : "iw_2.L51";
  @"iw_2.L51":
    %"iw_2.v68" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"iw_2.v69" : W = (Cmp Eq W) %"iw_2.v68", #0
    => br %"iw_2.v69" ? "iw_2.L64" : poll "iw_2.L28";
  @"iw_2.L64":
    (Flight (a "iw_2.v71") Sub [(FAddress (t "iw_2.v47")); (FValue (Const 1))] (LowerOf (t "iw_2.v47")));
    %"iw_2.v74" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v75" : W = Sub %"iw_2.v34", %"iw_2.v74";
    %"iw_2.v78" : W = Sub %"iw_2.v49", #1;
    %"iw_2.v80" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v81" : W = Udiv %"iw_2.v78", %"iw_2.v80";
    %"iw_2.v84" : W = Add %"iw_2.v44", %"iw_2.v81";
    %"iw_2.v88" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v89" : W = Mul %"iw_2.v81", %"iw_2.v88";
    %"iw_2.v90" : W = Sub %"iw_2.v49", %"iw_2.v89"
    => goto "iw_2.L30";
  @"iw_2.L30" [%"iw_2.pr.8" : W = phi("iw_2.L64" => %"iw_2.v84", "iw_2.L28" => %"iw_2.pr.7", "iw_2.L57" => %"iw_2.v44"); %"iw_2.pr.6" : W = phi("iw_2.L64" => %"iw_2.v75", "iw_2.L28" => %"iw_2.v34", "iw_2.L57" => %"iw_2.v34"); %"iw_2.pr.4" : W = phi("iw_2.L64" => %"iw_2.v90", "iw_2.L28" => %"iw_2.pr.3", "iw_2.L57" => %"iw_2.v49"); %"iw_2.pr.2" : P = phi("iw_2.L64" => %"iw_2.v71", "iw_2.L28" => %"iw_2.pr.1", "iw_2.L57" => %"iw_2.v47")]:
    %"chk13" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk13" + 0] <- %"iw_2.pr.4";
    %"iw_2.v95" = %"v0" +p #4;
    %"chk14" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"iw_2.v95";
    store Ww [%"chk14" + 0] <- %"v6";
    %"iw_2.v98" = %"v0" +p #8;
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"iw_2.v98";
    store.ptr [%"chk15" + 0] <- %"iw_2.pr.2";
    %"iw_2.v101" = %"v0" +p #16;
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"iw_2.v101";
    store Ww [%"chk16" + 0] <- %"iw_2.pr.6";
    %"iw_2.v104" = %"v0" +p #20;
    %"chk17" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"iw_2.v104";
    store Ww [%"chk17" + 0] <- %"iw_2.pr.8";
    %"iw_2.v108" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"iw_2.v109" : W = (Cmp Ugt W) %"iw_2.v108", #0
    => goto "iw_2.join";
  @"iw_2.join" [%"v23" : W = phi("iw_2.L6" => %"iw_2.v22", "iw_2.L30" => %"iw_2.v109")]:
    %"v24" : W = (Ext Ub) %"v23"
    => ret %"v24"
} }.

Definition fn___grouping_iterator_init_none : func :=
  ir_fn{ "export" "__grouping_iterator_init_none"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    call %"v5" : P = $"__GI_memset"(P %"v0", W #0, L #24);
    %"chk0" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk0" + 0] <- %"v2";
    %"v9" = %"v0" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v9";
    store Ww [%"chk1" + 0] <- %"v2"
    => ret #0
} }.

Definition fn___grouping_iterator_next : func :=
  ir_fn{ "export" "__grouping_iterator_next"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #4;
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v8" : W = (Cmp Ugt W) %"v7", #0
    => br %"v8" ? "L4" : "L3";
  @"L3":
    %"v9" : P = Copy $"glibc_grouping_iterator#str.41";
    %"v10" : P = Copy $"glibc_grouping_iterator#str.42";
    %"v11" : P = Copy $"glibc_grouping_iterator#str.43";
    call void $"__libc_assert_fail"(P %"v9", P %"v10", W #111, P %"v11")
    => goto "L4";
  @"L4":
    %"v13" = %"v0" +p #4;
    %"chk1" : A = (Renew 0 4 Read 1) %"chk0", %"v13";
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v15" : W = Sub %"v14", #1;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v13";
    store Ww [%"chk2" + 0] <- %"v15";
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v20" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v21" : W = (Cmp Ugt W) %"v20", #0
    => br %"v21" ? "L16" : "L18";
  @"L16":
    %"v23" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v24" : W = Sub %"v23", #1;
    store Ww [%"chk3" + 0] <- %"v24"
    => ret #0;
  @"L18":
    %"v31" = %"v0" +p #4;
    %"v32" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v34" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v34";
    %"v35" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v36" : W = (Cmp Ult W) %"v32", %"v35"
    => br %"v36" ? "L27" : "L29";
  @"L27":
    %"v38" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk8";
    (Flight (a "v40") Sub [(FAddress (t "v39")); (FValue (Const 1))] (LowerOf (t "v39")));
    %"chk9" : A = (Renew 0 8 Write 8) %"chk8", %"v38";
    store.ptr [%"chk9" + 0] <- %"v40"
    => goto "L29";
  @"L29":
    %"v43" = %"v0" +p #8;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 1 Read 1) %"v44";
    %"v45" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"v46" : W = Sub %"v45", #1;
    %"chk12" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk12" + 0] <- %"v46"
    => ret #1
} }.

Definition item_glibc_grouping_iterator'23str'2e41 : item :=
  (IData (a "glibc_grouping_iterator#str.41") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 114); (Item Wb 101); (Item Wb 109); (Item Wb 97); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 62); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_grouping_iterator'23str'2e42 : item :=
  (IData (a "glibc_grouping_iterator#str.42") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 114); (Item Wb 111); (Item Wb 117); (Item Wb 112); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 95); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_grouping_iterator'23str'2e43 : item :=
  (IData (a "glibc_grouping_iterator#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 114); (Item Wb 111); (Item Wb 117); (Item Wb 112); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 95); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 95); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 0)]).

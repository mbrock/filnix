(** This file defines checked IR from glibc’s `iconv/gconv_builtin.os` object.
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

Definition fn___gconv_get_builtin_trans : func :=
  ir_fn{ "export" "__gconv_get_builtin_trans"(P %"v0", P %"v2") -> RVoid {
  @"start":
    => goto "L5";
  @"L5" [%"pr.1" : L = phi("L7" => %"v25", "start" => #0)]:
    %"v11" : W = (Cmp Ult L) %"pr.1", #12
    => br %"v11" ? "L6" : "L8";
  @"L6":
    %"v16" : P = Copy $"glibc_gconv_builtin#map";
    %"v18" : L = Shl %"pr.1", #5;
    %"v19" = %"v16" +p %"v18";
    %"chk0" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v21" : W = $"__GI_strcmp"(P %"v0", P %"v20");
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => br %"v22" ? "L8" : "L7";
  @"L7":
    %"v25" : L = Add %"pr.1", #1
    => goto poll "L5";
  @"L8":
    => br %"v11" ? "L28" : "L27";
  @"L27":
    %"v32" : P = Copy $"glibc_gconv_builtin#str.244";
    %"v33" : P = Copy $"glibc_gconv_builtin#str.245";
    %"v34" : P = Copy $"glibc_gconv_builtin#str.246";
    call void $"__libc_assert_fail"(P %"v32", P %"v33", W #69, P %"v34")
    => goto "L28";
  @"L28":
    %"v36" = %"v2" +p #40;
    %"v37" : P = Copy $"glibc_gconv_builtin#map";
    %"v39" : L = Shl %"pr.1", #5;
    %"v40" = %"v37" +p %"v39";
    %"v41" = %"v40" +p #8;
    %"chk1" : A = (Check 0 8 Read 8) %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 8 Write 8) %"v36";
    store.ptr [%"chk2" + 0] <- %"v42";
    %"v44" = %"v2" +p #48;
    %"v45" : P = Copy $"glibc_gconv_builtin#map";
    %"v48" = %"v45" +p %"v39";
    %"v49" = %"v48" +p #16;
    %"chk3" : A = (Check 0 8 Read 8) %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v44";
    store.ptr [%"chk4" + 0] <- %"v50";
    %"v52" = %"v2" +p #56;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v52";
    store.ptr [%"chk5" + 0] <- #0;
    %"v54" = %"v2" +p #64;
    %"chk6" : A = (HalfCheck Upper 0 8 Write 8) %"chk2", %"v54";
    store.ptr [%"chk6" + 0] <- #0;
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"v2";
    store.ptr [%"chk7" + 0] <- #0;
    %"v57" = %"v2" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk2", %"v57";
    store.ptr [%"chk8" + 0] <- #0;
    %"v59" = %"v2" +p #72;
    %"v60" : P = Copy $"glibc_gconv_builtin#map";
    %"v63" = %"v60" +p %"v39";
    %"v64" = %"v63" +p #24;
    %"chk9" : A = (Check 0 1 Read 1) %"v64";
    %"v65" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"chk10" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v59";
    store Ww [%"chk10" + 0] <- %"v65";
    %"v67" = %"v2" +p #76;
    %"v68" : P = Copy $"glibc_gconv_builtin#map";
    %"v71" = %"v68" +p %"v39";
    %"v72" = %"v71" +p #25;
    %"chk11" : A = (Check 0 1 Read 1) %"v72";
    %"v73" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"chk12" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v67";
    store Ww [%"chk12" + 0] <- %"v73";
    %"v75" = %"v2" +p #80;
    %"v76" : P = Copy $"glibc_gconv_builtin#map";
    %"v79" = %"v76" +p %"v39";
    %"v80" = %"v79" +p #26;
    %"chk13" : A = (Check 0 1 Read 1) %"v80";
    %"v81" : W = (RawLoad (LdNarrow Sb) 0) %"chk13";
    %"chk14" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v75";
    store Ww [%"chk14" + 0] <- %"v81";
    %"v83" = %"v2" +p #84;
    %"v84" : P = Copy $"glibc_gconv_builtin#map";
    %"v87" = %"v84" +p %"v39";
    %"v88" = %"v87" +p #27;
    %"chk15" : A = (Check 0 1 Read 1) %"v88";
    %"v89" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v83";
    store Ww [%"chk16" + 0] <- %"v89";
    %"v91" = %"v2" +p #88;
    %"chk17" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v91";
    store Ww [%"chk17" + 0] <- #0
    => ret void
} }.

Definition item_glibc_gconv_builtin'23map : item :=
  (IData (a "glibc_gconv_builtin#map") (LRo (a "local")) 8 (app [(Sym (a "glibc_gconv_builtin#str.247") 0); (Sym (a "__gconv_transform_internal_ucs4") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.248") 0); (Sym (a "__gconv_transform_ucs4_internal") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.249") 0); (Sym (a "__gconv_transform_internal_ucs4le") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.250") 0); (Sym (a "__gconv_transform_ucs4le_internal") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.251") 0); (Sym (a "__gconv_transform_internal_utf8") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 1); (Item Wb 6); (Zero 4); (Sym (a "glibc_gconv_builtin#str.252") 0); (Sym (a "__gconv_transform_utf8_internal") 0); (Sym (a "__gconv_btwoc_ascii") 0); (Item Wb 1); (Item Wb 6); (Item Wb 4); (Item Wb 4); (Zero 4)] [(Sym (a "glibc_gconv_builtin#str.253") 0); (Sym (a "__gconv_transform_ucs2_internal") 0); (Item Wl 0); (Item Wb 2); (Item Wb 2); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.254") 0); (Sym (a "__gconv_transform_internal_ucs2") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 2); (Item Wb 2); (Zero 4); (Sym (a "glibc_gconv_builtin#str.255") 0); (Sym (a "__gconv_transform_ascii_internal") 0); (Sym (a "__gconv_btwoc_ascii") 0); (Item Wb 1); (Item Wb 1); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.256") 0); (Sym (a "__gconv_transform_internal_ascii") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 1); (Item Wb 1); (Zero 4); (Sym (a "glibc_gconv_builtin#str.257") 0); (Sym (a "__gconv_transform_ucs2reverse_internal") 0); (Item Wl 0); (Item Wb 2); (Item Wb 2); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.258") 0); (Sym (a "__gconv_transform_internal_ucs2reverse") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 2); (Item Wb 2); (Zero 4)])).

Definition item_glibc_gconv_builtin'23str'2e244 : item :=
  (IData (a "glibc_gconv_builtin#str.244") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 40); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 41); (Item Wb 32); (Item Wb 47); (Item Wb 32); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 40); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 41); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e245 : item :=
  (IData (a "glibc_gconv_builtin#str.245") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 105); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e246 : item :=
  (IData (a "glibc_gconv_builtin#str.246") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 105); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 95); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e247 : item :=
  (IData (a "glibc_gconv_builtin#str.247") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e248 : item :=
  (IData (a "glibc_gconv_builtin#str.248") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e249 : item :=
  (IData (a "glibc_gconv_builtin#str.249") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e250 : item :=
  (IData (a "glibc_gconv_builtin#str.250") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e251 : item :=
  (IData (a "glibc_gconv_builtin#str.251") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 116); (Item Wb 102); (Item Wb 56); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e252 : item :=
  (IData (a "glibc_gconv_builtin#str.252") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 116); (Item Wb 102); (Item Wb 56); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e253 : item :=
  (IData (a "glibc_gconv_builtin#str.253") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e254 : item :=
  (IData (a "glibc_gconv_builtin#str.254") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e255 : item :=
  (IData (a "glibc_gconv_builtin#str.255") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 97); (Item Wb 115); (Item Wb 99); (Item Wb 105); (Item Wb 105); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e256 : item :=
  (IData (a "glibc_gconv_builtin#str.256") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 97); (Item Wb 115); (Item Wb 99); (Item Wb 105); (Item Wb 105); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e257 : item :=
  (IData (a "glibc_gconv_builtin#str.257") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 114); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition item_glibc_gconv_builtin'23str'2e258 : item :=
  (IData (a "glibc_gconv_builtin#str.258") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 114); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 101); (Item Wb 0)]).

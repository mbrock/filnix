(** This file defines checked IR from glibc’s `misc/mmap64.os` object.
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

Definition item___GI___mmap : item :=
  (IAlias (a "__GI___mmap") (a "export") (a "__GI___mmap64")).

Definition fn___GI___mmap64 : func :=
  ir_fn{ "export" "__GI___mmap64"(P %"v0", L %"v2", W %"v4", W %"v6", W %"v8", L %"v10") -> (RClass P) {
  @"start":
    %"v18" : L = And %"v10", #4095;
    %"v19" : W = (Cmp Ne L) %"v18", #0
    => br %"v19" ? "L12" : "L14";
  @"L12":
    %"v20" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v20";
    store Ww [%"chk0" + 0] <- #22;
    (Flight (a "v22") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v22";
  @"L14":
    %"v28" : L = Ptoi %"v0";
    %"v29" : L = Ptoi #0;
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => br %"v30" ? "L31" : "L32";
  @"L31":
    %"v34" : W = And %"v4", #4;
    %"v35" : W = (Cmp Ne W) %"v34", #0
    => br %"v35" ? "L32" : "L36";
  @"L36":
    %"v39" : W = And %"v6", #2048;
    %"v40" : W = (Cmp Ne W) %"v39", #0
    => goto "L32";
  @"L32" [%"v44" : W = phi("L14" => #0, "L31" => #1, "L36" => %"v40")]:
    => br %"v44" ? "L45" : "L46";
  @"L45":
    %"v47" : P = Copy $"_dl_x86_cpu_features";
    %"v48" = %"v47" +p #340;
    %"chk1" : A = (Check 0 4 Read 1) %"v48";
    %"v50" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v51" : W = And %"v50", #1024;
    %"v52" : W = (Cmp Ne W) %"v51", #0
    => goto "L46";
  @"L46" [%"v54" : W = phi("L32" => #0, "L45" => %"v52")]:
    => br %"v54" ? "L24" : "L26";
  @"L24":
    %"v90" : P = Copy $"glibc_mmap64#str.279";
    call void $"zsafety_error"(P %"v90");
    (Flight (a "v106") Copy [(FValue (Const 0))] LowerNone);
    (Flight (a "v113") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v114" : L = Ptoi %"v106";
    %"v115" : L = Ptoi %"v113";
    %"v116" : W = (Cmp Ne L) %"v114", %"v115"
    => br %"v116" ? "L107" : "L26";
  @"L107":
    => ret %"v106";
  @"L26":
    call %"v125" : P = $"zsys_mmap"(P %"v0", L %"v2", W %"v4", W %"v6", W %"v8", L %"v10")
    => ret %"v125"
} }.

Definition item_glibc_mmap64'23str'2e279 : item :=
  (IData (a "glibc_mmap64#str.279") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110)] [(Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 10); (Item Wb 9); (Item Wb 0)])).

(** This file defines checked IR from glibc’s `nptl/futex-internal.os` object.
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

Definition fn___GI___futex_abstimed_wait64 : func :=
  ir_fn{ "export" "__GI___futex_abstimed_wait64"(P %"v0", W %"v2", W %"v4", P %"v6", W %"v8") -> (RClass W) {
  @"start":
    %"v21" : W = (Cmp Eq W) %"v8", #0
    => br %"v21" ? "L23" : "L22";
  @"L22":
    %"v25" : W = (Cmp Eq W) %"v8", #128
    => goto "L23";
  @"L23" [%"v27" : W = phi("start" => #1, "L22" => %"v25")]:
    => br %"v27" ? "L16" : "L19";
  @"L19":
    %"v29" : P = Copy $"glibc_futex_internal#str.244";
    %"v30" : P = Copy $"glibc_futex_internal#str.245";
    %"v31" : P = Copy $"glibc_futex_internal#str.246";
    %"v32" : P = Copy $"glibc_futex_internal#str.247";
    call void $"zerrorf"(P %"v29", P %"v30", W #31, P %"v31", P %"v32")
    => goto "L16";
  @"L16":
    => br %"v21" ? "L35" : "L34";
  @"L34":
    => goto "L35";
  @"L35" [%"v38" : W = phi("L34" => #0, "L16" => #1)]:
    call %"v39" : W = $"zsys_futex_timedwait"(P %"v0", W %"v2", W %"v4", P %"v6", W %"v38")
    => ret %"v39"
} }.

Definition item_glibc_futex_internal'23str'2e244 : item :=
  (IData (a "glibc_futex_internal#str.244") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition item_glibc_futex_internal'23str'2e245 : item :=
  (IData (a "glibc_futex_internal#str.245") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_futex_internal'23str'2e246 : item :=
  (IData (a "glibc_futex_internal#str.246") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 97); (Item Wb 98); (Item Wb 115); (Item Wb 116); (Item Wb 105); (Item Wb 109); (Item Wb 101); (Item Wb 100); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 105); (Item Wb 116); (Item Wb 54); (Item Wb 52); (Item Wb 0)]).

Definition item_glibc_futex_internal'23str'2e247 : item :=
  (IData (a "glibc_futex_internal#str.247") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

(** This file defines checked IR from glibc’s `assert/__libc_assert_fail.os` object.
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

Definition fn___libc_assert_fail : func :=
  ir_fn{ "export" "__libc_assert_fail"(P %"v0", P %"v2", W %"v4", P %"v6") -> RVoid {
  @"start":
    %"v8" : P = (Alloc 4) #11;
    %"v12" = %"v8" +p #11;
    %"v15" = %"v12" +p #18446744073709551615;
    %"chk0" : A = (Check 0 1 Write 1) %"v15";
    store Wb [%"chk0" + 0] <- #0;
    %"v18" : L = (Ext Uw) %"v4";
    (Flight (a "v23") Sub [(FAddress (t "v12")); (FValue (Const 1))] (LowerOf (t "v12")));
    call %"v24" : P = $"_itoa_word"(L %"v18", P %"v23", W #10, W #0);
    %"v25" : P = Copy $"glibc___libc_assert_fail#str.21";
    %"v26" : P = Copy $"glibc___libc_assert_fail#str.22";
    call void $"__libc_message_impl"(P %"v25", P %"v26", P %"v2", P %"v24", P %"v6", P %"v0")
    => ret void
} }.

Definition item_glibc___libc_assert_fail'23str'2e21 : item :=
  (IData (a "glibc___libc_assert_fail#str.21") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc___libc_assert_fail'23str'2e22 : item :=
  (IData (a "glibc___libc_assert_fail#str.22") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 40); (Item Wb 37); (Item Wb 115); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

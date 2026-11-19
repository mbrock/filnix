(** This file defines checked IR from glibc’s `nptl/unwind.os` object.
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

Definition fn___GI___pthread_unwind : func :=
  ir_fn{ "export" "__GI___pthread_unwind"(P %"v0") -> RVoid {
  @"start":
    call %"v5" : P = $"zthread_self_cookie"();
    %"v7" = %"v5" +p #1680;
    %"chk0" : A = (Check 0 8 Write 1) %"v7";
    store Wl [%"chk0" + 0] <- #0;
    %"v10" = %"v7" +p #8;
    %"v11" : P = Copy $"glibc_unwind#unwind_cleanup";
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v10";
    store.ptr [%"chk1" + 0] <- %"v11";
    %"v14" : P = Copy $"glibc_unwind#unwind_stop";
    call %"v16" : W = $"_Unwind_ForcedUnwind"(P %"v7", P %"v14", P %"v0");
    call void $"__GI_abort"()
    => ret void
} }.

Definition item_glibc_unwind'23str'2e287 : item :=
  (IData (a "glibc_unwind#str.287") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition item_glibc_unwind'23str'2e288 : item :=
  (IData (a "glibc_unwind#str.288") (LRo (a "local")) 1 [(Item Wb 117); (Item Wb 110); (Item Wb 119); (Item Wb 105); (Item Wb 110); (Item Wb 100); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_unwind'23str'2e289 : item :=
  (IData (a "glibc_unwind#str.289") (LRo (a "local")) 1 [(Item Wb 117); (Item Wb 110); (Item Wb 119); (Item Wb 105); (Item Wb 110); (Item Wb 100); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 111); (Item Wb 112); (Item Wb 0)]).

Definition item_glibc_unwind'23str'2e290 : item :=
  (IData (a "glibc_unwind#str.290") (LRo (a "local")) 1 [(Item Wb 33); (Item Wb 99); (Item Wb 117); (Item Wb 114); (Item Wb 112); (Item Wb 0)]).

Definition item_glibc_unwind'23str'2e291 : item :=
  (IData (a "glibc_unwind#str.291") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 65); (Item Wb 84); (Item Wb 65); (Item Wb 76); (Item Wb 58); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 99); (Item Wb 101); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 116); (Item Wb 104); (Item Wb 114); (Item Wb 111); (Item Wb 119); (Item Wb 110); (Item Wb 10); (Item Wb 0)]).

Definition fn_glibc_unwind'23unwind_cleanup : func :=
  ir_fn{ "local" "glibc_unwind#unwind_cleanup"(W %"v0", P %"v2") -> RVoid {
  @"start":
    %"v4" : P = Copy $"glibc_unwind#str.291";
    call void $"__GI___libc_fatal"(P %"v4")
    => ret void
} }.

Definition fn_glibc_unwind'23unwind_stop : func :=
  ir_fn{ "local" "glibc_unwind#unwind_stop"(W %"v0", W %"v2", L %"v4", P %"v6", P %"v8", P %"v10") -> (RClass W) {
  @"start":
    call %"v15" : P = $"zthread_self_cookie"();
    %"v18" = %"v15" +p #776;
    %"chk0" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v23" = %"v15" +p #1712;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" : L = Ptoi %"v24";
    %"v27" = %"v15" +p #1720;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v27";
    %"v28" : L = (RawLoad LdL 0) %"chk2";
    %"v29" : L = Add %"v25", %"v28";
    %"v34" : W = And %"v2", #16
    => br %"v34" ? "L36" : "L35";
  @"L35":
    call %"v38" : L = $"_Unwind_GetCFA"(P %"v8");
    (Flight (a "v39") Copy [(FValue (t "v38"))] LowerNone);
    %"v40" : L = Ptoi %"v39";
    %"v42" : L = Sub %"v40", %"v29";
    %"chk3" : A = (Check 0 8 Read 8) %"v10";
    %"iw_1.iw_1.v3" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"iw_1.iw_1.v4" : P = $"zget_jmp_buf_impl_frame"(P %"iw_1.iw_1.v3");
    %"iw_1.v4" : L = Ptoi %"iw_1.iw_1.v4";
    %"v47" : L = Sub %"iw_1.v4", %"v29";
    %"v49" : W = (Cmp Uge L) %"v42", %"v47"
    => goto "L36";
  @"L36" [%"v51" : W = phi("start" => #1, "L35" => %"v49")]:
    => br %"v51" ? "L32" : "L31";
  @"L31":
    => goto "L32";
  @"L32" [%"pr.1" : W = phi("L31" => #0, "L36" => #1)]:
    %"v59" : L = Ptoi %"v19";
    %"v61" : W = (Cmp Eq L) %"v59", #0
    => br %"v61" ? "L54" : "L57";
  @"L57":
    %"v63" : P = Copy $"glibc_unwind#str.287";
    %"v64" : P = Copy $"glibc_unwind#str.288";
    %"v65" : P = Copy $"glibc_unwind#str.289";
    %"v66" : P = Copy $"glibc_unwind#str.290";
    call void $"zerrorf"(P %"v63", P %"v64", W #64, P %"v65", P %"v66")
    => goto "L54";
  @"L54":
    => br %"pr.1" ? "L67" : "L69";
  @"L67":
    call void $"__libc_longjmp"(P %"v10", W #1)
    => goto "L69";
  @"L69":
    => ret #0
} }.

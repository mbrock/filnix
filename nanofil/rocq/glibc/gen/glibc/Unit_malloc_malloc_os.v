(** This file defines checked IR from glibc’s `malloc/malloc.os` object.
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

Definition fn___GI___libc_free : func :=
  ir_fn{ "export" "__GI___libc_free"(P %"v0") -> RVoid {
  @"start":
    call void $"zgc_free"(P %"v0")
    => ret void
} }.

Definition fn___GI___libc_malloc : func :=
  ir_fn{ "export" "__GI___libc_malloc"(L %"v0") -> (RClass P) {
  @"start":
    %"iw_1.v6" : W = (Cmp Ugt L) %"v0", #9223372036854775807
    => br %"iw_1.v6" ? "iw_1.join" : "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v14" : L = Add %"v0", #8;
    %"iw_1.v23" : L = Add %"iw_1.v14", #15;
    %"iw_1.v43" : W = (Cmp Ult L) %"iw_1.v23", #32
    => br %"iw_1.v43" ? "iw_1.join" : "iw_1.L76";
  @"iw_1.L76":
    %"iw_1.v83" : L = And %"iw_1.v23", #18446744073709551600
    => goto "iw_1.join";
  @"iw_1.join" [%"v4" : L = phi("start" => #18446744073709551615, "iw_1.L4" => #32, "iw_1.L76" => %"iw_1.v83")]:
    %"v9" : P = Copy $"glibc_malloc#mp_";
    %"v10" = %"v9" +p #120;
    %"chk0" : A = (Check 0 8 Read 1) %"v10";
    %"v11" : L = (RawLoad LdL 0) %"chk0";
    %"v12" : W = (Cmp Ult L) %"v4", %"v11"
    => br %"v12" ? "L26" : "L7";
  @"L26":
    %"v34" : L = Sub %"v4", #32;
    %"v42" : L = Shr %"v34", #4;
    %"v47" : W = (Cmp Ult L) %"v42", #64
    => br %"v47" ? "L43" : "iw_3.start";
  @"L43":
    %"v53" : P = Copy $"tcache";
    %"chk1" : A = (Check 0 8 Read 8) %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v55" = %"v54" +p #152;
    %"v57" : L = Shl %"v42", #3;
    %"v58" = %"v55" +p %"v57";
    %"chk2" : A = (Check 0 8 Read 8) %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v60" : L = Ptoi %"v59";
    %"v61" : L = Ptoi #0;
    %"v62" : W = (Cmp Ne L) %"v60", %"v61"
    => br %"v62" ? "iw_2.start" : "L7";
  @"iw_2.start":
    %"iw_2.v3" : P = Copy $"tcache";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_2.v3";
    %"iw_2.v4" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_2.v5" = %"iw_2.v4" +p #152;
    %"iw_2.v8" = %"iw_2.v5" +p %"v57";
    %"chk4" : A = (Check 0 8 Read 8) %"iw_2.v8";
    %"iw_2.iw_1.v13" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_2.iw_1.v26" : L = Ptoi %"iw_2.iw_1.v13";
    %"iw_2.iw_1.v35" : L = And %"iw_2.iw_1.v26", #15;
    %"iw_2.iw_1.v36" : W = (Cmp Ne L) %"iw_2.iw_1.v35", #0
    => br %"iw_2.iw_1.v36" ? "iw_2.iw_1.L22" : "iw_2.iw_1.L38";
  @"iw_2.iw_1.L22":
    %"iw_2.iw_1.v37" : P = Copy $"glibc_malloc#str.421";
    call void $"glibc_malloc#malloc_printerr"(P %"iw_2.iw_1.v37")
    => goto "iw_2.iw_1.L38";
  @"iw_2.iw_1.L38":
    %"iw_2.iw_1.v46" : L = Shr %"iw_2.iw_1.v26", #12;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_2.iw_1.v13";
    %"iw_2.iw_1.v48" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_2.iw_1.v49" : L = Ptoi %"iw_2.iw_1.v48";
    %"iw_2.iw_1.v50" : L = Xor %"iw_2.iw_1.v46", %"iw_2.iw_1.v49";
    (Flight (a "iw_2.iw_1.v51") Copy [(FValue (t "iw_2.iw_1.v50"))] LowerNone);
    %"chk6" : A = (Renew 0 8 Write 8) %"chk4", %"iw_2.v8";
    store.ptr [%"chk6" + 0] <- %"iw_2.iw_1.v51";
    %"iw_2.iw_1.v67" : P = Copy $"tcache";
    %"chk7" : A = (Check 0 8 Read 8) %"iw_2.iw_1.v67";
    %"iw_2.iw_1.v68" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_2.iw_1.v70" : L = Shl %"v42", #1;
    %"iw_2.iw_1.v71" = %"iw_2.iw_1.v68" +p %"iw_2.iw_1.v70";
    %"chk8" : A = (Check 0 2 Read 1) %"iw_2.iw_1.v71";
    %"iw_2.iw_1.v72" : W = (RawLoad (LdNarrow Uh) 0) %"chk8";
    %"iw_2.iw_1.v73" : W = Add %"iw_2.iw_1.v72", #1;
    %"iw_2.iw_1.v74" : W = (Ext Uh) %"iw_2.iw_1.v73";
    %"chk9" : A = (Renew 0 2 Write 1) %"chk8", %"iw_2.iw_1.v71";
    store Wh [%"chk9" + 0] <- %"iw_2.iw_1.v74";
    %"iw_2.iw_1.v76" = %"iw_2.iw_1.v13" +p #8;
    %"chk10" : A = (HalfCheck Upper 0 8 Write 1) %"chk5", %"iw_2.iw_1.v76";
    store Wl [%"chk10" + 0] <- #0
    => ret %"iw_2.iw_1.v13";
  @"iw_3.start":
    %"iw_3.iw_1.iw_1.v6" : W = (Cmp Eq L) %"v4", #0
    => br %"iw_3.iw_1.iw_1.v6" ? "iw_3.iw_1.iw_1.L4" : "iw_3.iw_1.iw_1.L3";
  @"iw_3.iw_1.iw_1.L3":
    %"iw_3.iw_1.iw_1.v8" : L = Shr %"v4", #1;
    %"iw_3.iw_1.iw_1.v9" : L = Or %"v4", %"iw_3.iw_1.iw_1.v8";
    %"iw_3.iw_1.iw_1.v10" : L = Shr %"iw_3.iw_1.iw_1.v9", #2;
    %"iw_3.iw_1.iw_1.v11" : L = Or %"iw_3.iw_1.iw_1.v9", %"iw_3.iw_1.iw_1.v10";
    %"iw_3.iw_1.iw_1.v12" : L = Shr %"iw_3.iw_1.iw_1.v11", #4;
    %"iw_3.iw_1.iw_1.v13" : L = Or %"iw_3.iw_1.iw_1.v11", %"iw_3.iw_1.iw_1.v12";
    %"iw_3.iw_1.iw_1.v14" : L = Shr %"iw_3.iw_1.iw_1.v13", #8;
    %"iw_3.iw_1.iw_1.v15" : L = Or %"iw_3.iw_1.iw_1.v13", %"iw_3.iw_1.iw_1.v14";
    %"iw_3.iw_1.iw_1.v16" : L = Shr %"iw_3.iw_1.iw_1.v15", #16;
    %"iw_3.iw_1.iw_1.v17" : L = Or %"iw_3.iw_1.iw_1.v15", %"iw_3.iw_1.iw_1.v16";
    %"iw_3.iw_1.iw_1.v18" : L = Shr %"iw_3.iw_1.iw_1.v17", #32;
    %"iw_3.iw_1.iw_1.v19" : L = Or %"iw_3.iw_1.iw_1.v17", %"iw_3.iw_1.iw_1.v18";
    %"iw_3.iw_1.iw_1.v20" : L = Shr %"iw_3.iw_1.iw_1.v19", #1;
    %"iw_3.iw_1.iw_1.v21" : L = And %"iw_3.iw_1.iw_1.v20", #6148914691236517205;
    %"iw_3.iw_1.iw_1.v22" : L = Sub %"iw_3.iw_1.iw_1.v19", %"iw_3.iw_1.iw_1.v21";
    %"iw_3.iw_1.iw_1.v23" : L = And %"iw_3.iw_1.iw_1.v22", #3689348814741910323;
    %"iw_3.iw_1.iw_1.v24" : L = Shr %"iw_3.iw_1.iw_1.v22", #2;
    %"iw_3.iw_1.iw_1.v25" : L = And %"iw_3.iw_1.iw_1.v24", #3689348814741910323;
    %"iw_3.iw_1.iw_1.v26" : L = Add %"iw_3.iw_1.iw_1.v23", %"iw_3.iw_1.iw_1.v25";
    %"iw_3.iw_1.iw_1.v27" : L = Shr %"iw_3.iw_1.iw_1.v26", #4;
    %"iw_3.iw_1.iw_1.v28" : L = Add %"iw_3.iw_1.iw_1.v26", %"iw_3.iw_1.iw_1.v27";
    %"iw_3.iw_1.iw_1.v29" : L = And %"iw_3.iw_1.iw_1.v28", #1085102592571150095;
    %"iw_3.iw_1.iw_1.v30" : L = Mul %"iw_3.iw_1.iw_1.v29", #72340172838076673;
    %"iw_3.iw_1.iw_1.v31" : L = Shr %"iw_3.iw_1.iw_1.v30", #56;
    %"iw_3.iw_1.iw_1.v32" : L = Sub %"iw_3.iw_1.iw_1.v31", #64;
    %"iw_3.iw_1.iw_1.v33" : L = Neg %"iw_3.iw_1.iw_1.v32"
    => goto "iw_3.iw_1.iw_1.L4";
  @"iw_3.iw_1.iw_1.L4" [%"iw_3.iw_1.iw_1.v34" : W = phi("iw_3.iw_1.iw_1.L3" => %"iw_3.iw_1.iw_1.v33", "iw_3.start" => #64)]:
    %"iw_3.iw_1.v4" : W = Sub #64, %"iw_3.iw_1.iw_1.v34";
    %"iw_3.v35" : W = Sub %"iw_3.iw_1.v4", #11;
    %"iw_3.v36" : L = (Ext Uw) %"iw_3.v35";
    %"iw_3.v38" : L = Add %"iw_3.v36", #64;
    %"iw_4.iw_1.v9" : P = Copy $"tcache";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_4.iw_1.v9";
    %"iw_4.iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_4.iw_1.v11" = %"iw_4.iw_1.v10" +p #152;
    %"iw_4.iw_1.v13" : L = Shl %"iw_3.v38", #3;
    %"iw_4.iw_1.v14" = %"iw_4.iw_1.v11" +p %"iw_4.iw_1.v13";
    %"chk12" : A = (Check 0 8 Read 8) %"iw_4.iw_1.v14";
    %"iw_4.iw_1.v17" : P = (RawLoadPointer 0 load_effects) %"chk12"
    => goto "iw_4.iw_1.L18";
  @"iw_4.iw_1.L18" [%"iw_4.iw_1.pr.2" : P = phi("iw_4.iw_1.L19" => %"iw_4.iw_1.v51", "iw_3.iw_1.iw_1.L4" => %"iw_4.iw_1.v17"); %"iw_4.iw_1.pr.1" : P = phi("iw_4.iw_1.L19" => %"iw_4.iw_1.pr.2", "iw_3.iw_1.iw_1.L4" => %"iw_4.iw_1.v14"); %"iw_4.pr.1" : W = phi("iw_4.iw_1.L19" => #1, "iw_3.iw_1.iw_1.L4" => #0)]:
    %"iw_4.iw_1.v22" : L = Ptoi %"iw_4.iw_1.pr.2";
    %"iw_4.iw_1.v23" : L = Ptoi #0;
    %"iw_4.iw_1.v24" : W = (Cmp Ne L) %"iw_4.iw_1.v22", %"iw_4.iw_1.v23"
    => br %"iw_4.iw_1.v24" ? "iw_4.iw_1.L25" : "iw_4.iw_1.L26";
  @"iw_4.iw_1.L25":
    (Flight (a "iw_4.iw_1.v29") Sub [(FAddress (t "iw_4.iw_1.pr.2")); (FValue (Const 16))] (LowerOf (t "iw_4.iw_1.pr.2")));
    %"iw_4.iw_1.v30" = %"iw_4.iw_1.v29" +p #8;
    %"chk13" : A = (Check 0 8 Read 1) %"iw_4.iw_1.v30";
    %"iw_4.iw_1.v31" : L = (RawLoad LdL 0) %"chk13";
    %"iw_4.iw_1.v36" : L = And %"iw_4.iw_1.v31", #18446744073709551608;
    %"iw_4.iw_1.v38" : W = (Cmp Ult L) %"iw_4.iw_1.v36", %"v4"
    => goto "iw_4.iw_1.L26";
  @"iw_4.iw_1.L26" [%"iw_4.iw_1.v42" : W = phi("iw_4.iw_1.L18" => #0, "iw_4.iw_1.L25" => %"iw_4.iw_1.v38")]:
    => br %"iw_4.iw_1.v42" ? "iw_4.iw_1.L19" : "iw_4.iw_1.join";
  @"iw_4.iw_1.L19":
    %"iw_4.iw_1.v46" : L = Shr %"iw_4.iw_1.v22", #12;
    %"chk14" : A = (Check 0 8 Read 8) %"iw_4.iw_1.pr.2";
    %"iw_4.iw_1.v48" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"iw_4.iw_1.v49" : L = Ptoi %"iw_4.iw_1.v48";
    %"iw_4.iw_1.v50" : L = Xor %"iw_4.iw_1.v46", %"iw_4.iw_1.v49";
    (Flight (a "iw_4.iw_1.v51") Copy [(FValue (t "iw_4.iw_1.v50"))] LowerNone)
    => goto poll "iw_4.iw_1.L18";
  @"iw_4.iw_1.join":
    %"iw_4.v17" : W = (Cmp Eq L) %"iw_4.iw_1.v22", %"iw_4.iw_1.v23"
    => br %"iw_4.v17" ? "iw_4.L19" : "iw_4.L18";
  @"iw_4.L18":
    (Flight (a "iw_4.v23") Sub [(FAddress (t "iw_4.iw_1.pr.2")); (FValue (Const 16))] (LowerOf (t "iw_4.iw_1.pr.2")));
    %"iw_4.v24" = %"iw_4.v23" +p #8;
    %"chk15" : A = (Check 0 8 Read 1) %"iw_4.v24";
    %"iw_4.v25" : L = (RawLoad LdL 0) %"chk15";
    %"iw_4.v30" : L = And %"iw_4.v25", #18446744073709551608;
    %"iw_4.v31" : W = (Cmp Ne L) %"v4", %"iw_4.v30"
    => goto "iw_4.L19";
  @"iw_4.L19" [%"iw_4.v33" : W = phi("iw_4.iw_1.join" => #1, "iw_4.L18" => %"iw_4.v31")]:
    => br %"iw_4.v33" ? "iw_4.join" : "iw_4.iw_2.start";
  @"iw_4.iw_2.start":
    => br %"iw_4.pr.1" ? "iw_4.iw_2.L8" : "iw_4.iw_2.L7";
  @"iw_4.iw_2.L7":
    %"chk16" : A = (Check 0 8 Read 8) %"iw_4.iw_1.pr.1";
    %"iw_4.iw_2.v13" : P = (RawLoadPointer 0 load_effects) %"chk16"
    => goto "iw_4.iw_2.L9";
  @"iw_4.iw_2.L8":
    %"iw_4.iw_2.v15" : L = Ptoi %"iw_4.iw_1.pr.1";
    %"iw_4.iw_2.v16" : L = Shr %"iw_4.iw_2.v15", #12;
    %"chk17" : A = (Check 0 8 Read 8) %"iw_4.iw_1.pr.1";
    %"iw_4.iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_4.iw_2.v19" : L = Ptoi %"iw_4.iw_2.v18";
    %"iw_4.iw_2.v20" : L = Xor %"iw_4.iw_2.v16", %"iw_4.iw_2.v19";
    (Flight (a "iw_4.iw_2.v21") Copy [(FValue (t "iw_4.iw_2.v20"))] LowerNone)
    => goto "iw_4.iw_2.L9";
  @"iw_4.iw_2.L9" [%"iw_4.iw_2.pr.1" : P = phi("iw_4.iw_2.L7" => %"iw_4.iw_2.v13", "iw_4.iw_2.L8" => %"iw_4.iw_2.v21")]:
    %"iw_4.iw_2.v26" : L = Ptoi %"iw_4.iw_2.pr.1";
    %"iw_4.iw_2.v35" : L = And %"iw_4.iw_2.v26", #15;
    %"iw_4.iw_2.v36" : W = (Cmp Ne L) %"iw_4.iw_2.v35", #0
    => br %"iw_4.iw_2.v36" ? "iw_4.iw_2.L22" : "iw_4.iw_2.L24";
  @"iw_4.iw_2.L22":
    %"iw_4.iw_2.v37" : P = Copy $"glibc_malloc#str.421";
    call void $"glibc_malloc#malloc_printerr"(P %"iw_4.iw_2.v37")
    => goto "iw_4.iw_2.L24";
  @"iw_4.iw_2.L24":
    => br %"iw_4.pr.1" ? "iw_4.iw_2.L39" : "iw_4.iw_2.L38";
  @"iw_4.iw_2.L38":
    %"iw_4.iw_2.v46" : L = Shr %"iw_4.iw_2.v26", #12;
    %"chk18" : A = (Check 0 8 Read 8) %"iw_4.iw_2.pr.1";
    %"iw_4.iw_2.v48" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"iw_4.iw_2.v49" : L = Ptoi %"iw_4.iw_2.v48";
    %"iw_4.iw_2.v50" : L = Xor %"iw_4.iw_2.v46", %"iw_4.iw_2.v49";
    (Flight (a "iw_4.iw_2.v51") Copy [(FValue (t "iw_4.iw_2.v50"))] LowerNone);
    %"chk19" : A = (Check 0 8 Write 8) %"iw_4.iw_1.pr.1";
    store.ptr [%"chk19" + 0] <- %"iw_4.iw_2.v51"
    => goto "iw_4.iw_2.L40";
  @"iw_4.iw_2.L39":
    %"iw_4.iw_2.v54" : L = Ptoi %"iw_4.iw_1.pr.1";
    %"iw_4.iw_2.v55" : L = Shr %"iw_4.iw_2.v54", #12;
    %"iw_4.iw_2.v58" : L = Shr %"iw_4.iw_2.v26", #12;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_4.iw_2.pr.1";
    %"iw_4.iw_2.v60" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_4.iw_2.v61" : L = Ptoi %"iw_4.iw_2.v60";
    %"iw_4.iw_2.v62" : L = Xor %"iw_4.iw_2.v58", %"iw_4.iw_2.v61";
    (Flight (a "iw_4.iw_2.v63") Copy [(FValue (t "iw_4.iw_2.v62"))] LowerNone);
    %"iw_4.iw_2.v64" : L = Ptoi %"iw_4.iw_2.v63";
    %"iw_4.iw_2.v65" : L = Xor %"iw_4.iw_2.v55", %"iw_4.iw_2.v64";
    (Flight (a "iw_4.iw_2.v66") Copy [(FValue (t "iw_4.iw_2.v65"))] LowerNone);
    %"chk21" : A = (Check 0 8 Write 8) %"iw_4.iw_1.pr.1";
    store.ptr [%"chk21" + 0] <- %"iw_4.iw_2.v66"
    => goto "iw_4.iw_2.L40";
  @"iw_4.iw_2.L40":
    %"iw_4.iw_2.v67" : P = Copy $"tcache";
    %"chk22" : A = (Check 0 8 Read 8) %"iw_4.iw_2.v67";
    %"iw_4.iw_2.v68" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_4.iw_2.v70" : L = Shl %"iw_3.v38", #1;
    %"iw_4.iw_2.v71" = %"iw_4.iw_2.v68" +p %"iw_4.iw_2.v70";
    %"chk23" : A = (Check 0 2 Read 1) %"iw_4.iw_2.v71";
    %"iw_4.iw_2.v72" : W = (RawLoad (LdNarrow Uh) 0) %"chk23";
    %"iw_4.iw_2.v73" : W = Add %"iw_4.iw_2.v72", #1;
    %"iw_4.iw_2.v74" : W = (Ext Uh) %"iw_4.iw_2.v73";
    %"chk24" : A = (Renew 0 2 Write 1) %"chk23", %"iw_4.iw_2.v71";
    store Wh [%"chk24" + 0] <- %"iw_4.iw_2.v74";
    %"iw_4.iw_2.v76" = %"iw_4.iw_2.pr.1" +p #8;
    %"chk25" : A = (Check 0 8 Write 1) %"iw_4.iw_2.v76";
    store Wl [%"chk25" + 0] <- #0
    => goto "iw_4.join";
  @"iw_4.join" [%"v71" : P = phi("iw_4.iw_2.L40" => %"iw_4.iw_2.pr.1", "iw_4.L19" => #0)]:
    %"v76" : L = Ptoi %"v71";
    %"v78" : W = (Cmp Ne L) %"v76", %"iw_4.iw_1.v23"
    => br %"v78" ? "L72" : "L7";
  @"L72":
    => ret %"v71";
  @"L7":
    call %"v82" : P = $"glibc_malloc#__libc_malloc2"(L %"v0")
    => ret %"v82"
} }.

Definition fn___GI___libc_realloc : func :=
  ir_fn{ "export" "__GI___libc_realloc"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    call %"v9" : P = $"zgc_realloc"(P %"v0", L %"v2")
    => ret %"v9"
} }.

Definition fn___libc_calloc : func :=
  ir_fn{ "export" "__libc_calloc"(L %"v0", L %"v2") -> (RClass P) {
  @"start":
    %"v10" : L = Mul %"v0", %"v2";
    %"v11" : L = And %"v0", #4294967295;
    %"v12" : L = Shr %"v0", #32;
    %"v13" : L = And %"v2", #4294967295;
    %"v14" : L = Shr %"v2", #32;
    %"v15" : L = Mul %"v11", %"v13";
    %"v16" : L = Mul %"v12", %"v13";
    %"v17" : L = Mul %"v11", %"v14";
    %"v18" : L = Mul %"v12", %"v14";
    %"v19" : L = Shr %"v15", #32;
    %"v20" : L = And %"v16", #4294967295;
    %"v21" : L = And %"v17", #4294967295;
    %"v22" : L = Add %"v19", %"v20";
    %"v23" : L = Add %"v22", %"v21";
    %"v24" : L = Shr %"v23", #32;
    %"v25" : L = Shr %"v16", #32;
    %"v26" : L = Shr %"v17", #32;
    %"v27" : L = Add %"v18", %"v25";
    %"v28" : L = Add %"v27", %"v26";
    %"v29" : L = Add %"v28", %"v24";
    %"v35" : W = (Cmp Ne L) %"v29", #0
    => br %"v35" ? "L5" : "L41";
  @"L5":
    %"v39" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v39";
    store Ww [%"chk0" + 0] <- #12
    => ret #0;
  @"L41":
    %"v45" : P = (Alloc 16) %"v10"
    => ret %"v45"
} }.

Definition fn___ptmalloc_init : func :=
  ir_fn{ "export" "__ptmalloc_init"() -> RVoid {
  @"start":
    %"v12" : P = (Alloc 8) #8;
    %"v17" : P = (Alloc 4) #4;
    %"v22" : P = (Alloc 8) #8;
    %"v27" : P = (Alloc 8) #8;
    %"v32" : P = (Alloc 4) #4;
    %"v37" : P = (Alloc 8) #8;
    %"v42" : P = (Alloc 8) #8;
    %"v47" : P = (Alloc 8) #8;
    %"v52" : P = (Alloc 8) #8;
    %"v57" : P = (Alloc 8) #8;
    %"iw_1.v3" : P = Copy $"glibc_malloc#tcache_key";
    %"iw_1.iw_1.v7" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"iw_1.iw_1.v13" : L = $"zsys_getrandom"(P %"iw_1.v3", L #8, W #1);
    %"iw_1.iw_1.v14" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.iw_1.v14";
    store Ww [%"chk1" + 0] <- %"iw_1.iw_1.v8";
    %"iw_1.v5" : W = (Cmp Ne L) %"iw_1.iw_1.v13", #8
    => br %"iw_1.v5" ? "iw_1.L0" : "iw_1.L12";
  @"iw_1.L0":
    %"iw_1.v6" : P = Copy $"glibc_malloc#tcache_key";
    %"chk2" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk2" + 0] <- #0
    => goto "iw_1.L12";
  @"iw_1.L12":
    %"iw_1.v15" : P = Copy $"glibc_malloc#tcache_key";
    %"chk3" : A = (Check 0 8 Read 1) %"iw_1.v15";
    %"iw_1.v16" : L = (RawLoad LdL 0) %"chk3";
    %"iw_1.v17" : W = (Cmp Ule L) %"iw_1.v16", #16777216
    => br %"iw_1.v17" ? "iw_1.L19" : "iw_1.L18";
  @"iw_1.L18":
    %"iw_1.v20" : P = Copy $"glibc_malloc#tcache_key";
    %"chk4" : A = (Check 0 8 Read 1) %"iw_1.v20";
    %"iw_1.v21" : L = (RawLoad LdL 0) %"chk4";
    %"iw_1.v25" : W = (Cmp Uge L) %"iw_1.v21", #18446744073692774399
    => goto "iw_1.L19";
  @"iw_1.L19" [%"iw_1.v27" : W = phi("iw_1.L12" => #1, "iw_1.L18" => %"iw_1.v25")]:
    => br %"iw_1.v27" ? "iw_1.L29" : "iw_1.L28";
  @"iw_1.L28":
    %"iw_1.v30" : P = Copy $"glibc_malloc#tcache_key";
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.v30";
    %"iw_1.v31" : L = (RawLoad LdL 0) %"chk5";
    %"iw_1.iw_2.v3" : L = Shr %"iw_1.v31", #1;
    %"iw_1.iw_2.v4" : L = And %"iw_1.iw_2.v3", #6148914691236517205;
    %"iw_1.iw_2.v5" : L = Sub %"iw_1.v31", %"iw_1.iw_2.v4";
    %"iw_1.iw_2.v6" : L = And %"iw_1.iw_2.v5", #3689348814741910323;
    %"iw_1.iw_2.v7" : L = Shr %"iw_1.iw_2.v5", #2;
    %"iw_1.iw_2.v8" : L = And %"iw_1.iw_2.v7", #3689348814741910323;
    %"iw_1.iw_2.v9" : L = Add %"iw_1.iw_2.v6", %"iw_1.iw_2.v8";
    %"iw_1.iw_2.v10" : L = Shr %"iw_1.iw_2.v9", #4;
    %"iw_1.iw_2.v11" : L = Add %"iw_1.iw_2.v9", %"iw_1.iw_2.v10";
    %"iw_1.iw_2.v12" : L = And %"iw_1.iw_2.v11", #1085102592571150095;
    %"iw_1.iw_2.v13" : L = Mul %"iw_1.iw_2.v12", #72340172838076673;
    %"iw_1.iw_2.v14" : L = Shr %"iw_1.iw_2.v13", #56
    => goto "iw_1.iw_2.join";
  @"iw_1.iw_2.join" [%"iw_1.v32" : W = phi("iw_1.L28" => %"iw_1.iw_2.v14")]:
    %"iw_1.v34" : W = (Cmp Ult W) %"iw_1.v32", #16
    => goto "iw_1.L29";
  @"iw_1.L29" [%"iw_1.v36" : W = phi("iw_1.L19" => #1, "iw_1.iw_2.join" => %"iw_1.v34")]:
    => br %"iw_1.v36" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v39" : P = Copy $"glibc_malloc#tcache_key";
    %"chk6" : A = (Check 0 8 Read 1) %"iw_1.v39";
    %"iw_1.v40" : L = (RawLoad LdL 0) %"chk6";
    %"iw_1.iw_3.v3" : L = Shr %"iw_1.v40", #1;
    %"iw_1.iw_3.v4" : L = And %"iw_1.iw_3.v3", #6148914691236517205;
    %"iw_1.iw_3.v5" : L = Sub %"iw_1.v40", %"iw_1.iw_3.v4";
    %"iw_1.iw_3.v6" : L = And %"iw_1.iw_3.v5", #3689348814741910323;
    %"iw_1.iw_3.v7" : L = Shr %"iw_1.iw_3.v5", #2;
    %"iw_1.iw_3.v8" : L = And %"iw_1.iw_3.v7", #3689348814741910323;
    %"iw_1.iw_3.v9" : L = Add %"iw_1.iw_3.v6", %"iw_1.iw_3.v8";
    %"iw_1.iw_3.v10" : L = Shr %"iw_1.iw_3.v9", #4;
    %"iw_1.iw_3.v11" : L = Add %"iw_1.iw_3.v9", %"iw_1.iw_3.v10";
    %"iw_1.iw_3.v12" : L = And %"iw_1.iw_3.v11", #1085102592571150095;
    %"iw_1.iw_3.v13" : L = Mul %"iw_1.iw_3.v12", #72340172838076673;
    %"iw_1.iw_3.v14" : L = Shr %"iw_1.iw_3.v13", #56
    => goto "iw_1.iw_3.join";
  @"iw_1.iw_3.join" [%"iw_1.v41" : W = phi("iw_1.L37" => %"iw_1.iw_3.v14")]:
    %"iw_1.v43" : W = (Cmp Ugt W) %"iw_1.v41", #48
    => goto "iw_1.L38";
  @"iw_1.L38" [%"iw_1.v45" : W = phi("iw_1.L29" => #1, "iw_1.iw_3.join" => %"iw_1.v43")]:
    => br %"iw_1.v45" ? "iw_1.L13" : "iw_1.join";
  @"iw_1.L13":
    %"iw_1.v46" : P = Copy $"glibc_malloc#tcache_key";
    %"iw_1.iw_4.v0" : P = (Alloc 8) #16;
    call %"iw_1.iw_4.v1" : W = $"__GI___clock_gettime"(W #1, P %"iw_1.iw_4.v0");
    %"iw_1.iw_4.v3" = %"iw_1.iw_4.v0" +p #8;
    %"chk7" : A = (Check 0 8 Read 1) %"iw_1.iw_4.v3";
    %"iw_1.iw_4.v4" : L = (RawLoad LdL 0) %"chk7";
    %"chk8" : A = (HalfCheck Lower 0 8 Read 1) %"chk7", %"iw_1.iw_4.v0";
    %"iw_1.iw_4.v5" : L = (RawLoad LdL 0) %"chk8";
    %"iw_1.iw_4.v6" : L = Xor %"iw_1.iw_4.v4", %"iw_1.iw_4.v5";
    %"iw_1.iw_4.v7" : W = Copy %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v8" : W = Copy %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v9" : W = Shl %"iw_1.iw_4.v8", #24;
    %"iw_1.iw_4.v10" : W = Copy %"iw_1.iw_4.v6";
    %"iw_1.iw_4.v11" : W = Shr %"iw_1.iw_4.v10", #8;
    %"iw_1.iw_4.v12" : W = Or %"iw_1.iw_4.v9", %"iw_1.iw_4.v11";
    %"iw_1.iw_4.v13" : W = Xor %"iw_1.iw_4.v7", %"iw_1.iw_4.v12";
    %"iw_1.v48" : L = (Ext Uw) %"iw_1.iw_4.v13";
    %"chk9" : A = (Check 0 8 Write 1) %"iw_1.v46";
    store Wl [%"chk9" + 0] <- %"iw_1.v48";
    %"iw_1.v49" : P = Copy $"glibc_malloc#tcache_key";
    %"iw_1.v50" : P = Copy $"glibc_malloc#tcache_key";
    %"chk10" : A = (Check 0 8 Read 1) %"iw_1.v50";
    %"iw_1.v51" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v52" : L = Shl %"iw_1.v51", #32;
    %"iw_1.iw_5.v0" : P = (Alloc 8) #16;
    call %"iw_1.iw_5.v1" : W = $"__GI___clock_gettime"(W #1, P %"iw_1.iw_5.v0");
    %"iw_1.iw_5.v3" = %"iw_1.iw_5.v0" +p #8;
    %"chk11" : A = (Check 0 8 Read 1) %"iw_1.iw_5.v3";
    %"iw_1.iw_5.v4" : L = (RawLoad LdL 0) %"chk11";
    %"chk12" : A = (HalfCheck Lower 0 8 Read 1) %"chk11", %"iw_1.iw_5.v0";
    %"iw_1.iw_5.v5" : L = (RawLoad LdL 0) %"chk12";
    %"iw_1.iw_5.v6" : L = Xor %"iw_1.iw_5.v4", %"iw_1.iw_5.v5";
    %"iw_1.iw_5.v7" : W = Copy %"iw_1.iw_5.v6";
    %"iw_1.iw_5.v8" : W = Copy %"iw_1.iw_5.v6";
    %"iw_1.iw_5.v9" : W = Shl %"iw_1.iw_5.v8", #24;
    %"iw_1.iw_5.v10" : W = Copy %"iw_1.iw_5.v6";
    %"iw_1.iw_5.v11" : W = Shr %"iw_1.iw_5.v10", #8;
    %"iw_1.iw_5.v12" : W = Or %"iw_1.iw_5.v9", %"iw_1.iw_5.v11";
    %"iw_1.iw_5.v13" : W = Xor %"iw_1.iw_5.v7", %"iw_1.iw_5.v12";
    %"iw_1.v54" : L = (Ext Uw) %"iw_1.iw_5.v13";
    %"iw_1.v55" : L = Or %"iw_1.v52", %"iw_1.v54";
    %"chk13" : A = (Check 0 8 Write 1) %"iw_1.v49";
    store Wl [%"chk13" + 0] <- %"iw_1.v55"
    => goto poll "iw_1.L12";
  @"iw_1.join":
    %"v3" : P = Copy $"__libc_initial";
    %"chk14" : A = (Check 0 1 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => br %"v5" ? "L0" : "L2";
  @"L0":
    %"v6" : P = Copy $"glibc_malloc#__always_fail_morecore";
    %"chk15" : A = (Check 0 1 Write 1) %"v6";
    store Wb [%"chk15" + 0] <- #1
    => goto "L2";
  @"L2":
    %"v8" : P = Copy $"thread_arena";
    %"v9" : P = Copy $"glibc_malloc#main_arena";
    %"chk16" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk16" + 0] <- %"v9";
    %"v10" : P = Copy $"glibc_malloc#main_arena"
    => goto "iw_2.L4";
  @"iw_2.L4" [%"iw_2.pr.1" : W = phi("iw_2.L5" => %"iw_2.v25", "L2" => #1)]:
    %"iw_2.v9" : W = (Cmp Slt W) %"iw_2.pr.1", #128
    => br %"iw_2.v9" ? "iw_2.L5" : "iw_2.L7";
  @"iw_2.L5":
    %"iw_2.v11" = %"v10" +p #24;
    %"iw_2.v13" : W = Sub %"iw_2.pr.1", #1;
    %"iw_2.v14" : W = Shl %"iw_2.v13", #1;
    %"iw_2.v15" : L = (Ext Sw) %"iw_2.v14";
    %"iw_2.v16" : L = Shl %"iw_2.v15", #3;
    %"iw_2.v17" = %"iw_2.v11" +p %"iw_2.v16";
    (Flight (a "iw_2.v18") Sub [(FAddress (t "iw_2.v17")); (FValue (Const 16))] (LowerOf (t "iw_2.v17")));
    %"iw_2.v20" = %"iw_2.v18" +p #16;
    %"iw_2.v22" = %"iw_2.v18" +p #24;
    %"chk17" : A = (Check 0 8 Write 8) %"iw_2.v22";
    store.ptr [%"chk17" + 0] <- %"iw_2.v18";
    %"chk18" : A = (HalfCheck Lower 0 8 Write 8) %"chk17", %"iw_2.v20";
    store.ptr [%"chk18" + 0] <- %"iw_2.v18";
    %"iw_2.v25" : W = Add %"iw_2.pr.1", #1
    => goto poll "iw_2.L4";
  @"iw_2.L7":
    %"iw_2.v30" : P = Copy $"glibc_malloc#main_arena";
    %"iw_2.v31" : L = Ptoi %"v10";
    %"iw_2.v32" : L = Ptoi %"iw_2.v30";
    %"iw_2.v33" : W = (Cmp Ne L) %"iw_2.v31", %"iw_2.v32"
    => br %"iw_2.v33" ? "iw_2.L26" : "iw_2.L28";
  @"iw_2.L26":
    %"iw_2.v35" = %"v10" +p #4;
    %"chk19" : A = (Check 0 4 Read 1) %"iw_2.v35";
    %"iw_2.v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"iw_2.v37" : W = Or %"iw_2.v36", #2;
    %"chk20" : A = (Renew 0 4 Write 1) %"chk19", %"iw_2.v35";
    store Ww [%"chk20" + 0] <- %"iw_2.v37"
    => goto "iw_2.L28";
  @"iw_2.L28":
    %"iw_2.v39" = %"v10" +p #8;
    %"iw_2.v41" = %"v10" +p #24;
    (Flight (a "iw_2.v47") Sub [(FAddress (t "iw_2.v41")); (FValue (Const 16))] (LowerOf (t "iw_2.v41")));
    %"chk21" : A = (Check 0 8 Write 8) %"iw_2.v39";
    store.ptr [%"chk21" + 0] <- %"iw_2.v47";
    %"v14" : P = Copy $"glibc_malloc#_dl_tunable_set_top_pad";
    call void $"__tunable_get_val"(W #24, P %"v12", P %"v14");
    %"chk22" : A = (Check 0 8 Read 1) %"v12";
    %"v15" : L = (RawLoad LdL 0) %"chk22";
    %"v19" : P = Copy $"glibc_malloc#_dl_tunable_set_perturb_byte";
    call void $"__tunable_get_val"(W #21, P %"v17", P %"v19");
    %"chk23" : A = (Check 0 4 Read 1) %"v17";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v24" : P = Copy $"glibc_malloc#_dl_tunable_set_mmap_threshold";
    call void $"__tunable_get_val"(W #19, P %"v22", P %"v24");
    %"chk24" : A = (Check 0 8 Read 1) %"v22";
    %"v25" : L = (RawLoad LdL 0) %"chk24";
    %"v29" : P = Copy $"glibc_malloc#_dl_tunable_set_trim_threshold";
    call void $"__tunable_get_val"(W #25, P %"v27", P %"v29");
    %"chk25" : A = (Check 0 8 Read 1) %"v27";
    %"v30" : L = (RawLoad LdL 0) %"chk25";
    %"v34" : P = Copy $"glibc_malloc#_dl_tunable_set_mmaps_max";
    call void $"__tunable_get_val"(W #18, P %"v32", P %"v34");
    %"chk26" : A = (Check 0 4 Read 1) %"v32";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v39" : P = Copy $"glibc_malloc#_dl_tunable_set_arena_max";
    call void $"__tunable_get_val"(W #14, P %"v37", P %"v39");
    %"chk27" : A = (Check 0 8 Read 1) %"v37";
    %"v40" : L = (RawLoad LdL 0) %"chk27";
    %"v44" : P = Copy $"glibc_malloc#_dl_tunable_set_arena_test";
    call void $"__tunable_get_val"(W #15, P %"v42", P %"v44");
    %"chk28" : A = (Check 0 8 Read 1) %"v42";
    %"v45" : L = (RawLoad LdL 0) %"chk28";
    %"v49" : P = Copy $"glibc_malloc#_dl_tunable_set_tcache_max";
    call void $"__tunable_get_val"(W #23, P %"v47", P %"v49");
    %"chk29" : A = (Check 0 8 Read 1) %"v47";
    %"v50" : L = (RawLoad LdL 0) %"chk29";
    %"v54" : P = Copy $"glibc_malloc#_dl_tunable_set_tcache_count";
    call void $"__tunable_get_val"(W #22, P %"v52", P %"v54");
    %"chk30" : A = (Check 0 8 Read 1) %"v52";
    %"v55" : L = (RawLoad LdL 0) %"chk30";
    %"v59" : P = Copy $"glibc_malloc#_dl_tunable_set_hugetlb";
    call void $"__tunable_get_val"(W #17, P %"v57", P %"v59");
    %"chk31" : A = (Check 0 8 Read 1) %"v57";
    %"v60" : L = (RawLoad LdL 0) %"chk31";
    %"v64" : P = Copy $"glibc_malloc#mp_";
    %"v65" = %"v64" +p #56;
    %"chk32" : A = (Check 0 8 Read 1) %"v65";
    %"v66" : L = (RawLoad LdL 0) %"chk32";
    %"v67" : W = (Cmp Ugt L) %"v66", #0
    => br %"v67" ? "L68" : "L69";
  @"L68":
    %"v70" : P = Copy $"glibc_malloc#mp_";
    %"v71" = %"v70" +p #56;
    %"chk33" : A = (Check 0 8 Read 1) %"v71";
    %"v72" : L = (RawLoad LdL 0) %"chk33";
    %"v74" : W = (Cmp Ule L) %"v72", #67108864
    => goto "L69";
  @"L69" [%"v76" : W = phi("iw_2.L28" => #0, "L68" => %"v74")]:
    => br %"v76" ? "L61" : "L63";
  @"L61":
    call %"v82" : W = $"__tunable_is_initialized"(W #19);
    %"v83" : W = (Ext Ub) %"v82";
    %"v84" : W = (Cmp Eq W) %"v83", #0
    => br %"v84" ? "L77" : "L79";
  @"L77":
    %"v85" : P = Copy $"glibc_malloc#mp_";
    %"v86" = %"v85" +p #56;
    %"chk34" : A = (Check 0 8 Read 1) %"v86";
    %"v87" : L = (RawLoad LdL 0) %"chk34";
    %"iw_4.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_4.v6" = %"iw_4.v5" +p #16;
    %"chk35" : A = (Check 0 8 Write 1) %"iw_4.v6";
    store Wl [%"chk35" + 0] <- %"v87";
    %"iw_4.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_4.v9" = %"iw_4.v8" +p #80;
    %"chk36" : A = (Check 0 4 Write 1) %"iw_4.v9";
    store Ww [%"chk36" + 0] <- #1
    => goto "L79";
  @"L79":
    %"v89" : P = Copy $"glibc_malloc#__always_fail_morecore";
    %"chk37" : A = (Check 0 1 Write 1) %"v89";
    store Wb [%"chk37" + 0] <- #1
    => goto "L63";
  @"L63":
    => ret void
} }.

Definition item_calloc : item :=
  (IAlias (a "calloc") (a "weak") (a "__libc_calloc")).

Definition item_free : item :=
  (IAlias (a "free") (a "export") (a "__GI___libc_free")).

Definition item_glibc_malloc'23__always_fail_morecore : item :=
  (IData (a "glibc_malloc#__always_fail_morecore") LLocal 1 [(Item Wb 0)]).

Definition fn_glibc_malloc'23__libc_malloc2 : func :=
  ir_fn{ "local" "glibc_malloc#__libc_malloc2"(L %"v0") -> (RClass P) {
  @"start":
    %"v6" : P = (Alloc 16) %"v0"
    => ret %"v6"
} }.

Definition item_glibc_malloc'23__tcache_dummy : item :=
  (IData (a "glibc_malloc#__tcache_dummy") (LRo (a "local")) 8 [(Zero 768)]).

Definition fn_glibc_malloc'23_dl_tunable_set_arena_max : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_arena_max"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #32;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4"
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_arena_test : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_arena_test"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #24;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4"
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_hugetlb : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_hugetlb"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.iw_1.v0" : P = Copy $"_dl_thp_mode";
    %"chk1" : A = (Check 0 4 Read 1) %"iw_1.iw_1.v0";
    %"iw_1.iw_1.v1" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"iw_1.v24" : W = (Cmp Eq L) %"v4", #0
    => br %"iw_1.v24" ? "iw_1.L20" : "iw_1.L21";
  @"iw_1.L20":
    %"iw_1.v25" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v26" = %"iw_1.v25" +p #40;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v26";
    store Ww [%"chk2" + 0] <- #4;
    %"iw_1.v27" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v28" = %"iw_1.v27" +p #48;
    %"chk3" : A = (Check 0 8 Write 1) %"iw_1.v28";
    store Wl [%"chk3" + 0] <- #0
    => goto "iw_1.join";
  @"iw_1.L21":
    %"iw_1.v33" : W = (Cmp Eq L) %"v4", #1
    => br %"iw_1.v33" ? "iw_1.L36" : "iw_1.L30";
  @"iw_1.L36":
    %"iw_1.v43" : W = (Cmp Eq W) %"iw_1.iw_1.v1", #0
    => br %"iw_1.v43" ? "iw_1.L39" : "iw_1.L40";
  @"iw_1.L39":
    %"iw_1.v44" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v45" = %"iw_1.v44" +p #40;
    call %"iw_1.v46" : W = $"__get_thp_mode"();
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v45";
    store Ww [%"chk4" + 0] <- %"iw_1.v46";
    %"iw_1.v50" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v51" = %"iw_1.v50" +p #40;
    %"chk5" : A = (Check 0 4 Read 1) %"iw_1.v51";
    %"iw_1.v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"iw_1.v53" : W = (Cmp Eq W) %"iw_1.v52", #3
    => br %"iw_1.v53" ? "iw_1.L55" : "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v56" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v57" = %"iw_1.v56" +p #40;
    %"chk6" : A = (Check 0 4 Read 1) %"iw_1.v57";
    %"iw_1.v58" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_1.v59" : W = (Cmp Eq W) %"iw_1.v58", #2
    => goto "iw_1.L55";
  @"iw_1.L55" [%"iw_1.v61" : W = phi("iw_1.L39" => #1, "iw_1.L54" => %"iw_1.v59")]:
    => br %"iw_1.v61" ? "iw_1.L47" : "iw_1.join";
  @"iw_1.L47":
    %"iw_1.v62" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v63" = %"iw_1.v62" +p #48;
    call %"iw_1.v64" : L = $"__get_thp_size"();
    %"chk7" : A = (Check 0 8 Write 1) %"iw_1.v63";
    store Wl [%"chk7" + 0] <- %"iw_1.v64"
    => goto "iw_1.join";
  @"iw_1.L40":
    %"iw_1.v65" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v66" = %"iw_1.v65" +p #40;
    %"chk8" : A = (Check 0 4 Write 1) %"iw_1.v66";
    store Ww [%"chk8" + 0] <- %"iw_1.iw_1.v1";
    %"iw_1.v74" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v75" = %"iw_1.v74" +p #48;
    call %"iw_1.iw_2.v1" : L = $"__get_thp_size"();
    %"iw_1.iw_2.v9" : W = (Cmp Ugt L) %"iw_1.iw_2.v1", #33554432
    => br %"iw_1.iw_2.v9" ? "iw_1.iw_2.L4" : "iw_1.iw_2.L3";
  @"iw_1.iw_2.L3":
    => goto "iw_1.iw_2.L4";
  @"iw_1.iw_2.L4" [%"iw_1.iw_2.pr.1" : L = phi("iw_1.iw_2.L3" => %"iw_1.iw_2.v1", "iw_1.L40" => #0)]:
    %"chk9" : A = (Check 0 8 Write 1) %"iw_1.v75";
    store Wl [%"chk9" + 0] <- %"iw_1.iw_2.pr.1"
    => goto "iw_1.join";
  @"iw_1.L30":
    %"iw_1.v84" : W = (Cmp Uge L) %"v4", #2
    => br %"iw_1.v84" ? "iw_1.L80" : "iw_1.join";
  @"iw_1.L80":
    %"iw_1.v89" : W = (Cmp Eq L) %"v4", #2
    => br %"iw_1.v89" ? "iw_1.L87" : "iw_1.L86";
  @"iw_1.L86":
    => goto "iw_1.L87";
  @"iw_1.L87" [%"iw_1.v91" : L = phi("iw_1.L86" => %"v4", "iw_1.L80" => #0)]:
    %"iw_1.v92" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v93" = %"iw_1.v92" +p #56;
    %"iw_1.v94" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v95" = %"iw_1.v94" +p #64;
    call void $"__get_hugepage_config"(L %"iw_1.v91", P %"iw_1.v93", P %"iw_1.v95")
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_mmap_threshold : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_mmap_threshold"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #16;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4";
    %"iw_1.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v9" = %"iw_1.v8" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v9";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_mmaps_max : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_mmaps_max"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v5" : W = Copy %"v4";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #72;
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v6";
    store Ww [%"chk1" + 0] <- %"v5";
    %"iw_1.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v9" = %"iw_1.v8" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v9";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_perturb_byte : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_perturb_byte"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v5" : W = Copy %"v4";
    %"iw_1.v5" : P = Copy $"glibc_malloc#perturb_byte";
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v5";
    store Ww [%"chk1" + 0] <- %"v5"
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_tcache_count : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_tcache_count"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v6" : W = (Cmp Ule L) %"v4", #65535
    => br %"iw_1.v6" ? "iw_1.L9" : "iw_1.join";
  @"iw_1.L9":
    %"iw_1.v10" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v11" = %"iw_1.v10" +p #128;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v11";
    store Wl [%"chk1" + 0] <- %"v4"
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_tcache_max : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_tcache_max"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v6" : W = (Cmp Ugt L) %"v4", #9223372036854775807
    => br %"iw_1.v6" ? "iw_1.join" : "iw_1.iw_1.start";
  @"iw_1.iw_1.start":
    => br %"iw_1.v6" ? "iw_1.iw_1.join" : "iw_1.iw_1.L4";
  @"iw_1.iw_1.L4":
    %"iw_1.iw_1.v14" : L = Add %"v4", #8;
    %"iw_1.iw_1.v23" : L = Add %"iw_1.iw_1.v14", #15;
    %"iw_1.iw_1.v43" : W = (Cmp Ult L) %"iw_1.iw_1.v23", #32
    => br %"iw_1.iw_1.v43" ? "iw_1.iw_1.join" : "iw_1.iw_1.L76";
  @"iw_1.iw_1.L76":
    %"iw_1.iw_1.v83" : L = And %"iw_1.iw_1.v23", #18446744073709551600
    => goto "iw_1.iw_1.join";
  @"iw_1.iw_1.join" [%"iw_1.v10" : L = phi("iw_1.iw_1.start" => #18446744073709551615, "iw_1.iw_1.L4" => #32, "iw_1.iw_1.L76" => %"iw_1.iw_1.v83")]:
    %"iw_1.v32" : L = Sub %"iw_1.v10", #32;
    %"iw_1.v40" : L = Shr %"iw_1.v32", #4;
    %"iw_1.v45" : W = (Cmp Uge L) %"iw_1.v40", #64
    => br %"iw_1.v45" ? "iw_1.iw_2.start" : "iw_1.L43";
  @"iw_1.iw_2.start":
    %"iw_1.iw_2.iw_1.iw_1.v6" : W = (Cmp Eq L) %"iw_1.v10", #0
    => br %"iw_1.iw_2.iw_1.iw_1.v6" ? "iw_1.iw_2.iw_1.iw_1.L4" : "iw_1.iw_2.iw_1.iw_1.L3";
  @"iw_1.iw_2.iw_1.iw_1.L3":
    %"iw_1.iw_2.iw_1.iw_1.v8" : L = Shr %"iw_1.v10", #1;
    %"iw_1.iw_2.iw_1.iw_1.v9" : L = Or %"iw_1.v10", %"iw_1.iw_2.iw_1.iw_1.v8";
    %"iw_1.iw_2.iw_1.iw_1.v10" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v9", #2;
    %"iw_1.iw_2.iw_1.iw_1.v11" : L = Or %"iw_1.iw_2.iw_1.iw_1.v9", %"iw_1.iw_2.iw_1.iw_1.v10";
    %"iw_1.iw_2.iw_1.iw_1.v12" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v11", #4;
    %"iw_1.iw_2.iw_1.iw_1.v13" : L = Or %"iw_1.iw_2.iw_1.iw_1.v11", %"iw_1.iw_2.iw_1.iw_1.v12";
    %"iw_1.iw_2.iw_1.iw_1.v14" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v13", #8;
    %"iw_1.iw_2.iw_1.iw_1.v15" : L = Or %"iw_1.iw_2.iw_1.iw_1.v13", %"iw_1.iw_2.iw_1.iw_1.v14";
    %"iw_1.iw_2.iw_1.iw_1.v16" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v15", #16;
    %"iw_1.iw_2.iw_1.iw_1.v17" : L = Or %"iw_1.iw_2.iw_1.iw_1.v15", %"iw_1.iw_2.iw_1.iw_1.v16";
    %"iw_1.iw_2.iw_1.iw_1.v18" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v17", #32;
    %"iw_1.iw_2.iw_1.iw_1.v19" : L = Or %"iw_1.iw_2.iw_1.iw_1.v17", %"iw_1.iw_2.iw_1.iw_1.v18";
    %"iw_1.iw_2.iw_1.iw_1.v20" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v19", #1;
    %"iw_1.iw_2.iw_1.iw_1.v21" : L = And %"iw_1.iw_2.iw_1.iw_1.v20", #6148914691236517205;
    %"iw_1.iw_2.iw_1.iw_1.v22" : L = Sub %"iw_1.iw_2.iw_1.iw_1.v19", %"iw_1.iw_2.iw_1.iw_1.v21";
    %"iw_1.iw_2.iw_1.iw_1.v23" : L = And %"iw_1.iw_2.iw_1.iw_1.v22", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_1.v24" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v22", #2;
    %"iw_1.iw_2.iw_1.iw_1.v25" : L = And %"iw_1.iw_2.iw_1.iw_1.v24", #3689348814741910323;
    %"iw_1.iw_2.iw_1.iw_1.v26" : L = Add %"iw_1.iw_2.iw_1.iw_1.v23", %"iw_1.iw_2.iw_1.iw_1.v25";
    %"iw_1.iw_2.iw_1.iw_1.v27" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v26", #4;
    %"iw_1.iw_2.iw_1.iw_1.v28" : L = Add %"iw_1.iw_2.iw_1.iw_1.v26", %"iw_1.iw_2.iw_1.iw_1.v27";
    %"iw_1.iw_2.iw_1.iw_1.v29" : L = And %"iw_1.iw_2.iw_1.iw_1.v28", #1085102592571150095;
    %"iw_1.iw_2.iw_1.iw_1.v30" : L = Mul %"iw_1.iw_2.iw_1.iw_1.v29", #72340172838076673;
    %"iw_1.iw_2.iw_1.iw_1.v31" : L = Shr %"iw_1.iw_2.iw_1.iw_1.v30", #56;
    %"iw_1.iw_2.iw_1.iw_1.v32" : L = Sub %"iw_1.iw_2.iw_1.iw_1.v31", #64;
    %"iw_1.iw_2.iw_1.iw_1.v33" : L = Neg %"iw_1.iw_2.iw_1.iw_1.v32"
    => goto "iw_1.iw_2.iw_1.iw_1.L4";
  @"iw_1.iw_2.iw_1.iw_1.L4" [%"iw_1.iw_2.iw_1.iw_1.v34" : W = phi("iw_1.iw_2.iw_1.iw_1.L3" => %"iw_1.iw_2.iw_1.iw_1.v33", "iw_1.iw_2.start" => #64)]:
    %"iw_1.iw_2.iw_1.v4" : W = Sub #64, %"iw_1.iw_2.iw_1.iw_1.v34";
    %"iw_1.iw_2.v35" : W = Sub %"iw_1.iw_2.iw_1.v4", #11;
    %"iw_1.iw_2.v36" : L = (Ext Uw) %"iw_1.iw_2.v35";
    %"iw_1.iw_2.v38" : L = Add %"iw_1.iw_2.v36", #64
    => goto "iw_1.L43";
  @"iw_1.L43" [%"iw_1.pr.1" : L = phi("iw_1.iw_2.iw_1.iw_1.L4" => %"iw_1.iw_2.v38", "iw_1.iw_1.join" => %"iw_1.v40")]:
    %"iw_1.v57" : W = (Cmp Ult L) %"iw_1.pr.1", #76
    => br %"iw_1.v57" ? "iw_1.L51" : "iw_1.join";
  @"iw_1.L51":
    %"iw_1.v62" : W = (Cmp Ult L) %"iw_1.pr.1", #64
    => br %"iw_1.v62" ? "iw_1.L58" : "iw_1.L60";
  @"iw_1.L58":
    %"iw_1.v63" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v64" = %"iw_1.v63" +p #112;
    %"iw_1.v66" : L = Add %"iw_1.pr.1", #1;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v64";
    store Wl [%"chk1" + 0] <- %"iw_1.v66"
    => goto "iw_1.L60";
  @"iw_1.L60":
    %"iw_1.v67" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v68" = %"iw_1.v67" +p #120;
    %"iw_1.v70" : L = Add %"iw_1.v10", #1;
    %"chk2" : A = (Check 0 8 Write 1) %"iw_1.v68";
    store Wl [%"chk2" + 0] <- %"iw_1.v70"
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_top_pad : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_top_pad"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v6" = %"iw_1.v5" +p #8;
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v6";
    store Wl [%"chk1" + 0] <- %"v4";
    %"iw_1.v8" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v9" = %"iw_1.v8" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v9";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition fn_glibc_malloc'23_dl_tunable_set_trim_threshold : func :=
  ir_fn{ "local" "glibc_malloc#_dl_tunable_set_trim_threshold"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"iw_1.v5" : P = Copy $"glibc_malloc#mp_";
    %"chk1" : A = (Check 0 8 Write 1) %"iw_1.v5";
    store Wl [%"chk1" + 0] <- %"v4";
    %"iw_1.v7" : P = Copy $"glibc_malloc#mp_";
    %"iw_1.v8" = %"iw_1.v7" +p #80;
    %"chk2" : A = (Check 0 4 Write 1) %"iw_1.v8";
    store Ww [%"chk2" + 0] <- #1
    => ret void
} }.

Definition item_glibc_malloc'23main_arena : item :=
  (IData (a "glibc_malloc#main_arena") LLocal 8 [(Item Ww 0); (Zero 2068); (Sym (a "glibc_malloc#main_arena") 0); (Zero 8); (Item Wl 1); (Zero 16)]).

Definition fn_glibc_malloc'23malloc_printerr : func :=
  ir_fn{ "local" "glibc_malloc#malloc_printerr"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_malloc#str.407";
    %"v3" : P = Copy $"glibc_malloc#str.408";
    call void $"__libc_message_impl"(P %"v2", P %"v3", P %"v0")
    => unreachable
} }.

Definition item_glibc_malloc'23mp_ : item :=
  (IData (a "glibc_malloc#mp_") LLocal 8 [(Item Wl 131072); (Item Wl 131072); (Item Wl 131072); (Item Wl 8); (Zero 8); (Item Ww 0); (Zero 28); (Item Ww 65536); (Zero 36); (Item Wl 64); (Item Wl 1041); (Item Wl 16)]).

Definition item_glibc_malloc'23perturb_byte : item :=
  (IData (a "glibc_malloc#perturb_byte") LLocal 4 [(Zero 4)]).

Definition item_glibc_malloc'23str'2e407 : item :=
  (IData (a "glibc_malloc#str.407") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_malloc'23str'2e408 : item :=
  (IData (a "glibc_malloc#str.408") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_malloc'23str'2e421 : item :=
  (IData (a "glibc_malloc#str.421") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 40); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 116); (Item Wb 99); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 117); (Item Wb 110); (Item Wb 107); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_malloc'23tcache_key : item :=
  (IData (a "glibc_malloc#tcache_key") LLocal 8 [(Zero 8)]).

Definition item_malloc : item :=
  (IAlias (a "malloc") (a "export") (a "__GI___libc_malloc")).

Definition item_realloc : item :=
  (IAlias (a "realloc") (a "export") (a "__GI___libc_realloc")).

Definition item_tcache : item :=
  (IData (a "tcache") (LTls (a "local")) 8 [(Sym (a "glibc_malloc#__tcache_dummy") 0)]).

Definition item_thread_arena : item :=
  (IData (a "thread_arena") (LTls (a "local")) 8 [(Zero 8)]).

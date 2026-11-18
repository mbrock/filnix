(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_fn_glibc_malloc'23__libc_malloc2 : func :=
  ir_fn{ "local" "glibc_malloc#__libc_malloc2"(L %"v0") -> (RClass P) {
  @"start":
    %"v6" : P = (Alloc 16) %"v0"
    => ret %"v6"
} }.

Definition hi_fn___GI___libc_malloc : func :=
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

Definition hi_fn___GI___libc_free : func :=
  ir_fn{ "export" "__GI___libc_free"(P %"v0") -> RVoid {
  @"start":
    call void $"zgc_free"(P %"v0")
    => ret void
} }.

Definition hi_fn___libc_calloc : func :=
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

Definition hi_fn___GI___libc_write : func :=
  ir_fn{ "export" "__GI___libc_write"(W %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call %"v9" : L = $"zsys_write"(W %"v0", P %"v2", L %"v4")
    => ret %"v9"
} }.

Definition hi_fn___GI___libc_cleanup_push_defer : func :=
  ir_fn{ "export" "__GI___libc_cleanup_push_defer"(P %"v0") -> RVoid {
  @"start":
    call %"v3" : P = $"zthread_self_cookie"();
    %"v5" = %"v0" +p #24;
    %"v7" = %"v3" +p #776;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk1" + 0] <- %"v8";
    %"v11" = %"v3" +p #792;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v11";
    %"v12" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v18" : W = And %"v12", #2;
    %"v19" : L = (Ext Sw) %"v18";
    %"v20" : W = (Cmp Ne L) %"v19", #0
    => br %"v20" ? "L22" : "L15";
  @"L22" [%"pr.2" : W = phi("L36" => %"pr.3", "start" => %"v12")]:
    %"v28" : W = And %"pr.2", #4294967293;
    %"v30" = %"v3" +p #792;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 4) %"chk0", %"v30";
    %"v33" : W = (RawCas (CasNarrow Sw) 0) %"chk3", %"pr.2", %"v28";
    %"v34" : W = (Cmp Eq W) %"v33", %"pr.2"
    => br %"v34" ? "L36" : "L35";
  @"L35":
    => goto "L36";
  @"L36" [%"pr.3" : W = phi("L22" => %"pr.2", "L35" => %"v33")]:
    %"v37" : W = (Cmp Ne W) %"v33", %"pr.2"
    => br %"v37" ? poll "L22" : "L15";
  @"L15" [%"pr.1" : W = phi("L36" => %"pr.3", "start" => %"v12")]:
    %"v39" = %"v0" +p #16;
    %"v45" : W = And %"pr.1", #2
    => br %"v45" ? "L42" : "L41";
  @"L41":
    => goto "L42";
  @"L42" [%"v46" : W = phi("L41" => #0, "L15" => #1)]:
    %"chk4" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"v39";
    store Ww [%"chk4" + 0] <- %"v46";
    %"v48" = %"v3" +p #776;
    %"chk5" : A = (Renew 0 8 Write 8) %"chk0", %"v48";
    store.ptr [%"chk5" + 0] <- %"v0"
    => ret void
} }.

Definition hi_fn___GI___libc_cleanup_pop_restore : func :=
  ir_fn{ "export" "__GI___libc_cleanup_pop_restore"(P %"v0") -> RVoid {
  @"start":
    call %"v3" : P = $"zthread_self_cookie"();
    %"v5" = %"v3" +p #776;
    %"v7" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk1" + 0] <- %"v8";
    %"v11" = %"v3" +p #792;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"v11";
    %"v12" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v17" = %"v0" +p #16;
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v17";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v19" : W = (Cmp Ne W) %"v18", #0
    => br %"v19" ? "L20" : "L21";
  @"L20":
    %"v24" : W = And %"v12", #2;
    %"v25" : W = (Cmp Eq W) %"v24", #0
    => goto "L21";
  @"L21" [%"v27" : W = phi("start" => #0, "L20" => %"v25")]:
    => br %"v27" ? "L29" : "L15";
  @"L29" [%"pr.1" : W = phi("L42" => %"pr.2", "L21" => %"v12")]:
    %"v34" : W = Or %"pr.1", #2;
    %"v36" = %"v3" +p #792;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 4) %"chk1", %"v36";
    %"v39" : W = (RawCas (CasNarrow Sw) 0) %"chk4", %"pr.1", %"v34";
    %"v40" : W = (Cmp Eq W) %"v39", %"pr.1"
    => br %"v40" ? "L42" : "L41";
  @"L41":
    => goto "L42";
  @"L42" [%"pr.2" : W = phi("L29" => %"pr.1", "L41" => %"v39")]:
    %"v43" : W = (Cmp Ne W) %"v39", %"pr.1"
    => br %"v43" ? poll "L29" : "iw_1.start";
  @"iw_1.start":
    %"iw_1.v10" : W = And %"pr.2", #57;
    %"iw_1.v12" : W = (Cmp Eq W) %"iw_1.v10", #8
    => br %"iw_1.v12" ? "L44" : "L15";
  @"L44":
    (Flight (a "v52") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    call %"iw_2.v3" : P = $"zthread_self_cookie"();
    %"iw_2.v5" = %"iw_2.v3" +p #1608;
    %"chk5" : A = (Check 0 8 Write 8) %"iw_2.v5";
    store.ptr [%"chk5" + 0] <- %"v52";
    %"iw_2.v9" = %"iw_2.v3" +p #792;
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk5", %"iw_2.v9";
    %"iw_2.v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk6"
    => goto "iw_2.L12";
  @"iw_2.L12" [%"iw_2.pr.1" : W = phi("iw_2.L38" => %"iw_2.pr.2", "L44" => %"iw_2.v10")]:
    %"iw_2.v17" : W = Or %"iw_2.pr.1", #1;
    %"iw_2.v19" : W = Or %"iw_2.v17", #16;
    %"iw_2.v23" : W = And %"iw_2.v19", #4294967293;
    %"iw_2.v29" : W = (Cmp Eq W) %"iw_2.pr.1", %"iw_2.v23"
    => br %"iw_2.v29" ? "iw_2.L14" : "iw_2.L13";
  @"iw_2.L13":
    %"iw_2.v32" = %"iw_2.v3" +p #792;
    %"chk7" : A = (HalfCheck Lower 0 4 Write 4) %"chk5", %"iw_2.v32";
    %"iw_2.v35" : W = (RawCas (CasNarrow Sw) 0) %"chk7", %"iw_2.pr.1", %"iw_2.v23";
    %"iw_2.v36" : W = (Cmp Eq W) %"iw_2.v35", %"iw_2.pr.1"
    => br %"iw_2.v36" ? "iw_2.L38" : "iw_2.L37";
  @"iw_2.L37":
    => goto "iw_2.L38";
  @"iw_2.L38" [%"iw_2.pr.2" : W = phi("iw_2.L13" => %"iw_2.pr.1", "iw_2.L37" => %"iw_2.v35")]:
    %"iw_2.v39" : W = (Cmp Ne W) %"iw_2.v35", %"iw_2.pr.1"
    => br %"iw_2.v39" ? poll "iw_2.L12" : "iw_2.L14";
  @"iw_2.L14":
    %"iw_2.v41" = %"iw_2.v3" +p #784;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"iw_2.v41";
    %"iw_2.v42" : P = (RawLoadPointer 0 load_effects) %"chk8";
    call void $"__GI___pthread_unwind"(P %"iw_2.v42")
    => goto "L15";
  @"L15":
    => ret void
} }.

Definition hi_fn_glibc_libc_start'23__libc_start_call_main : func :=
  ir_fn{ "local" "glibc_libc_start#__libc_start_call_main"(P %"v0", W %"v2", P %"v4") -> RVoid {
  @"start":
    %"v1" : P = (Alloc 8) #8;
    %"v3" : P = (Alloc 4) #4;
    %"v5" : P = (Alloc 8) #8;
    %"v6" : P = (Alloc 4) #4;
    %"v7" : P = (Alloc 8) #104;
    %"v8" : P = (Alloc 4) #4;
    %"v17" : P = (Alloc 8) #8;
    %"v36" : P = (Alloc 8) #128;
    %"v37" : P = (Alloc 8) #8;
    %"v62" : P = (Alloc 8) #8;
    %"v63" : P = (Alloc 4) #4;
    %"v64" : P = (Alloc 4) #4;
    %"chk0" : A = (Check 0 8 Write 8) %"v1";
    store.ptr [%"chk0" + 0] <- %"v0";
    %"chk1" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk1" + 0] <- %"v2";
    %"chk2" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk2" + 0] <- %"v4";
    %"v9" : W = (Setjmp SjUnderscore) %"v7", #0;
    %"chk3" : A = (Check 0 4 Write 1) %"v8";
    store Ww [%"chk3" + 0] <- %"v9";
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v14" : W = (Cmp Eq W) %"v13", #0;
    %"v15" : L = (Ext Sw) %"v14";
    %"v16" : W = (Cmp Ne L) %"v15", #0
    => br %"v16" ? "L10" : "L11";
  @"L10":
    call %"v18" : P = $"zthread_self_cookie"();
    %"chk5" : A = (Check 0 8 Write 8) %"v17";
    store.ptr [%"chk5" + 0] <- %"v18";
    %"v19" = %"v7" +p #72;
    %"chk6" : A = (Check 0 8 Read 8) %"v17";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v21" = %"v20" +p #784;
    %"chk7" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Write 8) %"v19";
    store.ptr [%"chk8" + 0] <- %"v22";
    %"v23" = %"v7" +p #72;
    %"v24" = %"v23" +p #8;
    %"chk9" : A = (Check 0 8 Read 8) %"v17";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v26" = %"v25" +p #776;
    %"chk10" : A = (Check 0 8 Read 8) %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk11" + 0] <- %"v27";
    %"chk12" : A = (Check 0 8 Read 8) %"v17";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v29" = %"v28" +p #784;
    %"chk13" : A = (Check 0 8 Write 8) %"v29";
    store.ptr [%"chk13" + 0] <- %"v7";
    %"chk14" : A = (Check 0 8 Read 8) %"v1";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 4 Read 1) %"v3";
    %"v31" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"chk16" : A = (Check 0 8 Read 8) %"v5";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v33" : P = Copy $"__environ";
    %"chk17" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : F = CheckFunction %"v30";
    rawcall %"v35" : W = %"chk18"(W %"v31", P %"v32", P %"v34");
    %"chk19" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk19" + 0] <- %"v35"
    => goto "L12";
  @"L11":
    call void $"__GI___nptl_deallocate_tsd"();
    %"chk20" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk20" + 0] <- #0;
    call void $"glibc_libc_start#internal_signal_block_all"(P %"v36");
    call %"v38" : P = $"zthread_self_cookie"();
    %"chk21" : A = (Check 0 8 Write 8) %"v37";
    store.ptr [%"chk21" + 0] <- %"v38"
    => goto "L39";
  @"L39":
    %"chk22" : A = (Check 0 8 Read 8) %"v37";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v43" = %"v42" +p #1592;
    %"chk23" : A = (Check 0 4 Write 1) %"v43";
    store Ww [%"chk23" + 0] <- #0
    => goto "L40";
  @"L40":
    => br #0 ? poll "L39" : "L41";
  @"L41":
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v45" = %"v44" +p #1592;
    call void $"glibc_libc_start#futex_wake"(P %"v45", W #1, W #128);
    %"v49" : P = Copy $"__GI___nptl_nthreads";
    %"v50" : W = Neg #1;
    %"chk25" : A = (Check 0 4 Read 1) %"v49";
    %"v51" : W = (RawLoad (LdNarrow Uw) 0) %"chk25"
    => goto "L52";
  @"L52" [%"v54" : W = phi("L41" => %"v51", "L52" => %"v56")]:
    %"v55" : W = Add %"v54", %"v50";
    %"chk26" : A = (Check 0 4 Write 4) %"v49";
    %"v56" : W = (RawCas (CasNarrow Uw) 0) %"chk26", %"v54", %"v55";
    %"v57" : W = (Cmp Eq W) %"v56", %"v54"
    => br %"v57" ? "L53" : poll "L52";
  @"L53":
    %"v58" : W = (Cmp Ne W) %"v54", #1
    => br %"v58" ? "L46" : "L47";
  @"L46":
    => goto "L59";
  @"L59":
    => br #1 ? "L60" : "L61";
  @"L60":
    %"chk27" : A = (Check 0 4 Write 1) %"v63";
    store Ww [%"chk27" + 0] <- #0;
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"chk29" : A = (Check 0 4 Write 1) %"v64";
    store Ww [%"chk29" + 0] <- %"v65";
    %"v66" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"v67" : P = Copy $"glibc_libc_start#str.319";
    call void $"zsafety_error"(P %"v67");
    %"chk31" : A = (Check 0 8 Read 1) %"v62";
    %"v68" : L = (RawLoad LdL 0) %"chk31"
    => goto poll "L59";
  @"L61":
    => goto "L48";
  @"L47":
    => goto "L48";
  @"L48":
    => goto "L12";
  @"L12":
    %"chk32" : A = (Check 0 4 Read 1) %"v6";
    %"v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    call void $"__GI_exit"(W %"v69")
    => ret void
} }.

Definition hi_fn___libc_start_main : func :=
  ir_fn{ "export" "__libc_start_main"(P %"v0", W %"v2", P %"v4", P %"v6", P %"v8") -> (RClass W) {
  @"start":
    call void $"zmake_setjmp_save_sigmask"(W #1);
    %"v11" : P = Copy $"__environ";
    %"chk0" : A = (Check 0 8 Write 8) %"v11";
    store.ptr [%"chk0" + 0] <- %"v6";
    %"v13" : P = Copy $"_dl_auxv";
    %"chk1" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk1" + 0] <- %"v8"
    => goto "L17";
  @"L17" [%"pr.1" : P = phi("L19" => %"v36", "start" => %"v8")]:
    %"chk2" : A = (Check 0 8 Read 1) %"pr.1";
    %"v22" : L = (RawLoad LdL 0) %"chk2";
    %"v23" : W = (Cmp Ne L) %"v22", #0
    => br %"v23" ? "L18" : "L20";
  @"L18":
    %"v28" : L = (RawLoad LdL 0) %"chk2";
    %"v29" : W = (Cmp Eq L) %"v28", #23
    => br %"v29" ? "L24" : "L19";
  @"L24":
    %"v30" : P = Copy $"__libc_enable_secure";
    %"v32" = %"pr.1" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v32";
    %"v33" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v30";
    store Ww [%"chk5" + 0] <- %"v33"
    => goto "L20";
  @"L19":
    %"v36" = %"pr.1" +p #16
    => goto poll "L17";
  @"L20":
    %"v40" : P = Copy $"__pthread_initialize_minimal";
    %"v41" : L = Ptoi %"v40";
    %"v42" : L = Ptoi #0;
    %"v43" : W = (Cmp Ne L) %"v41", %"v42"
    => br %"v43" ? "L37" : "L39";
  @"L37":
    call void $"__pthread_initialize_minimal"()
    => goto "L39";
  @"L39":
    %"v44" : P = Copy $"_dl_x86_cpu_features";
    call void $"glibc_libc_start#init_cpu_features"(P %"v44");
    call void $"__libc_setup_tls"();
    %"v45" : P = Copy $"glibc_libc_start#errno_handler";
    call void $"zregister_sys_errno_handler"(P %"v45");
    %"v46" : P = Copy $"glibc_libc_start#dlerror_handler";
    call void $"zregister_sys_dlerror_handler"(P %"v46");
    call void $"__libc_early_init"(W #1);
    %"v51" : P = Copy $"_dl_debug_mask";
    %"chk6" : A = (Check 0 4 Read 1) %"v51";
    %"v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v54" : W = And %"v52", #2;
    %"v55" : L = (Ext Sw) %"v54";
    %"v56" : W = (Cmp Ne L) %"v55", #0
    => br %"v56" ? "L48" : "L50";
  @"L48":
    %"v57" : P = Copy $"glibc_libc_start#str.320";
    %"chk7" : A = (Check 0 8 Read 8) %"v4";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call void $"zprintf"(P %"v57", P %"v60")
    => goto "L50";
  @"L50":
    call void $"zrun_deferred_global_ctors"();
    %"v64" : P = Copy $"_dl_debug_mask";
    %"chk8" : A = (Check 0 4 Read 1) %"v64";
    %"v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v67" : W = And %"v65", #2;
    %"v68" : L = (Ext Sw) %"v67";
    %"v69" : W = (Cmp Ne L) %"v68", #0
    => br %"v69" ? "L61" : "L63";
  @"L61":
    %"v70" : P = Copy $"glibc_libc_start#str.321";
    %"chk9" : A = (Check 0 8 Read 8) %"v4";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call void $"zprintf"(P %"v70", P %"v73")
    => goto "L63";
  @"L63":
    call void $"glibc_libc_start#__libc_start_call_main"(P %"v0", W %"v2", P %"v4")
    => ret #0
} }.

Definition hi_fn___libc_setup_tls : func :=
  ir_fn{ "export" "__libc_setup_tls"() -> RVoid {
  @"start":
    %"v1" : P = (Alloc 16) #2496;
    %"chk0" : A = (Check 0 8 Write 8) %"v1";
    store.ptr [%"chk0" + 0] <- %"v1";
    %"iw_1.v12" = %"v1" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v12";
    store.ptr [%"chk1" + 0] <- %"v1";
    call void $"zthread_set_self_cookie"(P %"v1");
    call void $"__tls_init_tp"()
    => ret void
} }.

Definition hi_fn___libc_early_init : func :=
  ir_fn{ "export" "__libc_early_init"(W %"v0") -> RVoid {
  @"start":
    call void $"__GI___ctype_init"();
    %"v2" : P = Copy $"__libc_single_threaded";
    %"v3" : W = (Ext Ub) %"v0";
    %"v4" : W = (Ext Sb) %"v3";
    %"chk0" : A = (Check 0 1 Write 1) %"v2";
    store Wb [%"chk0" + 0] <- %"v4";
    %"v5" : P = Copy $"__libc_single_threaded_internal";
    %"v6" : P = Copy $"__libc_initial";
    %"chk1" : A = (Check 0 1 Write 1) %"v6";
    store Wb [%"chk1" + 0] <- %"v3";
    %"chk2" : A = (Check 0 1 Write 1) %"v5";
    store Wb [%"chk2" + 0] <- %"v4";
    %"iw_1.v0" : P = (Alloc 8) #16;
    call %"iw_1.v4" : W = $"__GI___getrlimit"(W #3, P %"iw_1.v0");
    %"iw_1.v5" : W = (Cmp Ne W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "iw_1.L7" : "iw_1.L6";
  @"iw_1.L6":
    %"chk3" : A = (Check 0 8 Read 1) %"iw_1.v0";
    %"iw_1.v8" : L = (RawLoad LdL 0) %"chk3";
    %"iw_1.v11" : W = (Cmp Eq L) %"iw_1.v8", #18446744073709551615
    => goto "iw_1.L7";
  @"iw_1.L7" [%"iw_1.v13" : W = phi("start" => #1, "iw_1.L6" => %"iw_1.v11")]:
    => br %"iw_1.v13" ? "iw_1.L1" : "iw_1.L2";
  @"iw_1.L1":
    %"chk4" : A = (Check 0 8 Write 1) %"iw_1.v0";
    store Wl [%"chk4" + 0] <- #2097152
    => goto "iw_1.L3";
  @"iw_1.L2":
    %"chk5" : A = (Check 0 8 Read 1) %"iw_1.v0";
    %"iw_1.v20" : L = (RawLoad LdL 0) %"chk5";
    %"iw_1.v21" : W = (Cmp Ult L) %"iw_1.v20", #16384
    => br %"iw_1.v21" ? "iw_1.L17" : "iw_1.L3";
  @"iw_1.L17":
    %"chk6" : A = (Renew 0 8 Write 1) %"chk5", %"iw_1.v0";
    store Wl [%"chk6" + 0] <- #16384
    => goto "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v23" : P = Copy $"_dl_pagesize";
    %"chk7" : A = (Check 0 8 Read 1) %"iw_1.v23";
    %"iw_1.v24" : L = (RawLoad LdL 0) %"chk7";
    %"iw_1.v29" : L = Add %"iw_1.v24", #2048;
    %"chk8" : A = (Check 0 8 Read 1) %"iw_1.v0";
    %"iw_1.v33" : L = (RawLoad LdL 0) %"chk8";
    %"iw_1.v35" : W = (Cmp Ult L) %"iw_1.v33", %"iw_1.v29"
    => br %"iw_1.v35" ? "iw_1.L30" : "iw_1.L32";
  @"iw_1.L30":
    %"chk9" : A = (Renew 0 8 Write 1) %"chk8", %"iw_1.v0";
    store Wl [%"chk9" + 0] <- %"iw_1.v29"
    => goto "iw_1.L32";
  @"iw_1.L32":
    %"iw_1.v37" : L = (RawLoad LdL 0) %"chk8";
    %"iw_1.v39" : L = Add %"iw_1.v37", %"iw_1.v24";
    %"iw_1.v40" : L = Sub %"iw_1.v39", #1;
    %"iw_1.v42" : L = Neg %"iw_1.v24";
    %"iw_1.v43" : L = And %"iw_1.v40", %"iw_1.v42";
    %"chk11" : A = (Renew 0 8 Write 1) %"chk8", %"iw_1.v0";
    store Wl [%"chk11" + 0] <- %"iw_1.v43";
    %"iw_1.v44" : P = Copy $"__GI___default_pthread_attr";
    %"iw_1.v45" = %"iw_1.v44" +p #32;
    %"chk12" : A = (Renew 0 8 Read 1) %"chk8", %"iw_1.v0";
    %"iw_1.v46" : L = (RawLoad LdL 0) %"chk12";
    %"chk13" : A = (Check 0 8 Write 1) %"iw_1.v45";
    store Wl [%"chk13" + 0] <- %"iw_1.v46";
    %"iw_1.v47" : P = Copy $"__GI___default_pthread_attr";
    %"iw_1.v48" = %"iw_1.v47" +p #16;
    %"iw_1.v49" : P = Copy $"_dl_pagesize";
    %"chk14" : A = (Check 0 8 Read 1) %"iw_1.v49";
    %"iw_1.v50" : L = (RawLoad LdL 0) %"chk14";
    %"chk15" : A = (Check 0 8 Write 1) %"iw_1.v48";
    store Wl [%"chk15" + 0] <- %"iw_1.v50";
    call void $"__pthread_tunables_init"();
    call void $"__getrandom_early_init"(W %"v3");
    call void $"__ptmalloc_init"()
    => ret void
} }.

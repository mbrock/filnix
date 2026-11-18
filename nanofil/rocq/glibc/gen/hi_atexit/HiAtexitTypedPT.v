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

Definition hi_fn___ptmalloc_init : func :=
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

Definition hi_fn___pthread_tunables_init : func :=
  ir_fn{ "export" "__pthread_tunables_init"() -> RVoid {
  @"start":
    %"v1" : P = (Alloc 4) #4;
    %"v3" : P = Copy $"glibc_pthread_mutex_conf#_dl_tunable_set_mutex_spin_count";
    call void $"__tunable_get_val"(W #27, P %"v1", P %"v3");
    %"chk0" : A = (Check 0 4 Read 1) %"v1";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret void
} }.

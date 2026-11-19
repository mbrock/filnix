(** This file defines checked IR from glibc’s `csu/libc-start.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation Unit_csu_libcZ2dstart_os_Blocks_676c6962635f6c6962635f737461727423696e69745f6370755f6665617475726573_1 Unit_csu_libcZ2dstart_os_Blocks_676c6962635f6c6962635f737461727423696e69745f6370755f6665617475726573_2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___libc_start_main : func :=
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

Definition item___pthread_initialize_minimal : item :=
  (IData (a "__pthread_initialize_minimal") LExternWeak 1 []).

Definition item___x86_data_cache_size : item :=
  (IData (a "__x86_data_cache_size") LExport 8 [(Item Wl 32768)]).

Definition item___x86_data_cache_size_half : item :=
  (IData (a "__x86_data_cache_size_half") LExport 8 [(Item Wl 16384)]).

Definition item___x86_memset_non_temporal_threshold : item :=
  (IData (a "__x86_memset_non_temporal_threshold") LExport 8 [(Zero 8)]).

Definition item___x86_rep_movsb_stop_threshold : item :=
  (IData (a "__x86_rep_movsb_stop_threshold") LExport 8 [(Zero 8)]).

Definition item___x86_rep_movsb_threshold : item :=
  (IData (a "__x86_rep_movsb_threshold") LExport 8 [(Item Wl 2048)]).

Definition item___x86_rep_stosb_threshold : item :=
  (IData (a "__x86_rep_stosb_threshold") LExport 8 [(Item Wl 2048)]).

Definition item___x86_shared_cache_size : item :=
  (IData (a "__x86_shared_cache_size") LExport 8 [(Item Wl 1048576)]).

Definition item___x86_shared_cache_size_half : item :=
  (IData (a "__x86_shared_cache_size_half") LExport 8 [(Item Wl 524288)]).

Definition item___x86_shared_non_temporal_threshold : item :=
  (IData (a "__x86_shared_non_temporal_threshold") LExport 8 [(Zero 8)]).

Definition item___x86_string_control : item :=
  (IData (a "__x86_string_control") LExport 4 [(Zero 4)]).

Definition item__dl_x86_features_tlsdesc_state_size : item :=
  (IData (a "_dl_x86_features_tlsdesc_state_size") LExport 8 [(Zero 8)]).

Definition fn_glibc_libc_start'23__libc_start_call_main : func :=
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

Definition fn_glibc_libc_start'23_dl_tunable_set_plt_rewrite : func :=
  ir_fn{ "local" "glibc_libc_start#_dl_tunable_set_plt_rewrite"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v6" : L = (RawLoad LdL 0) %"chk0";
    %"v7" : W = (Cmp Ne L) %"v6", #0
    => br %"v7" ? "iw_1.start" : "L9";
  @"iw_1.start":
    %"iw_1.v30" : P = Copy $"glibc_libc_start#str.319";
    call void $"zsafety_error"(P %"iw_1.v30");
    (Flight (a "iw_1.v32") Copy [(FValue (Const 0))] LowerNone);
    (Flight (a "iw_1.v39") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"iw_1.v40" : L = Ptoi %"iw_1.v32";
    %"iw_1.v41" : L = Ptoi %"iw_1.v39";
    %"iw_1.v42" : W = (Cmp Eq L) %"iw_1.v40", %"iw_1.v41"
    => br %"iw_1.v42" ? "L9" : "iw_1.L35";
  @"iw_1.L35":
    %"chk1" : A = (Check 0 4 Write 1) %"iw_1.v32";
    store Ww [%"chk1" + 0] <- #1;
    %"iw_1.v65" : P = Copy $"glibc_libc_start#str.319";
    call void $"zsafety_error"(P %"iw_1.v65");
    %"iw_1.v80" : P = Copy $"glibc_libc_start#str.319";
    call void $"zsafety_error"(P %"iw_1.v80")
    => goto "L9";
  @"L9" [%"v13" : W = phi("start" => #0, "iw_1.L35" => #1, "iw_1.start" => #0)]:
    => br %"v13" ? "L2" : "L4";
  @"L2":
    %"v15" : P = Copy $"_dl_x86_cpu_features";
    %"v16" : P = Copy $"_dl_x86_feature_control";
    %"chk2" : A = (Renew 0 8 Read 1) %"chk0", %"v0";
    %"v21" : L = (RawLoad LdL 0) %"chk2";
    %"v22" : W = (Cmp Sgt L) %"v21", #1
    => br %"v22" ? "L23" : "L24";
  @"L23":
    %"v26" = %"v15" +p #20;
    %"v27" = %"v26" +p #192;
    %"v28" = %"v27" +p #12;
    %"chk3" : A = (Check 0 4 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v31" : W = And %"v29", #2097152;
    %"v32" : W = (Cmp Ne W) %"v31", #0
    => goto "L24";
  @"L24" [%"v34" : W = phi("L2" => #0, "L23" => %"v32")]:
    => br %"v34" ? "L19" : "L18";
  @"L18":
    => goto "L19";
  @"L19" [%"v35" : W = phi("L18" => #1, "L24" => #2)]:
    %"chk4" : A = (Check 0 4 Read 1) %"v16";
    %"v36" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v37" : W = And %"v36", #4294967247;
    %"v38" : W = Shl %"v35", #4;
    %"v39" : W = And %"v38", #48;
    %"v40" : W = Or %"v37", %"v39";
    %"chk5" : A = (Renew 0 4 Write 1) %"chk4", %"v16";
    store Ww [%"chk5" + 0] <- %"v40"
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition fn_glibc_libc_start'23_dl_tunable_set_prefer_map_32bit_exec : func :=
  ir_fn{ "local" "glibc_libc_start#_dl_tunable_set_prefer_map_32bit_exec"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v6" : L = (RawLoad LdL 0) %"chk0";
    %"v7" : W = (Cmp Ne L) %"v6", #0
    => br %"v7" ? "L2" : "L4";
  @"L2":
    %"v8" : P = Copy $"_dl_x86_cpu_features";
    %"v9" = %"v8" +p #340;
    %"chk1" : A = (Check 0 4 Read 1) %"v9";
    %"v11" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v12" : W = Or %"v11", #1024;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk1", %"v9";
    store Ww [%"chk2" + 0] <- %"v12"
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition fn_glibc_libc_start'23dl_init_cacheinfo : func :=
  ir_fn{ "local" "glibc_libc_start#dl_init_cacheinfo"(P %"v0") -> RVoid {
  @"start":
    %"v5" : P = (Alloc 8) #8;
    %"v8" : P = (Alloc 8) #8;
    %"v11" : P = (Alloc 4) #4;
    %"v54" : P = (Alloc 4) #276;
    %"v333" : P = (Alloc 8) #8;
    %"v343" : P = (Alloc 8) #8;
    %"v365" : P = (Alloc 8) #8;
    %"v392" : P = (Alloc 8) #8;
    %"v410" : P = (Alloc 8) #8;
    %"v421" : P = (Alloc 8) #8;
    %"v439" : P = (Alloc 8) #16;
    %"v442" : P = (Alloc 8) #8;
    %"v444" : P = (Alloc 8) #8;
    %"v471" : P = (Alloc 8) #8;
    %"v474" : P = (Alloc 8) #16;
    %"v477" : P = (Alloc 8) #8;
    %"v478" : P = (Alloc 8) #8;
    %"v479" : P = (Alloc 8) #16;
    %"v482" : P = (Alloc 8) #8;
    %"v483" : P = (Alloc 8) #8;
    %"v484" : P = (Alloc 8) #16;
    %"v487" : P = (Alloc 8) #8;
    %"v488" : P = (Alloc 8) #8;
    %"v489" : P = (Alloc 8) #16;
    %"v492" : P = (Alloc 8) #8;
    %"v494" : P = (Alloc 8) #8;
    %"v496" : P = (Alloc 8) #16;
    %"v499" : P = (Alloc 8) #8;
    %"v501" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 1) %"v5";
    store Wl [%"chk0" + 0] <- #18446744073709551615;
    %"chk1" : A = (Check 0 8 Write 1) %"v8";
    store Wl [%"chk1" + 0] <- #18446744073709551615;
    %"chk2" : A = (Check 0 4 Write 1) %"v11";
    store Ww [%"chk2" + 0] <- #0;
    %"chk3" : A = (Check 0 4 Read 1) %"v0";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v53" : W = (Cmp Eq W) %"v52", #1
    => br %"v53" ? "L48" : "L49";
  @"L48":
    %"v55" = %"v54" +p #1;
    %"chk4" : A = (Check 0 1 Write 1) %"v55";
    store Wb [%"chk4" + 0] <- #0;
    %"chk5" : A = (HalfCheck Lower 0 1 Write 1) %"chk4", %"v54";
    store Wb [%"chk5" + 0] <- #0;
    call %"v57" : L = $"glibc_libc_start#handle_intel"(W #188, P %"v0", P %"v54");
    call %"v59" : L = $"glibc_libc_start#handle_intel"(W #194, P %"v0", P %"v54");
    %"chk6" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk6" + 0] <- %"v59";
    %"v60" : L = (RawLoad LdL 0) %"chk6";
    %"chk8" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk8" + 0] <- %"v60";
    call %"v62" : L = $"glibc_libc_start#handle_intel"(W #185, P %"v0", P %"v54");
    call %"v64" : L = $"glibc_libc_start#handle_intel"(W #187, P %"v0", P %"v54");
    call %"v67" : L = $"glibc_libc_start#handle_intel"(W #189, P %"v0", P %"v54");
    call %"v69" : L = $"glibc_libc_start#handle_intel"(W #190, P %"v0", P %"v54");
    call %"v71" : L = $"glibc_libc_start#handle_intel"(W #191, P %"v0", P %"v54");
    call %"v73" : L = $"glibc_libc_start#handle_intel"(W #192, P %"v0", P %"v54");
    call %"v75" : L = $"glibc_libc_start#handle_intel"(W #193, P %"v0", P %"v54");
    %"chk9" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v76" : L = (RawLoad LdL 0) %"chk9";
    call %"v78" : L = $"glibc_libc_start#handle_intel"(W #195, P %"v0", P %"v54");
    call %"v80" : L = $"glibc_libc_start#handle_intel"(W #196, P %"v0", P %"v54");
    call %"v82" : L = $"glibc_libc_start#handle_intel"(W #197, P %"v0", P %"v54");
    call void $"glibc_libc_start#get_common_cache_info"(P %"v5", P %"v8", P %"v11", L %"v71", P %"v54")
    => goto "L50";
  @"L49":
    %"v88" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v89" : W = (Cmp Eq W) %"v88", #3
    => br %"v89" ? "L84" : "L85";
  @"L84":
    call %"v90" : L = $"glibc_libc_start#handle_zhaoxin"(W #188);
    call %"v91" : L = $"glibc_libc_start#handle_zhaoxin"(W #194);
    %"chk11" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk11" + 0] <- %"v91";
    %"v92" : L = (RawLoad LdL 0) %"chk11";
    %"chk13" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk13" + 0] <- %"v92";
    call %"v93" : L = $"glibc_libc_start#handle_zhaoxin"(W #185);
    call %"v94" : L = $"glibc_libc_start#handle_zhaoxin"(W #187);
    call %"v96" : L = $"glibc_libc_start#handle_zhaoxin"(W #189);
    call %"v97" : L = $"glibc_libc_start#handle_zhaoxin"(W #190);
    call %"v98" : L = $"glibc_libc_start#handle_zhaoxin"(W #191);
    call %"v99" : L = $"glibc_libc_start#handle_zhaoxin"(W #192);
    call %"v100" : L = $"glibc_libc_start#handle_zhaoxin"(W #193);
    %"chk14" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v101" : L = (RawLoad LdL 0) %"chk14";
    call %"v102" : L = $"glibc_libc_start#handle_zhaoxin"(W #195);
    call %"v103" : L = $"glibc_libc_start#handle_zhaoxin"(W #196);
    call void $"glibc_libc_start#get_common_cache_info"(P %"v5", P %"v8", P %"v11", L %"v98", P #0)
    => goto "L50";
  @"L85":
    %"v109" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v110" : W = (Cmp Eq W) %"v109", #2
    => br %"v110" ? "L105" : "L106";
  @"L105":
    call %"v111" : L = $"glibc_libc_start#handle_amd"(W #188);
    call %"v112" : L = $"glibc_libc_start#handle_amd"(W #194);
    %"chk16" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk16" + 0] <- %"v112";
    call %"v113" : L = $"glibc_libc_start#handle_amd"(W #185);
    call %"v114" : L = $"glibc_libc_start#handle_amd"(W #187);
    call %"v116" : L = $"glibc_libc_start#handle_amd"(W #189);
    call %"v117" : L = $"glibc_libc_start#handle_amd"(W #190);
    call %"v118" : L = $"glibc_libc_start#handle_amd"(W #191);
    call %"v119" : L = $"glibc_libc_start#handle_amd"(W #192);
    call %"v120" : L = $"glibc_libc_start#handle_amd"(W #193);
    %"chk17" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v121" : L = (RawLoad LdL 0) %"chk17";
    call %"v122" : L = $"glibc_libc_start#handle_amd"(W #195);
    call %"v123" : L = $"glibc_libc_start#handle_amd"(W #196);
    call %"v124" : L = $"glibc_libc_start#handle_amd"(W #197);
    %"chk18" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v128" : L = (RawLoad LdL 0) %"chk18";
    %"v129" : W = (Cmp Sle L) %"v128", #0
    => br %"v129" ? "L125" : "L126";
  @"L125":
    %"chk19" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk19" + 0] <- %"v118"
    => goto "L127";
  @"L126":
    %"v135" = %"v0" +p #8;
    %"chk20" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v135";
    %"v136" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v137" : W = (Cmp Ult W) %"v136", #23
    => br %"v137" ? "L131" : "L127";
  @"L131":
    %"v138" : L = (RawLoad LdL 0) %"chk18";
    %"v140" : L = Add %"v138", %"v118";
    %"chk22" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk22" + 0] <- %"v140"
    => goto "L127";
  @"L127":
    %"v141" : L = (RawLoad LdL 0) %"chk18";
    %"chk24" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk24" + 0] <- %"v141"
    => goto "L50";
  @"L106":
    %"v146" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v147" : W = (Cmp Eq W) %"v146", #4
    => br %"v147" ? "L142" : "L50";
  @"L142":
    call %"v148" : L = $"glibc_libc_start#handle_hygon"(W #188);
    call %"v149" : L = $"glibc_libc_start#handle_hygon"(W #194);
    %"chk26" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk26" + 0] <- %"v149";
    %"v150" : L = (RawLoad LdL 0) %"chk26";
    %"chk28" : A = (Renew 0 8 Write 1) %"chk1", %"v8";
    store Wl [%"chk28" + 0] <- %"v150";
    call %"v151" : L = $"glibc_libc_start#handle_hygon"(W #185);
    call %"v152" : L = $"glibc_libc_start#handle_hygon"(W #187);
    call %"v154" : L = $"glibc_libc_start#handle_hygon"(W #189);
    call %"v155" : L = $"glibc_libc_start#handle_hygon"(W #190);
    call %"v156" : L = $"glibc_libc_start#handle_hygon"(W #191);
    call %"v157" : L = $"glibc_libc_start#handle_hygon"(W #192);
    call %"v158" : L = $"glibc_libc_start#handle_hygon"(W #193);
    %"chk29" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v159" : L = (RawLoad LdL 0) %"chk29";
    call %"v160" : L = $"glibc_libc_start#handle_hygon"(W #195);
    call %"v161" : L = $"glibc_libc_start#handle_hygon"(W #196)
    => goto "L50";
  @"L50" [%"pr.51" : L = phi("L48" => %"v82", "L84" => #18446744073709551615, "L127" => %"v124", "L142" => #18446744073709551615, "L106" => #18446744073709551615); %"pr.48" : L = phi("L48" => %"v80", "L84" => %"v103", "L127" => %"v123", "L142" => %"v161", "L106" => #18446744073709551615); %"pr.44" : L = phi("L48" => %"v78", "L84" => %"v102", "L127" => %"v122", "L142" => %"v160", "L106" => #18446744073709551615); %"pr.40" : L = phi("L48" => %"v76", "L84" => %"v101", "L127" => %"v121", "L142" => %"v159", "L106" => #18446744073709551615); %"pr.36" : L = phi("L48" => %"v75", "L84" => %"v100", "L127" => %"v120", "L142" => %"v158", "L106" => #18446744073709551615); %"pr.32" : L = phi("L48" => %"v73", "L84" => %"v99", "L127" => %"v119", "L142" => %"v157", "L106" => #18446744073709551615); %"pr.28" : L = phi("L48" => %"v71", "L84" => %"v98", "L127" => %"v118", "L142" => %"v156", "L106" => #18446744073709551615); %"pr.24" : L = phi("L48" => %"v69", "L84" => %"v97", "L127" => %"v117", "L142" => %"v155", "L106" => #18446744073709551615); %"pr.20" : L = phi("L48" => %"v67", "L84" => %"v96", "L127" => %"v116", "L142" => %"v154", "L106" => #18446744073709551615); %"pr.16" : L = phi("L48" => %"v57", "L84" => %"v90", "L127" => %"v111", "L142" => %"v148", "L106" => #18446744073709551615); %"pr.12" : L = phi("L48" => %"v64", "L84" => %"v94", "L127" => %"v114", "L142" => %"v152", "L106" => #18446744073709551615); %"pr.8" : L = phi("L48" => %"v62", "L84" => %"v93", "L127" => %"v113", "L142" => %"v151", "L106" => #18446744073709551615); %"pr.4" : L = phi("L48" => %"v57", "L84" => %"v90", "L127" => %"v111", "L142" => %"v148", "L106" => #18446744073709551615)]:
    %"v163" = %"v0" +p #424;
    %"chk30" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v163";
    store Wl [%"chk30" + 0] <- %"pr.8";
    %"v166" = %"v0" +p #432;
    %"chk31" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v166";
    store Wl [%"chk31" + 0] <- %"pr.12";
    %"v169" = %"v0" +p #440;
    %"chk32" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v169";
    store Wl [%"chk32" + 0] <- %"pr.16";
    %"v172" = %"v0" +p #448;
    %"chk33" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v172";
    store Wl [%"chk33" + 0] <- %"pr.20";
    %"v175" = %"v0" +p #456;
    %"chk34" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v175";
    store Wl [%"chk34" + 0] <- %"pr.24";
    %"v178" = %"v0" +p #464;
    %"chk35" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v178";
    store Wl [%"chk35" + 0] <- %"pr.28";
    %"v181" = %"v0" +p #472;
    %"chk36" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v181";
    store Wl [%"chk36" + 0] <- %"pr.32";
    %"v184" = %"v0" +p #480;
    %"chk37" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v184";
    store Wl [%"chk37" + 0] <- %"pr.36";
    %"v187" = %"v0" +p #488;
    %"chk38" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v187";
    store Wl [%"chk38" + 0] <- %"pr.40";
    %"v190" = %"v0" +p #496;
    %"chk39" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v190";
    store Wl [%"chk39" + 0] <- %"pr.44";
    %"v193" = %"v0" +p #504;
    %"chk40" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v193";
    store Wl [%"chk40" + 0] <- %"pr.48";
    %"v196" = %"v0" +p #512;
    %"chk41" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v196";
    store Wl [%"chk41" + 0] <- %"pr.51";
    %"v200" = %"v0" +p #520;
    %"chk42" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v200";
    %"v201" : L = (RawLoad LdL 0) %"chk42";
    %"v206" : W = (Cmp Ule L) %"v201", #0
    => br %"v206" ? "L204" : "L203";
  @"L203":
    => goto "L204";
  @"L204" [%"pr.53" : L = phi("L203" => %"v201", "L50" => #4)]:
    %"chk43" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
    %"v208" : L = (RawLoad LdL 0) %"chk43";
    %"v210" : L = Udiv %"v208", %"pr.53";
    %"chk44" : A = (Renew 0 8 Read 1) %"chk1", %"v8";
    %"v212" : L = (RawLoad LdL 0) %"chk44";
    %"v213" : L = Mul %"v212", #3;
    %"v214" : L = Div %"v213", #4;
    %"v220" : W = (Cmp Ult L) %"v210", %"v214"
    => br %"v220" ? "L217" : "L216";
  @"L216":
    => goto "L217";
  @"L217" [%"pr.54" : L = phi("L216" => %"v210", "L204" => %"v214")]:
    %"v226" = %"v0" +p #20;
    %"v227" = %"v226" +p #32;
    %"v228" = %"v227" +p #16;
    %"v229" = %"v228" +p #4;
    %"chk45" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v229";
    %"v230" : W = (RawLoad (LdNarrow Uw) 0) %"chk45";
    %"v232" : W = And %"v230", #512;
    %"v234" : W = (Cmp Eq W) %"v232", #0
    => br %"v234" ? "L235" : "L236";
  @"L235":
    %"chk46" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v238" : W = (RawLoad (LdNarrow Uw) 0) %"chk46";
    %"v239" : W = (Cmp Ne W) %"v238", #3
    => goto "L236";
  @"L236" [%"v241" : W = phi("L217" => #0, "L235" => %"v239")]:
    => br %"v241" ? "L224" : "L223";
  @"L223":
    => goto "L224";
  @"L224" [%"pr.55" : L = phi("L223" => %"pr.54", "L236" => %"v214")]:
    %"v251" : W = (Cmp Ult L) %"pr.55", #16448
    => br %"v251" ? "L248" : "L247";
  @"L247":
    %"v260" : W = (Cmp Ugt L) %"pr.55", #1152921504606846975
    => br %"v260" ? "L248" : "L256";
  @"L256":
    => goto "L248";
  @"L248" [%"pr.56" : L = phi("L224" => #67108864, "L256" => %"pr.55", "L247" => #1152921504606846975)]:
    %"v268" = %"v0" +p #20;
    %"v269" = %"v268" +p #32;
    %"v270" = %"v269" +p #16;
    %"v271" = %"v270" +p #4;
    %"v272" : W = (RawLoad (LdNarrow Uw) 0) %"chk45";
    %"v274" : W = And %"v272", #65536;
    %"v275" : W = (Cmp Ne W) %"v274", #0
    => br %"v275" ? "L276" : "L277";
  @"L276":
    %"v279" = %"v0" +p #340;
    %"v281" : W = (RawLoad (LdNarrow Uw) (-84)) %"chk30";
    %"v282" : W = And %"v281", #8192;
    %"v284" : W = (Cmp Eq W) %"v282", #0
    => goto "L277";
  @"L277" [%"v286" : W = phi("L248" => #0, "L276" => %"v284")]:
    => br %"v286" ? "L266" : "L265";
  @"L265":
    %"v296" = %"v0" +p #340;
    %"v298" : W = (RawLoad (LdNarrow Uw) (-84)) %"chk30";
    %"v299" : W = And %"v298", #512;
    %"v300" : W = (Cmp Ne W) %"v299", #0
    => br %"v300" ? "L266" : "L293";
  @"L293":
    => goto "L266";
  @"L266" [%"pr.62" : L = phi("L277" => #16384, "L293" => #2048, "L265" => #8192); %"pr.60" : L = phi("L277" => #512, "L293" => #128, "L265" => #256)]:
    %"v315" = %"v0" +p #20;
    %"v316" = %"v315" +p #32;
    %"v317" = %"v316" +p #16;
    %"v318" = %"v317" +p #12;
    %"v319" : W = (RawLoad (LdNarrow Uw) 8) %"chk45";
    %"v321" : W = And %"v319", #16;
    %"v322" : W = (Cmp Ne W) %"v321", #0
    => br %"v322" ? "L313" : "L312";
  @"L312":
    => goto "L313";
  @"L313" [%"pr.64" : L = phi("L312" => %"pr.62", "L266" => #2112)]:
    %"chk51" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v327" : W = (RawLoad (LdNarrow Uw) 0) %"chk51";
    %"v328" : W = (Cmp Eq W) %"v327", #2
    => br %"v328" ? "L325" : "L324";
  @"L324":
    => goto "L325";
  @"L325" [%"pr.65" : L = phi("L324" => %"pr.64", "L313" => %"pr.56")]:
    call void $"__tunable_get_val"(W #3, P %"v333", P #0);
    %"chk52" : A = (Check 0 8 Read 1) %"v333";
    %"v335" : L = (RawLoad LdL 0) %"chk52";
    %"v340" : W = (Cmp Ne L) %"v335", #0
    => br %"v340" ? "L338" : "L337";
  @"L337":
    => goto "L338";
  @"L338" [%"pr.3" : L = phi("L337" => %"pr.4", "L325" => %"v335")]:
    call void $"__tunable_get_val"(W #9, P %"v343", P #0);
    %"chk53" : A = (Check 0 8 Read 1) %"v343";
    %"v345" : L = (RawLoad LdL 0) %"chk53";
    %"v350" : W = (Cmp Ne L) %"v345", #0
    => br %"v350" ? "L346" : "L348";
  @"L346":
    %"chk54" : A = (Renew 0 8 Write 1) %"chk0", %"v5";
    store Wl [%"chk54" + 0] <- %"v345"
    => goto "L348";
  @"L348":
    %"v357" = %"v0" +p #340;
    %"chk55" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v357";
    %"v359" : W = (RawLoad (LdNarrow Uw) 0) %"chk55";
    %"v360" : W = And %"v359", #131072;
    %"v362" : W = (Cmp Eq W) %"v360", #0
    => br %"v362" ? "L355" : "L354";
  @"L354":
    => goto "L355";
  @"L355" [%"pr.69" : L = phi("L354" => #18446744073709551615, "L348" => %"pr.56")]:
    call void $"__tunable_get_val"(W #6, P %"v365", P #0);
    %"chk56" : A = (Check 0 8 Read 1) %"v365";
    %"v367" : L = (RawLoad LdL 0) %"chk56";
    %"v373" : W = (Cmp Ugt L) %"v367", #16448
    => br %"v373" ? "L374" : "L375";
  @"L374":
    %"v378" : W = (Cmp Ule L) %"v367", #1152921504606846975
    => goto "L375";
  @"L375" [%"v380" : W = phi("L355" => #0, "L374" => %"v378")]:
    => br %"v380" ? "L370" : "L369";
  @"L369":
    %"chk57" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v386" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
    %"v387" : W = (Cmp Eq W) %"v386", #4
    => br %"v387" ? "L382" : "L370";
  @"L382":
    %"chk58" : A = (Renew 0 8 Read 1) %"chk1", %"v8";
    %"v388" : L = (RawLoad LdL 0) %"chk58";
    %"v389" : L = Mul %"v388", #3;
    %"v390" : L = Div %"v389", #8
    => goto "L370";
  @"L370" [%"pr.58" : L = phi("L375" => %"v367", "L382" => %"v390", "L369" => %"pr.56")]:
    call void $"__tunable_get_val"(W #5, P %"v392", P #0);
    %"chk59" : A = (Check 0 8 Read 1) %"v392";
    %"v394" : L = (RawLoad LdL 0) %"chk59";
    %"v400" : W = (Cmp Ugt L) %"v394", #16448
    => br %"v400" ? "L401" : "L402";
  @"L401":
    %"v405" : W = (Cmp Ule L) %"v394", #1152921504606846975
    => goto "L402";
  @"L402" [%"v407" : W = phi("L370" => #0, "L401" => %"v405")]:
    => br %"v407" ? "L397" : "L396";
  @"L396":
    => goto "L397";
  @"L397" [%"pr.70" : L = phi("L396" => %"pr.69", "L402" => %"v394")]:
    call void $"__tunable_get_val"(W #7, P %"v410", P #0);
    %"chk60" : A = (Check 0 8 Read 1) %"v410";
    %"v412" : L = (RawLoad LdL 0) %"chk60";
    %"v418" : W = (Cmp Ugt L) %"v412", %"pr.60"
    => br %"v418" ? "L415" : "L414";
  @"L414":
    => goto "L415";
  @"L415" [%"pr.66" : L = phi("L414" => %"pr.65", "L397" => %"v412")]:
    call void $"__tunable_get_val"(W #8, P %"v421", P #0);
    %"chk61" : A = (Check 0 8 Read 1) %"v421";
    %"v423" : L = (RawLoad LdL 0) %"chk61";
    %"chk62" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v428" : W = (RawLoad (LdNarrow Uw) 0) %"chk62";
    %"v429" : W = (Cmp Eq W) %"v428", #2
    => br %"v429" ? "L430" : "L431";
  @"L430":
    call %"v434" : W = $"__tunable_is_initialized"(W #8);
    %"v435" : W = (Ext Ub) %"v434";
    %"v436" : W = (Cmp Eq W) %"v435", #0
    => goto "L431";
  @"L431" [%"v438" : W = phi("L415" => #0, "L430" => %"v436")]:
    => br %"v438" ? "L426" : "L425";
  @"L425":
    => goto "L426";
  @"L426" [%"pr.67" : L = phi("L425" => %"v423", "L431" => #18446744073709551615)]:
    %"chk63" : A = (Check 0 8 Write 1) %"v439";
    store Wl [%"chk63" + 0] <- #0;
    %"v440" = %"v439" +p #8;
    %"chk64" : A = (HalfCheck Upper 0 8 Write 1) %"chk63", %"v440";
    store Wl [%"chk64" + 0] <- #0;
    store Wl [%"chk63" + 0] <- %"pr.70";
    %"chk66" : A = (Check 0 8 Write 1) %"v442";
    store Wl [%"chk66" + 0] <- #0;
    store Wl [%"chk66" + 0] <- #16448;
    %"chk68" : A = (Check 0 8 Write 1) %"v444";
    store Wl [%"chk68" + 0] <- #0;
    store Wl [%"chk68" + 0] <- #(-1);
    call void $"__tunable_set_val"(W #5, P %"v439", P %"v442", P %"v444");
    %"v449" = %"v0" +p #340;
    %"chk70" : A = (Renew 0 4 Read 1) %"chk55", %"v449";
    %"v451" : W = (RawLoad (LdNarrow Uw) 0) %"chk70";
    %"v452" : W = And %"v451", #262144;
    %"v453" : W = (Cmp Ne W) %"v452", #0
    => br %"v453" ? "L455" : "L454";
  @"L454":
    call %"v458" : W = $"__tunable_is_initialized"(W #8);
    %"v459" : W = (Ext Ub) %"v458";
    %"v460" : W = (Cmp Eq W) %"v459", #0
    => br %"v460" ? "L461" : "L455";
  @"L461":
    %"v465" : W = (Cmp Ugt L) %"pr.67", %"pr.70"
    => goto "L455";
  @"L455" [%"v469" : W = phi("L426" => #1, "L454" => #0, "L461" => %"v465")]:
    => br %"v469" ? "L445" : "L447";
  @"L445":
    call void $"__tunable_get_val"(W #5, P %"v471", P #0);
    %"chk71" : A = (Check 0 8 Read 1) %"v471";
    %"v473" : L = (RawLoad LdL 0) %"chk71"
    => goto "L447";
  @"L447" [%"pr.68" : L = phi("L445" => %"v473", "L455" => %"pr.67")]:
    code ((app ir[ %"chk72" : A = (Check 0 8 Write 1) %"v474";
      store Wl [%"chk72" + 0] <- #0;
      %"v475" = %"v474" +p #8;
      %"chk73" : A = (HalfCheck Upper 0 8 Write 1) %"chk72", %"v475";
      store Wl [%"chk73" + 0] <- #0;
      store Wl [%"chk72" + 0] <- %"pr.68";
      %"chk75" : A = (Check 0 8 Write 1) %"v477";
      store Wl [%"chk75" + 0] <- #0;
      store Wl [%"chk75" + 0] <- #1;
      %"chk77" : A = (Check 0 8 Write 1) %"v478";
      store Wl [%"chk77" + 0] <- #0;
      store Wl [%"chk77" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #8, P %"v474", P %"v477", P %"v478");
      %"chk79" : A = (Check 0 8 Write 1) %"v479";
      store Wl [%"chk79" + 0] <- #0;
      %"v480" = %"v479" +p #8;
      %"chk80" : A = (HalfCheck Upper 0 8 Write 1) %"chk79", %"v480";
      store Wl [%"chk80" + 0] <- #0;
      store Wl [%"chk79" + 0] <- %"pr.3";
      %"chk82" : A = (Check 0 8 Write 1) %"v482";
      store Wl [%"chk82" + 0] <- #0;
      store Wl [%"chk82" + 0] <- #0;
      %"chk84" : A = (Check 0 8 Write 1) %"v483";
      store Wl [%"chk84" + 0] <- #0;
      store Wl [%"chk84" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #3, P %"v479", P %"v482", P %"v483");
      %"chk86" : A = (Check 0 8 Write 1) %"v484";
      store Wl [%"chk86" + 0] <- #0;
      %"v485" = %"v484" +p #8;
      %"chk87" : A = (HalfCheck Upper 0 8 Write 1) %"chk86", %"v485";
      store Wl [%"chk87" + 0] <- #0;
      %"chk88" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
      %"v486" : L = (RawLoad LdL 0) %"chk88";
      store Wl [%"chk86" + 0] <- %"v486";
      %"chk90" : A = (Check 0 8 Write 1) %"v487";
      store Wl [%"chk90" + 0] <- #0;
      store Wl [%"chk90" + 0] <- #0;
      %"chk92" : A = (Check 0 8 Write 1) %"v488";
      store Wl [%"chk92" + 0] <- #0;
      store Wl [%"chk92" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #9, P %"v484", P %"v487", P %"v488");
      %"chk94" : A = (Check 0 8 Write 1) %"v489";
      store Wl [%"chk94" + 0] <- #0;
      %"v490" = %"v489" +p #8] ir[ %"chk95" : A = (HalfCheck Upper 0 8 Write 1) %"chk94", %"v490";
      store Wl [%"chk95" + 0] <- #0;
      store Wl [%"chk94" + 0] <- %"pr.58";
      %"chk97" : A = (Check 0 8 Write 1) %"v492";
      store Wl [%"chk97" + 0] <- #0;
      store Wl [%"chk97" + 0] <- #16448;
      %"chk99" : A = (Check 0 8 Write 1) %"v494";
      store Wl [%"chk99" + 0] <- #0;
      store Wl [%"chk99" + 0] <- #1152921504606846975;
      call void $"__tunable_set_val"(W #6, P %"v489", P %"v492", P %"v494");
      %"chk101" : A = (Check 0 8 Write 1) %"v496";
      store Wl [%"chk101" + 0] <- #0;
      %"v497" = %"v496" +p #8;
      %"chk102" : A = (HalfCheck Upper 0 8 Write 1) %"chk101", %"v497";
      store Wl [%"chk102" + 0] <- #0;
      store Wl [%"chk101" + 0] <- %"pr.66";
      %"chk104" : A = (Check 0 8 Write 1) %"v499";
      store Wl [%"chk104" + 0] <- #0;
      store Wl [%"chk104" + 0] <- %"pr.60";
      %"chk106" : A = (Check 0 8 Write 1) %"v501";
      store Wl [%"chk106" + 0] <- #0;
      store Wl [%"chk106" + 0] <- #(-1);
      call void $"__tunable_set_val"(W #7, P %"v496", P %"v499", P %"v501");
      %"v505" = %"v0" +p #368;
      %"chk108" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v505";
      store Wl [%"chk108" + 0] <- %"pr.3";
      %"v508" = %"v0" +p #376;
      %"chk109" : A = (Renew 0 8 Read 1) %"chk0", %"v5";
      %"v509" : L = (RawLoad LdL 0) %"chk109";
      %"chk110" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v508";
      store Wl [%"chk110" + 0] <- %"v509";
      %"v511" = %"v0" +p #384;
      %"chk111" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v511";
      store Wl [%"chk111" + 0] <- %"pr.58";
      %"v514" = %"v0" +p #392;
      %"chk112" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v514";
      store Wl [%"chk112" + 0] <- %"pr.70";
      %"v517" = %"v0" +p #400;
      %"chk113" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v517";
      store Wl [%"chk113" + 0] <- %"pr.66";
      %"v520" = %"v0" +p #416;
      %"chk114" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v520";
      store Wl [%"chk114" + 0] <- %"pr.68";
      %"v523" = %"v0" +p #408;
      store Wl [%"chk114" + (-8)] <- %"pr.58"]))
    => ret void
} }.

Definition fn_glibc_libc_start'23dlerror_handler : func :=
  ir_fn{ "local" "glibc_libc_start#dlerror_handler"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"__libc_dlerror_result_string";
    %"chk0" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk0" + 0] <- %"v0"
    => ret void
} }.

Definition fn_glibc_libc_start'23errno_handler : func :=
  ir_fn{ "local" "glibc_libc_start#errno_handler"(W %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk0" + 0] <- %"v0"
    => ret void
} }.

Definition fn_glibc_libc_start'23futex_wake : func :=
  ir_fn{ "local" "glibc_libc_start#futex_wake"(P %"v0", W %"v2", W %"v4") -> RVoid {
  @"start":
    %"v16" : W = (Cmp Eq W) %"v4", #0
    => br %"v16" ? "L18" : "L17";
  @"L17":
    %"v20" : W = (Cmp Eq W) %"v4", #128
    => goto "L18";
  @"L18" [%"v22" : W = phi("start" => #1, "L17" => %"v20")]:
    => br %"v22" ? "L11" : "L14";
  @"L14":
    %"v24" : P = Copy $"glibc_libc_start#str.322";
    %"v25" : P = Copy $"glibc_libc_start#str.323";
    %"v26" : P = Copy $"glibc_libc_start#str.324";
    %"v27" : P = Copy $"glibc_libc_start#str.325";
    call void $"zerrorf"(P %"v24", P %"v25", W #173, P %"v26", P %"v27")
    => goto "L11";
  @"L11":
    => br %"v16" ? "L30" : "L29";
  @"L29":
    => goto "L30";
  @"L30" [%"v33" : W = phi("L29" => #0, "L11" => #1)]:
    call void $"zsys_futex_wake"(P %"v0", W %"v2", W %"v33")
    => ret void
} }.

Definition fn_glibc_libc_start'23get_common_cache_info : func :=
  ir_fn{ "local" "glibc_libc_start#get_common_cache_info"(P %"v0", P %"v2", P %"v4", L %"v6", P %"v8") -> RVoid blocks ((app [ir_blk{ @"start":
    %"v10" : P = (Alloc 4) #4;
    %"v11" : P = (Alloc 4) #4;
    %"v12" : P = (Alloc 4) #4;
    %"v13" : P = (Alloc 4) #4;
    %"v17" : P = Copy $"_dl_x86_cpu_features";
    %"v20" = %"v17" +p #4;
    %"chk0" : A = (Check 0 4 Read 1) %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v24" = %"v17" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v24";
    %"v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v28" = %"v17" +p #12;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v28";
    %"v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"chk3" : A = (Check 0 8 Read 1) %"v0";
    %"v32" : L = (RawLoad LdL 0) %"chk3";
    %"chk4" : A = (Check 0 8 Read 1) %"v2";
    %"v35" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (Check 0 4 Read 1) %"v4";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v17";
    %"v48" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v49" : W = (Cmp Eq W) %"v48", #3
    => br %"v49" ? "L50" : "L51" };
  ir_blk{ @"L50":
    %"v53" : W = (Cmp Eq W) %"v25", #6
    => goto "L51" };
  ir_blk{ @"L51" [%"v55" : W = phi("start" => #0, "L50" => %"v53")]:
    => br %"v55" ? "L46" : "L45" };
  ir_blk{ @"L45":
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.46" : W = phi("L45" => #1, "L51" => #0)]:
    %"v61" : W = (Cmp Sle L) %"v32", #0
    => br %"v61" ? "L59" : "L58" };
  ir_blk{ @"L58":
    => goto "L59" };
  ir_blk{ @"L59" [%"pr.47" : W = phi("L58" => #3, "L46" => #2); %"pr.31" : L = phi("L58" => %"v35", "L46" => %"v6"); %"pr.28" : L = phi("L58" => %"v32", "L46" => %"v6"); %"pr.25" : W = phi("L58" => #0, "L46" => #4294967295)]:
    %"v68" : P = Copy $"_dl_x86_cpu_features";
    %"v69" = %"v68" +p #20;
    %"v71" = %"v69" +p #12;
    %"chk7" : A = (Check 0 4 Read 1) %"v71";
    %"v72" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v74" : W = And %"v72", #268435456;
    %"v75" : W = (Cmp Ne W) %"v74", #0
    => br %"v75" ? "L65" : "L67" };
  ir_blk{ @"L65":
    %"v80" : W = (Cmp Sge W) %"v21", #4
    => br %"v80" ? "L76" : "L154" };
  ir_blk{ @"L76":
    %"v84" : W = (Cmp Eq W) %"pr.25", #0;
    %"v85" : W = Shl %"v84", #1;
    %"v86" : W = Or %"v85", #1
    => goto "L87" };
  ir_blk{ @"L87" [%"pr.53" : W = phi("L76" => %"v86", "L160" => %"pr.50"); %"pr.49" : W = phi("L76" => #0, "L160" => %"v140"); %"pr.45" : W = phi("L76" => #1, "L160" => %"pr.41"); %"pr.26" : W = phi("L76" => %"pr.25", "L160" => %"pr.16"); %"pr.15" : W = phi("L76" => #0, "L160" => %"pr.2")]:
    %"v94" : L = Ptoi %"v8";
    %"v95" : L = Ptoi #0;
    %"v96" : W = (Cmp Ne L) %"v94", %"v95"
    => br %"v96" ? "L97" : "L98" };
  ir_blk{ @"L97":
    %"v101" = %"v8" +p #1;
    %"chk8" : A = (Check 0 1 Read 1) %"v101";
    %"v102" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v103" : W = (Cmp Slt W) %"pr.49", %"v102"
    => goto "L98" };
  ir_blk{ @"L98" [%"v105" : W = phi("L87" => #0, "L97" => %"v103")]:
    => br %"v105" ? "L90" : "L91" };
  ir_blk{ @"L90":
    %"v107" = %"v8" +p #20;
    %"v109" : L = (Ext Sw) %"pr.49";
    %"v110" : L = Shl %"v109", #4;
    %"v111" = %"v107" +p %"v110";
    %"chk9" : A = (Check 0 4 Read 1) %"v111";
    %"v113" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"chk10" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk10" + 0] <- %"v113";
    %"v120" = %"v111" +p #4;
    %"chk11" : A = (HalfCheck Upper 0 4 Read 1) %"chk9", %"v120";
    %"v121" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"chk12" : A = (Check 0 4 Write 1) %"v11";
    store Ww [%"chk12" + 0] <- %"v121";
    %"v128" = %"v111" +p #8;
    %"chk13" : A = (HalfCheck Upper 0 4 Read 1) %"chk9", %"v128";
    %"v129" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"chk14" : A = (Check 0 4 Write 1) %"v12";
    store Ww [%"chk14" + 0] <- %"v129";
    %"v136" = %"v111" +p #12;
    %"chk15" : A = (HalfCheck Upper 0 4 Read 1) %"chk9", %"v136";
    %"v137" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"chk16" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk16" + 0] <- %"v137"
    => goto "L92" };
  ir_blk{ @"L91":
    call void $"zcpuid_count"(W #4, W %"pr.49", P %"v10", P %"v11", P %"v12", P %"v13")
    => goto "L92" };
  ir_blk{ @"L92":
    %"v140" : W = Add %"pr.49", #1;
    %"chk17" : A = (Renew 0 4 Read 1) %"chk6", %"v17";
    %"v145" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v146" : W = (Cmp Eq W) %"v145", #1
    => br %"v146" ? "L147" : "L148" };
  ir_blk{ @"L147":
    %"chk18" : A = (Check 0 4 Read 1) %"v10";
    %"v149" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v150" : W = And %"v149", #31;
    %"v151" : W = (Cmp Eq W) %"v150", #0
    => goto "L148" };
  ir_blk{ @"L148" [%"v153" : W = phi("L92" => #0, "L147" => %"v151")]:
    => br %"v153" ? "L154" : "L143" };
  ir_blk{ @"L143":
    %"chk19" : A = (Check 0 4 Read 1) %"v10";
    %"v156" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v157" : W = Shr %"v156", #5;
    %"v158" : W = And %"v157", #7;
    %"v193" : W = (Cmp Eq W) %"v158", #2
    => br %"v193" ? "L162" : "L194" };
  ir_blk{ @"L162":
    %"v167" : W = And %"pr.53", #1
    => br %"v167" ? "L163" : "L160" };
  ir_blk{ @"L163":
    %"v168" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v169" : W = Shr %"v168", #14;
    %"v170" : W = And %"v169", #1023;
    %"v173" : W = And %"pr.53", #4294967294
    => goto "L160" };
  ir_blk{ @"L174":
    %"v180" : W = And %"pr.53", #2
    => br %"v180" ? "L175" : "L160" };
  ir_blk{ @"L175":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk19", %"v10";
    %"v181" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v182" : W = Shr %"v181", #14;
    %"v183" : W = And %"v182", #1023;
    %"chk22" : A = (Check 0 4 Read 1) %"v13";
    %"v184" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v185" : W = And %"v184", #2;
    %"v186" : W = (Cmp Ne W) %"v185", #0;
    %"v191" : W = And %"pr.53", #4294967293
    => goto "L160" };
  ir_blk{ @"L194":
    %"v195" : W = (Cmp Eq W) %"v158", #3
    => br %"v195" ? poll "L174" : "L160" };
  ir_blk{ @"L160" [%"pr.50" : W = phi("L163" => %"v173", "L162" => %"pr.53", "L175" => %"v191", "L174" => %"pr.53", "L194" => %"pr.53"); %"pr.41" : W = phi("L163" => %"pr.45", "L162" => %"pr.45", "L175" => %"v186", "L174" => %"pr.45", "L194" => %"pr.45"); %"pr.16" : W = phi("L163" => %"pr.26", "L162" => %"pr.26", "L175" => %"v183", "L174" => %"pr.26", "L194" => %"pr.26"); %"pr.2" : W = phi("L163" => %"v170", "L162" => %"pr.15", "L175" => %"pr.15", "L174" => %"pr.15", "L194" => %"pr.15")]:
    => br %"pr.50" ? poll "L87" : "L89" };
  ir_blk{ @"L89":
    %"v202" : W = (Cmp Sge W) %"v21", #11
    => br %"v202" ? "L203" : "L204" };
  ir_blk{ @"L203":
    => goto "L204" };
  ir_blk{ @"L204" [%"v207" : W = phi("L89" => #0, "L203" => %"pr.46")]:
    => br %"v207" ? "L198" : "L200" };
  ir_blk{ @"L198":
    %"v210" : W = (Cmp Sgt W) %"pr.2", #0
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v214" : W = (Cmp Eq W) %"pr.47", #3
    => goto "L212" };
  ir_blk{ @"L212" [%"v216" : W = phi("L198" => #0, "L211" => %"v214")]:
    %"v218" : W = (Cmp Sgt W) %"pr.16", #0
    => br %"v218" ? "L220" : "L219" };
  ir_blk{ @"L219":
    => br %"v210" ? "L223" : "L220" };
  ir_blk{ @"L223":
    %"v226" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L220" };
  ir_blk{ @"L220" [%"v230" : W = phi("L212" => #1, "L219" => #0, "L223" => %"v226")]:
    %"v231" : W = Shl %"v230", #1;
    %"v232" : W = Or %"v216", %"v231"
    => goto "L233" };
  ir_blk{ @"L233" [%"pr.54" : W = phi("L220" => %"v232", "L259" => %"pr.55"); %"pr.48" : W = phi("L220" => #0, "L259" => %"v238"); %"pr.19" : W = phi("L220" => %"pr.16", "L259" => %"pr.20"); %"pr.5" : W = phi("L220" => %"pr.2", "L259" => %"pr.6")]:
    => br %"pr.54" ? "L234" : "L200" };
  ir_blk{ @"L234":
    %"v238" : W = Add %"pr.48", #1;
    call void $"zcpuid_count"(W #11, W %"pr.48", P %"v10", P %"v11", P %"v12", P %"v13");
    %"chk23" : A = (Check 0 4 Read 1) %"v11";
    %"v240" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v241" : W = And %"v240", #255;
    %"chk24" : A = (Check 0 4 Read 1) %"v12";
    %"v243" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"v244" : W = And %"v243", #65280;
    %"v249" : W = (Cmp Eq W) %"v241", #0
    => br %"v249" ? "L251" : "L250" };
  ir_blk{ @"L250":
    %"v253" : W = (Cmp Eq W) %"v244", #0
    => goto "L251" };
  ir_blk{ @"L251" [%"v255" : W = phi("L234" => #1, "L250" => %"v253")]:
    => br %"v255" ? "L200" : "L246" };
  ir_blk{ @"L246":
    %"v261" : W = (Cmp Eq W) %"v244", #256
    => br %"v261" ? "L257" : "L258" };
  ir_blk{ @"L257":
    %"v266" : W = And %"pr.54", #1
    => br %"v266" ? "L262" : "L259" }] [ir_blk{ @"L262":
    %"v269" : L = (Ext Uw) %"pr.5";
    %"v270" : L = Shr %"v269", #1;
    %"v271" : L = Or %"v269", %"v270";
    %"v272" : L = Shr %"v271", #2;
    %"v273" : L = Or %"v271", %"v272";
    %"v274" : L = Shr %"v273", #4;
    %"v275" : L = Or %"v273", %"v274";
    %"v276" : L = Shr %"v275", #8;
    %"v277" : L = Or %"v275", %"v276";
    %"v278" : L = Shr %"v277", #16;
    %"v279" : L = Or %"v277", %"v278";
    %"v280" : L = Shr %"v279", #32;
    %"v281" : L = Or %"v279", %"v280";
    %"v282" : L = Shr %"v281", #1;
    %"v283" : L = And %"v282", #6148914691236517205;
    %"v284" : L = Sub %"v281", %"v283";
    %"v285" : L = And %"v284", #3689348814741910323;
    %"v286" : L = Shr %"v284", #2;
    %"v287" : L = And %"v286", #3689348814741910323;
    %"v288" : L = Add %"v285", %"v287";
    %"v289" : L = Shr %"v288", #4;
    %"v290" : L = Add %"v288", %"v289";
    %"v291" : L = And %"v290", #1085102592571150095;
    %"v292" : L = Mul %"v291", #72340172838076673;
    %"v293" : L = Shr %"v292", #56;
    %"v294" : L = Sub %"v293", #32;
    %"v295" : L = Neg %"v294";
    %"v296" : W = Xor %"v295", #31;
    %"v299" : W = Add %"v296", #1;
    %"v300" : W = Shl #4294967295, %"v299";
    %"v301" : W = Xor %"v300", #(-1);
    %"v303" : W = Sub %"v241", #1;
    %"v305" : W = And %"v303", %"v301";
    %"v308" : W = And %"pr.54", #4294967294
    => goto "L259" };
  ir_blk{ @"L258":
    %"v313" : W = (Cmp Eq W) %"v244", #512
    => br %"v313" ? "L309" : "L259" };
  ir_blk{ @"L309":
    %"v319" : W = And %"pr.54", #2
    => br %"v319" ? "L314" : "L259" };
  ir_blk{ @"L314":
    %"v326" : W = (Cmp Eq W) %"pr.47", #2
    => br %"v326" ? "L324" : "L323" };
  ir_blk{ @"L323":
    => goto "L324" };
  ir_blk{ @"L324" [%"v329" : W = phi("L323" => %"pr.19", "L314" => %"pr.5")]:
    %"v331" : L = (Ext Uw) %"v329";
    %"v332" : L = Shr %"v331", #1;
    %"v333" : L = Or %"v331", %"v332";
    %"v334" : L = Shr %"v333", #2;
    %"v335" : L = Or %"v333", %"v334";
    %"v336" : L = Shr %"v335", #4;
    %"v337" : L = Or %"v335", %"v336";
    %"v338" : L = Shr %"v337", #8;
    %"v339" : L = Or %"v337", %"v338";
    %"v340" : L = Shr %"v339", #16;
    %"v341" : L = Or %"v339", %"v340";
    %"v342" : L = Shr %"v341", #32;
    %"v343" : L = Or %"v341", %"v342";
    %"v344" : L = Shr %"v343", #1;
    %"v345" : L = And %"v344", #6148914691236517205;
    %"v346" : L = Sub %"v343", %"v345";
    %"v347" : L = And %"v346", #3689348814741910323;
    %"v348" : L = Shr %"v346", #2;
    %"v349" : L = And %"v348", #3689348814741910323;
    %"v350" : L = Add %"v347", %"v349";
    %"v351" : L = Shr %"v350", #4;
    %"v352" : L = Add %"v350", %"v351";
    %"v353" : L = And %"v352", #1085102592571150095;
    %"v354" : L = Mul %"v353", #72340172838076673;
    %"v355" : L = Shr %"v354", #56;
    %"v356" : L = Sub %"v355", #32;
    %"v357" : L = Neg %"v356";
    %"v358" : W = Xor %"v357", #31;
    %"v361" : W = Add %"v358", #1;
    %"v362" : W = Shl #4294967295, %"v361";
    %"v363" : W = Xor %"v362", #(-1);
    %"v365" : W = Sub %"v241", #1;
    %"v367" : W = And %"v365", %"v363"
    => br %"v326" ? "L370" : "L369" };
  ir_blk{ @"L369":
    => goto "L370" };
  ir_blk{ @"L370" [%"pr.23" : W = phi("L369" => %"v367", "L324" => %"pr.19"); %"pr.10" : W = phi("L369" => %"pr.5", "L324" => %"v367")]:
    %"v378" : W = And %"pr.54", #4294967293
    => goto "L259" };
  ir_blk{ @"L259" [%"pr.55" : W = phi("L262" => %"v308", "L257" => %"pr.54", "L370" => %"v378", "L309" => %"pr.54", "L258" => %"pr.54"); %"pr.20" : W = phi("L262" => %"pr.19", "L257" => %"pr.19", "L370" => %"pr.23", "L309" => %"pr.19", "L258" => %"pr.19"); %"pr.6" : W = phi("L262" => %"v305", "L257" => %"pr.5", "L370" => %"pr.10", "L309" => %"pr.5", "L258" => %"pr.5")]:
    => goto poll "L233" };
  ir_blk{ @"L200" [%"pr.18" : W = phi("L233" => %"pr.19", "L251" => %"pr.19", "L204" => %"pr.16"); %"pr.4" : W = phi("L233" => %"pr.5", "L251" => %"pr.5", "L204" => %"pr.2")]:
    %"v383" : W = (Cmp Sgt W) %"pr.4", #0
    => br %"v383" ? "L379" : "L381" };
  ir_blk{ @"L379":
    %"v385" : W = Add %"pr.4", #1
    => goto "L381" };
  ir_blk{ @"L381" [%"pr.11" : W = phi("L379" => %"v385", "L200" => %"pr.4")]:
    %"v390" : W = (Cmp Sgt W) %"pr.18", #0
    => br %"v390" ? "L386" : "L388" };
  ir_blk{ @"L386":
    %"v392" : W = Add %"pr.18", #1
    => goto "L388" };
  ir_blk{ @"L388" [%"pr.24" : W = phi("L386" => %"v392", "L381" => %"pr.18")]:
    %"v397" : W = (Cmp Eq W) %"pr.47", #2
    => br %"v397" ? "L393" : "L394" };
  ir_blk{ @"L393":
    => br %"pr.11" ? "L398" : "L78" };
  ir_blk{ @"L398":
    %"chk25" : A = (Renew 0 4 Read 1) %"chk6", %"v17";
    %"v407" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v408" : W = (Cmp Eq W) %"v407", #1
    => br %"v408" ? "L409" : "L410" };
  ir_blk{ @"L409":
    %"v412" : W = (Cmp Ugt W) %"pr.11", #2
    => goto "L410" };
  ir_blk{ @"L410" [%"v414" : W = phi("L398" => #0, "L409" => %"v412")]:
    => br %"v414" ? "L415" : "L416" };
  ir_blk{ @"L415":
    %"v418" : W = (Cmp Eq W) %"v25", #6
    => goto "L416" };
  ir_blk{ @"L416" [%"v420" : W = phi("L410" => #0, "L415" => %"v418")]:
    => br %"v420" ? "L422" : "L78" };
  ir_blk{ @"L422":
    %"v431" : W = (Cmp Ult W) %"v29", #77
    => br %"v431" ? "L432" : "L433" };
  ir_blk{ @"L432":
    %"v434" : W = (Cmp Eq W) %"v29", #55
    => br %"v434" ? "L78" : "L435" };
  ir_blk{ @"L435":
    %"v436" : W = (Cmp Eq W) %"v29", #74
    => br %"v436" ? "L78" : "L437" };
  ir_blk{ @"L437":
    => goto "L78" };
  ir_blk{ @"L433":
    %"v438" : W = (Cmp Eq W) %"v29", #77
    => br %"v438" ? "L78" : "L439" };
  ir_blk{ @"L439":
    %"v440" : W = (Cmp Eq W) %"v29", #90
    => br %"v440" ? "L78" : "L441" };
  ir_blk{ @"L441":
    %"v442" : W = (Cmp Eq W) %"v29", #93
    => br %"v442" ? "L78" : "L443" };
  ir_blk{ @"L443":
    => goto "L78" };
  ir_blk{ @"L394":
    => br %"pr.24" ? "L78" : "L445" };
  ir_blk{ @"L445":
    => goto "L78" };
  ir_blk{ @"L154" [%"pr.40" : W = phi("L148" => %"pr.45", "L65" => #1); %"pr.1" : W = phi("L148" => %"pr.15", "L65" => #0)]:
    %"v450" = %"v17" +p #20;
    %"v452" = %"v450" +p #4;
    %"chk26" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v452";
    %"v453" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v454" : W = Shr %"v453", #16;
    %"v455" : W = And %"v454", #255
    => goto "L78" };
  ir_blk{ @"L78" [%"pr.44" : W = phi("L154" => %"pr.40", "L441" => %"pr.41", "L439" => %"pr.41", "L433" => %"pr.41", "L435" => %"pr.41", "L432" => %"pr.41", "L437" => %"pr.41", "L443" => %"pr.41", "L416" => %"pr.41", "L393" => %"pr.41", "L445" => %"pr.41", "L394" => %"pr.41"); %"pr.39" : W = phi("L154" => %"v455", "L441" => #2, "L439" => #2, "L433" => #2, "L435" => #2, "L432" => #2, "L437" => %"pr.11", "L443" => %"pr.11", "L416" => %"pr.11", "L393" => %"v38", "L445" => %"v38", "L394" => %"pr.24"); %"pr.14" : W = phi("L154" => %"pr.1", "L441" => %"pr.11", "L439" => %"pr.11", "L433" => %"pr.11", "L435" => %"pr.11", "L432" => %"pr.11", "L437" => %"pr.11", "L443" => %"pr.11", "L416" => %"pr.11", "L393" => %"pr.11", "L445" => %"pr.11", "L394" => %"pr.11")]:
    %"v460" : W = (Cmp Sgt L) %"pr.31", #0
    => br %"v460" ? "L461" : "L462" };
  ir_blk{ @"L461":
    %"v464" : W = (Cmp Ugt W) %"pr.39", #0
    => goto "L462" };
  ir_blk{ @"L462" [%"v466" : W = phi("L78" => #0, "L461" => %"v464")]:
    => br %"v466" ? "L456" : "L67" };
  ir_blk{ @"L456":
    %"v469" : L = (Ext Uw) %"pr.39";
    %"v470" : L = Div %"pr.31", %"v469"
    => goto "L67" };
  ir_blk{ @"L67" [%"pr.43" : W = phi("L456" => %"pr.44", "L462" => %"pr.44", "L59" => #1); %"pr.38" : W = phi("L456" => %"pr.39", "L462" => %"pr.39", "L59" => %"v38"); %"pr.32" : L = phi("L456" => %"v470", "L462" => %"pr.31", "L59" => %"pr.31"); %"pr.13" : W = phi("L456" => %"pr.14", "L462" => %"pr.14", "L59" => #0)]:
    %"v474" : W = (Ext Ub) %"pr.43";
    %"v475" : W = (Cmp Eq W) %"v474", #0
    => br %"v475" ? "L471" : "L473" };
  ir_blk{ @"L471":
    %"v481" : W = (Cmp Sgt W) %"pr.13", #0
    => br %"v481" ? "L477" : "L479" };
  ir_blk{ @"L477":
    %"v484" : L = (Ext Sw) %"pr.13";
    %"v485" : L = Div %"v6", %"v484"
    => goto "L479" };
  ir_blk{ @"L479" [%"v487" : L = phi("L477" => %"v485", "L471" => %"v6")]:
    %"v490" : L = Add %"pr.32", %"v487";
    %"v493" : L = Add %"pr.28", %"v6"
    => goto "L473" };
  ir_blk{ @"L473" [%"pr.30" : L = phi("L479" => %"v490", "L67" => %"pr.32"); %"pr.27" : L = phi("L479" => %"v493", "L67" => %"pr.28")]:
    %"chk27" : A = (Renew 0 8 Write 1) %"chk3", %"v0";
    store Wl [%"chk27" + 0] <- %"pr.27";
    %"chk28" : A = (Renew 0 8 Write 1) %"chk4", %"v2";
    store Wl [%"chk28" + 0] <- %"pr.30";
    %"chk29" : A = (Renew 0 4 Write 1) %"chk5", %"v4";
    store Ww [%"chk29" + 0] <- %"pr.38"
    => ret void }])) }.

Definition fn_glibc_libc_start'23get_common_indices : func :=
  ir_fn{ "local" "glibc_libc_start#get_common_indices"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8") -> RVoid {
  @"start":
    %"v16" : P = (Alloc 4) #4;
    %"v14" : L = Ptoi %"v2";
    %"v15" : W = (Cmp Ne L) %"v14", #0
    => br %"v15" ? "L10" : "L12";
  @"L10":
    %"v18" = %"v0" +p #20;
    %"v20" = %"v18" +p #4;
    %"v24" = %"v18" +p #8;
    %"v28" = %"v18" +p #12;
    call void $"zcpuid"(W #1, P %"v16", P %"v20", P %"v24", P %"v28");
    %"chk0" : A = (Check 0 4 Read 1) %"v16";
    %"v32" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v18";
    store Ww [%"chk1" + 0] <- %"v32";
    %"v34" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v35" : W = Shr %"v34", #8;
    %"v36" : W = And %"v35", #15;
    %"chk3" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk3" + 0] <- %"v36";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v39" : W = Shr %"v38", #4;
    %"v40" : W = And %"v39", #15;
    %"chk5" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk5" + 0] <- %"v40";
    %"v42" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v43" : W = Shr %"v42", #12;
    %"v44" : W = And %"v43", #240;
    %"chk7" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk7" + 0] <- %"v44";
    %"v46" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v47" : W = And %"v46", #15;
    %"chk9" : A = (Check 0 4 Write 1) %"v8";
    store Ww [%"chk9" + 0] <- %"v47";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v53" : W = (Cmp Eq W) %"v52", #15
    => br %"v53" ? "L48" : "L12";
  @"L48":
    %"v55" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v56" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v57" : W = Shr %"v56", #20;
    %"v58" : W = And %"v57", #255;
    %"v59" : W = Add %"v55", %"v58";
    store Ww [%"chk3" + 0] <- %"v59";
    %"v61" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v63" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v64" : W = Add %"v61", %"v63";
    store Ww [%"chk5" + 0] <- %"v64"
    => goto "L12";
  @"L12":
    %"v69" = %"v0" +p #4;
    %"chk17" : A = (Check 0 4 Read 1) %"v69";
    %"v70" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v71" : W = (Cmp Sge W) %"v70", #7
    => br %"v71" ? "L65" : "L67";
  @"L65":
    %"v73" = %"v0" +p #20;
    %"v74" = %"v73" +p #32;
    %"v78" = %"v74" +p #4;
    %"v82" = %"v74" +p #8;
    %"v86" = %"v74" +p #12;
    call void $"zcpuid_count"(W #7, W #0, P %"v74", P %"v78", P %"v82", P %"v86");
    %"v89" = %"v73" +p #192;
    %"v93" = %"v89" +p #4;
    %"v97" = %"v89" +p #8;
    %"v101" = %"v89" +p #12;
    call void $"zcpuid_count"(W #7, W #1, P %"v89", P %"v93", P %"v97", P %"v101")
    => goto "L67";
  @"L67":
    %"v106" = %"v0" +p #4;
    %"chk18" : A = (Renew 0 4 Read 1) %"chk17", %"v106";
    %"v107" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v108" : W = (Cmp Sge W) %"v107", #13
    => br %"v108" ? "L102" : "L104";
  @"L102":
    %"v110" = %"v0" +p #20;
    %"v111" = %"v110" +p #96;
    %"v115" = %"v111" +p #4;
    %"v119" = %"v111" +p #8;
    %"v123" = %"v111" +p #12;
    call void $"zcpuid_count"(W #13, W #1, P %"v111", P %"v115", P %"v119", P %"v123")
    => goto "L104";
  @"L104":
    %"v128" = %"v0" +p #4;
    %"chk19" : A = (Renew 0 4 Read 1) %"chk17", %"v128";
    %"v129" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v130" : W = (Cmp Sge W) %"v129", #20
    => br %"v130" ? "L124" : "L126";
  @"L124":
    %"v132" = %"v0" +p #20;
    %"v133" = %"v132" +p #256;
    %"v137" = %"v133" +p #4;
    %"v141" = %"v133" +p #8;
    %"v145" = %"v133" +p #12;
    call void $"zcpuid_count"(W #20, W #0, P %"v133", P %"v137", P %"v141", P %"v145")
    => goto "L126";
  @"L126":
    %"v150" = %"v0" +p #4;
    %"chk20" : A = (Renew 0 4 Read 1) %"chk17", %"v150";
    %"v151" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"v152" : W = (Cmp Sge W) %"v151", #25
    => br %"v152" ? "L146" : "iw_1.start";
  @"L146":
    %"v154" = %"v0" +p #20;
    %"v155" = %"v154" +p #224;
    %"v159" = %"v155" +p #4;
    %"v163" = %"v155" +p #8;
    %"v167" = %"v155" +p #12;
    call void $"zcpuid_count"(W #25, W #0, P %"v155", P %"v159", P %"v163", P %"v167")
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v40" : P = (Alloc 4) #4;
    %"iw_1.v41" : P = (Alloc 4) #4;
    %"iw_1.v42" : P = (Alloc 4) #4;
    %"iw_1.v43" : P = (Alloc 4) #4;
    %"iw_1.v5" : P = Copy $"_dl_minsigstacksize";
    %"chk21" : A = (Check 0 8 Read 1) %"iw_1.v5";
    %"iw_1.v6" : L = (RawLoad LdL 0) %"chk21";
    %"iw_1.v7" : W = (Cmp Ne L) %"iw_1.v6", #0
    => br %"iw_1.v7" ? "iw_1.join" : "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v13" = %"v0" +p #4;
    %"chk22" : A = (Renew 0 4 Read 1) %"chk17", %"iw_1.v13";
    %"iw_1.v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"iw_1.v15" : W = (Cmp Sge W) %"iw_1.v14", #13
    => br %"iw_1.v15" ? "iw_1.L16" : "iw_1.L17";
  @"iw_1.L16":
    %"iw_1.v19" = %"v0" +p #20;
    %"iw_1.v21" = %"iw_1.v19" +p #8;
    %"chk23" : A = (HalfCheck Upper 0 4 Read 1) %"chk17", %"iw_1.v21";
    %"iw_1.v22" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"iw_1.v24" : W = And %"iw_1.v22", #134217728;
    %"iw_1.v25" : W = (Cmp Ne W) %"iw_1.v24", #0
    => goto "iw_1.L17";
  @"iw_1.L17" [%"iw_1.v27" : W = phi("iw_1.L4" => #0, "iw_1.L16" => %"iw_1.v25")]:
    => br %"iw_1.v27" ? "iw_1.L9" : "iw_1.L10";
  @"iw_1.L9":
    call void $"zcpuid_count"(W #13, W #0, P %"iw_1.v40", P %"iw_1.v41", P %"iw_1.v42", P %"iw_1.v43");
    %"chk24" : A = (Check 0 4 Read 1) %"iw_1.v41";
    %"iw_1.v45" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"iw_1.v46" : W = Add %"iw_1.v45", #512;
    %"iw_1.v48" : L = (Ext Uw) %"iw_1.v46";
    %"iw_1.v49" : L = Add %"iw_1.v48", #4;
    %"iw_1.v50" : P = Copy $"_dl_minsigstacksize";
    %"iw_1.v51" : W = Copy %"iw_1.v49";
    %"iw_1.v52" : L = (Ext Uw) %"iw_1.v51";
    %"chk25" : A = (Check 0 8 Write 1) %"iw_1.v50";
    store Wl [%"chk25" + 0] <- %"iw_1.v52"
    => goto "iw_1.join";
  @"iw_1.L10":
    %"iw_1.v53" : P = Copy $"_dl_minsigstacksize";
    %"chk26" : A = (Check 0 8 Write 1) %"iw_1.v53";
    store Wl [%"chk26" + 0] <- #2048
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition fn_glibc_libc_start'23get_isa_level : func :=
  ir_fn{ "local" "glibc_libc_start#get_isa_level"(P %"v0") -> (RClass W) {
  @"start":
    %"v7" = %"v0" +p #20;
    %"v9" = %"v7" +p #16;
    %"v10" = %"v9" +p #12;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v13" : W = And %"v11", #32768;
    %"v14" : W = (Cmp Ne W) %"v13", #0
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v18" = %"v0" +p #20;
    %"v20" = %"v18" +p #16;
    %"v21" = %"v20" +p #12;
    %"v22" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v24" : W = And %"v22", #256;
    %"v25" : W = (Cmp Ne W) %"v24", #0
    => goto "L16";
  @"L16" [%"v27" : W = phi("start" => #0, "L15" => %"v25")]:
    => br %"v27" ? "L28" : "L29";
  @"L28":
    %"v31" = %"v0" +p #20;
    %"v33" = %"v31" +p #12;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v33";
    %"v34" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v36" : W = And %"v34", #1
    => goto "L29";
  @"L29" [%"v39" : W = phi("L16" => #0, "L28" => %"v36")]:
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v43" = %"v0" +p #20;
    %"v45" = %"v43" +p #16;
    %"v46" = %"v45" +p #12;
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v49" : W = And %"v47", #16777216;
    %"v50" : W = (Cmp Ne W) %"v49", #0
    => goto "L41";
  @"L41" [%"v52" : W = phi("L29" => #0, "L40" => %"v50")]:
    => br %"v52" ? "L53" : "L54";
  @"L53":
    %"v56" = %"v0" +p #20;
    %"v58" = %"v56" +p #16;
    %"v59" = %"v58" +p #12;
    %"v60" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v62" : W = And %"v60", #8388608;
    %"v63" : W = (Cmp Ne W) %"v62", #0
    => goto "L54";
  @"L54" [%"v65" : W = phi("L41" => #0, "L53" => %"v63")]:
    => br %"v65" ? "L66" : "L67";
  @"L66":
    %"v69" = %"v0" +p #20;
    %"v71" = %"v69" +p #16;
    %"v72" = %"v71" +p #12;
    %"v73" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v75" : W = And %"v73", #33554432;
    %"v76" : W = (Cmp Ne W) %"v75", #0
    => goto "L67";
  @"L67" [%"v78" : W = phi("L54" => #0, "L66" => %"v76")]:
    => br %"v78" ? "L79" : "L80";
  @"L79":
    %"v82" = %"v0" +p #20;
    %"v84" = %"v82" +p #16;
    %"v85" = %"v84" +p #12;
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v88" : W = And %"v86", #67108864;
    %"v89" : W = (Cmp Ne W) %"v88", #0
    => goto "L80";
  @"L80" [%"v91" : W = phi("L67" => #0, "L79" => %"v89")]:
    => br %"v91" ? "L3" : "L5";
  @"L3":
    %"v97" = %"v0" +p #20;
    %"v99" = %"v97" +p #16;
    %"v100" = %"v99" +p #8;
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v100";
    %"v101" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v103" : W = And %"v101", #8192;
    %"v104" : W = (Cmp Ne W) %"v103", #0
    => br %"v104" ? "L105" : "L106";
  @"L105":
    %"v108" = %"v0" +p #20;
    %"v109" = %"v108" +p #64;
    %"v110" = %"v109" +p #16;
    %"v111" = %"v110" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v111";
    %"v112" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v114" : W = And %"v112", #1
    => goto "L106";
  @"L106" [%"v117" : W = phi("L3" => #0, "L105" => %"v114")]:
    => br %"v117" ? "L118" : "L119";
  @"L118":
    %"v121" = %"v0" +p #20;
    %"v123" = %"v121" +p #16;
    %"v124" = %"v123" +p #8;
    %"v125" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v127" : W = And %"v125", #8388608;
    %"v128" : W = (Cmp Ne W) %"v127", #0
    => goto "L119";
  @"L119" [%"v130" : W = phi("L106" => #0, "L118" => %"v128")]:
    => br %"v130" ? "L131" : "L132";
  @"L131":
    %"v134" = %"v0" +p #20;
    %"v136" = %"v134" +p #16;
    %"v137" = %"v136" +p #8;
    %"v138" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v140" : W = And %"v138", #1
    => goto "L132";
  @"L132" [%"v143" : W = phi("L119" => #0, "L131" => %"v140")]:
    => br %"v143" ? "L144" : "L145";
  @"L144":
    %"v147" = %"v0" +p #20;
    %"v149" = %"v147" +p #16;
    %"v150" = %"v149" +p #8;
    %"v151" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v153" : W = And %"v151", #512;
    %"v154" : W = (Cmp Ne W) %"v153", #0
    => goto "L145";
  @"L145" [%"v156" : W = phi("L132" => #0, "L144" => %"v154")]:
    => br %"v156" ? "L157" : "L158";
  @"L157":
    %"v160" = %"v0" +p #20;
    %"v162" = %"v160" +p #16;
    %"v163" = %"v162" +p #8;
    %"v164" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v166" : W = And %"v164", #524288;
    %"v167" : W = (Cmp Ne W) %"v166", #0
    => goto "L158";
  @"L158" [%"v169" : W = phi("L145" => #0, "L157" => %"v167")]:
    => br %"v169" ? "L170" : "L171";
  @"L170":
    %"v173" = %"v0" +p #20;
    %"v175" = %"v173" +p #16;
    %"v176" = %"v175" +p #8;
    %"v177" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v179" : W = And %"v177", #1048576;
    %"v180" : W = (Cmp Ne W) %"v179", #0
    => goto "L171";
  @"L171" [%"v182" : W = phi("L158" => #0, "L170" => %"v180")]:
    => br %"v182" ? "L93" : "L5";
  @"L93":
    %"v190" = %"v0" +p #20;
    %"v192" = %"v190" +p #16;
    %"v193" = %"v192" +p #8;
    %"v194" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v196" : W = And %"v194", #268435456;
    %"v197" : W = (Cmp Ne W) %"v196", #0
    => br %"v197" ? "L198" : "L199";
  @"L198":
    %"v201" = %"v0" +p #20;
    %"v202" = %"v201" +p #32;
    %"v203" = %"v202" +p #16;
    %"v204" = %"v203" +p #4;
    %"chk15" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v204";
    %"v205" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"v207" : W = And %"v205", #32;
    %"v208" : W = (Cmp Ne W) %"v207", #0
    => goto "L199";
  @"L199" [%"v210" : W = phi("L93" => #0, "L198" => %"v208")]:
    => br %"v210" ? "L211" : "L212";
  @"L211":
    %"v214" = %"v0" +p #20;
    %"v215" = %"v214" +p #32;
    %"v216" = %"v215" +p #16;
    %"v217" = %"v216" +p #4;
    %"chk16" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v217";
    %"v218" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"v220" : W = And %"v218", #8;
    %"v221" : W = (Cmp Ne W) %"v220", #0
    => goto "L212";
  @"L212" [%"v223" : W = phi("L199" => #0, "L211" => %"v221")]:
    => br %"v223" ? "L224" : "L225";
  @"L224":
    %"v227" = %"v0" +p #20;
    %"v228" = %"v227" +p #32;
    %"v229" = %"v228" +p #16;
    %"v230" = %"v229" +p #4;
    %"chk17" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v230";
    %"v231" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v233" : W = And %"v231", #256;
    %"v234" : W = (Cmp Ne W) %"v233", #0
    => goto "L225";
  @"L225" [%"v236" : W = phi("L212" => #0, "L224" => %"v234")]:
    => br %"v236" ? "L237" : "L238";
  @"L237":
    %"v240" = %"v0" +p #20;
    %"v242" = %"v240" +p #16;
    %"v243" = %"v242" +p #8;
    %"v244" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v246" : W = And %"v244", #536870912;
    %"v247" : W = (Cmp Ne W) %"v246", #0
    => goto "L238";
  @"L238" [%"v249" : W = phi("L225" => #0, "L237" => %"v247")]:
    => br %"v249" ? "L250" : "L251";
  @"L250":
    %"v253" = %"v0" +p #20;
    %"v255" = %"v253" +p #16;
    %"v256" = %"v255" +p #8;
    %"v257" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v259" : W = And %"v257", #4096;
    %"v260" : W = (Cmp Ne W) %"v259", #0
    => goto "L251";
  @"L251" [%"v262" : W = phi("L238" => #0, "L250" => %"v260")]:
    => br %"v262" ? "L263" : "L264";
  @"L263":
    %"v266" = %"v0" +p #20;
    %"v267" = %"v266" +p #64;
    %"v268" = %"v267" +p #16;
    %"v269" = %"v268" +p #8;
    %"chk20" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v269";
    %"v270" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v272" : W = And %"v270", #32;
    %"v273" : W = (Cmp Ne W) %"v272", #0
    => goto "L264";
  @"L264" [%"v275" : W = phi("L251" => #0, "L263" => %"v273")]:
    => br %"v275" ? "L276" : "L277";
  @"L276":
    %"v279" = %"v0" +p #20;
    %"v281" = %"v279" +p #16;
    %"v282" = %"v281" +p #8;
    %"v283" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v285" : W = And %"v283", #4194304;
    %"v286" : W = (Cmp Ne W) %"v285", #0
    => goto "L277";
  @"L277" [%"v288" : W = phi("L264" => #0, "L276" => %"v286")]:
    => br %"v288" ? "L186" : "L5";
  @"L186":
    %"v296" = %"v0" +p #20;
    %"v297" = %"v296" +p #32;
    %"v298" = %"v297" +p #16;
    %"v299" = %"v298" +p #4;
    %"chk22" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v299";
    %"v300" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v302" : W = And %"v300", #65536;
    %"v303" : W = (Cmp Ne W) %"v302", #0
    => br %"v303" ? "L304" : "L305";
  @"L304":
    %"v307" = %"v0" +p #20;
    %"v308" = %"v307" +p #32;
    %"v309" = %"v308" +p #16;
    %"v310" = %"v309" +p #4;
    %"v311" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v313" : W = And %"v311", #1073741824;
    %"v314" : W = (Cmp Ne W) %"v313", #0
    => goto "L305";
  @"L305" [%"v316" : W = phi("L186" => #0, "L304" => %"v314")]:
    => br %"v316" ? "L317" : "L318";
  @"L317":
    %"v320" = %"v0" +p #20;
    %"v321" = %"v320" +p #32;
    %"v322" = %"v321" +p #16;
    %"v323" = %"v322" +p #4;
    %"v324" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v326" : W = And %"v324", #268435456;
    %"v327" : W = (Cmp Ne W) %"v326", #0
    => goto "L318";
  @"L318" [%"v329" : W = phi("L305" => #0, "L317" => %"v327")]:
    => br %"v329" ? "L330" : "L331";
  @"L330":
    %"v333" = %"v0" +p #20;
    %"v334" = %"v333" +p #32;
    %"v335" = %"v334" +p #16;
    %"v336" = %"v335" +p #4;
    %"v337" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v339" : W = And %"v337", #131072;
    %"v340" : W = (Cmp Ne W) %"v339", #0
    => goto "L331";
  @"L331" [%"v342" : W = phi("L318" => #0, "L330" => %"v340")]:
    => br %"v342" ? "L343" : "L344";
  @"L343":
    %"v346" = %"v0" +p #20;
    %"v347" = %"v346" +p #32;
    %"v348" = %"v347" +p #16;
    %"v349" = %"v348" +p #4;
    %"v350" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v352" : W = And %"v350", #2147483648;
    %"v353" : W = (Cmp Ne W) %"v352", #0
    => goto "L344";
  @"L344" [%"v355" : W = phi("L331" => #0, "L343" => %"v353")]:
    => br %"v355" ? "L5" : "L293";
  @"L293":
    => goto "L5";
  @"L5" [%"pr.3" : W = phi("L293" => #7, "L344" => #15, "L277" => #3, "L171" => #1, "L80" => #0)]:
    => ret %"pr.3"
} }.

Definition fn_glibc_libc_start'23handle_amd : func :=
  ir_fn{ "local" "glibc_libc_start#handle_amd"(W %"v0") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v3" : P = (Alloc 4) #4;
    %"v4" : P = (Alloc 4) #4;
    %"v5" : P = (Alloc 4) #4;
    %"v6" : P = (Alloc 4) #4;
    %"chk0" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk0" + 0] <- #0;
    %"chk1" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk1" + 0] <- #0;
    %"v12" : W = (Cmp Sgt W) %"v0", #196
    => br %"v12" ? "L8" : "L10" };
  ir_blk{ @"L8":
    => ret #0 };
  ir_blk{ @"L10":
    call void $"zcpuid"(W #2147483648, P %"v6", P %"v3", P %"v4", P %"v5");
    %"chk2" : A = (Renew 0 4 Read 1) %"chk1", %"v6";
    %"v17" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v18" : W = (Cmp Uge W) %"v17", #2147483677
    => br %"v18" ? "L14" : "L16" };
  ir_blk{ @"L14":
    %"v24" : W = (Cmp Sge W) %"v0", #194
    => br %"v24" ? "L22" : "L21" };
  ir_blk{ @"L21":
    %"v29" : W = (Cmp Sge W) %"v0", #191
    => br %"v29" ? "L22" : "L26" };
  ir_blk{ @"L26":
    %"v34" : W = (Cmp Sge W) %"v0", #188
    => br %"v34" ? "L22" : "L31" };
  ir_blk{ @"L31":
    => goto "L22" };
  ir_blk{ @"L22" [%"pr.2" : W = phi("L14" => #3, "L21" => #2, "L31" => #1, "L26" => #0)]:
    call void $"zcpuid_count"(W #2147483677, W %"pr.2", P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk3" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v39" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v40" : W = (Cmp Ne W) %"v39", #0
    => br %"v40" ? "L42" : "L16" };
  ir_blk{ @"L47":
    %"chk4" : A = (Check 0 4 Read 1) %"v3";
    %"v48" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v49" : W = Shr %"v48", #22;
    %"v50" : W = And %"v49", #1023;
    %"v51" : W = Add %"v50", #1;
    %"v52" : L = (Ext Uw) %"v51"
    => ret %"v52" };
  ir_blk{ @"L56":
    %"chk5" : A = (Check 0 4 Read 1) %"v3";
    %"v57" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v58" : W = And %"v57", #4095;
    %"v59" : W = Add %"v58", #1;
    %"v60" : L = (Ext Uw) %"v59"
    => ret %"v60" };
  ir_blk{ @"L64":
    %"chk6" : A = (Check 0 4 Read 1) %"v3";
    %"v65" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v66" : W = Shr %"v65", #22;
    %"v67" : W = And %"v66", #1023;
    %"v68" : W = Add %"v67", #1;
    %"v69" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v70" : W = And %"v69", #4095;
    %"v71" : W = Add %"v70", #1;
    %"v72" : W = Mul %"v68", %"v71";
    %"chk8" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v73" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v74" : W = Add %"v73", #1;
    %"v75" : W = Mul %"v72", %"v74";
    %"v76" : L = (Ext Uw) %"v75"
    => ret %"v76" };
  ir_blk{ @"L77":
    => unreachable };
  ir_blk{ @"L42":
    %"v79" : W = (Cmp Slt W) %"v0", #191
    => br %"v79" ? "L80" : "L81" };
  ir_blk{ @"L80":
    %"v82" : W = (Cmp Slt W) %"v0", #188
    => br %"v82" ? "L83" : "L84" };
  ir_blk{ @"L83":
    %"v85" : W = (Cmp Eq W) %"v0", #185
    => br %"v85" ? poll "L64" : "L86" };
  ir_blk{ @"L86":
    %"v87" : W = (Cmp Eq W) %"v0", #186
    => br %"v87" ? poll "L47" : "L88" };
  ir_blk{ @"L88":
    %"v89" : W = (Cmp Eq W) %"v0", #187
    => br %"v89" ? poll "L56" : poll "L77" };
  ir_blk{ @"L84":
    %"v91" : W = (Cmp Eq W) %"v0", #188
    => br %"v91" ? poll "L64" : "L92" };
  ir_blk{ @"L92":
    %"v93" : W = (Cmp Eq W) %"v0", #189
    => br %"v93" ? poll "L47" : "L94" };
  ir_blk{ @"L94":
    %"v95" : W = (Cmp Eq W) %"v0", #190
    => br %"v95" ? poll "L56" : poll "L77" };
  ir_blk{ @"L81":
    %"v97" : W = (Cmp Slt W) %"v0", #194
    => br %"v97" ? "L98" : "L99" };
  ir_blk{ @"L98":
    %"v100" : W = (Cmp Eq W) %"v0", #191
    => br %"v100" ? poll "L64" : "L101" };
  ir_blk{ @"L101":
    %"v102" : W = (Cmp Eq W) %"v0", #192
    => br %"v102" ? poll "L47" : "L103" };
  ir_blk{ @"L103":
    %"v104" : W = (Cmp Eq W) %"v0", #193
    => br %"v104" ? poll "L56" : poll "L77" };
  ir_blk{ @"L99":
    %"v106" : W = (Cmp Eq W) %"v0", #194
    => br %"v106" ? poll "L64" : "L107" };
  ir_blk{ @"L107":
    %"v108" : W = (Cmp Eq W) %"v0", #195
    => br %"v108" ? poll "L47" : "L109" };
  ir_blk{ @"L109":
    %"v110" : W = (Cmp Eq W) %"v0", #196
    => br %"v110" ? poll "L56" : poll "L77" };
  ir_blk{ @"L16":
    %"v116" : W = (Cmp Sge W) %"v0", #191;
    %"v117" : W = Add %"v116", #2147483653;
    %"chk9" : A = (Renew 0 4 Read 1) %"chk1", %"v6";
    %"v121" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"v123" : W = (Cmp Ult W) %"v121", %"v117"
    => br %"v123" ? "L118" : "L120" };
  ir_blk{ @"L118":
    => ret #0 };
  ir_blk{ @"L120":
    call void $"zcpuid"(W %"v117", P %"v2", P %"v3", P %"v4", P %"v5");
    %"v130" : W = (Cmp Slt W) %"v0", #188
    => br %"v130" ? "L126" : "L128" };
  ir_blk{ @"L126":
    %"v133" : W = Add %"v0", #3;
    %"chk10" : A = (Check 0 4 Read 1) %"v5";
    %"v134" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"chk11" : A = (Renew 0 4 Write 1) %"chk0", %"v4";
    store Ww [%"chk11" + 0] <- %"v134"
    => goto "L128" };
  ir_blk{ @"L128" [%"pr.1" : W = phi("L126" => %"v133", "L120" => %"v0")]:
    %"v397" : W = (Cmp Slt W) %"pr.1", #192
    => br %"v397" ? "L398" : "L399" };
  ir_blk{ @"L138":
    %"chk12" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"v140" : W = Shr %"v139", #14;
    %"v141" : W = And %"v140", #261120;
    %"v142" : L = (Ext Uw) %"v141"
    => ret %"v142" };
  ir_blk{ @"L143":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v144" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v145" : W = Shr %"v144", #16;
    %"chk14" : A = (Renew 0 4 Write 1) %"chk0", %"v4";
    store Ww [%"chk14" + 0] <- %"v145";
    %"v149" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"v150" : W = And %"v149", #255;
    %"v151" : W = (Cmp Eq W) %"v150", #255
    => br %"v151" ? "L146" : "L148" };
  ir_blk{ @"L146":
    %"v152" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"v153" : W = Shl %"v152", #2;
    %"v154" : W = And %"v153", #261120;
    %"v155" : L = (Ext Uw) %"v154"
    => ret %"v155" };
  ir_blk{ @"L148":
    %"v157" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"v158" : W = And %"v157", #255;
    %"v159" : L = (Ext Uw) %"v158"
    => ret %"v159" };
  ir_blk{ @"L160":
    %"chk18" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v161" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v162" : W = And %"v161", #255;
    %"v163" : L = (Ext Uw) %"v162"
    => ret %"v163" };
  ir_blk{ @"L164":
    %"chk19" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v168" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v169" : W = And %"v168", #61440;
    %"v170" : W = (Cmp Eq W) %"v169", #0
    => br %"v170" ? "L167" : "L166" };
  ir_blk{ @"L166":
    %"v171" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v172" : W = Shr %"v171", #6;
    %"v173" : W = And %"v172", #67107840
    => goto "L167" };
  ir_blk{ @"L167" [%"v174" : W = phi("L166" => %"v173", "L164" => #0)]:
    %"v175" : L = (Ext Uw) %"v174"
    => ret %"v175" };
  ir_blk{ @"L176":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v177" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v178" : W = Shr %"v177", #12;
    %"v179" : W = And %"v178", #15;
    %"v207" : W = (Cmp Ult W) %"v179", #10
    => br %"v207" ? "L208" : "L209" };
  ir_blk{ @"L185":
    %"chk22" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v186" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v187" : W = Shr %"v186", #12;
    %"v188" : W = And %"v187", #15;
    %"v189" : L = (Ext Uw) %"v188"
    => ret %"v189" };
  ir_blk{ @"L190":
    => ret #8 };
  ir_blk{ @"L191":
    => ret #16 };
  ir_blk{ @"L192":
    => ret #32 };
  ir_blk{ @"L193":
    => ret #48 };
  ir_blk{ @"L194":
    => ret #64 };
  ir_blk{ @"L195":
    => ret #96 };
  ir_blk{ @"L196":
    => ret #128 };
  ir_blk{ @"L197":
    %"chk23" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v198" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v199" : W = Shr %"v198", #6;
    %"v200" : W = And %"v199", #67107840;
    %"v201" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v202" : W = And %"v201", #255;
    %"v203" : W = Udiv %"v200", %"v202";
    %"v204" : L = (Ext Uw) %"v203"
    => ret %"v204" };
  ir_blk{ @"L205":
    => ret #0 };
  ir_blk{ @"L208":
    %"v210" : W = (Cmp Ult W) %"v179", #4
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v213" : W = (Cmp Eq W) %"v179", #0
    => br %"v213" ? poll "L185" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v179", #1
    => br %"v215" ? poll "L185" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v179", #2
    => br %"v217" ? poll "L185" : poll "L205" };
  ir_blk{ @"L212":
    %"v219" : W = (Cmp Eq W) %"v179", #4
    => br %"v219" ? poll "L185" : "L220" };
  ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v179", #6
    => br %"v221" ? poll "L190" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v179", #8
    => br %"v223" ? poll "L191" : poll "L205" };
  ir_blk{ @"L209":
    %"v225" : W = (Cmp Ult W) %"v179", #13
    => br %"v225" ? "L226" : "L227" }] [ir_blk{ @"L226":
    %"v228" : W = (Cmp Eq W) %"v179", #10
    => br %"v228" ? poll "L192" : "L229" };
  ir_blk{ @"L229":
    %"v230" : W = (Cmp Eq W) %"v179", #11
    => br %"v230" ? poll "L193" : "L231" };
  ir_blk{ @"L231":
    %"v232" : W = (Cmp Eq W) %"v179", #12
    => br %"v232" ? poll "L194" : poll "L205" };
  ir_blk{ @"L227":
    %"v234" : W = (Cmp Eq W) %"v179", #13
    => br %"v234" ? poll "L195" : "L235" };
  ir_blk{ @"L235":
    %"v236" : W = (Cmp Eq W) %"v179", #14
    => br %"v236" ? poll "L196" : "L237" };
  ir_blk{ @"L237":
    %"v238" : W = (Cmp Eq W) %"v179", #15
    => br %"v238" ? poll "L197" : poll "L205" };
  ir_blk{ @"L240":
    %"chk25" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v244" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v245" : W = And %"v244", #61440;
    %"v246" : W = (Cmp Eq W) %"v245", #0
    => br %"v246" ? "L243" : "L242" };
  ir_blk{ @"L242":
    %"v247" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v248" : W = And %"v247", #255
    => goto "L243" };
  ir_blk{ @"L243" [%"v249" : W = phi("L242" => %"v248", "L240" => #0)]:
    %"v250" : L = (Ext Uw) %"v249"
    => ret %"v250" };
  ir_blk{ @"L251":
    %"chk27" : A = (Check 0 4 Read 1) %"v5";
    %"v259" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v260" : W = And %"v259", #61440;
    %"v261" : W = (Cmp Eq W) %"v260", #0
    => br %"v261" ? "L256" : "L258" };
  ir_blk{ @"L256":
    => ret #0 };
  ir_blk{ @"L258":
    %"v263" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v264" : W = And %"v263", #1073479680;
    %"v265" : W = Shl %"v264", #1;
    %"v266" : L = (Ext Uw) %"v265";
    %"v267" : P = Copy $"_dl_x86_cpu_features";
    %"chk29" : A = (Renew 0 4 Read 1) %"chk1", %"v6";
    %"v271" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v272" : W = (Cmp Uge W) %"v271", #2147483656
    => br %"v272" ? "L268" : "L270" };
  ir_blk{ @"L268":
    call void $"zcpuid"(W #2147483656, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk30" : A = (Renew 0 4 Read 1) %"chk0", %"v4";
    %"v273" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v274" : W = And %"v273", #255;
    %"v275" : W = Add %"v274", #1
    => goto "L270" };
  ir_blk{ @"L270" [%"pr.6" : W = phi("L268" => %"v275", "L258" => #0)]:
    %"v280" : W = (Cmp Eq W) %"pr.6", #0
    => br %"v280" ? "L276" : "L278" };
  ir_blk{ @"L276":
    call void $"zcpuid"(W #1, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk31" : A = (Renew 0 4 Read 1) %"chk27", %"v5";
    %"v284" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v286" : W = And %"v284", #268435456;
    %"v287" : W = (Cmp Ne W) %"v286", #0
    => br %"v287" ? "L281" : "L278" };
  ir_blk{ @"L281":
    %"chk32" : A = (Check 0 4 Read 1) %"v3";
    %"v288" : W = (RawLoad (LdNarrow Uw) 0) %"chk32";
    %"v289" : W = Shr %"v288", #16;
    %"v290" : W = And %"v289", #255
    => goto "L278" };
  ir_blk{ @"L278" [%"pr.7" : W = phi("L281" => %"v290", "L276" => %"pr.6", "L270" => %"pr.6")]:
    %"v295" : W = (Cmp Ugt W) %"pr.7", #0
    => br %"v295" ? "L291" : "L293" };
  ir_blk{ @"L291":
    %"v298" : L = (Ext Uw) %"pr.7";
    %"v299" : L = Div %"v266", %"v298"
    => goto "L293" };
  ir_blk{ @"L293" [%"pr.5" : L = phi("L291" => %"v299", "L278" => #0)]:
    %"v304" = %"v267" +p #8;
    %"chk33" : A = (Check 0 4 Read 1) %"v304";
    %"v305" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v306" : W = (Cmp Uge W) %"v305", #23
    => br %"v306" ? "L300" : "L301" };
  ir_blk{ @"L300":
    call void $"zcpuid_count"(W #2147483677, W #3, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk34" : A = (Check 0 4 Read 1) %"v2";
    %"v309" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"v310" : W = Shr %"v309", #14;
    %"v311" : W = And %"v310", #4095;
    %"v312" : W = Add %"v311", #1;
    %"v315" : L = (Ext Uw) %"v312";
    %"v316" : L = Mul %"pr.5", %"v315"
    => ret %"v316" };
  ir_blk{ @"L301":
    => ret %"pr.5" };
  ir_blk{ @"L320":
    %"chk35" : A = (Check 0 4 Read 1) %"v5";
    %"v321" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v322" : W = Shr %"v321", #12;
    %"v323" : W = And %"v322", #15;
    %"v351" : W = (Cmp Ult W) %"v323", #10
    => br %"v351" ? "L352" : "L353" };
  ir_blk{ @"L329":
    %"chk36" : A = (Renew 0 4 Read 1) %"chk35", %"v5";
    %"v330" : W = (RawLoad (LdNarrow Uw) 0) %"chk36";
    %"v331" : W = Shr %"v330", #12;
    %"v332" : W = And %"v331", #15;
    %"v333" : L = (Ext Uw) %"v332"
    => ret %"v333" };
  ir_blk{ @"L334":
    => ret #8 };
  ir_blk{ @"L335":
    => ret #16 };
  ir_blk{ @"L336":
    => ret #32 };
  ir_blk{ @"L337":
    => ret #48 };
  ir_blk{ @"L338":
    => ret #64 };
  ir_blk{ @"L339":
    => ret #96 };
  ir_blk{ @"L340":
    => ret #128 };
  ir_blk{ @"L341":
    %"chk37" : A = (Renew 0 4 Read 1) %"chk35", %"v5";
    %"v342" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v343" : W = And %"v342", #1073479680;
    %"v344" : W = Shl %"v343", #1;
    %"v345" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v346" : W = And %"v345", #255;
    %"v347" : W = Udiv %"v344", %"v346";
    %"v348" : L = (Ext Uw) %"v347"
    => ret %"v348" };
  ir_blk{ @"L349":
    => ret #0 };
  ir_blk{ @"L352":
    %"v354" : W = (Cmp Ult W) %"v323", #4
    => br %"v354" ? "L355" : "L356" };
  ir_blk{ @"L355":
    %"v357" : W = (Cmp Eq W) %"v323", #0
    => br %"v357" ? poll "L329" : "L358" };
  ir_blk{ @"L358":
    %"v359" : W = (Cmp Eq W) %"v323", #1
    => br %"v359" ? poll "L329" : "L360" };
  ir_blk{ @"L360":
    %"v361" : W = (Cmp Eq W) %"v323", #2
    => br %"v361" ? poll "L329" : poll "L349" };
  ir_blk{ @"L356":
    %"v363" : W = (Cmp Eq W) %"v323", #4
    => br %"v363" ? poll "L329" : "L364" };
  ir_blk{ @"L364":
    %"v365" : W = (Cmp Eq W) %"v323", #6
    => br %"v365" ? poll "L334" : "L366" };
  ir_blk{ @"L366":
    %"v367" : W = (Cmp Eq W) %"v323", #8
    => br %"v367" ? poll "L335" : poll "L349" };
  ir_blk{ @"L353":
    %"v369" : W = (Cmp Ult W) %"v323", #13
    => br %"v369" ? "L370" : "L371" };
  ir_blk{ @"L370":
    %"v372" : W = (Cmp Eq W) %"v323", #10
    => br %"v372" ? poll "L336" : "L373" };
  ir_blk{ @"L373":
    %"v374" : W = (Cmp Eq W) %"v323", #11
    => br %"v374" ? poll "L337" : "L375" };
  ir_blk{ @"L375":
    %"v376" : W = (Cmp Eq W) %"v323", #12
    => br %"v376" ? poll "L338" : poll "L349" };
  ir_blk{ @"L371":
    %"v378" : W = (Cmp Eq W) %"v323", #13
    => br %"v378" ? poll "L339" : "L379" };
  ir_blk{ @"L379":
    %"v380" : W = (Cmp Eq W) %"v323", #14
    => br %"v380" ? poll "L340" : "L381" };
  ir_blk{ @"L381":
    %"v382" : W = (Cmp Eq W) %"v323", #15
    => br %"v382" ? poll "L341" : poll "L349" };
  ir_blk{ @"L384":
    %"chk39" : A = (Check 0 4 Read 1) %"v5";
    %"v388" : W = (RawLoad (LdNarrow Uw) 0) %"chk39";
    %"v389" : W = And %"v388", #61440;
    %"v390" : W = (Cmp Eq W) %"v389", #0
    => br %"v390" ? "L387" : "L386" };
  ir_blk{ @"L386":
    %"v391" : W = (RawLoad (LdNarrow Uw) 0) %"chk39";
    %"v392" : W = And %"v391", #255
    => goto "L387" };
  ir_blk{ @"L387" [%"v393" : W = phi("L386" => %"v392", "L384" => #0)]:
    %"v394" : L = (Ext Uw) %"v393"
    => ret %"v394" };
  ir_blk{ @"L395":
    => unreachable };
  ir_blk{ @"L398":
    %"v400" : W = (Cmp Eq W) %"pr.1", #188
    => br %"v400" ? poll "L138" : "L401" };
  ir_blk{ @"L401":
    %"v402" : W = (Cmp Eq W) %"pr.1", #189
    => br %"v402" ? poll "L143" : "L403" };
  ir_blk{ @"L403":
    %"v404" : W = (Cmp Eq W) %"pr.1", #190
    => br %"v404" ? poll "L160" : "L405" };
  ir_blk{ @"L405":
    %"v406" : W = (Cmp Eq W) %"pr.1", #191
    => br %"v406" ? poll "L164" : poll "L395" };
  ir_blk{ @"L399":
    %"v408" : W = (Cmp Slt W) %"pr.1", #194
    => br %"v408" ? "L409" : "L410" };
  ir_blk{ @"L409":
    %"v411" : W = (Cmp Eq W) %"pr.1", #192
    => br %"v411" ? poll "L176" : "L412" };
  ir_blk{ @"L412":
    %"v413" : W = (Cmp Eq W) %"pr.1", #193
    => br %"v413" ? poll "L240" : poll "L395" };
  ir_blk{ @"L410":
    %"v415" : W = (Cmp Eq W) %"pr.1", #194
    => br %"v415" ? poll "L251" : "L416" };
  ir_blk{ @"L416":
    %"v417" : W = (Cmp Eq W) %"pr.1", #195
    => br %"v417" ? poll "L320" : "L418" };
  ir_blk{ @"L418":
    %"v419" : W = (Cmp Eq W) %"pr.1", #196
    => br %"v419" ? poll "L384" : poll "L395" }])) }.

Definition fn_glibc_libc_start'23handle_hygon : func :=
  ir_fn{ "local" "glibc_libc_start#handle_hygon"(W %"v0") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v3" : P = (Alloc 4) #4;
    %"v4" : P = (Alloc 4) #4;
    %"v5" : P = (Alloc 4) #4;
    %"v6" : P = (Alloc 4) #4;
    %"chk0" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk0" + 0] <- #0;
    %"v11" : W = (Cmp Sgt W) %"v0", #196
    => br %"v11" ? "L7" : "L9" };
  ir_blk{ @"L7":
    => ret #0 };
  ir_blk{ @"L9":
    call void $"zcpuid"(W #2147483648, P %"v6", P %"v3", P %"v4", P %"v5");
    %"chk1" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v17" : W = (Cmp Uge W) %"v16", #2147483677
    => br %"v17" ? "L13" : "L15" };
  ir_blk{ @"L13":
    %"v23" : W = (Cmp Sge W) %"v0", #194
    => br %"v23" ? "L21" : "L20" };
  ir_blk{ @"L20":
    %"v28" : W = (Cmp Sge W) %"v0", #191
    => br %"v28" ? "L21" : "L25" };
  ir_blk{ @"L25":
    %"v33" : W = (Cmp Sge W) %"v0", #188
    => br %"v33" ? "L21" : "L30" };
  ir_blk{ @"L30":
    => goto "L21" };
  ir_blk{ @"L21" [%"pr.2" : W = phi("L13" => #3, "L20" => #2, "L30" => #1, "L25" => #0)]:
    call void $"zcpuid_count"(W #2147483677, W %"pr.2", P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk2" : A = (Check 0 4 Read 1) %"v4";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v39" : W = (Cmp Ne W) %"v38", #0
    => br %"v39" ? "L41" : "L15" };
  ir_blk{ @"L46":
    %"chk3" : A = (Check 0 4 Read 1) %"v3";
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v48" : W = Shr %"v47", #22;
    %"v49" : W = And %"v48", #1023;
    %"v50" : W = Add %"v49", #1;
    %"v51" : L = (Ext Uw) %"v50"
    => ret %"v51" };
  ir_blk{ @"L55":
    %"chk4" : A = (Check 0 4 Read 1) %"v3";
    %"v56" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v57" : W = And %"v56", #4095;
    %"v58" : W = Add %"v57", #1;
    %"v59" : L = (Ext Uw) %"v58"
    => ret %"v59" };
  ir_blk{ @"L63":
    %"chk5" : A = (Check 0 4 Read 1) %"v3";
    %"v64" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v65" : W = Shr %"v64", #22;
    %"v66" : W = And %"v65", #1023;
    %"v67" : W = Add %"v66", #1;
    %"v68" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v69" : W = And %"v68", #4095;
    %"v70" : W = Add %"v69", #1;
    %"v71" : W = Mul %"v67", %"v70";
    %"chk7" : A = (Renew 0 4 Read 1) %"chk2", %"v4";
    %"v72" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v73" : W = Add %"v72", #1;
    %"v74" : W = Mul %"v71", %"v73";
    %"v75" : L = (Ext Uw) %"v74"
    => ret %"v75" };
  ir_blk{ @"L76":
    => unreachable };
  ir_blk{ @"L41":
    %"v78" : W = (Cmp Slt W) %"v0", #191
    => br %"v78" ? "L79" : "L80" };
  ir_blk{ @"L79":
    %"v81" : W = (Cmp Slt W) %"v0", #188
    => br %"v81" ? "L82" : "L83" };
  ir_blk{ @"L82":
    %"v84" : W = (Cmp Eq W) %"v0", #185
    => br %"v84" ? poll "L63" : "L85" };
  ir_blk{ @"L85":
    %"v86" : W = (Cmp Eq W) %"v0", #186
    => br %"v86" ? poll "L46" : "L87" };
  ir_blk{ @"L87":
    %"v88" : W = (Cmp Eq W) %"v0", #187
    => br %"v88" ? poll "L55" : poll "L76" };
  ir_blk{ @"L83":
    %"v90" : W = (Cmp Eq W) %"v0", #188
    => br %"v90" ? poll "L63" : "L91" };
  ir_blk{ @"L91":
    %"v92" : W = (Cmp Eq W) %"v0", #189
    => br %"v92" ? poll "L46" : "L93" };
  ir_blk{ @"L93":
    %"v94" : W = (Cmp Eq W) %"v0", #190
    => br %"v94" ? poll "L55" : poll "L76" };
  ir_blk{ @"L80":
    %"v96" : W = (Cmp Slt W) %"v0", #194
    => br %"v96" ? "L97" : "L98" };
  ir_blk{ @"L97":
    %"v99" : W = (Cmp Eq W) %"v0", #191
    => br %"v99" ? poll "L63" : "L100" };
  ir_blk{ @"L100":
    %"v101" : W = (Cmp Eq W) %"v0", #192
    => br %"v101" ? poll "L46" : "L102" };
  ir_blk{ @"L102":
    %"v103" : W = (Cmp Eq W) %"v0", #193
    => br %"v103" ? poll "L55" : poll "L76" };
  ir_blk{ @"L98":
    %"v105" : W = (Cmp Eq W) %"v0", #194
    => br %"v105" ? poll "L63" : "L106" };
  ir_blk{ @"L106":
    %"v107" : W = (Cmp Eq W) %"v0", #195
    => br %"v107" ? poll "L46" : "L108" };
  ir_blk{ @"L108":
    %"v109" : W = (Cmp Eq W) %"v0", #196
    => br %"v109" ? poll "L55" : poll "L76" };
  ir_blk{ @"L15":
    %"v116" : W = (Cmp Sge W) %"v0", #191;
    %"v117" : W = Add %"v116", #2147483653;
    %"chk8" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"v121" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v123" : W = (Cmp Ult W) %"v121", %"v117"
    => br %"v123" ? "L118" : "L120" };
  ir_blk{ @"L118":
    => ret #0 };
  ir_blk{ @"L120":
    call void $"zcpuid"(W %"v117", P %"v2", P %"v3", P %"v4", P %"v5");
    %"v130" : W = (Cmp Slt W) %"v0", #188
    => br %"v130" ? "L126" : "L128" };
  ir_blk{ @"L126":
    %"v133" : W = Add %"v0", #3;
    %"chk9" : A = (Check 0 4 Read 1) %"v5";
    %"v134" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"chk10" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk10" + 0] <- %"v134"
    => goto "L128" };
  ir_blk{ @"L128" [%"pr.1" : W = phi("L126" => %"v133", "L120" => %"v0")]:
    %"v386" : W = (Cmp Slt W) %"pr.1", #192
    => br %"v386" ? "L387" : "L388" };
  ir_blk{ @"L138":
    %"chk11" : A = (Check 0 4 Read 1) %"v4";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v140" : W = Shr %"v139", #14;
    %"v141" : W = And %"v140", #261120;
    %"v142" : L = (Ext Uw) %"v141"
    => ret %"v142" };
  ir_blk{ @"L143":
    %"chk12" : A = (Check 0 4 Read 1) %"v4";
    %"v144" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"v145" : W = Shr %"v144", #16;
    %"chk13" : A = (Renew 0 4 Write 1) %"chk12", %"v4";
    store Ww [%"chk13" + 0] <- %"v145";
    %"v149" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v150" : W = And %"v149", #255;
    %"v151" : W = (Cmp Eq W) %"v150", #255
    => br %"v151" ? "L146" : "L148" };
  ir_blk{ @"L146":
    %"v152" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v153" : W = Shl %"v152", #2;
    %"v154" : W = And %"v153", #261120;
    %"v155" : L = (Ext Uw) %"v154"
    => ret %"v155" };
  ir_blk{ @"L148":
    %"v157" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"v158" : W = And %"v157", #255;
    %"v159" : L = (Ext Uw) %"v158"
    => ret %"v159" };
  ir_blk{ @"L160":
    %"chk17" : A = (Check 0 4 Read 1) %"v4";
    %"v161" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v162" : W = And %"v161", #255;
    %"v163" : L = (Ext Uw) %"v162"
    => ret %"v163" };
  ir_blk{ @"L164":
    %"chk18" : A = (Check 0 4 Read 1) %"v4";
    %"v168" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v169" : W = And %"v168", #61440;
    %"v170" : W = (Cmp Eq W) %"v169", #0
    => br %"v170" ? "L167" : "L166" };
  ir_blk{ @"L166":
    %"v171" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v172" : W = Shr %"v171", #6;
    %"v173" : W = And %"v172", #67107840
    => goto "L167" };
  ir_blk{ @"L167" [%"v174" : W = phi("L166" => %"v173", "L164" => #0)]:
    %"v175" : L = (Ext Uw) %"v174"
    => ret %"v175" };
  ir_blk{ @"L176":
    %"chk20" : A = (Check 0 4 Read 1) %"v4";
    %"v177" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v178" : W = Shr %"v177", #12;
    %"v179" : W = And %"v178", #15;
    %"v207" : W = (Cmp Ult W) %"v179", #10
    => br %"v207" ? "L208" : "L209" };
  ir_blk{ @"L185":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk20", %"v4";
    %"v186" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v187" : W = Shr %"v186", #12;
    %"v188" : W = And %"v187", #15;
    %"v189" : L = (Ext Uw) %"v188"
    => ret %"v189" };
  ir_blk{ @"L190":
    => ret #8 };
  ir_blk{ @"L191":
    => ret #16 };
  ir_blk{ @"L192":
    => ret #32 };
  ir_blk{ @"L193":
    => ret #48 };
  ir_blk{ @"L194":
    => ret #64 };
  ir_blk{ @"L195":
    => ret #96 };
  ir_blk{ @"L196":
    => ret #128 };
  ir_blk{ @"L197":
    %"chk22" : A = (Renew 0 4 Read 1) %"chk20", %"v4";
    %"v198" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v199" : W = Shr %"v198", #6;
    %"v200" : W = And %"v199", #67107840;
    %"v201" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v202" : W = And %"v201", #255;
    %"v203" : W = Udiv %"v200", %"v202";
    %"v204" : L = (Ext Uw) %"v203"
    => ret %"v204" };
  ir_blk{ @"L205":
    => ret #0 };
  ir_blk{ @"L208":
    %"v210" : W = (Cmp Ult W) %"v179", #4
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v213" : W = (Cmp Eq W) %"v179", #0
    => br %"v213" ? poll "L185" : "L214" };
  ir_blk{ @"L214":
    %"v215" : W = (Cmp Eq W) %"v179", #1
    => br %"v215" ? poll "L185" : "L216" };
  ir_blk{ @"L216":
    %"v217" : W = (Cmp Eq W) %"v179", #2
    => br %"v217" ? poll "L185" : poll "L205" };
  ir_blk{ @"L212":
    %"v219" : W = (Cmp Eq W) %"v179", #4
    => br %"v219" ? poll "L185" : "L220" };
  ir_blk{ @"L220":
    %"v221" : W = (Cmp Eq W) %"v179", #6
    => br %"v221" ? poll "L190" : "L222" };
  ir_blk{ @"L222":
    %"v223" : W = (Cmp Eq W) %"v179", #8
    => br %"v223" ? poll "L191" : poll "L205" }] [ir_blk{ @"L209":
    %"v225" : W = (Cmp Ult W) %"v179", #13
    => br %"v225" ? "L226" : "L227" };
  ir_blk{ @"L226":
    %"v228" : W = (Cmp Eq W) %"v179", #10
    => br %"v228" ? poll "L192" : "L229" };
  ir_blk{ @"L229":
    %"v230" : W = (Cmp Eq W) %"v179", #11
    => br %"v230" ? poll "L193" : "L231" };
  ir_blk{ @"L231":
    %"v232" : W = (Cmp Eq W) %"v179", #12
    => br %"v232" ? poll "L194" : poll "L205" };
  ir_blk{ @"L227":
    %"v234" : W = (Cmp Eq W) %"v179", #13
    => br %"v234" ? poll "L195" : "L235" };
  ir_blk{ @"L235":
    %"v236" : W = (Cmp Eq W) %"v179", #14
    => br %"v236" ? poll "L196" : "L237" };
  ir_blk{ @"L237":
    %"v238" : W = (Cmp Eq W) %"v179", #15
    => br %"v238" ? poll "L197" : poll "L205" };
  ir_blk{ @"L240":
    %"chk24" : A = (Check 0 4 Read 1) %"v4";
    %"v244" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"v245" : W = And %"v244", #61440;
    %"v246" : W = (Cmp Eq W) %"v245", #0
    => br %"v246" ? "L243" : "L242" };
  ir_blk{ @"L242":
    %"v247" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"v248" : W = And %"v247", #255
    => goto "L243" };
  ir_blk{ @"L243" [%"v249" : W = phi("L242" => %"v248", "L240" => #0)]:
    %"v250" : L = (Ext Uw) %"v249"
    => ret %"v250" };
  ir_blk{ @"L251":
    %"chk26" : A = (Check 0 4 Read 1) %"v5";
    %"v258" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v259" : W = And %"v258", #61440;
    %"v260" : W = (Cmp Eq W) %"v259", #0
    => br %"v260" ? "L255" : "L257" };
  ir_blk{ @"L255":
    => ret #0 };
  ir_blk{ @"L257":
    %"v262" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v263" : W = And %"v262", #1073479680;
    %"v264" : W = Shl %"v263", #1;
    %"v265" : L = (Ext Uw) %"v264";
    %"chk28" : A = (Renew 0 4 Read 1) %"chk0", %"v6";
    %"v269" : W = (RawLoad (LdNarrow Uw) 0) %"chk28";
    %"v270" : W = (Cmp Uge W) %"v269", #2147483656
    => br %"v270" ? "L266" : "L268" };
  ir_blk{ @"L266":
    call void $"zcpuid"(W #2147483656, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk29" : A = (Check 0 4 Read 1) %"v4";
    %"v271" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v272" : W = And %"v271", #255;
    %"v273" : W = Add %"v272", #1
    => goto "L268" };
  ir_blk{ @"L268" [%"pr.6" : W = phi("L266" => %"v273", "L257" => #0)]:
    %"v278" : W = (Cmp Eq W) %"pr.6", #0
    => br %"v278" ? "L274" : "L276" };
  ir_blk{ @"L274":
    call void $"zcpuid"(W #1, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk30" : A = (Renew 0 4 Read 1) %"chk26", %"v5";
    %"v282" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v284" : W = And %"v282", #268435456;
    %"v285" : W = (Cmp Ne W) %"v284", #0
    => br %"v285" ? "L279" : "L276" };
  ir_blk{ @"L279":
    %"chk31" : A = (Check 0 4 Read 1) %"v3";
    %"v286" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v287" : W = Shr %"v286", #16;
    %"v288" : W = And %"v287", #255
    => goto "L276" };
  ir_blk{ @"L276" [%"pr.7" : W = phi("L279" => %"v288", "L274" => %"pr.6", "L268" => %"pr.6")]:
    %"v293" : W = (Cmp Ugt W) %"pr.7", #0
    => br %"v293" ? "L289" : "L291" };
  ir_blk{ @"L289":
    %"v296" : L = (Ext Uw) %"pr.7";
    %"v297" : L = Div %"v265", %"v296"
    => goto "L291" };
  ir_blk{ @"L291" [%"pr.5" : L = phi("L289" => %"v297", "L276" => #0)]:
    call void $"zcpuid_count"(W #2147483677, W #3, P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk32" : A = (Check 0 4 Read 1) %"v2";
    %"v299" : W = (RawLoad (LdNarrow Uw) 0) %"chk32";
    %"v300" : W = Shr %"v299", #14;
    %"v301" : W = And %"v300", #4095;
    %"v302" : W = Add %"v301", #1;
    %"v306" : L = (Ext Uw) %"v302";
    %"v307" : L = Mul %"pr.5", %"v306"
    => ret %"v307" };
  ir_blk{ @"L309":
    %"chk33" : A = (Check 0 4 Read 1) %"v5";
    %"v310" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v311" : W = Shr %"v310", #12;
    %"v312" : W = And %"v311", #15;
    %"v340" : W = (Cmp Ult W) %"v312", #10
    => br %"v340" ? "L341" : "L342" };
  ir_blk{ @"L318":
    %"chk34" : A = (Renew 0 4 Read 1) %"chk33", %"v5";
    %"v319" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"v320" : W = Shr %"v319", #12;
    %"v321" : W = And %"v320", #15;
    %"v322" : L = (Ext Uw) %"v321"
    => ret %"v322" };
  ir_blk{ @"L323":
    => ret #8 };
  ir_blk{ @"L324":
    => ret #16 };
  ir_blk{ @"L325":
    => ret #32 };
  ir_blk{ @"L326":
    => ret #48 };
  ir_blk{ @"L327":
    => ret #64 };
  ir_blk{ @"L328":
    => ret #96 };
  ir_blk{ @"L329":
    => ret #128 };
  ir_blk{ @"L330":
    %"chk35" : A = (Renew 0 4 Read 1) %"chk33", %"v5";
    %"v331" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v332" : W = And %"v331", #1073479680;
    %"v333" : W = Shl %"v332", #1;
    %"v334" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v335" : W = And %"v334", #255;
    %"v336" : W = Udiv %"v333", %"v335";
    %"v337" : L = (Ext Uw) %"v336"
    => ret %"v337" };
  ir_blk{ @"L338":
    => ret #0 };
  ir_blk{ @"L341":
    %"v343" : W = (Cmp Ult W) %"v312", #4
    => br %"v343" ? "L344" : "L345" };
  ir_blk{ @"L344":
    %"v346" : W = (Cmp Eq W) %"v312", #0
    => br %"v346" ? poll "L318" : "L347" };
  ir_blk{ @"L347":
    %"v348" : W = (Cmp Eq W) %"v312", #1
    => br %"v348" ? poll "L318" : "L349" };
  ir_blk{ @"L349":
    %"v350" : W = (Cmp Eq W) %"v312", #2
    => br %"v350" ? poll "L318" : poll "L338" };
  ir_blk{ @"L345":
    %"v352" : W = (Cmp Eq W) %"v312", #4
    => br %"v352" ? poll "L318" : "L353" };
  ir_blk{ @"L353":
    %"v354" : W = (Cmp Eq W) %"v312", #6
    => br %"v354" ? poll "L323" : "L355" };
  ir_blk{ @"L355":
    %"v356" : W = (Cmp Eq W) %"v312", #8
    => br %"v356" ? poll "L324" : poll "L338" };
  ir_blk{ @"L342":
    %"v358" : W = (Cmp Ult W) %"v312", #13
    => br %"v358" ? "L359" : "L360" };
  ir_blk{ @"L359":
    %"v361" : W = (Cmp Eq W) %"v312", #10
    => br %"v361" ? poll "L325" : "L362" };
  ir_blk{ @"L362":
    %"v363" : W = (Cmp Eq W) %"v312", #11
    => br %"v363" ? poll "L326" : "L364" };
  ir_blk{ @"L364":
    %"v365" : W = (Cmp Eq W) %"v312", #12
    => br %"v365" ? poll "L327" : poll "L338" };
  ir_blk{ @"L360":
    %"v367" : W = (Cmp Eq W) %"v312", #13
    => br %"v367" ? poll "L328" : "L368" };
  ir_blk{ @"L368":
    %"v369" : W = (Cmp Eq W) %"v312", #14
    => br %"v369" ? poll "L329" : "L370" };
  ir_blk{ @"L370":
    %"v371" : W = (Cmp Eq W) %"v312", #15
    => br %"v371" ? poll "L330" : poll "L338" };
  ir_blk{ @"L373":
    %"chk37" : A = (Check 0 4 Read 1) %"v5";
    %"v377" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v378" : W = And %"v377", #61440;
    %"v379" : W = (Cmp Eq W) %"v378", #0
    => br %"v379" ? "L376" : "L375" };
  ir_blk{ @"L375":
    %"v380" : W = (RawLoad (LdNarrow Uw) 0) %"chk37";
    %"v381" : W = And %"v380", #255
    => goto "L376" };
  ir_blk{ @"L376" [%"v382" : W = phi("L375" => %"v381", "L373" => #0)]:
    %"v383" : L = (Ext Uw) %"v382"
    => ret %"v383" };
  ir_blk{ @"L384":
    => unreachable };
  ir_blk{ @"L387":
    %"v389" : W = (Cmp Eq W) %"pr.1", #188
    => br %"v389" ? poll "L138" : "L390" };
  ir_blk{ @"L390":
    %"v391" : W = (Cmp Eq W) %"pr.1", #189
    => br %"v391" ? poll "L143" : "L392" };
  ir_blk{ @"L392":
    %"v393" : W = (Cmp Eq W) %"pr.1", #190
    => br %"v393" ? poll "L160" : "L394" };
  ir_blk{ @"L394":
    %"v395" : W = (Cmp Eq W) %"pr.1", #191
    => br %"v395" ? poll "L164" : poll "L384" };
  ir_blk{ @"L388":
    %"v397" : W = (Cmp Slt W) %"pr.1", #194
    => br %"v397" ? "L398" : "L399" };
  ir_blk{ @"L398":
    %"v400" : W = (Cmp Eq W) %"pr.1", #192
    => br %"v400" ? poll "L176" : "L401" };
  ir_blk{ @"L401":
    %"v402" : W = (Cmp Eq W) %"pr.1", #193
    => br %"v402" ? poll "L240" : poll "L384" };
  ir_blk{ @"L399":
    %"v404" : W = (Cmp Eq W) %"pr.1", #194
    => br %"v404" ? poll "L251" : "L405" };
  ir_blk{ @"L405":
    %"v406" : W = (Cmp Eq W) %"pr.1", #195
    => br %"v406" ? poll "L309" : "L407" };
  ir_blk{ @"L407":
    %"v408" : W = (Cmp Eq W) %"pr.1", #196
    => br %"v408" ? poll "L373" : poll "L384" }])) }.

Definition fn_glibc_libc_start'23handle_intel : func :=
  ir_fn{ "local" "glibc_libc_start#handle_intel"(W %"v0", P %"v2", P %"v4") -> (RClass L) {
  @"start":
    %"v19" : P = (Alloc 4) #1;
    %"v21" : P = (Alloc 4) #1;
    %"v8" = %"v2" +p #4;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v14" : W = (Cmp Ult W) %"v9", #2
    => br %"v14" ? "L10" : "L12";
  @"L10":
    => ret #18446744073709551615;
  @"L12":
    %"chk1" : A = (Check 0 1 Write 1) %"v19";
    store Wb [%"chk1" + 0] <- #0;
    %"chk2" : A = (Check 0 1 Write 1) %"v21";
    store Wb [%"chk2" + 0] <- #0;
    %"chk3" : A = (Check 0 1 Read 1) %"v4";
    %"v28" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"v29" : W = (Cmp Eq W) %"v28", #0
    => br %"v29" ? "L24" : "L26";
  @"L24":
    %"v31" = %"v4" +p #4;
    %"v35" = %"v31" +p #4;
    %"v38" = %"v31" +p #8;
    %"v41" = %"v31" +p #12;
    call void $"zcpuid"(W #2, P %"v31", P %"v35", P %"v38", P %"v41");
    %"chk4" : A = (Renew 0 1 Write 1) %"chk3", %"v4";
    store Wb [%"chk4" + 0] <- #1
    => goto "L26";
  @"L26":
    %"v47" = %"v4" +p #4;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk3", %"v47";
    %"v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v50" : W = And %"v49", #255;
    %"v51" : W = (Cmp Ne W) %"v50", #1
    => br %"v51" ? "L43" : "L45";
  @"L43":
    call %"v55" : L = $"glibc_libc_start#intel_check_word"(W %"v0", W #255, P %"v21", P %"v19", P %"v2", P %"v4")
    => ret %"v55";
  @"L45":
    %"v59" = %"v4" +p #4;
    %"v61" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v62" : W = And %"v61", #4294967040;
    call %"v65" : L = $"glibc_libc_start#intel_check_word"(W %"v0", W %"v62", P %"v21", P %"v19", P %"v2", P %"v4");
    %"v70" : W = (Cmp Ne L) %"v65", #0
    => br %"v70" ? "L66" : "L73";
  @"L66":
    => ret %"v65";
  @"L73" [%"pr.1" : W = phi("L75" => %"v98", "L45" => #1)]:
    %"v78" : W = (Cmp Slt W) %"pr.1", #4
    => br %"v78" ? "L74" : "L76";
  @"L74":
    %"v81" = %"v4" +p #4;
    %"v83" : L = (Ext Sw) %"pr.1";
    %"v84" : L = Shl %"v83", #2;
    %"v85" = %"v81" +p %"v84";
    %"chk7" : A = (Check 0 4 Read 1) %"v85";
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    call %"v89" : L = $"glibc_libc_start#intel_check_word"(W %"v0", W %"v86", P %"v21", P %"v19", P %"v2", P %"v4");
    %"v94" : W = (Cmp Ne L) %"v89", #0
    => br %"v94" ? "L90" : "L75";
  @"L90":
    => ret %"v89";
  @"L75":
    %"v98" : W = Add %"pr.1", #1
    => goto poll "L73";
  @"L76":
    %"v103" : W = (Cmp Sge W) %"v0", #191
    => br %"v103" ? "L104" : "L105";
  @"L104":
    %"v107" : W = (Cmp Sle W) %"v0", #196
    => goto "L105";
  @"L105" [%"v109" : W = phi("L76" => #0, "L104" => %"v107")]:
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"chk8" : A = (Renew 0 1 Read 1) %"chk1", %"v19";
    %"v112" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v113" : W = (Cmp Ne W) %"v112", #0
    => goto "L111";
  @"L111" [%"v114" : W = phi("L105" => #0, "L110" => %"v113")]:
    => br %"v114" ? "L99" : "L101";
  @"L99":
    => ret #18446744073709551615;
  @"L101":
    => ret #0
} }.

Definition fn_glibc_libc_start'23handle_zhaoxin : func :=
  ir_fn{ "local" "glibc_libc_start#handle_zhaoxin"(W %"v0") -> (RClass L) {
  @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v3" : P = (Alloc 4) #4;
    %"v4" : P = (Alloc 4) #4;
    %"v5" : P = (Alloc 4) #4;
    %"v8" : W = Sub %"v0", #185;
    %"v9" : W = Div %"v8", #3;
    %"v10" : W = Mul %"v9", #3
    => goto "L12";
  @"L12" [%"pr.1" : W = phi("L31" => %"v143", "start" => #0)]:
    call void $"zcpuid_count"(W #4, W %"pr.1", P %"v2", P %"v3", P %"v4", P %"v5");
    %"chk0" : A = (Check 0 4 Read 1) %"v2";
    %"v17" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v18" : W = And %"v17", #31;
    %"v23" : W = (Cmp Eq W) %"v18", #0
    => br %"v23" ? "L14" : "L21";
  @"L21":
    %"v26" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v27" : W = Shr %"v26", #5;
    %"v28" : W = And %"v27", #7;
    %"v33" : W = (Cmp Eq W) %"v28", #1
    => br %"v33" ? "L34" : "L35";
  @"L34":
    %"v37" : W = (Cmp Eq W) %"v18", #1
    => goto "L35";
  @"L35" [%"v39" : W = phi("L21" => #0, "L34" => %"v37")]:
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v44" : W = (Cmp Eq W) %"v10", #3
    => goto "L41";
  @"L41" [%"v46" : W = phi("L35" => #0, "L40" => %"v44")]:
    => br %"v46" ? "L48" : "L47";
  @"L47":
    => br %"v33" ? "L51" : "L52";
  @"L51":
    %"v54" : W = (Cmp Eq W) %"v18", #2
    => goto "L52";
  @"L52" [%"v56" : W = phi("L47" => #0, "L51" => %"v54")]:
    => br %"v56" ? "L57" : "L48";
  @"L57":
    %"v61" : W = (Cmp Eq W) %"v10", #0
    => goto "L48";
  @"L48" [%"v65" : W = phi("L41" => #1, "L52" => #0, "L57" => %"v61")]:
    => br %"v65" ? "L67" : "L66";
  @"L66":
    %"v69" : W = (Cmp Eq W) %"v28", #2
    => br %"v69" ? "L70" : "L67";
  @"L70":
    %"v74" : W = (Cmp Eq W) %"v10", #6
    => goto "L67";
  @"L67" [%"v78" : W = phi("L48" => #1, "L66" => #0, "L70" => %"v74")]:
    => br %"v78" ? "L80" : "L79";
  @"L79":
    %"v82" : W = (Cmp Eq W) %"v28", #3
    => br %"v82" ? "L83" : "L80";
  @"L83":
    %"v87" : W = (Cmp Eq W) %"v10", #9
    => goto "L80";
  @"L80" [%"v91" : W = phi("L67" => #1, "L79" => #0, "L83" => %"v87")]:
    => br %"v91" ? "L29" : "L31";
  @"L29":
    %"v96" : W = Sub %"v8", %"v10";
    %"v101" : W = (Cmp Eq W) %"v96", #0
    => br %"v101" ? "L97" : "L99";
  @"L97":
    %"chk2" : A = (Check 0 4 Read 1) %"v3";
    %"v102" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v103" : W = Shr %"v102", #22;
    %"v104" : W = Add %"v103", #1;
    %"v105" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v106" : W = Shr %"v105", #12;
    %"v107" : W = And %"v106", #1023;
    %"v108" : W = Add %"v107", #1;
    %"v109" : W = Mul %"v104", %"v108";
    %"v110" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v111" : W = And %"v110", #4095;
    %"v112" : W = Add %"v111", #1;
    %"v113" : W = Mul %"v109", %"v112";
    %"chk5" : A = (Check 0 4 Read 1) %"v4";
    %"v114" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v115" : W = Add %"v114", #1;
    %"v116" : W = Mul %"v113", %"v115";
    %"v117" : L = (Ext Uw) %"v116"
    => ret %"v117";
  @"L99":
    %"v123" : W = (Cmp Eq W) %"v96", #1
    => br %"v123" ? "L119" : "L121";
  @"L119":
    %"chk6" : A = (Check 0 4 Read 1) %"v3";
    %"v124" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v125" : W = Shr %"v124", #22;
    %"v126" : W = Add %"v125", #1;
    %"v127" : L = (Ext Uw) %"v126"
    => ret %"v127";
  @"L121":
    %"v133" : W = (Cmp Eq W) %"v96", #2
    => br %"v133" ? "L131" : "L130";
  @"L130":
    %"v134" : P = Copy $"glibc_libc_start#str.301";
    %"v135" : P = Copy $"glibc_libc_start#str.302";
    %"v136" : P = Copy $"glibc_libc_start#str.304";
    call void $"__libc_assert_fail"(P %"v134", P %"v135", W #587, P %"v136")
    => goto "L131";
  @"L131":
    %"chk7" : A = (Check 0 4 Read 1) %"v3";
    %"v137" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v138" : W = And %"v137", #4095;
    %"v139" : W = Add %"v138", #1;
    %"v140" : L = (Ext Uw) %"v139"
    => ret %"v140";
  @"L31":
    %"v143" : W = Add %"pr.1", #1
    => goto poll "L12";
  @"L14":
    => ret #0
} }.

Definition fn_glibc_libc_start'23init_cpu_features : func :=
  ir_fn{ "local" "glibc_libc_start#init_cpu_features"(P %"v0") -> RVoid blocks (fn_glibc_libc_start'23init_cpu_features'blocks1 ++ fn_glibc_libc_start'23init_cpu_features'blocks2) }.

Definition item_glibc_libc_start'23intel_02_known : item :=
  (IData (a "glibc_libc_start#intel_02_known") (LRo (a "local")) 4 (app (app (app [(Item Wb 6); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 8192); (Item Wb 8); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 16384); (Item Wb 9); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 32768); (Item Wb 10); (Item Wb 2); (Item Wb 32); (Item Wb 3); (Item Ww 8192); (Item Wb 12); (Item Wb 4); (Item Wb 32); (Item Wb 3); (Item Ww 16384); (Item Wb 13); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 14); (Item Wb 6); (Item Wb 64); (Item Wb 3); (Item Ww 24576); (Item Wb 33); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 34); (Item Wb 4)] [(Item Wb 64); (Item Wb 9); (Item Ww 524288); (Item Wb 35); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 37); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 41); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 44); (Item Wb 8); (Item Wb 64); (Item Wb 3); (Item Ww 32768); (Item Wb 48); (Item Wb 8); (Item Wb 64); (Item Wb 0); (Item Ww 32768); (Item Wb 57); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 131072); (Item Wb 58); (Item Wb 6); (Item Wb 64); (Item Wb 6); (Item Ww 196608); (Item Wb 59); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 131072)]) (app [(Item Wb 60); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 61); (Item Wb 6); (Item Wb 64); (Item Wb 6); (Item Ww 393216); (Item Wb 62); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 63); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 65); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 131072); (Item Wb 66); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 262144); (Item Wb 67); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 524288); (Item Wb 68); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 1048576); (Item Wb 69); (Item Wb 4)] [(Item Wb 32); (Item Wb 6); (Item Ww 2097152); (Item Wb 70); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 71); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 72); (Item Wb 12); (Item Wb 64); (Item Wb 6); (Item Ww 3145728); (Item Wb 73); (Item Wb 16); (Item Wb 64); (Item Wb 6); (Item Ww 4194304); (Item Wb 74); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 6291456); (Item Wb 75); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 76); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 12582912); (Item Wb 77); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 16777216)])) (app (app [(Item Wb 78); (Item Wb 24); (Item Wb 64); (Item Wb 6); (Item Ww 6291456); (Item Wb 96); (Item Wb 8); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 102); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 8192); (Item Wb 103); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 104); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 32768); (Item Wb 120); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 121); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 131072); (Item Wb 122); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 123); (Item Wb 8)] [(Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 124); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 125); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 2097152); (Item Wb 127); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 128); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 130); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 262144); (Item Wb 131); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 524288); (Item Wb 132); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 1048576); (Item Wb 133); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 2097152)]) (app [(Item Wb 134); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 135); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 208); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 524288); (Item Wb 209); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 210); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 214); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 215); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 216); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 220); (Item Wb 12)] [(Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 221); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 222); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 226); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 227); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 228); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 234); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 12582912); (Item Wb 235); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 18874368); (Item Wb 236); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 25165824)])))).

Definition fn_glibc_libc_start'23intel_02_known_compare : func :=
  ir_fn{ "local" "glibc_libc_start#intel_02_known_compare"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 1 Read 1) %"v0";
    %"v12" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"chk1" : A = (Check 0 1 Read 1) %"v2";
    %"v14" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v15" : W = (Cmp Eq W) %"v12", %"v14"
    => br %"v15" ? "L8" : "L10";
  @"L8":
    => ret #0;
  @"L10":
    %"v21" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"v23" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v24" : W = (Cmp Slt W) %"v21", %"v23"
    => br %"v24" ? "L19" : "L18";
  @"L18":
    => goto "L19";
  @"L19" [%"v26" : W = phi("L18" => #1, "L10" => #4294967295)]:
    => ret %"v26"
} }.

Definition fn_glibc_libc_start'23intel_check_word : func :=
  ir_fn{ "local" "glibc_libc_start#intel_check_word"(W %"v0", W %"v2", P %"v4", P %"v6", P %"v8", P %"v10") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v51" : P = (Alloc 4) #4;
    %"v52" : P = (Alloc 4) #4;
    %"v53" : P = (Alloc 4) #4;
    %"v54" : P = (Alloc 4) #4;
    %"v334" : P = (Alloc 4) #8;
    %"v16" : W = And %"v2", #2147483648;
    %"v17" : W = (Cmp Ne W) %"v16", #0
    => br %"v17" ? "L12" : "L14" };
  ir_blk{ @"L12":
    => ret #0 };
  ir_blk{ @"L14":
    %"v21" : W = Sub %"v0", #185;
    %"v22" : W = Div %"v21", #3;
    %"v23" : W = Mul %"v22", #3
    => goto "L24" };
  ir_blk{ @"L24" [%"pr.6" : W = phi("L14" => %"v23", "L34" => %"pr.9"); %"pr.5" : W = phi("L14" => %"v2", "L34" => %"v405"); %"pr.1" : W = phi("L14" => %"v0", "L34" => %"pr.4")]:
    %"v28" : W = (Cmp Ne W) %"pr.5", #0
    => br %"v28" ? "L25" : "L26" };
  ir_blk{ @"L25":
    %"v31" : W = And %"pr.5", #255;
    %"v36" : W = (Cmp Eq W) %"v31", #64
    => br %"v36" ? "L32" : "L33" };
  ir_blk{ @"L32":
    %"chk0" : A = (Check 0 1 Write 1) %"v6";
    store Wb [%"chk0" + 0] <- #1;
    %"v44" : W = (Cmp Eq W) %"pr.6", #9
    => br %"v44" ? "L26" : "L34" };
  ir_blk{ @"L33":
    %"v50" : W = (Cmp Eq W) %"v31", #255
    => br %"v50" ? "L56" : "L47" };
  ir_blk{ @"L56" [%"pr.10" : W = phi("L169" => %"v294", "L33" => #0)]:
    %"v64" = %"v10" +p #1;
    %"chk1" : A = (Check 0 1 Read 1) %"v64";
    %"v65" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v66" : W = (Cmp Ult W) %"pr.10", %"v65"
    => br %"v66" ? "L59" : "L60" };
  ir_blk{ @"L59":
    %"v68" = %"v10" +p #20;
    %"v70" : L = (Ext Uw) %"pr.10";
    %"v71" : L = Shl %"v70", #4;
    %"v72" = %"v68" +p %"v71";
    %"chk2" : A = (Check 0 4 Read 1) %"v72";
    %"v74" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"chk3" : A = (Check 0 4 Write 1) %"v51";
    store Ww [%"chk3" + 0] <- %"v74";
    %"v81" = %"v72" +p #4;
    %"chk4" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v81";
    %"v82" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v52";
    store Ww [%"chk5" + 0] <- %"v82";
    %"v89" = %"v72" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v89";
    %"v90" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"chk7" : A = (Check 0 4 Write 1) %"v53";
    store Ww [%"chk7" + 0] <- %"v90";
    %"v97" = %"v72" +p #12;
    %"chk8" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v97";
    %"v98" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"chk9" : A = (Check 0 4 Write 1) %"v54";
    store Ww [%"chk9" + 0] <- %"v98"
    => goto "L61" };
  ir_blk{ @"L60":
    %"v104" = %"v10" +p #1;
    %"v105" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v106" : W = (Cmp Eq W) %"pr.10", %"v105"
    => br %"v106" ? "L107" : "L108" };
  ir_blk{ @"L107":
    %"v111" : L = (Ext Uw) %"pr.10";
    %"v112" : W = (Cmp Ult L) %"v111", #16
    => goto "L108" };
  ir_blk{ @"L108" [%"v114" : W = phi("L60" => #0, "L107" => %"v112")]:
    => br %"v114" ? "L99" : "L100" };
  ir_blk{ @"L99":
    call void $"zcpuid_count"(W #4, W %"pr.10", P %"v51", P %"v52", P %"v53", P %"v54");
    %"v117" = %"v10" +p #20;
    %"v119" : L = (Ext Uw) %"pr.10";
    %"v120" : L = Shl %"v119", #4;
    %"v121" = %"v117" +p %"v120";
    %"chk11" : A = (Check 0 4 Read 1) %"v51";
    %"v123" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"chk12" : A = (Check 0 4 Write 1) %"v121";
    store Ww [%"chk12" + 0] <- %"v123";
    %"v130" = %"v121" +p #4;
    %"chk13" : A = (Check 0 4 Read 1) %"v52";
    %"v131" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"chk14" : A = (HalfCheck Upper 0 4 Write 1) %"chk12", %"v130";
    store Ww [%"chk14" + 0] <- %"v131";
    %"v138" = %"v121" +p #8;
    %"chk15" : A = (Check 0 4 Read 1) %"v53";
    %"v139" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk12", %"v138";
    store Ww [%"chk16" + 0] <- %"v139";
    %"v146" = %"v121" +p #12;
    %"chk17" : A = (Check 0 4 Read 1) %"v54";
    %"v147" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"chk18" : A = (HalfCheck Upper 0 4 Write 1) %"chk12", %"v146";
    store Ww [%"chk18" + 0] <- %"v147";
    %"v149" = %"v10" +p #1;
    %"chk19" : A = (Renew 0 1 Read 1) %"chk1", %"v149";
    %"v150" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v151" : W = Add %"v150", #1;
    %"v152" : W = (Ext Ub) %"v151";
    %"chk20" : A = (Renew 0 1 Write 1) %"chk1", %"v149";
    store Wb [%"chk20" + 0] <- %"v152"
    => goto "L61" };
  ir_blk{ @"L100":
    call void $"zcpuid_count"(W #4, W %"pr.10", P %"v51", P %"v52", P %"v53", P %"v54")
    => goto "L61" };
  ir_blk{ @"L61":
    %"chk21" : A = (Check 0 4 Read 1) %"v51";
    %"v155" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v156" : W = And %"v155", #31;
    %"v161" : W = (Cmp Eq W) %"v156", #0
    => br %"v161" ? "L58" : "L159" };
  ir_blk{ @"L159":
    %"v164" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v165" : W = Shr %"v164", #5;
    %"v166" : W = And %"v165", #7;
    %"v171" : W = (Cmp Eq W) %"v166", #1
    => br %"v171" ? "L172" : "L173" };
  ir_blk{ @"L172":
    %"v175" : W = (Cmp Eq W) %"v156", #1
    => goto "L173" };
  ir_blk{ @"L173" [%"v177" : W = phi("L159" => #0, "L172" => %"v175")]:
    => br %"v177" ? "L178" : "L179" };
  ir_blk{ @"L178":
    %"v182" : W = (Cmp Eq W) %"pr.6", #3
    => goto "L179" };
  ir_blk{ @"L179" [%"v184" : W = phi("L173" => #0, "L178" => %"v182")]:
    => br %"v184" ? "L186" : "L185" };
  ir_blk{ @"L185":
    => br %"v171" ? "L189" : "L190" };
  ir_blk{ @"L189":
    %"v192" : W = (Cmp Eq W) %"v156", #2
    => goto "L190" };
  ir_blk{ @"L190" [%"v194" : W = phi("L185" => #0, "L189" => %"v192")]:
    => br %"v194" ? "L195" : "L186" };
  ir_blk{ @"L195":
    %"v199" : W = (Cmp Eq W) %"pr.6", #0
    => goto "L186" };
  ir_blk{ @"L186" [%"v203" : W = phi("L179" => #1, "L190" => #0, "L195" => %"v199")]:
    => br %"v203" ? "L205" : "L204" };
  ir_blk{ @"L204":
    %"v207" : W = (Cmp Eq W) %"v166", #2
    => br %"v207" ? "L208" : "L205" };
  ir_blk{ @"L208":
    %"v212" : W = (Cmp Eq W) %"pr.6", #6
    => goto "L205" };
  ir_blk{ @"L205" [%"v216" : W = phi("L186" => #1, "L204" => #0, "L208" => %"v212")]:
    => br %"v216" ? "L218" : "L217" };
  ir_blk{ @"L217":
    %"v220" : W = (Cmp Eq W) %"v166", #3
    => br %"v220" ? "L221" : "L218" };
  ir_blk{ @"L221":
    %"v225" : W = (Cmp Eq W) %"pr.6", #9
    => goto "L218" };
  ir_blk{ @"L218" [%"v229" : W = phi("L205" => #1, "L217" => #0, "L221" => %"v225")]:
    => br %"v229" ? "L231" : "L230" };
  ir_blk{ @"L230":
    %"v233" : W = (Cmp Eq W) %"v166", #4
    => br %"v233" ? "L234" : "L231" };
  ir_blk{ @"L234":
    %"v238" : W = (Cmp Eq W) %"pr.6", #12
    => goto "L231" };
  ir_blk{ @"L231" [%"v242" : W = phi("L218" => #1, "L230" => #0, "L234" => %"v238")]:
    => br %"v242" ? "L167" : "L169" }] [ir_blk{ @"L167":
    %"v245" : W = Sub %"pr.1", #185;
    %"v247" : W = Sub %"v245", %"pr.6";
    %"v252" : W = (Cmp Eq W) %"v247", #0
    => br %"v252" ? "L248" : "L250" };
  ir_blk{ @"L248":
    %"chk23" : A = (Check 0 4 Read 1) %"v52";
    %"v253" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v254" : W = Shr %"v253", #22;
    %"v255" : W = Add %"v254", #1;
    %"v256" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v257" : W = Shr %"v256", #12;
    %"v258" : W = And %"v257", #1023;
    %"v259" : W = Add %"v258", #1;
    %"v260" : W = Mul %"v255", %"v259";
    %"v261" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v262" : W = And %"v261", #4095;
    %"v263" : W = Add %"v262", #1;
    %"v264" : W = Mul %"v260", %"v263";
    %"chk26" : A = (Check 0 4 Read 1) %"v53";
    %"v265" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v266" : W = Add %"v265", #1;
    %"v267" : W = Mul %"v264", %"v266";
    %"v268" : L = (Ext Uw) %"v267"
    => ret %"v268" };
  ir_blk{ @"L250":
    %"v274" : W = (Cmp Eq W) %"v247", #1
    => br %"v274" ? "L270" : "L272" };
  ir_blk{ @"L270":
    %"chk27" : A = (Check 0 4 Read 1) %"v52";
    %"v275" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"v276" : W = Shr %"v275", #22;
    %"v277" : W = Add %"v276", #1;
    %"v278" : L = (Ext Uw) %"v277"
    => ret %"v278" };
  ir_blk{ @"L272":
    %"v284" : W = (Cmp Eq W) %"v247", #2
    => br %"v284" ? "L282" : "L281" };
  ir_blk{ @"L281":
    %"v285" : P = Copy $"glibc_libc_start#str.301";
    %"v286" : P = Copy $"glibc_libc_start#str.302";
    %"v287" : P = Copy $"glibc_libc_start#str.303";
    call void $"__libc_assert_fail"(P %"v285", P %"v286", W #217, P %"v287")
    => goto "L282" };
  ir_blk{ @"L282":
    %"chk28" : A = (Check 0 4 Read 1) %"v52";
    %"v288" : W = (RawLoad (LdNarrow Uw) 0) %"chk28";
    %"v289" : W = And %"v288", #4095;
    %"v290" : W = Add %"v289", #1;
    %"v291" : L = (Ext Uw) %"v290"
    => ret %"v291" };
  ir_blk{ @"L169":
    %"v294" : W = Add %"pr.10", #1
    => goto poll "L56" };
  ir_blk{ @"L58":
    => ret #18446744073709551615 };
  ir_blk{ @"L47":
    %"v302" : W = (Cmp Eq W) %"v31", #73
    => br %"v302" ? "L303" : "L304" };
  ir_blk{ @"L303":
    %"v307" : W = (Cmp Eq W) %"pr.6", #9
    => goto "L304" };
  ir_blk{ @"L304" [%"v309" : W = phi("L47" => #0, "L303" => %"v307")]:
    => br %"v309" ? "L298" : "L300" };
  ir_blk{ @"L298":
    %"v312" = %"v8" +p #8;
    %"chk29" : A = (Check 0 4 Read 1) %"v312";
    %"v313" : W = (RawLoad (LdNarrow Uw) 0) %"chk29";
    %"v316" = %"v8" +p #12;
    %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk29", %"v316";
    %"v317" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v322" : W = (Cmp Eq W) %"v313", #15
    => br %"v322" ? "L323" : "L324" };
  ir_blk{ @"L323":
    %"v326" : W = (Cmp Eq W) %"v317", #6
    => goto "L324" };
  ir_blk{ @"L324" [%"v328" : W = phi("L298" => #0, "L323" => %"v326")]:
    => br %"v328" ? "L318" : "L300" };
  ir_blk{ @"L318":
    %"v330" : W = Sub %"pr.1", #194;
    %"v331" : W = Add %"v330", #191
    => goto "L300" };
  ir_blk{ @"L300" [%"pr.7" : W = phi("L318" => #6, "L324" => %"pr.6", "L304" => %"pr.6"); %"pr.2" : W = phi("L318" => %"v331", "L324" => %"pr.1", "L304" => %"pr.1")]:
    %"v336" : W = (Ext Ub) %"v31";
    %"chk31" : A = (Check 0 1 Write 1) %"v334";
    store Wb [%"chk31" + 0] <- %"v336";
    %"v337" : P = Copy $"glibc_libc_start#intel_02_known";
    %"v339" : P = Copy $"glibc_libc_start#intel_02_known_compare"
    => goto "iw_1.L12" };
  ir_blk{ @"iw_1.L12" [%"iw_1.pr.3" : L = phi("iw_1.L36" => %"iw_1.v45", "L300" => #68); %"iw_1.pr.1" : P = phi("iw_1.L36" => %"iw_1.pr.2", "L300" => %"v337")]:
    %"iw_1.v16" : W = (Cmp Ne L) %"iw_1.pr.3", #0
    => br %"iw_1.v16" ? "iw_1.L13" : "iw_1.join" };
  ir_blk{ @"iw_1.L13":
    %"iw_1.v19" : L = Shr %"iw_1.pr.3", #1;
    %"iw_1.v21" : L = Shl %"iw_1.v19", #3;
    %"iw_1.v22" = %"iw_1.pr.1" +p %"iw_1.v21";
    %"chk32" : F = CheckFunction %"v339";
    rawcall %"iw_1.v26" : W = %"chk32"(P %"v334", P %"iw_1.v22");
    %"iw_1.v31" : W = (Cmp Eq W) %"iw_1.v26", #0
    => br %"iw_1.v31" ? "iw_1.join" : "iw_1.L29" };
  ir_blk{ @"iw_1.L29":
    %"iw_1.v38" : W = (Cmp Sgt W) %"iw_1.v26", #0
    => br %"iw_1.v38" ? "iw_1.L34" : "iw_1.L36" };
  ir_blk{ @"iw_1.L34":
    %"iw_1.v41" = %"iw_1.v22" +p #8;
    %"iw_1.v43" : L = Sub %"iw_1.pr.3", #1
    => goto "iw_1.L36" };
  ir_blk{ @"iw_1.L36" [%"iw_1.pr.4" : L = phi("iw_1.L34" => %"iw_1.v43", "iw_1.L29" => %"iw_1.pr.3"); %"iw_1.pr.2" : P = phi("iw_1.L34" => %"iw_1.v41", "iw_1.L29" => %"iw_1.pr.1")]:
    %"iw_1.v45" : L = Shr %"iw_1.pr.4", #1
    => goto poll "iw_1.L12" };
  ir_blk{ @"iw_1.join" [%"v340" : P = phi("iw_1.L13" => %"iw_1.v22", "iw_1.L12" => #0)]:
    %"v345" : L = Ptoi %"v340";
    %"v346" : L = Ptoi #0;
    %"v347" : W = (Cmp Ne L) %"v345", %"v346"
    => br %"v347" ? "L341" : "L34" };
  ir_blk{ @"L341":
    %"v352" = %"v340" +p #3;
    %"chk33" : A = (Check 0 1 Read 1) %"v352";
    %"v353" : W = (RawLoad (LdNarrow Ub) 0) %"chk33";
    %"v355" : W = (Cmp Eq W) %"v353", %"pr.7"
    => br %"v355" ? "L348" : "L350" };
  ir_blk{ @"L348":
    %"v358" : W = Sub %"pr.2", #185;
    %"v360" : W = Sub %"v358", %"pr.7";
    %"v365" : W = (Cmp Eq W) %"v360", #0
    => br %"v365" ? "L361" : "L363" };
  ir_blk{ @"L361":
    %"v367" = %"v340" +p #4;
    %"chk34" : A = (HalfCheck Upper 0 4 Read 1) %"chk33", %"v367";
    %"v368" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"v369" : L = (Ext Uw) %"v368"
    => ret %"v369" };
  ir_blk{ @"L363":
    %"v375" : W = (Cmp Eq W) %"v360", #1
    => br %"v375" ? "L371" : "L373" };
  ir_blk{ @"L371":
    %"v377" = %"v340" +p #1;
    %"chk35" : A = (HalfCheck Lower 0 1 Read 1) %"chk33", %"v377";
    %"v378" : W = (RawLoad (LdNarrow Ub) 0) %"chk35";
    %"v379" : L = (Ext Uw) %"v378"
    => ret %"v379" };
  ir_blk{ @"L373":
    %"v385" : W = (Cmp Eq W) %"v360", #2
    => br %"v385" ? "L383" : "L382" };
  ir_blk{ @"L382":
    %"v386" : P = Copy $"glibc_libc_start#str.301";
    %"v387" : P = Copy $"glibc_libc_start#str.302";
    %"v388" : P = Copy $"glibc_libc_start#str.303";
    call void $"__libc_assert_fail"(P %"v386", P %"v387", W #266, P %"v388")
    => goto "L383" };
  ir_blk{ @"L383":
    %"v390" = %"v340" +p #2;
    %"chk36" : A = (HalfCheck Lower 0 1 Read 1) %"chk33", %"v390";
    %"v391" : W = (RawLoad (LdNarrow Ub) 0) %"chk36";
    %"v392" : L = (Ext Uw) %"v391"
    => ret %"v392" };
  ir_blk{ @"L350":
    %"v398" = %"v340" +p #3;
    %"v399" : W = (RawLoad (LdNarrow Ub) 0) %"chk33";
    %"v401" : W = (Cmp Eq W) %"v399", #6
    => br %"v401" ? "L394" : "L34" };
  ir_blk{ @"L394":
    %"chk38" : A = (Check 0 1 Write 1) %"v4";
    store Wb [%"chk38" + 0] <- #1
    => goto "L34" };
  ir_blk{ @"L34" [%"pr.9" : W = phi("L32" => %"pr.6", "L394" => %"pr.7", "L350" => %"pr.7", "iw_1.join" => %"pr.7"); %"pr.4" : W = phi("L32" => %"pr.1", "L394" => %"pr.2", "L350" => %"pr.2", "iw_1.join" => %"pr.2")]:
    %"v405" : W = Shr %"pr.5", #8
    => goto poll "L24" };
  ir_blk{ @"L26":
    => ret #0 }])) }.

Definition fn_glibc_libc_start'23internal_signal_block_all : func :=
  ir_fn{ "local" "glibc_libc_start#internal_signal_block_all"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_libc_start#sigall_set";
    call %"v4" : W = $"zsys_sigprocmask"(W #0, P %"v2", P %"v0")
    => ret void
} }.

Definition item_glibc_libc_start'23sigall_set : item :=
  (IData (a "glibc_libc_start#sigall_set") (LRo (a "local")) 8 [(Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615)]).

Definition item_glibc_libc_start'23str'2e301 : item :=
  (IData (a "glibc_libc_start#str.301") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 102); (Item Wb 102); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 50); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e302 : item :=
  (IData (a "glibc_libc_start#str.302") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 120); (Item Wb 56); (Item Wb 54); (Item Wb 47); (Item Wb 100); (Item Wb 108); (Item Wb 45); (Item Wb 99); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e303 : item :=
  (IData (a "glibc_libc_start#str.303") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 108); (Item Wb 95); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 99); (Item Wb 107); (Item Wb 95); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e304 : item :=
  (IData (a "glibc_libc_start#str.304") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 122); (Item Wb 104); (Item Wb 97); (Item Wb 111); (Item Wb 120); (Item Wb 105); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e319 : item :=
  (IData (a "glibc_libc_start#str.319") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110)] [(Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 10); (Item Wb 9); (Item Wb 0)])).

Definition item_glibc_libc_start'23str'2e320 : item :=
  (IData (a "glibc_libc_start#str.320") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 103); (Item Wb 114); (Item Wb 97); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e321 : item :=
  (IData (a "glibc_libc_start#str.321") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 116); (Item Wb 114); (Item Wb 111); (Item Wb 108); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 10); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e322 : item :=
  (IData (a "glibc_libc_start#str.322") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e323 : item :=
  (IData (a "glibc_libc_start#str.323") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 110); (Item Wb 112); (Item Wb 116); (Item Wb 108); (Item Wb 47); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e324 : item :=
  (IData (a "glibc_libc_start#str.324") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 107); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e325 : item :=
  (IData (a "glibc_libc_start#str.325") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e326 : item :=
  (IData (a "glibc_libc_start#str.326") (LRo (a "local")) 1 [(Item Wb 120); (Item Wb 101); (Item Wb 111); (Item Wb 110); (Item Wb 95); (Item Wb 112); (Item Wb 104); (Item Wb 105); (Item Wb 0)]).

Definition item_glibc_libc_start'23str'2e327 : item :=
  (IData (a "glibc_libc_start#str.327") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 97); (Item Wb 115); (Item Wb 119); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 0)]).

Definition fn_glibc_libc_start'23update_active : func :=
  ir_fn{ "local" "glibc_libc_start#update_active"(P %"v0") -> RVoid {
  @"start":
    code ((app (app (app ir[ %"v1523" : P = (Alloc 4) #4;
      %"v1524" : P = (Alloc 4) #4;
      %"v1525" : P = (Alloc 4) #4;
      %"v1526" : P = (Alloc 4) #4;
      %"v1562" : P = (Alloc 4) #80;
      %"v1563" : P = (Alloc 4) #80;
      %"v3" = %"v0" +p #20;
      %"v5" = %"v3" +p #16;
      %"v6" = %"v5" +p #8;
      %"chk0" : A = (Check 0 4 Read 1) %"v6";
      %"v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
      %"v11" = %"v3" +p #8;
      %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v11";
      %"v12" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v14" : W = And %"v12", #1;
      %"v15" : W = Or %"v7", %"v14";
      %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v6";
      store Ww [%"chk2" + 0] <- %"v15";
      %"v21" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v26" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v28" : W = And %"v26", #2;
      %"v29" : W = Or %"v21", %"v28";
      store Ww [%"chk2" + 0] <- %"v29";
      %"v35" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v40" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v42" : W = And %"v40", #512;
      %"v43" : W = Or %"v35", %"v42";
      store Ww [%"chk2" + 0] <- %"v43";
      %"v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v54" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v56" : W = And %"v54", #8192;
      %"v57" : W = Or %"v49", %"v56";
      store Ww [%"chk2" + 0] <- %"v57";
      %"v63" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v68" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v70" : W = And %"v68", #524288;
      %"v71" : W = Or %"v63", %"v70";
      store Ww [%"chk2" + 0] <- %"v71";
      %"v77" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v82" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v84" : W = And %"v82", #1048576] ir[ %"v85" : W = Or %"v77", %"v84";
      store Ww [%"chk2" + 0] <- %"v85";
      %"v91" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v96" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v98" : W = And %"v96", #4194304;
      %"v99" : W = Or %"v91", %"v98";
      store Ww [%"chk2" + 0] <- %"v99";
      %"v105" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v110" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v112" : W = And %"v110", #8388608;
      %"v113" : W = Or %"v105", %"v112";
      store Ww [%"chk2" + 0] <- %"v113";
      %"v119" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v124" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v126" : W = And %"v124", #33554432;
      %"v127" : W = Or %"v119", %"v126";
      store Ww [%"chk2" + 0] <- %"v127";
      %"v133" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v138" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v140" : W = And %"v138", #134217728;
      %"v141" : W = Or %"v133", %"v140";
      store Ww [%"chk2" + 0] <- %"v141";
      %"v146" = %"v5" +p #12;
      %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v146";
      %"v147" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v151" = %"v3" +p #12;
      %"v152" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v154" : W = And %"v152", #16;
      %"v155" : W = Or %"v147", %"v154";
      store Ww [%"chk30" + 0] <- %"v155";
      %"v161" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v166" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v168" : W = And %"v166", #256;
      %"v169" : W = Or %"v161", %"v168";
      store Ww [%"chk30" + 0] <- %"v169";
      %"v175" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v180" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v182" : W = And %"v180", #32768;
      %"v183" : W = Or %"v175", %"v182";
      store Ww [%"chk30" + 0] <- %"v183";
      %"v189" : W = (RawLoad (LdNarrow Uw) 0) %"chk30"]) (app ir[ %"v194" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v196" : W = And %"v194", #524288;
      %"v197" : W = Or %"v189", %"v196";
      store Ww [%"chk30" + 0] <- %"v197";
      %"v203" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v208" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v210" : W = And %"v208", #8388608;
      %"v211" : W = Or %"v203", %"v210";
      store Ww [%"chk30" + 0] <- %"v211";
      %"v217" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v222" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v224" : W = And %"v222", #16777216;
      %"v225" : W = Or %"v217", %"v224";
      store Ww [%"chk30" + 0] <- %"v225";
      %"v231" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v236" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v238" : W = And %"v236", #33554432;
      %"v239" : W = Or %"v231", %"v238";
      store Ww [%"chk30" + 0] <- %"v239";
      %"v245" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v250" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v252" : W = And %"v250", #67108864;
      %"v253" : W = Or %"v245", %"v252";
      store Ww [%"chk30" + 0] <- %"v253";
      %"v259" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
      %"v264" : W = (RawLoad (LdNarrow Uw) 4) %"chk1";
      %"v266" : W = And %"v264", #268435456;
      %"v267" : W = Or %"v259", %"v266";
      store Ww [%"chk30" + 0] <- %"v267";
      %"v270" = %"v3" +p #32;
      %"v271" = %"v270" +p #16;
      %"v272" = %"v271" +p #4;
      %"chk57" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v272";
      %"v273" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v277" = %"v270" +p #4;
      %"v278" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v280" : W = And %"v278", #8;
      %"v281" : W = Or %"v273", %"v280";
      store Ww [%"chk57" + 0] <- %"v281";
      %"v287" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v292" : W = (RawLoad (LdNarrow Uw) 8) %"chk30"] ir[ %"v294" : W = And %"v292", #16;
      %"v295" : W = Or %"v287", %"v294";
      store Ww [%"chk57" + 0] <- %"v295";
      %"v301" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v306" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v308" : W = And %"v306", #256;
      %"v309" : W = Or %"v301", %"v308";
      store Ww [%"chk57" + 0] <- %"v309";
      %"v315" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v320" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v322" : W = And %"v320", #512;
      %"v323" : W = Or %"v315", %"v322";
      store Ww [%"chk57" + 0] <- %"v323";
      %"v329" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v334" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v336" : W = And %"v334", #262144;
      %"v337" : W = Or %"v329", %"v336";
      store Ww [%"chk57" + 0] <- %"v337";
      %"v343" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v348" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v350" : W = And %"v348", #524288;
      %"v351" : W = Or %"v343", %"v350";
      store Ww [%"chk57" + 0] <- %"v351";
      %"v357" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v362" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v364" : W = And %"v362", #8388608;
      %"v365" : W = Or %"v357", %"v364";
      store Ww [%"chk57" + 0] <- %"v365";
      %"v371" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v376" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v378" : W = And %"v376", #16777216;
      %"v379" : W = Or %"v371", %"v378";
      store Ww [%"chk57" + 0] <- %"v379";
      %"v385" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
      %"v390" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
      %"v392" : W = And %"v390", #536870912;
      %"v393" : W = Or %"v385", %"v392";
      store Ww [%"chk57" + 0] <- %"v393";
      %"v398" = %"v271" +p #8;
      %"chk84" : A = (HalfCheck Upper 0 4 Read 1) %"chk57", %"v398";
      %"v399" : W = (RawLoad (LdNarrow Uw) 0) %"chk84"])) (app (app ir[ %"v403" = %"v270" +p #8;
      %"v404" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v406" : W = And %"v404", #1;
      %"v407" : W = Or %"v399", %"v406";
      store Ww [%"chk84" + 0] <- %"v407";
      %"v413" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v418" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v420" : W = And %"v418", #16;
      %"v421" : W = Or %"v413", %"v420";
      store Ww [%"chk84" + 0] <- %"v421";
      %"v427" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v432" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v434" : W = And %"v432", #32;
      %"v435" : W = Or %"v427", %"v434";
      store Ww [%"chk84" + 0] <- %"v435";
      %"v441" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v446" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v448" : W = And %"v446", #256;
      %"v449" : W = Or %"v441", %"v448";
      store Ww [%"chk84" + 0] <- %"v449";
      %"v455" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v460" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v462" : W = And %"v460", #4194304;
      %"v463" : W = Or %"v455", %"v462";
      store Ww [%"chk84" + 0] <- %"v463";
      %"v469" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
      %"v474" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
      %"v476" : W = And %"v474", #1073741824;
      %"v477" : W = Or %"v469", %"v476";
      store Ww [%"chk2" + 0] <- %"v477";
      %"v483" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v488" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v490" : W = And %"v488", #33554432;
      %"v491" : W = Or %"v483", %"v490";
      store Ww [%"chk84" + 0] <- %"v491";
      %"v497" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
      %"v502" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v504" : W = And %"v502", #134217728;
      %"v505" : W = Or %"v497", %"v504";
      store Ww [%"chk84" + 0] <- %"v505";
      %"v511" : W = (RawLoad (LdNarrow Uw) 0) %"chk84"] ir[ %"v516" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk57";
      %"v518" : W = And %"v516", #268435456;
      %"v519" : W = Or %"v511", %"v518";
      store Ww [%"chk84" + 0] <- %"v519";
      %"v524" = %"v271" +p #12;
      %"chk111" : A = (HalfCheck Upper 0 4 Read 1) %"chk57", %"v524";
      %"v525" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v529" = %"v270" +p #12;
      %"v530" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v532" : W = And %"v530", #16;
      %"v533" : W = Or %"v525", %"v532";
      store Ww [%"chk111" + 0] <- %"v533";
      %"v539" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v544" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v546" : W = And %"v544", #2048;
      %"v547" : W = Or %"v539", %"v546";
      store Ww [%"chk111" + 0] <- %"v547";
      %"v553" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v558" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v560" : W = And %"v558", #16384;
      %"v561" : W = Or %"v553", %"v560";
      store Ww [%"chk111" + 0] <- %"v561";
      %"v567" : W = (RawLoad (LdNarrow Uw) 0) %"chk111";
      %"v572" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v574" : W = And %"v572", #65536;
      %"v575" : W = Or %"v567", %"v574";
      store Ww [%"chk111" + 0] <- %"v575";
      %"v578" = %"v3" +p #64;
      %"v579" = %"v578" +p #16;
      %"v580" = %"v579" +p #8;
      %"chk123" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v580";
      %"v581" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v585" = %"v578" +p #8;
      %"v586" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v588" : W = And %"v586", #1;
      %"v589" : W = Or %"v581", %"v588";
      store Ww [%"chk123" + 0] <- %"v589";
      %"v595" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v600" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v602" : W = And %"v600", #32;
      %"v603" : W = Or %"v595", %"v602"]) (app ir[ store Ww [%"chk123" + 0] <- %"v603";
      %"v609" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v614" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v616" : W = And %"v614", #64;
      %"v617" : W = Or %"v609", %"v616";
      store Ww [%"chk123" + 0] <- %"v617";
      %"v623" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v628" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v630" : W = And %"v628", #256;
      %"v631" : W = Or %"v623", %"v630";
      store Ww [%"chk123" + 0] <- %"v631";
      %"v637" : W = (RawLoad (LdNarrow Uw) 0) %"chk123";
      %"v642" : W = (RawLoad (LdNarrow Uw) 12) %"chk111";
      %"v644" : W = And %"v642", #2097152;
      %"v645" : W = Or %"v637", %"v644";
      store Ww [%"chk123" + 0] <- %"v645";
      %"v650" = %"v579" +p #12;
      %"chk138" : A = (HalfCheck Upper 0 4 Read 1) %"chk123", %"v650";
      %"v651" : W = (RawLoad (LdNarrow Uw) 0) %"chk138";
      %"v655" = %"v578" +p #12;
      %"v656" : W = (RawLoad (LdNarrow Uw) (-12)) %"chk123";
      %"v658" : W = And %"v656", #134217728;
      %"v659" : W = Or %"v651", %"v658";
      store Ww [%"chk138" + 0] <- %"v659";
      %"v662" = %"v3" +p #160;
      %"v663" = %"v662" +p #16;
      %"v664" = %"v663" +p #4;
      %"chk141" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v664";
      %"v665" : W = (RawLoad (LdNarrow Uw) 0) %"chk141";
      %"v669" = %"v662" +p #4;
      %"v670" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk141";
      %"v672" : W = And %"v670", #512;
      %"v673" : W = Or %"v665", %"v672";
      store Ww [%"chk141" + 0] <- %"v673";
      %"v676" = %"v3" +p #192;
      %"v677" = %"v676" +p #16;
      %"chk144" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v677";
      %"v678" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v682" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v684" : W = And %"v682", #8;
      %"v685" : W = Or %"v678", %"v684"] ir[ store Ww [%"chk144" + 0] <- %"v685";
      %"v690" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v694" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v696" : W = And %"v694", #128;
      %"v697" : W = Or %"v690", %"v696";
      store Ww [%"chk144" + 0] <- %"v697";
      %"v702" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v706" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v708" : W = And %"v706", #1024;
      %"v709" : W = Or %"v702", %"v708";
      store Ww [%"chk144" + 0] <- %"v709";
      %"v714" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v718" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v720" : W = And %"v718", #2048;
      %"v721" : W = Or %"v714", %"v720";
      store Ww [%"chk144" + 0] <- %"v721";
      %"v726" : W = (RawLoad (LdNarrow Uw) 0) %"chk144";
      %"v730" : W = (RawLoad (LdNarrow Uw) 12) %"chk141";
      %"v732" : W = And %"v730", #4096;
      %"v733" : W = Or %"v726", %"v732";
      store Ww [%"chk144" + 0] <- %"v733";
      %"v738" = %"v677" +p #12;
      %"chk159" : A = (HalfCheck Upper 0 4 Read 1) %"chk144", %"v738";
      %"v739" : W = (RawLoad (LdNarrow Uw) 0) %"chk159";
      %"v743" = %"v676" +p #12;
      %"v744" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk144";
      %"v746" : W = And %"v744", #16384;
      %"v747" : W = Or %"v739", %"v746";
      store Ww [%"chk159" + 0] <- %"v747";
      %"v750" = %"v3" +p #256;
      %"v751" = %"v750" +p #16;
      %"v752" = %"v751" +p #4;
      %"chk162" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v752";
      %"v753" : W = (RawLoad (LdNarrow Uw) 0) %"chk162";
      %"v757" = %"v750" +p #4;
      %"v758" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk162";
      %"v760" : W = And %"v758", #16;
      %"v761" : W = Or %"v753", %"v760";
      store Ww [%"chk162" + 0] <- %"v761";
      %"v769" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk57";
      %"v771" : W = And %"v769", #2048;
      %"v773" : W = (Cmp Eq W) %"v771", #0]))))
    => br %"v773" ? "L762" : "L764";
  @"L762":
    %"v775" = %"v0" +p #20;
    %"v776" = %"v775" +p #32;
    %"v777" = %"v776" +p #16;
    %"v778" = %"v777" +p #4;
    %"v779" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
    %"v783" = %"v776" +p #4;
    %"v784" : W = (RawLoad (LdNarrow Uw) 8) %"chk30";
    %"v786" : W = And %"v784", #2048;
    %"v787" : W = Or %"v779", %"v786";
    store Ww [%"chk57" + 0] <- %"v787"
    => goto "L764";
  @"L764":
    %"v793" = %"v0" +p #20;
    %"v795" = %"v793" +p #8;
    %"v796" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v798" : W = And %"v796", #134217728;
    %"v799" : W = (Cmp Ne W) %"v798", #0
    => br %"v799" ? "L789" : "L791";
  @"L789":
    %"v802" = %"v0" +p #20;
    %"v803" = %"v802" +p #192;
    %"v804" = %"v803" +p #16;
    %"v805" = %"v804" +p #12;
    %"v806" : W = (RawLoad (LdNarrow Uw) 0) %"chk159";
    %"v810" = %"v803" +p #12;
    %"v811" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk144";
    %"v813" : W = And %"v811", #524288;
    %"v814" : W = Or %"v806", %"v813";
    store Ww [%"chk159" + 0] <- %"v814";
    call %"v815" : L = $"zxgetbv"();
    %"v819" : W = Copy %"v815";
    %"v823" : W = And %"v819", #6;
    %"v827" : W = (Cmp Eq W) %"v823", #6
    => br %"v827" ? "L816" : "L818";
  @"L816":
    %"v832" = %"v0" +p #20;
    %"v834" = %"v832" +p #8;
    %"chk173" : A = (Renew 0 4 Read 1) %"chk1", %"v834";
    %"v835" : W = (RawLoad (LdNarrow Uw) 0) %"chk173";
    %"v837" : W = And %"v835", #268435456;
    %"v838" : W = (Cmp Ne W) %"v837", #0
    => br %"v838" ? "L828" : "L830";
  @"L828":
    %"v842" = %"v0" +p #20;
    %"v844" = %"v842" +p #16;
    %"v845" = %"v844" +p #8;
    %"chk174" : A = (Renew 0 4 Read 1) %"chk0", %"v845";
    %"v846" : W = (RawLoad (LdNarrow Uw) 0) %"chk174";
    %"v848" : W = Or %"v846", #268435456;
    %"chk175" : A = (Renew 0 4 Write 1) %"chk0", %"v845";
    store Ww [%"chk175" + 0] <- %"v848";
    %"v854" = %"v842" +p #32;
    %"v855" = %"v854" +p #4;
    %"chk176" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v855";
    %"v856" : W = (RawLoad (LdNarrow Uw) 0) %"chk176";
    %"v858" : W = And %"v856", #32;
    %"v859" : W = (Cmp Ne W) %"v858", #0
    => br %"v859" ? "L849" : "L851";
  @"L849":
    %"v861" = %"v0" +p #20;
    %"v862" = %"v861" +p #32;
    %"v863" = %"v862" +p #16;
    %"v864" = %"v863" +p #4;
    %"chk177" : A = (Renew 0 4 Read 1) %"chk57", %"v864";
    %"v865" : W = (RawLoad (LdNarrow Uw) 0) %"chk177";
    %"v867" : W = Or %"v865", #32;
    store Ww [%"chk177" + 0] <- %"v867";
    %"v869" = %"v0" +p #340;
    %"chk179" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v869";
    %"v871" : W = (RawLoad (LdNarrow Uw) 0) %"chk179";
    %"v872" : W = Or %"v871", #512;
    store Ww [%"chk179" + 0] <- %"v872"
    => goto "L851";
  @"L851":
    %"v874" = %"v0" +p #20;
    %"v875" = %"v874" +p #192;
    %"v876" = %"v875" +p #16;
    %"chk181" : A = (Renew 0 4 Read 1) %"chk144", %"v876";
    %"v877" : W = (RawLoad (LdNarrow Uw) 0) %"chk181";
    %"v881" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk181";
    %"v883" : W = And %"v881", #8388608;
    %"v884" : W = Or %"v877", %"v883";
    store Ww [%"chk181" + 0] <- %"v884";
    %"v889" = %"v876" +p #12;
    %"chk184" : A = (Renew 0 4 Read 1) %"chk159", %"v889";
    %"v890" : W = (RawLoad (LdNarrow Uw) 0) %"chk184";
    %"v894" = %"v875" +p #12;
    %"v895" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk181";
    %"v897" : W = And %"v895", #32;
    %"v898" : W = Or %"v890", %"v897";
    store Ww [%"chk184" + 0] <- %"v898";
    %"v903" : W = (RawLoad (LdNarrow Uw) 0) %"chk181";
    %"v907" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk181";
    %"v909" : W = And %"v907", #16;
    %"v910" : W = Or %"v903", %"v909";
    store Ww [%"chk181" + 0] <- %"v910";
    %"v916" : W = (RawLoad (LdNarrow Uw) 0) %"chk184";
    %"v921" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk181";
    %"v923" : W = And %"v921", #16;
    %"v924" : W = Or %"v916", %"v923";
    store Ww [%"chk184" + 0] <- %"v924";
    %"v928" = %"v874" +p #16;
    %"v929" = %"v928" +p #8;
    %"v930" : W = (RawLoad (LdNarrow Uw) 0) %"chk175";
    %"v934" = %"v874" +p #8;
    %"v935" : W = (RawLoad (LdNarrow Uw) 0) %"chk173";
    %"v937" : W = And %"v935", #4096;
    %"v938" : W = Or %"v930", %"v937";
    store Ww [%"chk175" + 0] <- %"v938";
    %"v941" = %"v874" +p #32;
    %"v942" = %"v941" +p #16;
    %"v943" = %"v942" +p #8;
    %"v944" : W = (RawLoad (LdNarrow Uw) 20) %"chk176";
    %"v948" = %"v941" +p #8;
    %"v949" : W = (RawLoad (LdNarrow Uw) 4) %"chk176";
    %"v951" : W = And %"v949", #512;
    %"v952" : W = Or %"v944", %"v951";
    store Ww [%"chk176" + 20] <- %"v952";
    %"v958" : W = (RawLoad (LdNarrow Uw) 20) %"chk176";
    %"v963" : W = (RawLoad (LdNarrow Uw) 4) %"chk176";
    %"v965" : W = And %"v963", #1024;
    %"v966" : W = Or %"v958", %"v965";
    store Ww [%"chk176" + 20] <- %"v966";
    %"v969" = %"v874" +p #64;
    %"v970" = %"v969" +p #16;
    %"v971" = %"v970" +p #8;
    %"v972" : W = (RawLoad (LdNarrow Uw) 52) %"chk176";
    %"v976" = %"v969" +p #8;
    %"v977" : W = (RawLoad (LdNarrow Uw) 36) %"chk176";
    %"v979" : W = And %"v977", #2048;
    %"v980" : W = Or %"v972", %"v979";
    store Ww [%"chk176" + 52] <- %"v980";
    %"v986" : W = (RawLoad (LdNarrow Uw) 0) %"chk175";
    %"v991" : W = (RawLoad (LdNarrow Uw) 0) %"chk173";
    %"v993" : W = And %"v991", #536870912;
    %"v994" : W = Or %"v986", %"v993";
    store Ww [%"chk175" + 0] <- %"v994"
    => goto "L830";
  @"L830" [%"pr.2" : W = phi("L851" => #3, "L816" => #1)]:
    %"v998" : W = Copy %"v815";
    %"v1004" : W = And %"v998", #224;
    %"v1010" : W = (Cmp Eq W) %"v1004", #224
    => br %"v1010" ? "L995" : "L818";
  @"L995":
    %"v1012" : W = Or %"pr.2", #4;
    %"v1017" = %"v0" +p #20;
    %"v1018" = %"v1017" +p #32;
    %"v1019" = %"v1018" +p #4;
    %"chk208" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1019";
    %"v1020" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
    %"v1022" : W = And %"v1020", #65536;
    %"v1023" : W = (Cmp Ne W) %"v1022", #0
    => br %"v1023" ? "L1013" : "L818";
  @"L1013":
    code ((app ir[ %"v1025" = %"v0" +p #20;
      %"v1026" = %"v1025" +p #32;
      %"v1027" = %"v1026" +p #16;
      %"v1028" = %"v1027" +p #4;
      %"chk209" : A = (Renew 0 4 Read 1) %"chk57", %"v1028";
      %"v1029" : W = (RawLoad (LdNarrow Uw) 0) %"chk209";
      %"v1031" : W = Or %"v1029", #65536;
      %"chk210" : A = (Renew 0 4 Write 1) %"chk57", %"v1028";
      store Ww [%"chk210" + 0] <- %"v1031";
      %"v1037" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1041" = %"v1026" +p #4;
      %"v1042" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1044" : W = And %"v1042", #268435456;
      %"v1045" : W = Or %"v1037", %"v1044";
      store Ww [%"chk210" + 0] <- %"v1045";
      %"v1051" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1056" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1058" : W = And %"v1056", #134217728;
      %"v1059" : W = Or %"v1051", %"v1058";
      store Ww [%"chk210" + 0] <- %"v1059";
      %"v1065" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1070" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1072" : W = And %"v1070", #67108864;
      %"v1073" : W = Or %"v1065", %"v1072";
      store Ww [%"chk210" + 0] <- %"v1073";
      %"v1079" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1084" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1086" : W = And %"v1084", #2147483648;
      %"v1087" : W = Or %"v1079", %"v1086";
      store Ww [%"chk210" + 0] <- %"v1087";
      %"v1093" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1098" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1100" : W = And %"v1098", #131072;
      %"v1101" : W = Or %"v1093", %"v1100";
      store Ww [%"chk210" + 0] <- %"v1101";
      %"v1107" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1112" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1114" : W = And %"v1112", #1073741824;
      %"v1115" : W = Or %"v1107", %"v1114";
      store Ww [%"chk210" + 0] <- %"v1115";
      %"v1120" = %"v1027" +p #12;
      %"chk229" : A = (Renew 0 4 Read 1) %"chk111", %"v1120";
      %"v1121" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1125" = %"v1026" +p #12;
      %"v1126" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1128" : W = And %"v1126", #8;
      %"v1129" : W = Or %"v1121", %"v1128";
      store Ww [%"chk229" + 0] <- %"v1129";
      %"v1135" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1140" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1142" : W = And %"v1140", #4] ir[ %"v1143" : W = Or %"v1135", %"v1142";
      store Ww [%"chk229" + 0] <- %"v1143";
      %"v1148" = %"v1027" +p #8;
      %"v1149" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1153" = %"v1026" +p #8;
      %"v1154" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1156" : W = And %"v1154", #4096;
      %"v1157" : W = Or %"v1149", %"v1156";
      store Ww [%"chk229" + (-4)] <- %"v1157";
      %"v1163" : W = (RawLoad (LdNarrow Uw) 0) %"chk210";
      %"v1168" : W = (RawLoad (LdNarrow Uw) 0) %"chk208";
      %"v1170" : W = And %"v1168", #2097152;
      %"v1171" : W = Or %"v1163", %"v1170";
      store Ww [%"chk210" + 0] <- %"v1171";
      %"v1177" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1182" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1184" : W = And %"v1182", #2;
      %"v1185" : W = Or %"v1177", %"v1184";
      store Ww [%"chk229" + (-4)] <- %"v1185";
      %"v1191" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1196" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1198" : W = And %"v1196", #64;
      %"v1199" : W = Or %"v1191", %"v1198";
      store Ww [%"chk229" + (-4)] <- %"v1199";
      %"v1205" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1210" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1212" : W = And %"v1210", #2048;
      %"v1213" : W = Or %"v1205", %"v1212";
      store Ww [%"chk229" + (-4)] <- %"v1213";
      %"v1219" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk229";
      %"v1224" : W = (RawLoad (LdNarrow Uw) 4) %"chk208";
      %"v1226" : W = And %"v1224", #16384;
      %"v1227" : W = Or %"v1219", %"v1226";
      store Ww [%"chk229" + (-4)] <- %"v1227";
      %"v1233" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1238" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1240" : W = And %"v1238", #256;
      %"v1241" : W = Or %"v1233", %"v1240";
      store Ww [%"chk229" + 0] <- %"v1241";
      %"v1244" = %"v1025" +p #192;
      %"v1245" = %"v1244" +p #16;
      %"chk256" : A = (Renew 0 4 Read 1) %"chk144", %"v1245";
      %"v1246" : W = (RawLoad (LdNarrow Uw) 0) %"chk256";
      %"v1250" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk256";
      %"v1252" : W = And %"v1250", #32;
      %"v1253" : W = Or %"v1246", %"v1252";
      store Ww [%"chk256" + 0] <- %"v1253";
      %"v1259" : W = (RawLoad (LdNarrow Uw) 0) %"chk229";
      %"v1264" : W = (RawLoad (LdNarrow Uw) (-8)) %"chk210";
      %"v1266" : W = And %"v1264", #8388608;
      %"v1267" : W = Or %"v1259", %"v1266";
      store Ww [%"chk229" + 0] <- %"v1267"]))
    => goto "L818";
  @"L818" [%"pr.1" : W = phi("L1013" => %"v1012", "L995" => %"v1012", "L830" => %"pr.2", "L789" => #1)]:
    %"v1272" = %"v0" +p #20;
    %"v1273" = %"v1272" +p #192;
    %"v1274" = %"v1273" +p #12;
    %"chk262" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1274";
    %"v1275" : W = (RawLoad (LdNarrow Uw) 0) %"chk262";
    %"v1277" : W = And %"v1275", #524288;
    %"v1278" : W = (Cmp Ne W) %"v1277", #0
    => br %"v1278" ? "L1279" : "L1280";
  @"L1279":
    %"v1282" = %"v0" +p #4;
    %"chk263" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v1282";
    %"v1283" : W = (RawLoad (LdNarrow Sw) 0) %"chk263";
    %"v1284" : W = (Cmp Sge W) %"v1283", #36
    => goto "L1280";
  @"L1280" [%"v1286" : W = phi("L818" => #0, "L1279" => %"v1284")]:
    => br %"v1286" ? "L1268" : "L1270";
  @"L1268":
    %"v1288" = %"v0" +p #20;
    %"v1289" = %"v1288" +p #288;
    %"v1293" = %"v1289" +p #4;
    %"v1297" = %"v1289" +p #8;
    %"v1301" = %"v1289" +p #12;
    call void $"zcpuid_count"(W #36, W #0, P %"v1289", P %"v1293", P %"v1297", P %"v1301");
    %"v1306" : W = And %"pr.1", #1
    => br %"v1306" ? "L1302" : "L1304";
  @"L1302":
    %"v1308" = %"v0" +p #20;
    %"v1309" = %"v1308" +p #288;
    %"v1310" = %"v1309" +p #16;
    %"v1311" = %"v1310" +p #4;
    %"chk264" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1311";
    %"v1312" : W = (RawLoad (LdNarrow Uw) 0) %"chk264";
    %"v1316" = %"v1309" +p #4;
    %"chk265" : A = (HalfCheck Lower 0 4 Read 1) %"chk264", %"v1316";
    %"v1317" : W = (RawLoad (LdNarrow Uw) 0) %"chk265";
    %"v1319" : W = And %"v1317", #65536;
    %"v1320" : W = Or %"v1312", %"v1319";
    %"chk266" : A = (Renew 0 4 Write 1) %"chk264", %"v1311";
    store Ww [%"chk266" + 0] <- %"v1320"
    => goto "L1304";
  @"L1304":
    %"v1325" : W = And %"pr.1", #2
    => br %"v1325" ? "L1321" : "L1323";
  @"L1321":
    %"v1327" = %"v0" +p #20;
    %"v1328" = %"v1327" +p #288;
    %"v1329" = %"v1328" +p #16;
    %"v1330" = %"v1329" +p #4;
    %"chk267" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1330";
    %"v1331" : W = (RawLoad (LdNarrow Uw) 0) %"chk267";
    %"v1335" = %"v1328" +p #4;
    %"chk268" : A = (HalfCheck Lower 0 4 Read 1) %"chk267", %"v1335";
    %"v1336" : W = (RawLoad (LdNarrow Uw) 0) %"chk268";
    %"v1338" : W = And %"v1336", #131072;
    %"v1339" : W = Or %"v1331", %"v1338";
    %"chk269" : A = (Renew 0 4 Write 1) %"chk267", %"v1330";
    store Ww [%"chk269" + 0] <- %"v1339"
    => goto "L1323";
  @"L1323":
    %"v1344" : W = And %"pr.1", #4
    => br %"v1344" ? "L1340" : "L1270";
  @"L1340":
    %"v1346" = %"v0" +p #20;
    %"v1347" = %"v1346" +p #288;
    %"v1348" = %"v1347" +p #16;
    %"v1349" = %"v1348" +p #4;
    %"chk270" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1349";
    %"v1350" : W = (RawLoad (LdNarrow Uw) 0) %"chk270";
    %"v1354" = %"v1347" +p #4;
    %"chk271" : A = (HalfCheck Lower 0 4 Read 1) %"chk270", %"v1354";
    %"v1355" : W = (RawLoad (LdNarrow Uw) 0) %"chk271";
    %"v1357" : W = And %"v1355", #262144;
    %"v1358" : W = Or %"v1350", %"v1357";
    %"chk272" : A = (Renew 0 4 Write 1) %"chk270", %"v1349";
    store Ww [%"chk272" + 0] <- %"v1358"
    => goto "L1270";
  @"L1270":
    %"v1362" : W = Copy %"v815";
    %"v1366" : W = And %"v1362", #393216;
    %"v1370" : W = (Cmp Eq W) %"v1366", #393216
    => br %"v1370" ? "L1359" : "L1361";
  @"L1359":
    %"v1372" = %"v0" +p #20;
    %"v1373" = %"v1372" +p #32;
    %"v1374" = %"v1373" +p #16;
    %"v1375" = %"v1374" +p #12;
    %"chk273" : A = (Renew 0 4 Read 1) %"chk111", %"v1375";
    %"v1376" : W = (RawLoad (LdNarrow Uw) 0) %"chk273";
    %"v1380" = %"v1373" +p #12;
    %"chk274" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1380";
    %"v1381" : W = (RawLoad (LdNarrow Uw) 0) %"chk274";
    %"v1383" : W = And %"v1381", #4194304;
    %"v1384" : W = Or %"v1376", %"v1383";
    %"chk275" : A = (Renew 0 4 Write 1) %"chk111", %"v1375";
    store Ww [%"chk275" + 0] <- %"v1384";
    %"v1390" : W = (RawLoad (LdNarrow Uw) 0) %"chk275";
    %"v1395" : W = (RawLoad (LdNarrow Uw) 0) %"chk274";
    %"v1397" : W = And %"v1395", #16777216;
    %"v1398" : W = Or %"v1390", %"v1397";
    store Ww [%"chk275" + 0] <- %"v1398";
    %"v1404" : W = (RawLoad (LdNarrow Uw) 0) %"chk275";
    %"v1409" : W = (RawLoad (LdNarrow Uw) 0) %"chk274";
    %"v1411" : W = And %"v1409", #33554432;
    %"v1412" : W = Or %"v1404", %"v1411";
    store Ww [%"chk275" + 0] <- %"v1412";
    %"v1415" = %"v1372" +p #192;
    %"v1416" = %"v1415" +p #16;
    %"chk282" : A = (Renew 0 4 Read 1) %"chk144", %"v1416";
    %"v1417" : W = (RawLoad (LdNarrow Uw) 0) %"chk282";
    %"v1421" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk282";
    %"v1423" : W = And %"v1421", #2097152;
    %"v1424" : W = Or %"v1417", %"v1423";
    store Ww [%"chk282" + 0] <- %"v1424";
    %"v1429" = %"v1416" +p #12;
    %"chk285" : A = (Renew 0 4 Read 1) %"chk159", %"v1429";
    %"v1430" : W = (RawLoad (LdNarrow Uw) 0) %"chk285";
    %"v1434" = %"v1415" +p #12;
    %"v1435" : W = (RawLoad (LdNarrow Uw) (-4)) %"chk282";
    %"v1437" : W = And %"v1435", #256;
    %"v1438" : W = Or %"v1430", %"v1437";
    store Ww [%"chk285" + 0] <- %"v1438"
    => goto "L1361";
  @"L1361":
    %"v1442" : W = Copy %"v815";
    %"v1444" : W = And %"v1442", #524288;
    %"v1445" : W = (Cmp Ne W) %"v1444", #0
    => br %"v1445" ? "L1439" : "L1441";
  @"L1439":
    %"v1447" = %"v0" +p #20;
    %"v1448" = %"v1447" +p #192;
    %"v1449" = %"v1448" +p #16;
    %"v1450" = %"v1449" +p #12;
    %"chk288" : A = (Renew 0 4 Read 1) %"chk159", %"v1450";
    %"v1451" : W = (RawLoad (LdNarrow Uw) 0) %"chk288";
    %"v1455" = %"v1448" +p #12;
    %"chk289" : A = (Renew 0 4 Read 1) %"chk262", %"v1455";
    %"v1456" : W = (RawLoad (LdNarrow Uw) 0) %"chk289";
    %"v1458" : W = And %"v1456", #2097152;
    %"v1459" : W = Or %"v1451", %"v1458";
    %"chk290" : A = (Renew 0 4 Write 1) %"chk159", %"v1450";
    store Ww [%"chk290" + 0] <- %"v1459"
    => goto "L1441";
  @"L1441":
    %"v1461" = %"v0" +p #20;
    %"v1463" = %"v1461" +p #16;
    %"v1464" = %"v1463" +p #8;
    %"chk291" : A = (Renew 0 4 Read 1) %"chk0", %"v1464";
    %"v1465" : W = (RawLoad (LdNarrow Uw) 0) %"chk291";
    %"v1467" : W = Or %"v1465", #67108864;
    %"chk292" : A = (Renew 0 4 Write 1) %"chk0", %"v1464";
    store Ww [%"chk292" + 0] <- %"v1467";
    %"v1470" = %"v1461" +p #96;
    %"v1471" = %"v1470" +p #16;
    %"chk293" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1471";
    %"v1472" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1476" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1478" : W = And %"v1476", #1;
    %"v1479" : W = Or %"v1472", %"v1478";
    store Ww [%"chk293" + 0] <- %"v1479";
    %"v1484" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1488" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1490" : W = And %"v1488", #2;
    %"v1491" : W = Or %"v1484", %"v1490";
    store Ww [%"chk293" + 0] <- %"v1491";
    %"v1496" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1500" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1502" : W = And %"v1500", #4;
    %"v1503" : W = Or %"v1496", %"v1502";
    store Ww [%"chk293" + 0] <- %"v1503";
    %"v1508" : W = (RawLoad (LdNarrow Uw) 0) %"chk293";
    %"v1512" : W = (RawLoad (LdNarrow Uw) (-16)) %"chk293";
    %"v1514" : W = And %"v1512", #16;
    %"v1515" : W = Or %"v1508", %"v1514";
    store Ww [%"chk293" + 0] <- %"v1515";
    %"v1520" = %"v0" +p #4;
    %"chk305" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v1520";
    %"v1521" : W = (RawLoad (LdNarrow Sw) 0) %"chk305";
    %"v1522" : W = (Cmp Sge W) %"v1521", #13
    => br %"v1522" ? "L1516" : "L791";
  @"L1516":
    call void $"zcpuid_count"(W #13, W #0, P %"v1523", P %"v1524", P %"v1525", P %"v1526");
    %"chk306" : A = (Check 0 4 Read 1) %"v1524";
    %"v1530" : W = (RawLoad (LdNarrow Uw) 0) %"chk306";
    %"v1531" : W = (Cmp Ne W) %"v1530", #0
    => br %"v1531" ? "L1527" : "L791";
  @"L1527":
    %"v1533" : W = (RawLoad (LdNarrow Uw) 0) %"chk306";
    %"v1537" : W = Add %"v1533", #88;
    %"v1538" : W = Add %"v1537", #64;
    %"v1539" : W = Sub %"v1538", #1;
    %"v1541" : W = And %"v1539", #4294967232;
    %"v1543" = %"v0" +p #352;
    %"v1545" : L = (Ext Uw) %"v1541";
    %"chk308" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v1543";
    store Wl [%"chk308" + 0] <- %"v1545";
    %"v1547" = %"v0" +p #360;
    %"chk309" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v1547";
    store Ww [%"chk309" + 0] <- %"v1541";
    %"v1549" : P = Copy $"_dl_x86_features_tlsdesc_state_size";
    %"chk310" : A = (Check 0 8 Write 1) %"v1549";
    store Wl [%"chk310" + 0] <- %"v1545";
    %"v1556" = %"v0" +p #20;
    %"v1557" = %"v1556" +p #96;
    %"chk311" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1557";
    %"v1558" : W = (RawLoad (LdNarrow Uw) 0) %"chk311";
    %"v1560" : W = And %"v1558", #2;
    %"v1561" : W = (Cmp Ne W) %"v1560", #0
    => br %"v1561" ? "L1552" : "L791";
  @"L1552":
    %"chk312" : A = (Check 0 4 Write 1) %"v1562";
    store Ww [%"chk312" + 0] <- #0;
    %"v1566" = %"v1562" +p #4;
    %"chk313" : A = (HalfCheck Upper 0 4 Write 1) %"chk312", %"v1566";
    store Ww [%"chk313" + 0] <- #160;
    %"v1567" = %"v1562" +p #8;
    %"chk314" : A = (HalfCheck Upper 0 4 Write 1) %"chk312", %"v1567";
    store Ww [%"chk314" + 0] <- #576;
    %"chk315" : A = (Check 0 4 Write 1) %"v1563";
    store Ww [%"chk315" + 0] <- #160;
    %"v1569" = %"v1563" +p #4;
    %"chk316" : A = (HalfCheck Upper 0 4 Write 1) %"chk315", %"v1569";
    store Ww [%"chk316" + 0] <- #256
    => goto "L1570";
  @"L1570" [%"pr.4" : W = phi("L1552" => #2, "L1572" => %"v1653")]:
    %"v1575" : W = (Cmp Ule W) %"pr.4", #19
    => br %"v1575" ? "L1571" : "L1573";
  @"L1571":
    %"v1597" : W = Shl #1, %"pr.4";
    %"v1598" : W = And %"v1597", #917742;
    %"v1599" : W = (Cmp Ne W) %"v1598", #0
    => br %"v1599" ? "L1576" : "L1577";
  @"L1576":
    call void $"zcpuid_count"(W #13, W %"pr.4", P %"v1523", P %"v1524", P %"v1525", P %"v1526");
    %"v1602" : L = (Ext Uw) %"pr.4";
    %"v1603" : L = Shl %"v1602", #2;
    %"v1604" = %"v1563" +p %"v1603";
    %"chk317" : A = (Check 0 4 Read 1) %"v1523";
    %"v1605" : W = (RawLoad (LdNarrow Uw) 0) %"chk317";
    %"chk318" : A = (Check 0 4 Write 1) %"v1604";
    store Ww [%"chk318" + 0] <- %"v1605"
    => goto "L1578";
  @"L1577":
    %"chk319" : A = (Check 0 4 Write 1) %"v1525";
    store Ww [%"chk319" + 0] <- #0;
    %"v1607" : L = (Ext Uw) %"pr.4";
    %"v1608" : L = Shl %"v1607", #2;
    %"v1609" = %"v1563" +p %"v1608";
    %"chk320" : A = (Check 0 4 Write 1) %"v1609";
    store Ww [%"chk320" + 0] <- #0
    => goto "L1578";
  @"L1578":
    %"v1614" : W = (Cmp Ugt W) %"pr.4", #2
    => br %"v1614" ? "L1610" : "L1572";
  @"L1610":
    %"v1616" : L = (Ext Uw) %"pr.4";
    %"v1617" : L = Shl %"v1616", #2;
    %"v1618" = %"v1562" +p %"v1617";
    %"v1620" : W = Sub %"pr.4", #1;
    %"v1621" : L = (Ext Uw) %"v1620";
    %"v1622" : L = Shl %"v1621", #2;
    %"v1623" = %"v1562" +p %"v1622";
    %"chk321" : A = (Check 0 4 Read 1) %"v1623";
    %"v1624" : W = (RawLoad (LdNarrow Uw) 0) %"chk321";
    %"v1629" = %"v1563" +p %"v1622";
    %"chk322" : A = (Check 0 4 Read 1) %"v1629";
    %"v1630" : W = (RawLoad (LdNarrow Uw) 0) %"chk322";
    %"v1631" : W = Add %"v1624", %"v1630";
    %"chk323" : A = (Check 0 4 Write 1) %"v1618";
    store Ww [%"chk323" + 0] <- %"v1631";
    %"chk324" : A = (Check 0 4 Read 1) %"v1525";
    %"v1635" : W = (RawLoad (LdNarrow Uw) 0) %"chk324";
    %"v1637" : W = And %"v1635", #2;
    %"v1638" : W = (Cmp Ne W) %"v1637", #0
    => br %"v1638" ? "L1632" : "L1572";
  @"L1632":
    %"v1647" : W = (RawLoad (LdNarrow Uw) 0) %"chk323";
    %"v1648" : W = Add %"v1647", #64;
    %"v1649" : W = Sub %"v1648", #1;
    %"v1651" : W = And %"v1649", #4294967232;
    store Ww [%"chk323" + 0] <- %"v1651"
    => goto "L1572";
  @"L1572":
    %"v1653" : W = Add %"pr.4", #1
    => goto poll "L1570";
  @"L1573":
    %"v1655" = %"v1562" +p #76;
    %"chk327" : A = (HalfCheck Upper 0 4 Read 1) %"chk312", %"v1655";
    %"v1656" : W = (RawLoad (LdNarrow Uw) 0) %"chk327";
    %"v1657" = %"v1563" +p #76;
    %"chk328" : A = (HalfCheck Upper 0 4 Read 1) %"chk315", %"v1657";
    %"v1658" : W = (RawLoad (LdNarrow Uw) 0) %"chk328";
    %"v1659" : W = Add %"v1656", %"v1658"
    => br %"v1659" ? "L1660" : "L791";
  @"L1660":
    %"v1668" : W = Add %"v1659", #88;
    %"v1669" : W = Add %"v1668", #64;
    %"v1670" : W = Sub %"v1669", #1;
    %"v1672" : W = And %"v1670", #4294967232;
    %"v1673" : P = Copy $"_dl_x86_features_tlsdesc_state_size";
    %"v1675" : L = (Ext Uw) %"v1672";
    %"chk329" : A = (Check 0 8 Write 1) %"v1673";
    store Wl [%"chk329" + 0] <- %"v1675";
    %"v1680" = %"v1562" +p #76;
    %"chk330" : A = (Renew 0 4 Read 1) %"chk327", %"v1680";
    %"v1681" : W = (RawLoad (LdNarrow Uw) 0) %"chk330";
    %"v1682" = %"v1562" +p #68;
    %"chk331" : A = (HalfCheck Upper 0 4 Read 1) %"chk312", %"v1682";
    %"v1683" : W = (RawLoad (LdNarrow Uw) 0) %"chk331";
    %"v1684" : W = Sub %"v1681", %"v1683";
    %"v1685" : W = Sub %"v1672", %"v1684";
    %"v1687" = %"v0" +p #352;
    %"v1689" : L = (Ext Uw) %"v1685";
    %"chk332" : A = (Renew 0 8 Write 1) %"chk308", %"v1687";
    store Wl [%"chk332" + 0] <- %"v1689";
    %"v1691" = %"v0" +p #20;
    %"v1692" = %"v1691" +p #96;
    %"v1693" = %"v1692" +p #16;
    %"chk333" : A = (Renew 0 4 Read 1) %"chk293", %"v1693";
    %"v1694" : W = (RawLoad (LdNarrow Uw) 0) %"chk333";
    %"v1696" : W = Or %"v1694", #2;
    store Ww [%"chk333" + 0] <- %"v1696"
    => goto "L791";
  @"L791":
    %"v1701" = %"v0" +p #20;
    %"v1702" = %"v1701" +p #32;
    %"v1703" = %"v1702" +p #8;
    %"chk335" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1703";
    %"v1704" : W = (RawLoad (LdNarrow Uw) 0) %"chk335";
    %"v1706" : W = And %"v1704", #16;
    %"v1707" : W = (Cmp Ne W) %"v1706", #0
    => br %"v1707" ? "L1697" : "L1699";
  @"L1697":
    %"v1709" = %"v0" +p #20;
    %"v1710" = %"v1709" +p #32;
    %"v1711" = %"v1710" +p #16;
    %"v1712" = %"v1711" +p #8;
    %"chk336" : A = (Renew 0 4 Read 1) %"chk84", %"v1712";
    %"v1713" : W = (RawLoad (LdNarrow Uw) 0) %"chk336";
    %"v1715" : W = Or %"v1713", #8;
    %"chk337" : A = (Renew 0 4 Write 1) %"chk84", %"v1712";
    store Ww [%"chk337" + 0] <- %"v1715"
    => goto "L1699";
  @"L1699":
    %"v1720" = %"v0" +p #20;
    %"v1721" = %"v1720" +p #224;
    %"v1722" = %"v1721" +p #4;
    %"chk338" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1722";
    %"v1723" : W = (RawLoad (LdNarrow Uw) 0) %"chk338";
    %"v1725" : W = And %"v1723", #1
    => br %"v1725" ? "L1716" : "iw_1.start";
  @"L1716":
    %"v1728" = %"v0" +p #20;
    %"v1729" = %"v1728" +p #224;
    %"v1730" = %"v1729" +p #16;
    %"v1731" = %"v1730" +p #4;
    %"chk339" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1731";
    %"v1732" : W = (RawLoad (LdNarrow Uw) 0) %"chk339";
    %"v1734" : W = Or %"v1732", #1;
    %"chk340" : A = (Renew 0 4 Write 1) %"chk339", %"v1731";
    store Ww [%"chk340" + 0] <- %"v1734";
    %"v1737" = %"v1728" +p #32;
    %"v1738" = %"v1737" +p #16;
    %"v1739" = %"v1738" +p #8;
    %"v1740" : W = (RawLoad (LdNarrow Uw) 16) %"chk335";
    %"v1744" = %"v1737" +p #8;
    %"v1745" : W = (RawLoad (LdNarrow Uw) 0) %"chk335";
    %"v1747" : W = And %"v1745", #8388608;
    %"v1748" : W = Or %"v1740", %"v1747";
    store Ww [%"chk335" + 16] <- %"v1748";
    %"v1754" : W = (RawLoad (LdNarrow Uw) 0) %"chk340";
    %"v1758" = %"v1729" +p #4;
    %"v1759" : W = (RawLoad (LdNarrow Uw) 0) %"chk338";
    %"v1761" : W = And %"v1759", #4;
    %"v1762" : W = Or %"v1754", %"v1761";
    store Ww [%"chk340" + 0] <- %"v1762"
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v5" : P = Copy $"_dl_hwcap2";
    %"chk347" : A = (Check 0 8 Read 1) %"iw_1.v5";
    %"iw_1.v6" : L = (RawLoad LdL 0) %"chk347";
    %"iw_1.v9" : L = And %"iw_1.v6", #2;
    %"iw_1.v10" : W = (Cmp Ne L) %"iw_1.v9", #0
    => br %"iw_1.v10" ? "iw_1.L2" : "iw_1.join";
  @"iw_1.L2":
    %"iw_1.v12" = %"v0" +p #20;
    %"iw_1.v13" = %"iw_1.v12" +p #32;
    %"iw_1.v14" = %"iw_1.v13" +p #16;
    %"iw_1.v15" = %"iw_1.v14" +p #4;
    %"chk348" : A = (Renew 0 4 Read 1) %"chk57", %"iw_1.v15";
    %"iw_1.v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk348";
    %"iw_1.v20" = %"iw_1.v13" +p #4;
    %"chk349" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_1.v20";
    %"iw_1.v21" : W = (RawLoad (LdNarrow Uw) 0) %"chk349";
    %"iw_1.v23" : W = And %"iw_1.v21", #1;
    %"iw_1.v24" : W = Or %"iw_1.v16", %"iw_1.v23";
    %"chk350" : A = (Renew 0 4 Write 1) %"chk57", %"iw_1.v15";
    store Ww [%"chk350" + 0] <- %"iw_1.v24"
    => goto "iw_1.join";
  @"iw_1.join":
    %"v1765" = %"v0" +p #344;
    call %"v1767" : W = $"glibc_libc_start#get_isa_level"(P %"v0");
    %"chk351" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v1765";
    store Ww [%"chk351" + 0] <- %"v1767"
    => ret void
} }.

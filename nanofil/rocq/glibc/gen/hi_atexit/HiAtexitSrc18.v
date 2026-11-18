(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import HiAtexitSrcFiles.
Import HiAtexitSrcFiles.
Module HiAtexitSrc18.

Module fn_glibc_libc_start_internal_signal_block_all.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_18, 79%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_18, 82%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "oset"); ((TAtom "v3"), "oset")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "oset", 0)); ((TAtom "v2"), ((TAtom "v2"), "&sigall_set", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn_glibc_libc_start_internal_signal_block_all.

Module fn___libc_setup_tls.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_51, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_51, 35%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "addr"); ((TAtom "iw_1.v10"), "_thrdescr"); ((TAtom "iw_1.v11"), "_head"); ((TAtom "iw_1.v13"), "_thrdescr"); ((TAtom "iw_1.v14"), "_thrdescr"); ((TAtom "iw_1.v6"), "addr"); ((TAtom "iw_1.v8"), "_thrdescr"); ((TAtom "iw_1.v9"), "_head"); ((TAtom "v1"), "pd"); ((TAtom "v2"), "pd")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v1"), "pd", 0)); ((TAtom "chk1"), ((TAtom "v1"), "pd", 16)); ((TAtom "iw_1.v12"), ((TAtom "v1"), "pd", 16)); ((TAtom "v1"), ((TAtom "v1"), "pd", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "iw_1.v12")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (16)), "opaque")])].


End fn___libc_setup_tls.

Module fn___libc_early_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_52, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_52, 36%N)); ((TAtom "iw_1.L6"), (file_11, 33%N)); ((TAtom "iw_1.L7"), (file_11, 33%N)); ((TAtom "iw_1.L1"), (file_11, 37%N)); ((TAtom "iw_1.L2"), (file_11, 38%N)); ((TAtom "iw_1.L17"), (file_11, 41%N)); ((TAtom "iw_1.L3"), (file_11, 45%N)); ((TAtom "iw_1.L30"), (file_11, 49%N)); ((TAtom "iw_1.L32"), (file_11, 52%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v24"), "_dl_pagesize"); ((TAtom "iw_1.v26"), "pagesz"); ((TAtom "iw_1.v29"), "minstack"); ((TAtom "iw_1.v34"), "minstack"); ((TAtom "iw_1.v36"), "minstack"); ((TAtom "iw_1.v38"), "pagesz"); ((TAtom "iw_1.v41"), "pagesz"); ((TAtom "iw_1.v50"), "_dl_pagesize"); ((TAtom "v0"), "initial"); ((TAtom "v3"), "initial"); ((TAtom "v4"), "__libc_single_threaded"); ((TAtom "v7"), "initial"); ((TAtom "v8"), "__libc_single_threaded_internal"); ((TAtom "v9"), "initial")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v2"), "&__libc_single_threaded", 0)); ((TAtom "chk1"), ((TAtom "v6"), "&__libc_initial", 0)); ((TAtom "chk11"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "chk12"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "chk13"), ((TAtom "iw_1.v44"), "&__default_pthread_attr", 32)); ((TAtom "chk14"), ((TAtom "iw_1.v49"), "&_dl_pagesize", 0)); ((TAtom "chk15"), ((TAtom "iw_1.v47"), "&__default_pthread_attr", 16)); ((TAtom "chk2"), ((TAtom "v5"), "&__libc_single_threaded_internal", 0)); ((TAtom "chk3"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "chk4"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "chk5"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "chk6"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "chk7"), ((TAtom "iw_1.v23"), "&_dl_pagesize", 0)); ((TAtom "chk8"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "chk9"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "iw_1.v0"), ((TAtom "iw_1.v0"), "&limit", 0)); ((TAtom "iw_1.v23"), ((TAtom "iw_1.v23"), "&_dl_pagesize", 0)); ((TAtom "iw_1.v24"), ((TAtom "iw_1.v24"), "_dl_pagesize", 0)); ((TAtom "iw_1.v29"), ((TAtom "iw_1.v29"), "minstack", 0)); ((TAtom "iw_1.v44"), ((TAtom "iw_1.v44"), "&__default_pthread_attr", 0)); ((TAtom "iw_1.v45"), ((TAtom "iw_1.v44"), "&__default_pthread_attr", 32)); ((TAtom "iw_1.v47"), ((TAtom "iw_1.v47"), "&__default_pthread_attr", 0)); ((TAtom "iw_1.v48"), ((TAtom "iw_1.v47"), "&__default_pthread_attr", 16)); ((TAtom "iw_1.v49"), ((TAtom "iw_1.v49"), "&_dl_pagesize", 0)); ((TAtom "iw_1.v50"), ((TAtom "iw_1.v50"), "_dl_pagesize", 0)); ((TAtom "v0"), ((TAtom "v0"), "initial", 0)); ((TAtom "v2"), ((TAtom "v2"), "&__libc_single_threaded", 0)); ((TAtom "v3"), ((TAtom "v3"), "initial", 0)); ((TAtom "v4"), ((TAtom "v4"), "__libc_single_threaded", 0)); ((TAtom "v5"), ((TAtom "v5"), "&__libc_single_threaded_internal", 0)); ((TAtom "v6"), ((TAtom "v6"), "&__libc_initial", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L6"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L7"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L1"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L2"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L17"), [(TAtom "chk5"); (TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L3"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L30"), [(TAtom "chk8"); (TAtom "iw_1.v0"); (TAtom "iw_1.v24"); (TAtom "iw_1.v29"); (TAtom "v3")]); ((TAtom "iw_1.L32"), [(TAtom "chk8"); (TAtom "iw_1.v0"); (TAtom "iw_1.v24"); (TAtom "v3")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L6"), [(TAtom "iw_1.v0"); (TAtom "iw_1.v11"); (TAtom "v3")]); ((TAtom "iw_1.L7"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L1"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L2"), [(TAtom "chk5"); (TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L17"), [(TAtom "iw_1.v0"); (TAtom "v3")]); ((TAtom "iw_1.L3"), [(TAtom "chk8"); (TAtom "iw_1.v0"); (TAtom "iw_1.v24"); (TAtom "iw_1.v29"); (TAtom "v3")]); ((TAtom "iw_1.L30"), [(TAtom "chk8"); (TAtom "iw_1.v0"); (TAtom "iw_1.v24"); (TAtom "v3")]); ((TAtom "iw_1.L32"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(5%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 1), false, true, (Some (TAtom "v2")), (Some (0)), "opaque"); (9%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 1), false, true, (Some (TAtom "v6")), (Some (0)), "opaque"); (11%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 1), false, true, (Some (TAtom "v5")), (Some (0)), "opaque")]); ((TAtom "iw_1.L6"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur")]); ((TAtom "iw_1.L7"), []); ((TAtom "iw_1.L1"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur")]); ((TAtom "iw_1.L2"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur")]); ((TAtom "iw_1.L17"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur")]); ((TAtom "iw_1.L3"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v23")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v23")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur")]); ((TAtom "iw_1.L30"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur")]); ((TAtom "iw_1.L32"), [(0%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur"); (6%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur"); (10%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v0")), (Some (0)), "limit.rlim_cur"); (12%N, (TApp "tmp" [(TAtom "iw_1.v45")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v44")), (Some (32)), "__default_pthread_attr.internal.stacksize"); (17%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v49")), (Some (0)), "opaque"); (19%N, (TApp "tmp" [(TAtom "iw_1.v48")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v47")), (Some (16)), "__default_pthread_attr.internal.guardsize")])].


End fn___libc_early_init.

Module fn___tls_init_tp.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_7, 43%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_7, 46%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v1"), "pd"); ((TAtom "v10"), "pd"); ((TAtom "v13"), "pd"); ((TAtom "v16"), "pd"); ((TAtom "v18"), "pd"); ((TAtom "v2"), "pd"); ((TAtom "v20"), "pd"); ((TAtom "v23"), "__nptl_initial_report_events"); ((TAtom "v24"), "pd"); ((TAtom "v26"), "pd"); ((TAtom "v28"), "pd"); ((TAtom "v30"), "pd"); ((TAtom "v32"), "pd"); ((TAtom "v36"), "pd"); ((TAtom "v39"), "__libc_stack_end"); ((TAtom "v5"), "pd"); ((TAtom "v8"), "pd")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v1"), "pd", 720)); ((TAtom "chk1"), ((TAtom "v1"), "pd", 728)); ((TAtom "chk10"), ((TAtom "v1"), "pd", 760)); ((TAtom "chk11"), ((TAtom "v38"), "&__libc_stack_end", 0)); ((TAtom "chk12"), ((TAtom "v1"), "pd", 1720)); ((TAtom "chk2"), ((TAtom "v1"), "pd", 736)); ((TAtom "chk3"), ((TAtom "v1"), "pd", 1312)); ((TAtom "chk4"), ((TAtom "v1"), "pd", 1572)); ((TAtom "chk5"), ((TAtom "v1"), "pd", 1592)); ((TAtom "chk6"), ((TAtom "v22"), "&__nptl_initial_report_events", 0)); ((TAtom "chk7"), ((TAtom "v1"), "pd", 1569)); ((TAtom "chk8"), ((TAtom "v1"), "pd", 744)); ((TAtom "chk9"), ((TAtom "v1"), "pd", 752)); ((TAtom "v1"), ((TAtom "v1"), "pd", 0)); ((TAtom "v11"), ((TAtom "v1"), "pd", 1312)); ((TAtom "v14"), ((TAtom "v1"), "pd", 800)); ((TAtom "v17"), ((TAtom "v1"), "pd", 1572)); ((TAtom "v19"), ((TAtom "v1"), "pd", 1592)); ((TAtom "v21"), ((TAtom "v1"), "pd", 1569)); ((TAtom "v22"), ((TAtom "v22"), "&__nptl_initial_report_events", 0)); ((TAtom "v23"), ((TAtom "v23"), "__nptl_initial_report_events", 0)); ((TAtom "v25"), ((TAtom "v1"), "pd", 744)); ((TAtom "v27"), ((TAtom "v1"), "pd", 752)); ((TAtom "v3"), ((TAtom "v1"), "pd", 720)); ((TAtom "v34"), ((TAtom "v1"), "pd", 760)); ((TAtom "v37"), ((TAtom "v1"), "pd", 1720)); ((TAtom "v38"), ((TAtom "v38"), "&__libc_stack_end", 0)); ((TAtom "v39"), ((TAtom "v39"), "__libc_stack_end", 0)); ((TAtom "v6"), ((TAtom "v1"), "pd", 728)); ((TAtom "v9"), ((TAtom "v1"), "pd", 736))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 4), false, true, (Some (TAtom "v1")), (Some (720)), "pd->tid"); (8%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (728)), "pd->zthread"); (11%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), false, true, (Some (TAtom "v1")), (Some (736)), "pd->dead"); (15%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (1312)), "pd->specific"); (18%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 4), false, true, (Some (TAtom "v1")), (Some (1572)), "pd->stack_mode"); (21%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 4), false, true, (Some (TAtom "v1")), (Some (1592)), "pd->joinstate"); (25%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 1), true, false, (Some (TAtom "v22")), (Some (0)), "opaque"); (27%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 1), false, true, (Some (TAtom "v1")), (Some (1569)), "pd->report_events"); (31%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (744)), "pd->robust_prev"); (33%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (752)), "pd->robust_head.list"); (36%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (760)), "pd->robust_head.futex_offset"); (40%N, (TApp "tmp" [(TAtom "v38")]), (0), (Some 8), true, false, (Some (TAtom "v38")), (Some (0)), "opaque"); (43%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (1720)), "pd->stackblock_size")])].


End fn___tls_init_tp.

Module fn___GI___ctype_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_37, 35%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_37, 38%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v11"), "__libc_tsd_CTYPE_B"); ((TAtom "v14"), "__libc_tsd_LOCALE"); ((TAtom "v2"), "__libc_tsd_LOCALE"); ((TAtom "v23"), "__libc_tsd_CTYPE_TOUPPER"); ((TAtom "v26"), "__libc_tsd_LOCALE"); ((TAtom "v35"), "__libc_tsd_CTYPE_TOLOWER")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v1"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk1"), ((TAtom "v2"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk10"), ((TAtom "v28"), "v28", 80)); ((TAtom "chk11"), ((TAtom "v24"), "&__libc_tsd_CTYPE_TOLOWER", 0)); ((TAtom "chk2"), ((TAtom "v4"), "v4", 56)); ((TAtom "chk3"), ((TAtom "v0"), "&__libc_tsd_CTYPE_B", 0)); ((TAtom "chk4"), ((TAtom "v13"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk5"), ((TAtom "v14"), "__libc_tsd_LOCALE", 0)); ((TAtom "chk6"), ((TAtom "v16"), "v16", 64)); ((TAtom "chk7"), ((TAtom "v12"), "&__libc_tsd_CTYPE_TOUPPER", 0)); ((TAtom "chk8"), ((TAtom "v25"), "&__libc_tsd_LOCALE", 0)); ((TAtom "chk9"), ((TAtom "v26"), "__libc_tsd_LOCALE", 0)); ((TAtom "v0"), ((TAtom "v0"), "&__libc_tsd_CTYPE_B", 0)); ((TAtom "v1"), ((TAtom "v1"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v11"), ((TAtom "v11"), "__libc_tsd_CTYPE_B", 0)); ((TAtom "v12"), ((TAtom "v12"), "&__libc_tsd_CTYPE_TOUPPER", 0)); ((TAtom "v13"), ((TAtom "v13"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v14"), ((TAtom "v14"), "__libc_tsd_LOCALE", 0)); ((TAtom "v17"), ((TAtom "v16"), "v16", 56)); ((TAtom "v2"), ((TAtom "v2"), "__libc_tsd_LOCALE", 0)); ((TAtom "v21"), ((TAtom "v16"), "v16", 64)); ((TAtom "v23"), ((TAtom "v23"), "__libc_tsd_CTYPE_TOUPPER", 0)); ((TAtom "v24"), ((TAtom "v24"), "&__libc_tsd_CTYPE_TOLOWER", 0)); ((TAtom "v25"), ((TAtom "v25"), "&__libc_tsd_LOCALE", 0)); ((TAtom "v26"), ((TAtom "v26"), "__libc_tsd_LOCALE", 0)); ((TAtom "v29"), ((TAtom "v28"), "v28", 56)); ((TAtom "v33"), ((TAtom "v28"), "v28", 80)); ((TAtom "v35"), ((TAtom "v35"), "__libc_tsd_CTYPE_TOLOWER", 0)); ((TAtom "v5"), ((TAtom "v4"), "v4", 56))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), true, false, (Some (TAtom "v1")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (8%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)), "opaque"); (11%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)), "opaque"); (15%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v13")), (Some (0)), "opaque"); (17%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 8), true, false, (Some (TAtom "v14")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (21%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (64)), "opaque"); (24%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), false, true, (Some (TAtom "v12")), (Some (0)), "opaque"); (28%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v25")), (Some (0)), "opaque"); (30%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), true, false, (Some (TAtom "v26")), (Some (0)), "__libc_tsd_LOCALE->__locales"); (34%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v28")), (Some (80)), "opaque"); (37%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), false, true, (Some (TAtom "v24")), (Some (0)), "opaque")])].


End fn___GI___ctype_init.

Module fn___GI___nptl_deallocate_tsd.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_58, 21%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_58, 24%N)); ((TAtom "L10"), (file_58, 30%N)); ((TAtom "L17"), (file_58, 36%N)); ((TAtom "L18"), (file_58, 45%N)); ((TAtom "L42"), (file_58, 49%N)); ((TAtom "L43"), (file_58, 54%N)); ((TAtom "L55"), (file_58, 59%N)); ((TAtom "L81"), (file_58, 67%N)); ((TAtom "L82"), (file_58, 67%N)); ((TAtom "L67"), (file_58, 73%N)); ((TAtom "L44"), (file_58, 51%N)); ((TAtom "L35"), (file_58, 78%N)); ((TAtom "L36"), (file_58, 36%N)); ((TAtom "L20"), (file_58, 81%N)); ((TAtom "L11"), (file_58, 34%N)); ((TAtom "L12"), (file_58, 89%N)); ((TAtom "L130"), (file_58, 31%N)); ((TAtom "L131"), (file_58, 98%N)); ((TAtom "L147"), (file_58, 103%N)); ((TAtom "L132"), (file_58, 94%N)); ((TAtom "L133"), (file_58, 108%N)); ((TAtom "L4"), (file_58, 21%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "round"); ((TAtom "pr.2"), "cnt"); ((TAtom "pr.3"), "cnt"); ((TAtom "pr.4"), "idx"); ((TAtom "pr.5"), "idx"); ((TAtom "pr.6"), "idx"); ((TAtom "pr.7"), "inner"); ((TAtom "v1"), "self"); ((TAtom "v100"), "data"); ((TAtom "v101"), "inner"); ((TAtom "v102"), "inner"); ((TAtom "v103"), "idx"); ((TAtom "v104"), "idx"); ((TAtom "v105"), "idx"); ((TAtom "v110"), "idx"); ((TAtom "v111"), "cnt"); ((TAtom "v112"), "cnt"); ((TAtom "v116"), "self"); ((TAtom "v122"), "round"); ((TAtom "v123"), "round"); ((TAtom "v134"), "cnt"); ((TAtom "v14"), "self"); ((TAtom "v141"), "self"); ((TAtom "v143"), "cnt"); ((TAtom "v146"), "level2"); ((TAtom "v150"), "level2"); ((TAtom "v154"), "level2"); ((TAtom "v155"), "self"); ((TAtom "v157"), "cnt"); ((TAtom "v160"), "cnt"); ((TAtom "v161"), "cnt"); ((TAtom "v162"), "self"); ((TAtom "v21"), "cnt"); ((TAtom "v28"), "self"); ((TAtom "v30"), "cnt"); ((TAtom "v33"), "level2"); ((TAtom "v37"), "level2"); ((TAtom "v46"), "inner"); ((TAtom "v49"), "level2"); ((TAtom "v5"), "self"); ((TAtom "v50"), "inner"); ((TAtom "v54"), "data"); ((TAtom "v58"), "data"); ((TAtom "v62"), "level2"); ((TAtom "v63"), "inner"); ((TAtom "v70"), "level2"); ((TAtom "v71"), "inner"); ((TAtom "v76"), "idx"); ((TAtom "v84"), "idx"); ((TAtom "v95"), "idx")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v1"), "self", 1568)); ((TAtom "chk1"), ((TAtom "v1"), "self", 1568)); ((TAtom "chk10"), ((TAtom "v1"), "self", 1568)); ((TAtom "chk11"), ((TAtom "v145"), "v145", 0)); ((TAtom "chk12"), ((TAtom "v159"), "v159", 0)); ((TAtom "chk13"), ((TAtom "v1"), "self", 1568)); ((TAtom "chk2"), ((TAtom "v32"), "v32", 0)); ((TAtom "chk3"), ((TAtom "v52"), "v52", 8)); ((TAtom "chk4"), ((TAtom "v52"), "v52", 8)); ((TAtom "chk5"), ((TAtom "v52"), "v52", 0)); ((TAtom "chk6"), ((TAtom "v78"), "v78", 0)); ((TAtom "chk7"), ((TAtom "v86"), "v86", 8)); ((TAtom "chk8"), ((TAtom "v97"), "v97", 8)); ((TAtom "pr.1"), ((TAtom "pr.1"), "round", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "cnt", 0)); ((TAtom "pr.3"), ((TAtom "pr.3"), "cnt", 0)); ((TAtom "pr.4"), ((TAtom "pr.4"), "idx", 0)); ((TAtom "pr.5"), ((TAtom "pr.5"), "idx", 0)); ((TAtom "pr.6"), ((TAtom "pr.6"), "idx", 0)); ((TAtom "pr.7"), ((TAtom "pr.7"), "inner", 0)); ((TAtom "v1"), ((TAtom "v1"), "self", 0)); ((TAtom "v102"), ((TAtom "v102"), "inner", 0)); ((TAtom "v104"), ((TAtom "v104"), "idx", 0)); ((TAtom "v110"), ((TAtom "v110"), "idx", 0)); ((TAtom "v112"), ((TAtom "v112"), "cnt", 0)); ((TAtom "v117"), ((TAtom "v1"), "self", 1568)); ((TAtom "v123"), ((TAtom "v123"), "round", 0)); ((TAtom "v128"), ((TAtom "v127"), "v127", 800)); ((TAtom "v142"), ((TAtom "v1"), "self", 1312)); ((TAtom "v146"), ((TAtom "v146"), "level2", 0)); ((TAtom "v15"), ((TAtom "v1"), "self", 1568)); ((TAtom "v156"), ((TAtom "v1"), "self", 1312)); ((TAtom "v161"), ((TAtom "v161"), "cnt", 0)); ((TAtom "v163"), ((TAtom "v1"), "self", 1568)); ((TAtom "v29"), ((TAtom "v1"), "self", 1312)); ((TAtom "v33"), ((TAtom "v33"), "level2", 0)); ((TAtom "v53"), ((TAtom "v52"), "v52", 8)); ((TAtom "v54"), ((TAtom "v54"), "data", 0)); ((TAtom "v6"), ((TAtom "v1"), "self", 1568)); ((TAtom "v66"), ((TAtom "v52"), "v52", 8)); ((TAtom "v75"), ((TAtom "v75"), "&__pthread_keys", 0)); ((TAtom "v83"), ((TAtom "v83"), "&__pthread_keys", 0)); ((TAtom "v87"), ((TAtom "v86"), "v86", 8)); ((TAtom "v94"), ((TAtom "v94"), "&__pthread_keys", 0)); ((TAtom "v98"), ((TAtom "v97"), "v97", 8))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L10"); (TAtom "L130"); (TAtom "L17"); (TAtom "L42")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v1")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v1")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v1")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39")]); ((TAtom "L55"), [(TAtom "chk0"); (TAtom "chk3"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v52"); (TAtom "v54")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v54"); (TAtom "v77")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v54"); (TAtom "v77")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v54"); (TAtom "v77")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v1")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v1")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v1")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v1")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v1")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v1")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v1")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v1"); (TAtom "v144"); (TAtom "v146")]); ((TAtom "L132"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v1")]); ((TAtom "L133"), [(TAtom "chk0"); (TAtom "v1")]); ((TAtom "L4"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v1")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v1")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v1")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk3"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v52"); (TAtom "v54")]); ((TAtom "L55"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v54"); (TAtom "v77")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v54"); (TAtom "v77"); (TAtom "v91")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39"); (TAtom "v54"); (TAtom "v77")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "v1"); (TAtom "v33"); (TAtom "v39")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v1"); (TAtom "v102"); (TAtom "v104"); (TAtom "v33"); (TAtom "v39")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v1"); (TAtom "v110")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.5"); (TAtom "v1"); (TAtom "v112")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v1")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "v1"); (TAtom "v123")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v1")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v1")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v1"); (TAtom "v144"); (TAtom "v146")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v1")]); ((TAtom "L132"), [(TAtom "chk0"); (TAtom "v1"); (TAtom "v161")]); ((TAtom "L133"), []); ((TAtom "L4"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 1), true, false, (Some (TAtom "v1")), (Some (1568)), "self->specific_used")]); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 1), false, true, (Some (TAtom "v1")), (Some (1568)), "self->specific_used")]); ((TAtom "L17"), []); ((TAtom "L18"), [(4%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "v1")), None, "opaque")]); ((TAtom "L42"), []); ((TAtom "L43"), [(4%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v33")), None, "opaque")]); ((TAtom "L55"), [(2%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), false, true, (Some (TAtom "v33")), None, "opaque"); (4%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 8), true, false, (Some (TAtom "v33")), None, "opaque"); (9%N, (TApp "tmp" [(TAtom "v78")]), (0), (Some 8), true, false, (Some (TAtom "v75")), None, "opaque")]); ((TAtom "L81"), [(4%N, (TApp "tmp" [(TAtom "v87")]), (0), (Some 8), true, false, (Some (TAtom "v83")), None, "opaque")]); ((TAtom "L82"), []); ((TAtom "L67"), [(4%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 8), true, false, (Some (TAtom "v94")), None, "opaque")]); ((TAtom "L44"), []); ((TAtom "L35"), []); ((TAtom "L36"), []); ((TAtom "L20"), [(2%N, (TApp "tmp" [(TAtom "v117")]), (0), (Some 1), true, false, (Some (TAtom "v1")), (Some (1568)), "self->specific_used")]); ((TAtom "L11"), []); ((TAtom "L12"), []); ((TAtom "L130"), []); ((TAtom "L131"), [(4%N, (TApp "tmp" [(TAtom "v145")]), (0), (Some 8), true, false, (Some (TAtom "v1")), None, "opaque")]); ((TAtom "L147"), [(4%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), false, true, (Some (TAtom "v1")), None, "opaque")]); ((TAtom "L132"), []); ((TAtom "L133"), [(2%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 1), false, true, (Some (TAtom "v1")), (Some (1568)), "self->specific_used")]); ((TAtom "L4"), [])].


End fn___GI___nptl_deallocate_tsd.

Module fn_glibc_pthread_mutex_conf__dl_tunable_set_mutex_spin_count.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_59, 35%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_59, 38%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "valp"); ((TAtom "v3"), "valp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "valp", 0)); ((TAtom "chk1"), ((TAtom "v2"), "&__mutex_aconf", 0)); ((TAtom "v0"), ((TAtom "v0"), "valp", 0)); ((TAtom "v2"), ((TAtom "v2"), "&__mutex_aconf", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (4%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), false, true, (Some (TAtom "v2")), (Some (0)), "__mutex_aconf.spin_count")])].


End fn_glibc_pthread_mutex_conf__dl_tunable_set_mutex_spin_count.

Module fn___pthread_tunables_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_59, 51%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_59, 54%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v2"), "id"); ((TAtom "v4"), "ret")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v1"), "&ret", 0)); ((TAtom "v1"), ((TAtom "v1"), "&ret", 0)); ((TAtom "v4"), ((TAtom "v4"), "ret", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 4), true, false, (Some (TAtom "v1")), (Some (0)), "opaque")])].


End fn___pthread_tunables_init.

Module fn___getrandom_early_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_16, 47%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_16, 47%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "initial")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "initial", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___getrandom_early_init.

Module fn_glibc_dl_tunables_do_tunable_update_val.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_40, 69%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_40, 76%N)); ((TAtom "L11"), (file_40, 77%N)); ((TAtom "L13"), (file_40, 79%N)); ((TAtom "L23"), (file_40, 82%N)); ((TAtom "L34"), (file_40, 86%N)); ((TAtom "L38"), (file_40, 89%N)); ((TAtom "L41"), (file_40, 92%N)); ((TAtom "L44"), (file_40, 95%N)); ((TAtom "L47"), (file_40, 79%N)); ((TAtom "L49"), (file_40, 79%N)); ((TAtom "L51"), (file_40, 79%N)); ((TAtom "L22"), (file_40, 74%N)); ((TAtom "iw_1.L14"), (file_31, 66%N)); ((TAtom "iw_1.L16"), (file_31, 66%N)); ((TAtom "iw_1.L18"), (file_31, 66%N)); ((TAtom "iw_1.L20"), (file_31, 66%N)); ((TAtom "iw_1.L4"), (file_31, 77%N)); ((TAtom "iw_1.join"), (file_40, 100%N)); ((TAtom "L60"), (file_40, 100%N)); ((TAtom "L61"), (file_40, 100%N)); ((TAtom "L62"), (file_40, 100%N)); ((TAtom "L74"), (file_40, 101%N)); ((TAtom "L75"), (file_40, 101%N)); ((TAtom "L76"), (file_40, 101%N)); ((TAtom "iw_2.L6"), (file_32, 142%N)); ((TAtom "iw_2.L7"), (file_32, 144%N)); ((TAtom "iw_2.join"), (file_40, 104%N)); ((TAtom "L88"), (file_40, 105%N)); ((TAtom "L90"), (file_40, 74%N)); ((TAtom "iw_3.L6"), (file_32, 151%N)); ((TAtom "iw_3.L7"), (file_32, 153%N)); ((TAtom "iw_3.join"), (file_40, 107%N)); ((TAtom "L103"), (file_40, 108%N)); ((TAtom "L105"), (file_40, 74%N)); ((TAtom "iw_4.L6"), (file_32, 151%N)); ((TAtom "iw_4.L7"), (file_32, 153%N)); ((TAtom "iw_4.join"), (file_40, 111%N)); ((TAtom "L118"), (file_40, 113%N)); ((TAtom "L120"), (file_40, 74%N)); ((TAtom "iw_5.L6"), (file_32, 142%N)); ((TAtom "iw_5.L7"), (file_32, 144%N)); ((TAtom "iw_5.join"), (file_40, 118%N)); ((TAtom "iw_6.start"), (file_32, 141%N)); ((TAtom "iw_6.L6"), (file_32, 142%N)); ((TAtom "iw_6.L7"), (file_32, 144%N)); ((TAtom "L143"), (file_40, 118%N)); ((TAtom "L134"), (file_40, 120%N)); ((TAtom "L136"), (file_40, 122%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "t"); ((TAtom "iw_1.v2"), "t"); ((TAtom "iw_2.v0"), "lhs"); ((TAtom "iw_2.v10"), "lhs"); ((TAtom "iw_2.v11"), "rhs"); ((TAtom "iw_2.v15"), "lhs"); ((TAtom "iw_2.v16"), "rhs"); ((TAtom "iw_2.v2"), "rhs"); ((TAtom "iw_2.v4"), "unsigned_cmp"); ((TAtom "iw_2.v9"), "unsigned_cmp"); ((TAtom "iw_3.v0"), "lhs"); ((TAtom "iw_3.v10"), "lhs"); ((TAtom "iw_3.v11"), "rhs"); ((TAtom "iw_3.v15"), "lhs"); ((TAtom "iw_3.v16"), "rhs"); ((TAtom "iw_3.v2"), "rhs"); ((TAtom "iw_3.v4"), "unsigned_cmp"); ((TAtom "iw_3.v9"), "unsigned_cmp"); ((TAtom "iw_4.v0"), "lhs"); ((TAtom "iw_4.v10"), "lhs"); ((TAtom "iw_4.v11"), "rhs"); ((TAtom "iw_4.v15"), "lhs"); ((TAtom "iw_4.v16"), "rhs"); ((TAtom "iw_4.v2"), "rhs"); ((TAtom "iw_4.v4"), "unsigned_cmp"); ((TAtom "iw_4.v9"), "unsigned_cmp"); ((TAtom "iw_5.v0"), "lhs"); ((TAtom "iw_5.v10"), "lhs"); ((TAtom "iw_5.v11"), "rhs"); ((TAtom "iw_5.v15"), "lhs"); ((TAtom "iw_5.v16"), "rhs"); ((TAtom "iw_5.v2"), "rhs"); ((TAtom "iw_5.v4"), "unsigned_cmp"); ((TAtom "iw_5.v9"), "unsigned_cmp"); ((TAtom "iw_6.v0"), "lhs"); ((TAtom "iw_6.v10"), "lhs"); ((TAtom "iw_6.v11"), "rhs"); ((TAtom "iw_6.v15"), "lhs"); ((TAtom "iw_6.v16"), "rhs"); ((TAtom "iw_6.v2"), "rhs"); ((TAtom "iw_6.v4"), "unsigned_cmp"); ((TAtom "iw_6.v9"), "unsigned_cmp"); ((TAtom "pr.1"), "val"); ((TAtom "pr.2"), "min"); ((TAtom "pr.3"), "min"); ((TAtom "pr.4"), "max"); ((TAtom "pr.5"), "max"); ((TAtom "v0"), "cur"); ((TAtom "v102"), "min"); ((TAtom "v106"), "max"); ((TAtom "v107"), "cur"); ((TAtom "v111"), "unsigned_cmp"); ((TAtom "v114"), "cur"); ((TAtom "v117"), "max"); ((TAtom "v121"), "min"); ((TAtom "v122"), "max"); ((TAtom "v123"), "unsigned_cmp"); ((TAtom "v126"), "cur"); ((TAtom "v129"), "min"); ((TAtom "v130"), "cur"); ((TAtom "v133"), "max"); ((TAtom "v137"), "val"); ((TAtom "v138"), "min"); ((TAtom "v139"), "unsigned_cmp"); ((TAtom "v14"), "cur"); ((TAtom "v144"), "max"); ((TAtom "v145"), "val"); ((TAtom "v146"), "unsigned_cmp"); ((TAtom "v152"), "cur"); ((TAtom "v154"), "val"); ((TAtom "v155"), "cur"); ((TAtom "v158"), "min"); ((TAtom "v159"), "cur"); ((TAtom "v162"), "max"); ((TAtom "v163"), "cur"); ((TAtom "v18"), "cur"); ((TAtom "v2"), "valp"); ((TAtom "v24"), "cur"); ((TAtom "v26"), "valp"); ((TAtom "v31"), "cur"); ((TAtom "v35"), "valp"); ((TAtom "v37"), "val"); ((TAtom "v39"), "valp"); ((TAtom "v4"), "minp"); ((TAtom "v40"), "val"); ((TAtom "v42"), "valp"); ((TAtom "v43"), "val"); ((TAtom "v55"), "cur"); ((TAtom "v59"), "unsigned_cmp"); ((TAtom "v6"), "maxp"); ((TAtom "v63"), "minp"); ((TAtom "v67"), "minp"); ((TAtom "v69"), "cur"); ((TAtom "v73"), "min"); ((TAtom "v77"), "maxp"); ((TAtom "v81"), "maxp"); ((TAtom "v83"), "cur"); ((TAtom "v87"), "max"); ((TAtom "v91"), "min"); ((TAtom "v92"), "cur"); ((TAtom "v96"), "unsigned_cmp"); ((TAtom "v99"), "cur")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "cur", 105)); ((TAtom "chk1"), ((TAtom "v0"), "cur", 48)); ((TAtom "chk10"), ((TAtom "v0"), "cur", 48)); ((TAtom "chk11"), ((TAtom "v4"), "minp", 0)); ((TAtom "chk12"), ((TAtom "v0"), "cur", 56)); ((TAtom "chk13"), ((TAtom "v6"), "maxp", 0)); ((TAtom "chk14"), ((TAtom "v0"), "cur", 64)); ((TAtom "chk15"), ((TAtom "v0"), "cur", 56)); ((TAtom "chk17"), ((TAtom "v0"), "cur", 64)); ((TAtom "chk2"), ((TAtom "v2"), "valp", 0)); ((TAtom "chk21"), ((TAtom "v0"), "cur", 88)); ((TAtom "chk24"), ((TAtom "v0"), "cur", 104)); ((TAtom "chk3"), ((TAtom "v0"), "cur", 88)); ((TAtom "chk4"), ((TAtom "v2"), "valp", 8)); ((TAtom "chk5"), ((TAtom "v0"), "cur", 96)); ((TAtom "chk6"), ((TAtom "v0"), "cur", 104)); ((TAtom "chk7"), ((TAtom "v2"), "valp", 0)); ((TAtom "chk8"), ((TAtom "v2"), "valp", 0)); ((TAtom "chk9"), ((TAtom "v2"), "valp", 0)); ((TAtom "pr.1"), ((TAtom "pr.1"), "val", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "min", 0)); ((TAtom "pr.3"), ((TAtom "pr.3"), "min", 0)); ((TAtom "pr.4"), ((TAtom "pr.4"), "max", 0)); ((TAtom "pr.5"), ((TAtom "pr.5"), "max", 0)); ((TAtom "v0"), ((TAtom "v0"), "cur", 0)); ((TAtom "v100"), ((TAtom "v0"), "cur", 48)); ((TAtom "v101"), ((TAtom "v0"), "cur", 56)); ((TAtom "v102"), ((TAtom "v102"), "min", 0)); ((TAtom "v108"), ((TAtom "v0"), "cur", 48)); ((TAtom "v109"), ((TAtom "v0"), "cur", 64)); ((TAtom "v115"), ((TAtom "v0"), "cur", 48)); ((TAtom "v116"), ((TAtom "v0"), "cur", 64)); ((TAtom "v117"), ((TAtom "v117"), "max", 0)); ((TAtom "v127"), ((TAtom "v0"), "cur", 48)); ((TAtom "v128"), ((TAtom "v0"), "cur", 56)); ((TAtom "v129"), ((TAtom "v129"), "min", 0)); ((TAtom "v132"), ((TAtom "v0"), "cur", 64)); ((TAtom "v133"), ((TAtom "v133"), "max", 0)); ((TAtom "v15"), ((TAtom "v0"), "cur", 105)); ((TAtom "v153"), ((TAtom "v0"), "cur", 88)); ((TAtom "v156"), ((TAtom "v0"), "cur", 48)); ((TAtom "v157"), ((TAtom "v0"), "cur", 56)); ((TAtom "v161"), ((TAtom "v0"), "cur", 64)); ((TAtom "v164"), ((TAtom "v0"), "cur", 104)); ((TAtom "v19"), ((TAtom "v0"), "cur", 48)); ((TAtom "v2"), ((TAtom "v2"), "valp", 0)); ((TAtom "v25"), ((TAtom "v0"), "cur", 88)); ((TAtom "v28"), ((TAtom "v2"), "valp", 8)); ((TAtom "v29"), ((TAtom "v0"), "cur", 96)); ((TAtom "v32"), ((TAtom "v0"), "cur", 104)); ((TAtom "v37"), ((TAtom "v37"), "val", 0)); ((TAtom "v4"), ((TAtom "v4"), "minp", 0)); ((TAtom "v40"), ((TAtom "v40"), "val", 0)); ((TAtom "v43"), ((TAtom "v43"), "val", 0)); ((TAtom "v56"), ((TAtom "v0"), "cur", 48)); ((TAtom "v6"), ((TAtom "v6"), "maxp", 0)); ((TAtom "v70"), ((TAtom "v0"), "cur", 48)); ((TAtom "v71"), ((TAtom "v0"), "cur", 56)); ((TAtom "v73"), ((TAtom "v73"), "min", 0)); ((TAtom "v84"), ((TAtom "v0"), "cur", 48)); ((TAtom "v85"), ((TAtom "v0"), "cur", 64)); ((TAtom "v87"), ((TAtom "v87"), "max", 0)); ((TAtom "v93"), ((TAtom "v0"), "cur", 48)); ((TAtom "v94"), ((TAtom "v0"), "cur", 56))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), []); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L44"), []); ((TAtom "L47"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "iw_1.L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v57"); (TAtom "v6")]); ((TAtom "iw_1.L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v57"); (TAtom "v6")]); ((TAtom "iw_1.L18"), [(TAtom "v57")]); ((TAtom "iw_1.L20"), []); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v58"); (TAtom "v6"); (TAtom "v65")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v6"); (TAtom "v65")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v6"); (TAtom "v65")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v6"); (TAtom "v73")]); ((TAtom "L75"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73")]); ((TAtom "iw_2.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v87"); (TAtom "v95")]); ((TAtom "iw_2.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v87"); (TAtom "v95")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v87")]); ((TAtom "L88"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "L90"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "iw_3.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v110"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "iw_3.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v110"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "L103"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_4.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_4.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_4.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "L118"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "L120"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_5.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_5.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_5.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_6.start"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_6.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")]); ((TAtom "iw_6.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")]); ((TAtom "L134"), []); ((TAtom "L136"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), []); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), []); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v37"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v40"); (TAtom "v6")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v43"); (TAtom "v6")]); ((TAtom "L44"), []); ((TAtom "L47"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v57"); (TAtom "v6")]); ((TAtom "iw_1.L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v57"); (TAtom "v6")]); ((TAtom "iw_1.L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v57"); (TAtom "v6")]); ((TAtom "iw_1.L18"), []); ((TAtom "iw_1.L20"), []); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v4"); (TAtom "v58"); (TAtom "v6"); (TAtom "v65")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v6"); (TAtom "v65"); (TAtom "v68")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v6"); (TAtom "v65"); (TAtom "v72")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v6"); (TAtom "v73")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v82")]); ((TAtom "L75"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v86")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v87"); (TAtom "v95")]); ((TAtom "iw_2.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "iw_2.v12"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v87")]); ((TAtom "iw_2.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "iw_2.v17"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v87")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v58"); (TAtom "v73"); (TAtom "v87")]); ((TAtom "L88"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v102"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "L90"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v110"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "iw_3.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_3.v12"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "iw_3.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_3.v17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v58"); (TAtom "v87")]); ((TAtom "L103"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v117"); (TAtom "v58")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_4.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_4.v12"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_4.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_4.v17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_4.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "L118"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v129"); (TAtom "v133"); (TAtom "v58")]); ((TAtom "L120"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_5.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_5.v12"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_5.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_5.v17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_5.join"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v58")]); ((TAtom "iw_6.start"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")]); ((TAtom "iw_6.L6"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_6.v12"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")]); ((TAtom "iw_6.L7"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "iw_6.v17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "chk15"); (TAtom "chk17"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.5"); (TAtom "v0")]); ((TAtom "L134"), []); ((TAtom "L136"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 1), true, false, (Some (TAtom "v0")), (Some (105)), "cur->locked")]); ((TAtom "L11"), []); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (48)), "cur->type.type_code")]); ((TAtom "L23"), [(2%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "cur->val.strval"); (4%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88)), "opaque"); (8%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (8)), "cur->val.strval"); (10%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (96)), "cur->val.strval"); (13%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 1), false, true, (Some (TAtom "v0")), (Some (104)), "cur->initialized")]); ((TAtom "L34"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "valp->numval")]); ((TAtom "L38"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "valp->numval")]); ((TAtom "L41"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "valp->numval")]); ((TAtom "L44"), []); ((TAtom "L47"), []); ((TAtom "L49"), []); ((TAtom "L51"), []); ((TAtom "L22"), [(2%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (48)), "cur->type.type_code")]); ((TAtom "iw_1.L14"), []); ((TAtom "iw_1.L16"), []); ((TAtom "iw_1.L18"), []); ((TAtom "iw_1.L20"), []); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.join"), []); ((TAtom "L60"), [(1%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (0)), "opaque")]); ((TAtom "L61"), [(3%N, (TApp "tmp" [(TAtom "v71")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "cur->type.min")]); ((TAtom "L62"), []); ((TAtom "L74"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v6")), (Some (0)), "opaque")]); ((TAtom "L75"), [(3%N, (TApp "tmp" [(TAtom "v85")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (64)), "cur->type.max")]); ((TAtom "L76"), [(3%N, (TApp "tmp" [(TAtom "v94")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "cur->type.min")]); ((TAtom "iw_2.L6"), []); ((TAtom "iw_2.L7"), []); ((TAtom "iw_2.join"), []); ((TAtom "L88"), [(2%N, (TApp "tmp" [(TAtom "v94")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "cur->type.min")]); ((TAtom "L90"), [(3%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (64)), "cur->type.max")]); ((TAtom "iw_3.L6"), []); ((TAtom "iw_3.L7"), []); ((TAtom "iw_3.join"), []); ((TAtom "L103"), [(2%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (64)), "cur->type.max")]); ((TAtom "L105"), []); ((TAtom "iw_4.L6"), []); ((TAtom "iw_4.L7"), []); ((TAtom "iw_4.join"), []); ((TAtom "L118"), [(2%N, (TApp "tmp" [(TAtom "v94")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "cur->type.min"); (4%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (64)), "cur->type.max")]); ((TAtom "L120"), []); ((TAtom "iw_5.L6"), []); ((TAtom "iw_5.L7"), []); ((TAtom "iw_5.join"), []); ((TAtom "iw_6.start"), []); ((TAtom "iw_6.L6"), []); ((TAtom "iw_6.L7"), []); ((TAtom "L143"), []); ((TAtom "L134"), []); ((TAtom "L136"), [(2%N, (TApp "tmp" [(TAtom "v153")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88)), "cur->val.numval"); (5%N, (TApp "tmp" [(TAtom "v94")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (56)), "cur->type.min"); (7%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (64)), "cur->type.max"); (10%N, (TApp "tmp" [(TAtom "v164")]), (0), (Some 1), false, true, (Some (TAtom "v0")), (Some (104)), "cur->initialized")])].


End fn_glibc_dl_tunables_do_tunable_update_val.

Module fn___tunable_is_initialized.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_40, 158%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_40, 161%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "id"); ((TAtom "v3"), "id")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v6"), "v6", 104)); ((TAtom "v0"), ((TAtom "v0"), "id", 0)); ((TAtom "v2"), ((TAtom "v2"), "&tunable_list", 0)); ((TAtom "v7"), ((TAtom "v6"), "v6", 104))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(6%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 1), true, false, (Some (TAtom "v2")), None, "opaque")])].


End fn___tunable_is_initialized.

Module fn___tunable_set_val.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_40, 165%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_40, 169%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "id"); ((TAtom "v10"), "id"); ((TAtom "v13"), "cur"); ((TAtom "v14"), "cur"); ((TAtom "v15"), "valp"); ((TAtom "v16"), "minp"); ((TAtom "v17"), "maxp"); ((TAtom "v2"), "valp"); ((TAtom "v4"), "minp"); ((TAtom "v6"), "maxp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "id", 0)); ((TAtom "v13"), ((TAtom "v13"), "cur", 0)); ((TAtom "v2"), ((TAtom "v2"), "valp", 0)); ((TAtom "v4"), ((TAtom "v4"), "minp", 0)); ((TAtom "v6"), ((TAtom "v6"), "maxp", 0)); ((TAtom "v9"), ((TAtom "v9"), "&tunable_list", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___tunable_set_val.

Module fn___tunable_get_val.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_40, 613%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_40, 616%N)); ((TAtom "L17"), (file_40, 622%N)); ((TAtom "L22"), (file_40, 627%N)); ((TAtom "L27"), (file_40, 632%N)); ((TAtom "L32"), (file_40, 637%N)); ((TAtom "L36"), (file_40, 641%N)); ((TAtom "L39"), (file_40, 618%N)); ((TAtom "L41"), (file_40, 618%N)); ((TAtom "L43"), (file_40, 618%N)); ((TAtom "L16"), (file_40, 644%N)); ((TAtom "L52"), (file_40, 644%N)); ((TAtom "L53"), (file_40, 644%N)); ((TAtom "L46"), (file_40, 645%N)); ((TAtom "L48"), (file_40, 613%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "id"); ((TAtom "v11"), "cur"); ((TAtom "v12"), "cur"); ((TAtom "v18"), "valp"); ((TAtom "v19"), "cur"); ((TAtom "v2"), "valp"); ((TAtom "v23"), "valp"); ((TAtom "v24"), "cur"); ((TAtom "v28"), "valp"); ((TAtom "v29"), "cur"); ((TAtom "v33"), "valp"); ((TAtom "v34"), "cur"); ((TAtom "v4"), "callback"); ((TAtom "v49"), "cur"); ((TAtom "v54"), "callback"); ((TAtom "v60"), "callback"); ((TAtom "v61"), "cur"); ((TAtom "v8"), "id")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v11"), "cur", 48)); ((TAtom "chk1"), ((TAtom "v11"), "cur", 88)); ((TAtom "chk2"), ((TAtom "v2"), "valp", 0)); ((TAtom "chk3"), ((TAtom "v11"), "cur", 88)); ((TAtom "chk4"), ((TAtom "v2"), "valp", 0)); ((TAtom "chk5"), ((TAtom "v11"), "cur", 88)); ((TAtom "chk6"), ((TAtom "v2"), "valp", 0)); ((TAtom "chk7"), ((TAtom "v2"), "valp", 0)); ((TAtom "chk8"), ((TAtom "v11"), "cur", 104)); ((TAtom "v0"), ((TAtom "v0"), "id", 0)); ((TAtom "v11"), ((TAtom "v11"), "cur", 0)); ((TAtom "v13"), ((TAtom "v11"), "cur", 48)); ((TAtom "v2"), ((TAtom "v2"), "valp", 0)); ((TAtom "v20"), ((TAtom "v11"), "cur", 88)); ((TAtom "v25"), ((TAtom "v11"), "cur", 88)); ((TAtom "v30"), ((TAtom "v11"), "cur", 88)); ((TAtom "v35"), ((TAtom "v11"), "cur", 88)); ((TAtom "v4"), ((TAtom "v4"), "callback", 0)); ((TAtom "v50"), ((TAtom "v11"), "cur", 104)); ((TAtom "v62"), ((TAtom "v11"), "cur", 88)); ((TAtom "v7"), ((TAtom "v7"), "&tunable_list", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L36"), []); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v4")]); ((TAtom "L52"), [(TAtom "v11"); (TAtom "v4")]); ((TAtom "L53"), [(TAtom "v11"); (TAtom "v4")]); ((TAtom "L46"), [(TAtom "v11"); (TAtom "v4")]); ((TAtom "L48"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v4")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v4")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v4")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v4")]); ((TAtom "L36"), []); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "v11"); (TAtom "v4")]); ((TAtom "L52"), [(TAtom "v11"); (TAtom "v4"); (TAtom "v57")]); ((TAtom "L53"), [(TAtom "v11"); (TAtom "v4")]); ((TAtom "L46"), []); ((TAtom "L48"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(6%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 4), true, false, (Some (TAtom "v7")), None, "opaque")]); ((TAtom "L17"), [(2%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v7")), None, "opaque"); (4%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), false, true, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L22"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v7")), None, "opaque"); (4%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), false, true, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L27"), [(2%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), true, false, (Some (TAtom "v7")), None, "opaque"); (4%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), false, true, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L32"), [(2%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), false, true, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L36"), []); ((TAtom "L39"), []); ((TAtom "L41"), []); ((TAtom "L43"), []); ((TAtom "L16"), [(2%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 1), true, false, (Some (TAtom "v7")), None, "cur->initialized")]); ((TAtom "L52"), []); ((TAtom "L53"), []); ((TAtom "L46"), []); ((TAtom "L48"), [])].


End fn___tunable_get_val.

Module fn___GI___getrlimit64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_17, 37%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_17, 40%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "resource"); ((TAtom "v2"), "rlimits"); ((TAtom "v4"), "resource"); ((TAtom "v5"), "rlimits")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "resource", 0)); ((TAtom "v2"), ((TAtom "v2"), "rlimits", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___GI___getrlimit64.

Module fn_glibc_init_first__init_first.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_46, 44%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_46, 50%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "argc"); ((TAtom "v11"), "envp"); ((TAtom "v12"), "argc"); ((TAtom "v13"), "argv"); ((TAtom "v14"), "envp"); ((TAtom "v2"), "argv"); ((TAtom "v4"), "envp"); ((TAtom "v7"), "argc"); ((TAtom "v9"), "argv")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v6"), "&__libc_argc", 0)); ((TAtom "chk1"), ((TAtom "v8"), "&__libc_argv", 0)); ((TAtom "chk2"), ((TAtom "v10"), "&__environ", 0)); ((TAtom "v0"), ((TAtom "v0"), "argc", 0)); ((TAtom "v10"), ((TAtom "v10"), "&__environ", 0)); ((TAtom "v2"), ((TAtom "v2"), "argv", 0)); ((TAtom "v4"), ((TAtom "v4"), "envp", 0)); ((TAtom "v6"), ((TAtom "v6"), "&__libc_argc", 0)); ((TAtom "v8"), ((TAtom "v8"), "&__libc_argv", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), false, true, (Some (TAtom "v6")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), false, true, (Some (TAtom "v8")), (Some (0)), "opaque"); (8%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), false, true, (Some (TAtom "v10")), (Some (0)), "opaque")])].


End fn_glibc_init_first__init_first.

Module fn___init_misc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_47, 28%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_47, 31%N)); ((TAtom "L12"), (file_47, 31%N)); ((TAtom "L13"), (file_47, 31%N)); ((TAtom "L6"), (file_47, 33%N)); ((TAtom "L26"), (file_47, 35%N)); ((TAtom "L27"), (file_47, 37%N)); ((TAtom "L28"), (file_47, 38%N)); ((TAtom "L8"), (file_47, 28%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "argc"); ((TAtom "v14"), "argv"); ((TAtom "v2"), "argv"); ((TAtom "v22"), "argv"); ((TAtom "v25"), "p"); ((TAtom "v29"), "p"); ((TAtom "v34"), "argv"); ((TAtom "v36"), "__progname"); ((TAtom "v38"), "p"); ((TAtom "v39"), "__progname"); ((TAtom "v4"), "envp"); ((TAtom "v41"), "argv"); ((TAtom "v43"), "__progname_full"); ((TAtom "v9"), "argv")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v2"), "argv", 0)); ((TAtom "chk1"), ((TAtom "v2"), "argv", 0)); ((TAtom "chk2"), ((TAtom "v2"), "argv", 0)); ((TAtom "chk3"), ((TAtom "v33"), "&__progname", 0)); ((TAtom "chk4"), ((TAtom "v37"), "&__progname", 0)); ((TAtom "chk5"), ((TAtom "v2"), "argv", 0)); ((TAtom "chk6"), ((TAtom "v40"), "&__progname_full", 0)); ((TAtom "v0"), ((TAtom "v0"), "argc", 0)); ((TAtom "v2"), ((TAtom "v2"), "argv", 0)); ((TAtom "v25"), ((TAtom "v25"), "p", 0)); ((TAtom "v33"), ((TAtom "v33"), "&__progname", 0)); ((TAtom "v36"), ((TAtom "v36"), "__progname", 0)); ((TAtom "v37"), ((TAtom "v37"), "&__progname", 0)); ((TAtom "v39"), ((TAtom "v39"), "__progname", 0)); ((TAtom "v4"), ((TAtom "v4"), "envp", 0)); ((TAtom "v40"), ((TAtom "v40"), "&__progname_full", 0)); ((TAtom "v43"), ((TAtom "v43"), "__progname_full", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v2")]); ((TAtom "L12"), [(TAtom "v2")]); ((TAtom "L13"), [(TAtom "v2")]); ((TAtom "L6"), [(TAtom "v2")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "v2")]); ((TAtom "L27"), [(TAtom "chk1"); (TAtom "v2"); (TAtom "v25")]); ((TAtom "L28"), [(TAtom "chk1"); (TAtom "v2")]); ((TAtom "L8"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v2")]); ((TAtom "L12"), [(TAtom "v18"); (TAtom "v2")]); ((TAtom "L13"), [(TAtom "v2")]); ((TAtom "L6"), [(TAtom "chk1"); (TAtom "v2"); (TAtom "v25")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "v2")]); ((TAtom "L27"), [(TAtom "chk1"); (TAtom "v2")]); ((TAtom "L28"), []); ((TAtom "L8"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L12"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L13"), []); ((TAtom "L6"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "opaque"); (4%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), false, true, (Some (TAtom "v33")), (Some (0)), "opaque")]); ((TAtom "L27"), [(3%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v37")), (Some (0)), "opaque")]); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)), "opaque"); (4%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), false, true, (Some (TAtom "v40")), (Some (0)), "opaque")]); ((TAtom "L8"), [])].


End fn___init_misc.

Module fn___GI_strrchr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_62, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_62, 30%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "s"); ((TAtom "v2"), "c"); ((TAtom "v4"), "s"); ((TAtom "v5"), "c"); ((TAtom "v6"), "s")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "s", 0)); ((TAtom "v2"), ((TAtom "v2"), "c", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___GI_strrchr.

Module fn___GI___clock_gettime.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_13, 26%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_13, 29%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "clock_id"); ((TAtom "v2"), "tp"); ((TAtom "v4"), "clock_id"); ((TAtom "v5"), "tp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "clock_id", 0)); ((TAtom "v2"), ((TAtom "v2"), "tp", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___GI___clock_gettime.

End HiAtexitSrc18.

(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import HiAtexitSrcFiles.
Import HiAtexitSrcFiles.
Module HiAtexitSrc16.

Module fn_glibc_libc_start_get_common_indices.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 418%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 425%N)); ((TAtom "L10"), (file_27, 426%N)); ((TAtom "L48"), (file_27, 437%N)); ((TAtom "L12"), (file_27, 442%N)); ((TAtom "L65"), (file_27, 444%N)); ((TAtom "L67"), (file_27, 456%N)); ((TAtom "L102"), (file_27, 457%N)); ((TAtom "L104"), (file_27, 463%N)); ((TAtom "L124"), (file_27, 464%N)); ((TAtom "L126"), (file_27, 470%N)); ((TAtom "L146"), (file_27, 471%N)); ((TAtom "iw_1.start"), (file_24, 64%N)); ((TAtom "iw_1.L4"), (file_24, 27%N)); ((TAtom "iw_1.L16"), (file_24, 27%N)); ((TAtom "iw_1.L17"), (file_24, 27%N)); ((TAtom "iw_1.L9"), (file_24, 65%N)); ((TAtom "iw_1.L10"), (file_24, 81%N)); ((TAtom "iw_1.join"), (file_27, 418%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "cpu_features"); ((TAtom "iw_1.v12"), "cpu_features"); ((TAtom "iw_1.v18"), "cpu_features"); ((TAtom "iw_1.v29"), "sigframe_size"); ((TAtom "iw_1.v30"), "sigframe_size"); ((TAtom "iw_1.v31"), "sigframe_size"); ((TAtom "iw_1.v32"), "sigframe_size"); ((TAtom "iw_1.v36"), "sigframe_size"); ((TAtom "iw_1.v37"), "sigframe_size"); ((TAtom "iw_1.v39"), "sigframe_size"); ((TAtom "iw_1.v44"), "sigframe_size"); ((TAtom "iw_1.v45"), "ebx"); ((TAtom "iw_1.v46"), "sigframe_size"); ((TAtom "iw_1.v47"), "sigframe_size"); ((TAtom "iw_1.v49"), "sigframe_size"); ((TAtom "iw_1.v51"), "sigframe_size"); ((TAtom "iw_1.v52"), "_dl_minsigstacksize"); ((TAtom "iw_1.v6"), "_dl_minsigstacksize"); ((TAtom "v0"), "cpu_features"); ((TAtom "v105"), "cpu_features"); ((TAtom "v109"), "cpu_features"); ((TAtom "v112"), "cpu_features"); ((TAtom "v116"), "cpu_features"); ((TAtom "v120"), "cpu_features"); ((TAtom "v127"), "cpu_features"); ((TAtom "v13"), "family"); ((TAtom "v131"), "cpu_features"); ((TAtom "v134"), "cpu_features"); ((TAtom "v138"), "cpu_features"); ((TAtom "v142"), "cpu_features"); ((TAtom "v149"), "cpu_features"); ((TAtom "v153"), "cpu_features"); ((TAtom "v156"), "cpu_features"); ((TAtom "v160"), "cpu_features"); ((TAtom "v164"), "cpu_features"); ((TAtom "v168"), "cpu_features"); ((TAtom "v17"), "cpu_features"); ((TAtom "v2"), "family"); ((TAtom "v21"), "cpu_features"); ((TAtom "v25"), "cpu_features"); ((TAtom "v29"), "cpu_features"); ((TAtom "v32"), "eax"); ((TAtom "v33"), "family"); ((TAtom "v34"), "eax"); ((TAtom "v37"), "model"); ((TAtom "v38"), "eax"); ((TAtom "v4"), "model"); ((TAtom "v41"), "extended_model"); ((TAtom "v42"), "eax"); ((TAtom "v45"), "stepping"); ((TAtom "v46"), "eax"); ((TAtom "v51"), "family"); ((TAtom "v54"), "family"); ((TAtom "v56"), "eax"); ((TAtom "v6"), "extended_model"); ((TAtom "v60"), "model"); ((TAtom "v62"), "extended_model"); ((TAtom "v68"), "cpu_features"); ((TAtom "v72"), "cpu_features"); ((TAtom "v75"), "cpu_features"); ((TAtom "v79"), "cpu_features"); ((TAtom "v8"), "stepping"); ((TAtom "v83"), "cpu_features"); ((TAtom "v87"), "cpu_features"); ((TAtom "v90"), "cpu_features"); ((TAtom "v94"), "cpu_features"); ((TAtom "v98"), "cpu_features")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v16"), "&eax", 0)); ((TAtom "chk1"), ((TAtom "v0"), "cpu_features", 20)); ((TAtom "chk17"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "chk18"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "chk19"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "chk20"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "chk21"), ((TAtom "iw_1.v5"), "&_dl_minsigstacksize", 0)); ((TAtom "chk22"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "chk23"), ((TAtom "v0"), "cpu_features", 28)); ((TAtom "chk24"), ((TAtom "iw_1.v41"), "&ebx", 0)); ((TAtom "chk25"), ((TAtom "iw_1.v50"), "&_dl_minsigstacksize", 0)); ((TAtom "chk26"), ((TAtom "iw_1.v53"), "&_dl_minsigstacksize", 0)); ((TAtom "chk3"), ((TAtom "v2"), "family", 0)); ((TAtom "chk5"), ((TAtom "v4"), "model", 0)); ((TAtom "chk7"), ((TAtom "v6"), "extended_model", 0)); ((TAtom "chk9"), ((TAtom "v8"), "stepping", 0)); ((TAtom "iw_1.v13"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "iw_1.v19"), ((TAtom "v0"), "cpu_features", 20)); ((TAtom "iw_1.v21"), ((TAtom "v0"), "cpu_features", 28)); ((TAtom "iw_1.v40"), ((TAtom "iw_1.v40"), "&eax", 0)); ((TAtom "iw_1.v41"), ((TAtom "iw_1.v41"), "&ebx", 0)); ((TAtom "iw_1.v42"), ((TAtom "iw_1.v42"), "&ecx", 0)); ((TAtom "iw_1.v43"), ((TAtom "iw_1.v43"), "&edx", 0)); ((TAtom "iw_1.v45"), ((TAtom "iw_1.v45"), "ebx", 0)); ((TAtom "iw_1.v46"), ((TAtom "iw_1.v46"), "sigframe_size", 0)); ((TAtom "iw_1.v49"), ((TAtom "iw_1.v49"), "sigframe_size", 0)); ((TAtom "iw_1.v5"), ((TAtom "iw_1.v5"), "&_dl_minsigstacksize", 0)); ((TAtom "iw_1.v50"), ((TAtom "iw_1.v50"), "&_dl_minsigstacksize", 0)); ((TAtom "iw_1.v51"), ((TAtom "iw_1.v51"), "sigframe_size", 0)); ((TAtom "iw_1.v52"), ((TAtom "iw_1.v52"), "_dl_minsigstacksize", 0)); ((TAtom "iw_1.v53"), ((TAtom "iw_1.v53"), "&_dl_minsigstacksize", 0)); ((TAtom "iw_1.v6"), ((TAtom "iw_1.v6"), "_dl_minsigstacksize", 0)); ((TAtom "v0"), ((TAtom "v0"), "cpu_features", 0)); ((TAtom "v101"), ((TAtom "v0"), "cpu_features", 224)); ((TAtom "v106"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "v110"), ((TAtom "v0"), "cpu_features", 20)); ((TAtom "v111"), ((TAtom "v0"), "cpu_features", 116)); ((TAtom "v115"), ((TAtom "v0"), "cpu_features", 120)); ((TAtom "v119"), ((TAtom "v0"), "cpu_features", 124)); ((TAtom "v123"), ((TAtom "v0"), "cpu_features", 128)); ((TAtom "v128"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "v132"), ((TAtom "v0"), "cpu_features", 20)); ((TAtom "v133"), ((TAtom "v0"), "cpu_features", 276)); ((TAtom "v137"), ((TAtom "v0"), "cpu_features", 280)); ((TAtom "v141"), ((TAtom "v0"), "cpu_features", 284)); ((TAtom "v145"), ((TAtom "v0"), "cpu_features", 288)); ((TAtom "v150"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "v154"), ((TAtom "v0"), "cpu_features", 20)); ((TAtom "v155"), ((TAtom "v0"), "cpu_features", 244)); ((TAtom "v159"), ((TAtom "v0"), "cpu_features", 248)); ((TAtom "v16"), ((TAtom "v16"), "&eax", 0)); ((TAtom "v163"), ((TAtom "v0"), "cpu_features", 252)); ((TAtom "v167"), ((TAtom "v0"), "cpu_features", 256)); ((TAtom "v18"), ((TAtom "v0"), "cpu_features", 20)); ((TAtom "v2"), ((TAtom "v2"), "family", 0)); ((TAtom "v20"), ((TAtom "v0"), "cpu_features", 24)); ((TAtom "v24"), ((TAtom "v0"), "cpu_features", 28)); ((TAtom "v28"), ((TAtom "v0"), "cpu_features", 32)); ((TAtom "v32"), ((TAtom "v32"), "eax", 0)); ((TAtom "v34"), ((TAtom "v34"), "eax", 0)); ((TAtom "v38"), ((TAtom "v38"), "eax", 0)); ((TAtom "v4"), ((TAtom "v4"), "model", 0)); ((TAtom "v42"), ((TAtom "v42"), "eax", 0)); ((TAtom "v46"), ((TAtom "v46"), "eax", 0)); ((TAtom "v56"), ((TAtom "v56"), "eax", 0)); ((TAtom "v6"), ((TAtom "v6"), "extended_model", 0)); ((TAtom "v69"), ((TAtom "v0"), "cpu_features", 4)); ((TAtom "v73"), ((TAtom "v0"), "cpu_features", 20)); ((TAtom "v74"), ((TAtom "v0"), "cpu_features", 52)); ((TAtom "v78"), ((TAtom "v0"), "cpu_features", 56)); ((TAtom "v8"), ((TAtom "v8"), "stepping", 0)); ((TAtom "v82"), ((TAtom "v0"), "cpu_features", 60)); ((TAtom "v86"), ((TAtom "v0"), "cpu_features", 64)); ((TAtom "v89"), ((TAtom "v0"), "cpu_features", 212)); ((TAtom "v93"), ((TAtom "v0"), "cpu_features", 216)); ((TAtom "v97"), ((TAtom "v0"), "cpu_features", 220))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk3"); (TAtom "chk5"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L12"), [(TAtom "v0")]); ((TAtom "L65"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L67"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L102"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L104"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L124"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L126"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L146"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "iw_1.start"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "chk17"); (TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43"); (TAtom "v0")]); ((TAtom "iw_1.L16"), [(TAtom "chk17"); (TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43"); (TAtom "v0")]); ((TAtom "iw_1.L17"), [(TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43")]); ((TAtom "iw_1.L9"), [(TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "chk3"); (TAtom "chk5"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L48"), [(TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L65"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L67"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L102"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L104"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L124"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L126"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "L146"), [(TAtom "chk17"); (TAtom "v0")]); ((TAtom "iw_1.start"), [(TAtom "chk17"); (TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43"); (TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "chk17"); (TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43"); (TAtom "v0")]); ((TAtom "iw_1.L16"), [(TAtom "iw_1.v25"); (TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43")]); ((TAtom "iw_1.L17"), [(TAtom "iw_1.v40"); (TAtom "iw_1.v41"); (TAtom "iw_1.v42"); (TAtom "iw_1.v43")]); ((TAtom "iw_1.L9"), []); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L10"), [(6%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v16")), (Some (0)), "opaque"); (8%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (20)), "cpu_features->features"); (9%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v16")), (Some (0)), "opaque"); (13%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), false, true, (Some (TAtom "v2")), (Some (0)), "opaque"); (14%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v16")), (Some (0)), "opaque"); (18%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 4), false, true, (Some (TAtom "v4")), (Some (0)), "opaque"); (19%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v16")), (Some (0)), "opaque"); (23%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), false, true, (Some (TAtom "v6")), (Some (0)), "opaque"); (24%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v16")), (Some (0)), "opaque"); (27%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), false, true, (Some (TAtom "v8")), (Some (0)), "opaque"); (28%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), true, false, (Some (TAtom "v2")), (Some (0)), "opaque")]); ((TAtom "L48"), [(0%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), true, false, (Some (TAtom "v2")), (Some (0)), "opaque"); (1%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v16")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), false, true, (Some (TAtom "v2")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 4), true, false, (Some (TAtom "v4")), (Some (0)), "opaque"); (7%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), true, false, (Some (TAtom "v6")), (Some (0)), "opaque"); (9%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 4), false, true, (Some (TAtom "v4")), (Some (0)), "opaque")]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v69")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "cpu_features->basic.max_cpuid")]); ((TAtom "L65"), []); ((TAtom "L67"), [(2%N, (TApp "tmp" [(TAtom "v106")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "cpu_features->basic.max_cpuid")]); ((TAtom "L102"), []); ((TAtom "L104"), [(2%N, (TApp "tmp" [(TAtom "v128")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "cpu_features->basic.max_cpuid")]); ((TAtom "L124"), []); ((TAtom "L126"), [(2%N, (TApp "tmp" [(TAtom "v150")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "cpu_features->basic.max_cpuid")]); ((TAtom "L146"), []); ((TAtom "iw_1.start"), [(6%N, (TApp "tmp" [(TAtom "iw_1.v5")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v5")), (Some (0)), "opaque")]); ((TAtom "iw_1.L4"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v13")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (4)), "cpu_features->basic.max_cpuid")]); ((TAtom "iw_1.L16"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v21")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (28)), "opaque")]); ((TAtom "iw_1.L17"), []); ((TAtom "iw_1.L9"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v41")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v41")), (Some (0)), "opaque"); (10%N, (TApp "tmp" [(TAtom "iw_1.v50")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v50")), (Some (0)), "opaque")]); ((TAtom "iw_1.L10"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v53")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v53")), (Some (0)), "opaque")]); ((TAtom "iw_1.join"), [])].


End fn_glibc_libc_start_get_common_indices.

Module fn_glibc_libc_start___libc_start_call_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_9, 23%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_9, 23%N)); ((TAtom "L10"), (file_9, 49%N)); ((TAtom "L11"), (file_9, 64%N)); ((TAtom "L39"), (file_9, 74%N)); ((TAtom "L40"), (file_9, 74%N)); ((TAtom "L41"), (file_9, 75%N)); ((TAtom "L52"), (file_9, 77%N)); ((TAtom "L53"), (file_9, 77%N)); ((TAtom "L46"), (file_9, 79%N)); ((TAtom "L59"), (file_9, 79%N)); ((TAtom "L60"), (file_9, 80%N)); ((TAtom "L61"), (file_9, 77%N)); ((TAtom "L47"), (file_9, 77%N)); ((TAtom "L48"), (file_9, 47%N)); ((TAtom "L12"), (file_9, 83%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "main"); ((TAtom "v13"), "not_first_call"); ((TAtom "v18"), "self"); ((TAtom "v2"), "argc"); ((TAtom "v20"), "self"); ((TAtom "v25"), "self"); ((TAtom "v28"), "self"); ((TAtom "v30"), "main"); ((TAtom "v31"), "argc"); ((TAtom "v32"), "argv"); ((TAtom "v34"), "__environ"); ((TAtom "v35"), "result"); ((TAtom "v38"), "self"); ((TAtom "v4"), "argv"); ((TAtom "v42"), "self"); ((TAtom "v44"), "self"); ((TAtom "v51"), "__nptl_nthreads"); ((TAtom "v65"), "__arg1"); ((TAtom "v66"), "_a1"); ((TAtom "v68"), "resultvar"); ((TAtom "v69"), "result"); ((TAtom "v9"), "not_first_call")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v1"), "&main", 0)); ((TAtom "chk1"), ((TAtom "v3"), "&argc", 0)); ((TAtom "chk10"), ((TAtom "v25"), "self", 776)); ((TAtom "chk11"), ((TAtom "v7"), "&unwind_buf", 80)); ((TAtom "chk12"), ((TAtom "v17"), "&self", 0)); ((TAtom "chk13"), ((TAtom "v28"), "self", 784)); ((TAtom "chk14"), ((TAtom "v1"), "&main", 0)); ((TAtom "chk15"), ((TAtom "v3"), "&argc", 0)); ((TAtom "chk16"), ((TAtom "v5"), "&argv", 0)); ((TAtom "chk17"), ((TAtom "v33"), "&__environ", 0)); ((TAtom "chk19"), ((TAtom "v6"), "&result", 0)); ((TAtom "chk2"), ((TAtom "v5"), "&argv", 0)); ((TAtom "chk20"), ((TAtom "v6"), "&result", 0)); ((TAtom "chk21"), ((TAtom "v37"), "&self", 0)); ((TAtom "chk22"), ((TAtom "v37"), "&self", 0)); ((TAtom "chk23"), ((TAtom "v42"), "self", 1592)); ((TAtom "chk25"), ((TAtom "v49"), "&__nptl_nthreads", 0)); ((TAtom "chk26"), ((TAtom "v49"), "&__nptl_nthreads", 0)); ((TAtom "chk27"), ((TAtom "v63"), "&__arg1", 0)); ((TAtom "chk29"), ((TAtom "v64"), "&_a1", 0)); ((TAtom "chk3"), ((TAtom "v8"), "&not_first_call", 0)); ((TAtom "chk31"), ((TAtom "v62"), "&resultvar", 0)); ((TAtom "chk32"), ((TAtom "v6"), "&result", 0)); ((TAtom "chk5"), ((TAtom "v17"), "&self", 0)); ((TAtom "chk6"), ((TAtom "v17"), "&self", 0)); ((TAtom "chk7"), ((TAtom "v20"), "self", 784)); ((TAtom "chk8"), ((TAtom "v7"), "&unwind_buf", 72)); ((TAtom "chk9"), ((TAtom "v17"), "&self", 0)); ((TAtom "v0"), ((TAtom "v0"), "main", 0)); ((TAtom "v1"), ((TAtom "v1"), "&main", 0)); ((TAtom "v13"), ((TAtom "v13"), "not_first_call", 0)); ((TAtom "v17"), ((TAtom "v17"), "&self", 0)); ((TAtom "v18"), ((TAtom "v18"), "self", 0)); ((TAtom "v19"), ((TAtom "v7"), "&unwind_buf", 72)); ((TAtom "v2"), ((TAtom "v2"), "argc", 0)); ((TAtom "v20"), ((TAtom "v20"), "self", 0)); ((TAtom "v21"), ((TAtom "v20"), "self", 784)); ((TAtom "v23"), ((TAtom "v7"), "&unwind_buf", 72)); ((TAtom "v24"), ((TAtom "v7"), "&unwind_buf", 80)); ((TAtom "v25"), ((TAtom "v25"), "self", 0)); ((TAtom "v26"), ((TAtom "v25"), "self", 776)); ((TAtom "v28"), ((TAtom "v28"), "self", 0)); ((TAtom "v29"), ((TAtom "v28"), "self", 784)); ((TAtom "v3"), ((TAtom "v3"), "&argc", 0)); ((TAtom "v30"), ((TAtom "v30"), "main", 0)); ((TAtom "v31"), ((TAtom "v31"), "argc", 0)); ((TAtom "v32"), ((TAtom "v32"), "argv", 0)); ((TAtom "v33"), ((TAtom "v33"), "&__environ", 0)); ((TAtom "v34"), ((TAtom "v34"), "__environ", 0)); ((TAtom "v35"), ((TAtom "v35"), "result", 0)); ((TAtom "v36"), ((TAtom "v36"), "&set", 0)); ((TAtom "v37"), ((TAtom "v37"), "&self", 0)); ((TAtom "v38"), ((TAtom "v38"), "self", 0)); ((TAtom "v4"), ((TAtom "v4"), "argv", 0)); ((TAtom "v42"), ((TAtom "v42"), "self", 0)); ((TAtom "v43"), ((TAtom "v42"), "self", 1592)); ((TAtom "v44"), ((TAtom "v44"), "self", 0)); ((TAtom "v45"), ((TAtom "v44"), "self", 1592)); ((TAtom "v49"), ((TAtom "v49"), "&__nptl_nthreads", 0)); ((TAtom "v5"), ((TAtom "v5"), "&argv", 0)); ((TAtom "v51"), ((TAtom "v51"), "__nptl_nthreads", 0)); ((TAtom "v6"), ((TAtom "v6"), "&result", 0)); ((TAtom "v62"), ((TAtom "v62"), "&resultvar", 0)); ((TAtom "v63"), ((TAtom "v63"), "&__arg1", 0)); ((TAtom "v64"), ((TAtom "v64"), "&_a1", 0)); ((TAtom "v65"), ((TAtom "v65"), "__arg1", 0)); ((TAtom "v66"), ((TAtom "v66"), "_a1", 0)); ((TAtom "v68"), ((TAtom "v68"), "resultvar", 0)); ((TAtom "v69"), ((TAtom "v69"), "result", 0)); ((TAtom "v7"), ((TAtom "v7"), "&unwind_buf", 0)); ((TAtom "v8"), ((TAtom "v8"), "&not_first_call", 0)); ((TAtom "v9"), ((TAtom "v9"), "not_first_call", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L39"); (TAtom "L52"); (TAtom "L59")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "v1"); (TAtom "v17"); (TAtom "v3"); (TAtom "v5"); (TAtom "v6"); (TAtom "v7")]); ((TAtom "L11"), [(TAtom "v36"); (TAtom "v37"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L39"), [(TAtom "v37"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L40"), [(TAtom "chk22"); (TAtom "v37"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L41"), [(TAtom "chk22"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L52"), [(TAtom "v49"); (TAtom "v50"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L53"), [(TAtom "v54"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L46"), [(TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L59"), [(TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L60"), [(TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L61"), [(TAtom "v6")]); ((TAtom "L47"), [(TAtom "v6")]); ((TAtom "L48"), [(TAtom "v6")]); ((TAtom "L12"), [(TAtom "v6")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v1"); (TAtom "v17"); (TAtom "v3"); (TAtom "v36"); (TAtom "v37"); (TAtom "v5"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64"); (TAtom "v7")]); ((TAtom "L10"), [(TAtom "v6")]); ((TAtom "L11"), [(TAtom "v37"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L39"), [(TAtom "chk22"); (TAtom "v37"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L40"), [(TAtom "chk22"); (TAtom "v37"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L41"), [(TAtom "v49"); (TAtom "v50"); (TAtom "v51"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L52"), [(TAtom "v49"); (TAtom "v50"); (TAtom "v54"); (TAtom "v56"); (TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L53"), [(TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L46"), [(TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L59"), [(TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L60"), [(TAtom "v6"); (TAtom "v62"); (TAtom "v63"); (TAtom "v64")]); ((TAtom "L61"), [(TAtom "v6")]); ((TAtom "L47"), [(TAtom "v6")]); ((TAtom "L48"), [(TAtom "v6")]); ((TAtom "L12"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(13%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), false, true, (Some (TAtom "v1")), (Some (0)), "opaque"); (15%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 4), false, true, (Some (TAtom "v3")), (Some (0)), "opaque"); (17%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v5")), (Some (0)), "opaque"); (18%N, (TApp "tmp" [(TAtom "v7")]), (0), None, false, true, (Some (TAtom "v7")), (Some (0)), "opaque"); (20%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), false, true, (Some (TAtom "v8")), (Some (0)), "opaque"); (21%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), true, false, (Some (TAtom "v8")), (Some (0)), "opaque")]); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), false, true, (Some (TAtom "v17")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v17")), (Some (0)), "opaque"); (8%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v20")), (Some (784)), "self->cleanup_jmp_buf"); (10%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), false, true, (Some (TAtom "v7")), (Some (72)), "unwind_buf.priv.data.prev"); (14%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v17")), (Some (0)), "opaque"); (17%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), true, false, (Some (TAtom "v25")), (Some (776)), "self->cleanup"); (19%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), false, true, (Some (TAtom "v7")), (Some (80)), "unwind_buf.priv.data.cleanup"); (21%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v17")), (Some (0)), "opaque"); (24%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 8), false, true, (Some (TAtom "v28")), (Some (784)), "self->cleanup_jmp_buf"); (26%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), true, false, (Some (TAtom "v1")), (Some (0)), "opaque"); (28%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (0)), "opaque"); (30%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), true, false, (Some (TAtom "v5")), (Some (0)), "opaque"); (33%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v33")), (Some (0)), "opaque"); (37%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), false, true, (Some (TAtom "v6")), (Some (0)), "opaque")]); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), false, true, (Some (TAtom "v6")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v37")), (Some (0)), "opaque")]); ((TAtom "L39"), [(1%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v37")), (Some (0)), "opaque"); (4%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 4), false, true, (Some (TAtom "v42")), (Some (1592)), "self->joinstate")]); ((TAtom "L40"), []); ((TAtom "L41"), [(0%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v37")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 4), true, false, (Some (TAtom "v49")), (Some (0)), "opaque")]); ((TAtom "L52"), [(2%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 4), true, true, (Some (TAtom "v49")), (Some (0)), "opaque")]); ((TAtom "L53"), []); ((TAtom "L46"), []); ((TAtom "L59"), []); ((TAtom "L60"), [(1%N, (TApp "tmp" [(TAtom "v63")]), (0), (Some 4), false, true, (Some (TAtom "v63")), (Some (0)), "opaque"); (2%N, (TApp "tmp" [(TAtom "v63")]), (0), (Some 4), true, false, (Some (TAtom "v63")), (Some (0)), "opaque"); (4%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 4), false, true, (Some (TAtom "v64")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 4), true, false, (Some (TAtom "v64")), (Some (0)), "opaque"); (9%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v62")), (Some (0)), "opaque")]); ((TAtom "L61"), []); ((TAtom "L47"), []); ((TAtom "L48"), []); ((TAtom "L12"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), true, false, (Some (TAtom "v6")), (Some (0)), "opaque")])].


End fn_glibc_libc_start___libc_start_call_main.

Module fn_glibc_libc_start_errno_handler.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 88%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 90%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "errno_value"); ((TAtom "v3"), "errno_value")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v2"), "&__libc_errno", 0)); ((TAtom "v0"), ((TAtom "v0"), "errno_value", 0)); ((TAtom "v2"), ((TAtom "v2"), "&__libc_errno", 0))].

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
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), false, true, (Some (TAtom "v2")), (Some (0)), "opaque")])].


End fn_glibc_libc_start_errno_handler.

Module fn_glibc_libc_start_dlerror_handler.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 93%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 95%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "str"); ((TAtom "v3"), "str")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v2"), "&__libc_dlerror_result_string", 0)); ((TAtom "v0"), ((TAtom "v0"), "str", 0)); ((TAtom "v2"), ((TAtom "v2"), "&__libc_dlerror_result_string", 0))].

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
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), false, true, (Some (TAtom "v2")), (Some (0)), "opaque")])].


End fn_glibc_libc_start_dlerror_handler.

Module fn___libc_start_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 98%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 104%N)); ((TAtom "L17"), (file_1, 109%N)); ((TAtom "L18"), (file_1, 111%N)); ((TAtom "L24"), (file_1, 113%N)); ((TAtom "L19"), (file_1, 110%N)); ((TAtom "L20"), (file_1, 118%N)); ((TAtom "L37"), (file_1, 119%N)); ((TAtom "L39"), (file_1, 121%N)); ((TAtom "L48"), (file_1, 149%N)); ((TAtom "L50"), (file_1, 151%N)); ((TAtom "L61"), (file_1, 154%N)); ((TAtom "L63"), (file_1, 159%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "av"); ((TAtom "v0"), "main"); ((TAtom "v12"), "ev"); ((TAtom "v14"), "auxvec"); ((TAtom "v16"), "auxvec"); ((TAtom "v2"), "argc"); ((TAtom "v21"), "av"); ((TAtom "v27"), "av"); ((TAtom "v31"), "av"); ((TAtom "v33"), "__libc_enable_secure"); ((TAtom "v35"), "av"); ((TAtom "v36"), "av"); ((TAtom "v4"), "argv"); ((TAtom "v52"), "_dl_debug_mask"); ((TAtom "v58"), "argv"); ((TAtom "v6"), "ev"); ((TAtom "v65"), "_dl_debug_mask"); ((TAtom "v71"), "argv"); ((TAtom "v74"), "main"); ((TAtom "v75"), "argc"); ((TAtom "v76"), "argv"); ((TAtom "v8"), "auxvec")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v11"), "&__environ", 0)); ((TAtom "chk1"), ((TAtom "v13"), "&_dl_auxv", 0)); ((TAtom "chk2"), ((TAtom "pr.1"), "av", 0)); ((TAtom "chk4"), ((TAtom "pr.1"), "av", 8)); ((TAtom "chk5"), ((TAtom "v30"), "&__libc_enable_secure", 0)); ((TAtom "chk6"), ((TAtom "v51"), "&_dl_debug_mask", 0)); ((TAtom "chk7"), ((TAtom "v4"), "argv", 0)); ((TAtom "chk8"), ((TAtom "v64"), "&_dl_debug_mask", 0)); ((TAtom "chk9"), ((TAtom "v4"), "argv", 0)); ((TAtom "pr.1"), ((TAtom "pr.1"), "av", 0)); ((TAtom "v0"), ((TAtom "v0"), "main", 0)); ((TAtom "v11"), ((TAtom "v11"), "&__environ", 0)); ((TAtom "v13"), ((TAtom "v13"), "&_dl_auxv", 0)); ((TAtom "v2"), ((TAtom "v2"), "argc", 0)); ((TAtom "v30"), ((TAtom "v30"), "&__libc_enable_secure", 0)); ((TAtom "v32"), ((TAtom "pr.1"), "av", 8)); ((TAtom "v33"), ((TAtom "v33"), "__libc_enable_secure", 0)); ((TAtom "v36"), ((TAtom "v36"), "av", 0)); ((TAtom "v4"), ((TAtom "v4"), "argv", 0)); ((TAtom "v44"), ((TAtom "v44"), "&_dl_x86_cpu_features", 0)); ((TAtom "v51"), ((TAtom "v51"), "&_dl_debug_mask", 0)); ((TAtom "v52"), ((TAtom "v52"), "_dl_debug_mask", 0)); ((TAtom "v6"), ((TAtom "v6"), "ev", 0)); ((TAtom "v64"), ((TAtom "v64"), "&_dl_debug_mask", 0)); ((TAtom "v65"), ((TAtom "v65"), "_dl_debug_mask", 0)); ((TAtom "v8"), ((TAtom "v8"), "auxvec", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L17")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L17"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L24"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L39"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L50"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L61"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L63"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "L17"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L24"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v36"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L39"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L50"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L61"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L63"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), false, true, (Some (TAtom "v11")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v13")), (Some (0)), "opaque")]); ((TAtom "L17"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "av->a_type")]); ((TAtom "L18"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "av->a_type")]); ((TAtom "L24"), [(3%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)), "av->a_un.a_val"); (5%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 4), false, true, (Some (TAtom "v30")), (Some (0)), "opaque")]); ((TAtom "L19"), []); ((TAtom "L20"), []); ((TAtom "L37"), []); ((TAtom "L39"), [(10%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 4), true, false, (Some (TAtom "v51")), (Some (0)), "opaque")]); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (0)), "opaque")]); ((TAtom "L50"), [(3%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 4), true, false, (Some (TAtom "v64")), (Some (0)), "opaque")]); ((TAtom "L61"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (0)), "opaque")]); ((TAtom "L63"), [])].


End fn___libc_start_main.

Module fn_glibc_libc_start_futex_wake.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_8, 170%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_8, 173%N)); ((TAtom "L17"), (file_8, 173%N)); ((TAtom "L18"), (file_8, 173%N)); ((TAtom "L14"), (file_8, 173%N)); ((TAtom "L11"), (file_8, 173%N)); ((TAtom "L29"), (file_8, 173%N)); ((TAtom "L30"), (file_8, 173%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "futex_word"); ((TAtom "v15"), "private"); ((TAtom "v19"), "private"); ((TAtom "v2"), "processes_to_wake"); ((TAtom "v31"), "private"); ((TAtom "v37"), "res"); ((TAtom "v4"), "private"); ((TAtom "v40"), "res"); ((TAtom "v7"), "futex_word"); ((TAtom "v8"), "processes_to_wake")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "futex_word", 0)); ((TAtom "v2"), ((TAtom "v2"), "processes_to_wake", 0)); ((TAtom "v4"), ((TAtom "v4"), "private", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L17"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L14"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L17"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L18"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L14"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L30"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L17"), []); ((TAtom "L18"), []); ((TAtom "L14"), []); ((TAtom "L11"), []); ((TAtom "L29"), []); ((TAtom "L30"), [])].


End fn_glibc_libc_start_futex_wake.

End HiAtexitSrc16.

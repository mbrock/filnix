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
Module HiAtexitSrc01.

Module fn_hi_atexit_close_stdout_hi.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_31, 10%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_31, 11%N)); ((TAtom "L19"), (file_31, 14%N)); ((TAtom "L20"), (file_31, 14%N)); ((TAtom "L15"), (file_31, 15%N)); ((TAtom "L28"), (file_31, 15%N)); ((TAtom "L29"), (file_31, 15%N)); ((TAtom "L24"), (file_31, 16%N)); ((TAtom "L17"), (file_31, 10%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v12"), "stdout"); ((TAtom "v14"), "fclose_fail"); ((TAtom "v18"), "prev_fail"); ((TAtom "v2"), "stdout"); ((TAtom "v21"), "fclose_fail"); ((TAtom "v27"), "pending"); ((TAtom "v30"), "fclose_fail"); ((TAtom "v4"), "pending"); ((TAtom "v7"), "stdout"); ((TAtom "v9"), "prev_fail")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L19"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "v14")]); ((TAtom "L29"), []); ((TAtom "L24"), []); ((TAtom "L17"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "v14")]); ((TAtom "L28"), [(TAtom "v14")]); ((TAtom "L29"), []); ((TAtom "L24"), []); ((TAtom "L17"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), true, false, (Some (TAtom "v1")), (Some (0)), "opaque"); (7%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v6")), (Some (0)), "opaque"); (12%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (0)), "opaque")]); ((TAtom "L19"), []); ((TAtom "L20"), []); ((TAtom "L15"), []); ((TAtom "L28"), []); ((TAtom "L29"), []); ((TAtom "L24"), []); ((TAtom "L17"), [])].


End fn_hi_atexit_close_stdout_hi.

Module fn_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_31, 20%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_31, 21%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

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


End fn_main.

Module fn_glibc_malloc__dl_tunable_set_mmap_threshold.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 231%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 231%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v7"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

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
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (5%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v5")), (Some (16)), "mp_.mmap_threshold"); (9%N, (TApp "tmp" [(TAtom "iw_1.v9")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v8")), (Some (80)), "mp_.no_dyn_threshold")])].


End fn_glibc_malloc__dl_tunable_set_mmap_threshold.

Module fn_glibc_malloc__dl_tunable_set_mmaps_max.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 232%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 232%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v7"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

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
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (6%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v5")), (Some (72)), "mp_.n_mmaps_max"); (10%N, (TApp "tmp" [(TAtom "iw_1.v9")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v8")), (Some (80)), "mp_.no_dyn_threshold")])].


End fn_glibc_malloc__dl_tunable_set_mmaps_max.

Module fn_glibc_malloc__dl_tunable_set_top_pad.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 233%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 233%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v7"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

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
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (5%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v5")), (Some (8)), "mp_.top_pad"); (9%N, (TApp "tmp" [(TAtom "iw_1.v9")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v8")), (Some (80)), "mp_.no_dyn_threshold")])].


End fn_glibc_malloc__dl_tunable_set_top_pad.

Module fn_glibc_malloc__dl_tunable_set_perturb_byte.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 234%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 234%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v6"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

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
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (5%N, (TApp "tmp" [(TAtom "iw_1.v5")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v5")), (Some (0)), "opaque")])].


End fn_glibc_malloc__dl_tunable_set_perturb_byte.

Module fn_glibc_malloc__dl_tunable_set_trim_threshold.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 235%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 235%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v6"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

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
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (4%N, (TApp "tmp" [(TAtom "iw_1.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v5")), (Some (0)), "mp_.trim_threshold"); (8%N, (TApp "tmp" [(TAtom "iw_1.v8")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v7")), (Some (80)), "mp_.no_dyn_threshold")])].


End fn_glibc_malloc__dl_tunable_set_trim_threshold.

Module fn_glibc_malloc__dl_tunable_set_arena_max.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 236%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 236%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v7"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

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
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (5%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v5")), (Some (32)), "mp_.arena_max")])].


End fn_glibc_malloc__dl_tunable_set_arena_max.

Module fn_glibc_malloc__dl_tunable_set_arena_test.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 237%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 237%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v7"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

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
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (5%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v5")), (Some (24)), "mp_.arena_test")])].


End fn_glibc_malloc__dl_tunable_set_arena_test.

Module fn_glibc_malloc__dl_tunable_set_tcache_max.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 239%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 239%N)); ((TAtom "iw_1.iw_1.start"), (file_51, 1136%N)); ((TAtom "iw_1.iw_1.L4"), (file_51, 1139%N)); ((TAtom "iw_1.iw_1.L76"), (file_51, 1139%N)); ((TAtom "iw_1.iw_1.join"), (file_51, 4810%N)); ((TAtom "iw_1.iw_2.start"), (file_3, 79%N)); ((TAtom "iw_1.iw_2.iw_1.iw_1.L3"), (file_3, 79%N)); ((TAtom "iw_1.iw_2.iw_1.iw_1.L4"), (file_3, 79%N)); ((TAtom "iw_1.L43"), (file_51, 4810%N)); ((TAtom "iw_1.L51"), (file_51, 4819%N)); ((TAtom "iw_1.L58"), (file_51, 4820%N)); ((TAtom "iw_1.L60"), (file_51, 4821%N)); ((TAtom "iw_1.join"), (file_27, 239%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "req"); ((TAtom "iw_1.iw_1.v13"), "req"); ((TAtom "iw_1.iw_1.v5"), "req"); ((TAtom "iw_1.iw_1.v63"), "req"); ((TAtom "iw_1.iw_2.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_1.iw_2.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_1.iw_2.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_1.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_1.iw_2.iw_1.v2"), "__x"); ((TAtom "iw_1.iw_2.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_1.iw_2.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_1.iw_2.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_1.iw_2.iw_2.v0"), "__x"); ((TAtom "iw_1.iw_2.iw_2.v2"), "__x"); ((TAtom "iw_1.iw_2.v0"), "nb"); ((TAtom "iw_1.iw_2.v3"), "nb"); ((TAtom "iw_1.iw_2.v36"), "idx"); ((TAtom "iw_1.iw_2.v37"), "idx"); ((TAtom "iw_1.pr.1"), "tc_idx"); ((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v10"), "nb"); ((TAtom "iw_1.v12"), "nb"); ((TAtom "iw_1.v40"), "tc_idx"); ((TAtom "iw_1.v44"), "tc_idx"); ((TAtom "iw_1.v46"), "nb"); ((TAtom "iw_1.v47"), "tc_idx"); ((TAtom "iw_1.v5"), "value"); ((TAtom "iw_1.v54"), "tc_idx"); ((TAtom "iw_1.v61"), "tc_idx"); ((TAtom "iw_1.v65"), "tc_idx"); ((TAtom "iw_1.v69"), "nb"); ((TAtom "iw_1.v9"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.iw_1.start"), [(TAtom "iw_1.v6"); (TAtom "v4")]); ((TAtom "iw_1.iw_1.L4"), [(TAtom "v4")]); ((TAtom "iw_1.iw_1.L76"), [(TAtom "iw_1.iw_1.v23")]); ((TAtom "iw_1.iw_1.join"), []); ((TAtom "iw_1.iw_2.start"), [(TAtom "iw_1.v10")]); ((TAtom "iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_1.v10")]); ((TAtom "iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_1.v10")]); ((TAtom "iw_1.L43"), [(TAtom "iw_1.v10")]); ((TAtom "iw_1.L51"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.v10")]); ((TAtom "iw_1.L58"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.v10")]); ((TAtom "iw_1.L60"), [(TAtom "iw_1.v10")]); ((TAtom "iw_1.join"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_1.v6"); (TAtom "v4")]); ((TAtom "iw_1.iw_1.start"), [(TAtom "v4")]); ((TAtom "iw_1.iw_1.L4"), [(TAtom "iw_1.iw_1.v23")]); ((TAtom "iw_1.iw_1.L76"), [(TAtom "iw_1.iw_1.v83")]); ((TAtom "iw_1.iw_1.join"), [(TAtom "iw_1.v10"); (TAtom "iw_1.v40")]); ((TAtom "iw_1.iw_2.start"), [(TAtom "iw_1.v10")]); ((TAtom "iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_1.iw_2.iw_1.iw_1.v33"); (TAtom "iw_1.v10")]); ((TAtom "iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_1.iw_2.v38"); (TAtom "iw_1.v10")]); ((TAtom "iw_1.L43"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.v10")]); ((TAtom "iw_1.L51"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.v10")]); ((TAtom "iw_1.L58"), [(TAtom "iw_1.v10")]); ((TAtom "iw_1.L60"), []); ((TAtom "iw_1.join"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval")]); ((TAtom "iw_1.iw_1.start"), []); ((TAtom "iw_1.iw_1.L4"), []); ((TAtom "iw_1.iw_1.L76"), []); ((TAtom "iw_1.iw_1.join"), []); ((TAtom "iw_1.iw_2.start"), []); ((TAtom "iw_1.iw_2.iw_1.iw_1.L3"), []); ((TAtom "iw_1.iw_2.iw_1.iw_1.L4"), []); ((TAtom "iw_1.L43"), []); ((TAtom "iw_1.L51"), []); ((TAtom "iw_1.L58"), [(4%N, (TApp "tmp" [(TAtom "iw_1.v64")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v63")), (Some (112)), "mp_.tcache_small_bins")]); ((TAtom "iw_1.L60"), [(4%N, (TApp "tmp" [(TAtom "iw_1.v68")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v67")), (Some (120)), "mp_.tcache_max_bytes")]); ((TAtom "iw_1.join"), [])].


End fn_glibc_malloc__dl_tunable_set_tcache_max.

Module fn_glibc_malloc__dl_tunable_set_tcache_count.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 240%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 240%N)); ((TAtom "iw_1.L9"), (file_51, 4834%N)); ((TAtom "iw_1.join"), (file_27, 240%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v12"), "value"); ((TAtom "iw_1.v5"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L9"), [(TAtom "v4")]); ((TAtom "iw_1.join"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v4")]); ((TAtom "iw_1.L9"), []); ((TAtom "iw_1.join"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval")]); ((TAtom "iw_1.L9"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v11")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v10")), (Some (128)), "mp_.tcache_count")]); ((TAtom "iw_1.join"), [])].


End fn_glibc_malloc__dl_tunable_set_tcache_count.

Module fn_glibc_malloc__dl_tunable_set_hugetlb.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 242%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 242%N)); ((TAtom "iw_1.L20"), (file_51, 4889%N)); ((TAtom "iw_1.L21"), (file_51, 4892%N)); ((TAtom "iw_1.L36"), (file_51, 4899%N)); ((TAtom "iw_1.L39"), (file_51, 4903%N)); ((TAtom "iw_1.L54"), (file_51, 4904%N)); ((TAtom "iw_1.L55"), (file_51, 4904%N)); ((TAtom "iw_1.L47"), (file_51, 4906%N)); ((TAtom "iw_1.L40"), (file_51, 4914%N)); ((TAtom "iw_1.iw_2.L3"), (file_4, 76%N)); ((TAtom "iw_1.iw_2.L4"), (file_4, 75%N)); ((TAtom "iw_1.L30"), (file_51, 4921%N)); ((TAtom "iw_1.L80"), (file_51, 4922%N)); ((TAtom "iw_1.L86"), (file_51, 4922%N)); ((TAtom "iw_1.L87"), (file_51, 4922%N)); ((TAtom "iw_1.join"), (file_27, 242%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v1"), "_dl_thp_mode"); ((TAtom "iw_1.iw_2.pr.1"), "size"); ((TAtom "iw_1.iw_2.v1"), "size"); ((TAtom "iw_1.iw_2.v10"), "size"); ((TAtom "iw_1.iw_2.v5"), "size"); ((TAtom "iw_1.iw_3.v1"), "_dl_elf_thp_pagesize"); ((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v11"), "thp_mode"); ((TAtom "iw_1.v17"), "thp_mode"); ((TAtom "iw_1.v23"), "value"); ((TAtom "iw_1.v3"), "thp_mode"); ((TAtom "iw_1.v32"), "value"); ((TAtom "iw_1.v42"), "thp_mode"); ((TAtom "iw_1.v67"), "thp_mode"); ((TAtom "iw_1.v83"), "value"); ((TAtom "iw_1.v88"), "value"); ((TAtom "iw_1.v90"), "value"); ((TAtom "v0"), "valp"); ((TAtom "v3"), "valp"); ((TAtom "v4"), "value"); ((TAtom "v5"), "value")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L20"), []); ((TAtom "iw_1.L21"), [(TAtom "iw_1.iw_1.v1"); (TAtom "v4")]); ((TAtom "iw_1.L36"), [(TAtom "iw_1.iw_1.v1")]); ((TAtom "iw_1.L39"), []); ((TAtom "iw_1.L54"), []); ((TAtom "iw_1.L55"), []); ((TAtom "iw_1.L47"), []); ((TAtom "iw_1.L40"), [(TAtom "iw_1.iw_1.v1")]); ((TAtom "iw_1.iw_2.L3"), [(TAtom "iw_1.iw_2.v1"); (TAtom "iw_1.v75")]); ((TAtom "iw_1.iw_2.L4"), [(TAtom "iw_1.v75")]); ((TAtom "iw_1.L30"), [(TAtom "v4")]); ((TAtom "iw_1.L80"), [(TAtom "v4")]); ((TAtom "iw_1.L86"), [(TAtom "v4")]); ((TAtom "iw_1.L87"), []); ((TAtom "iw_1.join"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_1.iw_1.v1"); (TAtom "v4")]); ((TAtom "iw_1.L20"), []); ((TAtom "iw_1.L21"), [(TAtom "iw_1.iw_1.v1"); (TAtom "v4")]); ((TAtom "iw_1.L36"), [(TAtom "iw_1.iw_1.v1")]); ((TAtom "iw_1.L39"), []); ((TAtom "iw_1.L54"), [(TAtom "iw_1.v59")]); ((TAtom "iw_1.L55"), []); ((TAtom "iw_1.L47"), []); ((TAtom "iw_1.L40"), [(TAtom "iw_1.iw_2.v1"); (TAtom "iw_1.v75")]); ((TAtom "iw_1.iw_2.L3"), [(TAtom "iw_1.iw_2.v1"); (TAtom "iw_1.v75")]); ((TAtom "iw_1.iw_2.L4"), []); ((TAtom "iw_1.L30"), [(TAtom "v4")]); ((TAtom "iw_1.L80"), [(TAtom "v4")]); ((TAtom "iw_1.L86"), [(TAtom "v4")]); ((TAtom "iw_1.L87"), []); ((TAtom "iw_1.join"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "valp->numval"); (4%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v0")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.iw_1.v0")), (Some (0)), "opaque")]); ((TAtom "iw_1.L20"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v26")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v25")), (Some (40)), "mp_.thp_mode"); (7%N, (TApp "tmp" [(TAtom "iw_1.v28")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v27")), (Some (48)), "mp_.thp_pagesize")]); ((TAtom "iw_1.L21"), []); ((TAtom "iw_1.L36"), []); ((TAtom "iw_1.L39"), [(4%N, (TApp "tmp" [(TAtom "iw_1.v45")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v44")), (Some (40)), "mp_.thp_mode"); (8%N, (TApp "tmp" [(TAtom "iw_1.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v50")), (Some (40)), "mp_.thp_mode")]); ((TAtom "iw_1.L54"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v57")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v56")), (Some (40)), "mp_.thp_mode")]); ((TAtom "iw_1.L55"), []); ((TAtom "iw_1.L47"), [(4%N, (TApp "tmp" [(TAtom "iw_1.v63")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v62")), (Some (48)), "mp_.thp_pagesize")]); ((TAtom "iw_1.L40"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v66")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v65")), (Some (40)), "mp_.thp_mode")]); ((TAtom "iw_1.iw_2.L3"), []); ((TAtom "iw_1.iw_2.L4"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v75")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v74")), (Some (48)), "mp_.thp_pagesize")]); ((TAtom "iw_1.L30"), []); ((TAtom "iw_1.L80"), []); ((TAtom "iw_1.L86"), []); ((TAtom "iw_1.L87"), []); ((TAtom "iw_1.join"), [])].


End fn_glibc_malloc__dl_tunable_set_hugetlb.

Module fn___ptmalloc_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 248%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 268%N)); ((TAtom "iw_1.L0"), (file_51, 2791%N)); ((TAtom "iw_1.L12"), (file_51, 2801%N)); ((TAtom "iw_1.L18"), (file_51, 2801%N)); ((TAtom "iw_1.L19"), (file_51, 2801%N)); ((TAtom "iw_1.L28"), (file_51, 2801%N)); ((TAtom "iw_1.iw_2.join"), (file_51, 2801%N)); ((TAtom "iw_1.L29"), (file_51, 2801%N)); ((TAtom "iw_1.L37"), (file_51, 2801%N)); ((TAtom "iw_1.iw_3.join"), (file_51, 2801%N)); ((TAtom "iw_1.L38"), (file_51, 2801%N)); ((TAtom "iw_1.L13"), (file_51, 2806%N)); ((TAtom "iw_1.join"), (file_27, 260%N)); ((TAtom "L0"), (file_27, 261%N)); ((TAtom "L2"), (file_27, 264%N)); ((TAtom "iw_2.L4"), (file_51, 1677%N)); ((TAtom "iw_2.L5"), (file_51, 1683%N)); ((TAtom "iw_2.L7"), (file_51, 1688%N)); ((TAtom "iw_2.L26"), (file_51, 1690%N)); ((TAtom "iw_2.L28"), (file_51, 1692%N)); ((TAtom "L68"), (file_27, 281%N)); ((TAtom "L69"), (file_27, 281%N)); ((TAtom "L61"), (file_27, 287%N)); ((TAtom "L77"), (file_27, 288%N)); ((TAtom "L79"), (file_27, 289%N)); ((TAtom "L63"), (file_27, 248%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "buf"); ((TAtom "iw_1.iw_1.v10"), "buf"); ((TAtom "iw_1.iw_1.v11"), "buflen"); ((TAtom "iw_1.iw_1.v12"), "flags"); ((TAtom "iw_1.iw_1.v13"), "result"); ((TAtom "iw_1.iw_1.v15"), "old_errno"); ((TAtom "iw_1.iw_1.v16"), "result"); ((TAtom "iw_1.iw_1.v2"), "buflen"); ((TAtom "iw_1.iw_1.v4"), "flags"); ((TAtom "iw_1.iw_1.v8"), "__libc_errno"); ((TAtom "iw_1.iw_2.v0"), "__x"); ((TAtom "iw_1.iw_2.v2"), "__x"); ((TAtom "iw_1.iw_3.v0"), "__x"); ((TAtom "iw_1.iw_3.v2"), "__x"); ((TAtom "iw_1.iw_4.v10"), "ret"); ((TAtom "iw_1.iw_4.v13"), "ret"); ((TAtom "iw_1.iw_4.v14"), "ret"); ((TAtom "iw_1.iw_4.v6"), "ret"); ((TAtom "iw_1.iw_4.v7"), "ret"); ((TAtom "iw_1.iw_4.v8"), "ret"); ((TAtom "iw_1.iw_5.v10"), "ret"); ((TAtom "iw_1.iw_5.v13"), "ret"); ((TAtom "iw_1.iw_5.v14"), "ret"); ((TAtom "iw_1.iw_5.v6"), "ret"); ((TAtom "iw_1.iw_5.v7"), "ret"); ((TAtom "iw_1.iw_5.v8"), "ret"); ((TAtom "iw_1.v10"), "minimum_bits"); ((TAtom "iw_1.v11"), "maximum_bits"); ((TAtom "iw_1.v16"), "tcache_key"); ((TAtom "iw_1.v21"), "tcache_key"); ((TAtom "iw_1.v31"), "tcache_key"); ((TAtom "iw_1.v33"), "minimum_bits"); ((TAtom "iw_1.v40"), "tcache_key"); ((TAtom "iw_1.v42"), "maximum_bits"); ((TAtom "iw_1.v48"), "tcache_key"); ((TAtom "iw_1.v51"), "tcache_key"); ((TAtom "iw_1.v55"), "tcache_key"); ((TAtom "iw_1.v8"), "minimum_bits"); ((TAtom "iw_2.pr.1"), "i"); ((TAtom "iw_2.v0"), "av"); ((TAtom "iw_2.v10"), "av"); ((TAtom "iw_2.v12"), "i"); ((TAtom "iw_2.v18"), "bin"); ((TAtom "iw_2.v19"), "bin"); ((TAtom "iw_2.v21"), "bin"); ((TAtom "iw_2.v23"), "bin"); ((TAtom "iw_2.v24"), "i"); ((TAtom "iw_2.v25"), "i"); ((TAtom "iw_2.v29"), "av"); ((TAtom "iw_2.v34"), "av"); ((TAtom "iw_2.v38"), "av"); ((TAtom "iw_2.v40"), "av"); ((TAtom "iw_2.v8"), "i"); ((TAtom "iw_4.v0"), "value"); ((TAtom "iw_4.v7"), "value"); ((TAtom "v13"), "id"); ((TAtom "v15"), "ret"); ((TAtom "v18"), "id"); ((TAtom "v20"), "ret"); ((TAtom "v23"), "id"); ((TAtom "v25"), "ret"); ((TAtom "v28"), "id"); ((TAtom "v30"), "ret"); ((TAtom "v33"), "id"); ((TAtom "v35"), "ret"); ((TAtom "v38"), "id"); ((TAtom "v4"), "__libc_initial"); ((TAtom "v40"), "ret"); ((TAtom "v43"), "id"); ((TAtom "v45"), "ret"); ((TAtom "v48"), "id"); ((TAtom "v50"), "ret"); ((TAtom "v53"), "id"); ((TAtom "v55"), "ret"); ((TAtom "v58"), "id"); ((TAtom "v60"), "ret"); ((TAtom "v7"), "__always_fail_morecore"); ((TAtom "v81"), "id"); ((TAtom "v90"), "__always_fail_morecore")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_1.L12"); (TAtom "iw_2.L4")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "iw_1.L0"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L12"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L18"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L19"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L28"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.iw_2.join"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L29"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L37"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.iw_3.join"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L38"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L13"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.join"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "L0"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "L2"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L4"), [(TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L5"), [(TAtom "iw_2.pr.1"); (TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L7"), [(TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L26"), [(TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L28"), [(TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "L68"), []); ((TAtom "L69"), []); ((TAtom "L61"), []); ((TAtom "L77"), []); ((TAtom "L79"), []); ((TAtom "L63"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L0"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L12"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L18"), [(TAtom "iw_1.v25"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L19"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L28"), [(TAtom "iw_1.iw_2.v14"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.iw_2.join"), [(TAtom "iw_1.v34"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L29"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L37"), [(TAtom "iw_1.iw_3.v14"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.iw_3.join"), [(TAtom "iw_1.v43"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L38"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.L13"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_1.join"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "L0"), [(TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "L2"), [(TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L4"), [(TAtom "iw_2.pr.1"); (TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L5"), [(TAtom "iw_2.v25"); (TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L7"), [(TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L26"), [(TAtom "v10"); (TAtom "v12"); (TAtom "v17"); (TAtom "v22"); (TAtom "v27"); (TAtom "v32"); (TAtom "v37"); (TAtom "v42"); (TAtom "v47"); (TAtom "v52"); (TAtom "v57")]); ((TAtom "iw_2.L28"), []); ((TAtom "L68"), [(TAtom "v74")]); ((TAtom "L69"), []); ((TAtom "L61"), []); ((TAtom "L77"), []); ((TAtom "L79"), []); ((TAtom "L63"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(13%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v7")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.iw_1.v7")), (Some (0)), "opaque"); (17%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v14")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.iw_1.v14")), (Some (0)), "opaque")]); ((TAtom "iw_1.L0"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v6")), (Some (0)), "opaque")]); ((TAtom "iw_1.L12"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v15")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v15")), (Some (0)), "opaque")]); ((TAtom "iw_1.L18"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v20")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v20")), (Some (0)), "opaque")]); ((TAtom "iw_1.L19"), []); ((TAtom "iw_1.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v30")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v30")), (Some (0)), "opaque")]); ((TAtom "iw_1.iw_2.join"), []); ((TAtom "iw_1.L29"), []); ((TAtom "iw_1.L37"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v39")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v39")), (Some (0)), "opaque")]); ((TAtom "iw_1.iw_3.join"), []); ((TAtom "iw_1.L38"), []); ((TAtom "iw_1.L13"), [(5%N, (TApp "tmp" [(TAtom "iw_1.iw_4.v3")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.iw_4.v0")), (Some (8)), "tv.tv_nsec"); (7%N, (TApp "tmp" [(TAtom "iw_1.iw_4.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.iw_4.v0")), (Some (0)), "tv.tv_sec"); (18%N, (TApp "tmp" [(TAtom "iw_1.v46")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v46")), (Some (0)), "opaque"); (22%N, (TApp "tmp" [(TAtom "iw_1.v50")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v50")), (Some (0)), "opaque"); (28%N, (TApp "tmp" [(TAtom "iw_1.iw_5.v3")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.iw_5.v0")), (Some (8)), "tv.tv_nsec"); (30%N, (TApp "tmp" [(TAtom "iw_1.iw_5.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.iw_5.v0")), (Some (0)), "tv.tv_sec"); (42%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v49")), (Some (0)), "opaque")]); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 1), true, false, (Some (TAtom "v3")), (Some (0)), "opaque")]); ((TAtom "L0"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 1), false, true, (Some (TAtom "v6")), (Some (0)), "opaque")]); ((TAtom "L2"), [(3%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), false, true, (Some (TAtom "v8")), (Some (0)), "opaque")]); ((TAtom "iw_2.L4"), []); ((TAtom "iw_2.L5"), [(10%N, (TApp "tmp" [(TAtom "iw_2.v22")]), (0), (Some 8), false, true, (Some (TAtom "v10")), None, "opaque"); (12%N, (TApp "tmp" [(TAtom "iw_2.v20")]), (0), (Some 8), false, true, (Some (TAtom "v10")), None, "opaque")]); ((TAtom "iw_2.L7"), []); ((TAtom "iw_2.L26"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v35")]), (0), (Some 4), true, false, (Some (TAtom "v10")), (Some (4)), "main_arena.flags"); (5%N, (TApp "tmp" [(TAtom "iw_2.v35")]), (0), (Some 4), false, true, (Some (TAtom "v10")), (Some (4)), "main_arena.flags")]); ((TAtom "iw_2.L28"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), false, true, (Some (TAtom "v10")), (Some (8)), "main_arena.top"); (8%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (0)), "opaque"); (12%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 4), true, false, (Some (TAtom "v17")), (Some (0)), "opaque"); (16%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), true, false, (Some (TAtom "v22")), (Some (0)), "opaque"); (20%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v27")), (Some (0)), "opaque"); (24%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 4), true, false, (Some (TAtom "v32")), (Some (0)), "opaque"); (28%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v37")), (Some (0)), "opaque"); (32%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v42")), (Some (0)), "opaque"); (36%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v47")), (Some (0)), "opaque"); (40%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 8), true, false, (Some (TAtom "v52")), (Some (0)), "opaque"); (44%N, (TApp "tmp" [(TAtom "v57")]), (0), (Some 8), true, false, (Some (TAtom "v57")), (Some (0)), "opaque"); (48%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 8), true, false, (Some (TAtom "v64")), (Some (56)), "mp_.hp_pagesize")]); ((TAtom "L68"), [(3%N, (TApp "tmp" [(TAtom "v71")]), (0), (Some 8), true, false, (Some (TAtom "v70")), (Some (56)), "mp_.hp_pagesize")]); ((TAtom "L69"), []); ((TAtom "L61"), []); ((TAtom "L77"), [(3%N, (TApp "tmp" [(TAtom "v86")]), (0), (Some 8), true, false, (Some (TAtom "v85")), (Some (56)), "mp_.hp_pagesize"); (7%N, (TApp "tmp" [(TAtom "iw_4.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.v5")), (Some (16)), "mp_.mmap_threshold"); (11%N, (TApp "tmp" [(TAtom "iw_4.v9")]), (0), (Some 4), false, true, (Some (TAtom "iw_4.v8")), (Some (80)), "mp_.no_dyn_threshold")]); ((TAtom "L79"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 1), false, true, (Some (TAtom "v89")), (Some (0)), "opaque")]); ((TAtom "L63"), [])].


End fn___ptmalloc_init.

Module fn_glibc_malloc___libc_malloc2.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_51, 3065%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_51, 3069%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "ar_ptr"); ((TAtom "pr.2"), "ar_ptr"); ((TAtom "pr.3"), "ar_ptr"); ((TAtom "pr.4"), "victim"); ((TAtom "v0"), "bytes"); ((TAtom "v101"), "victim"); ((TAtom "v107"), "ar_ptr"); ((TAtom "v116"), "ar_ptr"); ((TAtom "v117"), "bytes"); ((TAtom "v118"), "ar_ptr"); ((TAtom "v119"), "ar_ptr"); ((TAtom "v120"), "bytes"); ((TAtom "v121"), "victim"); ((TAtom "v125"), "ar_ptr"); ((TAtom "v130"), "ar_ptr"); ((TAtom "v133"), "__futex"); ((TAtom "v137"), "__oldval"); ((TAtom "v14"), "__libc_single_threaded_internal"); ((TAtom "v143"), "__oldval"); ((TAtom "v155"), "__futex"); ((TAtom "v156"), "__futex"); ((TAtom "v157"), "__private"); ((TAtom "v161"), "victim"); ((TAtom "v167"), "victim"); ((TAtom "v17"), "bytes"); ((TAtom "v178"), "ar_ptr"); ((TAtom "v179"), "victim"); ((TAtom "v18"), "victim"); ((TAtom "v191"), "victim"); ((TAtom "v22"), "victim"); ((TAtom "v28"), "victim"); ((TAtom "v40"), "victim"); ((TAtom "v5"), "bytes"); ((TAtom "v52"), "victim"); ((TAtom "v58"), "thread_arena"); ((TAtom "v65"), "ar_ptr"); ((TAtom "v69"), "ar_ptr"); ((TAtom "v74"), "__futex"); ((TAtom "v75"), "__atg3_old"); ((TAtom "v76"), "__atg3_old"); ((TAtom "v91"), "__futex"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "bytes"); ((TAtom "v94"), "ar_ptr"); ((TAtom "v95"), "ar_ptr"); ((TAtom "v96"), "bytes"); ((TAtom "v97"), "victim")].

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


End fn_glibc_malloc___libc_malloc2.

Module fn___GI___libc_malloc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_51, 3102%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_51, 1136%N)); ((TAtom "iw_1.L4"), (file_51, 1139%N)); ((TAtom "iw_1.L76"), (file_51, 1139%N)); ((TAtom "iw_1.join"), (file_51, 3108%N)); ((TAtom "L26"), (file_51, 3110%N)); ((TAtom "L43"), (file_51, 3114%N)); ((TAtom "iw_2.start"), (file_51, 2879%N)); ((TAtom "iw_2.iw_1.L22"), (file_51, 2857%N)); ((TAtom "iw_2.iw_1.L38"), (file_51, 2860%N)); ((TAtom "iw_3.start"), (file_3, 79%N)); ((TAtom "iw_3.iw_1.iw_1.L3"), (file_3, 79%N)); ((TAtom "iw_3.iw_1.iw_1.L4"), (file_3, 79%N)); ((TAtom "iw_4.iw_1.L18"), (file_51, 2887%N)); ((TAtom "iw_4.iw_1.L25"), (file_51, 2888%N)); ((TAtom "iw_4.iw_1.L26"), (file_51, 2888%N)); ((TAtom "iw_4.iw_1.L19"), (file_51, 2892%N)); ((TAtom "iw_4.iw_1.join"), (file_51, 2919%N)); ((TAtom "iw_4.L18"), (file_51, 2919%N)); ((TAtom "iw_4.L19"), (file_51, 2919%N)); ((TAtom "iw_4.iw_2.start"), (file_51, 2851%N)); ((TAtom "iw_4.iw_2.L7"), (file_51, 2852%N)); ((TAtom "iw_4.iw_2.L8"), (file_51, 2854%N)); ((TAtom "iw_4.iw_2.L9"), (file_51, 2850%N)); ((TAtom "iw_4.iw_2.L22"), (file_51, 2857%N)); ((TAtom "iw_4.iw_2.L24"), (file_51, 2859%N)); ((TAtom "iw_4.iw_2.L38"), (file_51, 2860%N)); ((TAtom "iw_4.iw_2.L39"), (file_51, 2862%N)); ((TAtom "iw_4.iw_2.L40"), (file_51, 2864%N)); ((TAtom "iw_4.join"), (file_51, 3121%N)); ((TAtom "L72"), (file_51, 3122%N)); ((TAtom "L7"), (file_51, 3127%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "req"); ((TAtom "iw_1.v13"), "req"); ((TAtom "iw_1.v5"), "req"); ((TAtom "iw_1.v63"), "req"); ((TAtom "iw_2.iw_1.pr.1"), "e"); ((TAtom "iw_2.iw_1.v0"), "tc_idx"); ((TAtom "iw_2.iw_1.v10"), "mangled"); ((TAtom "iw_2.iw_1.v12"), "ep"); ((TAtom "iw_2.iw_1.v13"), "e"); ((TAtom "iw_2.iw_1.v14"), "ep"); ((TAtom "iw_2.iw_1.v17"), "ep"); ((TAtom "iw_2.iw_1.v2"), "ep"); ((TAtom "iw_2.iw_1.v21"), "e"); ((TAtom "iw_2.iw_1.v25"), "e"); ((TAtom "iw_2.iw_1.v4"), "mangled"); ((TAtom "iw_2.iw_1.v41"), "mangled"); ((TAtom "iw_2.iw_1.v43"), "ep"); ((TAtom "iw_2.iw_1.v44"), "e"); ((TAtom "iw_2.iw_1.v47"), "e"); ((TAtom "iw_2.iw_1.v52"), "ep"); ((TAtom "iw_2.iw_1.v53"), "ep"); ((TAtom "iw_2.iw_1.v56"), "e"); ((TAtom "iw_2.iw_1.v59"), "e"); ((TAtom "iw_2.iw_1.v68"), "tcache"); ((TAtom "iw_2.iw_1.v69"), "tc_idx"); ((TAtom "iw_2.iw_1.v75"), "e"); ((TAtom "iw_2.iw_1.v77"), "e"); ((TAtom "iw_2.v0"), "tc_idx"); ((TAtom "iw_2.v2"), "tc_idx"); ((TAtom "iw_2.v4"), "tcache"); ((TAtom "iw_2.v6"), "tc_idx"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.v2"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_2.v2"), "__x"); ((TAtom "iw_3.v0"), "nb"); ((TAtom "iw_3.v3"), "nb"); ((TAtom "iw_3.v36"), "idx"); ((TAtom "iw_3.v37"), "idx"); ((TAtom "iw_4.iw_1.pr.1"), "tep"); ((TAtom "iw_4.iw_1.pr.2"), "te"); ((TAtom "iw_4.iw_1.v0"), "nb"); ((TAtom "iw_4.iw_1.v10"), "tcache"); ((TAtom "iw_4.iw_1.v12"), "tc_idx"); ((TAtom "iw_4.iw_1.v14"), "tep"); ((TAtom "iw_4.iw_1.v16"), "tep"); ((TAtom "iw_4.iw_1.v17"), "te"); ((TAtom "iw_4.iw_1.v2"), "tc_idx"); ((TAtom "iw_4.iw_1.v21"), "te"); ((TAtom "iw_4.iw_1.v27"), "te"); ((TAtom "iw_4.iw_1.v37"), "nb"); ((TAtom "iw_4.iw_1.v4"), "mangled"); ((TAtom "iw_4.iw_1.v43"), "te"); ((TAtom "iw_4.iw_1.v44"), "te"); ((TAtom "iw_4.iw_1.v47"), "te"); ((TAtom "iw_4.iw_1.v51"), "te"); ((TAtom "iw_4.iw_1.v52"), "mangled"); ((TAtom "iw_4.iw_1.v54"), "demangled_ptr"); ((TAtom "iw_4.iw_1.v55"), "te"); ((TAtom "iw_4.iw_1.v56"), "tep"); ((TAtom "iw_4.iw_1.v6"), "demangled_ptr"); ((TAtom "iw_4.iw_2.pr.1"), "e"); ((TAtom "iw_4.iw_2.v0"), "tc_idx"); ((TAtom "iw_4.iw_2.v10"), "mangled"); ((TAtom "iw_4.iw_2.v12"), "ep"); ((TAtom "iw_4.iw_2.v13"), "e"); ((TAtom "iw_4.iw_2.v14"), "ep"); ((TAtom "iw_4.iw_2.v17"), "ep"); ((TAtom "iw_4.iw_2.v2"), "ep"); ((TAtom "iw_4.iw_2.v21"), "e"); ((TAtom "iw_4.iw_2.v25"), "e"); ((TAtom "iw_4.iw_2.v4"), "mangled"); ((TAtom "iw_4.iw_2.v41"), "mangled"); ((TAtom "iw_4.iw_2.v43"), "ep"); ((TAtom "iw_4.iw_2.v44"), "e"); ((TAtom "iw_4.iw_2.v47"), "e"); ((TAtom "iw_4.iw_2.v52"), "ep"); ((TAtom "iw_4.iw_2.v53"), "ep"); ((TAtom "iw_4.iw_2.v56"), "e"); ((TAtom "iw_4.iw_2.v59"), "e"); ((TAtom "iw_4.iw_2.v68"), "tcache"); ((TAtom "iw_4.iw_2.v69"), "tc_idx"); ((TAtom "iw_4.iw_2.v75"), "e"); ((TAtom "iw_4.iw_2.v77"), "e"); ((TAtom "iw_4.pr.1"), "mangled"); ((TAtom "iw_4.v0"), "tc_idx"); ((TAtom "iw_4.v10"), "entry"); ((TAtom "iw_4.v14"), "te"); ((TAtom "iw_4.v2"), "nb"); ((TAtom "iw_4.v20"), "nb"); ((TAtom "iw_4.v21"), "te"); ((TAtom "iw_4.v35"), "tc_idx"); ((TAtom "iw_4.v36"), "entry"); ((TAtom "iw_4.v37"), "mangled"); ((TAtom "iw_4.v6"), "mangled"); ((TAtom "iw_4.v8"), "nb"); ((TAtom "iw_4.v9"), "tc_idx"); ((TAtom "v0"), "bytes"); ((TAtom "v14"), "nb"); ((TAtom "v3"), "bytes"); ((TAtom "v4"), "nb"); ((TAtom "v42"), "tc_idx"); ((TAtom "v46"), "tc_idx"); ((TAtom "v54"), "tcache"); ((TAtom "v56"), "tc_idx"); ((TAtom "v63"), "tc_idx"); ((TAtom "v66"), "nb"); ((TAtom "v67"), "tc_idx"); ((TAtom "v69"), "tc_idx"); ((TAtom "v70"), "nb"); ((TAtom "v71"), "victim"); ((TAtom "v75"), "victim"); ((TAtom "v79"), "victim"); ((TAtom "v8"), "nb"); ((TAtom "v81"), "bytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_4.iw_1.L18")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "v0")]); ((TAtom "iw_1.L76"), [(TAtom "iw_1.v23"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.start"), [(TAtom "v42"); (TAtom "v57")]); ((TAtom "iw_2.iw_1.L22"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L38"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_3.start"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L4"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L18"), [(TAtom "iw_3.v38"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L25"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L26"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.join"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.start"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L7"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L8"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L9"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L22"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L24"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L38"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L39"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L40"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.join"), [(TAtom "iw_4.iw_1.v23"); (TAtom "v0")]); ((TAtom "L72"), [(TAtom "v71")]); ((TAtom "L7"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "iw_1.v23"); (TAtom "v0")]); ((TAtom "iw_1.L76"), [(TAtom "iw_1.v83"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v4"); (TAtom "v42")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v42"); (TAtom "v57")]); ((TAtom "iw_2.start"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L22"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L38"), []); ((TAtom "iw_3.start"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_3.iw_1.iw_1.v33"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L4"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v14"); (TAtom "iw_4.iw_1.v17"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L25"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_1.v38"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L26"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v51"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.join"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "iw_4.v31"); (TAtom "v0")]); ((TAtom "iw_4.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.start"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L7"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.v13"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L8"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.v21"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L9"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L22"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L24"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L38"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L39"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L40"), [(TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.join"), [(TAtom "v0"); (TAtom "v71")]); ((TAtom "L72"), []); ((TAtom "L7"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.L76"), []); ((TAtom "iw_1.join"), [(3%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v9")), (Some (120)), "mp_.tcache_max_bytes")]); ((TAtom "L26"), []); ((TAtom "L43"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v53")), (Some (0)), "opaque"); (7%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v54")), None, "opaque")]); ((TAtom "iw_2.start"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v3")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "iw_2.v8")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v4")), None, "opaque")]); ((TAtom "iw_2.iw_1.L22"), []); ((TAtom "iw_2.iw_1.L38"), [(2%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v13")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.iw_1.v13")), (Some (0)), "e->next"); (7%N, (TApp "tmp" [(TAtom "iw_2.v8")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v4")), None, "opaque"); (10%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v67")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.iw_1.v67")), (Some (0)), "opaque"); (14%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v71")]), (0), (Some 2), true, false, (Some (TAtom "iw_2.iw_1.v68")), None, "opaque"); (18%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v71")]), (0), (Some 2), false, true, (Some (TAtom "iw_2.iw_1.v68")), None, "opaque"); (21%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v76")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.iw_1.v13")), (Some (8)), "e->key")]); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_3.iw_1.iw_1.L4"), [(6%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v9")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.v9")), (Some (0)), "opaque"); (11%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v14")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.v10")), None, "opaque")]); ((TAtom "iw_4.iw_1.L18"), []); ((TAtom "iw_4.iw_1.L25"), [(3%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v30")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (-8)), "opaque")]); ((TAtom "iw_4.iw_1.L26"), []); ((TAtom "iw_4.iw_1.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.2")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (0)), "te->next")]); ((TAtom "iw_4.iw_1.join"), []); ((TAtom "iw_4.L18"), [(3%N, (TApp "tmp" [(TAtom "iw_4.v24")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (-8)), "opaque")]); ((TAtom "iw_4.L19"), []); ((TAtom "iw_4.iw_2.start"), []); ((TAtom "iw_4.iw_2.L7"), [(1%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)), "opaque")]); ((TAtom "iw_4.iw_2.L8"), [(3%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)), "opaque")]); ((TAtom "iw_4.iw_2.L9"), []); ((TAtom "iw_4.iw_2.L22"), []); ((TAtom "iw_4.iw_2.L24"), []); ((TAtom "iw_4.iw_2.L38"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (0)), "e->next"); (7%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)), "opaque")]); ((TAtom "iw_4.iw_2.L39"), [(4%N, (TApp "tmp" [(TAtom "iw_4.iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (0)), "e->next"); (12%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)), "opaque")]); ((TAtom "iw_4.iw_2.L40"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v67")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.v67")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v71")]), (0), (Some 2), true, false, (Some (TAtom "iw_4.iw_2.v68")), None, "opaque"); (10%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v71")]), (0), (Some 2), false, true, (Some (TAtom "iw_4.iw_2.v68")), None, "opaque"); (13%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v76")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (8)), "e->key")]); ((TAtom "iw_4.join"), []); ((TAtom "L72"), []); ((TAtom "L7"), [])].


End fn___GI___libc_malloc.

Module fn___GI___libc_free.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_51, 3138%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_51, 3142%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "mem"); ((TAtom "v103"), "tc_idx"); ((TAtom "v107"), "tc_idx"); ((TAtom "v11"), "mem"); ((TAtom "v115"), "tcache"); ((TAtom "v116"), "tc_idx"); ((TAtom "v123"), "p"); ((TAtom "v124"), "tc_idx"); ((TAtom "v126"), "size"); ((TAtom "v127"), "tc_idx"); ((TAtom "v131"), "size"); ((TAtom "v155"), "tcache"); ((TAtom "v156"), "tc_idx"); ((TAtom "v16"), "mem"); ((TAtom "v165"), "p"); ((TAtom "v166"), "tc_idx"); ((TAtom "v175"), "mem"); ((TAtom "v18"), "p"); ((TAtom "v192"), "p"); ((TAtom "v195"), "size"); ((TAtom "v20"), "p"); ((TAtom "v228"), "p"); ((TAtom "v231"), "size"); ((TAtom "v268"), "p"); ((TAtom "v27"), "size"); ((TAtom "v271"), "size"); ((TAtom "v300"), "size"); ((TAtom "v31"), "p"); ((TAtom "v322"), "p"); ((TAtom "v333"), "p"); ((TAtom "v336"), "size"); ((TAtom "v369"), "p"); ((TAtom "v372"), "size"); ((TAtom "v409"), "p"); ((TAtom "v412"), "size"); ((TAtom "v437"), "size"); ((TAtom "v469"), "p"); ((TAtom "v472"), "size"); ((TAtom "v5"), "mem"); ((TAtom "v50"), "size"); ((TAtom "v505"), "p"); ((TAtom "v508"), "size"); ((TAtom "v544"), "p"); ((TAtom "v547"), "size"); ((TAtom "v574"), "size"); ((TAtom "v58"), "p"); ((TAtom "v596"), "p"); ((TAtom "v60"), "e"); ((TAtom "v603"), "p"); ((TAtom "v606"), "size"); ((TAtom "v627"), "p"); ((TAtom "v629"), "size"); ((TAtom "v64"), "e"); ((TAtom "v655"), "size"); ((TAtom "v677"), "p"); ((TAtom "v679"), "p"); ((TAtom "v68"), "tcache_key"); ((TAtom "v681"), "size"); ((TAtom "v704"), "p"); ((TAtom "v706"), "size"); ((TAtom "v72"), "e"); ((TAtom "v728"), "size"); ((TAtom "v75"), "size"); ((TAtom "v757"), "p"); ((TAtom "v759"), "p"); ((TAtom "v760"), "size")].

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


End fn___GI___libc_free.

Module fn___libc_calloc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_51, 3539%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_51, 3544%N)); ((TAtom "L5"), (file_51, 3546%N)); ((TAtom "L41"), (file_51, 3551%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "req"); ((TAtom "iw_1.v13"), "req"); ((TAtom "iw_1.v5"), "req"); ((TAtom "iw_1.v63"), "req"); ((TAtom "iw_2.iw_1.pr.1"), "e"); ((TAtom "iw_2.iw_1.v0"), "tc_idx"); ((TAtom "iw_2.iw_1.v10"), "mangled"); ((TAtom "iw_2.iw_1.v12"), "ep"); ((TAtom "iw_2.iw_1.v13"), "e"); ((TAtom "iw_2.iw_1.v14"), "ep"); ((TAtom "iw_2.iw_1.v17"), "ep"); ((TAtom "iw_2.iw_1.v2"), "ep"); ((TAtom "iw_2.iw_1.v21"), "e"); ((TAtom "iw_2.iw_1.v25"), "e"); ((TAtom "iw_2.iw_1.v4"), "mangled"); ((TAtom "iw_2.iw_1.v41"), "mangled"); ((TAtom "iw_2.iw_1.v43"), "ep"); ((TAtom "iw_2.iw_1.v44"), "e"); ((TAtom "iw_2.iw_1.v47"), "e"); ((TAtom "iw_2.iw_1.v52"), "ep"); ((TAtom "iw_2.iw_1.v53"), "ep"); ((TAtom "iw_2.iw_1.v56"), "e"); ((TAtom "iw_2.iw_1.v59"), "e"); ((TAtom "iw_2.iw_1.v68"), "tcache"); ((TAtom "iw_2.iw_1.v69"), "tc_idx"); ((TAtom "iw_2.iw_1.v75"), "e"); ((TAtom "iw_2.iw_1.v77"), "e"); ((TAtom "iw_2.v0"), "tc_idx"); ((TAtom "iw_2.v2"), "tc_idx"); ((TAtom "iw_2.v4"), "tcache"); ((TAtom "iw_2.v6"), "tc_idx"); ((TAtom "iw_3.v0"), "p"); ((TAtom "iw_3.v12"), "nclears"); ((TAtom "iw_3.v14"), "d"); ((TAtom "iw_3.v15"), "clearsize"); ((TAtom "iw_3.v2"), "clearsize"); ((TAtom "iw_3.v21"), "nclears"); ((TAtom "iw_3.v24"), "d"); ((TAtom "iw_3.v26"), "d"); ((TAtom "iw_3.v28"), "d"); ((TAtom "iw_3.v30"), "d"); ((TAtom "iw_3.v31"), "nclears"); ((TAtom "iw_3.v35"), "d"); ((TAtom "iw_3.v36"), "nclears"); ((TAtom "iw_3.v44"), "nclears"); ((TAtom "iw_3.v46"), "d"); ((TAtom "iw_3.v48"), "d"); ((TAtom "iw_3.v5"), "p"); ((TAtom "iw_3.v51"), "d"); ((TAtom "iw_3.v52"), "nclears"); ((TAtom "iw_3.v56"), "d"); ((TAtom "iw_3.v57"), "nclears"); ((TAtom "iw_3.v62"), "d"); ((TAtom "iw_3.v7"), "clearsize"); ((TAtom "iw_3.v8"), "nclears"); ((TAtom "iw_4.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.v2"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_2.v0"), "__x"); ((TAtom "iw_4.iw_2.v2"), "__x"); ((TAtom "iw_4.v0"), "nb"); ((TAtom "iw_4.v3"), "nb"); ((TAtom "iw_4.v36"), "idx"); ((TAtom "iw_4.v37"), "idx"); ((TAtom "iw_5.iw_1.pr.1"), "tep"); ((TAtom "iw_5.iw_1.pr.2"), "te"); ((TAtom "iw_5.iw_1.v0"), "nb"); ((TAtom "iw_5.iw_1.v10"), "tcache"); ((TAtom "iw_5.iw_1.v12"), "tc_idx"); ((TAtom "iw_5.iw_1.v14"), "tep"); ((TAtom "iw_5.iw_1.v16"), "tep"); ((TAtom "iw_5.iw_1.v17"), "te"); ((TAtom "iw_5.iw_1.v2"), "tc_idx"); ((TAtom "iw_5.iw_1.v21"), "te"); ((TAtom "iw_5.iw_1.v27"), "te"); ((TAtom "iw_5.iw_1.v37"), "nb"); ((TAtom "iw_5.iw_1.v4"), "mangled"); ((TAtom "iw_5.iw_1.v43"), "te"); ((TAtom "iw_5.iw_1.v44"), "te"); ((TAtom "iw_5.iw_1.v47"), "te"); ((TAtom "iw_5.iw_1.v51"), "te"); ((TAtom "iw_5.iw_1.v52"), "mangled"); ((TAtom "iw_5.iw_1.v54"), "demangled_ptr"); ((TAtom "iw_5.iw_1.v55"), "te"); ((TAtom "iw_5.iw_1.v56"), "tep"); ((TAtom "iw_5.iw_1.v6"), "demangled_ptr"); ((TAtom "iw_5.iw_2.pr.1"), "e"); ((TAtom "iw_5.iw_2.v0"), "tc_idx"); ((TAtom "iw_5.iw_2.v10"), "mangled"); ((TAtom "iw_5.iw_2.v12"), "ep"); ((TAtom "iw_5.iw_2.v13"), "e"); ((TAtom "iw_5.iw_2.v14"), "ep"); ((TAtom "iw_5.iw_2.v17"), "ep"); ((TAtom "iw_5.iw_2.v2"), "ep"); ((TAtom "iw_5.iw_2.v21"), "e"); ((TAtom "iw_5.iw_2.v25"), "e"); ((TAtom "iw_5.iw_2.v4"), "mangled"); ((TAtom "iw_5.iw_2.v41"), "mangled"); ((TAtom "iw_5.iw_2.v43"), "ep"); ((TAtom "iw_5.iw_2.v44"), "e"); ((TAtom "iw_5.iw_2.v47"), "e"); ((TAtom "iw_5.iw_2.v52"), "ep"); ((TAtom "iw_5.iw_2.v53"), "ep"); ((TAtom "iw_5.iw_2.v56"), "e"); ((TAtom "iw_5.iw_2.v59"), "e"); ((TAtom "iw_5.iw_2.v68"), "tcache"); ((TAtom "iw_5.iw_2.v69"), "tc_idx"); ((TAtom "iw_5.iw_2.v75"), "e"); ((TAtom "iw_5.iw_2.v77"), "e"); ((TAtom "iw_5.pr.1"), "mangled"); ((TAtom "iw_5.v0"), "tc_idx"); ((TAtom "iw_5.v10"), "entry"); ((TAtom "iw_5.v14"), "te"); ((TAtom "iw_5.v2"), "nb"); ((TAtom "iw_5.v20"), "nb"); ((TAtom "iw_5.v21"), "te"); ((TAtom "iw_5.v35"), "tc_idx"); ((TAtom "iw_5.v36"), "entry"); ((TAtom "iw_5.v37"), "mangled"); ((TAtom "iw_5.v6"), "mangled"); ((TAtom "iw_5.v8"), "nb"); ((TAtom "iw_5.v9"), "tc_idx"); ((TAtom "v0"), "n"); ((TAtom "v10"), "bytes"); ((TAtom "v101"), "tc_idx"); ((TAtom "v108"), "tc_idx"); ((TAtom "v110"), "tc_idx"); ((TAtom "v142"), "nb"); ((TAtom "v143"), "tc_idx"); ((TAtom "v145"), "tc_idx"); ((TAtom "v146"), "nb"); ((TAtom "v147"), "mem"); ((TAtom "v151"), "mem"); ((TAtom "v155"), "mem"); ((TAtom "v156"), "mem"); ((TAtom "v171"), "bytes"); ((TAtom "v2"), "elem_size"); ((TAtom "v44"), "bytes"); ((TAtom "v48"), "bytes"); ((TAtom "v49"), "nb"); ((TAtom "v53"), "nb"); ((TAtom "v59"), "nb"); ((TAtom "v8"), "n"); ((TAtom "v87"), "tc_idx"); ((TAtom "v9"), "elem_size"); ((TAtom "v91"), "tc_idx"); ((TAtom "v99"), "tcache")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L41"), [(TAtom "v10")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v10")]); ((TAtom "L5"), []); ((TAtom "L41"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L5"), [(2%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 4), false, true, (Some (TAtom "v39")), (Some (0)), "opaque")]); ((TAtom "L41"), [])].


End fn___libc_calloc.

Module fn_glibc_malloc_malloc_printerr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_51, 5135%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_51, 5139%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "str"); ((TAtom "v4"), "str")].

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


End fn_glibc_malloc_malloc_printerr.

Module fn___internal_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_35, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_35, 41%N)); ((TAtom "L10"), (file_35, 41%N)); ((TAtom "L11"), (file_35, 43%N)); ((TAtom "L29"), (file_35, 43%N)); ((TAtom "L30"), (file_35, 43%N)); ((TAtom "L34"), (file_35, 43%N)); ((TAtom "L23"), (file_35, 44%N)); ((TAtom "L46"), (file_35, 48%N)); ((TAtom "L59"), (file_35, 48%N)); ((TAtom "L60"), (file_35, 48%N)); ((TAtom "L71"), (file_35, 48%N)); ((TAtom "L66"), (file_35, 49%N)); ((TAtom "L48"), (file_35, 53%N)); ((TAtom "L103"), (file_35, 57%N)); ((TAtom "L104"), (file_35, 57%N)); ((TAtom "L115"), (file_35, 57%N)); ((TAtom "L110"), (file_35, 58%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v101"), "__futex"); ((TAtom "v105"), "__oldval"); ((TAtom "v111"), "__oldval"); ((TAtom "v12"), "func"); ((TAtom "v123"), "__futex"); ((TAtom "v124"), "__futex"); ((TAtom "v125"), "__private"); ((TAtom "v2"), "arg"); ((TAtom "v25"), "__futex"); ((TAtom "v26"), "__atg3_old"); ((TAtom "v27"), "__atg3_old"); ((TAtom "v4"), "d"); ((TAtom "v42"), "__futex"); ((TAtom "v43"), "__futex"); ((TAtom "v44"), "listp"); ((TAtom "v45"), "new"); ((TAtom "v49"), "new"); ((TAtom "v57"), "__futex"); ((TAtom "v6"), "listp"); ((TAtom "v61"), "__oldval"); ((TAtom "v67"), "__oldval"); ((TAtom "v79"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__private"); ((TAtom "v84"), "func"); ((TAtom "v85"), "new"); ((TAtom "v87"), "func"); ((TAtom "v88"), "new"); ((TAtom "v91"), "arg"); ((TAtom "v92"), "new"); ((TAtom "v95"), "d"); ((TAtom "v96"), "new")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L103"); (TAtom "L59")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L46"), []); ((TAtom "L59"), [(TAtom "chk1"); (TAtom "v54")]); ((TAtom "L60"), [(TAtom "v54"); (TAtom "v61")]); ((TAtom "L71"), [(TAtom "v54")]); ((TAtom "L66"), []); ((TAtom "L48"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L103"), [(TAtom "chk7"); (TAtom "v98")]); ((TAtom "L104"), [(TAtom "v105"); (TAtom "v98")]); ((TAtom "L115"), [(TAtom "v98")]); ((TAtom "L110"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L46"), [(TAtom "chk1"); (TAtom "v54"); (TAtom "v58")]); ((TAtom "L59"), [(TAtom "chk1"); (TAtom "v54"); (TAtom "v61"); (TAtom "v62")]); ((TAtom "L60"), [(TAtom "v54")]); ((TAtom "L71"), []); ((TAtom "L66"), []); ((TAtom "L48"), [(TAtom "chk7"); (TAtom "v102"); (TAtom "v98")]); ((TAtom "L103"), [(TAtom "chk7"); (TAtom "v105"); (TAtom "v106"); (TAtom "v98")]); ((TAtom "L104"), [(TAtom "v98")]); ((TAtom "L115"), []); ((TAtom "L110"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 4), true, true, (Some (TAtom "v20")), (Some (0)), "opaque")]); ((TAtom "L29"), []); ((TAtom "L30"), []); ((TAtom "L34"), []); ((TAtom "L23"), []); ((TAtom "L46"), [(2%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), true, false, (Some (TAtom "v54")), (Some (0)), "opaque")]); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), true, true, (Some (TAtom "v54")), (Some (0)), "opaque")]); ((TAtom "L60"), []); ((TAtom "L71"), []); ((TAtom "L66"), []); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v86")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (8)), "new->func.cxa.fn"); (5%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (16)), "new->func.cxa.arg"); (8%N, (TApp "tmp" [(TAtom "v94")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (24)), "new->func.cxa.dso_handle"); (10%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (0)), "new->flavor"); (13%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, false, (Some (TAtom "v98")), (Some (0)), "opaque")]); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, true, (Some (TAtom "v98")), (Some (0)), "opaque")]); ((TAtom "L104"), []); ((TAtom "L115"), []); ((TAtom "L110"), [])].


End fn___internal_atexit.

Module fn___GI___cxa_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_35, 65%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_35, 68%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "arg"); ((TAtom "v4"), "d"); ((TAtom "v6"), "func"); ((TAtom "v7"), "arg"); ((TAtom "v8"), "d")].

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
  [((TAtom "start"), [])].


End fn___GI___cxa_atexit.

Module fn___new_exitfn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_35, 78%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_35, 86%N)); ((TAtom "L6"), (file_35, 89%N)); ((TAtom "L8"), (file_35, 91%N)); ((TAtom "L14"), (file_35, 84%N)); ((TAtom "L15"), (file_35, 93%N)); ((TAtom "L25"), (file_35, 84%N)); ((TAtom "L26"), (file_35, 94%N)); ((TAtom "L28"), (file_35, 97%N)); ((TAtom "L47"), (file_35, 101%N)); ((TAtom "L17"), (file_35, 84%N)); ((TAtom "L63"), (file_35, 104%N)); ((TAtom "L64"), (file_35, 104%N)); ((TAtom "L56"), (file_35, 108%N)); ((TAtom "L70"), (file_35, 110%N)); ((TAtom "L78"), (file_35, 110%N)); ((TAtom "L79"), (file_35, 111%N)); ((TAtom "L88"), (file_35, 115%N)); ((TAtom "L72"), (file_35, 81%N)); ((TAtom "L100"), (file_35, 122%N)); ((TAtom "L57"), (file_35, 129%N)); ((TAtom "L58"), (file_35, 83%N)); ((TAtom "L121"), (file_35, 136%N)); ((TAtom "L123"), (file_35, 140%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "p"); ((TAtom "pr.2"), "p"); ((TAtom "pr.3"), "l"); ((TAtom "pr.4"), "r"); ((TAtom "pr.5"), "r"); ((TAtom "pr.6"), "i"); ((TAtom "pr.7"), "i"); ((TAtom "pr.8"), "i"); ((TAtom "v0"), "listp"); ((TAtom "v10"), "__exit_funcs_done"); ((TAtom "v103"), "p"); ((TAtom "v107"), "p"); ((TAtom "v109"), "r"); ((TAtom "v110"), "p"); ((TAtom "v112"), "l"); ((TAtom "v114"), "i"); ((TAtom "v116"), "r"); ((TAtom "v117"), "l"); ((TAtom "v119"), "i"); ((TAtom "v12"), "listp"); ((TAtom "v124"), "r"); ((TAtom "v128"), "r"); ((TAtom "v13"), "l"); ((TAtom "v130"), "__new_exitfn_called"); ((TAtom "v131"), "__new_exitfn_called"); ((TAtom "v132"), "r"); ((TAtom "v18"), "l"); ((TAtom "v22"), "l"); ((TAtom "v24"), "i"); ((TAtom "v29"), "i"); ((TAtom "v34"), "l"); ((TAtom "v36"), "i"); ((TAtom "v43"), "i"); ((TAtom "v44"), "i"); ((TAtom "v48"), "i"); ((TAtom "v51"), "l"); ((TAtom "v53"), "l"); ((TAtom "v54"), "l"); ((TAtom "v55"), "l"); ((TAtom "v59"), "l"); ((TAtom "v65"), "i"); ((TAtom "v73"), "p"); ((TAtom "v80"), "l"); ((TAtom "v87"), "p"); ((TAtom "v91"), "p"); ((TAtom "v95"), "p"); ((TAtom "v96"), "listp"); ((TAtom "v98"), "listp"); ((TAtom "v99"), "p")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L14"); (TAtom "L25")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk1"); (TAtom "v0")]); ((TAtom "L15"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L28"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L47"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0")]); ((TAtom "L17"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L63"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L64"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L70"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L78"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L88"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v87")]); ((TAtom "L72"), [(TAtom "v20")]); ((TAtom "L100"), [(TAtom "pr.2"); (TAtom "v20")]); ((TAtom "L57"), [(TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v20")]); ((TAtom "L58"), [(TAtom "v20")]); ((TAtom "L121"), [(TAtom "pr.5")]); ((TAtom "L123"), [(TAtom "pr.5")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v13")]); ((TAtom "L14"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L15"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v24")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30"); (TAtom "v37")]); ((TAtom "L28"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L47"), [(TAtom "chk1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v55")]); ((TAtom "L17"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L63"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21"); (TAtom "v67")]); ((TAtom "L64"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L70"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L78"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v87")]); ((TAtom "L88"), [(TAtom "v20"); (TAtom "v87")]); ((TAtom "L72"), [(TAtom "pr.2"); (TAtom "v20")]); ((TAtom "L100"), [(TAtom "v108"); (TAtom "v20")]); ((TAtom "L57"), [(TAtom "v116"); (TAtom "v20")]); ((TAtom "L58"), [(TAtom "pr.5")]); ((TAtom "L121"), [(TAtom "pr.5")]); ((TAtom "L123"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 1), true, false, (Some (TAtom "v9")), (Some (0)), "opaque")]); ((TAtom "L6"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "opaque")]); ((TAtom "L14"), []); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), (Some (8)), "l->idx")]); ((TAtom "L25"), []); ((TAtom "L26"), [(5%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), None, "opaque")]); ((TAtom "L28"), []); ((TAtom "L47"), [(2%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 8), false, true, (Some (TAtom "pr.3")), (Some (8)), "l->idx"); (4%N, (TApp "tmp" [(TAtom "pr.3")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), (Some (0)), "l->next")]); ((TAtom "L17"), []); ((TAtom "L63"), []); ((TAtom "L64"), []); ((TAtom "L56"), []); ((TAtom "L70"), []); ((TAtom "L78"), []); ((TAtom "L79"), []); ((TAtom "L88"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)), "opaque"); (3%N, (TApp "tmp" [(TAtom "v87")]), (0), (Some 8), false, true, (Some (TAtom "v87")), (Some (0)), "p->next"); (5%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)), "opaque")]); ((TAtom "L72"), []); ((TAtom "L100"), [(3%N, (TApp "tmp" [(TAtom "v111")]), (0), (Some 8), false, true, (Some (TAtom "pr.2")), (Some (8)), "p->idx")]); ((TAtom "L57"), [(6%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 8), false, true, (Some (TAtom "pr.3")), (Some (8)), "l->idx")]); ((TAtom "L58"), []); ((TAtom "L121"), [(1%N, (TApp "tmp" [(TAtom "pr.5")]), (0), (Some 8), false, true, (Some (TAtom "pr.5")), (Some (0)), "r->flavor"); (4%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 8), true, false, (Some (TAtom "v129")), (Some (0)), "opaque"); (7%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 8), false, true, (Some (TAtom "v129")), (Some (0)), "opaque")]); ((TAtom "L123"), [])].


End fn___new_exitfn.

Module fn_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_33, 40%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_33, 46%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "func")].

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


End fn_atexit.

Module fn___fpending.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_32, 20%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_32, 23%N)); ((TAtom "L2"), (file_32, 24%N)); ((TAtom "L3"), (file_32, 26%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L3"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L2"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (32)), "fp->_wide_data->_IO_write_ptr"); (6%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (9%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (24)), "fp->_wide_data->_IO_write_base")]); ((TAtom "L3"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (5%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base")])].


End fn___fpending.

End HiAtexitSrc01.

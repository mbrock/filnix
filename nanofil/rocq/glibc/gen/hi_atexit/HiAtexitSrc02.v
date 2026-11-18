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
Module HiAtexitSrc02.

Module fn___libc_calloc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_54, 3539%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_54, 3544%N)); ((TAtom "L5"), (file_54, 3546%N)); ((TAtom "L41"), (file_54, 3551%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "req"); ((TAtom "iw_1.v13"), "req"); ((TAtom "iw_1.v5"), "req"); ((TAtom "iw_1.v63"), "req"); ((TAtom "iw_2.iw_1.pr.1"), "e"); ((TAtom "iw_2.iw_1.v0"), "tc_idx"); ((TAtom "iw_2.iw_1.v10"), "mangled"); ((TAtom "iw_2.iw_1.v12"), "ep"); ((TAtom "iw_2.iw_1.v13"), "e"); ((TAtom "iw_2.iw_1.v14"), "ep"); ((TAtom "iw_2.iw_1.v17"), "ep"); ((TAtom "iw_2.iw_1.v2"), "ep"); ((TAtom "iw_2.iw_1.v21"), "e"); ((TAtom "iw_2.iw_1.v25"), "e"); ((TAtom "iw_2.iw_1.v4"), "mangled"); ((TAtom "iw_2.iw_1.v41"), "mangled"); ((TAtom "iw_2.iw_1.v43"), "ep"); ((TAtom "iw_2.iw_1.v44"), "e"); ((TAtom "iw_2.iw_1.v47"), "e"); ((TAtom "iw_2.iw_1.v52"), "ep"); ((TAtom "iw_2.iw_1.v53"), "ep"); ((TAtom "iw_2.iw_1.v56"), "e"); ((TAtom "iw_2.iw_1.v59"), "e"); ((TAtom "iw_2.iw_1.v68"), "tcache"); ((TAtom "iw_2.iw_1.v69"), "tc_idx"); ((TAtom "iw_2.iw_1.v75"), "e"); ((TAtom "iw_2.iw_1.v77"), "e"); ((TAtom "iw_2.v0"), "tc_idx"); ((TAtom "iw_2.v2"), "tc_idx"); ((TAtom "iw_2.v4"), "tcache"); ((TAtom "iw_2.v6"), "tc_idx"); ((TAtom "iw_3.v0"), "p"); ((TAtom "iw_3.v12"), "nclears"); ((TAtom "iw_3.v14"), "d"); ((TAtom "iw_3.v15"), "clearsize"); ((TAtom "iw_3.v2"), "clearsize"); ((TAtom "iw_3.v21"), "nclears"); ((TAtom "iw_3.v24"), "d"); ((TAtom "iw_3.v26"), "d"); ((TAtom "iw_3.v28"), "d"); ((TAtom "iw_3.v30"), "d"); ((TAtom "iw_3.v31"), "nclears"); ((TAtom "iw_3.v35"), "d"); ((TAtom "iw_3.v36"), "nclears"); ((TAtom "iw_3.v44"), "nclears"); ((TAtom "iw_3.v46"), "d"); ((TAtom "iw_3.v48"), "d"); ((TAtom "iw_3.v5"), "p"); ((TAtom "iw_3.v51"), "d"); ((TAtom "iw_3.v52"), "nclears"); ((TAtom "iw_3.v56"), "d"); ((TAtom "iw_3.v57"), "nclears"); ((TAtom "iw_3.v62"), "d"); ((TAtom "iw_3.v7"), "clearsize"); ((TAtom "iw_3.v8"), "nclears"); ((TAtom "iw_4.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.v2"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_2.v0"), "__x"); ((TAtom "iw_4.iw_2.v2"), "__x"); ((TAtom "iw_4.v0"), "nb"); ((TAtom "iw_4.v3"), "nb"); ((TAtom "iw_4.v36"), "idx"); ((TAtom "iw_4.v37"), "idx"); ((TAtom "iw_5.iw_1.pr.1"), "tep"); ((TAtom "iw_5.iw_1.pr.2"), "te"); ((TAtom "iw_5.iw_1.v0"), "nb"); ((TAtom "iw_5.iw_1.v10"), "tcache"); ((TAtom "iw_5.iw_1.v12"), "tc_idx"); ((TAtom "iw_5.iw_1.v14"), "tep"); ((TAtom "iw_5.iw_1.v16"), "tep"); ((TAtom "iw_5.iw_1.v17"), "te"); ((TAtom "iw_5.iw_1.v2"), "tc_idx"); ((TAtom "iw_5.iw_1.v21"), "te"); ((TAtom "iw_5.iw_1.v27"), "te"); ((TAtom "iw_5.iw_1.v37"), "nb"); ((TAtom "iw_5.iw_1.v4"), "mangled"); ((TAtom "iw_5.iw_1.v43"), "te"); ((TAtom "iw_5.iw_1.v44"), "te"); ((TAtom "iw_5.iw_1.v47"), "te"); ((TAtom "iw_5.iw_1.v51"), "te"); ((TAtom "iw_5.iw_1.v52"), "mangled"); ((TAtom "iw_5.iw_1.v54"), "demangled_ptr"); ((TAtom "iw_5.iw_1.v55"), "te"); ((TAtom "iw_5.iw_1.v56"), "tep"); ((TAtom "iw_5.iw_1.v6"), "demangled_ptr"); ((TAtom "iw_5.iw_2.pr.1"), "e"); ((TAtom "iw_5.iw_2.v0"), "tc_idx"); ((TAtom "iw_5.iw_2.v10"), "mangled"); ((TAtom "iw_5.iw_2.v12"), "ep"); ((TAtom "iw_5.iw_2.v13"), "e"); ((TAtom "iw_5.iw_2.v14"), "ep"); ((TAtom "iw_5.iw_2.v17"), "ep"); ((TAtom "iw_5.iw_2.v2"), "ep"); ((TAtom "iw_5.iw_2.v21"), "e"); ((TAtom "iw_5.iw_2.v25"), "e"); ((TAtom "iw_5.iw_2.v4"), "mangled"); ((TAtom "iw_5.iw_2.v41"), "mangled"); ((TAtom "iw_5.iw_2.v43"), "ep"); ((TAtom "iw_5.iw_2.v44"), "e"); ((TAtom "iw_5.iw_2.v47"), "e"); ((TAtom "iw_5.iw_2.v52"), "ep"); ((TAtom "iw_5.iw_2.v53"), "ep"); ((TAtom "iw_5.iw_2.v56"), "e"); ((TAtom "iw_5.iw_2.v59"), "e"); ((TAtom "iw_5.iw_2.v68"), "tcache"); ((TAtom "iw_5.iw_2.v69"), "tc_idx"); ((TAtom "iw_5.iw_2.v75"), "e"); ((TAtom "iw_5.iw_2.v77"), "e"); ((TAtom "iw_5.pr.1"), "mangled"); ((TAtom "iw_5.v0"), "tc_idx"); ((TAtom "iw_5.v10"), "entry"); ((TAtom "iw_5.v14"), "te"); ((TAtom "iw_5.v2"), "nb"); ((TAtom "iw_5.v20"), "nb"); ((TAtom "iw_5.v21"), "te"); ((TAtom "iw_5.v35"), "tc_idx"); ((TAtom "iw_5.v36"), "entry"); ((TAtom "iw_5.v37"), "mangled"); ((TAtom "iw_5.v6"), "mangled"); ((TAtom "iw_5.v8"), "nb"); ((TAtom "iw_5.v9"), "tc_idx"); ((TAtom "v0"), "n"); ((TAtom "v10"), "bytes"); ((TAtom "v101"), "tc_idx"); ((TAtom "v108"), "tc_idx"); ((TAtom "v110"), "tc_idx"); ((TAtom "v142"), "nb"); ((TAtom "v143"), "tc_idx"); ((TAtom "v145"), "tc_idx"); ((TAtom "v146"), "nb"); ((TAtom "v147"), "mem"); ((TAtom "v151"), "mem"); ((TAtom "v155"), "mem"); ((TAtom "v156"), "mem"); ((TAtom "v171"), "bytes"); ((TAtom "v2"), "elem_size"); ((TAtom "v44"), "bytes"); ((TAtom "v48"), "bytes"); ((TAtom "v49"), "nb"); ((TAtom "v53"), "nb"); ((TAtom "v59"), "nb"); ((TAtom "v8"), "n"); ((TAtom "v87"), "tc_idx"); ((TAtom "v9"), "elem_size"); ((TAtom "v91"), "tc_idx"); ((TAtom "v99"), "tcache")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v39"), "&__libc_errno", 0)); ((TAtom "v0"), ((TAtom "v0"), "n", 0)); ((TAtom "v10"), ((TAtom "v10"), "bytes", 0)); ((TAtom "v2"), ((TAtom "v2"), "elem_size", 0)); ((TAtom "v39"), ((TAtom "v39"), "&__libc_errno", 0))].

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
Definition source : option (string * N) := Some (file_54, 5135%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_54, 5139%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "str"); ((TAtom "v4"), "str")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "str", 0))].

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
Definition source : option (string * N) := Some (file_38, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_38, 41%N)); ((TAtom "L10"), (file_38, 41%N)); ((TAtom "L11"), (file_38, 43%N)); ((TAtom "L29"), (file_38, 43%N)); ((TAtom "L30"), (file_38, 43%N)); ((TAtom "L34"), (file_38, 43%N)); ((TAtom "L23"), (file_38, 44%N)); ((TAtom "L46"), (file_38, 48%N)); ((TAtom "L59"), (file_38, 48%N)); ((TAtom "L60"), (file_38, 48%N)); ((TAtom "L71"), (file_38, 48%N)); ((TAtom "L66"), (file_38, 49%N)); ((TAtom "L48"), (file_38, 53%N)); ((TAtom "L103"), (file_38, 57%N)); ((TAtom "L104"), (file_38, 57%N)); ((TAtom "L115"), (file_38, 57%N)); ((TAtom "L110"), (file_38, 58%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v101"), "__futex"); ((TAtom "v105"), "__oldval"); ((TAtom "v111"), "__oldval"); ((TAtom "v12"), "func"); ((TAtom "v123"), "__futex"); ((TAtom "v124"), "__futex"); ((TAtom "v125"), "__private"); ((TAtom "v2"), "arg"); ((TAtom "v25"), "__futex"); ((TAtom "v26"), "__atg3_old"); ((TAtom "v27"), "__atg3_old"); ((TAtom "v4"), "d"); ((TAtom "v42"), "__futex"); ((TAtom "v43"), "__futex"); ((TAtom "v44"), "listp"); ((TAtom "v45"), "new"); ((TAtom "v49"), "new"); ((TAtom "v57"), "__futex"); ((TAtom "v6"), "listp"); ((TAtom "v61"), "__oldval"); ((TAtom "v67"), "__oldval"); ((TAtom "v79"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__private"); ((TAtom "v84"), "func"); ((TAtom "v85"), "new"); ((TAtom "v87"), "func"); ((TAtom "v88"), "new"); ((TAtom "v91"), "arg"); ((TAtom "v92"), "new"); ((TAtom "v95"), "d"); ((TAtom "v96"), "new")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v20"), "&__exit_funcs_lock", 0)); ((TAtom "chk1"), ((TAtom "v54"), "&__exit_funcs_lock", 0)); ((TAtom "chk2"), ((TAtom "v54"), "&__exit_funcs_lock", 0)); ((TAtom "chk3"), ((TAtom "v45"), "new", 8)); ((TAtom "chk4"), ((TAtom "v45"), "new", 16)); ((TAtom "chk5"), ((TAtom "v45"), "new", 24)); ((TAtom "chk6"), ((TAtom "v45"), "new", 0)); ((TAtom "chk7"), ((TAtom "v98"), "&__exit_funcs_lock", 0)); ((TAtom "chk8"), ((TAtom "v98"), "&__exit_funcs_lock", 0)); ((TAtom "v0"), ((TAtom "v0"), "func", 0)); ((TAtom "v105"), ((TAtom "v105"), "__oldval", 0)); ((TAtom "v2"), ((TAtom "v2"), "arg", 0)); ((TAtom "v20"), ((TAtom "v20"), "&__exit_funcs_lock", 0)); ((TAtom "v27"), ((TAtom "v27"), "__atg3_old", 0)); ((TAtom "v4"), ((TAtom "v4"), "d", 0)); ((TAtom "v45"), ((TAtom "v45"), "new", 0)); ((TAtom "v54"), ((TAtom "v54"), "&__exit_funcs_lock", 0)); ((TAtom "v6"), ((TAtom "v6"), "listp", 0)); ((TAtom "v61"), ((TAtom "v61"), "__oldval", 0)); ((TAtom "v86"), ((TAtom "v45"), "new", 8)); ((TAtom "v90"), ((TAtom "v45"), "new", 16)); ((TAtom "v94"), ((TAtom "v45"), "new", 24)); ((TAtom "v98"), ((TAtom "v98"), "&__exit_funcs_lock", 0))].

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
Definition source : option (string * N) := Some (file_38, 65%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_38, 68%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "arg"); ((TAtom "v4"), "d"); ((TAtom "v6"), "func"); ((TAtom "v7"), "arg"); ((TAtom "v8"), "d")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "func", 0)); ((TAtom "v2"), ((TAtom "v2"), "arg", 0)); ((TAtom "v4"), ((TAtom "v4"), "d", 0)); ((TAtom "v9"), ((TAtom "v9"), "&__exit_funcs", 0))].

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
Definition source : option (string * N) := Some (file_38, 78%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_38, 86%N)); ((TAtom "L6"), (file_38, 89%N)); ((TAtom "L8"), (file_38, 91%N)); ((TAtom "L14"), (file_38, 84%N)); ((TAtom "L15"), (file_38, 93%N)); ((TAtom "L25"), (file_38, 84%N)); ((TAtom "L26"), (file_38, 94%N)); ((TAtom "L28"), (file_38, 97%N)); ((TAtom "L47"), (file_38, 101%N)); ((TAtom "L17"), (file_38, 84%N)); ((TAtom "L63"), (file_38, 104%N)); ((TAtom "L64"), (file_38, 104%N)); ((TAtom "L56"), (file_38, 108%N)); ((TAtom "L70"), (file_38, 110%N)); ((TAtom "L78"), (file_38, 110%N)); ((TAtom "L79"), (file_38, 111%N)); ((TAtom "L88"), (file_38, 115%N)); ((TAtom "L72"), (file_38, 81%N)); ((TAtom "L100"), (file_38, 122%N)); ((TAtom "L57"), (file_38, 129%N)); ((TAtom "L58"), (file_38, 83%N)); ((TAtom "L121"), (file_38, 136%N)); ((TAtom "L123"), (file_38, 140%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "p"); ((TAtom "pr.2"), "p"); ((TAtom "pr.3"), "l"); ((TAtom "pr.4"), "r"); ((TAtom "pr.5"), "r"); ((TAtom "pr.6"), "i"); ((TAtom "pr.7"), "i"); ((TAtom "pr.8"), "i"); ((TAtom "v0"), "listp"); ((TAtom "v10"), "__exit_funcs_done"); ((TAtom "v103"), "p"); ((TAtom "v107"), "p"); ((TAtom "v109"), "r"); ((TAtom "v110"), "p"); ((TAtom "v112"), "l"); ((TAtom "v114"), "i"); ((TAtom "v116"), "r"); ((TAtom "v117"), "l"); ((TAtom "v119"), "i"); ((TAtom "v12"), "listp"); ((TAtom "v124"), "r"); ((TAtom "v128"), "r"); ((TAtom "v13"), "l"); ((TAtom "v130"), "__new_exitfn_called"); ((TAtom "v131"), "__new_exitfn_called"); ((TAtom "v132"), "r"); ((TAtom "v18"), "l"); ((TAtom "v22"), "l"); ((TAtom "v24"), "i"); ((TAtom "v29"), "i"); ((TAtom "v34"), "l"); ((TAtom "v36"), "i"); ((TAtom "v43"), "i"); ((TAtom "v44"), "i"); ((TAtom "v48"), "i"); ((TAtom "v51"), "l"); ((TAtom "v53"), "l"); ((TAtom "v54"), "l"); ((TAtom "v55"), "l"); ((TAtom "v59"), "l"); ((TAtom "v65"), "i"); ((TAtom "v73"), "p"); ((TAtom "v80"), "l"); ((TAtom "v87"), "p"); ((TAtom "v91"), "p"); ((TAtom "v95"), "p"); ((TAtom "v96"), "listp"); ((TAtom "v98"), "listp"); ((TAtom "v99"), "p")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v9"), "&__exit_funcs_done", 0)); ((TAtom "chk1"), ((TAtom "v0"), "listp", 0)); ((TAtom "chk10"), ((TAtom "pr.3"), "l", 8)); ((TAtom "chk11"), ((TAtom "pr.5"), "r", 0)); ((TAtom "chk12"), ((TAtom "v129"), "&__new_exitfn_called", 0)); ((TAtom "chk13"), ((TAtom "v129"), "&__new_exitfn_called", 0)); ((TAtom "chk2"), ((TAtom "pr.3"), "l", 8)); ((TAtom "chk3"), ((TAtom "v39"), "v39", 0)); ((TAtom "chk4"), ((TAtom "pr.3"), "l", 8)); ((TAtom "chk5"), ((TAtom "pr.3"), "l", 0)); ((TAtom "chk6"), ((TAtom "v0"), "listp", 0)); ((TAtom "chk7"), ((TAtom "v87"), "p", 0)); ((TAtom "chk8"), ((TAtom "v0"), "listp", 0)); ((TAtom "chk9"), ((TAtom "pr.2"), "p", 8)); ((TAtom "pr.1"), ((TAtom "pr.1"), "p", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "p", 0)); ((TAtom "pr.3"), ((TAtom "pr.3"), "l", 0)); ((TAtom "pr.5"), ((TAtom "pr.5"), "r", 0)); ((TAtom "pr.6"), ((TAtom "pr.6"), "i", 0)); ((TAtom "pr.7"), ((TAtom "pr.7"), "i", 0)); ((TAtom "pr.8"), ((TAtom "pr.8"), "i", 0)); ((TAtom "v0"), ((TAtom "v0"), "listp", 0)); ((TAtom "v10"), ((TAtom "v10"), "__exit_funcs_done", 0)); ((TAtom "v108"), ((TAtom "pr.2"), "p", 16)); ((TAtom "v111"), ((TAtom "pr.2"), "p", 8)); ((TAtom "v113"), ((TAtom "pr.3"), "l", 16)); ((TAtom "v116"), ((TAtom "v116"), "r", 0)); ((TAtom "v118"), ((TAtom "pr.3"), "l", 8)); ((TAtom "v129"), ((TAtom "v129"), "&__new_exitfn_called", 0)); ((TAtom "v13"), ((TAtom "v13"), "l", 0)); ((TAtom "v130"), ((TAtom "v130"), "__new_exitfn_called", 0)); ((TAtom "v131"), ((TAtom "v131"), "__new_exitfn_called", 0)); ((TAtom "v23"), ((TAtom "pr.3"), "l", 8)); ((TAtom "v24"), ((TAtom "v24"), "i", 0)); ((TAtom "v35"), ((TAtom "pr.3"), "l", 16)); ((TAtom "v52"), ((TAtom "pr.3"), "l", 8)); ((TAtom "v55"), ((TAtom "v55"), "l", 0)); ((TAtom "v87"), ((TAtom "v87"), "p", 0)); ((TAtom "v9"), ((TAtom "v9"), "&__exit_funcs_done", 0))].

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
Definition source : option (string * N) := Some (file_36, 40%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_36, 46%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "func")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "v0"), ((TAtom "v0"), "func", 0))].

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
Definition source : option (string * N) := Some (file_35, 20%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_35, 23%N)); ((TAtom "L2"), (file_35, 24%N)); ((TAtom "L3"), (file_35, 26%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v9"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk2"), ((TAtom "v11"), "v11", 32)); ((TAtom "chk4"), ((TAtom "v16"), "v16", 24)); ((TAtom "chk5"), ((TAtom "v0"), "fp", 40)); ((TAtom "chk6"), ((TAtom "v0"), "fp", 32)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v10"), ((TAtom "v0"), "fp", 160)); ((TAtom "v12"), ((TAtom "v11"), "v11", 32)); ((TAtom "v17"), ((TAtom "v16"), "v16", 24)); ((TAtom "v25"), ((TAtom "v0"), "fp", 40)); ((TAtom "v28"), ((TAtom "v0"), "fp", 32)); ((TAtom "v6"), ((TAtom "v0"), "fp", 192))].

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

Module fn__IO_ferror.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_42, 30%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_42, 35%N)); ((TAtom "L6"), (file_42, 36%N)); ((TAtom "L8"), (file_42, 37%N)); ((TAtom "L29"), (file_42, 37%N)); ((TAtom "L40"), (file_42, 37%N)); ((TAtom "L41"), (file_42, 37%N)); ((TAtom "L34"), (file_42, 37%N)); ((TAtom "L35"), (file_42, 37%N)); ((TAtom "L60"), (file_42, 37%N)); ((TAtom "L84"), (file_42, 37%N)); ((TAtom "L85"), (file_42, 37%N)); ((TAtom "L89"), (file_42, 37%N)); ((TAtom "L78"), (file_42, 37%N)); ((TAtom "L61"), (file_42, 37%N)); ((TAtom "L24"), (file_42, 38%N)); ((TAtom "L121"), (file_42, 39%N)); ((TAtom "L130"), (file_42, 39%N)); ((TAtom "L131"), (file_42, 39%N)); ((TAtom "L124"), (file_42, 39%N)); ((TAtom "L125"), (file_42, 39%N)); ((TAtom "L147"), (file_42, 39%N)); ((TAtom "L168"), (file_42, 39%N)); ((TAtom "L169"), (file_42, 39%N)); ((TAtom "L180"), (file_42, 39%N)); ((TAtom "L148"), (file_42, 39%N)); ((TAtom "L116"), (file_42, 40%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v103"), "__self"); ((TAtom "v104"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "result"); ((TAtom "v117"), "fp"); ((TAtom "v128"), "__libc_single_threaded_internal"); ((TAtom "v132"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v161"), "fp"); ((TAtom "v163"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v17"), "fp"); ((TAtom "v170"), "__oldval"); ((TAtom "v176"), "__oldval"); ((TAtom "v188"), "__futex"); ((TAtom "v189"), "__futex"); ((TAtom "v190"), "__private"); ((TAtom "v191"), "fp"); ((TAtom "v197"), "result"); ((TAtom "v25"), "fp"); ((TAtom "v33"), "__self"); ((TAtom "v38"), "__libc_single_threaded_internal"); ((TAtom "v42"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v59"), "__self"); ((TAtom "v63"), "fp"); ((TAtom "v68"), "__self"); ((TAtom "v73"), "fp"); ((TAtom "v75"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__atg3_old"); ((TAtom "v82"), "__atg3_old"); ((TAtom "v9"), "fp"); ((TAtom "v97"), "__futex"); ((TAtom "v98"), "__futex"); ((TAtom "v99"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 116)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk10"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk11"), ((TAtom "v65"), "v65", 8)); ((TAtom "chk13"), ((TAtom "v75"), "__futex", 0)); ((TAtom "chk14"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk15"), ((TAtom "v101"), "v101", 8)); ((TAtom "chk17"), ((TAtom "v106"), "v106", 4)); ((TAtom "chk18"), ((TAtom "v106"), "v106", 4)); ((TAtom "chk19"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk2"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk21"), ((TAtom "v127"), "&__libc_single_threaded_internal", 0)); ((TAtom "chk22"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk23"), ((TAtom "v134"), "v134", 4)); ((TAtom "chk24"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk25"), ((TAtom "v142"), "v142", 8)); ((TAtom "chk26"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk27"), ((TAtom "v146"), "v146", 0)); ((TAtom "chk28"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk29"), ((TAtom "v152"), "v152", 4)); ((TAtom "chk3"), ((TAtom "v37"), "&__libc_single_threaded_internal", 0)); ((TAtom "chk31"), ((TAtom "v158"), "v158", 8)); ((TAtom "chk32"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk33"), ((TAtom "v163"), "__futex", 0)); ((TAtom "chk34"), ((TAtom "v163"), "__futex", 0)); ((TAtom "chk36"), ((TAtom "v193"), "v193", 4)); ((TAtom "chk37"), ((TAtom "v193"), "v193", 4)); ((TAtom "chk4"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk5"), ((TAtom "v44"), "v44", 8)); ((TAtom "chk6"), ((TAtom "v0"), "fp", 136)); ((TAtom "chk7"), ((TAtom "v54"), "v54", 0)); ((TAtom "chk9"), ((TAtom "v57"), "v57", 8)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v10"), ((TAtom "v0"), "fp", 116)); ((TAtom "v100"), ((TAtom "v0"), "fp", 136)); ((TAtom "v102"), ((TAtom "v101"), "v101", 8)); ((TAtom "v105"), ((TAtom "v0"), "fp", 136)); ((TAtom "v107"), ((TAtom "v106"), "v106", 4)); ((TAtom "v113"), ((TAtom "v113"), "result", 0)); ((TAtom "v127"), ((TAtom "v127"), "&__libc_single_threaded_internal", 0)); ((TAtom "v128"), ((TAtom "v128"), "__libc_single_threaded_internal", 0)); ((TAtom "v133"), ((TAtom "v0"), "fp", 136)); ((TAtom "v135"), ((TAtom "v134"), "v134", 4)); ((TAtom "v141"), ((TAtom "v0"), "fp", 136)); ((TAtom "v143"), ((TAtom "v142"), "v142", 8)); ((TAtom "v151"), ((TAtom "v0"), "fp", 136)); ((TAtom "v153"), ((TAtom "v152"), "v152", 4)); ((TAtom "v157"), ((TAtom "v0"), "fp", 136)); ((TAtom "v159"), ((TAtom "v158"), "v158", 8)); ((TAtom "v163"), ((TAtom "v163"), "__futex", 0)); ((TAtom "v170"), ((TAtom "v170"), "__oldval", 0)); ((TAtom "v192"), ((TAtom "v0"), "fp", 136)); ((TAtom "v194"), ((TAtom "v193"), "v193", 4)); ((TAtom "v33"), ((TAtom "v33"), "__self", 0)); ((TAtom "v37"), ((TAtom "v37"), "&__libc_single_threaded_internal", 0)); ((TAtom "v38"), ((TAtom "v38"), "__libc_single_threaded_internal", 0)); ((TAtom "v43"), ((TAtom "v0"), "fp", 136)); ((TAtom "v45"), ((TAtom "v44"), "v44", 8)); ((TAtom "v53"), ((TAtom "v0"), "fp", 136)); ((TAtom "v58"), ((TAtom "v57"), "v57", 8)); ((TAtom "v64"), ((TAtom "v0"), "fp", 136)); ((TAtom "v66"), ((TAtom "v65"), "v65", 8)); ((TAtom "v74"), ((TAtom "v0"), "fp", 136)); ((TAtom "v75"), ((TAtom "v75"), "__futex", 0)); ((TAtom "v82"), ((TAtom "v82"), "__atg3_old", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L168")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163"); (TAtom "v170")]); ((TAtom "L180"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L148"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L116"), [(TAtom "v113")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v49")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113"); (TAtom "v137")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v167")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v170"); (TAtom "v171")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L180"), [(TAtom "v113")]); ((TAtom "L148"), [(TAtom "v113")]); ((TAtom "L116"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "fp->_flags2")]); ((TAtom "L6"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 1), true, false, (Some (TAtom "v37")), (Some (0)), "opaque")]); ((TAtom "L40"), [(2%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), true, false, (Some (TAtom "v44")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L41"), []); ((TAtom "L34"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), false, true, (Some (TAtom "v54")), (Some (0)), "fp->_lock->lock"); (5%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (8%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), false, true, (Some (TAtom "v57")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L35"), [(2%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v65")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L60"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (3%N, (TApp "tmp" [(TAtom "v75")]), (0), (Some 4), true, true, (Some (TAtom "v75")), (Some (0)), "opaque")]); ((TAtom "L84"), []); ((TAtom "L85"), []); ((TAtom "L89"), []); ((TAtom "L78"), [(2%N, (TApp "tmp" [(TAtom "v100")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 8), false, true, (Some (TAtom "v101")), (Some (8)), "fp->_lock->owner")]); ((TAtom "L61"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), true, false, (Some (TAtom "v106")), (Some (4)), "fp->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), false, true, (Some (TAtom "v106")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L24"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 1), true, false, (Some (TAtom "v127")), (Some (0)), "opaque")]); ((TAtom "L130"), [(2%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v135")]), (0), (Some 4), true, false, (Some (TAtom "v134")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L131"), []); ((TAtom "L124"), [(2%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v143")]), (0), (Some 8), false, true, (Some (TAtom "v142")), (Some (8)), "fp->_lock->owner"); (7%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (9%N, (TApp "tmp" [(TAtom "v146")]), (0), (Some 4), false, true, (Some (TAtom "v146")), (Some (0)), "fp->_lock->lock")]); ((TAtom "L125"), [(2%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (5%N, (TApp "tmp" [(TAtom "v153")]), (0), (Some 4), true, false, (Some (TAtom "v152")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L147"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), false, true, (Some (TAtom "v158")), (Some (8)), "fp->_lock->owner"); (6%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (8%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, false, (Some (TAtom "v163")), (Some (0)), "opaque")]); ((TAtom "L168"), [(1%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, true, (Some (TAtom "v163")), (Some (0)), "opaque")]); ((TAtom "L169"), []); ((TAtom "L180"), []); ((TAtom "L148"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)), "fp->_lock"); (4%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), true, false, (Some (TAtom "v193")), (Some (4)), "fp->_lock->cnt"); (7%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), false, true, (Some (TAtom "v193")), (Some (4)), "fp->_lock->cnt")]); ((TAtom "L116"), [])].


End fn__IO_ferror.

Module fn___GI__IO_file_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_43, 66%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_43, 71%N)); ((TAtom "L12"), (file_43, 74%N)); ((TAtom "iw_1.L10"), (file_33, 1049%N)); ((TAtom "iw_1.join"), (file_43, 74%N)); ((TAtom "L13"), (file_43, 74%N)); ((TAtom "L5"), (file_43, 76%N)); ((TAtom "L26"), (file_43, 81%N)); ((TAtom "L42"), (file_43, 81%N)); ((TAtom "L43"), (file_43, 81%N)); ((TAtom "L48"), (file_43, 79%N)); ((TAtom "L49"), (file_43, 79%N)); ((TAtom "L33"), (file_43, 84%N)); ((TAtom "L28"), (file_43, 87%N)); ((TAtom "L65"), (file_43, 87%N)); ((TAtom "L66"), (file_43, 87%N)); ((TAtom "L59"), (file_43, 88%N)); ((TAtom "L7"), (file_43, 69%N)); ((TAtom "L76"), (file_43, 93%N)); ((TAtom "L78"), (file_43, 94%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "size"); ((TAtom "pr.2"), "size"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v39"), "__dev_major"); ((TAtom "v40"), "__dev_major"); ((TAtom "v44"), "__dev_major"); ((TAtom "v50"), "fp"); ((TAtom "v56"), "fp"); ((TAtom "v73"), "size"); ((TAtom "v74"), "size"); ((TAtom "v75"), "p"); ((TAtom "v79"), "p"); ((TAtom "v8"), "fp"); ((TAtom "v87"), "fp"); ((TAtom "v88"), "p"); ((TAtom "v89"), "p"); ((TAtom "v90"), "size")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 112)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 216)); ((TAtom "chk2"), ((TAtom "v16"), "v16", 144)); ((TAtom "chk4"), ((TAtom "v4"), "&st", 24)); ((TAtom "chk5"), ((TAtom "v4"), "&st", 40)); ((TAtom "chk6"), ((TAtom "v0"), "fp", 112)); ((TAtom "chk7"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk8"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk9"), ((TAtom "v4"), "&st", 56)); ((TAtom "iw_1.v4"), ((TAtom "iw_1.v4"), "ptr", 0)); ((TAtom "iw_1.v7"), ((TAtom "iw_1.v7"), "&__io_vtables", 0)); ((TAtom "iw_1.v9"), ((TAtom "iw_1.v9"), "offset", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "size", 0)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v15"), ((TAtom "v0"), "fp", 216)); ((TAtom "v18"), ((TAtom "v16"), "v16", 144)); ((TAtom "v29"), ((TAtom "v4"), "&st", 24)); ((TAtom "v37"), ((TAtom "v4"), "&st", 40)); ((TAtom "v39"), ((TAtom "v39"), "__dev_major", 0)); ((TAtom "v4"), ((TAtom "v4"), "&st", 0)); ((TAtom "v51"), ((TAtom "v0"), "fp", 112)); ((TAtom "v62"), ((TAtom "v4"), "&st", 56)); ((TAtom "v67"), ((TAtom "v4"), "&st", 56)); ((TAtom "v72"), ((TAtom "v4"), "&st", 56)); ((TAtom "v73"), ((TAtom "v73"), "size", 0)); ((TAtom "v75"), ((TAtom "v75"), "p", 0)); ((TAtom "v9"), ((TAtom "v0"), "fp", 112))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L7"), [(TAtom "v0")]); ((TAtom "L76"), []); ((TAtom "L78"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v54")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v69")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "v0"); (TAtom "v73")]); ((TAtom "L7"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")]); ((TAtom "L76"), []); ((TAtom "L78"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (144)), "opaque")]); ((TAtom "L13"), []); ((TAtom "L5"), [(2%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 4), true, false, (Some (TAtom "v4")), (Some (24)), "st.st_mode")]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (40)), "st.st_rdev")]); ((TAtom "L42"), []); ((TAtom "L43"), []); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")]); ((TAtom "L49"), []); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags"); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)), "st.st_blksize")]); ((TAtom "L65"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)), "st.st_blksize")]); ((TAtom "L66"), []); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)), "st.st_blksize")]); ((TAtom "L7"), []); ((TAtom "L76"), []); ((TAtom "L78"), [])].


End fn___GI__IO_file_doallocate.

Module fn__IO_file_close_maybe_unlink.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_44, 129%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_44, 133%N)); ((TAtom "L5"), (file_44, 134%N)); ((TAtom "L7"), (file_44, 136%N)); ((TAtom "L23"), (file_44, 136%N)); ((TAtom "L24"), (file_44, 136%N)); ((TAtom "L16"), (file_44, 138%N)); ((TAtom "L31"), (file_44, 138%N)); ((TAtom "L32"), (file_44, 138%N)); ((TAtom "L17"), (file_44, 139%N)); ((TAtom "L81"), (file_44, 139%N)); ((TAtom "L86"), (file_44, 139%N)); ((TAtom "L92"), (file_44, 139%N)); ((TAtom "L87"), (file_44, 139%N)); ((TAtom "L110"), (file_44, 139%N)); ((TAtom "L118"), (file_44, 139%N)); ((TAtom "L82"), (file_44, 139%N)); ((TAtom "L74"), (file_44, 159%N)); ((TAtom "iw_1.L10"), (file_33, 1049%N)); ((TAtom "iw_1.join"), (file_44, 159%N)); ((TAtom "L147"), (file_44, 162%N)); ((TAtom "L155"), (file_44, 162%N)); ((TAtom "L148"), (file_44, 167%N)); ((TAtom "L161"), (file_44, 168%N)); ((TAtom "L163"), (file_44, 159%N)); ((TAtom "iw_2.L10"), (file_33, 1049%N)); ((TAtom "iw_2.join"), (file_44, 169%N)); ((TAtom "L191"), (file_44, 169%N)); ((TAtom "L192"), (file_44, 169%N)); ((TAtom "L179"), (file_44, 169%N)); ((TAtom "L18"), (file_44, 132%N)); ((TAtom "L202"), (file_44, 177%N)); ((TAtom "iw_3.L10"), (file_33, 1049%N)); ((TAtom "iw_3.join"), (file_44, 177%N)); ((TAtom "L204"), (file_44, 177%N)); ((TAtom "L221"), (file_44, 183%N)); ((TAtom "L228"), (file_44, 184%N)); ((TAtom "L230"), (file_44, 185%N)); ((TAtom "L223"), (file_44, 189%N)); ((TAtom "L277"), (file_44, 194%N)); ((TAtom "L279"), (file_44, 197%N)); ((TAtom "L299"), (file_44, 201%N)); ((TAtom "L300"), (file_44, 201%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "vtable"); ((TAtom "iw_3.v13"), "offset"); ((TAtom "iw_3.v18"), "vtable"); ((TAtom "iw_3.v3"), "vtable"); ((TAtom "iw_3.v4"), "ptr"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v9"), "offset"); ((TAtom "pr.1"), "flush_status"); ((TAtom "pr.2"), "flush_status"); ((TAtom "pr.3"), "flush_status"); ((TAtom "pr.4"), "flush_status"); ((TAtom "pr.5"), "o"); ((TAtom "v0"), "fp"); ((TAtom "v112"), "fp"); ((TAtom "v120"), "fp"); ((TAtom "v124"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v145"), "fp"); ((TAtom "v146"), "o"); ((TAtom "v150"), "o"); ((TAtom "v158"), "__libc_errno"); ((TAtom "v160"), "flush_status"); ((TAtom "v164"), "fp"); ((TAtom "v167"), "o"); ((TAtom "v168"), "fp"); ((TAtom "v171"), "fp"); ((TAtom "v177"), "o"); ((TAtom "v181"), "fp"); ((TAtom "v187"), "fp"); ((TAtom "v188"), "o"); ((TAtom "v19"), "fp"); ((TAtom "v194"), "__libc_errno"); ((TAtom "v199"), "flush_status"); ((TAtom "v2"), "unlink"); ((TAtom "v200"), "fp"); ((TAtom "v205"), "fp"); ((TAtom "v212"), "fp"); ((TAtom "v218"), "fp"); ((TAtom "v220"), "close_status"); ((TAtom "v224"), "fp"); ((TAtom "v231"), "fp"); ((TAtom "v239"), "fp"); ((TAtom "v240"), "fp"); ((TAtom "v241"), "fp"); ((TAtom "v245"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v25"), "fp"); ((TAtom "v252"), "fp"); ((TAtom "v256"), "fp"); ((TAtom "v260"), "fp"); ((TAtom "v264"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v267"), "fp"); ((TAtom "v269"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v273"), "fp"); ((TAtom "v275"), "fp"); ((TAtom "v280"), "unlink"); ((TAtom "v281"), "fp"); ((TAtom "v282"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v291"), "fp"); ((TAtom "v294"), "fp"); ((TAtom "v301"), "close_status"); ((TAtom "v302"), "close_status"); ((TAtom "v303"), "flush_status"); ((TAtom "v34"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v42"), "fp"); ((TAtom "v45"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v73"), "flush_status"); ((TAtom "v77"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v83"), "fp"); ((TAtom "v88"), "fp"); ((TAtom "v94"), "fp"); ((TAtom "v97"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 112)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk10"), ((TAtom "v60"), "v60", 32)); ((TAtom "chk12"), ((TAtom "v65"), "v65", 24)); ((TAtom "chk15"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk16"), ((TAtom "v0"), "fp", 8)); ((TAtom "chk18"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk19"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk20"), ((TAtom "v122"), "v122", 0)); ((TAtom "chk22"), ((TAtom "v126"), "v126", 8)); ((TAtom "chk23"), ((TAtom "v0"), "fp", 216)); ((TAtom "chk24"), ((TAtom "v141"), "v141", 72)); ((TAtom "chk26"), ((TAtom "v157"), "&__libc_errno", 0)); ((TAtom "chk27"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk28"), ((TAtom "v0"), "fp", 88)); ((TAtom "chk3"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk30"), ((TAtom "v0"), "fp", 216)); ((TAtom "chk31"), ((TAtom "v183"), "v183", 128)); ((TAtom "chk33"), ((TAtom "v193"), "&__libc_errno", 0)); ((TAtom "chk34"), ((TAtom "v0"), "fp", 116)); ((TAtom "chk35"), ((TAtom "v0"), "fp", 216)); ((TAtom "chk36"), ((TAtom "v214"), "v214", 136)); ((TAtom "chk38"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk39"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk4"), ((TAtom "v0"), "fp", 32)); ((TAtom "chk40"), ((TAtom "v233"), "v233", 72)); ((TAtom "chk41"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk42"), ((TAtom "v243"), "v243", 16)); ((TAtom "chk43"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk44"), ((TAtom "v247"), "v247", 0)); ((TAtom "chk45"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk46"), ((TAtom "v250"), "v250", 8)); ((TAtom "chk47"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk49"), ((TAtom "v258"), "v258", 32)); ((TAtom "chk50"), ((TAtom "v254"), "v254", 24)); ((TAtom "chk51"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk52"), ((TAtom "v262"), "v262", 40)); ((TAtom "chk53"), ((TAtom "v0"), "fp", 24)); ((TAtom "chk54"), ((TAtom "v0"), "fp", 8)); ((TAtom "chk55"), ((TAtom "v0"), "fp", 16)); ((TAtom "chk56"), ((TAtom "v0"), "fp", 40)); ((TAtom "chk57"), ((TAtom "v0"), "fp", 32)); ((TAtom "chk58"), ((TAtom "v0"), "fp", 48)); ((TAtom "chk59"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk60"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk61"), ((TAtom "v0"), "fp", 112)); ((TAtom "chk62"), ((TAtom "v0"), "fp", 144)); ((TAtom "chk7"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk8"), ((TAtom "v55"), "v55", 24)); ((TAtom "iw_1.v4"), ((TAtom "iw_1.v4"), "ptr", 0)); ((TAtom "iw_1.v7"), ((TAtom "iw_1.v7"), "&__io_vtables", 0)); ((TAtom "iw_1.v9"), ((TAtom "iw_1.v9"), "offset", 0)); ((TAtom "iw_2.v4"), ((TAtom "iw_2.v4"), "ptr", 0)); ((TAtom "iw_2.v7"), ((TAtom "iw_2.v7"), "&__io_vtables", 0)); ((TAtom "iw_2.v9"), ((TAtom "iw_2.v9"), "offset", 0)); ((TAtom "iw_3.v4"), ((TAtom "iw_3.v4"), "ptr", 0)); ((TAtom "iw_3.v7"), ((TAtom "iw_3.v7"), "&__io_vtables", 0)); ((TAtom "iw_3.v9"), ((TAtom "iw_3.v9"), "offset", 0)); ((TAtom "pr.3"), ((TAtom "pr.3"), "flush_status", 0)); ((TAtom "pr.5"), ((TAtom "pr.5"), "o", 0)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v113"), ((TAtom "v0"), "fp", 192)); ((TAtom "v121"), ((TAtom "v0"), "fp", 160)); ((TAtom "v127"), ((TAtom "v126"), "v126", 8)); ((TAtom "v140"), ((TAtom "v0"), "fp", 216)); ((TAtom "v143"), ((TAtom "v141"), "v141", 72)); ((TAtom "v146"), ((TAtom "v146"), "o", 0)); ((TAtom "v157"), ((TAtom "v157"), "&__libc_errno", 0)); ((TAtom "v158"), ((TAtom "v158"), "__libc_errno", 0)); ((TAtom "v169"), ((TAtom "v0"), "fp", 88)); ((TAtom "v172"), ((TAtom "v0"), "fp", 72)); ((TAtom "v177"), ((TAtom "v177"), "o", 0)); ((TAtom "v182"), ((TAtom "v0"), "fp", 216)); ((TAtom "v185"), ((TAtom "v183"), "v183", 128)); ((TAtom "v193"), ((TAtom "v193"), "&__libc_errno", 0)); ((TAtom "v194"), ((TAtom "v194"), "__libc_errno", 0)); ((TAtom "v2"), ((TAtom "v2"), "unlink", 0)); ((TAtom "v206"), ((TAtom "v0"), "fp", 116)); ((TAtom "v213"), ((TAtom "v0"), "fp", 216)); ((TAtom "v216"), ((TAtom "v214"), "v214", 136)); ((TAtom "v220"), ((TAtom "v220"), "close_status", 0)); ((TAtom "v225"), ((TAtom "v0"), "fp", 192)); ((TAtom "v232"), ((TAtom "v0"), "fp", 160)); ((TAtom "v234"), ((TAtom "v233"), "v233", 72)); ((TAtom "v242"), ((TAtom "v0"), "fp", 160)); ((TAtom "v244"), ((TAtom "v243"), "v243", 16)); ((TAtom "v251"), ((TAtom "v250"), "v250", 8)); ((TAtom "v255"), ((TAtom "v254"), "v254", 24)); ((TAtom "v259"), ((TAtom "v258"), "v258", 32)); ((TAtom "v263"), ((TAtom "v262"), "v262", 40)); ((TAtom "v266"), ((TAtom "v0"), "fp", 24)); ((TAtom "v268"), ((TAtom "v0"), "fp", 8)); ((TAtom "v270"), ((TAtom "v0"), "fp", 16)); ((TAtom "v272"), ((TAtom "v0"), "fp", 32)); ((TAtom "v274"), ((TAtom "v0"), "fp", 40)); ((TAtom "v276"), ((TAtom "v0"), "fp", 48)); ((TAtom "v280"), ((TAtom "v280"), "unlink", 0)); ((TAtom "v292"), ((TAtom "v0"), "fp", 112)); ((TAtom "v295"), ((TAtom "v0"), "fp", 144)); ((TAtom "v35"), ((TAtom "v0"), "fp", 192)); ((TAtom "v40"), ((TAtom "v0"), "fp", 32)); ((TAtom "v43"), ((TAtom "v0"), "fp", 40)); ((TAtom "v54"), ((TAtom "v0"), "fp", 160)); ((TAtom "v56"), ((TAtom "v55"), "v55", 24)); ((TAtom "v61"), ((TAtom "v60"), "v60", 32)); ((TAtom "v66"), ((TAtom "v65"), "v65", 24)); ((TAtom "v78"), ((TAtom "v0"), "fp", 112)); ((TAtom "v89"), ((TAtom "v0"), "fp", 192)); ((TAtom "v9"), ((TAtom "v0"), "fp", 112)); ((TAtom "v95"), ((TAtom "v0"), "fp", 8)); ((TAtom "v98"), ((TAtom "v0"), "fp", 16))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L86"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L92"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L87"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L110"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L118"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L155"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L148"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L161"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L163"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "L191"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L192"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L179"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L202"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_3.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "L204"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L221"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L228"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L230"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L223"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L277"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L279"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L299"), [(TAtom "pr.3")]); ((TAtom "L300"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v28")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v51")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v72")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L86"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L92"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v102"); (TAtom "v2")]); ((TAtom "L87"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L110"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L118"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v131"); (TAtom "v2")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L155"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L148"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L161"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v177"); (TAtom "v2")]); ((TAtom "L163"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L191"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v195"); (TAtom "v2")]); ((TAtom "L192"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L179"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L202"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "iw_3.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v219")]); ((TAtom "L204"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L221"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L228"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L230"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L223"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L277"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L279"), [(TAtom "pr.3"); (TAtom "v220")]); ((TAtom "L299"), [(TAtom "pr.3")]); ((TAtom "L300"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")]); ((TAtom "L5"), []); ((TAtom "L7"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L23"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L24"), []); ((TAtom "L16"), [(2%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L31"), [(2%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base"); (4%N, (TApp "tmp" [(TAtom "v40")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (5%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base")]); ((TAtom "L32"), [(2%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), true, false, (Some (TAtom "v55")), (Some (24)), "fp->_wide_data->_IO_write_base"); (6%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (9%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v60")), (Some (32)), "fp->_wide_data->_IO_write_ptr"); (10%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (13%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v65")), (Some (24)), "fp->_wide_data->_IO_write_base")]); ((TAtom "L17"), [(1%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")]); ((TAtom "L81"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L86"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L92"), [(2%N, (TApp "tmp" [(TAtom "v95")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "fp->_IO_read_ptr"); (4%N, (TApp "tmp" [(TAtom "v95")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "fp->_IO_read_end")]); ((TAtom "L87"), []); ((TAtom "L110"), [(2%N, (TApp "tmp" [(TAtom "v113")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L118"), [(2%N, (TApp "tmp" [(TAtom "v121")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (4%N, (TApp "tmp" [(TAtom "v122")]), (0), (Some 8), true, false, (Some (TAtom "v122")), (Some (0)), "fp->_wide_data->_IO_read_ptr"); (5%N, (TApp "tmp" [(TAtom "v121")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (8%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 8), true, false, (Some (TAtom "v126")), (Some (8)), "fp->_wide_data->_IO_read_end")]); ((TAtom "L82"), []); ((TAtom "L74"), [(2%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v143")]), (0), (Some 8), true, false, (Some (TAtom "v141")), (Some (72)), "opaque")]); ((TAtom "L147"), [(2%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 4), true, false, (Some (TAtom "v157")), (Some (0)), "opaque")]); ((TAtom "L155"), []); ((TAtom "L148"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L161"), [(2%N, (TApp "tmp" [(TAtom "v169")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88)), "fp->_IO_save_end"); (4%N, (TApp "tmp" [(TAtom "v169")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72)), "fp->_IO_save_base")]); ((TAtom "L163"), [(2%N, (TApp "tmp" [(TAtom "v182")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_2.L10"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v185")]), (0), (Some 8), true, false, (Some (TAtom "v183")), (Some (128)), "opaque")]); ((TAtom "L191"), [(2%N, (TApp "tmp" [(TAtom "v193")]), (0), (Some 4), true, false, (Some (TAtom "v193")), (Some (0)), "opaque")]); ((TAtom "L192"), []); ((TAtom "L179"), []); ((TAtom "L18"), [(3%N, (TApp "tmp" [(TAtom "v206")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "fp->_flags2")]); ((TAtom "L202"), [(2%N, (TApp "tmp" [(TAtom "v213")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_3.L10"), []); ((TAtom "iw_3.join"), [(2%N, (TApp "tmp" [(TAtom "v216")]), (0), (Some 8), true, false, (Some (TAtom "v214")), (Some (136)), "opaque")]); ((TAtom "L204"), [(2%N, (TApp "tmp" [(TAtom "v225")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L221"), [(2%N, (TApp "tmp" [(TAtom "v232")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v234")]), (0), (Some 8), true, false, (Some (TAtom "v233")), (Some (72)), "fp->_wide_data->_IO_backup_base")]); ((TAtom "L228"), []); ((TAtom "L230"), [(3%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (6%N, (TApp "tmp" [(TAtom "v244")]), (0), (Some 8), false, true, (Some (TAtom "v243")), (Some (16)), "fp->_wide_data->_IO_read_base"); (8%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (10%N, (TApp "tmp" [(TAtom "v247")]), (0), (Some 8), false, true, (Some (TAtom "v247")), (Some (0)), "fp->_wide_data->_IO_read_ptr"); (12%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (15%N, (TApp "tmp" [(TAtom "v251")]), (0), (Some 8), false, true, (Some (TAtom "v250")), (Some (8)), "fp->_wide_data->_IO_read_end"); (17%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (19%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (22%N, (TApp "tmp" [(TAtom "v259")]), (0), (Some 8), false, true, (Some (TAtom "v258")), (Some (32)), "fp->_wide_data->_IO_write_ptr"); (24%N, (TApp "tmp" [(TAtom "v255")]), (0), (Some 8), false, true, (Some (TAtom "v254")), (Some (24)), "fp->_wide_data->_IO_write_base"); (26%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (29%N, (TApp "tmp" [(TAtom "v263")]), (0), (Some 8), false, true, (Some (TAtom "v262")), (Some (40)), "fp->_wide_data->_IO_write_end")]); ((TAtom "L223"), [(3%N, (TApp "tmp" [(TAtom "v266")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)), "fp->_IO_read_base"); (6%N, (TApp "tmp" [(TAtom "v268")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "fp->_IO_read_ptr"); (9%N, (TApp "tmp" [(TAtom "v270")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)), "fp->_IO_read_end"); (13%N, (TApp "tmp" [(TAtom "v274")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (15%N, (TApp "tmp" [(TAtom "v272")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base"); (18%N, (TApp "tmp" [(TAtom "v276")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (48)), "fp->_IO_write_end")]); ((TAtom "L277"), []); ((TAtom "L279"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags"); (5%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)), "fp->_flags"); (8%N, (TApp "tmp" [(TAtom "v292")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (112)), "fp->_fileno"); (11%N, (TApp "tmp" [(TAtom "v295")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (144)), "fp->_offset")]); ((TAtom "L299"), []); ((TAtom "L300"), [])].


End fn__IO_file_close_maybe_unlink.

Module fn__IO_new_file_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_44, 211%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_44, 214%N)); ((TAtom "L4"), (file_44, 216%N)); ((TAtom "L12"), (file_44, 216%N)); ((TAtom "L13"), (file_44, 216%N)); ((TAtom "L14"), (file_44, 217%N)); ((TAtom "L55"), (file_44, 218%N)); ((TAtom "iw_1.L10"), (file_33, 1049%N)); ((TAtom "iw_1.join"), (file_44, 218%N)); ((TAtom "L6"), (file_44, 220%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v20"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v62"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v70"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 112)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 192)); ((TAtom "chk10"), ((TAtom "v46"), "v46", 24)); ((TAtom "chk11"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk12"), ((TAtom "v0"), "fp", 216)); ((TAtom "chk13"), ((TAtom "v64"), "v64", 136)); ((TAtom "chk2"), ((TAtom "v0"), "fp", 32)); ((TAtom "chk5"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk6"), ((TAtom "v36"), "v36", 24)); ((TAtom "chk8"), ((TAtom "v41"), "v41", 32)); ((TAtom "iw_1.v4"), ((TAtom "iw_1.v4"), "ptr", 0)); ((TAtom "iw_1.v7"), ((TAtom "iw_1.v7"), "&__io_vtables", 0)); ((TAtom "iw_1.v9"), ((TAtom "iw_1.v9"), "offset", 0)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v16"), ((TAtom "v0"), "fp", 192)); ((TAtom "v2"), ((TAtom "v2"), "dummy", 0)); ((TAtom "v21"), ((TAtom "v0"), "fp", 32)); ((TAtom "v24"), ((TAtom "v0"), "fp", 40)); ((TAtom "v35"), ((TAtom "v0"), "fp", 160)); ((TAtom "v37"), ((TAtom "v36"), "v36", 24)); ((TAtom "v42"), ((TAtom "v41"), "v41", 32)); ((TAtom "v47"), ((TAtom "v46"), "v46", 24)); ((TAtom "v63"), ((TAtom "v0"), "fp", 216)); ((TAtom "v66"), ((TAtom "v64"), "v64", 136)); ((TAtom "v8"), ((TAtom "v0"), "fp", 112))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L55"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "L6"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L55"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L6"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)), "fp->_fileno")]); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base"); (4%N, (TApp "tmp" [(TAtom "v21")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (5%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base")]); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v36")), (Some (24)), "fp->_wide_data->_IO_write_base"); (6%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (9%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v41")), (Some (32)), "fp->_wide_data->_IO_write_ptr"); (10%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (13%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v46")), (Some (24)), "fp->_wide_data->_IO_write_base")]); ((TAtom "L14"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L55"), [(2%N, (TApp "tmp" [(TAtom "v63")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v64")), (Some (136)), "opaque")]); ((TAtom "L6"), [])].


End fn__IO_new_file_finish.

Module fn__IO_new_file_setbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_44, 430%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_44, 433%N)); ((TAtom "L6"), (file_44, 434%N)); ((TAtom "L8"), (file_44, 436%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v10"), "p"); ((TAtom "v11"), "len"); ((TAtom "v17"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "p"); ((TAtom "v21"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v36"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v4"), "len"); ((TAtom "v41"), "fp"); ((TAtom "v9"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 56)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 48)); ((TAtom "chk2"), ((TAtom "v0"), "fp", 40)); ((TAtom "chk3"), ((TAtom "v0"), "fp", 32)); ((TAtom "chk4"), ((TAtom "v0"), "fp", 56)); ((TAtom "chk5"), ((TAtom "v0"), "fp", 24)); ((TAtom "chk6"), ((TAtom "v0"), "fp", 56)); ((TAtom "chk7"), ((TAtom "v0"), "fp", 8)); ((TAtom "chk8"), ((TAtom "v0"), "fp", 56)); ((TAtom "chk9"), ((TAtom "v0"), "fp", 16)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v18"), ((TAtom "v0"), "fp", 32)); ((TAtom "v2"), ((TAtom "v2"), "p", 0)); ((TAtom "v20"), ((TAtom "v0"), "fp", 40)); ((TAtom "v22"), ((TAtom "v0"), "fp", 48)); ((TAtom "v24"), ((TAtom "v0"), "fp", 56)); ((TAtom "v27"), ((TAtom "v0"), "fp", 24)); ((TAtom "v32"), ((TAtom "v0"), "fp", 8)); ((TAtom "v37"), ((TAtom "v0"), "fp", 16)); ((TAtom "v4"), ((TAtom "v4"), "len", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L6"), []); ((TAtom "L8"), [(5%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "fp->_IO_buf_base"); (7%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (48)), "fp->_IO_write_end"); (9%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (11%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base"); (14%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "fp->_IO_buf_base"); (16%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)), "fp->_IO_read_base"); (19%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "fp->_IO_buf_base"); (21%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "fp->_IO_read_ptr"); (24%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "fp->_IO_buf_base"); (26%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)), "fp->_IO_read_end")])].


End fn__IO_new_file_setbuf.

End HiAtexitSrc02.

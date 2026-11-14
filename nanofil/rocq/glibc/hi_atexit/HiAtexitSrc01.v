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
Definition source : option (string * N) := Some (file_11, 10%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_11, 11%N)); ((TAtom "L19"), (file_11, 14%N)); ((TAtom "L20"), (file_11, 14%N)); ((TAtom "L15"), (file_11, 15%N)); ((TAtom "L28"), (file_11, 15%N)); ((TAtom "L29"), (file_11, 15%N)); ((TAtom "L24"), (file_11, 16%N)); ((TAtom "L17"), (file_11, 10%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v12"), "stdout"); ((TAtom "v14"), "fclose_fail"); ((TAtom "v18"), "prev_fail"); ((TAtom "v2"), "stdout"); ((TAtom "v21"), "fclose_fail"); ((TAtom "v27"), "pending"); ((TAtom "v30"), "fclose_fail"); ((TAtom "v4"), "pending"); ((TAtom "v7"), "stdout"); ((TAtom "v9"), "prev_fail")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L19"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "v14")]); ((TAtom "L29"), []); ((TAtom "L24"), []); ((TAtom "L17"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v14"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "v14")]); ((TAtom "L28"), [(TAtom "v14")]); ((TAtom "L29"), []); ((TAtom "L24"), []); ((TAtom "L17"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), true, false, (Some (TAtom "v1")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v6")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (0)))]); ((TAtom "L19"), []); ((TAtom "L20"), []); ((TAtom "L15"), []); ((TAtom "L28"), []); ((TAtom "L29"), []); ((TAtom "L24"), []); ((TAtom "L17"), [])].


End fn_hi_atexit_close_stdout_hi.

Module fn_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_11, 20%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_11, 21%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn_main.

Module fn_malloc___libc_malloc2.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_25, 3065%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_25, 3069%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "ar_ptr"); ((TAtom "pr.2"), "ar_ptr"); ((TAtom "pr.3"), "ar_ptr"); ((TAtom "pr.4"), "victim"); ((TAtom "v0"), "bytes"); ((TAtom "v101"), "victim"); ((TAtom "v107"), "ar_ptr"); ((TAtom "v116"), "ar_ptr"); ((TAtom "v117"), "bytes"); ((TAtom "v118"), "ar_ptr"); ((TAtom "v119"), "ar_ptr"); ((TAtom "v120"), "bytes"); ((TAtom "v121"), "victim"); ((TAtom "v125"), "ar_ptr"); ((TAtom "v130"), "ar_ptr"); ((TAtom "v133"), "__futex"); ((TAtom "v137"), "__oldval"); ((TAtom "v14"), "__libc_single_threaded_internal"); ((TAtom "v143"), "__oldval"); ((TAtom "v155"), "__futex"); ((TAtom "v156"), "__futex"); ((TAtom "v157"), "__private"); ((TAtom "v161"), "victim"); ((TAtom "v167"), "victim"); ((TAtom "v17"), "bytes"); ((TAtom "v178"), "ar_ptr"); ((TAtom "v179"), "victim"); ((TAtom "v18"), "victim"); ((TAtom "v191"), "victim"); ((TAtom "v22"), "victim"); ((TAtom "v28"), "victim"); ((TAtom "v40"), "victim"); ((TAtom "v5"), "bytes"); ((TAtom "v52"), "victim"); ((TAtom "v58"), "thread_arena"); ((TAtom "v65"), "ar_ptr"); ((TAtom "v69"), "ar_ptr"); ((TAtom "v74"), "__futex"); ((TAtom "v75"), "__atg3_old"); ((TAtom "v76"), "__atg3_old"); ((TAtom "v91"), "__futex"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "bytes"); ((TAtom "v94"), "ar_ptr"); ((TAtom "v95"), "ar_ptr"); ((TAtom "v96"), "bytes"); ((TAtom "v97"), "victim")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn_malloc___libc_malloc2.

Module fn___GI___libc_malloc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_25, 3102%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_25, 1136%N)); ((TAtom "iw_1.L4"), (file_25, 1139%N)); ((TAtom "iw_1.L76"), (file_25, 1139%N)); ((TAtom "iw_1.join"), (file_25, 3108%N)); ((TAtom "L26"), (file_25, 3110%N)); ((TAtom "L43"), (file_25, 3114%N)); ((TAtom "iw_2.start"), (file_25, 2879%N)); ((TAtom "iw_2.iw_1.L22"), (file_25, 2857%N)); ((TAtom "iw_2.iw_1.L38"), (file_25, 2860%N)); ((TAtom "iw_3.start"), (file_1, 79%N)); ((TAtom "iw_3.iw_1.iw_1.L3"), (file_1, 79%N)); ((TAtom "iw_3.iw_1.iw_1.L4"), (file_1, 79%N)); ((TAtom "iw_4.iw_1.L18"), (file_25, 2887%N)); ((TAtom "iw_4.iw_1.L25"), (file_25, 2888%N)); ((TAtom "iw_4.iw_1.L26"), (file_25, 2888%N)); ((TAtom "iw_4.iw_1.L19"), (file_25, 2892%N)); ((TAtom "iw_4.iw_1.join"), (file_25, 2919%N)); ((TAtom "iw_4.L18"), (file_25, 2919%N)); ((TAtom "iw_4.L19"), (file_25, 2919%N)); ((TAtom "iw_4.iw_2.start"), (file_25, 2851%N)); ((TAtom "iw_4.iw_2.L7"), (file_25, 2852%N)); ((TAtom "iw_4.iw_2.L8"), (file_25, 2854%N)); ((TAtom "iw_4.iw_2.L9"), (file_25, 2850%N)); ((TAtom "iw_4.iw_2.L22"), (file_25, 2857%N)); ((TAtom "iw_4.iw_2.L24"), (file_25, 2859%N)); ((TAtom "iw_4.iw_2.L38"), (file_25, 2860%N)); ((TAtom "iw_4.iw_2.L39"), (file_25, 2862%N)); ((TAtom "iw_4.iw_2.L40"), (file_25, 2864%N)); ((TAtom "iw_4.join"), (file_25, 3121%N)); ((TAtom "L72"), (file_25, 3122%N)); ((TAtom "L7"), (file_25, 3127%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "req"); ((TAtom "iw_1.v13"), "req"); ((TAtom "iw_1.v5"), "req"); ((TAtom "iw_1.v63"), "req"); ((TAtom "iw_2.iw_1.pr.1"), "e"); ((TAtom "iw_2.iw_1.v0"), "tc_idx"); ((TAtom "iw_2.iw_1.v10"), "mangled"); ((TAtom "iw_2.iw_1.v12"), "ep"); ((TAtom "iw_2.iw_1.v13"), "e"); ((TAtom "iw_2.iw_1.v14"), "ep"); ((TAtom "iw_2.iw_1.v17"), "ep"); ((TAtom "iw_2.iw_1.v2"), "ep"); ((TAtom "iw_2.iw_1.v21"), "e"); ((TAtom "iw_2.iw_1.v25"), "e"); ((TAtom "iw_2.iw_1.v4"), "mangled"); ((TAtom "iw_2.iw_1.v41"), "mangled"); ((TAtom "iw_2.iw_1.v43"), "ep"); ((TAtom "iw_2.iw_1.v44"), "e"); ((TAtom "iw_2.iw_1.v47"), "e"); ((TAtom "iw_2.iw_1.v52"), "ep"); ((TAtom "iw_2.iw_1.v53"), "ep"); ((TAtom "iw_2.iw_1.v56"), "e"); ((TAtom "iw_2.iw_1.v59"), "e"); ((TAtom "iw_2.iw_1.v68"), "tcache"); ((TAtom "iw_2.iw_1.v69"), "tc_idx"); ((TAtom "iw_2.iw_1.v75"), "e"); ((TAtom "iw_2.iw_1.v77"), "e"); ((TAtom "iw_2.v0"), "tc_idx"); ((TAtom "iw_2.v2"), "tc_idx"); ((TAtom "iw_2.v4"), "tcache"); ((TAtom "iw_2.v6"), "tc_idx"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.v2"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_2.v2"), "__x"); ((TAtom "iw_3.v0"), "nb"); ((TAtom "iw_3.v3"), "nb"); ((TAtom "iw_3.v36"), "idx"); ((TAtom "iw_3.v37"), "idx"); ((TAtom "iw_4.iw_1.pr.1"), "tep"); ((TAtom "iw_4.iw_1.pr.2"), "te"); ((TAtom "iw_4.iw_1.v0"), "nb"); ((TAtom "iw_4.iw_1.v10"), "tcache"); ((TAtom "iw_4.iw_1.v12"), "tc_idx"); ((TAtom "iw_4.iw_1.v14"), "tep"); ((TAtom "iw_4.iw_1.v16"), "tep"); ((TAtom "iw_4.iw_1.v17"), "te"); ((TAtom "iw_4.iw_1.v2"), "tc_idx"); ((TAtom "iw_4.iw_1.v21"), "te"); ((TAtom "iw_4.iw_1.v27"), "te"); ((TAtom "iw_4.iw_1.v37"), "nb"); ((TAtom "iw_4.iw_1.v4"), "mangled"); ((TAtom "iw_4.iw_1.v43"), "te"); ((TAtom "iw_4.iw_1.v44"), "te"); ((TAtom "iw_4.iw_1.v47"), "te"); ((TAtom "iw_4.iw_1.v51"), "te"); ((TAtom "iw_4.iw_1.v52"), "mangled"); ((TAtom "iw_4.iw_1.v54"), "demangled_ptr"); ((TAtom "iw_4.iw_1.v55"), "te"); ((TAtom "iw_4.iw_1.v56"), "tep"); ((TAtom "iw_4.iw_1.v6"), "demangled_ptr"); ((TAtom "iw_4.iw_2.pr.1"), "e"); ((TAtom "iw_4.iw_2.v0"), "tc_idx"); ((TAtom "iw_4.iw_2.v10"), "mangled"); ((TAtom "iw_4.iw_2.v12"), "ep"); ((TAtom "iw_4.iw_2.v13"), "e"); ((TAtom "iw_4.iw_2.v14"), "ep"); ((TAtom "iw_4.iw_2.v17"), "ep"); ((TAtom "iw_4.iw_2.v2"), "ep"); ((TAtom "iw_4.iw_2.v21"), "e"); ((TAtom "iw_4.iw_2.v25"), "e"); ((TAtom "iw_4.iw_2.v4"), "mangled"); ((TAtom "iw_4.iw_2.v41"), "mangled"); ((TAtom "iw_4.iw_2.v43"), "ep"); ((TAtom "iw_4.iw_2.v44"), "e"); ((TAtom "iw_4.iw_2.v47"), "e"); ((TAtom "iw_4.iw_2.v52"), "ep"); ((TAtom "iw_4.iw_2.v53"), "ep"); ((TAtom "iw_4.iw_2.v56"), "e"); ((TAtom "iw_4.iw_2.v59"), "e"); ((TAtom "iw_4.iw_2.v68"), "tcache"); ((TAtom "iw_4.iw_2.v69"), "tc_idx"); ((TAtom "iw_4.iw_2.v75"), "e"); ((TAtom "iw_4.iw_2.v77"), "e"); ((TAtom "iw_4.pr.1"), "mangled"); ((TAtom "iw_4.v0"), "tc_idx"); ((TAtom "iw_4.v10"), "entry"); ((TAtom "iw_4.v14"), "te"); ((TAtom "iw_4.v2"), "nb"); ((TAtom "iw_4.v20"), "nb"); ((TAtom "iw_4.v21"), "te"); ((TAtom "iw_4.v35"), "tc_idx"); ((TAtom "iw_4.v36"), "entry"); ((TAtom "iw_4.v37"), "mangled"); ((TAtom "iw_4.v6"), "mangled"); ((TAtom "iw_4.v8"), "nb"); ((TAtom "iw_4.v9"), "tc_idx"); ((TAtom "v0"), "bytes"); ((TAtom "v14"), "nb"); ((TAtom "v3"), "bytes"); ((TAtom "v4"), "nb"); ((TAtom "v42"), "tc_idx"); ((TAtom "v46"), "tc_idx"); ((TAtom "v54"), "tcache"); ((TAtom "v56"), "tc_idx"); ((TAtom "v63"), "tc_idx"); ((TAtom "v66"), "nb"); ((TAtom "v67"), "tc_idx"); ((TAtom "v69"), "tc_idx"); ((TAtom "v70"), "nb"); ((TAtom "v71"), "victim"); ((TAtom "v75"), "victim"); ((TAtom "v79"), "victim"); ((TAtom "v8"), "nb"); ((TAtom "v81"), "bytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_4.iw_1.L18")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "v0")]); ((TAtom "iw_1.L76"), [(TAtom "iw_1.v23"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.start"), [(TAtom "v42"); (TAtom "v57")]); ((TAtom "iw_2.iw_1.L22"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L38"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_3.start"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L4"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L18"), [(TAtom "iw_3.v38"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L25"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L26"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.join"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.start"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L7"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L8"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L9"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L22"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L24"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L38"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L39"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L40"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.join"), [(TAtom "iw_4.iw_1.v23"); (TAtom "v0")]); ((TAtom "L72"), [(TAtom "v71")]); ((TAtom "L7"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "iw_1.v23"); (TAtom "v0")]); ((TAtom "iw_1.L76"), [(TAtom "iw_1.v83"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v4"); (TAtom "v42")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v42"); (TAtom "v57")]); ((TAtom "iw_2.start"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L22"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L38"), []); ((TAtom "iw_3.start"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_3.iw_1.iw_1.v33"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L4"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v14"); (TAtom "iw_4.iw_1.v17"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L25"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_1.v38"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L26"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v51"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.join"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "iw_4.v31"); (TAtom "v0")]); ((TAtom "iw_4.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.start"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L7"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.v13"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L8"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.v21"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L9"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L22"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L24"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L38"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L39"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L40"), [(TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.join"), [(TAtom "v0"); (TAtom "v71")]); ((TAtom "L72"), []); ((TAtom "L7"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.L76"), []); ((TAtom "iw_1.join"), [(3%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v9")), (Some (120)))]); ((TAtom "L26"), []); ((TAtom "L43"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v53")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v54")), None)]); ((TAtom "iw_2.start"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v3")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "iw_2.v8")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v4")), None)]); ((TAtom "iw_2.iw_1.L22"), []); ((TAtom "iw_2.iw_1.L38"), [(2%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v13")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.iw_1.v13")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "iw_2.v8")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v4")), None); (10%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v67")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.iw_1.v67")), (Some (0))); (14%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v71")]), (0), (Some 2), true, false, (Some (TAtom "iw_2.iw_1.v68")), None); (18%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v71")]), (0), (Some 2), false, true, (Some (TAtom "iw_2.iw_1.v68")), None); (21%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v76")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.iw_1.v13")), (Some (8)))]); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_3.iw_1.iw_1.L4"), [(6%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v9")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.v9")), (Some (0))); (11%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v14")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.v10")), None)]); ((TAtom "iw_4.iw_1.L18"), []); ((TAtom "iw_4.iw_1.L25"), [(3%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v30")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (-8)))]); ((TAtom "iw_4.iw_1.L26"), []); ((TAtom "iw_4.iw_1.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.2")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (0)))]); ((TAtom "iw_4.iw_1.join"), []); ((TAtom "iw_4.L18"), [(3%N, (TApp "tmp" [(TAtom "iw_4.v24")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (-8)))]); ((TAtom "iw_4.L19"), []); ((TAtom "iw_4.iw_2.start"), []); ((TAtom "iw_4.iw_2.L7"), [(1%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L8"), [(3%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L9"), []); ((TAtom "iw_4.iw_2.L22"), []); ((TAtom "iw_4.iw_2.L24"), []); ((TAtom "iw_4.iw_2.L38"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L39"), [(4%N, (TApp "tmp" [(TAtom "iw_4.iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L40"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v67")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.v67")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v71")]), (0), (Some 2), true, false, (Some (TAtom "iw_4.iw_2.v68")), None); (10%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v71")]), (0), (Some 2), false, true, (Some (TAtom "iw_4.iw_2.v68")), None); (13%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v76")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (8)))]); ((TAtom "iw_4.join"), []); ((TAtom "L72"), []); ((TAtom "L7"), [])].


End fn___GI___libc_malloc.

Module fn___GI___libc_free.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_25, 3138%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_25, 3142%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "mem"); ((TAtom "v103"), "tc_idx"); ((TAtom "v107"), "tc_idx"); ((TAtom "v11"), "mem"); ((TAtom "v115"), "tcache"); ((TAtom "v116"), "tc_idx"); ((TAtom "v123"), "p"); ((TAtom "v124"), "tc_idx"); ((TAtom "v126"), "size"); ((TAtom "v127"), "tc_idx"); ((TAtom "v131"), "size"); ((TAtom "v155"), "tcache"); ((TAtom "v156"), "tc_idx"); ((TAtom "v16"), "mem"); ((TAtom "v165"), "p"); ((TAtom "v166"), "tc_idx"); ((TAtom "v175"), "mem"); ((TAtom "v18"), "p"); ((TAtom "v192"), "p"); ((TAtom "v195"), "size"); ((TAtom "v20"), "p"); ((TAtom "v228"), "p"); ((TAtom "v231"), "size"); ((TAtom "v268"), "p"); ((TAtom "v27"), "size"); ((TAtom "v271"), "size"); ((TAtom "v300"), "size"); ((TAtom "v31"), "p"); ((TAtom "v322"), "p"); ((TAtom "v333"), "p"); ((TAtom "v336"), "size"); ((TAtom "v369"), "p"); ((TAtom "v372"), "size"); ((TAtom "v409"), "p"); ((TAtom "v412"), "size"); ((TAtom "v437"), "size"); ((TAtom "v469"), "p"); ((TAtom "v472"), "size"); ((TAtom "v5"), "mem"); ((TAtom "v50"), "size"); ((TAtom "v505"), "p"); ((TAtom "v508"), "size"); ((TAtom "v544"), "p"); ((TAtom "v547"), "size"); ((TAtom "v574"), "size"); ((TAtom "v58"), "p"); ((TAtom "v596"), "p"); ((TAtom "v60"), "e"); ((TAtom "v603"), "p"); ((TAtom "v606"), "size"); ((TAtom "v627"), "p"); ((TAtom "v629"), "size"); ((TAtom "v64"), "e"); ((TAtom "v655"), "size"); ((TAtom "v677"), "p"); ((TAtom "v679"), "p"); ((TAtom "v68"), "tcache_key"); ((TAtom "v681"), "size"); ((TAtom "v704"), "p"); ((TAtom "v706"), "size"); ((TAtom "v72"), "e"); ((TAtom "v728"), "size"); ((TAtom "v75"), "size"); ((TAtom "v757"), "p"); ((TAtom "v759"), "p"); ((TAtom "v760"), "size")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___libc_free.

Module fn___libc_calloc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_25, 3539%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_25, 3544%N)); ((TAtom "L5"), (file_25, 3546%N)); ((TAtom "L41"), (file_25, 3551%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "req"); ((TAtom "iw_1.v13"), "req"); ((TAtom "iw_1.v5"), "req"); ((TAtom "iw_1.v63"), "req"); ((TAtom "iw_2.iw_1.pr.1"), "e"); ((TAtom "iw_2.iw_1.v0"), "tc_idx"); ((TAtom "iw_2.iw_1.v10"), "mangled"); ((TAtom "iw_2.iw_1.v12"), "ep"); ((TAtom "iw_2.iw_1.v13"), "e"); ((TAtom "iw_2.iw_1.v14"), "ep"); ((TAtom "iw_2.iw_1.v17"), "ep"); ((TAtom "iw_2.iw_1.v2"), "ep"); ((TAtom "iw_2.iw_1.v21"), "e"); ((TAtom "iw_2.iw_1.v25"), "e"); ((TAtom "iw_2.iw_1.v4"), "mangled"); ((TAtom "iw_2.iw_1.v41"), "mangled"); ((TAtom "iw_2.iw_1.v43"), "ep"); ((TAtom "iw_2.iw_1.v44"), "e"); ((TAtom "iw_2.iw_1.v47"), "e"); ((TAtom "iw_2.iw_1.v52"), "ep"); ((TAtom "iw_2.iw_1.v53"), "ep"); ((TAtom "iw_2.iw_1.v56"), "e"); ((TAtom "iw_2.iw_1.v59"), "e"); ((TAtom "iw_2.iw_1.v68"), "tcache"); ((TAtom "iw_2.iw_1.v69"), "tc_idx"); ((TAtom "iw_2.iw_1.v75"), "e"); ((TAtom "iw_2.iw_1.v77"), "e"); ((TAtom "iw_2.v0"), "tc_idx"); ((TAtom "iw_2.v2"), "tc_idx"); ((TAtom "iw_2.v4"), "tcache"); ((TAtom "iw_2.v6"), "tc_idx"); ((TAtom "iw_3.v0"), "p"); ((TAtom "iw_3.v12"), "nclears"); ((TAtom "iw_3.v14"), "d"); ((TAtom "iw_3.v15"), "clearsize"); ((TAtom "iw_3.v2"), "clearsize"); ((TAtom "iw_3.v21"), "nclears"); ((TAtom "iw_3.v24"), "d"); ((TAtom "iw_3.v26"), "d"); ((TAtom "iw_3.v28"), "d"); ((TAtom "iw_3.v30"), "d"); ((TAtom "iw_3.v31"), "nclears"); ((TAtom "iw_3.v35"), "d"); ((TAtom "iw_3.v36"), "nclears"); ((TAtom "iw_3.v44"), "nclears"); ((TAtom "iw_3.v46"), "d"); ((TAtom "iw_3.v48"), "d"); ((TAtom "iw_3.v5"), "p"); ((TAtom "iw_3.v51"), "d"); ((TAtom "iw_3.v52"), "nclears"); ((TAtom "iw_3.v56"), "d"); ((TAtom "iw_3.v57"), "nclears"); ((TAtom "iw_3.v62"), "d"); ((TAtom "iw_3.v7"), "clearsize"); ((TAtom "iw_3.v8"), "nclears"); ((TAtom "iw_4.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.v2"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_2.v0"), "__x"); ((TAtom "iw_4.iw_2.v2"), "__x"); ((TAtom "iw_4.v0"), "nb"); ((TAtom "iw_4.v3"), "nb"); ((TAtom "iw_4.v36"), "idx"); ((TAtom "iw_4.v37"), "idx"); ((TAtom "iw_5.iw_1.pr.1"), "tep"); ((TAtom "iw_5.iw_1.pr.2"), "te"); ((TAtom "iw_5.iw_1.v0"), "nb"); ((TAtom "iw_5.iw_1.v10"), "tcache"); ((TAtom "iw_5.iw_1.v12"), "tc_idx"); ((TAtom "iw_5.iw_1.v14"), "tep"); ((TAtom "iw_5.iw_1.v16"), "tep"); ((TAtom "iw_5.iw_1.v17"), "te"); ((TAtom "iw_5.iw_1.v2"), "tc_idx"); ((TAtom "iw_5.iw_1.v21"), "te"); ((TAtom "iw_5.iw_1.v27"), "te"); ((TAtom "iw_5.iw_1.v37"), "nb"); ((TAtom "iw_5.iw_1.v4"), "mangled"); ((TAtom "iw_5.iw_1.v43"), "te"); ((TAtom "iw_5.iw_1.v44"), "te"); ((TAtom "iw_5.iw_1.v47"), "te"); ((TAtom "iw_5.iw_1.v51"), "te"); ((TAtom "iw_5.iw_1.v52"), "mangled"); ((TAtom "iw_5.iw_1.v54"), "demangled_ptr"); ((TAtom "iw_5.iw_1.v55"), "te"); ((TAtom "iw_5.iw_1.v56"), "tep"); ((TAtom "iw_5.iw_1.v6"), "demangled_ptr"); ((TAtom "iw_5.iw_2.pr.1"), "e"); ((TAtom "iw_5.iw_2.v0"), "tc_idx"); ((TAtom "iw_5.iw_2.v10"), "mangled"); ((TAtom "iw_5.iw_2.v12"), "ep"); ((TAtom "iw_5.iw_2.v13"), "e"); ((TAtom "iw_5.iw_2.v14"), "ep"); ((TAtom "iw_5.iw_2.v17"), "ep"); ((TAtom "iw_5.iw_2.v2"), "ep"); ((TAtom "iw_5.iw_2.v21"), "e"); ((TAtom "iw_5.iw_2.v25"), "e"); ((TAtom "iw_5.iw_2.v4"), "mangled"); ((TAtom "iw_5.iw_2.v41"), "mangled"); ((TAtom "iw_5.iw_2.v43"), "ep"); ((TAtom "iw_5.iw_2.v44"), "e"); ((TAtom "iw_5.iw_2.v47"), "e"); ((TAtom "iw_5.iw_2.v52"), "ep"); ((TAtom "iw_5.iw_2.v53"), "ep"); ((TAtom "iw_5.iw_2.v56"), "e"); ((TAtom "iw_5.iw_2.v59"), "e"); ((TAtom "iw_5.iw_2.v68"), "tcache"); ((TAtom "iw_5.iw_2.v69"), "tc_idx"); ((TAtom "iw_5.iw_2.v75"), "e"); ((TAtom "iw_5.iw_2.v77"), "e"); ((TAtom "iw_5.pr.1"), "mangled"); ((TAtom "iw_5.v0"), "tc_idx"); ((TAtom "iw_5.v10"), "entry"); ((TAtom "iw_5.v14"), "te"); ((TAtom "iw_5.v2"), "nb"); ((TAtom "iw_5.v20"), "nb"); ((TAtom "iw_5.v21"), "te"); ((TAtom "iw_5.v35"), "tc_idx"); ((TAtom "iw_5.v36"), "entry"); ((TAtom "iw_5.v37"), "mangled"); ((TAtom "iw_5.v6"), "mangled"); ((TAtom "iw_5.v8"), "nb"); ((TAtom "iw_5.v9"), "tc_idx"); ((TAtom "v0"), "n"); ((TAtom "v10"), "bytes"); ((TAtom "v101"), "tc_idx"); ((TAtom "v108"), "tc_idx"); ((TAtom "v110"), "tc_idx"); ((TAtom "v142"), "nb"); ((TAtom "v143"), "tc_idx"); ((TAtom "v145"), "tc_idx"); ((TAtom "v146"), "nb"); ((TAtom "v147"), "mem"); ((TAtom "v151"), "mem"); ((TAtom "v155"), "mem"); ((TAtom "v156"), "mem"); ((TAtom "v171"), "bytes"); ((TAtom "v2"), "elem_size"); ((TAtom "v44"), "bytes"); ((TAtom "v48"), "bytes"); ((TAtom "v49"), "nb"); ((TAtom "v53"), "nb"); ((TAtom "v59"), "nb"); ((TAtom "v8"), "n"); ((TAtom "v87"), "tc_idx"); ((TAtom "v9"), "elem_size"); ((TAtom "v91"), "tc_idx"); ((TAtom "v99"), "tcache")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L41"), [(TAtom "v10")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v10")]); ((TAtom "L5"), []); ((TAtom "L41"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L5"), [(2%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 4), false, true, (Some (TAtom "v39")), (Some (0)))]); ((TAtom "L41"), [])].


End fn___libc_calloc.

Module fn_malloc_malloc_printerr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_25, 5135%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_25, 5139%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "str"); ((TAtom "v4"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn_malloc_malloc_printerr.

Module fn___internal_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_14, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_14, 41%N)); ((TAtom "L10"), (file_14, 41%N)); ((TAtom "L11"), (file_14, 43%N)); ((TAtom "L29"), (file_14, 43%N)); ((TAtom "L30"), (file_14, 43%N)); ((TAtom "L34"), (file_14, 43%N)); ((TAtom "L23"), (file_14, 44%N)); ((TAtom "L46"), (file_14, 48%N)); ((TAtom "L59"), (file_14, 48%N)); ((TAtom "L60"), (file_14, 48%N)); ((TAtom "L71"), (file_14, 48%N)); ((TAtom "L66"), (file_14, 49%N)); ((TAtom "L48"), (file_14, 53%N)); ((TAtom "L103"), (file_14, 57%N)); ((TAtom "L104"), (file_14, 57%N)); ((TAtom "L115"), (file_14, 57%N)); ((TAtom "L110"), (file_14, 58%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v101"), "__futex"); ((TAtom "v105"), "__oldval"); ((TAtom "v111"), "__oldval"); ((TAtom "v12"), "func"); ((TAtom "v123"), "__futex"); ((TAtom "v124"), "__futex"); ((TAtom "v125"), "__private"); ((TAtom "v2"), "arg"); ((TAtom "v25"), "__futex"); ((TAtom "v26"), "__atg3_old"); ((TAtom "v27"), "__atg3_old"); ((TAtom "v4"), "d"); ((TAtom "v42"), "__futex"); ((TAtom "v43"), "__futex"); ((TAtom "v44"), "listp"); ((TAtom "v45"), "new"); ((TAtom "v49"), "new"); ((TAtom "v57"), "__futex"); ((TAtom "v6"), "listp"); ((TAtom "v61"), "__oldval"); ((TAtom "v67"), "__oldval"); ((TAtom "v79"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__private"); ((TAtom "v84"), "func"); ((TAtom "v85"), "new"); ((TAtom "v87"), "func"); ((TAtom "v88"), "new"); ((TAtom "v91"), "arg"); ((TAtom "v92"), "new"); ((TAtom "v95"), "d"); ((TAtom "v96"), "new")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L103"); (TAtom "L59")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L46"), []); ((TAtom "L59"), [(TAtom "chk1"); (TAtom "v54")]); ((TAtom "L60"), [(TAtom "v54"); (TAtom "v61")]); ((TAtom "L71"), [(TAtom "v54")]); ((TAtom "L66"), []); ((TAtom "L48"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L103"), [(TAtom "chk7"); (TAtom "v98")]); ((TAtom "L104"), [(TAtom "v105"); (TAtom "v98")]); ((TAtom "L115"), [(TAtom "v98")]); ((TAtom "L110"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L46"), [(TAtom "chk1"); (TAtom "v54"); (TAtom "v58")]); ((TAtom "L59"), [(TAtom "chk1"); (TAtom "v54"); (TAtom "v61"); (TAtom "v62")]); ((TAtom "L60"), [(TAtom "v54")]); ((TAtom "L71"), []); ((TAtom "L66"), []); ((TAtom "L48"), [(TAtom "chk7"); (TAtom "v102"); (TAtom "v98")]); ((TAtom "L103"), [(TAtom "chk7"); (TAtom "v105"); (TAtom "v106"); (TAtom "v98")]); ((TAtom "L104"), [(TAtom "v98")]); ((TAtom "L115"), []); ((TAtom "L110"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 4), true, true, (Some (TAtom "v20")), (Some (0)))]); ((TAtom "L29"), []); ((TAtom "L30"), []); ((TAtom "L34"), []); ((TAtom "L23"), []); ((TAtom "L46"), [(2%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), true, false, (Some (TAtom "v54")), (Some (0)))]); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), true, true, (Some (TAtom "v54")), (Some (0)))]); ((TAtom "L60"), []); ((TAtom "L71"), []); ((TAtom "L66"), []); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v86")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (16))); (8%N, (TApp "tmp" [(TAtom "v94")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (24))); (10%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (0))); (13%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, false, (Some (TAtom "v98")), (Some (0)))]); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, true, (Some (TAtom "v98")), (Some (0)))]); ((TAtom "L104"), []); ((TAtom "L115"), []); ((TAtom "L110"), [])].


End fn___internal_atexit.

Module fn___GI___cxa_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_14, 65%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_14, 68%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "arg"); ((TAtom "v4"), "d"); ((TAtom "v6"), "func"); ((TAtom "v7"), "arg"); ((TAtom "v8"), "d")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___cxa_atexit.

Module fn___new_exitfn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_14, 78%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_14, 86%N)); ((TAtom "L6"), (file_14, 89%N)); ((TAtom "L8"), (file_14, 91%N)); ((TAtom "L14"), (file_14, 84%N)); ((TAtom "L15"), (file_14, 93%N)); ((TAtom "L25"), (file_14, 84%N)); ((TAtom "L26"), (file_14, 94%N)); ((TAtom "L28"), (file_14, 97%N)); ((TAtom "L47"), (file_14, 101%N)); ((TAtom "L17"), (file_14, 84%N)); ((TAtom "L63"), (file_14, 104%N)); ((TAtom "L64"), (file_14, 104%N)); ((TAtom "L56"), (file_14, 108%N)); ((TAtom "L70"), (file_14, 110%N)); ((TAtom "L78"), (file_14, 110%N)); ((TAtom "L79"), (file_14, 111%N)); ((TAtom "L88"), (file_14, 115%N)); ((TAtom "L72"), (file_14, 81%N)); ((TAtom "L100"), (file_14, 122%N)); ((TAtom "L57"), (file_14, 129%N)); ((TAtom "L58"), (file_14, 83%N)); ((TAtom "L121"), (file_14, 136%N)); ((TAtom "L123"), (file_14, 140%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "p"); ((TAtom "pr.2"), "p"); ((TAtom "pr.3"), "l"); ((TAtom "pr.4"), "r"); ((TAtom "pr.5"), "r"); ((TAtom "pr.6"), "i"); ((TAtom "pr.7"), "i"); ((TAtom "pr.8"), "i"); ((TAtom "v0"), "listp"); ((TAtom "v10"), "__exit_funcs_done"); ((TAtom "v103"), "p"); ((TAtom "v107"), "p"); ((TAtom "v109"), "r"); ((TAtom "v110"), "p"); ((TAtom "v112"), "l"); ((TAtom "v114"), "i"); ((TAtom "v116"), "r"); ((TAtom "v117"), "l"); ((TAtom "v119"), "i"); ((TAtom "v12"), "listp"); ((TAtom "v124"), "r"); ((TAtom "v128"), "r"); ((TAtom "v13"), "l"); ((TAtom "v130"), "__new_exitfn_called"); ((TAtom "v131"), "__new_exitfn_called"); ((TAtom "v132"), "r"); ((TAtom "v18"), "l"); ((TAtom "v22"), "l"); ((TAtom "v24"), "i"); ((TAtom "v29"), "i"); ((TAtom "v34"), "l"); ((TAtom "v36"), "i"); ((TAtom "v43"), "i"); ((TAtom "v44"), "i"); ((TAtom "v48"), "i"); ((TAtom "v51"), "l"); ((TAtom "v53"), "l"); ((TAtom "v54"), "l"); ((TAtom "v55"), "l"); ((TAtom "v59"), "l"); ((TAtom "v65"), "i"); ((TAtom "v73"), "p"); ((TAtom "v80"), "l"); ((TAtom "v87"), "p"); ((TAtom "v91"), "p"); ((TAtom "v95"), "p"); ((TAtom "v96"), "listp"); ((TAtom "v98"), "listp"); ((TAtom "v99"), "p")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L14"); (TAtom "L25")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk1"); (TAtom "v0")]); ((TAtom "L15"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L28"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L47"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0")]); ((TAtom "L17"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L63"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L64"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L70"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L78"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L88"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v87")]); ((TAtom "L72"), [(TAtom "v20")]); ((TAtom "L100"), [(TAtom "pr.2"); (TAtom "v20")]); ((TAtom "L57"), [(TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v20")]); ((TAtom "L58"), [(TAtom "v20")]); ((TAtom "L121"), [(TAtom "pr.5")]); ((TAtom "L123"), [(TAtom "pr.5")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v13")]); ((TAtom "L14"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L15"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v24")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30"); (TAtom "v37")]); ((TAtom "L28"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L47"), [(TAtom "chk1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v55")]); ((TAtom "L17"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L63"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21"); (TAtom "v67")]); ((TAtom "L64"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L70"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L78"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v87")]); ((TAtom "L88"), [(TAtom "v20"); (TAtom "v87")]); ((TAtom "L72"), [(TAtom "pr.2"); (TAtom "v20")]); ((TAtom "L100"), [(TAtom "v108"); (TAtom "v20")]); ((TAtom "L57"), [(TAtom "v116"); (TAtom "v20")]); ((TAtom "L58"), [(TAtom "pr.5")]); ((TAtom "L121"), [(TAtom "pr.5")]); ((TAtom "L123"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 1), true, false, (Some (TAtom "v9")), (Some (0)))]); ((TAtom "L6"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L14"), []); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), (Some (8)))]); ((TAtom "L25"), []); ((TAtom "L26"), [(5%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), None)]); ((TAtom "L28"), []); ((TAtom "L47"), [(2%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 8), false, true, (Some (TAtom "pr.3")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "pr.3")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), (Some (0)))]); ((TAtom "L17"), []); ((TAtom "L63"), []); ((TAtom "L64"), []); ((TAtom "L56"), []); ((TAtom "L70"), []); ((TAtom "L78"), []); ((TAtom "L79"), []); ((TAtom "L88"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0))); (3%N, (TApp "tmp" [(TAtom "v87")]), (0), (Some 8), false, true, (Some (TAtom "v87")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L72"), []); ((TAtom "L100"), [(3%N, (TApp "tmp" [(TAtom "v111")]), (0), (Some 8), false, true, (Some (TAtom "pr.2")), (Some (8)))]); ((TAtom "L57"), [(6%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 8), false, true, (Some (TAtom "pr.3")), (Some (8)))]); ((TAtom "L58"), []); ((TAtom "L121"), [(1%N, (TApp "tmp" [(TAtom "pr.5")]), (0), (Some 8), false, true, (Some (TAtom "pr.5")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 8), true, false, (Some (TAtom "v129")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 8), false, true, (Some (TAtom "v129")), (Some (0)))]); ((TAtom "L123"), [])].


End fn___new_exitfn.

Module fn_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_13, 40%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_13, 46%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "func")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn_atexit.

Module fn___fpending.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_12, 20%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_12, 23%N)); ((TAtom "L2"), (file_12, 24%N)); ((TAtom "L3"), (file_12, 26%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L3"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L2"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (32))); (6%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (9%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (24)))]); ((TAtom "L3"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)))])].


End fn___fpending.

Module fn__IO_ferror.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_17, 30%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_17, 35%N)); ((TAtom "L6"), (file_17, 36%N)); ((TAtom "L8"), (file_17, 37%N)); ((TAtom "L29"), (file_17, 37%N)); ((TAtom "L40"), (file_17, 37%N)); ((TAtom "L41"), (file_17, 37%N)); ((TAtom "L34"), (file_17, 37%N)); ((TAtom "L35"), (file_17, 37%N)); ((TAtom "L60"), (file_17, 37%N)); ((TAtom "L84"), (file_17, 37%N)); ((TAtom "L85"), (file_17, 37%N)); ((TAtom "L89"), (file_17, 37%N)); ((TAtom "L78"), (file_17, 37%N)); ((TAtom "L61"), (file_17, 37%N)); ((TAtom "L24"), (file_17, 38%N)); ((TAtom "L121"), (file_17, 39%N)); ((TAtom "L130"), (file_17, 39%N)); ((TAtom "L131"), (file_17, 39%N)); ((TAtom "L124"), (file_17, 39%N)); ((TAtom "L125"), (file_17, 39%N)); ((TAtom "L147"), (file_17, 39%N)); ((TAtom "L168"), (file_17, 39%N)); ((TAtom "L169"), (file_17, 39%N)); ((TAtom "L180"), (file_17, 39%N)); ((TAtom "L148"), (file_17, 39%N)); ((TAtom "L116"), (file_17, 40%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v103"), "__self"); ((TAtom "v104"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "result"); ((TAtom "v117"), "fp"); ((TAtom "v128"), "__libc_single_threaded_internal"); ((TAtom "v132"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v161"), "fp"); ((TAtom "v163"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v17"), "fp"); ((TAtom "v170"), "__oldval"); ((TAtom "v176"), "__oldval"); ((TAtom "v188"), "__futex"); ((TAtom "v189"), "__futex"); ((TAtom "v190"), "__private"); ((TAtom "v191"), "fp"); ((TAtom "v197"), "result"); ((TAtom "v25"), "fp"); ((TAtom "v33"), "__self"); ((TAtom "v38"), "__libc_single_threaded_internal"); ((TAtom "v42"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v59"), "__self"); ((TAtom "v63"), "fp"); ((TAtom "v68"), "__self"); ((TAtom "v73"), "fp"); ((TAtom "v75"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__atg3_old"); ((TAtom "v82"), "__atg3_old"); ((TAtom "v9"), "fp"); ((TAtom "v97"), "__futex"); ((TAtom "v98"), "__futex"); ((TAtom "v99"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L168")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163"); (TAtom "v170")]); ((TAtom "L180"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L148"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L116"), [(TAtom "v113")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v49")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113"); (TAtom "v137")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v167")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v170"); (TAtom "v171")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L180"), [(TAtom "v113")]); ((TAtom "L148"), [(TAtom "v113")]); ((TAtom "L116"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)))]); ((TAtom "L6"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 1), true, false, (Some (TAtom "v37")), (Some (0)))]); ((TAtom "L40"), [(2%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), true, false, (Some (TAtom "v44")), (Some (8)))]); ((TAtom "L41"), []); ((TAtom "L34"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), false, true, (Some (TAtom "v54")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), false, true, (Some (TAtom "v57")), (Some (8)))]); ((TAtom "L35"), [(2%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v65")), (Some (8)))]); ((TAtom "L60"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "v75")]), (0), (Some 4), true, true, (Some (TAtom "v75")), (Some (0)))]); ((TAtom "L84"), []); ((TAtom "L85"), []); ((TAtom "L89"), []); ((TAtom "L78"), [(2%N, (TApp "tmp" [(TAtom "v100")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 8), false, true, (Some (TAtom "v101")), (Some (8)))]); ((TAtom "L61"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), true, false, (Some (TAtom "v106")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), false, true, (Some (TAtom "v106")), (Some (4)))]); ((TAtom "L24"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 1), true, false, (Some (TAtom "v127")), (Some (0)))]); ((TAtom "L130"), [(2%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v135")]), (0), (Some 4), true, false, (Some (TAtom "v134")), (Some (4)))]); ((TAtom "L131"), []); ((TAtom "L124"), [(2%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v143")]), (0), (Some 8), false, true, (Some (TAtom "v142")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "v146")]), (0), (Some 4), false, true, (Some (TAtom "v146")), (Some (0)))]); ((TAtom "L125"), [(2%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v153")]), (0), (Some 4), true, false, (Some (TAtom "v152")), (Some (4)))]); ((TAtom "L147"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), false, true, (Some (TAtom "v158")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, false, (Some (TAtom "v163")), (Some (0)))]); ((TAtom "L168"), [(1%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, true, (Some (TAtom "v163")), (Some (0)))]); ((TAtom "L169"), []); ((TAtom "L180"), []); ((TAtom "L148"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), true, false, (Some (TAtom "v193")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), false, true, (Some (TAtom "v193")), (Some (4)))]); ((TAtom "L116"), [])].


End fn__IO_ferror.

Module fn___GI__IO_file_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_18, 66%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_18, 71%N)); ((TAtom "L12"), (file_18, 74%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_18, 74%N)); ((TAtom "L13"), (file_18, 74%N)); ((TAtom "L5"), (file_18, 76%N)); ((TAtom "L26"), (file_18, 81%N)); ((TAtom "L42"), (file_18, 81%N)); ((TAtom "L43"), (file_18, 81%N)); ((TAtom "L48"), (file_18, 79%N)); ((TAtom "L49"), (file_18, 79%N)); ((TAtom "L33"), (file_18, 84%N)); ((TAtom "L28"), (file_18, 87%N)); ((TAtom "L65"), (file_18, 87%N)); ((TAtom "L66"), (file_18, 87%N)); ((TAtom "L59"), (file_18, 88%N)); ((TAtom "L7"), (file_18, 69%N)); ((TAtom "L76"), (file_18, 93%N)); ((TAtom "L78"), (file_18, 94%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "size"); ((TAtom "pr.2"), "size"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v39"), "__dev_major"); ((TAtom "v40"), "__dev_major"); ((TAtom "v44"), "__dev_major"); ((TAtom "v50"), "fp"); ((TAtom "v56"), "fp"); ((TAtom "v73"), "size"); ((TAtom "v74"), "size"); ((TAtom "v75"), "p"); ((TAtom "v79"), "p"); ((TAtom "v8"), "fp"); ((TAtom "v87"), "fp"); ((TAtom "v88"), "p"); ((TAtom "v89"), "p"); ((TAtom "v90"), "size")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L7"), [(TAtom "v0")]); ((TAtom "L76"), []); ((TAtom "L78"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v54")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v69")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "v0"); (TAtom "v73")]); ((TAtom "L7"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")]); ((TAtom "L76"), []); ((TAtom "L78"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (144)))]); ((TAtom "L13"), []); ((TAtom "L5"), [(2%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 4), true, false, (Some (TAtom "v4")), (Some (24)))]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (40)))]); ((TAtom "L42"), []); ((TAtom "L43"), []); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L49"), []); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)))]); ((TAtom "L65"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)))]); ((TAtom "L66"), []); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)))]); ((TAtom "L7"), []); ((TAtom "L76"), []); ((TAtom "L78"), [])].


End fn___GI__IO_file_doallocate.

Module fn__IO_file_close_maybe_unlink.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 129%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 133%N)); ((TAtom "L5"), (file_19, 134%N)); ((TAtom "L7"), (file_19, 136%N)); ((TAtom "L23"), (file_19, 136%N)); ((TAtom "L24"), (file_19, 136%N)); ((TAtom "L16"), (file_19, 138%N)); ((TAtom "L31"), (file_19, 138%N)); ((TAtom "L32"), (file_19, 138%N)); ((TAtom "L17"), (file_19, 139%N)); ((TAtom "L81"), (file_19, 139%N)); ((TAtom "L86"), (file_19, 139%N)); ((TAtom "L92"), (file_19, 139%N)); ((TAtom "L87"), (file_19, 139%N)); ((TAtom "L110"), (file_19, 139%N)); ((TAtom "L118"), (file_19, 139%N)); ((TAtom "L82"), (file_19, 139%N)); ((TAtom "L74"), (file_19, 159%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 159%N)); ((TAtom "L147"), (file_19, 162%N)); ((TAtom "L155"), (file_19, 162%N)); ((TAtom "L148"), (file_19, 167%N)); ((TAtom "L161"), (file_19, 168%N)); ((TAtom "L163"), (file_19, 159%N)); ((TAtom "iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_2.join"), (file_19, 169%N)); ((TAtom "L191"), (file_19, 169%N)); ((TAtom "L192"), (file_19, 169%N)); ((TAtom "L179"), (file_19, 169%N)); ((TAtom "L18"), (file_19, 132%N)); ((TAtom "L202"), (file_19, 177%N)); ((TAtom "iw_3.L10"), (file_10, 1049%N)); ((TAtom "iw_3.join"), (file_19, 177%N)); ((TAtom "L204"), (file_19, 177%N)); ((TAtom "L221"), (file_19, 183%N)); ((TAtom "L228"), (file_19, 184%N)); ((TAtom "L230"), (file_19, 185%N)); ((TAtom "L223"), (file_19, 189%N)); ((TAtom "L277"), (file_19, 194%N)); ((TAtom "L279"), (file_19, 197%N)); ((TAtom "L299"), (file_19, 201%N)); ((TAtom "L300"), (file_19, 201%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "vtable"); ((TAtom "iw_3.v13"), "offset"); ((TAtom "iw_3.v18"), "vtable"); ((TAtom "iw_3.v3"), "vtable"); ((TAtom "iw_3.v4"), "ptr"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v9"), "offset"); ((TAtom "pr.1"), "flush_status"); ((TAtom "pr.2"), "flush_status"); ((TAtom "pr.3"), "flush_status"); ((TAtom "pr.4"), "flush_status"); ((TAtom "pr.5"), "o"); ((TAtom "v0"), "fp"); ((TAtom "v112"), "fp"); ((TAtom "v120"), "fp"); ((TAtom "v124"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v145"), "fp"); ((TAtom "v146"), "o"); ((TAtom "v150"), "o"); ((TAtom "v158"), "__libc_errno"); ((TAtom "v160"), "flush_status"); ((TAtom "v164"), "fp"); ((TAtom "v167"), "o"); ((TAtom "v168"), "fp"); ((TAtom "v171"), "fp"); ((TAtom "v177"), "o"); ((TAtom "v181"), "fp"); ((TAtom "v187"), "fp"); ((TAtom "v188"), "o"); ((TAtom "v19"), "fp"); ((TAtom "v194"), "__libc_errno"); ((TAtom "v199"), "flush_status"); ((TAtom "v2"), "unlink"); ((TAtom "v200"), "fp"); ((TAtom "v205"), "fp"); ((TAtom "v212"), "fp"); ((TAtom "v218"), "fp"); ((TAtom "v220"), "close_status"); ((TAtom "v224"), "fp"); ((TAtom "v231"), "fp"); ((TAtom "v239"), "fp"); ((TAtom "v240"), "fp"); ((TAtom "v241"), "fp"); ((TAtom "v245"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v25"), "fp"); ((TAtom "v252"), "fp"); ((TAtom "v256"), "fp"); ((TAtom "v260"), "fp"); ((TAtom "v264"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v267"), "fp"); ((TAtom "v269"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v273"), "fp"); ((TAtom "v275"), "fp"); ((TAtom "v280"), "unlink"); ((TAtom "v281"), "fp"); ((TAtom "v282"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v291"), "fp"); ((TAtom "v294"), "fp"); ((TAtom "v301"), "close_status"); ((TAtom "v302"), "close_status"); ((TAtom "v303"), "flush_status"); ((TAtom "v34"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v42"), "fp"); ((TAtom "v45"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v73"), "flush_status"); ((TAtom "v77"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v83"), "fp"); ((TAtom "v88"), "fp"); ((TAtom "v94"), "fp"); ((TAtom "v97"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L86"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L92"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L87"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L110"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L118"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L155"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L148"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L161"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L163"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "L191"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L192"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L179"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L202"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_3.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "L204"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L221"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L228"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L230"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L223"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L277"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L279"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L299"), [(TAtom "pr.3")]); ((TAtom "L300"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v28")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v51")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v72")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L86"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L92"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v102"); (TAtom "v2")]); ((TAtom "L87"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L110"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L118"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v131"); (TAtom "v2")]); ((TAtom "L82"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v141"); (TAtom "v2")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L155"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L148"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v146"); (TAtom "v2")]); ((TAtom "L161"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk23"); (TAtom "v0"); (TAtom "v177"); (TAtom "v2")]); ((TAtom "L163"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.5"); (TAtom "v0"); (TAtom "v183"); (TAtom "v2")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L191"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v195"); (TAtom "v2")]); ((TAtom "L192"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L179"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L202"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "iw_3.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v214")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v219")]); ((TAtom "L204"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L221"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L228"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk39"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L230"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v2"); (TAtom "v220")]); ((TAtom "L223"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L277"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v220")]); ((TAtom "L279"), [(TAtom "pr.3"); (TAtom "v220")]); ((TAtom "L299"), [(TAtom "pr.3")]); ((TAtom "L300"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L5"), []); ((TAtom "L7"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L23"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L24"), []); ((TAtom "L16"), [(2%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L31"), [(2%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32))); (4%N, (TApp "tmp" [(TAtom "v40")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L32"), [(2%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), true, false, (Some (TAtom "v55")), (Some (24))); (6%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (9%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v60")), (Some (32))); (10%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (13%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v65")), (Some (24)))]); ((TAtom "L17"), [(1%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L81"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L86"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L92"), [(2%N, (TApp "tmp" [(TAtom "v95")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v95")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L87"), []); ((TAtom "L110"), [(2%N, (TApp "tmp" [(TAtom "v113")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L118"), [(2%N, (TApp "tmp" [(TAtom "v121")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (4%N, (TApp "tmp" [(TAtom "v122")]), (0), (Some 8), true, false, (Some (TAtom "v122")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v121")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (8%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 8), true, false, (Some (TAtom "v126")), (Some (8)))]); ((TAtom "L82"), []); ((TAtom "L74"), [(2%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v143")]), (0), (Some 8), true, false, (Some (TAtom "v141")), (Some (72)))]); ((TAtom "L147"), [(2%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 4), true, false, (Some (TAtom "v157")), (Some (0)))]); ((TAtom "L155"), []); ((TAtom "L148"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L161"), [(2%N, (TApp "tmp" [(TAtom "v169")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (4%N, (TApp "tmp" [(TAtom "v169")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72)))]); ((TAtom "L163"), [(2%N, (TApp "tmp" [(TAtom "v182")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_2.L10"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v185")]), (0), (Some 8), true, false, (Some (TAtom "v183")), (Some (128)))]); ((TAtom "L191"), [(2%N, (TApp "tmp" [(TAtom "v193")]), (0), (Some 4), true, false, (Some (TAtom "v193")), (Some (0)))]); ((TAtom "L192"), []); ((TAtom "L179"), []); ((TAtom "L18"), [(3%N, (TApp "tmp" [(TAtom "v206")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)))]); ((TAtom "L202"), [(2%N, (TApp "tmp" [(TAtom "v213")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_3.L10"), []); ((TAtom "iw_3.join"), [(2%N, (TApp "tmp" [(TAtom "v216")]), (0), (Some 8), true, false, (Some (TAtom "v214")), (Some (136)))]); ((TAtom "L204"), [(2%N, (TApp "tmp" [(TAtom "v225")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L221"), [(2%N, (TApp "tmp" [(TAtom "v232")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v234")]), (0), (Some 8), true, false, (Some (TAtom "v233")), (Some (72)))]); ((TAtom "L228"), []); ((TAtom "L230"), [(3%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (6%N, (TApp "tmp" [(TAtom "v244")]), (0), (Some 8), false, true, (Some (TAtom "v243")), (Some (16))); (8%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (10%N, (TApp "tmp" [(TAtom "v247")]), (0), (Some 8), false, true, (Some (TAtom "v247")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (15%N, (TApp "tmp" [(TAtom "v251")]), (0), (Some 8), false, true, (Some (TAtom "v250")), (Some (8))); (17%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (19%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (22%N, (TApp "tmp" [(TAtom "v259")]), (0), (Some 8), false, true, (Some (TAtom "v258")), (Some (32))); (24%N, (TApp "tmp" [(TAtom "v255")]), (0), (Some 8), false, true, (Some (TAtom "v254")), (Some (24))); (26%N, (TApp "tmp" [(TAtom "v242")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (29%N, (TApp "tmp" [(TAtom "v263")]), (0), (Some 8), false, true, (Some (TAtom "v262")), (Some (40)))]); ((TAtom "L223"), [(3%N, (TApp "tmp" [(TAtom "v266")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (6%N, (TApp "tmp" [(TAtom "v268")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (9%N, (TApp "tmp" [(TAtom "v270")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16))); (13%N, (TApp "tmp" [(TAtom "v274")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40))); (15%N, (TApp "tmp" [(TAtom "v272")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (32))); (18%N, (TApp "tmp" [(TAtom "v276")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (48)))]); ((TAtom "L277"), []); ((TAtom "L279"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0))); (8%N, (TApp "tmp" [(TAtom "v292")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (112))); (11%N, (TApp "tmp" [(TAtom "v295")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (144)))]); ((TAtom "L299"), []); ((TAtom "L300"), [])].


End fn__IO_file_close_maybe_unlink.

Module fn__IO_new_file_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 211%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 214%N)); ((TAtom "L4"), (file_19, 216%N)); ((TAtom "L12"), (file_19, 216%N)); ((TAtom "L13"), (file_19, 216%N)); ((TAtom "L14"), (file_19, 217%N)); ((TAtom "L55"), (file_19, 218%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 218%N)); ((TAtom "L6"), (file_19, 220%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v20"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v62"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v70"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L55"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "L6"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L55"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v64")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L6"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32))); (4%N, (TApp "tmp" [(TAtom "v21")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v36")), (Some (24))); (6%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (9%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v41")), (Some (32))); (10%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (13%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v46")), (Some (24)))]); ((TAtom "L14"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L55"), [(2%N, (TApp "tmp" [(TAtom "v63")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v64")), (Some (136)))]); ((TAtom "L6"), [])].


End fn__IO_new_file_finish.

Module fn__IO_new_file_setbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 430%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 433%N)); ((TAtom "L6"), (file_19, 434%N)); ((TAtom "L8"), (file_19, 436%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v10"), "p"); ((TAtom "v11"), "len"); ((TAtom "v17"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "p"); ((TAtom "v21"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v36"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v4"), "len"); ((TAtom "v41"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L6"), []); ((TAtom "L8"), [(5%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56))); (7%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (48))); (9%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40))); (11%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (32))); (14%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56))); (16%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (19%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56))); (21%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (24%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56))); (26%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)))])].


End fn__IO_new_file_setbuf.

End HiAtexitSrc01.

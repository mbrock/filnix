(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


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

End fn__IO_new_file_setbuf.

Module fn__IO_file_setbuf_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 445%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 451%N)); ((TAtom "L21"), (file_19, 460%N)); ((TAtom "L23"), (file_19, 464%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v11"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v18"), "p"); ((TAtom "v19"), "len"); ((TAtom "v2"), "p"); ((TAtom "v20"), "result"); ((TAtom "v24"), "result"); ((TAtom "v28"), "fp"); ((TAtom "v32"), "fp"); ((TAtom "v38"), "result"); ((TAtom "v4"), "len"); ((TAtom "v7"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_setbuf_mmap.

Module fn__IO_new_do_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 472%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 475%N)); ((TAtom "iw_1.start"), (file_19, 484%N)); ((TAtom "iw_1.L7"), (file_19, 490%N)); ((TAtom "iw_1.L8"), (file_19, 491%N)); ((TAtom "iw_1.L17"), (file_19, 493%N)); ((TAtom "iw_1.iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.iw_1.join"), (file_19, 493%N)); ((TAtom "iw_1.L49"), (file_19, 497%N)); ((TAtom "iw_1.L9"), (file_19, 499%N)); ((TAtom "iw_1.iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_1.iw_2.join"), (file_19, 499%N)); ((TAtom "iw_1.L74"), (file_19, 500%N)); ((TAtom "iw_1.L75"), (file_19, 500%N)); ((TAtom "iw_1.L68"), (file_19, 501%N)); ((TAtom "iw_1.L70"), (file_19, 502%N)); ((TAtom "iw_1.L122"), (file_19, 504%N)); ((TAtom "iw_1.L123"), (file_19, 504%N)); ((TAtom "iw_1.L115"), (file_19, 504%N)); ((TAtom "iw_1.L116"), (file_19, 504%N)); ((TAtom "iw_1.L117"), (file_19, 504%N)); ((TAtom "iw_1.join"), (file_19, 475%N)); ((TAtom "L12"), (file_19, 475%N)); ((TAtom "L7"), (file_19, 475%N)); ((TAtom "L8"), (file_19, 475%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.iw_2.v0"), "vtable"); ((TAtom "iw_1.iw_2.v13"), "offset"); ((TAtom "iw_1.iw_2.v18"), "vtable"); ((TAtom "iw_1.iw_2.v3"), "vtable"); ((TAtom "iw_1.iw_2.v4"), "ptr"); ((TAtom "iw_1.iw_2.v6"), "ptr"); ((TAtom "iw_1.iw_2.v9"), "offset"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v10"), "fp"); ((TAtom "iw_1.v101"), "fp"); ((TAtom "iw_1.v103"), "fp"); ((TAtom "iw_1.v106"), "fp"); ((TAtom "iw_1.v108"), "fp"); ((TAtom "iw_1.v110"), "fp"); ((TAtom "iw_1.v113"), "fp"); ((TAtom "iw_1.v118"), "fp"); ((TAtom "iw_1.v124"), "fp"); ((TAtom "iw_1.v13"), "fp"); ((TAtom "iw_1.v130"), "fp"); ((TAtom "iw_1.v133"), "fp"); ((TAtom "iw_1.v137"), "count"); ((TAtom "iw_1.v2"), "data"); ((TAtom "iw_1.v20"), "fp"); ((TAtom "iw_1.v23"), "fp"); ((TAtom "iw_1.v30"), "fp"); ((TAtom "iw_1.v36"), "fp"); ((TAtom "iw_1.v37"), "fp"); ((TAtom "iw_1.v4"), "to_do"); ((TAtom "iw_1.v40"), "fp"); ((TAtom "iw_1.v46"), "new_pos"); ((TAtom "iw_1.v50"), "new_pos"); ((TAtom "iw_1.v55"), "fp"); ((TAtom "iw_1.v57"), "new_pos"); ((TAtom "iw_1.v58"), "fp"); ((TAtom "iw_1.v64"), "fp"); ((TAtom "iw_1.v65"), "data"); ((TAtom "iw_1.v66"), "to_do"); ((TAtom "iw_1.v67"), "count"); ((TAtom "iw_1.v71"), "fp"); ((TAtom "iw_1.v76"), "count"); ((TAtom "iw_1.v80"), "fp"); ((TAtom "iw_1.v82"), "fp"); ((TAtom "iw_1.v86"), "data"); ((TAtom "iw_1.v87"), "count"); ((TAtom "iw_1.v91"), "fp"); ((TAtom "iw_1.v93"), "fp"); ((TAtom "iw_1.v96"), "fp"); ((TAtom "iw_1.v98"), "fp"); ((TAtom "v0"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v14"), "data"); ((TAtom "v15"), "to_do"); ((TAtom "v17"), "to_do"); ((TAtom "v2"), "data"); ((TAtom "v4"), "to_do"); ((TAtom "v9"), "to_do")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_new_do_write.

Module fn__IO_new_file_underflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 510%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 516%N)); ((TAtom "L3"), (file_19, 517%N)); ((TAtom "L5"), (file_19, 519%N)); ((TAtom "L11"), (file_19, 521%N)); ((TAtom "L13"), (file_19, 525%N)); ((TAtom "L23"), (file_19, 526%N)); ((TAtom "L25"), (file_19, 528%N)); ((TAtom "L40"), (file_19, 531%N)); ((TAtom "L49"), (file_19, 533%N)); ((TAtom "iw_1.L4"), (file_10, 1059%N)); ((TAtom "iw_1.join"), (file_19, 534%N)); ((TAtom "L51"), (file_19, 536%N)); ((TAtom "L42"), (file_19, 540%N)); ((TAtom "L74"), (file_19, 547%N)); ((TAtom "L87"), (file_19, 547%N)); ((TAtom "L98"), (file_19, 547%N)); ((TAtom "L99"), (file_19, 547%N)); ((TAtom "L92"), (file_19, 547%N)); ((TAtom "L93"), (file_19, 547%N)); ((TAtom "L118"), (file_19, 547%N)); ((TAtom "L142"), (file_19, 547%N)); ((TAtom "L143"), (file_19, 547%N)); ((TAtom "L147"), (file_19, 547%N)); ((TAtom "L136"), (file_19, 547%N)); ((TAtom "L119"), (file_19, 547%N)); ((TAtom "L82"), (file_19, 549%N)); ((TAtom "L168"), (file_19, 551%N)); ((TAtom "iw_2.L10"), (file_10, 1049%N)); ((TAtom "iw_2.join"), (file_19, 551%N)); ((TAtom "iw_3.start"), (file_10, 999%N)); ((TAtom "iw_3.L5"), (file_10, 1000%N)); ((TAtom "iw_3.L19"), (file_10, 1000%N)); ((TAtom "iw_3.L28"), (file_10, 1000%N)); ((TAtom "iw_3.L29"), (file_10, 1000%N)); ((TAtom "iw_3.L22"), (file_10, 1000%N)); ((TAtom "iw_3.L23"), (file_10, 1000%N)); ((TAtom "iw_3.L45"), (file_10, 1000%N)); ((TAtom "iw_3.L66"), (file_10, 1000%N)); ((TAtom "iw_3.L67"), (file_10, 1000%N)); ((TAtom "iw_3.L78"), (file_10, 1000%N)); ((TAtom "iw_3.L46"), (file_10, 1000%N)); ((TAtom "L69"), (file_19, 556%N)); ((TAtom "iw_4.L10"), (file_10, 1049%N)); ((TAtom "iw_4.join"), (file_19, 567%N)); ((TAtom "L233"), (file_19, 571%N)); ((TAtom "L238"), (file_19, 572%N)); ((TAtom "L239"), (file_19, 574%N)); ((TAtom "L235"), (file_19, 513%N)); ((TAtom "L254"), (file_19, 582%N)); ((TAtom "L256"), (file_19, 585%N)); ((TAtom "L265"), (file_19, 586%N)); ((TAtom "L267"), (file_19, 587%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "p"); ((TAtom "iw_3.v15"), "fp"); ((TAtom "iw_3.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_3.v3"), "p"); ((TAtom "iw_3.v30"), "fp"); ((TAtom "iw_3.v38"), "fp"); ((TAtom "iw_3.v4"), "fp"); ((TAtom "iw_3.v42"), "fp"); ((TAtom "iw_3.v48"), "fp"); ((TAtom "iw_3.v54"), "fp"); ((TAtom "iw_3.v59"), "fp"); ((TAtom "iw_3.v61"), "__futex"); ((TAtom "iw_3.v64"), "__futex"); ((TAtom "iw_3.v68"), "__oldval"); ((TAtom "iw_3.v74"), "__oldval"); ((TAtom "iw_3.v8"), "fp"); ((TAtom "iw_3.v86"), "__futex"); ((TAtom "iw_3.v87"), "__futex"); ((TAtom "iw_3.v88"), "__private"); ((TAtom "iw_3.v89"), "fp"); ((TAtom "iw_4.v0"), "vtable"); ((TAtom "iw_4.v13"), "offset"); ((TAtom "iw_4.v18"), "vtable"); ((TAtom "iw_4.v3"), "vtable"); ((TAtom "iw_4.v4"), "ptr"); ((TAtom "iw_4.v6"), "ptr"); ((TAtom "iw_4.v9"), "offset"); ((TAtom "pr.1"), "count"); ((TAtom "pr.2"), "count"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "_IO_acquire_lock_file"); ((TAtom "v110"), "_IO_acquire_lock_file"); ((TAtom "v113"), "_IO_acquire_lock_file"); ((TAtom "v117"), "__self"); ((TAtom "v121"), "_IO_acquire_lock_file"); ((TAtom "v126"), "__self"); ((TAtom "v131"), "_IO_acquire_lock_file"); ((TAtom "v133"), "__futex"); ((TAtom "v138"), "__futex"); ((TAtom "v139"), "__atg3_old"); ((TAtom "v14"), "fp"); ((TAtom "v140"), "__atg3_old"); ((TAtom "v155"), "__futex"); ((TAtom "v156"), "__futex"); ((TAtom "v157"), "_IO_acquire_lock_file"); ((TAtom "v161"), "__self"); ((TAtom "v162"), "_IO_acquire_lock_file"); ((TAtom "v17"), "fp"); ((TAtom "v172"), "stdout"); ((TAtom "v180"), "stdout"); ((TAtom "v187"), "stdout"); ((TAtom "v190"), "fp"); ((TAtom "v192"), "fp"); ((TAtom "v194"), "fp"); ((TAtom "v196"), "fp"); ((TAtom "v199"), "fp"); ((TAtom "v201"), "fp"); ((TAtom "v204"), "fp"); ((TAtom "v206"), "fp"); ((TAtom "v208"), "fp"); ((TAtom "v210"), "fp"); ((TAtom "v213"), "fp"); ((TAtom "v219"), "fp"); ((TAtom "v220"), "fp"); ((TAtom "v223"), "fp"); ((TAtom "v226"), "fp"); ((TAtom "v232"), "count"); ((TAtom "v236"), "count"); ((TAtom "v241"), "count"); ((TAtom "v243"), "fp"); ((TAtom "v246"), "fp"); ((TAtom "v249"), "fp"); ((TAtom "v252"), "count"); ((TAtom "v257"), "count"); ((TAtom "v259"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v268"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v277"), "count"); ((TAtom "v279"), "fp"); ((TAtom "v29"), "fp"); ((TAtom "v35"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v59"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v62"), "fp"); ((TAtom "v66"), "fp"); ((TAtom "v70"), "fp"); ((TAtom "v79"), "stdout"); ((TAtom "v83"), "_IO_acquire_lock_file"); ((TAtom "v91"), "__self"); ((TAtom "v96"), "__libc_single_threaded_internal")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_3.L66")].

End fn__IO_new_file_underflow.

Module fn_glibc_fileops_mmap_remap_check.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 595%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 598%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 600%N)); ((TAtom "L15"), (file_19, 600%N)); ((TAtom "L16"), (file_19, 600%N)); ((TAtom "L23"), (file_19, 600%N)); ((TAtom "L24"), (file_19, 600%N)); ((TAtom "L34"), (file_19, 600%N)); ((TAtom "L31"), (file_19, 600%N)); ((TAtom "L3"), (file_19, 605%N)); ((TAtom "L48"), (file_19, 611%N)); ((TAtom "L49"), (file_19, 616%N)); ((TAtom "L125"), (file_19, 622%N)); ((TAtom "L184"), (file_19, 627%N)); ((TAtom "L186"), (file_19, 639%N)); ((TAtom "L126"), (file_19, 645%N)); ((TAtom "L50"), (file_19, 649%N)); ((TAtom "L248"), (file_19, 650%N)); ((TAtom "L249"), (file_19, 650%N)); ((TAtom "L250"), (file_19, 650%N)); ((TAtom "L280"), (file_19, 662%N)); ((TAtom "L296"), (file_19, 665%N)); ((TAtom "L297"), (file_19, 667%N)); ((TAtom "L282"), (file_19, 670%N)); ((TAtom "L4"), (file_19, 675%N)); ((TAtom "L207"), (file_19, 678%N)); ((TAtom "L360"), (file_19, 681%N)); ((TAtom "L361"), (file_19, 683%N)); ((TAtom "L362"), (file_19, 684%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v102"), "pagesize"); ((TAtom "v108"), "pagesize"); ((TAtom "v111"), "pagesize"); ((TAtom "v117"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v130"), "pagesize"); ((TAtom "v133"), "pagesize"); ((TAtom "v137"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v146"), "pagesize"); ((TAtom "v149"), "pagesize"); ((TAtom "v155"), "fp"); ((TAtom "v158"), "fp"); ((TAtom "v161"), "fp"); ((TAtom "v167"), "pagesize"); ((TAtom "v170"), "pagesize"); ((TAtom "v176"), "pagesize"); ((TAtom "v179"), "pagesize"); ((TAtom "v183"), "p"); ((TAtom "v187"), "p"); ((TAtom "v194"), "fp"); ((TAtom "v197"), "fp"); ((TAtom "v200"), "fp"); ((TAtom "v209"), "fp"); ((TAtom "v211"), "p"); ((TAtom "v212"), "fp"); ((TAtom "v214"), "fp"); ((TAtom "v220"), "fp"); ((TAtom "v222"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v231"), "fp"); ((TAtom "v234"), "fp"); ((TAtom "v241"), "fp"); ((TAtom "v243"), "fp"); ((TAtom "v246"), "fp"); ((TAtom "v251"), "fp"); ((TAtom "v254"), "fp"); ((TAtom "v257"), "fp"); ((TAtom "v264"), "fp"); ((TAtom "v267"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v275"), "fp"); ((TAtom "v277"), "fp"); ((TAtom "v283"), "fp"); ((TAtom "v286"), "fp"); ((TAtom "v289"), "fp"); ((TAtom "v299"), "fp"); ((TAtom "v302"), "fp"); ((TAtom "v305"), "fp"); ((TAtom "v312"), "fp"); ((TAtom "v315"), "fp"); ((TAtom "v322"), "fp"); ((TAtom "v325"), "fp"); ((TAtom "v327"), "fp"); ((TAtom "v330"), "fp"); ((TAtom "v337"), "fp"); ((TAtom "v340"), "fp"); ((TAtom "v343"), "fp"); ((TAtom "v350"), "fp"); ((TAtom "v352"), "fp"); ((TAtom "v354"), "fp"); ((TAtom "v356"), "fp"); ((TAtom "v358"), "fp"); ((TAtom "v363"), "fp"); ((TAtom "v367"), "fp"); ((TAtom "v371"), "fp"); ((TAtom "v375"), "fp"); ((TAtom "v47"), "pagesize"); ((TAtom "v53"), "pagesize"); ((TAtom "v56"), "pagesize"); ((TAtom "v6"), "fp"); ((TAtom "v60"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v69"), "pagesize"); ((TAtom "v72"), "pagesize"); ((TAtom "v77"), "fp"); ((TAtom "v82"), "pagesize"); ((TAtom "v85"), "pagesize"); ((TAtom "v90"), "fp"); ((TAtom "v93"), "fp"); ((TAtom "v99"), "pagesize")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn_glibc_fileops_mmap_remap_check.

Module fn__IO_file_underflow_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 691%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 694%N)); ((TAtom "L2"), (file_19, 695%N)); ((TAtom "L4"), (file_19, 697%N)); ((TAtom "L19"), (file_19, 699%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 699%N)); ((TAtom "L21"), (file_19, 701%N)); ((TAtom "L35"), (file_19, 702%N)); ((TAtom "L37"), (file_19, 704%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v22"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v32"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_underflow_mmap.

Module fn_glibc_fileops_decide_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 708%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 716%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 718%N)); ((TAtom "L15"), (file_19, 718%N)); ((TAtom "L16"), (file_19, 718%N)); ((TAtom "L23"), (file_19, 718%N)); ((TAtom "L24"), (file_19, 718%N)); ((TAtom "L34"), (file_19, 718%N)); ((TAtom "L31"), (file_19, 718%N)); ((TAtom "L45"), (file_19, 718%N)); ((TAtom "L53"), (file_19, 718%N)); ((TAtom "L46"), (file_19, 718%N)); ((TAtom "L3"), (file_19, 728%N)); ((TAtom "L72"), (file_19, 735%N)); ((TAtom "L82"), (file_19, 737%N)); ((TAtom "L83"), (file_19, 742%N)); ((TAtom "L108"), (file_19, 745%N)); ((TAtom "L110"), (file_19, 747%N)); ((TAtom "L139"), (file_19, 751%N)); ((TAtom "L140"), (file_19, 753%N)); ((TAtom "L141"), (file_19, 754%N)); ((TAtom "L5"), (file_19, 763%N)); ((TAtom "L160"), (file_19, 764%N)); ((TAtom "L161"), (file_19, 766%N)); ((TAtom "L162"), (file_19, 767%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v102"), "fp"); ((TAtom "v103"), "p"); ((TAtom "v104"), "p"); ((TAtom "v111"), "fp"); ((TAtom "v117"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v121"), "p"); ((TAtom "v122"), "fp"); ((TAtom "v124"), "p"); ((TAtom "v125"), "fp"); ((TAtom "v129"), "fp"); ((TAtom "v131"), "p"); ((TAtom "v135"), "fp"); ((TAtom "v142"), "fp"); ((TAtom "v146"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v154"), "fp"); ((TAtom "v163"), "fp"); ((TAtom "v167"), "fp"); ((TAtom "v171"), "fp"); ((TAtom "v175"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v71"), "p"); ((TAtom "v75"), "p"); ((TAtom "v85"), "fp"); ((TAtom "v94"), "p"); ((TAtom "v98"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn_glibc_fileops_decide_maybe_mmap.

Module fn__IO_file_underflow_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_19, 770%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_19, 775%N)); ((TAtom "iw_1.L10"), (file_10, 1049%N)); ((TAtom "iw_1.join"), (file_19, 776%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v2"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_underflow_maybe_mmap.

End HiAtexitSrc01.

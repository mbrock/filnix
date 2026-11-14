(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude HiAtexitTerm.
Import ListNotations.
Open Scope string_scope.

Module HiAtexitSrc.

Module fn_hi_atexit_close_stdout_hi.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("rocq/glibc/hi_atexit.c", 10%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("rocq/glibc/hi_atexit.c", 11%nat)); ((TAtom "L19"), ("rocq/glibc/hi_atexit.c", 14%nat)); ((TAtom "L20"), ("rocq/glibc/hi_atexit.c", 14%nat)); ((TAtom "L15"), ("rocq/glibc/hi_atexit.c", 15%nat)); ((TAtom "L28"), ("rocq/glibc/hi_atexit.c", 15%nat)); ((TAtom "L29"), ("rocq/glibc/hi_atexit.c", 15%nat)); ((TAtom "L24"), ("rocq/glibc/hi_atexit.c", 16%nat)); ((TAtom "L17"), ("rocq/glibc/hi_atexit.c", 10%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v12"), "stdout"); ((TAtom "v14"), "fclose_fail"); ((TAtom "v18"), "prev_fail"); ((TAtom "v2"), "stdout"); ((TAtom "v21"), "fclose_fail"); ((TAtom "v27"), "pending"); ((TAtom "v30"), "fclose_fail"); ((TAtom "v4"), "pending"); ((TAtom "v7"), "stdout"); ((TAtom "v9"), "prev_fail")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "hi_atexit#close_stdout_hi") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_hi_atexit_close_stdout_hi.

Module fn_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("rocq/glibc/hi_atexit.c", 20%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("rocq/glibc/hi_atexit.c", 21%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "main") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_main.

Module fn_malloc___libc_malloc2.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("malloc.c", 3065%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("malloc.c", 3069%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "ar_ptr"); ((TAtom "pr.2"), "ar_ptr"); ((TAtom "pr.3"), "ar_ptr"); ((TAtom "pr.4"), "victim"); ((TAtom "v0"), "bytes"); ((TAtom "v101"), "victim"); ((TAtom "v107"), "ar_ptr"); ((TAtom "v116"), "ar_ptr"); ((TAtom "v117"), "bytes"); ((TAtom "v118"), "ar_ptr"); ((TAtom "v119"), "ar_ptr"); ((TAtom "v120"), "bytes"); ((TAtom "v121"), "victim"); ((TAtom "v125"), "ar_ptr"); ((TAtom "v130"), "ar_ptr"); ((TAtom "v133"), "__futex"); ((TAtom "v137"), "__oldval"); ((TAtom "v14"), "__libc_single_threaded_internal"); ((TAtom "v143"), "__oldval"); ((TAtom "v155"), "__futex"); ((TAtom "v156"), "__futex"); ((TAtom "v157"), "__private"); ((TAtom "v161"), "victim"); ((TAtom "v167"), "victim"); ((TAtom "v17"), "bytes"); ((TAtom "v178"), "ar_ptr"); ((TAtom "v179"), "victim"); ((TAtom "v18"), "victim"); ((TAtom "v191"), "victim"); ((TAtom "v22"), "victim"); ((TAtom "v28"), "victim"); ((TAtom "v40"), "victim"); ((TAtom "v5"), "bytes"); ((TAtom "v52"), "victim"); ((TAtom "v58"), "thread_arena"); ((TAtom "v65"), "ar_ptr"); ((TAtom "v69"), "ar_ptr"); ((TAtom "v74"), "__futex"); ((TAtom "v75"), "__atg3_old"); ((TAtom "v76"), "__atg3_old"); ((TAtom "v91"), "__futex"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "bytes"); ((TAtom "v94"), "ar_ptr"); ((TAtom "v95"), "ar_ptr"); ((TAtom "v96"), "bytes"); ((TAtom "v97"), "victim")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "malloc#__libc_malloc2") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_malloc___libc_malloc2.

Module fn___GI___libc_malloc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("malloc.c", 3102%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("malloc.c", 1136%nat)); ((TAtom "iw_1.L4"), ("malloc.c", 1139%nat)); ((TAtom "iw_1.L76"), ("malloc.c", 1139%nat)); ((TAtom "iw_1.join"), ("malloc.c", 3108%nat)); ((TAtom "L26"), ("malloc.c", 3110%nat)); ((TAtom "L43"), ("malloc.c", 3114%nat)); ((TAtom "iw_2.start"), ("malloc.c", 2879%nat)); ((TAtom "iw_2.iw_1.L22"), ("malloc.c", 2857%nat)); ((TAtom "iw_2.iw_1.L38"), ("malloc.c", 2860%nat)); ((TAtom "iw_3.start"), ("../stdlib/stdbit.h", 79%nat)); ((TAtom "iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 79%nat)); ((TAtom "iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 79%nat)); ((TAtom "iw_4.iw_1.L18"), ("malloc.c", 2887%nat)); ((TAtom "iw_4.iw_1.L25"), ("malloc.c", 2888%nat)); ((TAtom "iw_4.iw_1.L26"), ("malloc.c", 2888%nat)); ((TAtom "iw_4.iw_1.L19"), ("malloc.c", 2892%nat)); ((TAtom "iw_4.iw_1.join"), ("malloc.c", 2919%nat)); ((TAtom "iw_4.L18"), ("malloc.c", 2919%nat)); ((TAtom "iw_4.L19"), ("malloc.c", 2919%nat)); ((TAtom "iw_4.iw_2.start"), ("malloc.c", 2851%nat)); ((TAtom "iw_4.iw_2.L7"), ("malloc.c", 2852%nat)); ((TAtom "iw_4.iw_2.L8"), ("malloc.c", 2854%nat)); ((TAtom "iw_4.iw_2.L9"), ("malloc.c", 2850%nat)); ((TAtom "iw_4.iw_2.L22"), ("malloc.c", 2857%nat)); ((TAtom "iw_4.iw_2.L24"), ("malloc.c", 2859%nat)); ((TAtom "iw_4.iw_2.L38"), ("malloc.c", 2860%nat)); ((TAtom "iw_4.iw_2.L39"), ("malloc.c", 2862%nat)); ((TAtom "iw_4.iw_2.L40"), ("malloc.c", 2864%nat)); ((TAtom "iw_4.join"), ("malloc.c", 3121%nat)); ((TAtom "L72"), ("malloc.c", 3122%nat)); ((TAtom "L7"), ("malloc.c", 3127%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "req"); ((TAtom "iw_1.v13"), "req"); ((TAtom "iw_1.v5"), "req"); ((TAtom "iw_1.v63"), "req"); ((TAtom "iw_2.iw_1.pr.1"), "e"); ((TAtom "iw_2.iw_1.v0"), "tc_idx"); ((TAtom "iw_2.iw_1.v10"), "mangled"); ((TAtom "iw_2.iw_1.v12"), "ep"); ((TAtom "iw_2.iw_1.v13"), "e"); ((TAtom "iw_2.iw_1.v14"), "ep"); ((TAtom "iw_2.iw_1.v17"), "ep"); ((TAtom "iw_2.iw_1.v2"), "ep"); ((TAtom "iw_2.iw_1.v21"), "e"); ((TAtom "iw_2.iw_1.v25"), "e"); ((TAtom "iw_2.iw_1.v4"), "mangled"); ((TAtom "iw_2.iw_1.v41"), "mangled"); ((TAtom "iw_2.iw_1.v43"), "ep"); ((TAtom "iw_2.iw_1.v44"), "e"); ((TAtom "iw_2.iw_1.v47"), "e"); ((TAtom "iw_2.iw_1.v52"), "ep"); ((TAtom "iw_2.iw_1.v53"), "ep"); ((TAtom "iw_2.iw_1.v56"), "e"); ((TAtom "iw_2.iw_1.v59"), "e"); ((TAtom "iw_2.iw_1.v68"), "tcache"); ((TAtom "iw_2.iw_1.v69"), "tc_idx"); ((TAtom "iw_2.iw_1.v75"), "e"); ((TAtom "iw_2.iw_1.v77"), "e"); ((TAtom "iw_2.v0"), "tc_idx"); ((TAtom "iw_2.v2"), "tc_idx"); ((TAtom "iw_2.v4"), "tcache"); ((TAtom "iw_2.v6"), "tc_idx"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.v2"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_2.v2"), "__x"); ((TAtom "iw_3.v0"), "nb"); ((TAtom "iw_3.v3"), "nb"); ((TAtom "iw_3.v36"), "idx"); ((TAtom "iw_3.v37"), "idx"); ((TAtom "iw_4.iw_1.pr.1"), "tep"); ((TAtom "iw_4.iw_1.pr.2"), "te"); ((TAtom "iw_4.iw_1.v0"), "nb"); ((TAtom "iw_4.iw_1.v10"), "tcache"); ((TAtom "iw_4.iw_1.v12"), "tc_idx"); ((TAtom "iw_4.iw_1.v14"), "tep"); ((TAtom "iw_4.iw_1.v16"), "tep"); ((TAtom "iw_4.iw_1.v17"), "te"); ((TAtom "iw_4.iw_1.v2"), "tc_idx"); ((TAtom "iw_4.iw_1.v21"), "te"); ((TAtom "iw_4.iw_1.v27"), "te"); ((TAtom "iw_4.iw_1.v37"), "nb"); ((TAtom "iw_4.iw_1.v4"), "mangled"); ((TAtom "iw_4.iw_1.v43"), "te"); ((TAtom "iw_4.iw_1.v44"), "te"); ((TAtom "iw_4.iw_1.v47"), "te"); ((TAtom "iw_4.iw_1.v51"), "te"); ((TAtom "iw_4.iw_1.v52"), "mangled"); ((TAtom "iw_4.iw_1.v54"), "demangled_ptr"); ((TAtom "iw_4.iw_1.v55"), "te"); ((TAtom "iw_4.iw_1.v56"), "tep"); ((TAtom "iw_4.iw_1.v6"), "demangled_ptr"); ((TAtom "iw_4.iw_2.pr.1"), "e"); ((TAtom "iw_4.iw_2.v0"), "tc_idx"); ((TAtom "iw_4.iw_2.v10"), "mangled"); ((TAtom "iw_4.iw_2.v12"), "ep"); ((TAtom "iw_4.iw_2.v13"), "e"); ((TAtom "iw_4.iw_2.v14"), "ep"); ((TAtom "iw_4.iw_2.v17"), "ep"); ((TAtom "iw_4.iw_2.v2"), "ep"); ((TAtom "iw_4.iw_2.v21"), "e"); ((TAtom "iw_4.iw_2.v25"), "e"); ((TAtom "iw_4.iw_2.v4"), "mangled"); ((TAtom "iw_4.iw_2.v41"), "mangled"); ((TAtom "iw_4.iw_2.v43"), "ep"); ((TAtom "iw_4.iw_2.v44"), "e"); ((TAtom "iw_4.iw_2.v47"), "e"); ((TAtom "iw_4.iw_2.v52"), "ep"); ((TAtom "iw_4.iw_2.v53"), "ep"); ((TAtom "iw_4.iw_2.v56"), "e"); ((TAtom "iw_4.iw_2.v59"), "e"); ((TAtom "iw_4.iw_2.v68"), "tcache"); ((TAtom "iw_4.iw_2.v69"), "tc_idx"); ((TAtom "iw_4.iw_2.v75"), "e"); ((TAtom "iw_4.iw_2.v77"), "e"); ((TAtom "iw_4.pr.1"), "mangled"); ((TAtom "iw_4.v0"), "tc_idx"); ((TAtom "iw_4.v10"), "entry"); ((TAtom "iw_4.v14"), "te"); ((TAtom "iw_4.v2"), "nb"); ((TAtom "iw_4.v20"), "nb"); ((TAtom "iw_4.v21"), "te"); ((TAtom "iw_4.v35"), "tc_idx"); ((TAtom "iw_4.v36"), "entry"); ((TAtom "iw_4.v37"), "mangled"); ((TAtom "iw_4.v6"), "mangled"); ((TAtom "iw_4.v8"), "nb"); ((TAtom "iw_4.v9"), "tc_idx"); ((TAtom "v0"), "bytes"); ((TAtom "v14"), "nb"); ((TAtom "v3"), "bytes"); ((TAtom "v4"), "nb"); ((TAtom "v42"), "tc_idx"); ((TAtom "v46"), "tc_idx"); ((TAtom "v54"), "tcache"); ((TAtom "v56"), "tc_idx"); ((TAtom "v63"), "tc_idx"); ((TAtom "v66"), "nb"); ((TAtom "v67"), "tc_idx"); ((TAtom "v69"), "tc_idx"); ((TAtom "v70"), "nb"); ((TAtom "v71"), "victim"); ((TAtom "v75"), "victim"); ((TAtom "v79"), "victim"); ((TAtom "v8"), "nb"); ((TAtom "v81"), "bytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_4.iw_1.L18")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_malloc") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_malloc.

Module fn___GI___libc_free.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("malloc.c", 3138%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("malloc.c", 3142%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "mem"); ((TAtom "v103"), "tc_idx"); ((TAtom "v107"), "tc_idx"); ((TAtom "v11"), "mem"); ((TAtom "v115"), "tcache"); ((TAtom "v116"), "tc_idx"); ((TAtom "v123"), "p"); ((TAtom "v124"), "tc_idx"); ((TAtom "v126"), "size"); ((TAtom "v127"), "tc_idx"); ((TAtom "v131"), "size"); ((TAtom "v155"), "tcache"); ((TAtom "v156"), "tc_idx"); ((TAtom "v16"), "mem"); ((TAtom "v165"), "p"); ((TAtom "v166"), "tc_idx"); ((TAtom "v175"), "mem"); ((TAtom "v18"), "p"); ((TAtom "v192"), "p"); ((TAtom "v195"), "size"); ((TAtom "v20"), "p"); ((TAtom "v228"), "p"); ((TAtom "v231"), "size"); ((TAtom "v268"), "p"); ((TAtom "v27"), "size"); ((TAtom "v271"), "size"); ((TAtom "v300"), "size"); ((TAtom "v31"), "p"); ((TAtom "v322"), "p"); ((TAtom "v333"), "p"); ((TAtom "v336"), "size"); ((TAtom "v369"), "p"); ((TAtom "v372"), "size"); ((TAtom "v409"), "p"); ((TAtom "v412"), "size"); ((TAtom "v437"), "size"); ((TAtom "v469"), "p"); ((TAtom "v472"), "size"); ((TAtom "v5"), "mem"); ((TAtom "v50"), "size"); ((TAtom "v505"), "p"); ((TAtom "v508"), "size"); ((TAtom "v544"), "p"); ((TAtom "v547"), "size"); ((TAtom "v574"), "size"); ((TAtom "v58"), "p"); ((TAtom "v596"), "p"); ((TAtom "v60"), "e"); ((TAtom "v603"), "p"); ((TAtom "v606"), "size"); ((TAtom "v627"), "p"); ((TAtom "v629"), "size"); ((TAtom "v64"), "e"); ((TAtom "v655"), "size"); ((TAtom "v677"), "p"); ((TAtom "v679"), "p"); ((TAtom "v68"), "tcache_key"); ((TAtom "v681"), "size"); ((TAtom "v704"), "p"); ((TAtom "v706"), "size"); ((TAtom "v72"), "e"); ((TAtom "v728"), "size"); ((TAtom "v75"), "size"); ((TAtom "v757"), "p"); ((TAtom "v759"), "p"); ((TAtom "v760"), "size")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_free") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_free.

Module fn___libc_calloc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("malloc.c", 3539%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("malloc.c", 3544%nat)); ((TAtom "L5"), ("malloc.c", 3546%nat)); ((TAtom "L41"), ("malloc.c", 3551%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "req"); ((TAtom "iw_1.v13"), "req"); ((TAtom "iw_1.v5"), "req"); ((TAtom "iw_1.v63"), "req"); ((TAtom "iw_2.iw_1.pr.1"), "e"); ((TAtom "iw_2.iw_1.v0"), "tc_idx"); ((TAtom "iw_2.iw_1.v10"), "mangled"); ((TAtom "iw_2.iw_1.v12"), "ep"); ((TAtom "iw_2.iw_1.v13"), "e"); ((TAtom "iw_2.iw_1.v14"), "ep"); ((TAtom "iw_2.iw_1.v17"), "ep"); ((TAtom "iw_2.iw_1.v2"), "ep"); ((TAtom "iw_2.iw_1.v21"), "e"); ((TAtom "iw_2.iw_1.v25"), "e"); ((TAtom "iw_2.iw_1.v4"), "mangled"); ((TAtom "iw_2.iw_1.v41"), "mangled"); ((TAtom "iw_2.iw_1.v43"), "ep"); ((TAtom "iw_2.iw_1.v44"), "e"); ((TAtom "iw_2.iw_1.v47"), "e"); ((TAtom "iw_2.iw_1.v52"), "ep"); ((TAtom "iw_2.iw_1.v53"), "ep"); ((TAtom "iw_2.iw_1.v56"), "e"); ((TAtom "iw_2.iw_1.v59"), "e"); ((TAtom "iw_2.iw_1.v68"), "tcache"); ((TAtom "iw_2.iw_1.v69"), "tc_idx"); ((TAtom "iw_2.iw_1.v75"), "e"); ((TAtom "iw_2.iw_1.v77"), "e"); ((TAtom "iw_2.v0"), "tc_idx"); ((TAtom "iw_2.v2"), "tc_idx"); ((TAtom "iw_2.v4"), "tcache"); ((TAtom "iw_2.v6"), "tc_idx"); ((TAtom "iw_3.v0"), "p"); ((TAtom "iw_3.v12"), "nclears"); ((TAtom "iw_3.v14"), "d"); ((TAtom "iw_3.v15"), "clearsize"); ((TAtom "iw_3.v2"), "clearsize"); ((TAtom "iw_3.v21"), "nclears"); ((TAtom "iw_3.v24"), "d"); ((TAtom "iw_3.v26"), "d"); ((TAtom "iw_3.v28"), "d"); ((TAtom "iw_3.v30"), "d"); ((TAtom "iw_3.v31"), "nclears"); ((TAtom "iw_3.v35"), "d"); ((TAtom "iw_3.v36"), "nclears"); ((TAtom "iw_3.v44"), "nclears"); ((TAtom "iw_3.v46"), "d"); ((TAtom "iw_3.v48"), "d"); ((TAtom "iw_3.v5"), "p"); ((TAtom "iw_3.v51"), "d"); ((TAtom "iw_3.v52"), "nclears"); ((TAtom "iw_3.v56"), "d"); ((TAtom "iw_3.v57"), "nclears"); ((TAtom "iw_3.v62"), "d"); ((TAtom "iw_3.v7"), "clearsize"); ((TAtom "iw_3.v8"), "nclears"); ((TAtom "iw_4.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_1.v2"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_4.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_4.iw_2.v0"), "__x"); ((TAtom "iw_4.iw_2.v2"), "__x"); ((TAtom "iw_4.v0"), "nb"); ((TAtom "iw_4.v3"), "nb"); ((TAtom "iw_4.v36"), "idx"); ((TAtom "iw_4.v37"), "idx"); ((TAtom "iw_5.iw_1.pr.1"), "tep"); ((TAtom "iw_5.iw_1.pr.2"), "te"); ((TAtom "iw_5.iw_1.v0"), "nb"); ((TAtom "iw_5.iw_1.v10"), "tcache"); ((TAtom "iw_5.iw_1.v12"), "tc_idx"); ((TAtom "iw_5.iw_1.v14"), "tep"); ((TAtom "iw_5.iw_1.v16"), "tep"); ((TAtom "iw_5.iw_1.v17"), "te"); ((TAtom "iw_5.iw_1.v2"), "tc_idx"); ((TAtom "iw_5.iw_1.v21"), "te"); ((TAtom "iw_5.iw_1.v27"), "te"); ((TAtom "iw_5.iw_1.v37"), "nb"); ((TAtom "iw_5.iw_1.v4"), "mangled"); ((TAtom "iw_5.iw_1.v43"), "te"); ((TAtom "iw_5.iw_1.v44"), "te"); ((TAtom "iw_5.iw_1.v47"), "te"); ((TAtom "iw_5.iw_1.v51"), "te"); ((TAtom "iw_5.iw_1.v52"), "mangled"); ((TAtom "iw_5.iw_1.v54"), "demangled_ptr"); ((TAtom "iw_5.iw_1.v55"), "te"); ((TAtom "iw_5.iw_1.v56"), "tep"); ((TAtom "iw_5.iw_1.v6"), "demangled_ptr"); ((TAtom "iw_5.iw_2.pr.1"), "e"); ((TAtom "iw_5.iw_2.v0"), "tc_idx"); ((TAtom "iw_5.iw_2.v10"), "mangled"); ((TAtom "iw_5.iw_2.v12"), "ep"); ((TAtom "iw_5.iw_2.v13"), "e"); ((TAtom "iw_5.iw_2.v14"), "ep"); ((TAtom "iw_5.iw_2.v17"), "ep"); ((TAtom "iw_5.iw_2.v2"), "ep"); ((TAtom "iw_5.iw_2.v21"), "e"); ((TAtom "iw_5.iw_2.v25"), "e"); ((TAtom "iw_5.iw_2.v4"), "mangled"); ((TAtom "iw_5.iw_2.v41"), "mangled"); ((TAtom "iw_5.iw_2.v43"), "ep"); ((TAtom "iw_5.iw_2.v44"), "e"); ((TAtom "iw_5.iw_2.v47"), "e"); ((TAtom "iw_5.iw_2.v52"), "ep"); ((TAtom "iw_5.iw_2.v53"), "ep"); ((TAtom "iw_5.iw_2.v56"), "e"); ((TAtom "iw_5.iw_2.v59"), "e"); ((TAtom "iw_5.iw_2.v68"), "tcache"); ((TAtom "iw_5.iw_2.v69"), "tc_idx"); ((TAtom "iw_5.iw_2.v75"), "e"); ((TAtom "iw_5.iw_2.v77"), "e"); ((TAtom "iw_5.pr.1"), "mangled"); ((TAtom "iw_5.v0"), "tc_idx"); ((TAtom "iw_5.v10"), "entry"); ((TAtom "iw_5.v14"), "te"); ((TAtom "iw_5.v2"), "nb"); ((TAtom "iw_5.v20"), "nb"); ((TAtom "iw_5.v21"), "te"); ((TAtom "iw_5.v35"), "tc_idx"); ((TAtom "iw_5.v36"), "entry"); ((TAtom "iw_5.v37"), "mangled"); ((TAtom "iw_5.v6"), "mangled"); ((TAtom "iw_5.v8"), "nb"); ((TAtom "iw_5.v9"), "tc_idx"); ((TAtom "v0"), "n"); ((TAtom "v10"), "bytes"); ((TAtom "v101"), "tc_idx"); ((TAtom "v108"), "tc_idx"); ((TAtom "v110"), "tc_idx"); ((TAtom "v142"), "nb"); ((TAtom "v143"), "tc_idx"); ((TAtom "v145"), "tc_idx"); ((TAtom "v146"), "nb"); ((TAtom "v147"), "mem"); ((TAtom "v151"), "mem"); ((TAtom "v155"), "mem"); ((TAtom "v156"), "mem"); ((TAtom "v171"), "bytes"); ((TAtom "v2"), "elem_size"); ((TAtom "v44"), "bytes"); ((TAtom "v48"), "bytes"); ((TAtom "v49"), "nb"); ((TAtom "v53"), "nb"); ((TAtom "v59"), "nb"); ((TAtom "v8"), "n"); ((TAtom "v87"), "tc_idx"); ((TAtom "v9"), "elem_size"); ((TAtom "v91"), "tc_idx"); ((TAtom "v99"), "tcache")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__libc_calloc") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___libc_calloc.

Module fn_malloc_malloc_printerr.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("malloc.c", 5135%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("malloc.c", 5139%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "str"); ((TAtom "v4"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "malloc#malloc_printerr") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_malloc_malloc_printerr.

Module fn___internal_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("cxa_atexit.c", 32%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("cxa_atexit.c", 41%nat)); ((TAtom "L10"), ("cxa_atexit.c", 41%nat)); ((TAtom "L11"), ("cxa_atexit.c", 43%nat)); ((TAtom "L29"), ("cxa_atexit.c", 43%nat)); ((TAtom "L30"), ("cxa_atexit.c", 43%nat)); ((TAtom "L34"), ("cxa_atexit.c", 43%nat)); ((TAtom "L23"), ("cxa_atexit.c", 44%nat)); ((TAtom "L46"), ("cxa_atexit.c", 48%nat)); ((TAtom "L59"), ("cxa_atexit.c", 48%nat)); ((TAtom "L60"), ("cxa_atexit.c", 48%nat)); ((TAtom "L71"), ("cxa_atexit.c", 48%nat)); ((TAtom "L66"), ("cxa_atexit.c", 49%nat)); ((TAtom "L48"), ("cxa_atexit.c", 53%nat)); ((TAtom "L103"), ("cxa_atexit.c", 57%nat)); ((TAtom "L104"), ("cxa_atexit.c", 57%nat)); ((TAtom "L115"), ("cxa_atexit.c", 57%nat)); ((TAtom "L110"), ("cxa_atexit.c", 58%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v101"), "__futex"); ((TAtom "v105"), "__oldval"); ((TAtom "v111"), "__oldval"); ((TAtom "v12"), "func"); ((TAtom "v123"), "__futex"); ((TAtom "v124"), "__futex"); ((TAtom "v125"), "__private"); ((TAtom "v2"), "arg"); ((TAtom "v25"), "__futex"); ((TAtom "v26"), "__atg3_old"); ((TAtom "v27"), "__atg3_old"); ((TAtom "v4"), "d"); ((TAtom "v42"), "__futex"); ((TAtom "v43"), "__futex"); ((TAtom "v44"), "listp"); ((TAtom "v45"), "new"); ((TAtom "v49"), "new"); ((TAtom "v57"), "__futex"); ((TAtom "v6"), "listp"); ((TAtom "v61"), "__oldval"); ((TAtom "v67"), "__oldval"); ((TAtom "v79"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__private"); ((TAtom "v84"), "func"); ((TAtom "v85"), "new"); ((TAtom "v87"), "func"); ((TAtom "v88"), "new"); ((TAtom "v91"), "arg"); ((TAtom "v92"), "new"); ((TAtom "v95"), "d"); ((TAtom "v96"), "new")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L103"); (TAtom "L59")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__internal_atexit") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___internal_atexit.

Module fn___GI___cxa_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("cxa_atexit.c", 65%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("cxa_atexit.c", 68%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "arg"); ((TAtom "v4"), "d"); ((TAtom "v6"), "func"); ((TAtom "v7"), "arg"); ((TAtom "v8"), "d")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___cxa_atexit") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___cxa_atexit.

Module fn___new_exitfn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("cxa_atexit.c", 78%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("cxa_atexit.c", 86%nat)); ((TAtom "L6"), ("cxa_atexit.c", 89%nat)); ((TAtom "L8"), ("cxa_atexit.c", 91%nat)); ((TAtom "L14"), ("cxa_atexit.c", 84%nat)); ((TAtom "L15"), ("cxa_atexit.c", 93%nat)); ((TAtom "L25"), ("cxa_atexit.c", 84%nat)); ((TAtom "L26"), ("cxa_atexit.c", 94%nat)); ((TAtom "L28"), ("cxa_atexit.c", 97%nat)); ((TAtom "L47"), ("cxa_atexit.c", 101%nat)); ((TAtom "L17"), ("cxa_atexit.c", 84%nat)); ((TAtom "L63"), ("cxa_atexit.c", 104%nat)); ((TAtom "L64"), ("cxa_atexit.c", 104%nat)); ((TAtom "L56"), ("cxa_atexit.c", 108%nat)); ((TAtom "L70"), ("cxa_atexit.c", 110%nat)); ((TAtom "L78"), ("cxa_atexit.c", 110%nat)); ((TAtom "L79"), ("cxa_atexit.c", 111%nat)); ((TAtom "L88"), ("cxa_atexit.c", 115%nat)); ((TAtom "L72"), ("cxa_atexit.c", 81%nat)); ((TAtom "L100"), ("cxa_atexit.c", 122%nat)); ((TAtom "L57"), ("cxa_atexit.c", 129%nat)); ((TAtom "L58"), ("cxa_atexit.c", 83%nat)); ((TAtom "L121"), ("cxa_atexit.c", 136%nat)); ((TAtom "L123"), ("cxa_atexit.c", 140%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "p"); ((TAtom "pr.2"), "p"); ((TAtom "pr.3"), "l"); ((TAtom "pr.4"), "r"); ((TAtom "pr.5"), "r"); ((TAtom "pr.6"), "i"); ((TAtom "pr.7"), "i"); ((TAtom "pr.8"), "i"); ((TAtom "v0"), "listp"); ((TAtom "v10"), "__exit_funcs_done"); ((TAtom "v103"), "p"); ((TAtom "v107"), "p"); ((TAtom "v109"), "r"); ((TAtom "v110"), "p"); ((TAtom "v112"), "l"); ((TAtom "v114"), "i"); ((TAtom "v116"), "r"); ((TAtom "v117"), "l"); ((TAtom "v119"), "i"); ((TAtom "v12"), "listp"); ((TAtom "v124"), "r"); ((TAtom "v128"), "r"); ((TAtom "v13"), "l"); ((TAtom "v130"), "__new_exitfn_called"); ((TAtom "v131"), "__new_exitfn_called"); ((TAtom "v132"), "r"); ((TAtom "v18"), "l"); ((TAtom "v22"), "l"); ((TAtom "v24"), "i"); ((TAtom "v29"), "i"); ((TAtom "v34"), "l"); ((TAtom "v36"), "i"); ((TAtom "v43"), "i"); ((TAtom "v44"), "i"); ((TAtom "v48"), "i"); ((TAtom "v51"), "l"); ((TAtom "v53"), "l"); ((TAtom "v54"), "l"); ((TAtom "v55"), "l"); ((TAtom "v59"), "l"); ((TAtom "v65"), "i"); ((TAtom "v73"), "p"); ((TAtom "v80"), "l"); ((TAtom "v87"), "p"); ((TAtom "v91"), "p"); ((TAtom "v95"), "p"); ((TAtom "v96"), "listp"); ((TAtom "v98"), "listp"); ((TAtom "v99"), "p")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L14"); (TAtom "L25")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__new_exitfn") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___new_exitfn.

Module fn_atexit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("atexit.c", 40%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("atexit.c", 46%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "func"); ((TAtom "v2"), "func")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "atexit") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_atexit.

Module fn___fpending.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("__fpending.c", 20%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("__fpending.c", 23%nat)); ((TAtom "L2"), ("__fpending.c", 24%nat)); ((TAtom "L3"), ("__fpending.c", 26%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__fpending") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___fpending.

Module fn__IO_ferror.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("ferror.c", 30%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("ferror.c", 35%nat)); ((TAtom "L6"), ("ferror.c", 36%nat)); ((TAtom "L8"), ("ferror.c", 37%nat)); ((TAtom "L29"), ("ferror.c", 37%nat)); ((TAtom "L40"), ("ferror.c", 37%nat)); ((TAtom "L41"), ("ferror.c", 37%nat)); ((TAtom "L34"), ("ferror.c", 37%nat)); ((TAtom "L35"), ("ferror.c", 37%nat)); ((TAtom "L60"), ("ferror.c", 37%nat)); ((TAtom "L84"), ("ferror.c", 37%nat)); ((TAtom "L85"), ("ferror.c", 37%nat)); ((TAtom "L89"), ("ferror.c", 37%nat)); ((TAtom "L78"), ("ferror.c", 37%nat)); ((TAtom "L61"), ("ferror.c", 37%nat)); ((TAtom "L24"), ("ferror.c", 38%nat)); ((TAtom "L121"), ("ferror.c", 39%nat)); ((TAtom "L130"), ("ferror.c", 39%nat)); ((TAtom "L131"), ("ferror.c", 39%nat)); ((TAtom "L124"), ("ferror.c", 39%nat)); ((TAtom "L125"), ("ferror.c", 39%nat)); ((TAtom "L147"), ("ferror.c", 39%nat)); ((TAtom "L168"), ("ferror.c", 39%nat)); ((TAtom "L169"), ("ferror.c", 39%nat)); ((TAtom "L180"), ("ferror.c", 39%nat)); ((TAtom "L148"), ("ferror.c", 39%nat)); ((TAtom "L116"), ("ferror.c", 40%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v103"), "__self"); ((TAtom "v104"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "result"); ((TAtom "v117"), "fp"); ((TAtom "v128"), "__libc_single_threaded_internal"); ((TAtom "v132"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v161"), "fp"); ((TAtom "v163"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v17"), "fp"); ((TAtom "v170"), "__oldval"); ((TAtom "v176"), "__oldval"); ((TAtom "v188"), "__futex"); ((TAtom "v189"), "__futex"); ((TAtom "v190"), "__private"); ((TAtom "v191"), "fp"); ((TAtom "v197"), "result"); ((TAtom "v25"), "fp"); ((TAtom "v33"), "__self"); ((TAtom "v38"), "__libc_single_threaded_internal"); ((TAtom "v42"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v59"), "__self"); ((TAtom "v63"), "fp"); ((TAtom "v68"), "__self"); ((TAtom "v73"), "fp"); ((TAtom "v75"), "__futex"); ((TAtom "v80"), "__futex"); ((TAtom "v81"), "__atg3_old"); ((TAtom "v82"), "__atg3_old"); ((TAtom "v9"), "fp"); ((TAtom "v97"), "__futex"); ((TAtom "v98"), "__futex"); ((TAtom "v99"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L168")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_ferror") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_ferror.

Module fn___GI__IO_file_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("filedoalloc.c", 66%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("filedoalloc.c", 71%nat)); ((TAtom "L12"), ("filedoalloc.c", 74%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("filedoalloc.c", 74%nat)); ((TAtom "L13"), ("filedoalloc.c", 74%nat)); ((TAtom "L5"), ("filedoalloc.c", 76%nat)); ((TAtom "L26"), ("filedoalloc.c", 81%nat)); ((TAtom "L42"), ("filedoalloc.c", 81%nat)); ((TAtom "L43"), ("filedoalloc.c", 81%nat)); ((TAtom "L48"), ("filedoalloc.c", 79%nat)); ((TAtom "L49"), ("filedoalloc.c", 79%nat)); ((TAtom "L33"), ("filedoalloc.c", 84%nat)); ((TAtom "L28"), ("filedoalloc.c", 87%nat)); ((TAtom "L65"), ("filedoalloc.c", 87%nat)); ((TAtom "L66"), ("filedoalloc.c", 87%nat)); ((TAtom "L59"), ("filedoalloc.c", 88%nat)); ((TAtom "L7"), ("filedoalloc.c", 69%nat)); ((TAtom "L76"), ("filedoalloc.c", 93%nat)); ((TAtom "L78"), ("filedoalloc.c", 94%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "size"); ((TAtom "pr.2"), "size"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v39"), "__dev_major"); ((TAtom "v40"), "__dev_major"); ((TAtom "v44"), "__dev_major"); ((TAtom "v50"), "fp"); ((TAtom "v56"), "fp"); ((TAtom "v73"), "size"); ((TAtom "v74"), "size"); ((TAtom "v75"), "p"); ((TAtom "v79"), "p"); ((TAtom "v8"), "fp"); ((TAtom "v87"), "fp"); ((TAtom "v88"), "p"); ((TAtom "v89"), "p"); ((TAtom "v90"), "size")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_doallocate") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_doallocate.

Module fn__IO_file_close_maybe_unlink.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 129%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 133%nat)); ((TAtom "L5"), ("fileops.c", 134%nat)); ((TAtom "L7"), ("fileops.c", 136%nat)); ((TAtom "L23"), ("fileops.c", 136%nat)); ((TAtom "L24"), ("fileops.c", 136%nat)); ((TAtom "L16"), ("fileops.c", 138%nat)); ((TAtom "L31"), ("fileops.c", 138%nat)); ((TAtom "L32"), ("fileops.c", 138%nat)); ((TAtom "L17"), ("fileops.c", 139%nat)); ((TAtom "L81"), ("fileops.c", 139%nat)); ((TAtom "L86"), ("fileops.c", 139%nat)); ((TAtom "L92"), ("fileops.c", 139%nat)); ((TAtom "L87"), ("fileops.c", 139%nat)); ((TAtom "L110"), ("fileops.c", 139%nat)); ((TAtom "L118"), ("fileops.c", 139%nat)); ((TAtom "L82"), ("fileops.c", 139%nat)); ((TAtom "L74"), ("fileops.c", 159%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 159%nat)); ((TAtom "L147"), ("fileops.c", 162%nat)); ((TAtom "L155"), ("fileops.c", 162%nat)); ((TAtom "L148"), ("fileops.c", 167%nat)); ((TAtom "L161"), ("fileops.c", 168%nat)); ((TAtom "L163"), ("fileops.c", 159%nat)); ((TAtom "iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.join"), ("fileops.c", 169%nat)); ((TAtom "L191"), ("fileops.c", 169%nat)); ((TAtom "L192"), ("fileops.c", 169%nat)); ((TAtom "L179"), ("fileops.c", 169%nat)); ((TAtom "L18"), ("fileops.c", 132%nat)); ((TAtom "L202"), ("fileops.c", 177%nat)); ((TAtom "iw_3.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_3.join"), ("fileops.c", 177%nat)); ((TAtom "L204"), ("fileops.c", 177%nat)); ((TAtom "L221"), ("fileops.c", 183%nat)); ((TAtom "L228"), ("fileops.c", 184%nat)); ((TAtom "L230"), ("fileops.c", 185%nat)); ((TAtom "L223"), ("fileops.c", 189%nat)); ((TAtom "L277"), ("fileops.c", 194%nat)); ((TAtom "L279"), ("fileops.c", 197%nat)); ((TAtom "L299"), ("fileops.c", 201%nat)); ((TAtom "L300"), ("fileops.c", 201%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "vtable"); ((TAtom "iw_3.v13"), "offset"); ((TAtom "iw_3.v18"), "vtable"); ((TAtom "iw_3.v3"), "vtable"); ((TAtom "iw_3.v4"), "ptr"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v9"), "offset"); ((TAtom "pr.1"), "flush_status"); ((TAtom "pr.2"), "flush_status"); ((TAtom "pr.3"), "flush_status"); ((TAtom "pr.4"), "flush_status"); ((TAtom "pr.5"), "o"); ((TAtom "v0"), "fp"); ((TAtom "v112"), "fp"); ((TAtom "v120"), "fp"); ((TAtom "v124"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v145"), "fp"); ((TAtom "v146"), "o"); ((TAtom "v150"), "o"); ((TAtom "v158"), "__libc_errno"); ((TAtom "v160"), "flush_status"); ((TAtom "v164"), "fp"); ((TAtom "v167"), "o"); ((TAtom "v168"), "fp"); ((TAtom "v171"), "fp"); ((TAtom "v177"), "o"); ((TAtom "v181"), "fp"); ((TAtom "v187"), "fp"); ((TAtom "v188"), "o"); ((TAtom "v19"), "fp"); ((TAtom "v194"), "__libc_errno"); ((TAtom "v199"), "flush_status"); ((TAtom "v2"), "unlink"); ((TAtom "v200"), "fp"); ((TAtom "v205"), "fp"); ((TAtom "v212"), "fp"); ((TAtom "v218"), "fp"); ((TAtom "v220"), "close_status"); ((TAtom "v224"), "fp"); ((TAtom "v231"), "fp"); ((TAtom "v239"), "fp"); ((TAtom "v240"), "fp"); ((TAtom "v241"), "fp"); ((TAtom "v245"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v25"), "fp"); ((TAtom "v252"), "fp"); ((TAtom "v256"), "fp"); ((TAtom "v260"), "fp"); ((TAtom "v264"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v267"), "fp"); ((TAtom "v269"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v273"), "fp"); ((TAtom "v275"), "fp"); ((TAtom "v280"), "unlink"); ((TAtom "v281"), "fp"); ((TAtom "v282"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v291"), "fp"); ((TAtom "v294"), "fp"); ((TAtom "v301"), "close_status"); ((TAtom "v302"), "close_status"); ((TAtom "v303"), "flush_status"); ((TAtom "v34"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v42"), "fp"); ((TAtom "v45"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v73"), "flush_status"); ((TAtom "v77"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v83"), "fp"); ((TAtom "v88"), "fp"); ((TAtom "v94"), "fp"); ((TAtom "v97"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_close_maybe_unlink") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_close_maybe_unlink.

Module fn__IO_new_file_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 211%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 214%nat)); ((TAtom "L4"), ("fileops.c", 216%nat)); ((TAtom "L12"), ("fileops.c", 216%nat)); ((TAtom "L13"), ("fileops.c", 216%nat)); ((TAtom "L14"), ("fileops.c", 217%nat)); ((TAtom "L55"), ("fileops.c", 218%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 218%nat)); ((TAtom "L6"), ("fileops.c", 220%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v20"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v62"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v70"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_finish") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_finish.

Module fn__IO_new_file_setbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 430%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 433%nat)); ((TAtom "L6"), ("fileops.c", 434%nat)); ((TAtom "L8"), ("fileops.c", 436%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v10"), "p"); ((TAtom "v11"), "len"); ((TAtom "v17"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "p"); ((TAtom "v21"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v36"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v4"), "len"); ((TAtom "v41"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_setbuf") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_setbuf.

Module fn__IO_file_setbuf_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 445%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 451%nat)); ((TAtom "L21"), ("fileops.c", 460%nat)); ((TAtom "L23"), ("fileops.c", 464%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v11"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v18"), "p"); ((TAtom "v19"), "len"); ((TAtom "v2"), "p"); ((TAtom "v20"), "result"); ((TAtom "v24"), "result"); ((TAtom "v28"), "fp"); ((TAtom "v32"), "fp"); ((TAtom "v38"), "result"); ((TAtom "v4"), "len"); ((TAtom "v7"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_setbuf_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_setbuf_mmap.

Module fn__IO_new_do_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 472%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 475%nat)); ((TAtom "iw_1.start"), ("fileops.c", 484%nat)); ((TAtom "iw_1.L7"), ("fileops.c", 490%nat)); ((TAtom "iw_1.L8"), ("fileops.c", 491%nat)); ((TAtom "iw_1.L17"), ("fileops.c", 493%nat)); ((TAtom "iw_1.iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.iw_1.join"), ("fileops.c", 493%nat)); ((TAtom "iw_1.L49"), ("fileops.c", 497%nat)); ((TAtom "iw_1.L9"), ("fileops.c", 499%nat)); ((TAtom "iw_1.iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.iw_2.join"), ("fileops.c", 499%nat)); ((TAtom "iw_1.L74"), ("fileops.c", 500%nat)); ((TAtom "iw_1.L75"), ("fileops.c", 500%nat)); ((TAtom "iw_1.L68"), ("fileops.c", 501%nat)); ((TAtom "iw_1.L70"), ("fileops.c", 502%nat)); ((TAtom "iw_1.L122"), ("fileops.c", 504%nat)); ((TAtom "iw_1.L123"), ("fileops.c", 504%nat)); ((TAtom "iw_1.L115"), ("fileops.c", 504%nat)); ((TAtom "iw_1.L116"), ("fileops.c", 504%nat)); ((TAtom "iw_1.L117"), ("fileops.c", 504%nat)); ((TAtom "iw_1.join"), ("fileops.c", 475%nat)); ((TAtom "L12"), ("fileops.c", 475%nat)); ((TAtom "L7"), ("fileops.c", 475%nat)); ((TAtom "L8"), ("fileops.c", 475%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.iw_2.v0"), "vtable"); ((TAtom "iw_1.iw_2.v13"), "offset"); ((TAtom "iw_1.iw_2.v18"), "vtable"); ((TAtom "iw_1.iw_2.v3"), "vtable"); ((TAtom "iw_1.iw_2.v4"), "ptr"); ((TAtom "iw_1.iw_2.v6"), "ptr"); ((TAtom "iw_1.iw_2.v9"), "offset"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v10"), "fp"); ((TAtom "iw_1.v101"), "fp"); ((TAtom "iw_1.v103"), "fp"); ((TAtom "iw_1.v106"), "fp"); ((TAtom "iw_1.v108"), "fp"); ((TAtom "iw_1.v110"), "fp"); ((TAtom "iw_1.v113"), "fp"); ((TAtom "iw_1.v118"), "fp"); ((TAtom "iw_1.v124"), "fp"); ((TAtom "iw_1.v13"), "fp"); ((TAtom "iw_1.v130"), "fp"); ((TAtom "iw_1.v133"), "fp"); ((TAtom "iw_1.v137"), "count"); ((TAtom "iw_1.v2"), "data"); ((TAtom "iw_1.v20"), "fp"); ((TAtom "iw_1.v23"), "fp"); ((TAtom "iw_1.v30"), "fp"); ((TAtom "iw_1.v36"), "fp"); ((TAtom "iw_1.v37"), "fp"); ((TAtom "iw_1.v4"), "to_do"); ((TAtom "iw_1.v40"), "fp"); ((TAtom "iw_1.v46"), "new_pos"); ((TAtom "iw_1.v50"), "new_pos"); ((TAtom "iw_1.v55"), "fp"); ((TAtom "iw_1.v57"), "new_pos"); ((TAtom "iw_1.v58"), "fp"); ((TAtom "iw_1.v64"), "fp"); ((TAtom "iw_1.v65"), "data"); ((TAtom "iw_1.v66"), "to_do"); ((TAtom "iw_1.v67"), "count"); ((TAtom "iw_1.v71"), "fp"); ((TAtom "iw_1.v76"), "count"); ((TAtom "iw_1.v80"), "fp"); ((TAtom "iw_1.v82"), "fp"); ((TAtom "iw_1.v86"), "data"); ((TAtom "iw_1.v87"), "count"); ((TAtom "iw_1.v91"), "fp"); ((TAtom "iw_1.v93"), "fp"); ((TAtom "iw_1.v96"), "fp"); ((TAtom "iw_1.v98"), "fp"); ((TAtom "v0"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v14"), "data"); ((TAtom "v15"), "to_do"); ((TAtom "v17"), "to_do"); ((TAtom "v2"), "data"); ((TAtom "v4"), "to_do"); ((TAtom "v9"), "to_do")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_do_write") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_do_write.

Module fn__IO_new_file_underflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 510%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 516%nat)); ((TAtom "L3"), ("fileops.c", 517%nat)); ((TAtom "L5"), ("fileops.c", 519%nat)); ((TAtom "L11"), ("fileops.c", 521%nat)); ((TAtom "L13"), ("fileops.c", 525%nat)); ((TAtom "L23"), ("fileops.c", 526%nat)); ((TAtom "L25"), ("fileops.c", 528%nat)); ((TAtom "L40"), ("fileops.c", 531%nat)); ((TAtom "L49"), ("fileops.c", 533%nat)); ((TAtom "iw_1.L4"), ("./libioP.h", 1059%nat)); ((TAtom "iw_1.join"), ("fileops.c", 534%nat)); ((TAtom "L51"), ("fileops.c", 536%nat)); ((TAtom "L42"), ("fileops.c", 540%nat)); ((TAtom "L74"), ("fileops.c", 547%nat)); ((TAtom "L87"), ("fileops.c", 547%nat)); ((TAtom "L98"), ("fileops.c", 547%nat)); ((TAtom "L99"), ("fileops.c", 547%nat)); ((TAtom "L92"), ("fileops.c", 547%nat)); ((TAtom "L93"), ("fileops.c", 547%nat)); ((TAtom "L118"), ("fileops.c", 547%nat)); ((TAtom "L142"), ("fileops.c", 547%nat)); ((TAtom "L143"), ("fileops.c", 547%nat)); ((TAtom "L147"), ("fileops.c", 547%nat)); ((TAtom "L136"), ("fileops.c", 547%nat)); ((TAtom "L119"), ("fileops.c", 547%nat)); ((TAtom "L82"), ("fileops.c", 549%nat)); ((TAtom "L168"), ("fileops.c", 551%nat)); ((TAtom "iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.join"), ("fileops.c", 551%nat)); ((TAtom "iw_3.start"), ("./libioP.h", 999%nat)); ((TAtom "iw_3.L5"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L19"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L28"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L29"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L22"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L23"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L45"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L66"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L67"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L78"), ("./libioP.h", 1000%nat)); ((TAtom "iw_3.L46"), ("./libioP.h", 1000%nat)); ((TAtom "L69"), ("fileops.c", 556%nat)); ((TAtom "iw_4.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_4.join"), ("fileops.c", 567%nat)); ((TAtom "L233"), ("fileops.c", 571%nat)); ((TAtom "L238"), ("fileops.c", 572%nat)); ((TAtom "L239"), ("fileops.c", 574%nat)); ((TAtom "L235"), ("fileops.c", 513%nat)); ((TAtom "L254"), ("fileops.c", 582%nat)); ((TAtom "L256"), ("fileops.c", 585%nat)); ((TAtom "L265"), ("fileops.c", 586%nat)); ((TAtom "L267"), ("fileops.c", 587%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "p"); ((TAtom "iw_3.v15"), "fp"); ((TAtom "iw_3.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_3.v3"), "p"); ((TAtom "iw_3.v30"), "fp"); ((TAtom "iw_3.v38"), "fp"); ((TAtom "iw_3.v4"), "fp"); ((TAtom "iw_3.v42"), "fp"); ((TAtom "iw_3.v48"), "fp"); ((TAtom "iw_3.v54"), "fp"); ((TAtom "iw_3.v59"), "fp"); ((TAtom "iw_3.v61"), "__futex"); ((TAtom "iw_3.v64"), "__futex"); ((TAtom "iw_3.v68"), "__oldval"); ((TAtom "iw_3.v74"), "__oldval"); ((TAtom "iw_3.v8"), "fp"); ((TAtom "iw_3.v86"), "__futex"); ((TAtom "iw_3.v87"), "__futex"); ((TAtom "iw_3.v88"), "__private"); ((TAtom "iw_3.v89"), "fp"); ((TAtom "iw_4.v0"), "vtable"); ((TAtom "iw_4.v13"), "offset"); ((TAtom "iw_4.v18"), "vtable"); ((TAtom "iw_4.v3"), "vtable"); ((TAtom "iw_4.v4"), "ptr"); ((TAtom "iw_4.v6"), "ptr"); ((TAtom "iw_4.v9"), "offset"); ((TAtom "pr.1"), "count"); ((TAtom "pr.2"), "count"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "_IO_acquire_lock_file"); ((TAtom "v110"), "_IO_acquire_lock_file"); ((TAtom "v113"), "_IO_acquire_lock_file"); ((TAtom "v117"), "__self"); ((TAtom "v121"), "_IO_acquire_lock_file"); ((TAtom "v126"), "__self"); ((TAtom "v131"), "_IO_acquire_lock_file"); ((TAtom "v133"), "__futex"); ((TAtom "v138"), "__futex"); ((TAtom "v139"), "__atg3_old"); ((TAtom "v14"), "fp"); ((TAtom "v140"), "__atg3_old"); ((TAtom "v155"), "__futex"); ((TAtom "v156"), "__futex"); ((TAtom "v157"), "_IO_acquire_lock_file"); ((TAtom "v161"), "__self"); ((TAtom "v162"), "_IO_acquire_lock_file"); ((TAtom "v17"), "fp"); ((TAtom "v172"), "stdout"); ((TAtom "v180"), "stdout"); ((TAtom "v187"), "stdout"); ((TAtom "v190"), "fp"); ((TAtom "v192"), "fp"); ((TAtom "v194"), "fp"); ((TAtom "v196"), "fp"); ((TAtom "v199"), "fp"); ((TAtom "v201"), "fp"); ((TAtom "v204"), "fp"); ((TAtom "v206"), "fp"); ((TAtom "v208"), "fp"); ((TAtom "v210"), "fp"); ((TAtom "v213"), "fp"); ((TAtom "v219"), "fp"); ((TAtom "v220"), "fp"); ((TAtom "v223"), "fp"); ((TAtom "v226"), "fp"); ((TAtom "v232"), "count"); ((TAtom "v236"), "count"); ((TAtom "v241"), "count"); ((TAtom "v243"), "fp"); ((TAtom "v246"), "fp"); ((TAtom "v249"), "fp"); ((TAtom "v252"), "count"); ((TAtom "v257"), "count"); ((TAtom "v259"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v268"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v277"), "count"); ((TAtom "v279"), "fp"); ((TAtom "v29"), "fp"); ((TAtom "v35"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v59"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v62"), "fp"); ((TAtom "v66"), "fp"); ((TAtom "v70"), "fp"); ((TAtom "v79"), "stdout"); ((TAtom "v83"), "_IO_acquire_lock_file"); ((TAtom "v91"), "__self"); ((TAtom "v96"), "__libc_single_threaded_internal")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_3.L66")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_underflow") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_underflow.

Module fn_glibc_fileops_mmap_remap_check.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 595%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 598%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 600%nat)); ((TAtom "L15"), ("fileops.c", 600%nat)); ((TAtom "L16"), ("fileops.c", 600%nat)); ((TAtom "L23"), ("fileops.c", 600%nat)); ((TAtom "L24"), ("fileops.c", 600%nat)); ((TAtom "L34"), ("fileops.c", 600%nat)); ((TAtom "L31"), ("fileops.c", 600%nat)); ((TAtom "L3"), ("fileops.c", 605%nat)); ((TAtom "L48"), ("fileops.c", 611%nat)); ((TAtom "L49"), ("fileops.c", 616%nat)); ((TAtom "L125"), ("fileops.c", 622%nat)); ((TAtom "L184"), ("fileops.c", 627%nat)); ((TAtom "L186"), ("fileops.c", 639%nat)); ((TAtom "L126"), ("fileops.c", 645%nat)); ((TAtom "L50"), ("fileops.c", 649%nat)); ((TAtom "L248"), ("fileops.c", 650%nat)); ((TAtom "L249"), ("fileops.c", 650%nat)); ((TAtom "L250"), ("fileops.c", 650%nat)); ((TAtom "L280"), ("fileops.c", 662%nat)); ((TAtom "L296"), ("fileops.c", 665%nat)); ((TAtom "L297"), ("fileops.c", 667%nat)); ((TAtom "L282"), ("fileops.c", 670%nat)); ((TAtom "L4"), ("fileops.c", 675%nat)); ((TAtom "L207"), ("fileops.c", 678%nat)); ((TAtom "L360"), ("fileops.c", 681%nat)); ((TAtom "L361"), ("fileops.c", 683%nat)); ((TAtom "L362"), ("fileops.c", 684%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v102"), "pagesize"); ((TAtom "v108"), "pagesize"); ((TAtom "v111"), "pagesize"); ((TAtom "v117"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v130"), "pagesize"); ((TAtom "v133"), "pagesize"); ((TAtom "v137"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v146"), "pagesize"); ((TAtom "v149"), "pagesize"); ((TAtom "v155"), "fp"); ((TAtom "v158"), "fp"); ((TAtom "v161"), "fp"); ((TAtom "v167"), "pagesize"); ((TAtom "v170"), "pagesize"); ((TAtom "v176"), "pagesize"); ((TAtom "v179"), "pagesize"); ((TAtom "v183"), "p"); ((TAtom "v187"), "p"); ((TAtom "v194"), "fp"); ((TAtom "v197"), "fp"); ((TAtom "v200"), "fp"); ((TAtom "v209"), "fp"); ((TAtom "v211"), "p"); ((TAtom "v212"), "fp"); ((TAtom "v214"), "fp"); ((TAtom "v220"), "fp"); ((TAtom "v222"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v231"), "fp"); ((TAtom "v234"), "fp"); ((TAtom "v241"), "fp"); ((TAtom "v243"), "fp"); ((TAtom "v246"), "fp"); ((TAtom "v251"), "fp"); ((TAtom "v254"), "fp"); ((TAtom "v257"), "fp"); ((TAtom "v264"), "fp"); ((TAtom "v267"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v275"), "fp"); ((TAtom "v277"), "fp"); ((TAtom "v283"), "fp"); ((TAtom "v286"), "fp"); ((TAtom "v289"), "fp"); ((TAtom "v299"), "fp"); ((TAtom "v302"), "fp"); ((TAtom "v305"), "fp"); ((TAtom "v312"), "fp"); ((TAtom "v315"), "fp"); ((TAtom "v322"), "fp"); ((TAtom "v325"), "fp"); ((TAtom "v327"), "fp"); ((TAtom "v330"), "fp"); ((TAtom "v337"), "fp"); ((TAtom "v340"), "fp"); ((TAtom "v343"), "fp"); ((TAtom "v350"), "fp"); ((TAtom "v352"), "fp"); ((TAtom "v354"), "fp"); ((TAtom "v356"), "fp"); ((TAtom "v358"), "fp"); ((TAtom "v363"), "fp"); ((TAtom "v367"), "fp"); ((TAtom "v371"), "fp"); ((TAtom "v375"), "fp"); ((TAtom "v47"), "pagesize"); ((TAtom "v53"), "pagesize"); ((TAtom "v56"), "pagesize"); ((TAtom "v6"), "fp"); ((TAtom "v60"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v69"), "pagesize"); ((TAtom "v72"), "pagesize"); ((TAtom "v77"), "fp"); ((TAtom "v82"), "pagesize"); ((TAtom "v85"), "pagesize"); ((TAtom "v90"), "fp"); ((TAtom "v93"), "fp"); ((TAtom "v99"), "pagesize")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "glibc_fileops#mmap_remap_check") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_glibc_fileops_mmap_remap_check.

Module fn__IO_file_underflow_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 691%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 694%nat)); ((TAtom "L2"), ("fileops.c", 695%nat)); ((TAtom "L4"), ("fileops.c", 697%nat)); ((TAtom "L19"), ("fileops.c", 699%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 699%nat)); ((TAtom "L21"), ("fileops.c", 701%nat)); ((TAtom "L35"), ("fileops.c", 702%nat)); ((TAtom "L37"), ("fileops.c", 704%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v22"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v32"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_underflow_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_underflow_mmap.

Module fn_glibc_fileops_decide_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 708%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 716%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 718%nat)); ((TAtom "L15"), ("fileops.c", 718%nat)); ((TAtom "L16"), ("fileops.c", 718%nat)); ((TAtom "L23"), ("fileops.c", 718%nat)); ((TAtom "L24"), ("fileops.c", 718%nat)); ((TAtom "L34"), ("fileops.c", 718%nat)); ((TAtom "L31"), ("fileops.c", 718%nat)); ((TAtom "L45"), ("fileops.c", 718%nat)); ((TAtom "L53"), ("fileops.c", 718%nat)); ((TAtom "L46"), ("fileops.c", 718%nat)); ((TAtom "L3"), ("fileops.c", 728%nat)); ((TAtom "L72"), ("fileops.c", 735%nat)); ((TAtom "L82"), ("fileops.c", 737%nat)); ((TAtom "L83"), ("fileops.c", 742%nat)); ((TAtom "L108"), ("fileops.c", 745%nat)); ((TAtom "L110"), ("fileops.c", 747%nat)); ((TAtom "L139"), ("fileops.c", 751%nat)); ((TAtom "L140"), ("fileops.c", 753%nat)); ((TAtom "L141"), ("fileops.c", 754%nat)); ((TAtom "L5"), ("fileops.c", 763%nat)); ((TAtom "L160"), ("fileops.c", 764%nat)); ((TAtom "L161"), ("fileops.c", 766%nat)); ((TAtom "L162"), ("fileops.c", 767%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v102"), "fp"); ((TAtom "v103"), "p"); ((TAtom "v104"), "p"); ((TAtom "v111"), "fp"); ((TAtom "v117"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v121"), "p"); ((TAtom "v122"), "fp"); ((TAtom "v124"), "p"); ((TAtom "v125"), "fp"); ((TAtom "v129"), "fp"); ((TAtom "v131"), "p"); ((TAtom "v135"), "fp"); ((TAtom "v142"), "fp"); ((TAtom "v146"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v154"), "fp"); ((TAtom "v163"), "fp"); ((TAtom "v167"), "fp"); ((TAtom "v171"), "fp"); ((TAtom "v175"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v71"), "p"); ((TAtom "v75"), "p"); ((TAtom "v85"), "fp"); ((TAtom "v94"), "p"); ((TAtom "v98"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "glibc_fileops#decide_maybe_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_glibc_fileops_decide_maybe_mmap.

Module fn__IO_file_underflow_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 770%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 775%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 776%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v2"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_underflow_maybe_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_underflow_maybe_mmap.

Module fn__IO_new_file_overflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 780%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 783%nat)); ((TAtom "L4"), ("fileops.c", 785%nat)); ((TAtom "L6"), ("fileops.c", 790%nat)); ((TAtom "L23"), ("fileops.c", 790%nat)); ((TAtom "L24"), ("fileops.c", 790%nat)); ((TAtom "L16"), ("fileops.c", 793%nat)); ((TAtom "L33"), ("fileops.c", 795%nat)); ((TAtom "L35"), ("fileops.c", 805%nat)); ((TAtom "L58"), ("fileops.c", 807%nat)); ((TAtom "L81"), ("fileops.c", 809%nat)); ((TAtom "L82"), ("fileops.c", 809%nat)); ((TAtom "L60"), ("fileops.c", 814%nat)); ((TAtom "L111"), ("fileops.c", 815%nat)); ((TAtom "L113"), ("fileops.c", 816%nat)); ((TAtom "L162"), ("fileops.c", 822%nat)); ((TAtom "L163"), ("fileops.c", 822%nat)); ((TAtom "L155"), ("fileops.c", 823%nat)); ((TAtom "L18"), ("fileops.c", 825%nat)); ((TAtom "L175"), ("fileops.c", 826%nat)); ((TAtom "L177"), ("fileops.c", 828%nat)); ((TAtom "L196"), ("fileops.c", 829%nat)); ((TAtom "L211"), ("fileops.c", 829%nat)); ((TAtom "L212"), ("fileops.c", 829%nat)); ((TAtom "L213"), ("fileops.c", 829%nat)); ((TAtom "L208"), ("fileops.c", 830%nat)); ((TAtom "L198"), ("fileops.c", 831%nat)); ((TAtom "L270"), ("fileops.c", 832%nat)); ((TAtom "L275"), ("fileops.c", 832%nat)); ((TAtom "L271"), ("fileops.c", 832%nat)); ((TAtom "L264"), ("fileops.c", 834%nat)); ((TAtom "L283"), ("fileops.c", 836%nat)); ((TAtom "L266"), ("fileops.c", 837%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v10"), "f"); ((TAtom "v106"), "f"); ((TAtom "v108"), "f"); ((TAtom "v114"), "f"); ((TAtom "v117"), "f"); ((TAtom "v123"), "f"); ((TAtom "v125"), "f"); ((TAtom "v127"), "f"); ((TAtom "v130"), "f"); ((TAtom "v132"), "f"); ((TAtom "v135"), "f"); ((TAtom "v137"), "f"); ((TAtom "v140"), "f"); ((TAtom "v142"), "f"); ((TAtom "v145"), "f"); ((TAtom "v147"), "f"); ((TAtom "v149"), "f"); ((TAtom "v152"), "f"); ((TAtom "v158"), "f"); ((TAtom "v164"), "f"); ((TAtom "v170"), "f"); ((TAtom "v172"), "f"); ((TAtom "v178"), "ch"); ((TAtom "v181"), "f"); ((TAtom "v182"), "f"); ((TAtom "v185"), "f"); ((TAtom "v188"), "f"); ((TAtom "v19"), "f"); ((TAtom "v199"), "f"); ((TAtom "v2"), "ch"); ((TAtom "v202"), "f"); ((TAtom "v214"), "f"); ((TAtom "v218"), "f"); ((TAtom "v219"), "f"); ((TAtom "v222"), "f"); ((TAtom "v225"), "f"); ((TAtom "v232"), "f"); ((TAtom "v233"), "f"); ((TAtom "v238"), "f"); ((TAtom "v243"), "f"); ((TAtom "v25"), "f"); ((TAtom "v258"), "f"); ((TAtom "v262"), "ch"); ((TAtom "v267"), "f"); ((TAtom "v272"), "f"); ((TAtom "v277"), "ch"); ((TAtom "v286"), "f"); ((TAtom "v287"), "f"); ((TAtom "v290"), "f"); ((TAtom "v293"), "f"); ((TAtom "v304"), "ch"); ((TAtom "v36"), "f"); ((TAtom "v42"), "f"); ((TAtom "v43"), "f"); ((TAtom "v45"), "f"); ((TAtom "v48"), "f"); ((TAtom "v50"), "f"); ((TAtom "v53"), "f"); ((TAtom "v55"), "f"); ((TAtom "v61"), "f"); ((TAtom "v67"), "f"); ((TAtom "v7"), "f"); ((TAtom "v70"), "f"); ((TAtom "v75"), "nbackup"); ((TAtom "v76"), "f"); ((TAtom "v77"), "f"); ((TAtom "v83"), "nbackup"); ((TAtom "v84"), "f"); ((TAtom "v87"), "f"); ((TAtom "v94"), "nbackup"); ((TAtom "v95"), "f"); ((TAtom "v98"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_overflow") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_overflow.

Module fn__IO_new_file_sync.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 841%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 848%nat)); ((TAtom "L4"), ("fileops.c", 849%nat)); ((TAtom "L19"), ("fileops.c", 849%nat)); ((TAtom "L20"), ("fileops.c", 849%nat)); ((TAtom "L21"), ("fileops.c", 849%nat)); ((TAtom "L16"), ("fileops.c", 849%nat)); ((TAtom "L6"), ("fileops.c", 850%nat)); ((TAtom "L73"), ("fileops.c", 853%nat)); ((TAtom "L75"), ("fileops.c", 844%nat)); ((TAtom "L91"), ("fileops.c", 858%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 858%nat)); ((TAtom "L106"), ("fileops.c", 860%nat)); ((TAtom "L107"), ("fileops.c", 861%nat)); ((TAtom "L119"), ("fileops.c", 861%nat)); ((TAtom "L93"), ("fileops.c", 845%nat)); ((TAtom "L125"), ("fileops.c", 867%nat)); ((TAtom "L127"), ("fileops.c", 870%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "delta"); ((TAtom "pr.2"), "retval"); ((TAtom "pr.3"), "retval"); ((TAtom "pr.4"), "retval"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v103"), "fp"); ((TAtom "v104"), "delta"); ((TAtom "v105"), "new_pos"); ((TAtom "v109"), "new_pos"); ((TAtom "v113"), "fp"); ((TAtom "v115"), "fp"); ((TAtom "v122"), "__libc_errno"); ((TAtom "v124"), "retval"); ((TAtom "v128"), "retval"); ((TAtom "v131"), "fp"); ((TAtom "v135"), "retval"); ((TAtom "v22"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v40"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v46"), "fp"); ((TAtom "v51"), "fp"); ((TAtom "v64"), "fp"); ((TAtom "v67"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v72"), "delta"); ((TAtom "v76"), "fp"); ((TAtom "v79"), "fp"); ((TAtom "v80"), "delta"); ((TAtom "v81"), "fp"); ((TAtom "v84"), "fp"); ((TAtom "v90"), "delta"); ((TAtom "v94"), "delta"); ((TAtom "v97"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_sync") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_sync.

Module fn__IO_file_sync_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 874%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 877%nat)); ((TAtom "L16"), ("fileops.c", 880%nat)); ((TAtom "L28"), ("fileops.c", 882%nat)); ((TAtom "L30"), ("fileops.c", 877%nat)); ((TAtom "L46"), ("fileops.c", 887%nat)); ((TAtom "L18"), ("fileops.c", 877%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "o"); ((TAtom "pr.2"), "o"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "o"); ((TAtom "v19"), "fp"); ((TAtom "v22"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v35"), "o"); ((TAtom "v36"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v45"), "o"); ((TAtom "v49"), "fp"); ((TAtom "v52"), "o"); ((TAtom "v54"), "o"); ((TAtom "v56"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v61"), "fp"); ((TAtom "v63"), "o"); ((TAtom "v64"), "fp"); ((TAtom "v66"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_sync_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_sync_mmap.

Module fn__IO_new_file_seekoff.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 968%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1034%nat)); ((TAtom "iw_1.start"), ("fileops.c", 906%nat)); ((TAtom "iw_1.L4"), ("fileops.c", 908%nat)); ((TAtom "iw_1.L34"), ("fileops.c", 915%nat)); ((TAtom "iw_1.L35"), ("fileops.c", 915%nat)); ((TAtom "iw_1.L30"), ("fileops.c", 917%nat)); ((TAtom "iw_1.iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.iw_1.join"), ("fileops.c", 917%nat)); ((TAtom "iw_1.L48"), ("fileops.c", 921%nat)); ((TAtom "iw_1.L32"), ("fileops.c", 925%nat)); ((TAtom "iw_1.L60"), ("fileops.c", 926%nat)); ((TAtom "iw_1.L61"), ("fileops.c", 932%nat)); ((TAtom "iw_1.L76"), ("fileops.c", 933%nat)); ((TAtom "iw_1.L77"), ("fileops.c", 936%nat)); ((TAtom "iw_1.L6"), ("fileops.c", 902%nat)); ((TAtom "iw_1.L102"), ("fileops.c", 940%nat)); ((TAtom "iw_1.L103"), ("fileops.c", 942%nat)); ((TAtom "iw_1.iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.iw_2.join"), ("fileops.c", 942%nat)); ((TAtom "iw_1.L104"), ("fileops.c", 902%nat)); ((TAtom "iw_1.L124"), ("fileops.c", 947%nat)); ((TAtom "iw_1.L136"), ("fileops.c", 947%nat)); ((TAtom "iw_1.L137"), ("fileops.c", 947%nat)); ((TAtom "iw_1.L131"), ("fileops.c", 953%nat)); ((TAtom "iw_1.L133"), ("fileops.c", 957%nat)); ((TAtom "iw_1.L149"), ("fileops.c", 961%nat)); ((TAtom "iw_1.join"), ("fileops.c", 979%nat)); ((TAtom "L14"), ("fileops.c", 983%nat)); ((TAtom "L30"), ("fileops.c", 983%nat)); ((TAtom "L31"), ("fileops.c", 983%nat)); ((TAtom "L53"), ("fileops.c", 986%nat)); ((TAtom "L54"), ("fileops.c", 986%nat)); ((TAtom "L65"), ("fileops.c", 996%nat)); ((TAtom "L66"), ("fileops.c", 996%nat)); ((TAtom "L61"), ("fileops.c", 997%nat)); ((TAtom "L63"), ("fileops.c", 999%nat)); ((TAtom "L74"), ("fileops.c", 1002%nat)); ((TAtom "L83"), ("fileops.c", 1004%nat)); ((TAtom "iw_2.L4"), ("./libioP.h", 1059%nat)); ((TAtom "iw_2.join"), ("fileops.c", 1005%nat)); ((TAtom "L85"), ("fileops.c", 1007%nat)); ((TAtom "L131"), ("fileops.c", 1016%nat)); ((TAtom "L145"), ("fileops.c", 1021%nat)); ((TAtom "L159"), ("fileops.c", 1024%nat)); ((TAtom "L169"), ("fileops.c", 1035%nat)); ((TAtom "iw_3.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_3.join"), ("fileops.c", 1035%nat)); ((TAtom "L183"), ("fileops.c", 1035%nat)); ((TAtom "L184"), ("fileops.c", 1035%nat)); ((TAtom "L171"), ("fileops.c", 1037%nat)); ((TAtom "L129"), ("fileops.c", 1012%nat)); ((TAtom "L196"), ("fileops.c", 1012%nat)); ((TAtom "L198"), ("fileops.c", 1012%nat)); ((TAtom "L130"), ("fileops.c", 968%nat)); ((TAtom "L211"), ("fileops.c", 1050%nat)); ((TAtom "L212"), ("fileops.c", 1050%nat)); ((TAtom "L221"), ("fileops.c", 1050%nat)); ((TAtom "L222"), ("fileops.c", 1050%nat)); ((TAtom "L202"), ("fileops.c", 1053%nat)); ((TAtom "L249"), ("fileops.c", 1055%nat)); ((TAtom "L250"), ("fileops.c", 1055%nat)); ((TAtom "L243"), ("fileops.c", 1057%nat)); ((TAtom "L204"), ("fileops.c", 1067%nat)); ((TAtom "L300"), ("fileops.c", 1071%nat)); ((TAtom "L322"), ("fileops.c", 1073%nat)); ((TAtom "L323"), ("fileops.c", 972%nat)); ((TAtom "iw_4.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_4.join"), ("fileops.c", 1078%nat)); ((TAtom "L345"), ("fileops.c", 1080%nat)); ((TAtom "L347"), ("fileops.c", 1081%nat)); ((TAtom "L354"), ("fileops.c", 1085%nat)); ((TAtom "iw_5.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_5.join"), ("fileops.c", 1085%nat)); ((TAtom "L369"), ("fileops.c", 1085%nat)); ((TAtom "L370"), ("fileops.c", 1085%nat)); ((TAtom "L384"), ("fileops.c", 1091%nat)); ((TAtom "L391"), ("fileops.c", 1091%nat)); ((TAtom "L355"), ("fileops.c", 973%nat)); ((TAtom "L152"), ("fileops.c", 968%nat)); ((TAtom "iw_6.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_6.join"), ("fileops.c", 1105%nat)); ((TAtom "L458"), ("fileops.c", 1108%nat)); ((TAtom "L460"), ("fileops.c", 1113%nat)); ((TAtom "L503"), ("fileops.c", 1121%nat)); ((TAtom "iw_7.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_7.join"), ("fileops.c", 1121%nat)); ((TAtom "L505"), ("fileops.c", 1123%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.iw_2.v0"), "vtable"); ((TAtom "iw_1.iw_2.v13"), "offset"); ((TAtom "iw_1.iw_2.v18"), "vtable"); ((TAtom "iw_1.iw_2.v3"), "vtable"); ((TAtom "iw_1.iw_2.v4"), "ptr"); ((TAtom "iw_1.iw_2.v6"), "ptr"); ((TAtom "iw_1.iw_2.v9"), "offset"); ((TAtom "iw_1.pr.1"), "result"); ((TAtom "iw_1.pr.2"), "offset"); ((TAtom "iw_1.pr.3"), "offset"); ((TAtom "iw_1.pr.4"), "offset"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v101"), "offset"); ((TAtom "iw_1.v105"), "fp"); ((TAtom "iw_1.v111"), "fp"); ((TAtom "iw_1.v113"), "result"); ((TAtom "iw_1.v114"), "fp"); ((TAtom "iw_1.v120"), "fp"); ((TAtom "iw_1.v121"), "result"); ((TAtom "iw_1.v125"), "result"); ((TAtom "iw_1.v129"), "result"); ((TAtom "iw_1.v134"), "result"); ((TAtom "iw_1.v138"), "offset"); ((TAtom "iw_1.v14"), "fp"); ((TAtom "iw_1.v146"), "result"); ((TAtom "iw_1.v147"), "offset"); ((TAtom "iw_1.v148"), "result"); ((TAtom "iw_1.v152"), "result"); ((TAtom "iw_1.v158"), "result"); ((TAtom "iw_1.v17"), "fp"); ((TAtom "iw_1.v23"), "unflushed_writes"); ((TAtom "iw_1.v25"), "fp"); ((TAtom "iw_1.v29"), "append_mode"); ((TAtom "iw_1.v33"), "unflushed_writes"); ((TAtom "iw_1.v36"), "append_mode"); ((TAtom "iw_1.v39"), "fp"); ((TAtom "iw_1.v45"), "fp"); ((TAtom "iw_1.v46"), "result"); ((TAtom "iw_1.v50"), "result"); ((TAtom "iw_1.v57"), "fp"); ((TAtom "iw_1.v59"), "result"); ((TAtom "iw_1.v63"), "unflushed_writes"); ((TAtom "iw_1.v65"), "offset"); ((TAtom "iw_1.v66"), "fp"); ((TAtom "iw_1.v69"), "fp"); ((TAtom "iw_1.v7"), "fp"); ((TAtom "iw_1.v75"), "offset"); ((TAtom "iw_1.v79"), "append_mode"); ((TAtom "iw_1.v80"), "offset"); ((TAtom "iw_1.v81"), "fp"); ((TAtom "iw_1.v84"), "fp"); ((TAtom "iw_1.v90"), "offset"); ((TAtom "iw_1.v91"), "offset"); ((TAtom "iw_1.v92"), "fp"); ((TAtom "iw_1.v95"), "fp"); ((TAtom "iw_2.v0"), "fp"); ((TAtom "iw_2.v13"), "ptr"); ((TAtom "iw_2.v2"), "ptr"); ((TAtom "iw_2.v7"), "ptr"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_3.v0"), "vtable"); ((TAtom "iw_3.v13"), "offset"); ((TAtom "iw_3.v18"), "vtable"); ((TAtom "iw_3.v3"), "vtable"); ((TAtom "iw_3.v4"), "ptr"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v9"), "offset"); ((TAtom "iw_4.v0"), "vtable"); ((TAtom "iw_4.v13"), "offset"); ((TAtom "iw_4.v18"), "vtable"); ((TAtom "iw_4.v3"), "vtable"); ((TAtom "iw_4.v4"), "ptr"); ((TAtom "iw_4.v6"), "ptr"); ((TAtom "iw_4.v9"), "offset"); ((TAtom "iw_5.v0"), "vtable"); ((TAtom "iw_5.v13"), "offset"); ((TAtom "iw_5.v18"), "vtable"); ((TAtom "iw_5.v3"), "vtable"); ((TAtom "iw_5.v4"), "ptr"); ((TAtom "iw_5.v6"), "ptr"); ((TAtom "iw_5.v9"), "offset"); ((TAtom "iw_6.v0"), "vtable"); ((TAtom "iw_6.v13"), "offset"); ((TAtom "iw_6.v18"), "vtable"); ((TAtom "iw_6.v3"), "vtable"); ((TAtom "iw_6.v4"), "ptr"); ((TAtom "iw_6.v6"), "ptr"); ((TAtom "iw_6.v9"), "offset"); ((TAtom "iw_7.v0"), "vtable"); ((TAtom "iw_7.v13"), "offset"); ((TAtom "iw_7.v18"), "vtable"); ((TAtom "iw_7.v3"), "vtable"); ((TAtom "iw_7.v4"), "ptr"); ((TAtom "iw_7.v6"), "ptr"); ((TAtom "iw_7.v9"), "offset"); ((TAtom "pr.1"), "offset"); ((TAtom "pr.2"), "offset"); ((TAtom "pr.3"), "dir"); ((TAtom "pr.4"), "dir"); ((TAtom "pr.5"), "delta"); ((TAtom "pr.6"), "new_offset"); ((TAtom "pr.7"), "count"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "fp"); ((TAtom "v101"), "fp"); ((TAtom "v103"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v108"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "fp"); ((TAtom "v115"), "fp"); ((TAtom "v118"), "fp"); ((TAtom "v120"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v125"), "fp"); ((TAtom "v128"), "dir"); ((TAtom "v132"), "offset"); ((TAtom "v133"), "fp"); ((TAtom "v136"), "fp"); ((TAtom "v142"), "offset"); ((TAtom "v146"), "fp"); ((TAtom "v15"), "mode"); ((TAtom "v154"), "offset"); ((TAtom "v155"), "fp"); ((TAtom "v158"), "offset"); ((TAtom "v162"), "offset"); ((TAtom "v17"), "fp"); ((TAtom "v174"), "fp"); ((TAtom "v180"), "fp"); ((TAtom "v191"), "offset"); ((TAtom "v194"), "offset"); ((TAtom "v2"), "offset"); ((TAtom "v201"), "fp"); ((TAtom "v205"), "fp"); ((TAtom "v21"), "fp"); ((TAtom "v213"), "fp"); ((TAtom "v223"), "fp"); ((TAtom "v230"), "fp"); ((TAtom "v233"), "fp"); ((TAtom "v236"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v242"), "start_offset"); ((TAtom "v246"), "offset"); ((TAtom "v247"), "start_offset"); ((TAtom "v251"), "offset"); ((TAtom "v252"), "fp"); ((TAtom "v258"), "fp"); ((TAtom "v260"), "fp"); ((TAtom "v263"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v268"), "offset"); ((TAtom "v269"), "start_offset"); ((TAtom "v272"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v277"), "fp"); ((TAtom "v279"), "fp"); ((TAtom "v281"), "fp"); ((TAtom "v284"), "fp"); ((TAtom "v286"), "fp"); ((TAtom "v289"), "fp"); ((TAtom "v290"), "fp"); ((TAtom "v301"), "fp"); ((TAtom "v305"), "offset"); ((TAtom "v306"), "fp"); ((TAtom "v309"), "fp"); ((TAtom "v317"), "new_offset"); ((TAtom "v318"), "offset"); ((TAtom "v319"), "new_offset"); ((TAtom "v32"), "fp"); ((TAtom "v320"), "delta"); ((TAtom "v324"), "delta"); ((TAtom "v325"), "fp"); ((TAtom "v328"), "fp"); ((TAtom "v335"), "offset"); ((TAtom "v336"), "fp"); ((TAtom "v342"), "fp"); ((TAtom "v343"), "new_offset"); ((TAtom "v344"), "result"); ((TAtom "v348"), "result"); ((TAtom "v35"), "fp"); ((TAtom "v356"), "delta"); ((TAtom "v358"), "fp"); ((TAtom "v364"), "fp"); ((TAtom "v365"), "fp"); ((TAtom "v371"), "must_be_exact"); ((TAtom "v372"), "delta"); ((TAtom "v373"), "fp"); ((TAtom "v376"), "fp"); ((TAtom "v383"), "count"); ((TAtom "v387"), "count"); ((TAtom "v388"), "delta"); ((TAtom "v393"), "count"); ((TAtom "v397"), "delta"); ((TAtom "v398"), "delta"); ((TAtom "v399"), "count"); ((TAtom "v4"), "dir"); ((TAtom "v401"), "offset"); ((TAtom "v403"), "fp"); ((TAtom "v405"), "fp"); ((TAtom "v408"), "fp"); ((TAtom "v410"), "fp"); ((TAtom "v413"), "delta"); ((TAtom "v415"), "fp"); ((TAtom "v417"), "fp"); ((TAtom "v42"), "must_be_exact"); ((TAtom "v420"), "count"); ((TAtom "v422"), "fp"); ((TAtom "v424"), "fp"); ((TAtom "v426"), "fp"); ((TAtom "v429"), "fp"); ((TAtom "v431"), "fp"); ((TAtom "v434"), "fp"); ((TAtom "v436"), "result"); ((TAtom "v437"), "count"); ((TAtom "v439"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v440"), "fp"); ((TAtom "v446"), "offset"); ((TAtom "v447"), "fp"); ((TAtom "v448"), "fp"); ((TAtom "v454"), "fp"); ((TAtom "v455"), "offset"); ((TAtom "v456"), "dir"); ((TAtom "v457"), "result"); ((TAtom "v461"), "result"); ((TAtom "v465"), "fp"); ((TAtom "v466"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v472"), "fp"); ((TAtom "v474"), "result"); ((TAtom "v475"), "fp"); ((TAtom "v477"), "fp"); ((TAtom "v480"), "fp"); ((TAtom "v482"), "fp"); ((TAtom "v485"), "fp"); ((TAtom "v487"), "fp"); ((TAtom "v490"), "fp"); ((TAtom "v492"), "fp"); ((TAtom "v494"), "fp"); ((TAtom "v497"), "fp"); ((TAtom "v499"), "fp"); ((TAtom "v502"), "result"); ((TAtom "v506"), "fp"); ((TAtom "v510"), "fp"); ((TAtom "v516"), "fp"); ((TAtom "v517"), "fp"); ((TAtom "v521"), "offset"); ((TAtom "v55"), "fp"); ((TAtom "v6"), "mode"); ((TAtom "v60"), "was_writing"); ((TAtom "v64"), "was_writing"); ((TAtom "v67"), "fp"); ((TAtom "v77"), "fp"); ((TAtom "v86"), "fp"); ((TAtom "v92"), "fp"); ((TAtom "v93"), "fp"); ((TAtom "v96"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_seekoff") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_seekoff.

Module fn__IO_file_seekoff_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1127%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1136%nat)); ((TAtom "L9"), ("fileops.c", 1137%nat)); ((TAtom "L11"), ("fileops.c", 1139%nat)); ((TAtom "L28"), ("fileops.c", 1141%nat)); ((TAtom "L34"), ("fileops.c", 1142%nat)); ((TAtom "L36"), ("fileops.c", 1127%nat)); ((TAtom "L30"), ("fileops.c", 1127%nat)); ((TAtom "L54"), ("fileops.c", 1150%nat)); ((TAtom "L71"), ("fileops.c", 1155%nat)); ((TAtom "L85"), ("fileops.c", 1146%nat)); ((TAtom "L87"), ("fileops.c", 1146%nat)); ((TAtom "L53"), ("fileops.c", 1127%nat)); ((TAtom "L90"), ("fileops.c", 1163%nat)); ((TAtom "L92"), ("fileops.c", 1167%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 1167%nat)); ((TAtom "L108"), ("fileops.c", 1169%nat)); ((TAtom "L110"), ("fileops.c", 1171%nat)); ((TAtom "L116"), ("fileops.c", 1175%nat)); ((TAtom "L117"), ("fileops.c", 1179%nat)); ((TAtom "L118"), ("fileops.c", 1182%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "offset"); ((TAtom "pr.2"), "offset"); ((TAtom "pr.3"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v106"), "offset"); ((TAtom "v107"), "result"); ((TAtom "v111"), "result"); ((TAtom "v119"), "offset"); ((TAtom "v12"), "mode"); ((TAtom "v120"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v130"), "fp"); ((TAtom "v132"), "fp"); ((TAtom "v135"), "fp"); ((TAtom "v137"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v142"), "fp"); ((TAtom "v145"), "fp"); ((TAtom "v147"), "fp"); ((TAtom "v150"), "fp"); ((TAtom "v152"), "fp"); ((TAtom "v155"), "offset"); ((TAtom "v157"), "fp"); ((TAtom "v159"), "fp"); ((TAtom "v162"), "offset"); ((TAtom "v164"), "fp"); ((TAtom "v166"), "result"); ((TAtom "v167"), "fp"); ((TAtom "v168"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v174"), "offset"); ((TAtom "v2"), "offset"); ((TAtom "v20"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v37"), "dir"); ((TAtom "v39"), "offset"); ((TAtom "v4"), "dir"); ((TAtom "v40"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v49"), "offset"); ((TAtom "v50"), "fp"); ((TAtom "v51"), "dir"); ((TAtom "v55"), "offset"); ((TAtom "v56"), "fp"); ((TAtom "v59"), "fp"); ((TAtom "v6"), "mode"); ((TAtom "v62"), "fp"); ((TAtom "v69"), "offset"); ((TAtom "v72"), "offset"); ((TAtom "v73"), "fp"); ((TAtom "v76"), "fp"); ((TAtom "v82"), "offset"); ((TAtom "v93"), "offset"); ((TAtom "v99"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_seekoff_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_seekoff_mmap.

Module fn__IO_file_seekoff_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1189%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1197%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 1197%nat)); ((TAtom "L19"), ("fileops.c", 1199%nat)); ((TAtom "L21"), ("fileops.c", 1201%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v16"), "offset"); ((TAtom "v17"), "dir"); ((TAtom "v18"), "result"); ((TAtom "v2"), "offset"); ((TAtom "v22"), "result"); ((TAtom "v27"), "fp"); ((TAtom "v29"), "result"); ((TAtom "v30"), "result"); ((TAtom "v4"), "dir"); ((TAtom "v6"), "mode"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_seekoff_maybe_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_seekoff_maybe_mmap.

Module fn___GI__IO_file_read.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1205%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1208%nat)); ((TAtom "L6"), ("fileops.c", 1208%nat)); ((TAtom "L7"), ("fileops.c", 1208%nat)); ((TAtom "L8"), ("fileops.c", 1208%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v2"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v21"), "size"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "buf"); ((TAtom "v27"), "size"); ((TAtom "v4"), "size"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_read") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_read.

Module fn___GI__IO_file_seek.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1214%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1217%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v10"), "dir"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "dir"); ((TAtom "v6"), "fp"); ((TAtom "v9"), "offset")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_seek") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_seek.

Module fn___GI__IO_file_stat.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1221%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1224%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "st"); ((TAtom "v4"), "fp"); ((TAtom "v7"), "st")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_stat") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_stat.

Module fn__IO_file_close_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1228%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1232%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_close_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_close_mmap.

Module fn___GI__IO_file_close.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1239%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1244%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_close") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_close.

Module fn__IO_new_file_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1248%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1252%nat)); ((TAtom "L8"), ("fileops.c", 1251%nat)); ((TAtom "L9"), ("fileops.c", 1254%nat)); ((TAtom "L14"), ("fileops.c", 1254%nat)); ((TAtom "L15"), ("fileops.c", 1254%nat)); ((TAtom "L16"), ("fileops.c", 1254%nat)); ((TAtom "L38"), ("fileops.c", 1260%nat)); ((TAtom "L40"), ("fileops.c", 1263%nat)); ((TAtom "L10"), ("fileops.c", 1267%nat)); ((TAtom "L61"), ("fileops.c", 1269%nat)); ((TAtom "L63"), ("fileops.c", 1270%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "data"); ((TAtom "pr.2"), "to_do"); ((TAtom "v0"), "f"); ((TAtom "v11"), "to_do"); ((TAtom "v17"), "f"); ((TAtom "v2"), "data"); ((TAtom "v25"), "f"); ((TAtom "v28"), "data"); ((TAtom "v29"), "to_do"); ((TAtom "v31"), "f"); ((TAtom "v34"), "data"); ((TAtom "v35"), "to_do"); ((TAtom "v37"), "count"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v43"), "f"); ((TAtom "v47"), "f"); ((TAtom "v50"), "count"); ((TAtom "v52"), "to_do"); ((TAtom "v53"), "count"); ((TAtom "v54"), "to_do"); ((TAtom "v55"), "data"); ((TAtom "v56"), "count"); ((TAtom "v57"), "data"); ((TAtom "v58"), "n"); ((TAtom "v59"), "to_do"); ((TAtom "v60"), "n"); ((TAtom "v64"), "f"); ((TAtom "v68"), "f"); ((TAtom "v7"), "n"); ((TAtom "v71"), "n"); ((TAtom "v73"), "n")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L8")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_write") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_write.

Module fn__IO_new_file_xsputn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1273%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1281%nat)); ((TAtom "L12"), ("fileops.c", 1282%nat)); ((TAtom "L14"), ("fileops.c", 1288%nat)); ((TAtom "L24"), ("fileops.c", 1288%nat)); ((TAtom "L25"), ("fileops.c", 1288%nat)); ((TAtom "L18"), ("fileops.c", 1290%nat)); ((TAtom "L40"), ("fileops.c", 1294%nat)); ((TAtom "L50"), ("fileops.c", 1293%nat)); ((TAtom "L51"), ("fileops.c", 1296%nat)); ((TAtom "L59"), ("fileops.c", 1298%nat)); ((TAtom "L19"), ("fileops.c", 1305%nat)); ((TAtom "L73"), ("fileops.c", 1306%nat)); ((TAtom "L20"), ("fileops.c", 1279%nat)); ((TAtom "L94"), ("fileops.c", 1311%nat)); ((TAtom "L100"), ("fileops.c", 1311%nat)); ((TAtom "L101"), ("fileops.c", 1279%nat)); ((TAtom "L96"), ("fileops.c", 1277%nat)); ((TAtom "L120"), ("fileops.c", 1321%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 1321%nat)); ((TAtom "L130"), ("fileops.c", 1324%nat)); ((TAtom "L145"), ("fileops.c", 1324%nat)); ((TAtom "L146"), ("fileops.c", 1324%nat)); ((TAtom "L132"), ("fileops.c", 1327%nat)); ((TAtom "L166"), ("fileops.c", 1328%nat)); ((TAtom "L168"), ("fileops.c", 1328%nat)); ((TAtom "iw_2.start"), ("fileops.c", 484%nat)); ((TAtom "iw_2.L7"), ("fileops.c", 490%nat)); ((TAtom "iw_2.L8"), ("fileops.c", 491%nat)); ((TAtom "iw_2.L17"), ("fileops.c", 493%nat)); ((TAtom "iw_2.iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.iw_1.join"), ("fileops.c", 493%nat)); ((TAtom "iw_2.L49"), ("fileops.c", 497%nat)); ((TAtom "iw_2.L9"), ("fileops.c", 499%nat)); ((TAtom "iw_2.iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.iw_2.join"), ("fileops.c", 499%nat)); ((TAtom "iw_2.L74"), ("fileops.c", 500%nat)); ((TAtom "iw_2.L75"), ("fileops.c", 500%nat)); ((TAtom "iw_2.L68"), ("fileops.c", 501%nat)); ((TAtom "iw_2.L70"), ("fileops.c", 502%nat)); ((TAtom "iw_2.L122"), ("fileops.c", 504%nat)); ((TAtom "iw_2.L123"), ("fileops.c", 504%nat)); ((TAtom "iw_2.L115"), ("fileops.c", 504%nat)); ((TAtom "iw_2.L116"), ("fileops.c", 504%nat)); ((TAtom "iw_2.L117"), ("fileops.c", 504%nat)); ((TAtom "iw_2.join"), ("fileops.c", 1333%nat)); ((TAtom "L188"), ("fileops.c", 1335%nat)); ((TAtom "L178"), ("fileops.c", 1277%nat)); ((TAtom "L198"), ("fileops.c", 1342%nat)); ((TAtom "L122"), ("fileops.c", 1277%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.iw_1.v0"), "vtable"); ((TAtom "iw_2.iw_1.v13"), "offset"); ((TAtom "iw_2.iw_1.v18"), "vtable"); ((TAtom "iw_2.iw_1.v3"), "vtable"); ((TAtom "iw_2.iw_1.v4"), "ptr"); ((TAtom "iw_2.iw_1.v6"), "ptr"); ((TAtom "iw_2.iw_1.v9"), "offset"); ((TAtom "iw_2.iw_2.v0"), "vtable"); ((TAtom "iw_2.iw_2.v13"), "offset"); ((TAtom "iw_2.iw_2.v18"), "vtable"); ((TAtom "iw_2.iw_2.v3"), "vtable"); ((TAtom "iw_2.iw_2.v4"), "ptr"); ((TAtom "iw_2.iw_2.v6"), "ptr"); ((TAtom "iw_2.iw_2.v9"), "offset"); ((TAtom "iw_2.v0"), "fp"); ((TAtom "iw_2.v10"), "fp"); ((TAtom "iw_2.v101"), "fp"); ((TAtom "iw_2.v103"), "fp"); ((TAtom "iw_2.v106"), "fp"); ((TAtom "iw_2.v108"), "fp"); ((TAtom "iw_2.v110"), "fp"); ((TAtom "iw_2.v113"), "fp"); ((TAtom "iw_2.v118"), "fp"); ((TAtom "iw_2.v124"), "fp"); ((TAtom "iw_2.v13"), "fp"); ((TAtom "iw_2.v130"), "fp"); ((TAtom "iw_2.v133"), "fp"); ((TAtom "iw_2.v137"), "count"); ((TAtom "iw_2.v2"), "data"); ((TAtom "iw_2.v20"), "fp"); ((TAtom "iw_2.v23"), "fp"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v36"), "fp"); ((TAtom "iw_2.v37"), "fp"); ((TAtom "iw_2.v4"), "to_do"); ((TAtom "iw_2.v40"), "fp"); ((TAtom "iw_2.v46"), "new_pos"); ((TAtom "iw_2.v50"), "new_pos"); ((TAtom "iw_2.v55"), "fp"); ((TAtom "iw_2.v57"), "new_pos"); ((TAtom "iw_2.v58"), "fp"); ((TAtom "iw_2.v64"), "fp"); ((TAtom "iw_2.v65"), "data"); ((TAtom "iw_2.v66"), "to_do"); ((TAtom "iw_2.v67"), "count"); ((TAtom "iw_2.v71"), "fp"); ((TAtom "iw_2.v76"), "count"); ((TAtom "iw_2.v80"), "fp"); ((TAtom "iw_2.v82"), "fp"); ((TAtom "iw_2.v86"), "data"); ((TAtom "iw_2.v87"), "count"); ((TAtom "iw_2.v91"), "fp"); ((TAtom "iw_2.v93"), "fp"); ((TAtom "iw_2.v96"), "fp"); ((TAtom "iw_2.v98"), "fp"); ((TAtom "pr.1"), "s"); ((TAtom "pr.10"), "count"); ((TAtom "pr.11"), "count"); ((TAtom "pr.12"), "count"); ((TAtom "pr.13"), "count"); ((TAtom "pr.14"), "p"); ((TAtom "pr.2"), "to_do"); ((TAtom "pr.3"), "to_do"); ((TAtom "pr.4"), "to_do"); ((TAtom "pr.5"), "to_do"); ((TAtom "pr.6"), "must_flush"); ((TAtom "pr.7"), "must_flush"); ((TAtom "pr.8"), "must_flush"); ((TAtom "pr.9"), "count"); ((TAtom "v0"), "f"); ((TAtom "v102"), "count"); ((TAtom "v103"), "to_do"); ((TAtom "v105"), "to_do"); ((TAtom "v106"), "f"); ((TAtom "v108"), "f"); ((TAtom "v111"), "s"); ((TAtom "v112"), "count"); ((TAtom "v114"), "s"); ((TAtom "v115"), "count"); ((TAtom "v116"), "s"); ((TAtom "v117"), "to_do"); ((TAtom "v118"), "count"); ((TAtom "v119"), "to_do"); ((TAtom "v123"), "to_do"); ((TAtom "v124"), "must_flush"); ((TAtom "v133"), "f"); ((TAtom "v139"), "f"); ((TAtom "v147"), "to_do"); ((TAtom "v15"), "n"); ((TAtom "v151"), "n"); ((TAtom "v152"), "to_do"); ((TAtom "v156"), "f"); ((TAtom "v159"), "f"); ((TAtom "v164"), "block_size"); ((TAtom "v165"), "to_do"); ((TAtom "v169"), "block_size"); ((TAtom "v171"), "to_do"); ((TAtom "v172"), "block_size"); ((TAtom "v175"), "do_write"); ((TAtom "v179"), "do_write"); ((TAtom "v181"), "f"); ((TAtom "v182"), "s"); ((TAtom "v183"), "do_write"); ((TAtom "v184"), "count"); ((TAtom "v185"), "to_do"); ((TAtom "v186"), "count"); ((TAtom "v187"), "to_do"); ((TAtom "v191"), "count"); ((TAtom "v192"), "do_write"); ((TAtom "v194"), "n"); ((TAtom "v195"), "to_do"); ((TAtom "v2"), "data"); ((TAtom "v201"), "to_do"); ((TAtom "v203"), "to_do"); ((TAtom "v204"), "f"); ((TAtom "v205"), "s"); ((TAtom "v206"), "do_write"); ((TAtom "v208"), "to_do"); ((TAtom "v21"), "f"); ((TAtom "v210"), "to_do"); ((TAtom "v211"), "n"); ((TAtom "v212"), "to_do"); ((TAtom "v26"), "f"); ((TAtom "v31"), "f"); ((TAtom "v34"), "f"); ((TAtom "v39"), "count"); ((TAtom "v4"), "n"); ((TAtom "v43"), "count"); ((TAtom "v44"), "n"); ((TAtom "v47"), "s"); ((TAtom "v48"), "n"); ((TAtom "v49"), "p"); ((TAtom "v54"), "p"); ((TAtom "v55"), "s"); ((TAtom "v62"), "p"); ((TAtom "v63"), "p"); ((TAtom "v66"), "p"); ((TAtom "v67"), "s"); ((TAtom "v7"), "data"); ((TAtom "v71"), "count"); ((TAtom "v76"), "f"); ((TAtom "v79"), "f"); ((TAtom "v85"), "f"); ((TAtom "v88"), "f"); ((TAtom "v9"), "n"); ((TAtom "v93"), "count"); ((TAtom "v97"), "count")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L50")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_xsputn") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_xsputn.

Module fn___GI__IO_file_xsgetn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1348%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1357%nat)); ((TAtom "L12"), ("fileops.c", 1360%nat)); ((TAtom "L21"), ("fileops.c", 1362%nat)); ((TAtom "iw_1.L4"), ("./libioP.h", 1059%nat)); ((TAtom "iw_1.join"), ("fileops.c", 1363%nat)); ((TAtom "L23"), ("fileops.c", 1365%nat)); ((TAtom "L39"), ("fileops.c", 1353%nat)); ((TAtom "L40"), ("fileops.c", 1370%nat)); ((TAtom "L53"), ("fileops.c", 1373%nat)); ((TAtom "L54"), ("fileops.c", 1379%nat)); ((TAtom "L70"), ("fileops.c", 1381%nat)); ((TAtom "L72"), ("fileops.c", 1353%nat)); ((TAtom "L89"), ("fileops.c", 1389%nat)); ((TAtom "L91"), ("fileops.c", 1396%nat)); ((TAtom "L105"), ("fileops.c", 1396%nat)); ((TAtom "L106"), ("fileops.c", 1396%nat)); ((TAtom "L97"), ("fileops.c", 1399%nat)); ((TAtom "L99"), ("fileops.c", 1407%nat)); ((TAtom "L157"), ("fileops.c", 1414%nat)); ((TAtom "L175"), ("fileops.c", 1416%nat)); ((TAtom "L159"), ("fileops.c", 1352%nat)); ((TAtom "iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.join"), ("fileops.c", 1419%nat)); ((TAtom "L195"), ("fileops.c", 1422%nat)); ((TAtom "L200"), ("fileops.c", 1423%nat)); ((TAtom "L201"), ("fileops.c", 1425%nat)); ((TAtom "L197"), ("fileops.c", 1430%nat)); ((TAtom "L218"), ("fileops.c", 1433%nat)); ((TAtom "L41"), ("fileops.c", 1351%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "pr.1"), "want"); ((TAtom "pr.2"), "want"); ((TAtom "pr.3"), "want"); ((TAtom "pr.4"), "want"); ((TAtom "pr.5"), "count"); ((TAtom "pr.6"), "count"); ((TAtom "pr.7"), "s"); ((TAtom "pr.8"), "s"); ((TAtom "pr.9"), "s"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "data"); ((TAtom "v100"), "fp"); ((TAtom "v107"), "want"); ((TAtom "v108"), "fp"); ((TAtom "v11"), "n"); ((TAtom "v111"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v129"), "fp"); ((TAtom "v131"), "fp"); ((TAtom "v134"), "fp"); ((TAtom "v136"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v141"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v146"), "fp"); ((TAtom "v148"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v151"), "fp"); ((TAtom "v153"), "fp"); ((TAtom "v156"), "want"); ((TAtom "v160"), "fp"); ((TAtom "v166"), "fp"); ((TAtom "v169"), "fp"); ((TAtom "v174"), "block_size"); ((TAtom "v178"), "block_size"); ((TAtom "v180"), "count"); ((TAtom "v181"), "want"); ((TAtom "v182"), "block_size"); ((TAtom "v184"), "count"); ((TAtom "v185"), "fp"); ((TAtom "v191"), "fp"); ((TAtom "v192"), "s"); ((TAtom "v193"), "count"); ((TAtom "v194"), "count"); ((TAtom "v198"), "count"); ((TAtom "v2"), "data"); ((TAtom "v203"), "count"); ((TAtom "v205"), "fp"); ((TAtom "v208"), "fp"); ((TAtom "v212"), "s"); ((TAtom "v213"), "count"); ((TAtom "v214"), "s"); ((TAtom "v215"), "want"); ((TAtom "v216"), "count"); ((TAtom "v217"), "want"); ((TAtom "v221"), "fp"); ((TAtom "v227"), "fp"); ((TAtom "v230"), "count"); ((TAtom "v232"), "n"); ((TAtom "v233"), "want"); ((TAtom "v24"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v4"), "n"); ((TAtom "v42"), "want"); ((TAtom "v44"), "fp"); ((TAtom "v47"), "fp"); ((TAtom "v52"), "have"); ((TAtom "v56"), "want"); ((TAtom "v57"), "have"); ((TAtom "v59"), "s"); ((TAtom "v60"), "fp"); ((TAtom "v63"), "want"); ((TAtom "v65"), "fp"); ((TAtom "v68"), "want"); ((TAtom "v73"), "have"); ((TAtom "v75"), "s"); ((TAtom "v76"), "fp"); ((TAtom "v79"), "have"); ((TAtom "v80"), "s"); ((TAtom "v81"), "want"); ((TAtom "v82"), "have"); ((TAtom "v83"), "want"); ((TAtom "v84"), "fp"); ((TAtom "v87"), "have"); ((TAtom "v92"), "fp"); ((TAtom "v95"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L39")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_file_xsgetn") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_file_xsgetn.

Module fn__IO_file_xsgetn_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1441%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1445%nat)); ((TAtom "L22"), ("fileops.c", 1452%nat)); ((TAtom "L28"), ("fileops.c", 1454%nat)); ((TAtom "L30"), ("fileops.c", 1446%nat)); ((TAtom "L56"), ("fileops.c", 1464%nat)); ((TAtom "L62"), ("fileops.c", 1466%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 1466%nat)); ((TAtom "L64"), ("fileops.c", 1468%nat)); ((TAtom "L24"), ("fileops.c", 1446%nat)); ((TAtom "L96"), ("fileops.c", 1474%nat)); ((TAtom "L98"), ("fileops.c", 1476%nat)); ((TAtom "L105"), ("fileops.c", 1478%nat)); ((TAtom "L111"), ("fileops.c", 1478%nat)); ((TAtom "L112"), ("fileops.c", 1478%nat)); ((TAtom "L107"), ("fileops.c", 1446%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "n"); ((TAtom "pr.10"), "s"); ((TAtom "pr.11"), "s"); ((TAtom "pr.2"), "n"); ((TAtom "pr.3"), "have"); ((TAtom "pr.4"), "have"); ((TAtom "pr.5"), "have"); ((TAtom "pr.6"), "read_ptr"); ((TAtom "pr.7"), "read_ptr"); ((TAtom "pr.8"), "read_ptr"); ((TAtom "pr.9"), "s"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "read_ptr"); ((TAtom "v100"), "n"); ((TAtom "v102"), "fp"); ((TAtom "v108"), "have"); ((TAtom "v113"), "have"); ((TAtom "v114"), "n"); ((TAtom "v116"), "have"); ((TAtom "v117"), "n"); ((TAtom "v118"), "have"); ((TAtom "v119"), "s"); ((TAtom "v12"), "data"); ((TAtom "v120"), "read_ptr"); ((TAtom "v121"), "have"); ((TAtom "v122"), "s"); ((TAtom "v123"), "fp"); ((TAtom "v125"), "read_ptr"); ((TAtom "v126"), "have"); ((TAtom "v128"), "s"); ((TAtom "v129"), "data"); ((TAtom "v13"), "fp"); ((TAtom "v16"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v21"), "have"); ((TAtom "v25"), "have"); ((TAtom "v26"), "n"); ((TAtom "v31"), "fp"); ((TAtom "v36"), "s"); ((TAtom "v37"), "read_ptr"); ((TAtom "v38"), "have"); ((TAtom "v39"), "s"); ((TAtom "v4"), "n"); ((TAtom "v40"), "n"); ((TAtom "v41"), "have"); ((TAtom "v42"), "n"); ((TAtom "v43"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v46"), "read_ptr"); ((TAtom "v47"), "fp"); ((TAtom "v50"), "fp"); ((TAtom "v55"), "have"); ((TAtom "v59"), "have"); ((TAtom "v60"), "n"); ((TAtom "v65"), "fp"); ((TAtom "v69"), "s"); ((TAtom "v70"), "data"); ((TAtom "v74"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v80"), "fp"); ((TAtom "v81"), "data"); ((TAtom "v82"), "n"); ((TAtom "v86"), "fp"); ((TAtom "v88"), "read_ptr"); ((TAtom "v89"), "fp"); ((TAtom "v92"), "read_ptr"); ((TAtom "v95"), "have"); ((TAtom "v99"), "have")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_xsgetn_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_xsgetn_mmap.

Module fn__IO_file_xsgetn_maybe_mmap.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 1486%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 1492%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 1493%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v14"), "data"); ((TAtom "v15"), "n"); ((TAtom "v2"), "data"); ((TAtom "v4"), "n"); ((TAtom "v6"), "fp"); ((TAtom "v7"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_xsgetn_maybe_mmap") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_xsgetn_maybe_mmap.

Module fn_glibc_genops_flush_cleanup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 43%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 46%nat)); ((TAtom "L2"), ("genops.c", 47%nat)); ((TAtom "L18"), ("genops.c", 47%nat)); ((TAtom "L27"), ("genops.c", 47%nat)); ((TAtom "L28"), ("genops.c", 47%nat)); ((TAtom "L21"), ("genops.c", 47%nat)); ((TAtom "L22"), ("genops.c", 47%nat)); ((TAtom "L47"), ("genops.c", 47%nat)); ((TAtom "L71"), ("genops.c", 47%nat)); ((TAtom "L72"), ("genops.c", 47%nat)); ((TAtom "L83"), ("genops.c", 47%nat)); ((TAtom "L48"), ("genops.c", 47%nat)); ((TAtom "L101"), ("genops.c", 48%nat)); ((TAtom "L110"), ("genops.c", 48%nat)); ((TAtom "L111"), ("genops.c", 48%nat)); ((TAtom "L104"), ("genops.c", 48%nat)); ((TAtom "L105"), ("genops.c", 48%nat)); ((TAtom "L121"), ("genops.c", 48%nat)); ((TAtom "L136"), ("genops.c", 48%nat)); ((TAtom "L137"), ("genops.c", 48%nat)); ((TAtom "L148"), ("genops.c", 48%nat)); ((TAtom "L122"), ("genops.c", 48%nat)); ((TAtom "L103"), ("genops.c", 43%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "not_used"); ((TAtom "v108"), "__libc_single_threaded_internal"); ((TAtom "v134"), "__futex"); ((TAtom "v138"), "__oldval"); ((TAtom "v14"), "run_fp"); ((TAtom "v144"), "__oldval"); ((TAtom "v156"), "__futex"); ((TAtom "v157"), "__futex"); ((TAtom "v158"), "__private"); ((TAtom "v25"), "__libc_single_threaded_internal"); ((TAtom "v30"), "run_fp"); ((TAtom "v39"), "run_fp"); ((TAtom "v44"), "run_fp"); ((TAtom "v51"), "run_fp"); ((TAtom "v58"), "run_fp"); ((TAtom "v6"), "run_fp"); ((TAtom "v64"), "run_fp"); ((TAtom "v66"), "__futex"); ((TAtom "v69"), "__futex"); ((TAtom "v73"), "__oldval"); ((TAtom "v79"), "__oldval"); ((TAtom "v91"), "__futex"); ((TAtom "v92"), "__futex"); ((TAtom "v93"), "__private"); ((TAtom "v95"), "run_fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L136"); (TAtom "L71")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "glibc_genops#flush_cleanup") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_glibc_genops_flush_cleanup.

Module fn___GI__IO_un_link.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 65%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 72%nat)); ((TAtom "L2"), ("genops.c", 72%nat)); ((TAtom "L31"), ("genops.c", 73%nat)); ((TAtom "L32"), ("genops.c", 73%nat)); ((TAtom "L25"), ("genops.c", 73%nat)); ((TAtom "L26"), ("genops.c", 73%nat)); ((TAtom "L45"), ("genops.c", 73%nat)); ((TAtom "L65"), ("genops.c", 73%nat)); ((TAtom "L66"), ("genops.c", 73%nat)); ((TAtom "L70"), ("genops.c", 73%nat)); ((TAtom "L59"), ("genops.c", 73%nat)); ((TAtom "L46"), ("genops.c", 73%nat)); ((TAtom "L22"), ("genops.c", 74%nat)); ((TAtom "L96"), ("genops.c", 75%nat)); ((TAtom "L107"), ("genops.c", 75%nat)); ((TAtom "L108"), ("genops.c", 75%nat)); ((TAtom "L101"), ("genops.c", 75%nat)); ((TAtom "L102"), ("genops.c", 75%nat)); ((TAtom "L127"), ("genops.c", 75%nat)); ((TAtom "L151"), ("genops.c", 75%nat)); ((TAtom "L152"), ("genops.c", 75%nat)); ((TAtom "L156"), ("genops.c", 75%nat)); ((TAtom "L145"), ("genops.c", 75%nat)); ((TAtom "L128"), ("genops.c", 75%nat)); ((TAtom "L91"), ("genops.c", 77%nat)); ((TAtom "L185"), ("genops.c", 81%nat)); ((TAtom "L199"), ("genops.c", 85%nat)); ((TAtom "L179"), ("genops.c", 96%nat)); ((TAtom "L262"), ("genops.c", 98%nat)); ((TAtom "L271"), ("genops.c", 98%nat)); ((TAtom "L272"), ("genops.c", 98%nat)); ((TAtom "L265"), ("genops.c", 98%nat)); ((TAtom "L266"), ("genops.c", 98%nat)); ((TAtom "L288"), ("genops.c", 98%nat)); ((TAtom "L309"), ("genops.c", 98%nat)); ((TAtom "L310"), ("genops.c", 98%nat)); ((TAtom "L321"), ("genops.c", 98%nat)); ((TAtom "L289"), ("genops.c", 98%nat)); ((TAtom "L257"), ("genops.c", 99%nat)); ((TAtom "L348"), ("genops.c", 100%nat)); ((TAtom "L349"), ("genops.c", 100%nat)); ((TAtom "L342"), ("genops.c", 100%nat)); ((TAtom "L343"), ("genops.c", 100%nat)); ((TAtom "L359"), ("genops.c", 100%nat)); ((TAtom "L374"), ("genops.c", 100%nat)); ((TAtom "L375"), ("genops.c", 100%nat)); ((TAtom "L386"), ("genops.c", 100%nat)); ((TAtom "L360"), ("genops.c", 100%nat)); ((TAtom "L401"), ("genops.c", 101%nat)); ((TAtom "L4"), ("genops.c", 65%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "pr.2"), "_cleanup_start_doit"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "__self"); ((TAtom "v105"), "__libc_single_threaded_internal"); ((TAtom "v109"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "_cleanup_routine"); ((TAtom "v122"), "fp"); ((TAtom "v126"), "__self"); ((TAtom "v130"), "fp"); ((TAtom "v135"), "__self"); ((TAtom "v140"), "fp"); ((TAtom "v142"), "__futex"); ((TAtom "v147"), "__futex"); ((TAtom "v148"), "__atg3_old"); ((TAtom "v149"), "__atg3_old"); ((TAtom "v164"), "__futex"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "fp"); ((TAtom "v17"), "_cleanup_start_doit"); ((TAtom "v170"), "__self"); ((TAtom "v171"), "fp"); ((TAtom "v18"), "_cleanup_routine"); ((TAtom "v181"), "_IO_list_all"); ((TAtom "v19"), "_cleanup_start_doit"); ((TAtom "v190"), "fp"); ((TAtom "v192"), "pr"); ((TAtom "v194"), "fp"); ((TAtom "v196"), "nx"); ((TAtom "v197"), "pr"); ((TAtom "v198"), "nx"); ((TAtom "v202"), "nx"); ((TAtom "v206"), "nx"); ((TAtom "v208"), "pr"); ((TAtom "v212"), "fp"); ((TAtom "v214"), "_IO_list_all"); ((TAtom "v220"), "_IO_list_all"); ((TAtom "v222"), "_IO_list_all"); ((TAtom "v224"), "_IO_list_all"); ((TAtom "v225"), "f"); ((TAtom "v230"), "f"); ((TAtom "v237"), "f"); ((TAtom "v239"), "fp"); ((TAtom "v24"), "__self"); ((TAtom "v243"), "f"); ((TAtom "v244"), "fp"); ((TAtom "v248"), "f"); ((TAtom "v250"), "f"); ((TAtom "v251"), "fp"); ((TAtom "v258"), "fp"); ((TAtom "v269"), "__libc_single_threaded_internal"); ((TAtom "v273"), "fp"); ((TAtom "v281"), "fp"); ((TAtom "v285"), "fp"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v291"), "fp"); ((TAtom "v297"), "fp"); ((TAtom "v302"), "fp"); ((TAtom "v304"), "__futex"); ((TAtom "v307"), "__futex"); ((TAtom "v311"), "__oldval"); ((TAtom "v317"), "__oldval"); ((TAtom "v329"), "__futex"); ((TAtom "v330"), "__futex"); ((TAtom "v331"), "__private"); ((TAtom "v332"), "fp"); ((TAtom "v346"), "__libc_single_threaded_internal"); ((TAtom "v372"), "__futex"); ((TAtom "v376"), "__oldval"); ((TAtom "v382"), "__oldval"); ((TAtom "v394"), "__futex"); ((TAtom "v395"), "__futex"); ((TAtom "v396"), "__private"); ((TAtom "v404"), "_cleanup_start_doit"); ((TAtom "v408"), "_cleanup_routine"); ((TAtom "v44"), "__self"); ((TAtom "v5"), "fp"); ((TAtom "v51"), "__self"); ((TAtom "v61"), "__futex"); ((TAtom "v62"), "__atg3_old"); ((TAtom "v63"), "__atg3_old"); ((TAtom "v78"), "__futex"); ((TAtom "v79"), "__futex"); ((TAtom "v82"), "__self"); ((TAtom "v88"), "fp"); ((TAtom "v92"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L309"); (TAtom "L374")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_un_link") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_un_link.

Module fn__IO_switch_to_main_get_area.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 152%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 156%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v17"), "tmp"); ((TAtom "v18"), "fp"); ((TAtom "v20"), "tmp"); ((TAtom "v21"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "tmp"); ((TAtom "v29"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v31"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v9"), "tmp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_switch_to_main_get_area") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_switch_to_main_get_area.

Module fn__IO_switch_to_backup_area.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 171%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 175%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v11"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v16"), "tmp"); ((TAtom "v17"), "fp"); ((TAtom "v19"), "tmp"); ((TAtom "v20"), "fp"); ((TAtom "v22"), "fp"); ((TAtom "v25"), "fp"); ((TAtom "v27"), "tmp"); ((TAtom "v28"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v6"), "fp"); ((TAtom "v8"), "tmp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_switch_to_backup_area") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_switch_to_backup_area.

Module fn___GI__IO_switch_to_get_mode.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 188%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 191%nat)); ((TAtom "L2"), ("genops.c", 192%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 192%nat)); ((TAtom "L14"), ("genops.c", 193%nat)); ((TAtom "L4"), ("genops.c", 194%nat)); ((TAtom "L30"), ("genops.c", 195%nat)); ((TAtom "L31"), ("genops.c", 198%nat)); ((TAtom "L46"), ("genops.c", 200%nat)); ((TAtom "L32"), ("genops.c", 202%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v36"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v49"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v60"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v65"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v70"), "fp"); ((TAtom "v72"), "fp"); ((TAtom "v74"), "fp"); ((TAtom "v77"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_switch_to_get_mode") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_switch_to_get_mode.

Module fn___GI__IO_free_backup_area.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 211%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 214%nat)); ((TAtom "L2"), ("genops.c", 215%nat)); ((TAtom "L4"), ("genops.c", 216%nat)); ((TAtom "iw_1.L4"), ("./libioP.h", 1059%nat)); ((TAtom "iw_1.join"), ("genops.c", 217%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v5"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_free_backup_area") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_free_backup_area.

Module fn___GI___overflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 223%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 227%nat)); ((TAtom "L13"), ("genops.c", 228%nat)); ((TAtom "L23"), ("genops.c", 228%nat)); ((TAtom "L25"), ("genops.c", 228%nat)); ((TAtom "L6"), ("genops.c", 229%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 229%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "__result"); ((TAtom "pr.2"), "__result"); ((TAtom "v0"), "f"); ((TAtom "v12"), "__result"); ((TAtom "v16"), "__result"); ((TAtom "v2"), "ch"); ((TAtom "v26"), "f"); ((TAtom "v30"), "f"); ((TAtom "v33"), "f"); ((TAtom "v35"), "__result"); ((TAtom "v49"), "f"); ((TAtom "v52"), "__result"); ((TAtom "v53"), "f"); ((TAtom "v54"), "__result"); ((TAtom "v55"), "__result"); ((TAtom "v56"), "__result"); ((TAtom "v57"), "f"); ((TAtom "v63"), "f"); ((TAtom "v64"), "ch"); ((TAtom "v7"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___overflow") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___overflow.

Module fn_glibc_genops_save_for_backup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 233%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 142%nat)); ((TAtom "iw_1.L16"), ("genops.c", 143%nat)); ((TAtom "iw_1.L17"), ("genops.c", 145%nat)); ((TAtom "iw_1.L24"), ("genops.c", 146%nat)); ((TAtom "iw_1.L26"), ("genops.c", 142%nat)); ((TAtom "iw_1.join"), ("genops.c", 239%nat)); ((TAtom "L31"), ("genops.c", 249%nat)); ((TAtom "L42"), ("genops.c", 251%nat)); ((TAtom "L44"), ("genops.c", 252%nat)); ((TAtom "L51"), ("genops.c", 254%nat)); ((TAtom "L52"), ("genops.c", 261%nat)); ((TAtom "L53"), ("genops.c", 264%nat)); ((TAtom "iw_2.L4"), ("./libioP.h", 1059%nat)); ((TAtom "iw_2.join"), ("genops.c", 265%nat)); ((TAtom "L32"), ("genops.c", 270%nat)); ((TAtom "L105"), ("genops.c", 273%nat)); ((TAtom "L106"), ("genops.c", 280%nat)); ((TAtom "L141"), ("genops.c", 281%nat)); ((TAtom "L33"), ("genops.c", 242%nat)); ((TAtom "L175"), ("genops.c", 244%nat)); ((TAtom "L176"), ("genops.c", 289%nat)); ((TAtom "L178"), ("genops.c", 290%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.pr.1"), "least_so_far"); ((TAtom "iw_1.pr.2"), "least_so_far"); ((TAtom "iw_1.pr.3"), "mark"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v11"), "least_so_far"); ((TAtom "iw_1.v13"), "fp"); ((TAtom "iw_1.v15"), "mark"); ((TAtom "iw_1.v2"), "end_p"); ((TAtom "iw_1.v20"), "mark"); ((TAtom "iw_1.v27"), "mark"); ((TAtom "iw_1.v30"), "least_so_far"); ((TAtom "iw_1.v33"), "mark"); ((TAtom "iw_1.v36"), "least_so_far"); ((TAtom "iw_1.v37"), "mark"); ((TAtom "iw_1.v38"), "mark"); ((TAtom "iw_1.v39"), "least_so_far"); ((TAtom "iw_1.v5"), "end_p"); ((TAtom "iw_1.v6"), "fp"); ((TAtom "iw_2.v0"), "fp"); ((TAtom "iw_2.v13"), "ptr"); ((TAtom "iw_2.v2"), "ptr"); ((TAtom "iw_2.v7"), "ptr"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "pr.1"), "avail"); ((TAtom "pr.2"), "mark"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v100"), "needed_size"); ((TAtom "v102"), "current_Bsize"); ((TAtom "v103"), "needed_size"); ((TAtom "v104"), "avail"); ((TAtom "v108"), "least_mark"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "avail"); ((TAtom "v115"), "fp"); ((TAtom "v118"), "least_mark"); ((TAtom "v120"), "least_mark"); ((TAtom "v123"), "fp"); ((TAtom "v126"), "avail"); ((TAtom "v128"), "least_mark"); ((TAtom "v130"), "fp"); ((TAtom "v133"), "end_p"); ((TAtom "v134"), "fp"); ((TAtom "v144"), "needed_size"); ((TAtom "v146"), "fp"); ((TAtom "v149"), "avail"); ((TAtom "v151"), "fp"); ((TAtom "v154"), "least_mark"); ((TAtom "v156"), "needed_size"); ((TAtom "v158"), "fp"); ((TAtom "v16"), "least_mark"); ((TAtom "v160"), "fp"); ((TAtom "v163"), "avail"); ((TAtom "v165"), "end_p"); ((TAtom "v166"), "fp"); ((TAtom "v17"), "needed_size"); ((TAtom "v171"), "delta"); ((TAtom "v172"), "fp"); ((TAtom "v174"), "mark"); ((TAtom "v179"), "mark"); ((TAtom "v183"), "mark"); ((TAtom "v186"), "delta"); ((TAtom "v189"), "mark"); ((TAtom "v19"), "fp"); ((TAtom "v190"), "mark"); ((TAtom "v2"), "end_p"); ((TAtom "v22"), "fp"); ((TAtom "v27"), "current_Bsize"); ((TAtom "v34"), "needed_size"); ((TAtom "v35"), "current_Bsize"); ((TAtom "v38"), "avail"); ((TAtom "v39"), "needed_size"); ((TAtom "v41"), "new_buffer"); ((TAtom "v45"), "new_buffer"); ((TAtom "v5"), "fp"); ((TAtom "v54"), "least_mark"); ((TAtom "v56"), "new_buffer"); ((TAtom "v57"), "avail"); ((TAtom "v59"), "fp"); ((TAtom "v6"), "end_p"); ((TAtom "v62"), "least_mark"); ((TAtom "v64"), "least_mark"); ((TAtom "v67"), "fp"); ((TAtom "v7"), "least_mark"); ((TAtom "v70"), "end_p"); ((TAtom "v71"), "fp"); ((TAtom "v78"), "new_buffer"); ((TAtom "v79"), "avail"); ((TAtom "v81"), "fp"); ((TAtom "v84"), "least_mark"); ((TAtom "v86"), "needed_size"); ((TAtom "v88"), "fp"); ((TAtom "v89"), "fp"); ((TAtom "v9"), "end_p"); ((TAtom "v92"), "fp"); ((TAtom "v94"), "new_buffer"); ((TAtom "v95"), "fp"); ((TAtom "v97"), "new_buffer"); ((TAtom "v98"), "avail")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L175"); (TAtom "iw_1.L16")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "glibc_genops#save_for_backup") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_glibc_genops_save_for_backup.

Module fn___GI___underflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 293%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 296%nat)); ((TAtom "L20"), ("genops.c", 296%nat)); ((TAtom "L22"), ("genops.c", 296%nat)); ((TAtom "L2"), ("genops.c", 297%nat)); ((TAtom "L4"), ("genops.c", 299%nat)); ((TAtom "L69"), ("genops.c", 300%nat)); ((TAtom "L79"), ("genops.c", 300%nat)); ((TAtom "L81"), ("genops.c", 300%nat)); ((TAtom "L62"), ("genops.c", 301%nat)); ((TAtom "L113"), ("genops.c", 302%nat)); ((TAtom "L119"), ("genops.c", 303%nat)); ((TAtom "L115"), ("genops.c", 304%nat)); ((TAtom "L128"), ("genops.c", 305%nat)); ((TAtom "L130"), ("genops.c", 306%nat)); ((TAtom "L145"), ("genops.c", 308%nat)); ((TAtom "L152"), ("genops.c", 310%nat)); ((TAtom "L147"), ("genops.c", 312%nat)); ((TAtom "L169"), ("genops.c", 314%nat)); ((TAtom "L178"), ("genops.c", 315%nat)); ((TAtom "L170"), ("genops.c", 317%nat)); ((TAtom "L188"), ("genops.c", 318%nat)); ((TAtom "L171"), ("genops.c", 319%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 319%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "__result"); ((TAtom "pr.2"), "__result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v108"), "__result"); ((TAtom "v109"), "fp"); ((TAtom "v110"), "__result"); ((TAtom "v111"), "__result"); ((TAtom "v112"), "__result"); ((TAtom "v116"), "fp"); ((TAtom "v122"), "fp"); ((TAtom "v13"), "__result"); ((TAtom "v131"), "fp"); ((TAtom "v134"), "fp"); ((TAtom "v140"), "fp"); ((TAtom "v148"), "fp"); ((TAtom "v151"), "fp"); ((TAtom "v155"), "fp"); ((TAtom "v158"), "fp"); ((TAtom "v164"), "fp"); ((TAtom "v172"), "fp"); ((TAtom "v181"), "fp"); ((TAtom "v182"), "fp"); ((TAtom "v191"), "fp"); ((TAtom "v197"), "fp"); ((TAtom "v198"), "fp"); ((TAtom "v204"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v32"), "__result"); ((TAtom "v46"), "fp"); ((TAtom "v49"), "__result"); ((TAtom "v50"), "fp"); ((TAtom "v51"), "__result"); ((TAtom "v52"), "__result"); ((TAtom "v53"), "__result"); ((TAtom "v63"), "fp"); ((TAtom "v68"), "__result"); ((TAtom "v72"), "__result"); ((TAtom "v82"), "fp"); ((TAtom "v86"), "fp"); ((TAtom "v89"), "fp"); ((TAtom "v9"), "__result"); ((TAtom "v91"), "__result")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___underflow") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___underflow.

Module fn___GI__IO_setb.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 353%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 356%nat)); ((TAtom "L16"), ("genops.c", 356%nat)); ((TAtom "L17"), ("genops.c", 356%nat)); ((TAtom "L8"), ("genops.c", 357%nat)); ((TAtom "L10"), ("genops.c", 358%nat)); ((TAtom "L33"), ("genops.c", 361%nat)); ((TAtom "L34"), ("genops.c", 363%nat)); ((TAtom "L35"), ("genops.c", 353%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v11"), "f"); ((TAtom "v18"), "f"); ((TAtom "v2"), "b"); ((TAtom "v24"), "f"); ((TAtom "v27"), "f"); ((TAtom "v29"), "b"); ((TAtom "v30"), "f"); ((TAtom "v32"), "eb"); ((TAtom "v36"), "a"); ((TAtom "v37"), "f"); ((TAtom "v4"), "eb"); ((TAtom "v41"), "f"); ((TAtom "v6"), "a")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_setb") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_setb.

Module fn___GI__IO_doallocbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 367%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 370%nat)); ((TAtom "L2"), ("genops.c", 371%nat)); ((TAtom "L4"), ("genops.c", 372%nat)); ((TAtom "L18"), ("genops.c", 372%nat)); ((TAtom "L19"), ("genops.c", 372%nat)); ((TAtom "L11"), ("genops.c", 373%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 373%nat)); ((TAtom "L26"), ("genops.c", 374%nat)); ((TAtom "L13"), ("genops.c", 375%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v14"), "fp"); ((TAtom "v20"), "fp"); ((TAtom "v29"), "fp"); ((TAtom "v35"), "fp"); ((TAtom "v40"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v43"), "fp"); ((TAtom "v5"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_doallocbuf") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_doallocbuf.

Module fn___GI__IO_default_uflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 385%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 388%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 388%nat)); ((TAtom "L11"), ("genops.c", 390%nat)); ((TAtom "L13"), ("genops.c", 391%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "ch"); ((TAtom "v14"), "ch"); ((TAtom "v19"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_uflow") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_uflow.

Module fn___GI__IO_default_xsputn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 395%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 400%nat)); ((TAtom "L10"), ("genops.c", 401%nat)); ((TAtom "L16"), ("genops.c", 399%nat)); ((TAtom "L20"), ("genops.c", 407%nat)); ((TAtom "L43"), ("genops.c", 408%nat)); ((TAtom "L44"), ("genops.c", 407%nat)); ((TAtom "L49"), ("genops.c", 412%nat)); ((TAtom "L50"), ("genops.c", 415%nat)); ((TAtom "L65"), ("genops.c", 417%nat)); ((TAtom "L76"), ("genops.c", 418%nat)); ((TAtom "L77"), ("genops.c", 420%nat)); ((TAtom "L79"), ("genops.c", 421%nat)); ((TAtom "L51"), ("genops.c", 398%nat)); ((TAtom "L22"), ("genops.c", 399%nat)); ((TAtom "L99"), ("genops.c", 425%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 425%nat)); ((TAtom "L100"), ("genops.c", 425%nat)); ((TAtom "L96"), ("genops.c", 427%nat)); ((TAtom "L19"), ("genops.c", 429%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "s"); ((TAtom "pr.10"), "p"); ((TAtom "pr.11"), "i"); ((TAtom "pr.2"), "s"); ((TAtom "pr.3"), "s"); ((TAtom "pr.4"), "s"); ((TAtom "pr.5"), "s"); ((TAtom "pr.6"), "s"); ((TAtom "pr.7"), "more"); ((TAtom "pr.8"), "more"); ((TAtom "pr.9"), "count"); ((TAtom "v0"), "f"); ((TAtom "v101"), "f"); ((TAtom "v107"), "f"); ((TAtom "v108"), "s"); ((TAtom "v109"), "s"); ((TAtom "v118"), "more"); ((TAtom "v119"), "more"); ((TAtom "v120"), "n"); ((TAtom "v121"), "more"); ((TAtom "v13"), "more"); ((TAtom "v2"), "data"); ((TAtom "v23"), "f"); ((TAtom "v26"), "f"); ((TAtom "v33"), "f"); ((TAtom "v36"), "f"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v45"), "count"); ((TAtom "v46"), "more"); ((TAtom "v48"), "more"); ((TAtom "v52"), "count"); ((TAtom "v54"), "f"); ((TAtom "v56"), "f"); ((TAtom "v59"), "s"); ((TAtom "v60"), "count"); ((TAtom "v62"), "s"); ((TAtom "v63"), "count"); ((TAtom "v64"), "s"); ((TAtom "v68"), "count"); ((TAtom "v7"), "data"); ((TAtom "v71"), "f"); ((TAtom "v73"), "p"); ((TAtom "v75"), "count"); ((TAtom "v80"), "i"); ((TAtom "v81"), "i"); ((TAtom "v83"), "p"); ((TAtom "v84"), "p"); ((TAtom "v85"), "s"); ((TAtom "v86"), "s"); ((TAtom "v88"), "f"); ((TAtom "v9"), "n"); ((TAtom "v90"), "p"); ((TAtom "v91"), "more"); ((TAtom "v92"), "count"); ((TAtom "v93"), "more"); ((TAtom "v97"), "more")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L16"); (TAtom "L76")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_xsputn") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_xsputn.

Module fn___GI__IO_default_xsgetn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 441%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 446%nat)); ((TAtom "L10"), ("genops.c", 445%nat)); ((TAtom "L14"), ("genops.c", 451%nat)); ((TAtom "L37"), ("genops.c", 452%nat)); ((TAtom "L38"), ("genops.c", 451%nat)); ((TAtom "L43"), ("genops.c", 456%nat)); ((TAtom "L44"), ("genops.c", 459%nat)); ((TAtom "L59"), ("genops.c", 461%nat)); ((TAtom "L70"), ("genops.c", 462%nat)); ((TAtom "L71"), ("genops.c", 464%nat)); ((TAtom "L72"), ("genops.c", 465%nat)); ((TAtom "L45"), ("genops.c", 445%nat)); ((TAtom "L16"), ("genops.c", 445%nat)); ((TAtom "L92"), ("genops.c", 469%nat)); ((TAtom "L93"), ("genops.c", 469%nat)); ((TAtom "L13"), ("genops.c", 472%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "more"); ((TAtom "pr.10"), "i"); ((TAtom "pr.2"), "more"); ((TAtom "pr.3"), "s"); ((TAtom "pr.4"), "s"); ((TAtom "pr.5"), "s"); ((TAtom "pr.6"), "s"); ((TAtom "pr.7"), "s"); ((TAtom "pr.8"), "count"); ((TAtom "pr.9"), "p"); ((TAtom "v0"), "fp"); ((TAtom "v101"), "n"); ((TAtom "v102"), "more"); ((TAtom "v17"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v20"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v35"), "count"); ((TAtom "v39"), "count"); ((TAtom "v4"), "n"); ((TAtom "v40"), "more"); ((TAtom "v42"), "more"); ((TAtom "v46"), "count"); ((TAtom "v48"), "s"); ((TAtom "v49"), "fp"); ((TAtom "v52"), "count"); ((TAtom "v53"), "s"); ((TAtom "v54"), "fp"); ((TAtom "v57"), "count"); ((TAtom "v62"), "count"); ((TAtom "v65"), "fp"); ((TAtom "v67"), "p"); ((TAtom "v69"), "count"); ((TAtom "v7"), "n"); ((TAtom "v73"), "i"); ((TAtom "v74"), "i"); ((TAtom "v76"), "s"); ((TAtom "v77"), "s"); ((TAtom "v78"), "p"); ((TAtom "v79"), "p"); ((TAtom "v81"), "fp"); ((TAtom "v83"), "p"); ((TAtom "v84"), "more"); ((TAtom "v85"), "count"); ((TAtom "v86"), "more"); ((TAtom "v9"), "data"); ((TAtom "v90"), "more"); ((TAtom "v94"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L10"); (TAtom "L70")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_xsgetn") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_xsgetn.

Module fn__IO_default_setbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 476%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 479%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 479%nat)); ((TAtom "L6"), ("genops.c", 480%nat)); ((TAtom "L8"), ("genops.c", 481%nat)); ((TAtom "L27"), ("genops.c", 481%nat)); ((TAtom "L28"), ("genops.c", 481%nat)); ((TAtom "L20"), ("genops.c", 483%nat)); ((TAtom "L21"), ("genops.c", 488%nat)); ((TAtom "L22"), ("genops.c", 491%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v2"), "p"); ((TAtom "v23"), "p"); ((TAtom "v29"), "len"); ((TAtom "v33"), "fp"); ((TAtom "v36"), "fp"); ((TAtom "v37"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v4"), "len"); ((TAtom "v42"), "fp"); ((TAtom "v46"), "fp"); ((TAtom "v47"), "p"); ((TAtom "v48"), "p"); ((TAtom "v49"), "len"); ((TAtom "v51"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v57"), "fp"); ((TAtom "v59"), "fp"); ((TAtom "v61"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v9"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_setbuf") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_setbuf.

Module fn__IO_default_seekpos.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 496%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 499%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 499%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v13"), "pos"); ((TAtom "v14"), "mode"); ((TAtom "v2"), "pos"); ((TAtom "v4"), "mode"); ((TAtom "v6"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_seekpos") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_seekpos.

Module fn___GI__IO_default_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 502%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 507%nat)); ((TAtom "L4"), ("genops.c", 509%nat)); ((TAtom "L6"), ("genops.c", 511%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v16"), "buf"); ((TAtom "v17"), "buf"); ((TAtom "v3"), "buf"); ((TAtom "v7"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_doallocate") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_doallocate.

Module fn__IO_default_sync.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 617%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 620%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_sync") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_sync.

Module fn___GI__IO_default_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 626%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 630%nat)); ((TAtom "L13"), ("genops.c", 630%nat)); ((TAtom "L14"), ("genops.c", 630%nat)); ((TAtom "L5"), ("genops.c", 632%nat)); ((TAtom "L7"), ("genops.c", 636%nat)); ((TAtom "L31"), ("genops.c", 629%nat)); ((TAtom "L32"), ("genops.c", 637%nat)); ((TAtom "L34"), ("genops.c", 639%nat)); ((TAtom "L43"), ("genops.c", 640%nat)); ((TAtom "L45"), ("genops.c", 642%nat)); ((TAtom "L55"), ("genops.c", 645%nat)); ((TAtom "L56"), ("genops.c", 626%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "mark"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v21"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "fp"); ((TAtom "v30"), "mark"); ((TAtom "v35"), "mark"); ((TAtom "v39"), "mark"); ((TAtom "v41"), "mark"); ((TAtom "v42"), "mark"); ((TAtom "v46"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v57"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L31")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_finish") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_finish.

Module fn___GI__IO_adjust_column.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 697%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 700%nat)); ((TAtom "L11"), ("genops.c", 700%nat)); ((TAtom "L12"), ("genops.c", 702%nat)); ((TAtom "L19"), ("genops.c", 703%nat)); ((TAtom "L13"), ("genops.c", 704%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "ptr"); ((TAtom "v0"), "start"); ((TAtom "v10"), "ptr"); ((TAtom "v14"), "ptr"); ((TAtom "v15"), "line"); ((TAtom "v2"), "line"); ((TAtom "v22"), "ptr"); ((TAtom "v23"), "ptr"); ((TAtom "v26"), "line"); ((TAtom "v27"), "count"); ((TAtom "v30"), "ptr"); ((TAtom "v36"), "start"); ((TAtom "v37"), "count"); ((TAtom "v4"), "count"); ((TAtom "v7"), "line"); ((TAtom "v8"), "count")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L11")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_adjust_column") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_adjust_column.

Module fn___GI__IO_flush_all.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 708%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 715%nat)); ((TAtom "L24"), ("genops.c", 716%nat)); ((TAtom "L25"), ("genops.c", 716%nat)); ((TAtom "L18"), ("genops.c", 716%nat)); ((TAtom "L19"), ("genops.c", 716%nat)); ((TAtom "L38"), ("genops.c", 716%nat)); ((TAtom "L58"), ("genops.c", 716%nat)); ((TAtom "L59"), ("genops.c", 716%nat)); ((TAtom "L63"), ("genops.c", 716%nat)); ((TAtom "L52"), ("genops.c", 716%nat)); ((TAtom "L39"), ("genops.c", 716%nat)); ((TAtom "L15"), ("genops.c", 719%nat)); ((TAtom "L82"), ("genops.c", 712%nat)); ((TAtom "L83"), ("genops.c", 721%nat)); ((TAtom "L99"), ("genops.c", 722%nat)); ((TAtom "L110"), ("genops.c", 722%nat)); ((TAtom "L111"), ("genops.c", 722%nat)); ((TAtom "L104"), ("genops.c", 722%nat)); ((TAtom "L105"), ("genops.c", 722%nat)); ((TAtom "L130"), ("genops.c", 722%nat)); ((TAtom "L154"), ("genops.c", 722%nat)); ((TAtom "L155"), ("genops.c", 722%nat)); ((TAtom "L159"), ("genops.c", 722%nat)); ((TAtom "L148"), ("genops.c", 722%nat)); ((TAtom "L131"), ("genops.c", 722%nat)); ((TAtom "L94"), ("genops.c", 726%nat)); ((TAtom "L180"), ("genops.c", 728%nat)); ((TAtom "L197"), ("genops.c", 728%nat)); ((TAtom "L198"), ("genops.c", 728%nat)); ((TAtom "L213"), ("genops.c", 728%nat)); ((TAtom "L221"), ("genops.c", 728%nat)); ((TAtom "L211"), ("genops.c", 728%nat)); ((TAtom "L240"), ("genops.c", 728%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 728%nat)); ((TAtom "L241"), ("genops.c", 728%nat)); ((TAtom "L191"), ("genops.c", 728%nat)); ((TAtom "L192"), ("genops.c", 711%nat)); ((TAtom "L263"), ("genops.c", 735%nat)); ((TAtom "L269"), ("genops.c", 735%nat)); ((TAtom "L270"), ("genops.c", 735%nat)); ((TAtom "L285"), ("genops.c", 735%nat)); ((TAtom "L293"), ("genops.c", 735%nat)); ((TAtom "L264"), ("genops.c", 735%nat)); ((TAtom "L313"), ("genops.c", 735%nat)); ((TAtom "iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.join"), ("genops.c", 735%nat)); ((TAtom "L314"), ("genops.c", 735%nat)); ((TAtom "L257"), ("genops.c", 735%nat)); ((TAtom "L182"), ("genops.c", 711%nat)); ((TAtom "L334"), ("genops.c", 744%nat)); ((TAtom "L343"), ("genops.c", 744%nat)); ((TAtom "L344"), ("genops.c", 744%nat)); ((TAtom "L337"), ("genops.c", 744%nat)); ((TAtom "L338"), ("genops.c", 744%nat)); ((TAtom "L360"), ("genops.c", 744%nat)); ((TAtom "L381"), ("genops.c", 744%nat)); ((TAtom "L382"), ("genops.c", 744%nat)); ((TAtom "L393"), ("genops.c", 744%nat)); ((TAtom "L361"), ("genops.c", 744%nat)); ((TAtom "L329"), ("genops.c", 745%nat)); ((TAtom "L414"), ("genops.c", 749%nat)); ((TAtom "L423"), ("genops.c", 749%nat)); ((TAtom "L424"), ("genops.c", 749%nat)); ((TAtom "L417"), ("genops.c", 749%nat)); ((TAtom "L418"), ("genops.c", 749%nat)); ((TAtom "L434"), ("genops.c", 749%nat)); ((TAtom "L449"), ("genops.c", 749%nat)); ((TAtom "L450"), ("genops.c", 749%nat)); ((TAtom "L461"), ("genops.c", 749%nat)); ((TAtom "L435"), ("genops.c", 749%nat)); ((TAtom "L476"), ("genops.c", 750%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "result"); ((TAtom "pr.4"), "result"); ((TAtom "pr.5"), "fp"); ((TAtom "pr.6"), "_cleanup_start_doit"); ((TAtom "v10"), "_cleanup_start_doit"); ((TAtom "v103"), "__self"); ((TAtom "v108"), "__libc_single_threaded_internal"); ((TAtom "v11"), "_cleanup_routine"); ((TAtom "v112"), "fp"); ((TAtom "v12"), "_cleanup_start_doit"); ((TAtom "v122"), "fp"); ((TAtom "v125"), "fp"); ((TAtom "v129"), "__self"); ((TAtom "v133"), "fp"); ((TAtom "v138"), "__self"); ((TAtom "v143"), "fp"); ((TAtom "v145"), "__futex"); ((TAtom "v150"), "__futex"); ((TAtom "v151"), "__atg3_old"); ((TAtom "v152"), "__atg3_old"); ((TAtom "v167"), "__futex"); ((TAtom "v168"), "__futex"); ((TAtom "v169"), "fp"); ((TAtom "v17"), "__self"); ((TAtom "v173"), "__self"); ((TAtom "v174"), "fp"); ((TAtom "v183"), "fp"); ((TAtom "v193"), "fp"); ((TAtom "v199"), "fp"); ((TAtom "v202"), "fp"); ((TAtom "v215"), "fp"); ((TAtom "v22"), "__libc_single_threaded_internal"); ((TAtom "v223"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v242"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v255"), "result"); ((TAtom "v259"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v274"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v295"), "fp"); ((TAtom "v299"), "fp"); ((TAtom "v315"), "fp"); ((TAtom "v321"), "fp"); ((TAtom "v326"), "result"); ((TAtom "v330"), "fp"); ((TAtom "v341"), "__libc_single_threaded_internal"); ((TAtom "v345"), "fp"); ((TAtom "v353"), "fp"); ((TAtom "v357"), "fp"); ((TAtom "v363"), "fp"); ((TAtom "v369"), "fp"); ((TAtom "v37"), "__self"); ((TAtom "v374"), "fp"); ((TAtom "v376"), "__futex"); ((TAtom "v379"), "__futex"); ((TAtom "v383"), "__oldval"); ((TAtom "v389"), "__oldval"); ((TAtom "v401"), "__futex"); ((TAtom "v402"), "__futex"); ((TAtom "v403"), "__private"); ((TAtom "v404"), "fp"); ((TAtom "v411"), "fp"); ((TAtom "v413"), "fp"); ((TAtom "v421"), "__libc_single_threaded_internal"); ((TAtom "v44"), "__self"); ((TAtom "v447"), "__futex"); ((TAtom "v451"), "__oldval"); ((TAtom "v457"), "__oldval"); ((TAtom "v469"), "__futex"); ((TAtom "v470"), "__futex"); ((TAtom "v471"), "__private"); ((TAtom "v479"), "_cleanup_start_doit"); ((TAtom "v483"), "_cleanup_routine"); ((TAtom "v486"), "result"); ((TAtom "v5"), "_cleanup_routine"); ((TAtom "v54"), "__futex"); ((TAtom "v55"), "__atg3_old"); ((TAtom "v56"), "__atg3_old"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__futex"); ((TAtom "v75"), "__self"); ((TAtom "v81"), "_IO_list_all"); ((TAtom "v86"), "fp"); ((TAtom "v91"), "fp"); ((TAtom "v95"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L381"); (TAtom "L449"); (TAtom "L82")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_flush_all") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_flush_all.

Module fn__IO_cleanup.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 886%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 889%nat)); ((TAtom "iw_1.L23"), ("genops.c", 817%nat)); ((TAtom "iw_1.L24"), ("genops.c", 817%nat)); ((TAtom "iw_1.L17"), ("genops.c", 817%nat)); ((TAtom "iw_1.L18"), ("genops.c", 817%nat)); ((TAtom "iw_1.L37"), ("genops.c", 817%nat)); ((TAtom "iw_1.L57"), ("genops.c", 817%nat)); ((TAtom "iw_1.L58"), ("genops.c", 817%nat)); ((TAtom "iw_1.L62"), ("genops.c", 817%nat)); ((TAtom "iw_1.L51"), ("genops.c", 817%nat)); ((TAtom "iw_1.L38"), ("genops.c", 817%nat)); ((TAtom "iw_1.L14"), ("genops.c", 820%nat)); ((TAtom "iw_1.L81"), ("genops.c", 813%nat)); ((TAtom "iw_1.L82"), ("genops.c", 824%nat)); ((TAtom "iw_1.L98"), ("genops.c", 825%nat)); ((TAtom "iw_1.L109"), ("genops.c", 825%nat)); ((TAtom "iw_1.L110"), ("genops.c", 825%nat)); ((TAtom "iw_1.L103"), ("genops.c", 825%nat)); ((TAtom "iw_1.L104"), ("genops.c", 825%nat)); ((TAtom "iw_1.L129"), ("genops.c", 825%nat)); ((TAtom "iw_1.L153"), ("genops.c", 825%nat)); ((TAtom "iw_1.L154"), ("genops.c", 825%nat)); ((TAtom "iw_1.L158"), ("genops.c", 825%nat)); ((TAtom "iw_1.L147"), ("genops.c", 825%nat)); ((TAtom "iw_1.L130"), ("genops.c", 825%nat)); ((TAtom "iw_1.L93"), ("genops.c", 833%nat)); ((TAtom "iw_1.L179"), ("genops.c", 834%nat)); ((TAtom "iw_1.L194"), ("genops.c", 835%nat)); ((TAtom "iw_1.L202"), ("genops.c", 835%nat)); ((TAtom "iw_1.L203"), ("genops.c", 835%nat)); ((TAtom "iw_1.L189"), ("genops.c", 836%nat)); ((TAtom "iw_1.L191"), ("genops.c", 838%nat)); ((TAtom "iw_1.L225"), ("genops.c", 838%nat)); ((TAtom "iw_1.L223"), ("genops.c", 838%nat)); ((TAtom "iw_1.L240"), ("genops.c", 842%nat)); ((TAtom "iw_1.L247"), ("genops.c", 842%nat)); ((TAtom "iw_1.L248"), ("genops.c", 842%nat)); ((TAtom "iw_1.L235"), ("genops.c", 844%nat)); ((TAtom "iw_1.L237"), ("genops.c", 851%nat)); ((TAtom "iw_1.iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.iw_1.join"), ("genops.c", 851%nat)); ((TAtom "iw_1.L277"), ("genops.c", 854%nat)); ((TAtom "iw_1.L291"), ("genops.c", 860%nat)); ((TAtom "iw_1.L306"), ("genops.c", 862%nat)); ((TAtom "iw_1.L315"), ("genops.c", 862%nat)); ((TAtom "iw_1.L316"), ("genops.c", 862%nat)); ((TAtom "iw_1.L309"), ("genops.c", 862%nat)); ((TAtom "iw_1.L310"), ("genops.c", 862%nat)); ((TAtom "iw_1.L332"), ("genops.c", 862%nat)); ((TAtom "iw_1.L353"), ("genops.c", 862%nat)); ((TAtom "iw_1.L354"), ("genops.c", 862%nat)); ((TAtom "iw_1.L365"), ("genops.c", 862%nat)); ((TAtom "iw_1.L333"), ("genops.c", 862%nat)); ((TAtom "iw_1.L301"), ("genops.c", 863%nat)); ((TAtom "iw_1.L386"), ("genops.c", 867%nat)); ((TAtom "iw_1.L395"), ("genops.c", 867%nat)); ((TAtom "iw_1.L396"), ("genops.c", 867%nat)); ((TAtom "iw_1.L389"), ("genops.c", 867%nat)); ((TAtom "iw_1.L390"), ("genops.c", 867%nat)); ((TAtom "iw_1.L406"), ("genops.c", 867%nat)); ((TAtom "iw_1.L421"), ("genops.c", 867%nat)); ((TAtom "iw_1.L422"), ("genops.c", 867%nat)); ((TAtom "iw_1.L433"), ("genops.c", 867%nat)); ((TAtom "iw_1.L407"), ("genops.c", 867%nat)); ((TAtom "iw_1.L448"), ("genops.c", 868%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.pr.1"), "fp"); ((TAtom "iw_1.pr.2"), "_cleanup_start_doit"); ((TAtom "iw_1.v10"), "_cleanup_routine"); ((TAtom "iw_1.v102"), "__self"); ((TAtom "iw_1.v107"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v11"), "_cleanup_start_doit"); ((TAtom "iw_1.v111"), "fp"); ((TAtom "iw_1.v121"), "fp"); ((TAtom "iw_1.v124"), "fp"); ((TAtom "iw_1.v128"), "__self"); ((TAtom "iw_1.v132"), "fp"); ((TAtom "iw_1.v137"), "__self"); ((TAtom "iw_1.v142"), "fp"); ((TAtom "iw_1.v144"), "__futex"); ((TAtom "iw_1.v149"), "__futex"); ((TAtom "iw_1.v150"), "__atg3_old"); ((TAtom "iw_1.v151"), "__atg3_old"); ((TAtom "iw_1.v16"), "__self"); ((TAtom "iw_1.v166"), "__futex"); ((TAtom "iw_1.v167"), "__futex"); ((TAtom "iw_1.v168"), "fp"); ((TAtom "iw_1.v172"), "__self"); ((TAtom "iw_1.v173"), "fp"); ((TAtom "iw_1.v182"), "fp"); ((TAtom "iw_1.v188"), "fp"); ((TAtom "iw_1.v192"), "legacy"); ((TAtom "iw_1.v196"), "fp"); ((TAtom "iw_1.v204"), "fp"); ((TAtom "iw_1.v21"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v214"), "fp"); ((TAtom "iw_1.v218"), "fp"); ((TAtom "iw_1.v224"), "legacy"); ((TAtom "iw_1.v227"), "fp"); ((TAtom "iw_1.v238"), "legacy"); ((TAtom "iw_1.v243"), "dealloc_buffers"); ((TAtom "iw_1.v249"), "fp"); ((TAtom "iw_1.v255"), "fp"); ((TAtom "iw_1.v258"), "fp"); ((TAtom "iw_1.v261"), "freeres_list"); ((TAtom "iw_1.v263"), "fp"); ((TAtom "iw_1.v264"), "fp"); ((TAtom "iw_1.v266"), "fp"); ((TAtom "iw_1.v269"), "fp"); ((TAtom "iw_1.v275"), "fp"); ((TAtom "iw_1.v280"), "legacy"); ((TAtom "iw_1.v284"), "fp"); ((TAtom "iw_1.v290"), "fp"); ((TAtom "iw_1.v294"), "legacy"); ((TAtom "iw_1.v296"), "fp"); ((TAtom "iw_1.v302"), "fp"); ((TAtom "iw_1.v313"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v317"), "fp"); ((TAtom "iw_1.v325"), "fp"); ((TAtom "iw_1.v329"), "fp"); ((TAtom "iw_1.v335"), "fp"); ((TAtom "iw_1.v341"), "fp"); ((TAtom "iw_1.v346"), "fp"); ((TAtom "iw_1.v348"), "__futex"); ((TAtom "iw_1.v351"), "__futex"); ((TAtom "iw_1.v355"), "__oldval"); ((TAtom "iw_1.v36"), "__self"); ((TAtom "iw_1.v361"), "__oldval"); ((TAtom "iw_1.v373"), "__futex"); ((TAtom "iw_1.v374"), "__futex"); ((TAtom "iw_1.v375"), "__private"); ((TAtom "iw_1.v376"), "fp"); ((TAtom "iw_1.v383"), "fp"); ((TAtom "iw_1.v385"), "fp"); ((TAtom "iw_1.v393"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v4"), "_cleanup_routine"); ((TAtom "iw_1.v419"), "__futex"); ((TAtom "iw_1.v423"), "__oldval"); ((TAtom "iw_1.v429"), "__oldval"); ((TAtom "iw_1.v43"), "__self"); ((TAtom "iw_1.v441"), "__futex"); ((TAtom "iw_1.v442"), "__futex"); ((TAtom "iw_1.v443"), "__private"); ((TAtom "iw_1.v451"), "_cleanup_start_doit"); ((TAtom "iw_1.v455"), "_cleanup_routine"); ((TAtom "iw_1.v53"), "__futex"); ((TAtom "iw_1.v54"), "__atg3_old"); ((TAtom "iw_1.v55"), "__atg3_old"); ((TAtom "iw_1.v70"), "__futex"); ((TAtom "iw_1.v71"), "__futex"); ((TAtom "iw_1.v74"), "__self"); ((TAtom "iw_1.v80"), "_IO_list_all"); ((TAtom "iw_1.v85"), "fp"); ((TAtom "iw_1.v9"), "_cleanup_start_doit"); ((TAtom "iw_1.v90"), "fp"); ((TAtom "iw_1.v94"), "fp"); ((TAtom "v1"), "result"); ((TAtom "v2"), "result")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_1.L353"); (TAtom "iw_1.L421"); (TAtom "iw_1.L81")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_cleanup") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_cleanup.

Module fn___GI__IO_unsave_markers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 981%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 984%nat)); ((TAtom "L6"), ("genops.c", 987%nat)); ((TAtom "L8"), ("genops.c", 990%nat)); ((TAtom "L14"), ("genops.c", 991%nat)); ((TAtom "L16"), ("genops.c", 981%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v5"), "mark"); ((TAtom "v9"), "mark")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_unsave_markers") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_unsave_markers.

Module fn___GI__IO_default_pbackfail.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 995%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 998%nat)); ((TAtom "L16"), ("genops.c", 998%nat)); ((TAtom "L17"), ("genops.c", 998%nat)); ((TAtom "L24"), ("genops.c", 998%nat)); ((TAtom "L25"), ("genops.c", 998%nat)); ((TAtom "L4"), ("genops.c", 1000%nat)); ((TAtom "L5"), ("genops.c", 1004%nat)); ((TAtom "L42"), ("genops.c", 1008%nat)); ((TAtom "L61"), ("genops.c", 1008%nat)); ((TAtom "L62"), ("genops.c", 1008%nat)); ((TAtom "L49"), ("genops.c", 1010%nat)); ((TAtom "L71"), ("genops.c", 1011%nat)); ((TAtom "L50"), ("genops.c", 1013%nat)); ((TAtom "L81"), ("genops.c", 1017%nat)); ((TAtom "L96"), ("genops.c", 1021%nat)); ((TAtom "L98"), ("genops.c", 1017%nat)); ((TAtom "L51"), ("genops.c", 1028%nat)); ((TAtom "L43"), ("genops.c", 1031%nat)); ((TAtom "L127"), ("genops.c", 1035%nat)); ((TAtom "L155"), ("genops.c", 1040%nat)); ((TAtom "L157"), ("genops.c", 1041%nat)); ((TAtom "iw_1.L4"), ("./libioP.h", 1059%nat)); ((TAtom "iw_1.join"), ("genops.c", 1044%nat)); ((TAtom "L44"), ("genops.c", 1049%nat)); ((TAtom "L6"), ("genops.c", 1051%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v13"), "ptr"); ((TAtom "iw_1.v2"), "ptr"); ((TAtom "iw_1.v7"), "ptr"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "pr.1"), "backup_size"); ((TAtom "pr.2"), "bbuf"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v103"), "fp"); ((TAtom "v104"), "bbuf"); ((TAtom "v105"), "fp"); ((TAtom "v107"), "bbuf"); ((TAtom "v108"), "fp"); ((TAtom "v110"), "fp"); ((TAtom "v113"), "backup_size"); ((TAtom "v116"), "fp"); ((TAtom "v118"), "fp"); ((TAtom "v121"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v126"), "fp"); ((TAtom "v130"), "fp"); ((TAtom "v133"), "fp"); ((TAtom "v141"), "fp"); ((TAtom "v144"), "fp"); ((TAtom "v149"), "old_size"); ((TAtom "v151"), "old_size"); ((TAtom "v152"), "new_size"); ((TAtom "v153"), "new_size"); ((TAtom "v154"), "new_buf"); ((TAtom "v158"), "new_buf"); ((TAtom "v164"), "new_buf"); ((TAtom "v165"), "new_size"); ((TAtom "v166"), "old_size"); ((TAtom "v169"), "fp"); ((TAtom "v172"), "old_size"); ((TAtom "v174"), "fp"); ((TAtom "v175"), "fp"); ((TAtom "v178"), "fp"); ((TAtom "v18"), "fp"); ((TAtom "v180"), "new_buf"); ((TAtom "v181"), "fp"); ((TAtom "v183"), "new_buf"); ((TAtom "v184"), "new_size"); ((TAtom "v185"), "old_size"); ((TAtom "v188"), "fp"); ((TAtom "v190"), "new_buf"); ((TAtom "v191"), "new_size"); ((TAtom "v193"), "fp"); ((TAtom "v195"), "fp"); ((TAtom "v198"), "fp"); ((TAtom "v2"), "c"); ((TAtom "v202"), "c"); ((TAtom "v204"), "c"); ((TAtom "v26"), "fp"); ((TAtom "v34"), "c"); ((TAtom "v38"), "fp"); ((TAtom "v45"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v55"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v74"), "fp"); ((TAtom "v75"), "fp"); ((TAtom "v84"), "fp"); ((TAtom "v93"), "backup_size"); ((TAtom "v95"), "bbuf"); ((TAtom "v99"), "bbuf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_pbackfail") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_pbackfail.

Module fn__IO_default_seek.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 1055%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 1058%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "dir")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_seek") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_seek.

Module fn__IO_default_stat.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 1061%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 1064%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "st")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_stat") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_stat.

Module fn__IO_default_read.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 1067%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 1070%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v4"), "n")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_read") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_read.

Module fn__IO_default_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 1073%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 1076%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "data"); ((TAtom "v4"), "n")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_write") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_write.

Module fn__IO_default_showmanyc.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 1079%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 1082%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_showmanyc") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_showmanyc.

Module fn__IO_default_imbue.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 1085%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 1085%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v2"), "locale")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_default_imbue") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_default_imbue.

Module fn__IO_new_fclose.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("iofclose.c", 32%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("iofclose.c", 47%nat)); ((TAtom "L18"), ("iofclose.c", 47%nat)); ((TAtom "L29"), ("iofclose.c", 47%nat)); ((TAtom "L30"), ("iofclose.c", 47%nat)); ((TAtom "L23"), ("iofclose.c", 47%nat)); ((TAtom "L24"), ("iofclose.c", 47%nat)); ((TAtom "L49"), ("iofclose.c", 47%nat)); ((TAtom "L73"), ("iofclose.c", 47%nat)); ((TAtom "L74"), ("iofclose.c", 47%nat)); ((TAtom "L78"), ("iofclose.c", 47%nat)); ((TAtom "L67"), ("iofclose.c", 47%nat)); ((TAtom "L50"), ("iofclose.c", 47%nat)); ((TAtom "L13"), ("iofclose.c", 48%nat)); ((TAtom "L99"), ("iofclose.c", 50%nat)); ((TAtom "L100"), ("iofclose.c", 55%nat)); ((TAtom "L121"), ("iofclose.c", 55%nat)); ((TAtom "L101"), ("iofclose.c", 35%nat)); ((TAtom "iw_1.L5"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L19"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L28"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L29"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L22"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L23"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L45"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L66"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L67"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L78"), ("./libioP.h", 1000%nat)); ((TAtom "iw_1.L46"), ("./libioP.h", 1000%nat)); ((TAtom "L8"), ("iofclose.c", 65%nat)); ((TAtom "iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.join"), ("iofclose.c", 67%nat)); ((TAtom "L136"), ("iofclose.c", 70%nat)); ((TAtom "L143"), ("iofclose.c", 71%nat)); ((TAtom "L145"), ("iofclose.c", 74%nat)); ((TAtom "L169"), ("iofclose.c", 76%nat)); ((TAtom "L170"), ("iofclose.c", 76%nat)); ((TAtom "L174"), ("iofclose.c", 76%nat)); ((TAtom "L163"), ("iofclose.c", 77%nat)); ((TAtom "L195"), ("iofclose.c", 79%nat)); ((TAtom "L196"), ("iofclose.c", 79%nat)); ((TAtom "L207"), ("iofclose.c", 79%nat)); ((TAtom "L137"), ("iofclose.c", 83%nat)); ((TAtom "L218"), ("iofclose.c", 84%nat)); ((TAtom "iw_3.start"), ("./libioP.h", 971%nat)); ((TAtom "iw_3.L10"), ("./libioP.h", 971%nat)); ((TAtom "iw_3.L11"), ("./libioP.h", 971%nat)); ((TAtom "iw_3.L19"), ("./libioP.h", 971%nat)); ((TAtom "iw_3.L20"), ("./libioP.h", 971%nat)); ((TAtom "iw_3.L4"), ("./libioP.h", 978%nat)); ((TAtom "iw_3.join"), ("iofclose.c", 87%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "p"); ((TAtom "iw_1.v15"), "fp"); ((TAtom "iw_1.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v3"), "p"); ((TAtom "iw_1.v30"), "fp"); ((TAtom "iw_1.v38"), "fp"); ((TAtom "iw_1.v4"), "fp"); ((TAtom "iw_1.v42"), "fp"); ((TAtom "iw_1.v48"), "fp"); ((TAtom "iw_1.v54"), "fp"); ((TAtom "iw_1.v59"), "fp"); ((TAtom "iw_1.v61"), "__futex"); ((TAtom "iw_1.v64"), "__futex"); ((TAtom "iw_1.v68"), "__oldval"); ((TAtom "iw_1.v74"), "__oldval"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "iw_1.v86"), "__futex"); ((TAtom "iw_1.v87"), "__futex"); ((TAtom "iw_1.v88"), "__private"); ((TAtom "iw_1.v89"), "fp"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "fp"); ((TAtom "iw_3.v12"), "fp"); ((TAtom "iw_3.v21"), "fp"); ((TAtom "iw_3.v29"), "fp"); ((TAtom "iw_3.v5"), "fp"); ((TAtom "pr.1"), "status"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v102"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v107"), "status"); ((TAtom "v108"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v127"), "status"); ((TAtom "v128"), "fp"); ((TAtom "v129"), "fp"); ((TAtom "v135"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v14"), "_IO_acquire_lock_file"); ((TAtom "v146"), "fp"); ((TAtom "v154"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v158"), "cc"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "__atg3_old"); ((TAtom "v167"), "__atg3_old"); ((TAtom "v182"), "__futex"); ((TAtom "v183"), "__futex"); ((TAtom "v184"), "cc"); ((TAtom "v186"), "cc"); ((TAtom "v193"), "__futex"); ((TAtom "v197"), "__oldval"); ((TAtom "v203"), "__oldval"); ((TAtom "v215"), "__futex"); ((TAtom "v216"), "__futex"); ((TAtom "v217"), "__private"); ((TAtom "v22"), "__self"); ((TAtom "v221"), "fp"); ((TAtom "v227"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v229"), "status"); ((TAtom "v27"), "__libc_single_threaded_internal"); ((TAtom "v31"), "_IO_acquire_lock_file"); ((TAtom "v41"), "_IO_acquire_lock_file"); ((TAtom "v44"), "_IO_acquire_lock_file"); ((TAtom "v48"), "__self"); ((TAtom "v52"), "_IO_acquire_lock_file"); ((TAtom "v57"), "__self"); ((TAtom "v62"), "_IO_acquire_lock_file"); ((TAtom "v64"), "__futex"); ((TAtom "v69"), "__futex"); ((TAtom "v70"), "__atg3_old"); ((TAtom "v71"), "__atg3_old"); ((TAtom "v86"), "__futex"); ((TAtom "v87"), "__futex"); ((TAtom "v88"), "_IO_acquire_lock_file"); ((TAtom "v92"), "__self"); ((TAtom "v93"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L195"); (TAtom "iw_1.L66")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_fclose") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_fclose.

Module fn___GI__IO_puts.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("ioputs.c", 31%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("ioputs.c", 35%nat)); ((TAtom "L20"), ("ioputs.c", 36%nat)); ((TAtom "L31"), ("ioputs.c", 36%nat)); ((TAtom "L32"), ("ioputs.c", 36%nat)); ((TAtom "L25"), ("ioputs.c", 36%nat)); ((TAtom "L26"), ("ioputs.c", 36%nat)); ((TAtom "L51"), ("ioputs.c", 36%nat)); ((TAtom "L75"), ("ioputs.c", 36%nat)); ((TAtom "L76"), ("ioputs.c", 36%nat)); ((TAtom "L80"), ("ioputs.c", 36%nat)); ((TAtom "L69"), ("ioputs.c", 36%nat)); ((TAtom "L52"), ("ioputs.c", 36%nat)); ((TAtom "L109"), ("ioputs.c", 39%nat)); ((TAtom "L119"), ("ioputs.c", 39%nat)); ((TAtom "L121"), ("ioputs.c", 39%nat)); ((TAtom "L162"), ("ioputs.c", 38%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("ioputs.c", 38%nat)); ((TAtom "L163"), ("ioputs.c", 38%nat)); ((TAtom "L180"), ("ioputs.c", 38%nat)); ((TAtom "L182"), ("ioputs.c", 38%nat)); ((TAtom "L183"), ("ioputs.c", 38%nat)); ((TAtom "L184"), ("ioputs.c", 38%nat)); ((TAtom "L181"), ("ioputs.c", 38%nat)); ((TAtom "L101"), ("ioputs.c", 42%nat)); ((TAtom "L212"), ("ioputs.c", 42%nat)); ((TAtom "L103"), ("ioputs.c", 34%nat)); ((TAtom "iw_2.L5"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L19"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L28"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L29"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L22"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L23"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L45"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L66"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L67"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L78"), ("./libioP.h", 1000%nat)); ((TAtom "iw_2.L46"), ("./libioP.h", 1000%nat)); ((TAtom "L9"), ("ioputs.c", 45%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "p"); ((TAtom "iw_2.v15"), "fp"); ((TAtom "iw_2.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_2.v3"), "p"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v38"), "fp"); ((TAtom "iw_2.v4"), "fp"); ((TAtom "iw_2.v42"), "fp"); ((TAtom "iw_2.v48"), "fp"); ((TAtom "iw_2.v54"), "fp"); ((TAtom "iw_2.v59"), "fp"); ((TAtom "iw_2.v61"), "__futex"); ((TAtom "iw_2.v64"), "__futex"); ((TAtom "iw_2.v68"), "__oldval"); ((TAtom "iw_2.v74"), "__oldval"); ((TAtom "iw_2.v8"), "fp"); ((TAtom "iw_2.v86"), "__futex"); ((TAtom "iw_2.v87"), "__futex"); ((TAtom "iw_2.v88"), "__private"); ((TAtom "iw_2.v89"), "fp"); ((TAtom "pr.1"), "result"); ((TAtom "pr.2"), "result"); ((TAtom "pr.3"), "__result"); ((TAtom "pr.4"), "__result"); ((TAtom "v0"), "str"); ((TAtom "v108"), "__result"); ((TAtom "v112"), "__result"); ((TAtom "v12"), "stdout"); ((TAtom "v123"), "stdout"); ((TAtom "v128"), "stdout"); ((TAtom "v132"), "stdout"); ((TAtom "v134"), "__result"); ((TAtom "v149"), "stdout"); ((TAtom "v152"), "__result"); ((TAtom "v154"), "stdout"); ((TAtom "v155"), "__result"); ((TAtom "v156"), "__result"); ((TAtom "v157"), "__result"); ((TAtom "v16"), "_IO_acquire_lock_file"); ((TAtom "v165"), "stdout"); ((TAtom "v172"), "stdout"); ((TAtom "v173"), "str"); ((TAtom "v174"), "len"); ((TAtom "v176"), "len"); ((TAtom "v186"), "stdout"); ((TAtom "v190"), "stdout"); ((TAtom "v199"), "stdout"); ((TAtom "v202"), "stdout"); ((TAtom "v214"), "len"); ((TAtom "v217"), "len"); ((TAtom "v219"), "result"); ((TAtom "v220"), "result"); ((TAtom "v24"), "__self"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v3"), "result"); ((TAtom "v33"), "_IO_acquire_lock_file"); ((TAtom "v43"), "_IO_acquire_lock_file"); ((TAtom "v46"), "_IO_acquire_lock_file"); ((TAtom "v5"), "str"); ((TAtom "v50"), "__self"); ((TAtom "v54"), "_IO_acquire_lock_file"); ((TAtom "v59"), "__self"); ((TAtom "v6"), "len"); ((TAtom "v64"), "_IO_acquire_lock_file"); ((TAtom "v66"), "__futex"); ((TAtom "v71"), "__futex"); ((TAtom "v72"), "__atg3_old"); ((TAtom "v73"), "__atg3_old"); ((TAtom "v88"), "__futex"); ((TAtom "v89"), "__futex"); ((TAtom "v90"), "_IO_acquire_lock_file"); ((TAtom "v94"), "__self"); ((TAtom "v95"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "iw_2.L66")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_puts") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_puts.

Module fn_glibc_stdfiles__IO_stdfiles_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("stdfiles.c", 61%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("stdfiles.c", 66%nat)); ((TAtom "L2"), ("stdfiles.c", 65%nat)); ((TAtom "L3"), ("stdfiles.c", 69%nat)); ((TAtom "L5"), ("stdfiles.c", 61%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "v11"), "f"); ((TAtom "v14"), "f"); ((TAtom "v15"), "f"); ((TAtom "v17"), "f"); ((TAtom "v6"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L2")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "glibc_stdfiles#_IO_stdfiles_init") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_glibc_stdfiles__IO_stdfiles_init.

Module fn__IO_vtable_check.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("vtables.c", 507%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("vtables.c", 510%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_vtable_check") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_vtable_check.

Module fn_glibc_vtables_check_stdfiles_vtables.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("vtables.c", 518%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("vtables.c", 522%nat)); ((TAtom "L11"), ("vtables.c", 522%nat)); ((TAtom "L12"), ("vtables.c", 522%nat)); ((TAtom "L23"), ("vtables.c", 522%nat)); ((TAtom "L24"), ("vtables.c", 522%nat)); ((TAtom "L0"), ("vtables.c", 525%nat)); ((TAtom "L2"), ("vtables.c", 518%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "flag"); ((TAtom "iw_1.v2"), "flag"); ((TAtom "iw_1.v7"), "flag")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "glibc_vtables#check_stdfiles_vtables") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_glibc_vtables_check_stdfiles_vtables.

Module fn___isatty_nostatus.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/isatty_nostatus.c", 22%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/isatty_nostatus.c", 25%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v3"), "fd")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__isatty_nostatus") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___isatty_nostatus.

Module fn___GI___libc_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/write.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/write.c", 27%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "nbytes"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "buf"); ((TAtom "v8"), "nbytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_write") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_write.

Module fn___GI___write_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/write_nocancel.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/write_nocancel.c", 27%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "nbytes"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "buf"); ((TAtom "v8"), "nbytes")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___write_nocancel") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___write_nocancel.

Module fn___lseek64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/lseek64.c", 27%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/lseek64.c", 30%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "offset"); ((TAtom "v4"), "whence"); ((TAtom "v6"), "fd"); ((TAtom "v7"), "offset"); ((TAtom "v8"), "whence")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__lseek64") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___lseek64.

Module fn___GI___fstat64.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/fstat64.c", 29%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/fstat64.c", 32%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "buf"); ((TAtom "v4"), "fd"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___fstat64") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___fstat64.

Module fn___GI___close_nocancel.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/close_nocancel.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/close_nocancel.c", 27%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fd"); ((TAtom "v2"), "fd")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___close_nocancel") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___close_nocancel.

Module fn___GI__exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("../sysdeps/unix/sysv/linux/_exit.c", 26%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../sysdeps/unix/sysv/linux/_exit.c", 30%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__exit") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__exit.

Module fn___run_exit_handlers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("exit.c", 42%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("exit.c", 48%nat)); ((TAtom "L13"), ("exit.c", 48%nat)); ((TAtom "L33"), ("exit.c", 48%nat)); ((TAtom "L34"), ("exit.c", 48%nat)); ((TAtom "L38"), ("exit.c", 48%nat)); ((TAtom "L27"), ("exit.c", 48%nat)); ((TAtom "L15"), ("exit.c", 48%nat)); ((TAtom "L55"), ("exit.c", 52%nat)); ((TAtom "L57"), ("exit.c", 54%nat)); ((TAtom "L69"), ("exit.c", 54%nat)); ((TAtom "L70"), ("exit.c", 54%nat)); ((TAtom "L74"), ("exit.c", 54%nat)); ((TAtom "L88"), ("exit.c", 65%nat)); ((TAtom "L91"), ("exit.c", 71%nat)); ((TAtom "L101"), ("exit.c", 75%nat)); ((TAtom "L102"), ("exit.c", 77%nat)); ((TAtom "L130"), ("exit.c", 91%nat)); ((TAtom "L145"), ("exit.c", 96%nat)); ((TAtom "L146"), ("exit.c", 96%nat)); ((TAtom "L157"), ("exit.c", 96%nat)); ((TAtom "L152"), ("exit.c", 97%nat)); ((TAtom "L181"), ("exit.c", 98%nat)); ((TAtom "L182"), ("exit.c", 98%nat)); ((TAtom "L186"), ("exit.c", 98%nat)); ((TAtom "L196"), ("exit.c", 101%nat)); ((TAtom "L207"), ("exit.c", 105%nat)); ((TAtom "L208"), ("exit.c", 105%nat)); ((TAtom "L219"), ("exit.c", 105%nat)); ((TAtom "L214"), ("exit.c", 106%nat)); ((TAtom "L241"), ("exit.c", 107%nat)); ((TAtom "L242"), ("exit.c", 107%nat)); ((TAtom "L246"), ("exit.c", 107%nat)); ((TAtom "L256"), ("exit.c", 112%nat)); ((TAtom "L272"), ("exit.c", 118%nat)); ((TAtom "L273"), ("exit.c", 118%nat)); ((TAtom "L284"), ("exit.c", 118%nat)); ((TAtom "L279"), ("exit.c", 119%nat)); ((TAtom "L308"), ("exit.c", 120%nat)); ((TAtom "L309"), ("exit.c", 120%nat)); ((TAtom "L313"), ("exit.c", 120%nat)); ((TAtom "L325"), ("exit.c", 80%nat)); ((TAtom "L328"), ("exit.c", 80%nat)); ((TAtom "L330"), ("exit.c", 80%nat)); ((TAtom "L326"), ("exit.c", 80%nat)); ((TAtom "L332"), ("exit.c", 80%nat)); ((TAtom "L334"), ("exit.c", 80%nat)); ((TAtom "L123"), ("exit.c", 124%nat)); ((TAtom "L103"), ("exit.c", 130%nat)); ((TAtom "L350"), ("exit.c", 134%nat)); ((TAtom "L365"), ("exit.c", 137%nat)); ((TAtom "L366"), ("exit.c", 137%nat)); ((TAtom "L377"), ("exit.c", 137%nat)); ((TAtom "L372"), ("exit.c", 139%nat)); ((TAtom "L388"), ("exit.c", 140%nat)); ((TAtom "L390"), ("exit.c", 143%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v104"), "cur"); ((TAtom "v109"), "cur"); ((TAtom "v111"), "cur"); ((TAtom "v116"), "f"); ((TAtom "v119"), "__new_exitfn_called"); ((TAtom "v12"), "self"); ((TAtom "v120"), "f"); ((TAtom "v131"), "f"); ((TAtom "v133"), "onfct"); ((TAtom "v134"), "f"); ((TAtom "v137"), "arg"); ((TAtom "v138"), "onfct"); ((TAtom "v143"), "__futex"); ((TAtom "v147"), "__oldval"); ((TAtom "v153"), "__oldval"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "__futex"); ((TAtom "v167"), "__private"); ((TAtom "v168"), "onfct"); ((TAtom "v169"), "status"); ((TAtom "v170"), "arg"); ((TAtom "v177"), "__futex"); ((TAtom "v178"), "__atg3_old"); ((TAtom "v179"), "__atg3_old"); ((TAtom "v19"), "self"); ((TAtom "v194"), "__futex"); ((TAtom "v195"), "__futex"); ((TAtom "v197"), "f"); ((TAtom "v199"), "atfct"); ((TAtom "v2"), "listp"); ((TAtom "v200"), "atfct"); ((TAtom "v205"), "__futex"); ((TAtom "v209"), "__oldval"); ((TAtom "v215"), "__oldval"); ((TAtom "v227"), "__futex"); ((TAtom "v228"), "__futex"); ((TAtom "v229"), "__private"); ((TAtom "v230"), "atfct"); ((TAtom "v237"), "__futex"); ((TAtom "v238"), "__atg3_old"); ((TAtom "v239"), "__atg3_old"); ((TAtom "v254"), "__futex"); ((TAtom "v255"), "__futex"); ((TAtom "v257"), "f"); ((TAtom "v258"), "f"); ((TAtom "v260"), "cxafct"); ((TAtom "v261"), "f"); ((TAtom "v264"), "arg"); ((TAtom "v265"), "cxafct"); ((TAtom "v270"), "__futex"); ((TAtom "v274"), "__oldval"); ((TAtom "v280"), "__oldval"); ((TAtom "v29"), "__futex"); ((TAtom "v292"), "__futex"); ((TAtom "v293"), "__futex"); ((TAtom "v294"), "__private"); ((TAtom "v295"), "cxafct"); ((TAtom "v296"), "arg"); ((TAtom "v297"), "status"); ((TAtom "v30"), "__atg3_old"); ((TAtom "v304"), "__futex"); ((TAtom "v305"), "__atg3_old"); ((TAtom "v306"), "__atg3_old"); ((TAtom "v31"), "__atg3_old"); ((TAtom "v321"), "__futex"); ((TAtom "v322"), "__futex"); ((TAtom "v340"), "new_exitfn_called"); ((TAtom "v342"), "__new_exitfn_called"); ((TAtom "v347"), "listp"); ((TAtom "v348"), "cur"); ((TAtom "v353"), "listp"); ((TAtom "v358"), "cur"); ((TAtom "v363"), "__futex"); ((TAtom "v367"), "__oldval"); ((TAtom "v373"), "__oldval"); ((TAtom "v385"), "__futex"); ((TAtom "v386"), "__futex"); ((TAtom "v387"), "__private"); ((TAtom "v391"), "run_list_atexit"); ((TAtom "v393"), "status"); ((TAtom "v4"), "run_list_atexit"); ((TAtom "v46"), "__futex"); ((TAtom "v47"), "__futex"); ((TAtom "v50"), "self"); ((TAtom "v58"), "run_dtors"); ((TAtom "v6"), "run_dtors"); ((TAtom "v65"), "__futex"); ((TAtom "v66"), "__atg3_old"); ((TAtom "v67"), "__atg3_old"); ((TAtom "v82"), "__futex"); ((TAtom "v83"), "__futex"); ((TAtom "v89"), "listp"); ((TAtom "v90"), "cur"); ((TAtom "v94"), "cur"); ((TAtom "v99"), "__exit_funcs_done")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L101"); (TAtom "L145"); (TAtom "L207"); (TAtom "L272"); (TAtom "L365"); (TAtom "L88")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__run_exit_handlers") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___run_exit_handlers.

Module fn___GI_exit.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("exit.c", 147%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("exit.c", 150%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "status")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI_exit") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI_exit.

Module fn___GI___call_tls_dtors.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("cxa_thread_atexit_impl.c", 80%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("cxa_thread_atexit_impl.c", 80%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___call_tls_dtors") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___call_tls_dtors.

Module fn___GI___libc_cleanup_push_defer.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("libc-cleanup.c", 22%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("libc-cleanup.c", 25%nat)); ((TAtom "L22"), ("libc-cleanup.c", 29%nat)); ((TAtom "L35"), ("libc-cleanup.c", 39%nat)); ((TAtom "L36"), ("libc-cleanup.c", 29%nat)); ((TAtom "L15"), ("libc-cleanup.c", 29%nat)); ((TAtom "L41"), ("libc-cleanup.c", 44%nat)); ((TAtom "L42"), ("libc-cleanup.c", 44%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "pr.3"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "cancelhandling"); ((TAtom "v25"), "cancelhandling"); ((TAtom "v28"), "newval"); ((TAtom "v29"), "self"); ((TAtom "v3"), "self"); ((TAtom "v31"), "newval"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v33"), "cancelhandling"); ((TAtom "v38"), "buffer"); ((TAtom "v4"), "buffer"); ((TAtom "v43"), "cancelhandling"); ((TAtom "v47"), "self"); ((TAtom "v49"), "buffer"); ((TAtom "v6"), "self")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L22")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_cleanup_push_defer") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_cleanup_push_defer.

Module fn___GI___libc_cleanup_pop_restore.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("libc-cleanup.c", 52%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("libc-cleanup.c", 55%nat)); ((TAtom "L20"), ("libc-cleanup.c", 60%nat)); ((TAtom "L21"), ("libc-cleanup.c", 60%nat)); ((TAtom "L29"), ("libc-cleanup.c", 59%nat)); ((TAtom "L41"), ("libc-cleanup.c", 68%nat)); ((TAtom "L42"), ("libc-cleanup.c", 59%nat)); ((TAtom "iw_1.start"), ("../nptl/descr.h", 463%nat)); ((TAtom "L44"), ("libc-cleanup.c", 72%nat)); ((TAtom "iw_2.L12"), ("../sysdeps/nptl/pthreadP.h", 256%nat)); ((TAtom "iw_2.L13"), ("../sysdeps/nptl/pthreadP.h", 268%nat)); ((TAtom "iw_2.L37"), ("../sysdeps/nptl/pthreadP.h", 268%nat)); ((TAtom "iw_2.L38"), ("../sysdeps/nptl/pthreadP.h", 256%nat)); ((TAtom "iw_2.L14"), ("../sysdeps/nptl/pthreadP.h", 271%nat)); ((TAtom "L15"), ("libc-cleanup.c", 52%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v2"), "value"); ((TAtom "iw_2.pr.1"), "oldval"); ((TAtom "iw_2.pr.2"), "oldval"); ((TAtom "iw_2.v0"), "result"); ((TAtom "iw_2.v10"), "oldval"); ((TAtom "iw_2.v15"), "oldval"); ((TAtom "iw_2.v19"), "newval"); ((TAtom "iw_2.v20"), "newval"); ((TAtom "iw_2.v23"), "newval"); ((TAtom "iw_2.v27"), "oldval"); ((TAtom "iw_2.v28"), "newval"); ((TAtom "iw_2.v3"), "self"); ((TAtom "iw_2.v31"), "self"); ((TAtom "iw_2.v33"), "newval"); ((TAtom "iw_2.v34"), "oldval"); ((TAtom "iw_2.v35"), "oldval"); ((TAtom "iw_2.v4"), "self"); ((TAtom "iw_2.v40"), "self"); ((TAtom "iw_2.v6"), "result"); ((TAtom "iw_2.v8"), "self"); ((TAtom "pr.1"), "cancelhandling"); ((TAtom "pr.2"), "cancelhandling"); ((TAtom "v0"), "buffer"); ((TAtom "v10"), "self"); ((TAtom "v12"), "cancelhandling"); ((TAtom "v16"), "buffer"); ((TAtom "v22"), "cancelhandling"); ((TAtom "v3"), "self"); ((TAtom "v32"), "cancelhandling"); ((TAtom "v34"), "newval"); ((TAtom "v35"), "self"); ((TAtom "v37"), "newval"); ((TAtom "v38"), "cancelhandling"); ((TAtom "v39"), "cancelhandling"); ((TAtom "v4"), "self"); ((TAtom "v47"), "cancelhandling"); ((TAtom "v6"), "buffer")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L29"); (TAtom "iw_2.L12")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___libc_cleanup_pop_restore") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___libc_cleanup_pop_restore.

Module fn___gnu_dev_major.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("makedev.c", 28%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("makedev.c", 28%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "__dev"); ((TAtom "v11"), "__major"); ((TAtom "v12"), "__major"); ((TAtom "v3"), "__dev"); ((TAtom "v5"), "__major"); ((TAtom "v6"), "__major"); ((TAtom "v7"), "__dev")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__gnu_dev_major") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___gnu_dev_major.

Module fn___strlen.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("strlen.c", 31%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("strlen.c", 35%nat)); ((TAtom "iw_3.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "L28"), ("strlen.c", 36%nat)); ((TAtom "iw_5.start"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), ("../stdlib/stdbit.h", 193%nat)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), ("../stdlib/stdbit.h", 193%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_1.v0"), "x"); ((TAtom "iw_1.v11"), "m"); ((TAtom "iw_1.v3"), "m"); ((TAtom "iw_1.v4"), "x"); ((TAtom "iw_1.v5"), "m"); ((TAtom "iw_1.v7"), "m"); ((TAtom "iw_1.v9"), "x"); ((TAtom "iw_2.v0"), "word"); ((TAtom "iw_2.v14"), "word"); ((TAtom "iw_2.v15"), "s"); ((TAtom "iw_2.v2"), "s"); ((TAtom "iw_2.v8"), "word"); ((TAtom "iw_2.v9"), "s"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "c"); ((TAtom "iw_3.iw_1.v12"), "c"); ((TAtom "iw_3.iw_1.v18"), "c"); ((TAtom "iw_3.iw_1.v21"), "c"); ((TAtom "iw_3.iw_1.v6"), "c"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "c"); ((TAtom "iw_3.iw_2.v2"), "c"); ((TAtom "iw_3.pr.1"), "r"); ((TAtom "iw_3.v0"), "c"); ((TAtom "iw_3.v10"), "r"); ((TAtom "iw_3.v11"), "r"); ((TAtom "iw_3.v7"), "c"); ((TAtom "iw_3.v8"), "r"); ((TAtom "iw_3.v9"), "c"); ((TAtom "iw_4.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_4.iw_1.v0"), "x"); ((TAtom "iw_4.iw_1.v12"), "msb"); ((TAtom "iw_4.iw_1.v3"), "lsb"); ((TAtom "iw_4.iw_1.v5"), "msb"); ((TAtom "iw_4.iw_1.v6"), "x"); ((TAtom "iw_4.iw_1.v7"), "lsb"); ((TAtom "iw_4.iw_1.v9"), "x"); ((TAtom "iw_4.v0"), "x"); ((TAtom "iw_4.v2"), "x"); ((TAtom "iw_5.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.v0"), "x"); ((TAtom "iw_5.iw_1.v12"), "msb"); ((TAtom "iw_5.iw_1.v3"), "lsb"); ((TAtom "iw_5.iw_1.v5"), "msb"); ((TAtom "iw_5.iw_1.v6"), "x"); ((TAtom "iw_5.iw_1.v7"), "lsb"); ((TAtom "iw_5.iw_1.v9"), "x"); ((TAtom "iw_5.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_2.v0"), "x"); ((TAtom "iw_5.iw_2.v11"), "m"); ((TAtom "iw_5.iw_2.v3"), "m"); ((TAtom "iw_5.iw_2.v4"), "x"); ((TAtom "iw_5.iw_2.v5"), "m"); ((TAtom "iw_5.iw_2.v7"), "m"); ((TAtom "iw_5.iw_2.v9"), "x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.v0"), "c"); ((TAtom "iw_5.iw_3.iw_1.v12"), "c"); ((TAtom "iw_5.iw_3.iw_1.v18"), "c"); ((TAtom "iw_5.iw_3.iw_1.v21"), "c"); ((TAtom "iw_5.iw_3.iw_1.v6"), "c"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_2.v0"), "c"); ((TAtom "iw_5.iw_3.iw_2.v2"), "c"); ((TAtom "iw_5.iw_3.pr.1"), "r"); ((TAtom "iw_5.iw_3.v0"), "c"); ((TAtom "iw_5.iw_3.v10"), "r"); ((TAtom "iw_5.iw_3.v11"), "r"); ((TAtom "iw_5.iw_3.v7"), "c"); ((TAtom "iw_5.iw_3.v8"), "r"); ((TAtom "iw_5.iw_3.v9"), "c"); ((TAtom "iw_5.pr.1"), "x"); ((TAtom "iw_5.v0"), "x"); ((TAtom "iw_5.v10"), "x"); ((TAtom "iw_5.v6"), "x"); ((TAtom "iw_5.v7"), "x"); ((TAtom "iw_5.v8"), "x"); ((TAtom "iw_5.v9"), "x"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "v0"), "str"); ((TAtom "v10"), "word_ptr"); ((TAtom "v12"), "word_ptr"); ((TAtom "v13"), "word"); ((TAtom "v15"), "word"); ((TAtom "v17"), "s_int"); ((TAtom "v18"), "mask"); ((TAtom "v22"), "mask"); ((TAtom "v24"), "mask"); ((TAtom "v3"), "str"); ((TAtom "v31"), "word_ptr"); ((TAtom "v32"), "word_ptr"); ((TAtom "v33"), "word"); ((TAtom "v34"), "word"); ((TAtom "v38"), "word_ptr"); ((TAtom "v39"), "word"); ((TAtom "v4"), "s_int"); ((TAtom "v43"), "str"); ((TAtom "v6"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L28")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__strlen") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___strlen.

Module fn___GI___mempcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("mempcpy.c", 32%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("mempcpy.c", 35%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dest"); ((TAtom "v10"), "len"); ((TAtom "v2"), "src"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dest"); ((TAtom "v7"), "src"); ((TAtom "v8"), "len")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___mempcpy") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___mempcpy.

Module fn___GI_memcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("memcpy.c", 28%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("memcpy.c", 37%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dstpp"); ((TAtom "v2"), "srcpp"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dstpp"); ((TAtom "v7"), "srcpp"); ((TAtom "v8"), "len"); ((TAtom "v9"), "dstpp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI_memcpy") (code_module hi_atexit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI_memcpy.

End HiAtexitSrc.

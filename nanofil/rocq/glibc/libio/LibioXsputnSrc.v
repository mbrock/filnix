(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioXsputnCode.
Import ListNotations.
Open Scope string_scope.

Module LibioXsputnSrc.

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
  match find_direct (TAtom "_IO_new_file_xsputn") (code_module libioxsputn_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_xsputn.

End LibioXsputnSrc.

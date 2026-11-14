(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioXsputnCode.
Module LibioXsputnSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "fileops.c".

Module fn__IO_new_file_xsputn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 1273%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 1281%N)); ((TAtom "L12"), (file_1, 1282%N)); ((TAtom "L14"), (file_1, 1288%N)); ((TAtom "L24"), (file_1, 1288%N)); ((TAtom "L25"), (file_1, 1288%N)); ((TAtom "L18"), (file_1, 1290%N)); ((TAtom "L40"), (file_1, 1294%N)); ((TAtom "L50"), (file_1, 1293%N)); ((TAtom "L51"), (file_1, 1296%N)); ((TAtom "L59"), (file_1, 1298%N)); ((TAtom "L19"), (file_1, 1305%N)); ((TAtom "L73"), (file_1, 1306%N)); ((TAtom "L20"), (file_1, 1279%N)); ((TAtom "L94"), (file_1, 1311%N)); ((TAtom "L100"), (file_1, 1311%N)); ((TAtom "L101"), (file_1, 1279%N)); ((TAtom "L96"), (file_1, 1277%N)); ((TAtom "L120"), (file_1, 1321%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_1, 1321%N)); ((TAtom "L130"), (file_1, 1324%N)); ((TAtom "L145"), (file_1, 1324%N)); ((TAtom "L146"), (file_1, 1324%N)); ((TAtom "L132"), (file_1, 1327%N)); ((TAtom "L166"), (file_1, 1328%N)); ((TAtom "L168"), (file_1, 1328%N)); ((TAtom "iw_2.start"), (file_1, 484%N)); ((TAtom "iw_2.L7"), (file_1, 490%N)); ((TAtom "iw_2.L8"), (file_1, 491%N)); ((TAtom "iw_2.L17"), (file_1, 493%N)); ((TAtom "iw_2.iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_2.iw_1.join"), (file_1, 493%N)); ((TAtom "iw_2.L49"), (file_1, 497%N)); ((TAtom "iw_2.L9"), (file_1, 499%N)); ((TAtom "iw_2.iw_2.L10"), (file_0, 1049%N)); ((TAtom "iw_2.iw_2.join"), (file_1, 499%N)); ((TAtom "iw_2.L74"), (file_1, 500%N)); ((TAtom "iw_2.L75"), (file_1, 500%N)); ((TAtom "iw_2.L68"), (file_1, 501%N)); ((TAtom "iw_2.L70"), (file_1, 502%N)); ((TAtom "iw_2.L122"), (file_1, 504%N)); ((TAtom "iw_2.L123"), (file_1, 504%N)); ((TAtom "iw_2.L115"), (file_1, 504%N)); ((TAtom "iw_2.L116"), (file_1, 504%N)); ((TAtom "iw_2.L117"), (file_1, 504%N)); ((TAtom "iw_2.join"), (file_1, 1333%N)); ((TAtom "L188"), (file_1, 1335%N)); ((TAtom "L178"), (file_1, 1277%N)); ((TAtom "L198"), (file_1, 1342%N)); ((TAtom "L122"), (file_1, 1277%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.iw_1.v0"), "vtable"); ((TAtom "iw_2.iw_1.v13"), "offset"); ((TAtom "iw_2.iw_1.v18"), "vtable"); ((TAtom "iw_2.iw_1.v3"), "vtable"); ((TAtom "iw_2.iw_1.v4"), "ptr"); ((TAtom "iw_2.iw_1.v6"), "ptr"); ((TAtom "iw_2.iw_1.v9"), "offset"); ((TAtom "iw_2.iw_2.v0"), "vtable"); ((TAtom "iw_2.iw_2.v13"), "offset"); ((TAtom "iw_2.iw_2.v18"), "vtable"); ((TAtom "iw_2.iw_2.v3"), "vtable"); ((TAtom "iw_2.iw_2.v4"), "ptr"); ((TAtom "iw_2.iw_2.v6"), "ptr"); ((TAtom "iw_2.iw_2.v9"), "offset"); ((TAtom "iw_2.v0"), "fp"); ((TAtom "iw_2.v10"), "fp"); ((TAtom "iw_2.v101"), "fp"); ((TAtom "iw_2.v103"), "fp"); ((TAtom "iw_2.v106"), "fp"); ((TAtom "iw_2.v108"), "fp"); ((TAtom "iw_2.v110"), "fp"); ((TAtom "iw_2.v113"), "fp"); ((TAtom "iw_2.v118"), "fp"); ((TAtom "iw_2.v124"), "fp"); ((TAtom "iw_2.v13"), "fp"); ((TAtom "iw_2.v130"), "fp"); ((TAtom "iw_2.v133"), "fp"); ((TAtom "iw_2.v137"), "count"); ((TAtom "iw_2.v2"), "data"); ((TAtom "iw_2.v20"), "fp"); ((TAtom "iw_2.v23"), "fp"); ((TAtom "iw_2.v30"), "fp"); ((TAtom "iw_2.v36"), "fp"); ((TAtom "iw_2.v37"), "fp"); ((TAtom "iw_2.v4"), "to_do"); ((TAtom "iw_2.v40"), "fp"); ((TAtom "iw_2.v46"), "new_pos"); ((TAtom "iw_2.v50"), "new_pos"); ((TAtom "iw_2.v55"), "fp"); ((TAtom "iw_2.v57"), "new_pos"); ((TAtom "iw_2.v58"), "fp"); ((TAtom "iw_2.v64"), "fp"); ((TAtom "iw_2.v65"), "data"); ((TAtom "iw_2.v66"), "to_do"); ((TAtom "iw_2.v67"), "count"); ((TAtom "iw_2.v71"), "fp"); ((TAtom "iw_2.v76"), "count"); ((TAtom "iw_2.v80"), "fp"); ((TAtom "iw_2.v82"), "fp"); ((TAtom "iw_2.v86"), "data"); ((TAtom "iw_2.v87"), "count"); ((TAtom "iw_2.v91"), "fp"); ((TAtom "iw_2.v93"), "fp"); ((TAtom "iw_2.v96"), "fp"); ((TAtom "iw_2.v98"), "fp"); ((TAtom "pr.1"), "s"); ((TAtom "pr.10"), "count"); ((TAtom "pr.11"), "count"); ((TAtom "pr.12"), "count"); ((TAtom "pr.13"), "count"); ((TAtom "pr.14"), "p"); ((TAtom "pr.2"), "to_do"); ((TAtom "pr.3"), "to_do"); ((TAtom "pr.4"), "to_do"); ((TAtom "pr.5"), "to_do"); ((TAtom "pr.6"), "must_flush"); ((TAtom "pr.7"), "must_flush"); ((TAtom "pr.8"), "must_flush"); ((TAtom "pr.9"), "count"); ((TAtom "v0"), "f"); ((TAtom "v102"), "count"); ((TAtom "v103"), "to_do"); ((TAtom "v105"), "to_do"); ((TAtom "v106"), "f"); ((TAtom "v108"), "f"); ((TAtom "v111"), "s"); ((TAtom "v112"), "count"); ((TAtom "v114"), "s"); ((TAtom "v115"), "count"); ((TAtom "v116"), "s"); ((TAtom "v117"), "to_do"); ((TAtom "v118"), "count"); ((TAtom "v119"), "to_do"); ((TAtom "v123"), "to_do"); ((TAtom "v124"), "must_flush"); ((TAtom "v133"), "f"); ((TAtom "v139"), "f"); ((TAtom "v147"), "to_do"); ((TAtom "v15"), "n"); ((TAtom "v151"), "n"); ((TAtom "v152"), "to_do"); ((TAtom "v156"), "f"); ((TAtom "v159"), "f"); ((TAtom "v164"), "block_size"); ((TAtom "v165"), "to_do"); ((TAtom "v169"), "block_size"); ((TAtom "v171"), "to_do"); ((TAtom "v172"), "block_size"); ((TAtom "v175"), "do_write"); ((TAtom "v179"), "do_write"); ((TAtom "v181"), "f"); ((TAtom "v182"), "s"); ((TAtom "v183"), "do_write"); ((TAtom "v184"), "count"); ((TAtom "v185"), "to_do"); ((TAtom "v186"), "count"); ((TAtom "v187"), "to_do"); ((TAtom "v191"), "count"); ((TAtom "v192"), "do_write"); ((TAtom "v194"), "n"); ((TAtom "v195"), "to_do"); ((TAtom "v2"), "data"); ((TAtom "v201"), "to_do"); ((TAtom "v203"), "to_do"); ((TAtom "v204"), "f"); ((TAtom "v205"), "s"); ((TAtom "v206"), "do_write"); ((TAtom "v208"), "to_do"); ((TAtom "v21"), "f"); ((TAtom "v210"), "to_do"); ((TAtom "v211"), "n"); ((TAtom "v212"), "to_do"); ((TAtom "v26"), "f"); ((TAtom "v31"), "f"); ((TAtom "v34"), "f"); ((TAtom "v39"), "count"); ((TAtom "v4"), "n"); ((TAtom "v43"), "count"); ((TAtom "v44"), "n"); ((TAtom "v47"), "s"); ((TAtom "v48"), "n"); ((TAtom "v49"), "p"); ((TAtom "v54"), "p"); ((TAtom "v55"), "s"); ((TAtom "v62"), "p"); ((TAtom "v63"), "p"); ((TAtom "v66"), "p"); ((TAtom "v67"), "s"); ((TAtom "v7"), "data"); ((TAtom "v71"), "count"); ((TAtom "v76"), "f"); ((TAtom "v79"), "f"); ((TAtom "v85"), "f"); ((TAtom "v88"), "f"); ((TAtom "v9"), "n"); ((TAtom "v93"), "count"); ((TAtom "v97"), "count")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L50")].

End fn__IO_new_file_xsputn.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libioxsputn_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_IO_new_file_xsputn"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("_IO_new_file_xsputn", app (map fst fn__IO_new_file_xsputn.block_src) fn__IO_new_file_xsputn.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioXsputnSrc.

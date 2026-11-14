(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioDoWriteCode.
Import ListNotations.
Open Scope string_scope.

Module LibioDoWriteSrc.

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
  match find_direct (TAtom "_IO_new_do_write") (code_module libiodowrite_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_do_write.

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
  match find_direct (TAtom "_IO_new_file_overflow") (code_module libiodowrite_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_overflow.

End LibioDoWriteSrc.

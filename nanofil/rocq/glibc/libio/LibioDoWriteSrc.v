(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioDoWriteCode.
Module LibioDoWriteSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "fileops.c".

Module fn__IO_new_do_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 472%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 475%N)); ((TAtom "iw_1.start"), (file_1, 484%N)); ((TAtom "iw_1.L7"), (file_1, 490%N)); ((TAtom "iw_1.L8"), (file_1, 491%N)); ((TAtom "iw_1.L17"), (file_1, 493%N)); ((TAtom "iw_1.iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.iw_1.join"), (file_1, 493%N)); ((TAtom "iw_1.L49"), (file_1, 497%N)); ((TAtom "iw_1.L9"), (file_1, 499%N)); ((TAtom "iw_1.iw_2.L10"), (file_0, 1049%N)); ((TAtom "iw_1.iw_2.join"), (file_1, 499%N)); ((TAtom "iw_1.L74"), (file_1, 500%N)); ((TAtom "iw_1.L75"), (file_1, 500%N)); ((TAtom "iw_1.L68"), (file_1, 501%N)); ((TAtom "iw_1.L70"), (file_1, 502%N)); ((TAtom "iw_1.L122"), (file_1, 504%N)); ((TAtom "iw_1.L123"), (file_1, 504%N)); ((TAtom "iw_1.L115"), (file_1, 504%N)); ((TAtom "iw_1.L116"), (file_1, 504%N)); ((TAtom "iw_1.L117"), (file_1, 504%N)); ((TAtom "iw_1.join"), (file_1, 475%N)); ((TAtom "L12"), (file_1, 475%N)); ((TAtom "L7"), (file_1, 475%N)); ((TAtom "L8"), (file_1, 475%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "vtable"); ((TAtom "iw_1.iw_1.v13"), "offset"); ((TAtom "iw_1.iw_1.v18"), "vtable"); ((TAtom "iw_1.iw_1.v3"), "vtable"); ((TAtom "iw_1.iw_1.v4"), "ptr"); ((TAtom "iw_1.iw_1.v6"), "ptr"); ((TAtom "iw_1.iw_1.v9"), "offset"); ((TAtom "iw_1.iw_2.v0"), "vtable"); ((TAtom "iw_1.iw_2.v13"), "offset"); ((TAtom "iw_1.iw_2.v18"), "vtable"); ((TAtom "iw_1.iw_2.v3"), "vtable"); ((TAtom "iw_1.iw_2.v4"), "ptr"); ((TAtom "iw_1.iw_2.v6"), "ptr"); ((TAtom "iw_1.iw_2.v9"), "offset"); ((TAtom "iw_1.v0"), "fp"); ((TAtom "iw_1.v10"), "fp"); ((TAtom "iw_1.v101"), "fp"); ((TAtom "iw_1.v103"), "fp"); ((TAtom "iw_1.v106"), "fp"); ((TAtom "iw_1.v108"), "fp"); ((TAtom "iw_1.v110"), "fp"); ((TAtom "iw_1.v113"), "fp"); ((TAtom "iw_1.v118"), "fp"); ((TAtom "iw_1.v124"), "fp"); ((TAtom "iw_1.v13"), "fp"); ((TAtom "iw_1.v130"), "fp"); ((TAtom "iw_1.v133"), "fp"); ((TAtom "iw_1.v137"), "count"); ((TAtom "iw_1.v2"), "data"); ((TAtom "iw_1.v20"), "fp"); ((TAtom "iw_1.v23"), "fp"); ((TAtom "iw_1.v30"), "fp"); ((TAtom "iw_1.v36"), "fp"); ((TAtom "iw_1.v37"), "fp"); ((TAtom "iw_1.v4"), "to_do"); ((TAtom "iw_1.v40"), "fp"); ((TAtom "iw_1.v46"), "new_pos"); ((TAtom "iw_1.v50"), "new_pos"); ((TAtom "iw_1.v55"), "fp"); ((TAtom "iw_1.v57"), "new_pos"); ((TAtom "iw_1.v58"), "fp"); ((TAtom "iw_1.v64"), "fp"); ((TAtom "iw_1.v65"), "data"); ((TAtom "iw_1.v66"), "to_do"); ((TAtom "iw_1.v67"), "count"); ((TAtom "iw_1.v71"), "fp"); ((TAtom "iw_1.v76"), "count"); ((TAtom "iw_1.v80"), "fp"); ((TAtom "iw_1.v82"), "fp"); ((TAtom "iw_1.v86"), "data"); ((TAtom "iw_1.v87"), "count"); ((TAtom "iw_1.v91"), "fp"); ((TAtom "iw_1.v93"), "fp"); ((TAtom "iw_1.v96"), "fp"); ((TAtom "iw_1.v98"), "fp"); ((TAtom "v0"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v14"), "data"); ((TAtom "v15"), "to_do"); ((TAtom "v17"), "to_do"); ((TAtom "v2"), "data"); ((TAtom "v4"), "to_do"); ((TAtom "v9"), "to_do")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_new_do_write.

Module fn__IO_new_file_overflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 780%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 783%N)); ((TAtom "L4"), (file_1, 785%N)); ((TAtom "L6"), (file_1, 790%N)); ((TAtom "L23"), (file_1, 790%N)); ((TAtom "L24"), (file_1, 790%N)); ((TAtom "L16"), (file_1, 793%N)); ((TAtom "L33"), (file_1, 795%N)); ((TAtom "L35"), (file_1, 805%N)); ((TAtom "L58"), (file_1, 807%N)); ((TAtom "L81"), (file_1, 809%N)); ((TAtom "L82"), (file_1, 809%N)); ((TAtom "L60"), (file_1, 814%N)); ((TAtom "L111"), (file_1, 815%N)); ((TAtom "L113"), (file_1, 816%N)); ((TAtom "L162"), (file_1, 822%N)); ((TAtom "L163"), (file_1, 822%N)); ((TAtom "L155"), (file_1, 823%N)); ((TAtom "L18"), (file_1, 825%N)); ((TAtom "L175"), (file_1, 826%N)); ((TAtom "L177"), (file_1, 828%N)); ((TAtom "L196"), (file_1, 829%N)); ((TAtom "L211"), (file_1, 829%N)); ((TAtom "L212"), (file_1, 829%N)); ((TAtom "L213"), (file_1, 829%N)); ((TAtom "L208"), (file_1, 830%N)); ((TAtom "L198"), (file_1, 831%N)); ((TAtom "L270"), (file_1, 832%N)); ((TAtom "L275"), (file_1, 832%N)); ((TAtom "L271"), (file_1, 832%N)); ((TAtom "L264"), (file_1, 834%N)); ((TAtom "L283"), (file_1, 836%N)); ((TAtom "L266"), (file_1, 837%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v10"), "f"); ((TAtom "v106"), "f"); ((TAtom "v108"), "f"); ((TAtom "v114"), "f"); ((TAtom "v117"), "f"); ((TAtom "v123"), "f"); ((TAtom "v125"), "f"); ((TAtom "v127"), "f"); ((TAtom "v130"), "f"); ((TAtom "v132"), "f"); ((TAtom "v135"), "f"); ((TAtom "v137"), "f"); ((TAtom "v140"), "f"); ((TAtom "v142"), "f"); ((TAtom "v145"), "f"); ((TAtom "v147"), "f"); ((TAtom "v149"), "f"); ((TAtom "v152"), "f"); ((TAtom "v158"), "f"); ((TAtom "v164"), "f"); ((TAtom "v170"), "f"); ((TAtom "v172"), "f"); ((TAtom "v178"), "ch"); ((TAtom "v181"), "f"); ((TAtom "v182"), "f"); ((TAtom "v185"), "f"); ((TAtom "v188"), "f"); ((TAtom "v19"), "f"); ((TAtom "v199"), "f"); ((TAtom "v2"), "ch"); ((TAtom "v202"), "f"); ((TAtom "v214"), "f"); ((TAtom "v218"), "f"); ((TAtom "v219"), "f"); ((TAtom "v222"), "f"); ((TAtom "v225"), "f"); ((TAtom "v232"), "f"); ((TAtom "v233"), "f"); ((TAtom "v238"), "f"); ((TAtom "v243"), "f"); ((TAtom "v25"), "f"); ((TAtom "v258"), "f"); ((TAtom "v262"), "ch"); ((TAtom "v267"), "f"); ((TAtom "v272"), "f"); ((TAtom "v277"), "ch"); ((TAtom "v286"), "f"); ((TAtom "v287"), "f"); ((TAtom "v290"), "f"); ((TAtom "v293"), "f"); ((TAtom "v304"), "ch"); ((TAtom "v36"), "f"); ((TAtom "v42"), "f"); ((TAtom "v43"), "f"); ((TAtom "v45"), "f"); ((TAtom "v48"), "f"); ((TAtom "v50"), "f"); ((TAtom "v53"), "f"); ((TAtom "v55"), "f"); ((TAtom "v61"), "f"); ((TAtom "v67"), "f"); ((TAtom "v7"), "f"); ((TAtom "v70"), "f"); ((TAtom "v75"), "nbackup"); ((TAtom "v76"), "f"); ((TAtom "v77"), "f"); ((TAtom "v83"), "nbackup"); ((TAtom "v84"), "f"); ((TAtom "v87"), "f"); ((TAtom "v94"), "nbackup"); ((TAtom "v95"), "f"); ((TAtom "v98"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_new_file_overflow.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiodowrite_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_IO_new_do_write"; "_IO_new_file_overflow"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("_IO_new_do_write", app (map fst fn__IO_new_do_write.block_src) fn__IO_new_do_write.loop_heads); ("_IO_new_file_overflow", app (map fst fn__IO_new_file_overflow.block_src) fn__IO_new_file_overflow.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioDoWriteSrc.

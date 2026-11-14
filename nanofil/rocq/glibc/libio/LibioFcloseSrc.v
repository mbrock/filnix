(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioFcloseCode.
Module LibioFcloseSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "iofclose.c".

Module fn__IO_new_fclose.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 47%N)); ((TAtom "L18"), (file_1, 47%N)); ((TAtom "L29"), (file_1, 47%N)); ((TAtom "L30"), (file_1, 47%N)); ((TAtom "L23"), (file_1, 47%N)); ((TAtom "L24"), (file_1, 47%N)); ((TAtom "L49"), (file_1, 47%N)); ((TAtom "L73"), (file_1, 47%N)); ((TAtom "L74"), (file_1, 47%N)); ((TAtom "L78"), (file_1, 47%N)); ((TAtom "L67"), (file_1, 47%N)); ((TAtom "L50"), (file_1, 47%N)); ((TAtom "L13"), (file_1, 48%N)); ((TAtom "L99"), (file_1, 50%N)); ((TAtom "L100"), (file_1, 55%N)); ((TAtom "L121"), (file_1, 55%N)); ((TAtom "L101"), (file_1, 35%N)); ((TAtom "iw_1.L5"), (file_0, 1000%N)); ((TAtom "iw_1.L19"), (file_0, 1000%N)); ((TAtom "iw_1.L28"), (file_0, 1000%N)); ((TAtom "iw_1.L29"), (file_0, 1000%N)); ((TAtom "iw_1.L22"), (file_0, 1000%N)); ((TAtom "iw_1.L23"), (file_0, 1000%N)); ((TAtom "iw_1.L45"), (file_0, 1000%N)); ((TAtom "iw_1.L66"), (file_0, 1000%N)); ((TAtom "iw_1.L67"), (file_0, 1000%N)); ((TAtom "iw_1.L78"), (file_0, 1000%N)); ((TAtom "iw_1.L46"), (file_0, 1000%N)); ((TAtom "L8"), (file_1, 65%N)); ((TAtom "iw_2.L10"), (file_0, 1049%N)); ((TAtom "iw_2.join"), (file_1, 67%N)); ((TAtom "L136"), (file_1, 70%N)); ((TAtom "L143"), (file_1, 71%N)); ((TAtom "L145"), (file_1, 74%N)); ((TAtom "L169"), (file_1, 76%N)); ((TAtom "L170"), (file_1, 76%N)); ((TAtom "L174"), (file_1, 76%N)); ((TAtom "L163"), (file_1, 77%N)); ((TAtom "L195"), (file_1, 79%N)); ((TAtom "L196"), (file_1, 79%N)); ((TAtom "L207"), (file_1, 79%N)); ((TAtom "L137"), (file_1, 83%N)); ((TAtom "L218"), (file_1, 84%N)); ((TAtom "iw_3.start"), (file_0, 971%N)); ((TAtom "iw_3.L10"), (file_0, 971%N)); ((TAtom "iw_3.L11"), (file_0, 971%N)); ((TAtom "iw_3.L19"), (file_0, 971%N)); ((TAtom "iw_3.L20"), (file_0, 971%N)); ((TAtom "iw_3.L4"), (file_0, 978%N)); ((TAtom "iw_3.join"), (file_1, 87%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "p"); ((TAtom "iw_1.v15"), "fp"); ((TAtom "iw_1.v26"), "__libc_single_threaded_internal"); ((TAtom "iw_1.v3"), "p"); ((TAtom "iw_1.v30"), "fp"); ((TAtom "iw_1.v38"), "fp"); ((TAtom "iw_1.v4"), "fp"); ((TAtom "iw_1.v42"), "fp"); ((TAtom "iw_1.v48"), "fp"); ((TAtom "iw_1.v54"), "fp"); ((TAtom "iw_1.v59"), "fp"); ((TAtom "iw_1.v61"), "__futex"); ((TAtom "iw_1.v64"), "__futex"); ((TAtom "iw_1.v68"), "__oldval"); ((TAtom "iw_1.v74"), "__oldval"); ((TAtom "iw_1.v8"), "fp"); ((TAtom "iw_1.v86"), "__futex"); ((TAtom "iw_1.v87"), "__futex"); ((TAtom "iw_1.v88"), "__private"); ((TAtom "iw_1.v89"), "fp"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "fp"); ((TAtom "iw_3.v12"), "fp"); ((TAtom "iw_3.v21"), "fp"); ((TAtom "iw_3.v29"), "fp"); ((TAtom "iw_3.v5"), "fp"); ((TAtom "pr.1"), "status"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v102"), "fp"); ((TAtom "v105"), "fp"); ((TAtom "v107"), "status"); ((TAtom "v108"), "fp"); ((TAtom "v123"), "fp"); ((TAtom "v127"), "status"); ((TAtom "v128"), "fp"); ((TAtom "v129"), "fp"); ((TAtom "v135"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v14"), "_IO_acquire_lock_file"); ((TAtom "v146"), "fp"); ((TAtom "v154"), "fp"); ((TAtom "v156"), "fp"); ((TAtom "v158"), "cc"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "__atg3_old"); ((TAtom "v167"), "__atg3_old"); ((TAtom "v182"), "__futex"); ((TAtom "v183"), "__futex"); ((TAtom "v184"), "cc"); ((TAtom "v186"), "cc"); ((TAtom "v193"), "__futex"); ((TAtom "v197"), "__oldval"); ((TAtom "v203"), "__oldval"); ((TAtom "v215"), "__futex"); ((TAtom "v216"), "__futex"); ((TAtom "v217"), "__private"); ((TAtom "v22"), "__self"); ((TAtom "v221"), "fp"); ((TAtom "v227"), "fp"); ((TAtom "v228"), "fp"); ((TAtom "v229"), "status"); ((TAtom "v27"), "__libc_single_threaded_internal"); ((TAtom "v31"), "_IO_acquire_lock_file"); ((TAtom "v41"), "_IO_acquire_lock_file"); ((TAtom "v44"), "_IO_acquire_lock_file"); ((TAtom "v48"), "__self"); ((TAtom "v52"), "_IO_acquire_lock_file"); ((TAtom "v57"), "__self"); ((TAtom "v62"), "_IO_acquire_lock_file"); ((TAtom "v64"), "__futex"); ((TAtom "v69"), "__futex"); ((TAtom "v70"), "__atg3_old"); ((TAtom "v71"), "__atg3_old"); ((TAtom "v86"), "__futex"); ((TAtom "v87"), "__futex"); ((TAtom "v88"), "_IO_acquire_lock_file"); ((TAtom "v92"), "__self"); ((TAtom "v93"), "_IO_acquire_lock_file")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L195"); (TAtom "iw_1.L66")].

End fn__IO_new_fclose.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiofclose_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_IO_new_fclose"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("_IO_new_fclose", app (map fst fn__IO_new_fclose.block_src) fn__IO_new_fclose.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioFcloseSrc.

(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioFcloseCode.
Import ListNotations.
Open Scope string_scope.

Module LibioFcloseSrc.

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
  match find_direct (TAtom "_IO_new_fclose") (code_module libiofclose_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_fclose.

End LibioFcloseSrc.

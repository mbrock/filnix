(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude PrintfBufferFileCode.
Import ListNotations.
Open Scope string_scope.

Module PrintfBufferFileSrc.

Module fn___printf_buffer_to_file_switch.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("printf_buffer_to_file.c", 27%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("printf_buffer_to_file.c", 30%nat)); ((TAtom "L2"), ("printf_buffer_to_file.c", 34%nat)); ((TAtom "L3"), ("printf_buffer_to_file.c", 40%nat)); ((TAtom "L4"), ("printf_buffer_to_file.c", 44%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v18"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v25"), "buf"); ((TAtom "v27"), "buf"); ((TAtom "v32"), "buf"); ((TAtom "v34"), "buf"); ((TAtom "v36"), "buf"); ((TAtom "v38"), "buf"); ((TAtom "v44"), "buf"); ((TAtom "v45"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__printf_buffer_to_file_switch") (code_module printf_buffer_file_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___printf_buffer_to_file_switch.

Module fn___printf_buffer_flush_to_file.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("printf_buffer_to_file.c", 47%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("printf_buffer_to_file.c", 51%nat)); ((TAtom "L14"), ("printf_buffer_to_file.c", 58%nat)); ((TAtom "iw_1.L10"), ("../libio/libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("printf_buffer_to_file.c", 59%nat)); ((TAtom "iw_2.start"), ("../include/printf_buffer.h", 107%nat)); ((TAtom "L40"), ("printf_buffer_to_file.c", 65%nat)); ((TAtom "L15"), ("printf_buffer_to_file.c", 68%nat)); ((TAtom "L62"), ("printf_buffer_to_file.c", 72%nat)); ((TAtom "L74"), ("printf_buffer_to_file.c", 74%nat)); ((TAtom "iw_3.start"), ("../include/printf_buffer.h", 107%nat)); ((TAtom "L88"), ("printf_buffer_to_file.c", 79%nat)); ((TAtom "L76"), ("printf_buffer_to_file.c", 82%nat)); ((TAtom "L16"), ("printf_buffer_to_file.c", 86%nat)); ((TAtom "L104"), ("printf_buffer_to_file.c", 86%nat)); ((TAtom "L105"), ("printf_buffer_to_file.c", 89%nat)); ((TAtom "L127"), ("printf_buffer_to_file.c", 98%nat)); ((TAtom "L129"), ("printf_buffer_to_file.c", 103%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "buf"); ((TAtom "iw_2.v2"), "buf"); ((TAtom "iw_3.v0"), "buf"); ((TAtom "iw_3.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v101"), "buf"); ((TAtom "v106"), "buf"); ((TAtom "v109"), "buf"); ((TAtom "v120"), "buf"); ((TAtom "v124"), "buf"); ((TAtom "v130"), "buf"); ((TAtom "v133"), "buf"); ((TAtom "v139"), "buf"); ((TAtom "v141"), "buf"); ((TAtom "v143"), "buf"); ((TAtom "v145"), "buf"); ((TAtom "v148"), "buf"); ((TAtom "v149"), "buf"); ((TAtom "v17"), "buf"); ((TAtom "v2"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v30"), "buf"); ((TAtom "v33"), "buf"); ((TAtom "v37"), "count"); ((TAtom "v41"), "buf"); ((TAtom "v49"), "buf"); ((TAtom "v5"), "buf"); ((TAtom "v52"), "buf"); ((TAtom "v54"), "count"); ((TAtom "v56"), "count"); ((TAtom "v58"), "buf"); ((TAtom "v60"), "buf"); ((TAtom "v65"), "buf"); ((TAtom "v68"), "buf"); ((TAtom "v77"), "buf"); ((TAtom "v8"), "buf"); ((TAtom "v80"), "buf"); ((TAtom "v89"), "buf"); ((TAtom "v92"), "buf"); ((TAtom "v99"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__printf_buffer_flush_to_file") (code_module printf_buffer_file_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___printf_buffer_flush_to_file.

Module fn___printf_buffer_to_file_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("printf_buffer_to_file.c", 106%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("printf_buffer_to_file.c", 109%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "buf"); ((TAtom "iw_1.iw_1.v10"), "buf"); ((TAtom "iw_1.iw_1.v12"), "base"); ((TAtom "iw_1.iw_1.v13"), "buf"); ((TAtom "iw_1.iw_1.v15"), "end"); ((TAtom "iw_1.iw_1.v16"), "buf"); ((TAtom "iw_1.iw_1.v18"), "buf"); ((TAtom "iw_1.iw_1.v2"), "base"); ((TAtom "iw_1.iw_1.v20"), "mode"); ((TAtom "iw_1.iw_1.v4"), "end"); ((TAtom "iw_1.iw_1.v6"), "mode"); ((TAtom "iw_1.iw_1.v8"), "buf"); ((TAtom "iw_1.iw_1.v9"), "base"); ((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v10"), "base"); ((TAtom "iw_1.v11"), "len"); ((TAtom "iw_1.v13"), "mode"); ((TAtom "iw_1.v2"), "base"); ((TAtom "iw_1.v4"), "len"); ((TAtom "iw_1.v6"), "mode"); ((TAtom "iw_1.v8"), "buf"); ((TAtom "iw_1.v9"), "base"); ((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v12"), "fp"); ((TAtom "v13"), "buf"); ((TAtom "v2"), "fp"); ((TAtom "v4"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__printf_buffer_to_file_init") (code_module printf_buffer_file_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___printf_buffer_to_file_init.

Module fn___printf_buffer_to_file_done.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("printf_buffer_to_file.c", 115%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../include/printf_buffer.h", 115%nat)); ((TAtom "L2"), ("printf_buffer_to_file.c", 119%nat)); ((TAtom "L4"), ("printf_buffer_to_file.c", 120%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v11"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__printf_buffer_to_file_done") (code_module printf_buffer_file_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___printf_buffer_to_file_done.

End PrintfBufferFileSrc.

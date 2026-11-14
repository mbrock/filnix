(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import PrintfBufferFileCode.
Module PrintfBufferFileSrc.

Definition file_0 : string := "../include/printf_buffer.h".

Definition file_1 : string := "../libio/libioP.h".

Definition file_2 : string := "printf_buffer_to_file.c".

Module fn___printf_buffer_to_file_switch.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 30%N)); ((TAtom "L2"), (file_2, 34%N)); ((TAtom "L3"), (file_2, 40%N)); ((TAtom "L4"), (file_2, 44%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v18"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v25"), "buf"); ((TAtom "v27"), "buf"); ((TAtom "v32"), "buf"); ((TAtom "v34"), "buf"); ((TAtom "v36"), "buf"); ((TAtom "v38"), "buf"); ((TAtom "v44"), "buf"); ((TAtom "v45"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___printf_buffer_to_file_switch.

Module fn___printf_buffer_flush_to_file.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 47%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 51%N)); ((TAtom "L14"), (file_2, 58%N)); ((TAtom "iw_1.L10"), (file_1, 1049%N)); ((TAtom "iw_1.join"), (file_2, 59%N)); ((TAtom "iw_2.start"), (file_0, 107%N)); ((TAtom "L40"), (file_2, 65%N)); ((TAtom "L15"), (file_2, 68%N)); ((TAtom "L62"), (file_2, 72%N)); ((TAtom "L74"), (file_2, 74%N)); ((TAtom "iw_3.start"), (file_0, 107%N)); ((TAtom "L88"), (file_2, 79%N)); ((TAtom "L76"), (file_2, 82%N)); ((TAtom "L16"), (file_2, 86%N)); ((TAtom "L104"), (file_2, 86%N)); ((TAtom "L105"), (file_2, 89%N)); ((TAtom "L127"), (file_2, 98%N)); ((TAtom "L129"), (file_2, 103%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "buf"); ((TAtom "iw_2.v2"), "buf"); ((TAtom "iw_3.v0"), "buf"); ((TAtom "iw_3.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v101"), "buf"); ((TAtom "v106"), "buf"); ((TAtom "v109"), "buf"); ((TAtom "v120"), "buf"); ((TAtom "v124"), "buf"); ((TAtom "v130"), "buf"); ((TAtom "v133"), "buf"); ((TAtom "v139"), "buf"); ((TAtom "v141"), "buf"); ((TAtom "v143"), "buf"); ((TAtom "v145"), "buf"); ((TAtom "v148"), "buf"); ((TAtom "v149"), "buf"); ((TAtom "v17"), "buf"); ((TAtom "v2"), "buf"); ((TAtom "v20"), "buf"); ((TAtom "v30"), "buf"); ((TAtom "v33"), "buf"); ((TAtom "v37"), "count"); ((TAtom "v41"), "buf"); ((TAtom "v49"), "buf"); ((TAtom "v5"), "buf"); ((TAtom "v52"), "buf"); ((TAtom "v54"), "count"); ((TAtom "v56"), "count"); ((TAtom "v58"), "buf"); ((TAtom "v60"), "buf"); ((TAtom "v65"), "buf"); ((TAtom "v68"), "buf"); ((TAtom "v77"), "buf"); ((TAtom "v8"), "buf"); ((TAtom "v80"), "buf"); ((TAtom "v89"), "buf"); ((TAtom "v92"), "buf"); ((TAtom "v99"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___printf_buffer_flush_to_file.

Module fn___printf_buffer_to_file_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 106%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 109%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "buf"); ((TAtom "iw_1.iw_1.v10"), "buf"); ((TAtom "iw_1.iw_1.v12"), "base"); ((TAtom "iw_1.iw_1.v13"), "buf"); ((TAtom "iw_1.iw_1.v15"), "end"); ((TAtom "iw_1.iw_1.v16"), "buf"); ((TAtom "iw_1.iw_1.v18"), "buf"); ((TAtom "iw_1.iw_1.v2"), "base"); ((TAtom "iw_1.iw_1.v20"), "mode"); ((TAtom "iw_1.iw_1.v4"), "end"); ((TAtom "iw_1.iw_1.v6"), "mode"); ((TAtom "iw_1.iw_1.v8"), "buf"); ((TAtom "iw_1.iw_1.v9"), "base"); ((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v10"), "base"); ((TAtom "iw_1.v11"), "len"); ((TAtom "iw_1.v13"), "mode"); ((TAtom "iw_1.v2"), "base"); ((TAtom "iw_1.v4"), "len"); ((TAtom "iw_1.v6"), "mode"); ((TAtom "iw_1.v8"), "buf"); ((TAtom "iw_1.v9"), "base"); ((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v12"), "fp"); ((TAtom "v13"), "buf"); ((TAtom "v2"), "fp"); ((TAtom "v4"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___printf_buffer_to_file_init.

Module fn___printf_buffer_to_file_done.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 115%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L2"), (file_2, 119%N)); ((TAtom "L4"), (file_2, 120%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v10"), "buf"); ((TAtom "v11"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___printf_buffer_to_file_done.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) printf_buffer_file_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__printf_buffer_to_file_switch"; "__printf_buffer_flush_to_file"; "__printf_buffer_to_file_init"; "__printf_buffer_to_file_done"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__printf_buffer_to_file_switch", app (map fst fn___printf_buffer_to_file_switch.block_src) fn___printf_buffer_to_file_switch.loop_heads); ("__printf_buffer_flush_to_file", app (map fst fn___printf_buffer_flush_to_file.block_src) fn___printf_buffer_flush_to_file.loop_heads); ("__printf_buffer_to_file_init", app (map fst fn___printf_buffer_to_file_init.block_src) fn___printf_buffer_to_file_init.loop_heads); ("__printf_buffer_to_file_done", app (map fst fn___printf_buffer_to_file_done.block_src) fn___printf_buffer_to_file_done.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfBufferFileSrc.

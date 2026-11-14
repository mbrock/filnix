(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import PrintfBufferIoCode.
Module PrintfBufferIoSrc.

Definition file_0 : string := "../include/printf_buffer.h".

Definition file_1 : string := "./Xprintf_buffer_flush.c".

Definition file_2 : string := "./Xprintf_buffer_write.c".

Definition file_3 : string := "printf_buffer_flush.c".

Module fn___printf_buffer_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 24%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L6"), (file_2, 29%N)); ((TAtom "L15"), (file_2, 24%N)); ((TAtom "L16"), (file_2, 33%N)); ((TAtom "L32"), (file_2, 33%N)); ((TAtom "L33"), (file_2, 33%N)); ((TAtom "L20"), (file_2, 34%N)); ((TAtom "L22"), (file_2, 35%N)); ((TAtom "L42"), (file_2, 35%N)); ((TAtom "L43"), (file_2, 36%N)); ((TAtom "L67"), (file_2, 37%N)); ((TAtom "L68"), (file_2, 36%N)); ((TAtom "L17"), (file_2, 24%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "pr.1"), "s"); ((TAtom "pr.2"), "count"); ((TAtom "pr.3"), "to_copy"); ((TAtom "v0"), "buf"); ((TAtom "v18"), "count"); ((TAtom "v2"), "s"); ((TAtom "v23"), "buf"); ((TAtom "v26"), "buf"); ((TAtom "v34"), "buf"); ((TAtom "v4"), "count"); ((TAtom "v44"), "buf"); ((TAtom "v47"), "buf"); ((TAtom "v57"), "buf"); ((TAtom "v60"), "buf"); ((TAtom "v65"), "to_copy"); ((TAtom "v69"), "to_copy"); ((TAtom "v70"), "count"); ((TAtom "v72"), "count"); ((TAtom "v73"), "buf"); ((TAtom "v76"), "s"); ((TAtom "v77"), "to_copy"); ((TAtom "v79"), "buf"); ((TAtom "v82"), "to_copy"); ((TAtom "v84"), "s"); ((TAtom "v85"), "to_copy"); ((TAtom "v86"), "s"); ((TAtom "v87"), "count"); ((TAtom "v88"), "to_copy"); ((TAtom "v89"), "count"); ((TAtom "v9"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L15")].

End fn___printf_buffer_write.

Module fn___printf_buffer_flush.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 59%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L2"), (file_1, 63%N)); ((TAtom "iw_2.start"), (file_3, 41%N)); ((TAtom "iw_2.L9"), (file_3, 47%N)); ((TAtom "iw_2.L11"), (file_3, 50%N)); ((TAtom "iw_2.L12"), (file_3, 53%N)); ((TAtom "iw_2.L14"), (file_3, 56%N)); ((TAtom "iw_2.L16"), (file_3, 59%N)); ((TAtom "iw_2.L18"), (file_3, 62%N)); ((TAtom "iw_2.L21"), (file_3, 66%N)); ((TAtom "iw_2.L23"), (file_3, 69%N)); ((TAtom "iw_2.L25"), (file_3, 73%N)); ((TAtom "iw_2.L27"), (file_3, 77%N)); ((TAtom "iw_2.L31"), (file_3, 41%N)); ((TAtom "iw_2.L34"), (file_3, 41%N)); ((TAtom "iw_2.L37"), (file_3, 41%N)); ((TAtom "iw_2.L39"), (file_3, 41%N)); ((TAtom "iw_2.L35"), (file_3, 41%N)); ((TAtom "iw_2.L43"), (file_3, 41%N)); ((TAtom "iw_2.L45"), (file_3, 41%N)); ((TAtom "iw_2.L32"), (file_3, 41%N)); ((TAtom "iw_2.L49"), (file_3, 41%N)); ((TAtom "iw_2.L52"), (file_3, 41%N)); ((TAtom "iw_2.L54"), (file_3, 41%N)); ((TAtom "iw_2.L50"), (file_3, 41%N)); ((TAtom "iw_2.L58"), (file_3, 41%N)); ((TAtom "iw_2.L60"), (file_3, 41%N)); ((TAtom "iw_2.L6"), (file_3, 80%N)); ((TAtom "iw_3.start"), (file_0, 115%N)); ((TAtom "L13"), (file_1, 67%N)); ((TAtom "L15"), (file_1, 70%N)); ((TAtom "L22"), (file_1, 70%N)); ((TAtom "L23"), (file_1, 71%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "iw_2.iw_1.v0"), "buf"); ((TAtom "iw_2.iw_1.v2"), "buf"); ((TAtom "iw_2.v0"), "buf"); ((TAtom "iw_2.v10"), "buf"); ((TAtom "iw_2.v13"), "buf"); ((TAtom "iw_2.v15"), "buf"); ((TAtom "iw_2.v17"), "buf"); ((TAtom "iw_2.v2"), "buf"); ((TAtom "iw_2.v20"), "buf"); ((TAtom "iw_2.v22"), "buf"); ((TAtom "iw_2.v24"), "buf"); ((TAtom "iw_2.v26"), "buf"); ((TAtom "iw_2.v28"), "buf"); ((TAtom "iw_3.v0"), "buf"); ((TAtom "iw_3.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v12"), "buf"); ((TAtom "v16"), "buf"); ((TAtom "v24"), "buf"); ((TAtom "v27"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___printf_buffer_flush.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) printf_buffer_io_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__printf_buffer_write"; "__printf_buffer_flush"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__printf_buffer_write", app (map fst fn___printf_buffer_write.block_src) fn___printf_buffer_write.loop_heads); ("__printf_buffer_flush", app (map fst fn___printf_buffer_flush.block_src) fn___printf_buffer_flush.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfBufferIoSrc.

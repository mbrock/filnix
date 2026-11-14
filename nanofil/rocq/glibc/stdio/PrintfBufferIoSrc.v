(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude PrintfBufferIoCode.
Import ListNotations.
Open Scope string_scope.

Module PrintfBufferIoSrc.

Module fn___printf_buffer_write.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("./Xprintf_buffer_write.c", 24%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../include/printf_buffer.h", 115%nat)); ((TAtom "L6"), ("./Xprintf_buffer_write.c", 29%nat)); ((TAtom "L15"), ("./Xprintf_buffer_write.c", 24%nat)); ((TAtom "L16"), ("./Xprintf_buffer_write.c", 33%nat)); ((TAtom "L32"), ("./Xprintf_buffer_write.c", 33%nat)); ((TAtom "L33"), ("./Xprintf_buffer_write.c", 33%nat)); ((TAtom "L20"), ("./Xprintf_buffer_write.c", 34%nat)); ((TAtom "L22"), ("./Xprintf_buffer_write.c", 35%nat)); ((TAtom "L42"), ("./Xprintf_buffer_write.c", 35%nat)); ((TAtom "L43"), ("./Xprintf_buffer_write.c", 36%nat)); ((TAtom "L67"), ("./Xprintf_buffer_write.c", 37%nat)); ((TAtom "L68"), ("./Xprintf_buffer_write.c", 36%nat)); ((TAtom "L17"), ("./Xprintf_buffer_write.c", 24%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "pr.1"), "s"); ((TAtom "pr.2"), "count"); ((TAtom "pr.3"), "to_copy"); ((TAtom "v0"), "buf"); ((TAtom "v18"), "count"); ((TAtom "v2"), "s"); ((TAtom "v23"), "buf"); ((TAtom "v26"), "buf"); ((TAtom "v34"), "buf"); ((TAtom "v4"), "count"); ((TAtom "v44"), "buf"); ((TAtom "v47"), "buf"); ((TAtom "v57"), "buf"); ((TAtom "v60"), "buf"); ((TAtom "v65"), "to_copy"); ((TAtom "v69"), "to_copy"); ((TAtom "v70"), "count"); ((TAtom "v72"), "count"); ((TAtom "v73"), "buf"); ((TAtom "v76"), "s"); ((TAtom "v77"), "to_copy"); ((TAtom "v79"), "buf"); ((TAtom "v82"), "to_copy"); ((TAtom "v84"), "s"); ((TAtom "v85"), "to_copy"); ((TAtom "v86"), "s"); ((TAtom "v87"), "count"); ((TAtom "v88"), "to_copy"); ((TAtom "v89"), "count"); ((TAtom "v9"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L15")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__printf_buffer_write") (code_module printf_buffer_io_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___printf_buffer_write.

Module fn___printf_buffer_flush.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("./Xprintf_buffer_flush.c", 59%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../include/printf_buffer.h", 115%nat)); ((TAtom "L2"), ("./Xprintf_buffer_flush.c", 63%nat)); ((TAtom "iw_2.start"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L9"), ("printf_buffer_flush.c", 47%nat)); ((TAtom "iw_2.L11"), ("printf_buffer_flush.c", 50%nat)); ((TAtom "iw_2.L12"), ("printf_buffer_flush.c", 53%nat)); ((TAtom "iw_2.L14"), ("printf_buffer_flush.c", 56%nat)); ((TAtom "iw_2.L16"), ("printf_buffer_flush.c", 59%nat)); ((TAtom "iw_2.L18"), ("printf_buffer_flush.c", 62%nat)); ((TAtom "iw_2.L21"), ("printf_buffer_flush.c", 66%nat)); ((TAtom "iw_2.L23"), ("printf_buffer_flush.c", 69%nat)); ((TAtom "iw_2.L25"), ("printf_buffer_flush.c", 73%nat)); ((TAtom "iw_2.L27"), ("printf_buffer_flush.c", 77%nat)); ((TAtom "iw_2.L31"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L34"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L37"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L39"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L35"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L43"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L45"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L32"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L49"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L52"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L54"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L50"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L58"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L60"), ("printf_buffer_flush.c", 41%nat)); ((TAtom "iw_2.L6"), ("printf_buffer_flush.c", 80%nat)); ((TAtom "iw_3.start"), ("../include/printf_buffer.h", 115%nat)); ((TAtom "L13"), ("./Xprintf_buffer_flush.c", 67%nat)); ((TAtom "L15"), ("./Xprintf_buffer_flush.c", 70%nat)); ((TAtom "L22"), ("./Xprintf_buffer_flush.c", 70%nat)); ((TAtom "L23"), ("./Xprintf_buffer_flush.c", 71%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "iw_2.iw_1.v0"), "buf"); ((TAtom "iw_2.iw_1.v2"), "buf"); ((TAtom "iw_2.v0"), "buf"); ((TAtom "iw_2.v10"), "buf"); ((TAtom "iw_2.v13"), "buf"); ((TAtom "iw_2.v15"), "buf"); ((TAtom "iw_2.v17"), "buf"); ((TAtom "iw_2.v2"), "buf"); ((TAtom "iw_2.v20"), "buf"); ((TAtom "iw_2.v22"), "buf"); ((TAtom "iw_2.v24"), "buf"); ((TAtom "iw_2.v26"), "buf"); ((TAtom "iw_2.v28"), "buf"); ((TAtom "iw_3.v0"), "buf"); ((TAtom "iw_3.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v12"), "buf"); ((TAtom "v16"), "buf"); ((TAtom "v24"), "buf"); ((TAtom "v27"), "buf"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__printf_buffer_flush") (code_module printf_buffer_io_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___printf_buffer_flush.

End PrintfBufferIoSrc.

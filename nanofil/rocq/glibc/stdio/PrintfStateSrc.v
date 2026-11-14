(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude PrintfStateCode.
Import ListNotations.
Open Scope string_scope.

Module PrintfStateSrc.

Module fn___GI___pthread_setcancelstate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("pthread_setcancelstate.c", 23%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("pthread_setcancelstate.c", 28%nat)); ((TAtom "L10"), ("pthread_setcancelstate.c", 28%nat)); ((TAtom "L11"), ("pthread_setcancelstate.c", 28%nat)); ((TAtom "L5"), ("pthread_setcancelstate.c", 29%nat)); ((TAtom "L7"), ("pthread_setcancelstate.c", 31%nat)); ((TAtom "L22"), ("pthread_setcancelstate.c", 33%nat)); ((TAtom "L26"), ("pthread_setcancelstate.c", 36%nat)); ((TAtom "L27"), ("pthread_setcancelstate.c", 36%nat)); ((TAtom "L28"), ("pthread_setcancelstate.c", 36%nat)); ((TAtom "L39"), ("pthread_setcancelstate.c", 41%nat)); ((TAtom "L48"), ("pthread_setcancelstate.c", 41%nat)); ((TAtom "L49"), ("pthread_setcancelstate.c", 41%nat)); ((TAtom "L41"), ("pthread_setcancelstate.c", 44%nat)); ((TAtom "L56"), ("pthread_setcancelstate.c", 47%nat)); ((TAtom "L70"), ("pthread_setcancelstate.c", 47%nat)); ((TAtom "L71"), ("pthread_setcancelstate.c", 33%nat)); ((TAtom "iw_1.start"), ("../nptl/descr.h", 471%nat)); ((TAtom "L72"), ("pthread_setcancelstate.c", 51%nat)); ((TAtom "iw_2.L12"), ("../sysdeps/nptl/pthreadP.h", 256%nat)); ((TAtom "iw_2.L13"), ("../sysdeps/nptl/pthreadP.h", 268%nat)); ((TAtom "iw_2.L37"), ("../sysdeps/nptl/pthreadP.h", 268%nat)); ((TAtom "iw_2.L38"), ("../sysdeps/nptl/pthreadP.h", 256%nat)); ((TAtom "iw_2.L14"), ("../sysdeps/nptl/pthreadP.h", 271%nat)); ((TAtom "L24"), ("pthread_setcancelstate.c", 57%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v2"), "value"); ((TAtom "iw_2.pr.1"), "oldval"); ((TAtom "iw_2.pr.2"), "oldval"); ((TAtom "iw_2.v0"), "result"); ((TAtom "iw_2.v10"), "oldval"); ((TAtom "iw_2.v15"), "oldval"); ((TAtom "iw_2.v19"), "newval"); ((TAtom "iw_2.v20"), "newval"); ((TAtom "iw_2.v23"), "newval"); ((TAtom "iw_2.v27"), "oldval"); ((TAtom "iw_2.v28"), "newval"); ((TAtom "iw_2.v3"), "self"); ((TAtom "iw_2.v31"), "self"); ((TAtom "iw_2.v33"), "newval"); ((TAtom "iw_2.v34"), "oldval"); ((TAtom "iw_2.v35"), "oldval"); ((TAtom "iw_2.v4"), "self"); ((TAtom "iw_2.v40"), "self"); ((TAtom "iw_2.v6"), "result"); ((TAtom "iw_2.v8"), "self"); ((TAtom "pr.1"), "oldval"); ((TAtom "pr.2"), "oldval"); ((TAtom "v0"), "state"); ((TAtom "v12"), "state"); ((TAtom "v17"), "self"); ((TAtom "v19"), "self"); ((TAtom "v2"), "oldstate"); ((TAtom "v21"), "oldval"); ((TAtom "v29"), "state"); ((TAtom "v31"), "oldval"); ((TAtom "v34"), "oldval"); ((TAtom "v38"), "newval"); ((TAtom "v42"), "oldstate"); ((TAtom "v46"), "oldstate"); ((TAtom "v50"), "oldval"); ((TAtom "v57"), "oldval"); ((TAtom "v58"), "newval"); ((TAtom "v64"), "self"); ((TAtom "v66"), "newval"); ((TAtom "v67"), "oldval"); ((TAtom "v68"), "oldval"); ((TAtom "v75"), "newval"); ((TAtom "v8"), "state")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L22"); (TAtom "iw_2.L12")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___pthread_setcancelstate") (code_module printf_state_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___pthread_setcancelstate.

Module fn___printf_buffer_done.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("./Xprintf_buffer_done.c", 23%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("../include/printf_buffer.h", 115%nat)); ((TAtom "L2"), ("./Xprintf_buffer_done.c", 27%nat)); ((TAtom "L4"), ("./Xprintf_buffer_done.c", 31%nat)); ((TAtom "L20"), ("./Xprintf_buffer_done.c", 35%nat)); ((TAtom "L21"), ("./Xprintf_buffer_done.c", 39%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v11"), "buf"); ((TAtom "v14"), "buf"); ((TAtom "v18"), "written_current"); ((TAtom "v23"), "buf"); ((TAtom "v26"), "written_current"); ((TAtom "v27"), "written_total"); ((TAtom "v40"), "written_total"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__printf_buffer_done") (code_module printf_state_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___printf_buffer_done.

End PrintfStateSrc.

(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import PrintfStateCode.
Module PrintfStateSrc.

Definition file_0 : string := "../include/printf_buffer.h".

Definition file_1 : string := "../nptl/descr.h".

Definition file_2 : string := "../sysdeps/nptl/pthreadP.h".

Definition file_3 : string := "./Xprintf_buffer_done.c".

Definition file_4 : string := "pthread_setcancelstate.c".

Module fn___GI___pthread_setcancelstate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_4, 23%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_4, 28%N)); ((TAtom "L10"), (file_4, 28%N)); ((TAtom "L11"), (file_4, 28%N)); ((TAtom "L5"), (file_4, 29%N)); ((TAtom "L7"), (file_4, 31%N)); ((TAtom "L22"), (file_4, 33%N)); ((TAtom "L26"), (file_4, 36%N)); ((TAtom "L27"), (file_4, 36%N)); ((TAtom "L28"), (file_4, 36%N)); ((TAtom "L39"), (file_4, 41%N)); ((TAtom "L48"), (file_4, 41%N)); ((TAtom "L49"), (file_4, 41%N)); ((TAtom "L41"), (file_4, 44%N)); ((TAtom "L56"), (file_4, 47%N)); ((TAtom "L70"), (file_4, 47%N)); ((TAtom "L71"), (file_4, 33%N)); ((TAtom "iw_1.start"), (file_1, 471%N)); ((TAtom "L72"), (file_4, 51%N)); ((TAtom "iw_2.L12"), (file_2, 256%N)); ((TAtom "iw_2.L13"), (file_2, 268%N)); ((TAtom "iw_2.L37"), (file_2, 268%N)); ((TAtom "iw_2.L38"), (file_2, 256%N)); ((TAtom "iw_2.L14"), (file_2, 271%N)); ((TAtom "L24"), (file_4, 57%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "value"); ((TAtom "iw_1.v2"), "value"); ((TAtom "iw_2.pr.1"), "oldval"); ((TAtom "iw_2.pr.2"), "oldval"); ((TAtom "iw_2.v0"), "result"); ((TAtom "iw_2.v10"), "oldval"); ((TAtom "iw_2.v15"), "oldval"); ((TAtom "iw_2.v19"), "newval"); ((TAtom "iw_2.v20"), "newval"); ((TAtom "iw_2.v23"), "newval"); ((TAtom "iw_2.v27"), "oldval"); ((TAtom "iw_2.v28"), "newval"); ((TAtom "iw_2.v3"), "self"); ((TAtom "iw_2.v31"), "self"); ((TAtom "iw_2.v33"), "newval"); ((TAtom "iw_2.v34"), "oldval"); ((TAtom "iw_2.v35"), "oldval"); ((TAtom "iw_2.v4"), "self"); ((TAtom "iw_2.v40"), "self"); ((TAtom "iw_2.v6"), "result"); ((TAtom "iw_2.v8"), "self"); ((TAtom "pr.1"), "oldval"); ((TAtom "pr.2"), "oldval"); ((TAtom "v0"), "state"); ((TAtom "v12"), "state"); ((TAtom "v17"), "self"); ((TAtom "v19"), "self"); ((TAtom "v2"), "oldstate"); ((TAtom "v21"), "oldval"); ((TAtom "v29"), "state"); ((TAtom "v31"), "oldval"); ((TAtom "v34"), "oldval"); ((TAtom "v38"), "newval"); ((TAtom "v42"), "oldstate"); ((TAtom "v46"), "oldstate"); ((TAtom "v50"), "oldval"); ((TAtom "v57"), "oldval"); ((TAtom "v58"), "newval"); ((TAtom "v64"), "self"); ((TAtom "v66"), "newval"); ((TAtom "v67"), "oldval"); ((TAtom "v68"), "oldval"); ((TAtom "v75"), "newval"); ((TAtom "v8"), "state")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L22"); (TAtom "iw_2.L12")].

End fn___GI___pthread_setcancelstate.

Module fn___printf_buffer_done.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_3, 23%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L2"), (file_3, 27%N)); ((TAtom "L4"), (file_3, 31%N)); ((TAtom "L20"), (file_3, 35%N)); ((TAtom "L21"), (file_3, 39%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "v0"), "buf"); ((TAtom "v11"), "buf"); ((TAtom "v14"), "buf"); ((TAtom "v18"), "written_current"); ((TAtom "v23"), "buf"); ((TAtom "v26"), "written_current"); ((TAtom "v27"), "written_total"); ((TAtom "v40"), "written_total"); ((TAtom "v5"), "buf")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn___printf_buffer_done.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) printf_state_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI___pthread_setcancelstate"; "__printf_buffer_done"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("__GI___pthread_setcancelstate", app (map fst fn___GI___pthread_setcancelstate.block_src) fn___GI___pthread_setcancelstate.loop_heads); ("__printf_buffer_done", app (map fst fn___printf_buffer_done.block_src) fn___printf_buffer_done.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfStateSrc.

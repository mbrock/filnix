(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L56"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v68"); (TAtom "v69")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v69")]); ((TAtom "iw_1.start"), [(TAtom "v38")]); ((TAtom "L72"), []); ((TAtom "iw_2.L12"), [(TAtom "chk3"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L37"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L14"), [(TAtom "chk3"); (TAtom "iw_2.v3")]); ((TAtom "L24"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v13"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v21")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v33")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v37")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L56"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v68"); (TAtom "v69")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v68"); (TAtom "v69")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "iw_1.start"), []); ((TAtom "L72"), [(TAtom "chk3"); (TAtom "iw_2.v10"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L12"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L37"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk3"); (TAtom "iw_2.pr.2"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L14"), []); ((TAtom "L24"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L11"), []); ((TAtom "L5"), []); ((TAtom "L7"), [(3%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 4), true, false, (Some (TAtom "v17")), (Some (792)))]); ((TAtom "L22"), []); ((TAtom "L26"), []); ((TAtom "L27"), []); ((TAtom "L28"), []); ((TAtom "L39"), []); ((TAtom "L48"), []); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), false, true, (Some (TAtom "v2")), (Some (0)))]); ((TAtom "L41"), []); ((TAtom "L56"), [(2%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 4), true, true, (Some (TAtom "v17")), (Some (792)))]); ((TAtom "L70"), []); ((TAtom "L71"), []); ((TAtom "iw_1.start"), []); ((TAtom "L72"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v3")), (Some (1608))); (7%N, (TApp "tmp" [(TAtom "iw_2.v9")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L13"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v32")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L38"), []); ((TAtom "iw_2.L14"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (784)))]); ((TAtom "L24"), [])].


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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L21"), [(TAtom "v27")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "v27")]); ((TAtom "L20"), []); ((TAtom "L21"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0))); (9%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (-8), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L20"), [(2%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 4), false, true, (Some (TAtom "v37")), (Some (0)))]); ((TAtom "L21"), [])].


End fn___printf_buffer_done.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) printf_state_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI___pthread_setcancelstate"; "__printf_buffer_done"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__GI___pthread_setcancelstate", app (map fst fn___GI___pthread_setcancelstate.block_src) (app (map fst fn___GI___pthread_setcancelstate.live_in) (app (map fst fn___GI___pthread_setcancelstate.live_out) (app (map fst fn___GI___pthread_setcancelstate.footprint) (fn___GI___pthread_setcancelstate.loop_heads))))); ("__printf_buffer_done", app (map fst fn___printf_buffer_done.block_src) (app (map fst fn___printf_buffer_done.live_in) (app (map fst fn___printf_buffer_done.live_out) (app (map fst fn___printf_buffer_done.footprint) (fn___printf_buffer_done.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfStateSrc.

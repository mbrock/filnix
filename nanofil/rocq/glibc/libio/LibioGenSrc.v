(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioGenCode.
Import ListNotations.
Open Scope string_scope.

Module LibioGenSrc.

Module fn___GI___overflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 223%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 227%nat)); ((TAtom "L13"), ("genops.c", 228%nat)); ((TAtom "L23"), ("genops.c", 228%nat)); ((TAtom "L25"), ("genops.c", 228%nat)); ((TAtom "L6"), ("genops.c", 229%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 229%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "__result"); ((TAtom "pr.2"), "__result"); ((TAtom "v0"), "f"); ((TAtom "v12"), "__result"); ((TAtom "v16"), "__result"); ((TAtom "v2"), "ch"); ((TAtom "v26"), "f"); ((TAtom "v30"), "f"); ((TAtom "v33"), "f"); ((TAtom "v35"), "__result"); ((TAtom "v49"), "f"); ((TAtom "v52"), "__result"); ((TAtom "v53"), "f"); ((TAtom "v54"), "__result"); ((TAtom "v55"), "__result"); ((TAtom "v56"), "__result"); ((TAtom "v57"), "f"); ((TAtom "v63"), "f"); ((TAtom "v64"), "ch"); ((TAtom "v7"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___overflow") (code_module libiogen_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___overflow.

Module fn___GI__IO_default_xsputn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 395%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 400%nat)); ((TAtom "L10"), ("genops.c", 401%nat)); ((TAtom "L16"), ("genops.c", 399%nat)); ((TAtom "L20"), ("genops.c", 407%nat)); ((TAtom "L43"), ("genops.c", 408%nat)); ((TAtom "L44"), ("genops.c", 407%nat)); ((TAtom "L49"), ("genops.c", 412%nat)); ((TAtom "L50"), ("genops.c", 415%nat)); ((TAtom "L65"), ("genops.c", 417%nat)); ((TAtom "L76"), ("genops.c", 418%nat)); ((TAtom "L77"), ("genops.c", 420%nat)); ((TAtom "L79"), ("genops.c", 421%nat)); ((TAtom "L51"), ("genops.c", 398%nat)); ((TAtom "L22"), ("genops.c", 399%nat)); ((TAtom "L99"), ("genops.c", 425%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("genops.c", 425%nat)); ((TAtom "L100"), ("genops.c", 425%nat)); ((TAtom "L96"), ("genops.c", 427%nat)); ((TAtom "L19"), ("genops.c", 429%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "s"); ((TAtom "pr.10"), "p"); ((TAtom "pr.11"), "i"); ((TAtom "pr.2"), "s"); ((TAtom "pr.3"), "s"); ((TAtom "pr.4"), "s"); ((TAtom "pr.5"), "s"); ((TAtom "pr.6"), "s"); ((TAtom "pr.7"), "more"); ((TAtom "pr.8"), "more"); ((TAtom "pr.9"), "count"); ((TAtom "v0"), "f"); ((TAtom "v101"), "f"); ((TAtom "v107"), "f"); ((TAtom "v108"), "s"); ((TAtom "v109"), "s"); ((TAtom "v118"), "more"); ((TAtom "v119"), "more"); ((TAtom "v120"), "n"); ((TAtom "v121"), "more"); ((TAtom "v13"), "more"); ((TAtom "v2"), "data"); ((TAtom "v23"), "f"); ((TAtom "v26"), "f"); ((TAtom "v33"), "f"); ((TAtom "v36"), "f"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v45"), "count"); ((TAtom "v46"), "more"); ((TAtom "v48"), "more"); ((TAtom "v52"), "count"); ((TAtom "v54"), "f"); ((TAtom "v56"), "f"); ((TAtom "v59"), "s"); ((TAtom "v60"), "count"); ((TAtom "v62"), "s"); ((TAtom "v63"), "count"); ((TAtom "v64"), "s"); ((TAtom "v68"), "count"); ((TAtom "v7"), "data"); ((TAtom "v71"), "f"); ((TAtom "v73"), "p"); ((TAtom "v75"), "count"); ((TAtom "v80"), "i"); ((TAtom "v81"), "i"); ((TAtom "v83"), "p"); ((TAtom "v84"), "p"); ((TAtom "v85"), "s"); ((TAtom "v86"), "s"); ((TAtom "v88"), "f"); ((TAtom "v9"), "n"); ((TAtom "v90"), "p"); ((TAtom "v91"), "more"); ((TAtom "v92"), "count"); ((TAtom "v93"), "more"); ((TAtom "v97"), "more")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L16"); (TAtom "L76")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_xsputn") (code_module libiogen_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_xsputn.

Module fn___GI__IO_unsave_markers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 981%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 984%nat)); ((TAtom "L6"), ("genops.c", 987%nat)); ((TAtom "L8"), ("genops.c", 990%nat)); ((TAtom "L14"), ("genops.c", 991%nat)); ((TAtom "L16"), ("genops.c", 981%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v5"), "mark"); ((TAtom "v9"), "mark")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_unsave_markers") (code_module libiogen_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_unsave_markers.

Module fn___GI___call_tls_dtors.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("cxa_thread_atexit_impl.c", 80%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("cxa_thread_atexit_impl.c", 80%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI___call_tls_dtors") (code_module libiogen_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI___call_tls_dtors.

End LibioGenSrc.

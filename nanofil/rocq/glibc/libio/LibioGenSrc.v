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


From Glibc Require Import LibioGenCode.
Module LibioGenSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "cxa_thread_atexit_impl.c".

Definition file_2 : string := "genops.c".

Module fn___GI___overflow.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 223%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 227%N)); ((TAtom "L13"), (file_2, 228%N)); ((TAtom "L23"), (file_2, 228%N)); ((TAtom "L25"), (file_2, 228%N)); ((TAtom "L6"), (file_2, 229%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_2, 229%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "__result"); ((TAtom "pr.2"), "__result"); ((TAtom "v0"), "f"); ((TAtom "v12"), "__result"); ((TAtom "v16"), "__result"); ((TAtom "v2"), "ch"); ((TAtom "v26"), "f"); ((TAtom "v30"), "f"); ((TAtom "v33"), "f"); ((TAtom "v35"), "__result"); ((TAtom "v49"), "f"); ((TAtom "v52"), "__result"); ((TAtom "v53"), "f"); ((TAtom "v54"), "__result"); ((TAtom "v55"), "__result"); ((TAtom "v56"), "__result"); ((TAtom "v57"), "f"); ((TAtom "v63"), "f"); ((TAtom "v64"), "ch"); ((TAtom "v7"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L25"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v59")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v59")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L25"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L6"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v59")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v59")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L13"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L23"), [(2%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L25"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L6"), [(2%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v59")), (Some (24)))])].


End fn___GI___overflow.

Module fn___GI__IO_default_xsputn.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 395%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 400%N)); ((TAtom "L10"), (file_2, 401%N)); ((TAtom "L16"), (file_2, 399%N)); ((TAtom "L20"), (file_2, 407%N)); ((TAtom "L43"), (file_2, 408%N)); ((TAtom "L44"), (file_2, 407%N)); ((TAtom "L49"), (file_2, 412%N)); ((TAtom "L50"), (file_2, 415%N)); ((TAtom "L65"), (file_2, 417%N)); ((TAtom "L76"), (file_2, 418%N)); ((TAtom "L77"), (file_2, 420%N)); ((TAtom "L79"), (file_2, 421%N)); ((TAtom "L51"), (file_2, 398%N)); ((TAtom "L22"), (file_2, 399%N)); ((TAtom "L99"), (file_2, 425%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_2, 425%N)); ((TAtom "L100"), (file_2, 425%N)); ((TAtom "L96"), (file_2, 427%N)); ((TAtom "L19"), (file_2, 429%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "s"); ((TAtom "pr.10"), "p"); ((TAtom "pr.11"), "i"); ((TAtom "pr.2"), "s"); ((TAtom "pr.3"), "s"); ((TAtom "pr.4"), "s"); ((TAtom "pr.5"), "s"); ((TAtom "pr.6"), "s"); ((TAtom "pr.7"), "more"); ((TAtom "pr.8"), "more"); ((TAtom "pr.9"), "count"); ((TAtom "v0"), "f"); ((TAtom "v101"), "f"); ((TAtom "v107"), "f"); ((TAtom "v108"), "s"); ((TAtom "v109"), "s"); ((TAtom "v118"), "more"); ((TAtom "v119"), "more"); ((TAtom "v120"), "n"); ((TAtom "v121"), "more"); ((TAtom "v13"), "more"); ((TAtom "v2"), "data"); ((TAtom "v23"), "f"); ((TAtom "v26"), "f"); ((TAtom "v33"), "f"); ((TAtom "v36"), "f"); ((TAtom "v4"), "n"); ((TAtom "v41"), "count"); ((TAtom "v45"), "count"); ((TAtom "v46"), "more"); ((TAtom "v48"), "more"); ((TAtom "v52"), "count"); ((TAtom "v54"), "f"); ((TAtom "v56"), "f"); ((TAtom "v59"), "s"); ((TAtom "v60"), "count"); ((TAtom "v62"), "s"); ((TAtom "v63"), "count"); ((TAtom "v64"), "s"); ((TAtom "v68"), "count"); ((TAtom "v7"), "data"); ((TAtom "v71"), "f"); ((TAtom "v73"), "p"); ((TAtom "v75"), "count"); ((TAtom "v80"), "i"); ((TAtom "v81"), "i"); ((TAtom "v83"), "p"); ((TAtom "v84"), "p"); ((TAtom "v85"), "s"); ((TAtom "v86"), "s"); ((TAtom "v88"), "f"); ((TAtom "v9"), "n"); ((TAtom "v90"), "p"); ((TAtom "v91"), "more"); ((TAtom "v92"), "count"); ((TAtom "v93"), "more"); ((TAtom "v97"), "more")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L16"); (TAtom "L76")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), []); ((TAtom "L16"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4"); (TAtom "v41")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L77"), [(TAtom "chk0"); (TAtom "pr.10"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v81")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "pr.10"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "L100"), [(TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L96"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "pr.8"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), []); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4"); (TAtom "v41")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v4"); (TAtom "v41")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v64")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk0"); (TAtom "pr.10"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v81")]); ((TAtom "L77"), [(TAtom "chk0"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v81"); (TAtom "v84"); (TAtom "v86")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "pr.6"); (TAtom "pr.7"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v93")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L99"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v103"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "pr.8"); (TAtom "v0"); (TAtom "v109"); (TAtom "v114"); (TAtom "v4")]); ((TAtom "L100"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L96"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v119"); (TAtom "v4")]); ((TAtom "L19"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L16"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (48)))]); ((TAtom "L20"), [(1%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (48))); (3%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L43"), []); ((TAtom "L44"), []); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (4%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L50"), []); ((TAtom "L65"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L76"), []); ((TAtom "L77"), [(3%N, (TApp "tmp" [(TAtom "pr.6")]), (0), (Some 1), true, false, (Some (TAtom "pr.6")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "pr.10")]), (0), (Some 1), false, true, (Some (TAtom "pr.10")), (Some (0)))]); ((TAtom "L79"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "L51"), []); ((TAtom "L22"), []); ((TAtom "L99"), [(2%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v103")), (Some (24))); (5%N, (TApp "tmp" [(TAtom "pr.3")]), (0), (Some 1), true, false, (Some (TAtom "pr.3")), (Some (0)))]); ((TAtom "L100"), []); ((TAtom "L96"), []); ((TAtom "L19"), [])].


End fn___GI__IO_default_xsputn.

Module fn___GI__IO_unsave_markers.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 981%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 984%N)); ((TAtom "L6"), (file_2, 987%N)); ((TAtom "L8"), (file_2, 990%N)); ((TAtom "L14"), (file_2, 991%N)); ((TAtom "L16"), (file_2, 981%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v12"), "fp"); ((TAtom "v17"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v3"), "fp"); ((TAtom "v5"), "mark"); ((TAtom "v9"), "mark")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "v0")]); ((TAtom "L16"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "v0")]); ((TAtom "L14"), []); ((TAtom "L16"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L6"), [(2%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L8"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L14"), []); ((TAtom "L16"), [])].


End fn___GI__IO_unsave_markers.

Module fn___GI___call_tls_dtors.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 80%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 80%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn___GI___call_tls_dtors.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiogen_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI___overflow"; "__GI__IO_default_xsputn"; "__GI__IO_unsave_markers"; "__GI___call_tls_dtors"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__GI___overflow", app (map fst fn___GI___overflow.block_src) (app (map fst fn___GI___overflow.live_in) (app (map fst fn___GI___overflow.live_out) (app (map fst fn___GI___overflow.footprint) (fn___GI___overflow.loop_heads))))); ("__GI__IO_default_xsputn", app (map fst fn___GI__IO_default_xsputn.block_src) (app (map fst fn___GI__IO_default_xsputn.live_in) (app (map fst fn___GI__IO_default_xsputn.live_out) (app (map fst fn___GI__IO_default_xsputn.footprint) (fn___GI__IO_default_xsputn.loop_heads))))); ("__GI__IO_unsave_markers", app (map fst fn___GI__IO_unsave_markers.block_src) (app (map fst fn___GI__IO_unsave_markers.live_in) (app (map fst fn___GI__IO_unsave_markers.live_out) (app (map fst fn___GI__IO_unsave_markers.footprint) (fn___GI__IO_unsave_markers.loop_heads))))); ("__GI___call_tls_dtors", app (map fst fn___GI___call_tls_dtors.block_src) (app (map fst fn___GI___call_tls_dtors.live_in) (app (map fst fn___GI___call_tls_dtors.live_out) (app (map fst fn___GI___call_tls_dtors.footprint) (fn___GI___call_tls_dtors.loop_heads)))))].

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

End LibioGenSrc.

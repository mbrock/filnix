(** An executor needs to know which values and memory regions a block may use.
    These tables list live temporaries and explicit memory accesses to guide that choice.
    Wrong hints can stop execution, but they cannot justify a memory access.
    No soundness theorem may assume that these tables are correct.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import LibioGenSrc.
Module LibioGenBlocks.

Module fn___GI___overflow.

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

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__GI___overflow", app (map fst fn___GI___overflow.live_in) (app (map fst fn___GI___overflow.live_out) (map fst fn___GI___overflow.footprint))); ("__GI__IO_default_xsputn", app (map fst fn___GI__IO_default_xsputn.live_in) (app (map fst fn___GI__IO_default_xsputn.live_out) (map fst fn___GI__IO_default_xsputn.footprint))); ("__GI__IO_unsave_markers", app (map fst fn___GI__IO_unsave_markers.live_in) (app (map fst fn___GI__IO_unsave_markers.live_out) (map fst fn___GI__IO_unsave_markers.footprint))); ("__GI___call_tls_dtors", app (map fst fn___GI___call_tls_dtors.live_in) (app (map fst fn___GI___call_tls_dtors.live_out) (map fst fn___GI___call_tls_dtors.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) LibioGenSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End LibioGenBlocks.

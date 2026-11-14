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


From Glibc Require Import GetoptSrcFiles.
Import GetoptSrcFiles.
Module GetoptSrc03.

Module fn__getopt_internal.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 702%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 709%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "argc"); ((TAtom "v10"), "long_only"); ((TAtom "v12"), "posixly_correct"); ((TAtom "v17"), "optind"); ((TAtom "v2"), "argv"); ((TAtom "v21"), "opterr"); ((TAtom "v22"), "argc"); ((TAtom "v23"), "argv"); ((TAtom "v24"), "optstring"); ((TAtom "v25"), "longopts"); ((TAtom "v26"), "longind"); ((TAtom "v27"), "long_only"); ((TAtom "v29"), "posixly_correct"); ((TAtom "v30"), "result"); ((TAtom "v33"), "optind"); ((TAtom "v37"), "optarg"); ((TAtom "v4"), "optstring"); ((TAtom "v41"), "optopt"); ((TAtom "v42"), "result"); ((TAtom "v6"), "longopts"); ((TAtom "v8"), "longind")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 4), true, false, (Some (TAtom "v16")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 4), false, true, (Some (TAtom "v15")), (Some (0))); (10%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 4), true, false, (Some (TAtom "v20")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 4), false, true, (Some (TAtom "v18")), (Some (4))); (18%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 4), true, false, (Some (TAtom "v32")), (Some (0))); (20%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 4), false, true, (Some (TAtom "v31")), (Some (0))); (25%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), true, false, (Some (TAtom "v35")), (Some (16))); (27%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), false, true, (Some (TAtom "v34")), (Some (0))); (32%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 4), true, false, (Some (TAtom "v39")), (Some (8))); (34%N, (TApp "tmp" [(TAtom "v38")]), (0), (Some 4), false, true, (Some (TAtom "v38")), (Some (0)))])].


End fn__getopt_internal.

Module fn_getopt_long.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 27%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 31%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "argc"); ((TAtom "v10"), "argc"); ((TAtom "v11"), "argv"); ((TAtom "v12"), "options"); ((TAtom "v13"), "long_options"); ((TAtom "v14"), "opt_index"); ((TAtom "v2"), "argv"); ((TAtom "v4"), "options"); ((TAtom "v6"), "long_options"); ((TAtom "v8"), "opt_index")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].


End fn_getopt_long.

End GetoptSrc03.

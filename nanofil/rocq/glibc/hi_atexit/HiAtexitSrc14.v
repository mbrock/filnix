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


From Glibc Require Import HiAtexitSrcFiles.
Import HiAtexitSrcFiles.
Module HiAtexitSrc14.

Module fn___libc_start_main.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 98%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 104%N)); ((TAtom "L17"), (file_1, 109%N)); ((TAtom "L18"), (file_1, 111%N)); ((TAtom "L24"), (file_1, 113%N)); ((TAtom "L19"), (file_1, 110%N)); ((TAtom "L20"), (file_1, 118%N)); ((TAtom "L37"), (file_1, 119%N)); ((TAtom "L39"), (file_1, 121%N)); ((TAtom "L48"), (file_1, 149%N)); ((TAtom "L50"), (file_1, 151%N)); ((TAtom "L61"), (file_1, 154%N)); ((TAtom "L63"), (file_1, 159%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "av"); ((TAtom "v0"), "main"); ((TAtom "v12"), "ev"); ((TAtom "v14"), "auxvec"); ((TAtom "v16"), "auxvec"); ((TAtom "v2"), "argc"); ((TAtom "v21"), "av"); ((TAtom "v27"), "av"); ((TAtom "v31"), "av"); ((TAtom "v33"), "__libc_enable_secure"); ((TAtom "v35"), "av"); ((TAtom "v36"), "av"); ((TAtom "v4"), "argv"); ((TAtom "v52"), "_dl_debug_mask"); ((TAtom "v58"), "argv"); ((TAtom "v6"), "ev"); ((TAtom "v65"), "_dl_debug_mask"); ((TAtom "v71"), "argv"); ((TAtom "v74"), "main"); ((TAtom "v75"), "argc"); ((TAtom "v76"), "argv"); ((TAtom "v8"), "auxvec")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L17")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L17"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L24"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L39"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L50"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L61"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L63"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "L17"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [(TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L24"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v36"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L39"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L50"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L61"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L63"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), false, true, (Some (TAtom "v11")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v13")), (Some (0)), "opaque")]); ((TAtom "L17"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "av->a_type")]); ((TAtom "L18"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "av->a_type")]); ((TAtom "L24"), [(3%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)), "av->a_un.a_val"); (5%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 4), false, true, (Some (TAtom "v30")), (Some (0)), "opaque")]); ((TAtom "L19"), []); ((TAtom "L20"), []); ((TAtom "L37"), []); ((TAtom "L39"), [(10%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 4), true, false, (Some (TAtom "v51")), (Some (0)), "opaque")]); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (0)), "opaque")]); ((TAtom "L50"), [(3%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 4), true, false, (Some (TAtom "v64")), (Some (0)), "opaque")]); ((TAtom "L61"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (0)), "opaque")]); ((TAtom "L63"), [])].


End fn___libc_start_main.

Module fn_glibc_libc_start_futex_wake.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_8, 170%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_8, 173%N)); ((TAtom "L17"), (file_8, 173%N)); ((TAtom "L18"), (file_8, 173%N)); ((TAtom "L14"), (file_8, 173%N)); ((TAtom "L11"), (file_8, 173%N)); ((TAtom "L29"), (file_8, 173%N)); ((TAtom "L30"), (file_8, 173%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "futex_word"); ((TAtom "v15"), "private"); ((TAtom "v19"), "private"); ((TAtom "v2"), "processes_to_wake"); ((TAtom "v31"), "private"); ((TAtom "v37"), "res"); ((TAtom "v4"), "private"); ((TAtom "v40"), "res"); ((TAtom "v7"), "futex_word"); ((TAtom "v8"), "processes_to_wake")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L17"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L18"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L14"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L17"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2"); (TAtom "v20")]); ((TAtom "L18"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L14"), [(TAtom "v0"); (TAtom "v16"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L30"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L17"), []); ((TAtom "L18"), []); ((TAtom "L14"), []); ((TAtom "L11"), []); ((TAtom "L29"), []); ((TAtom "L30"), [])].


End fn_glibc_libc_start_futex_wake.

End HiAtexitSrc14.

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
Module HiAtexitSrc08.

Module fn___strlen.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_29, 31%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_29, 35%N)); ((TAtom "iw_3.start"), (file_1, 193%N)); ((TAtom "iw_3.iw_1.iw_1.L3"), (file_1, 193%N)); ((TAtom "iw_3.iw_1.iw_1.L4"), (file_1, 193%N)); ((TAtom "L28"), (file_29, 36%N)); ((TAtom "iw_5.start"), (file_1, 193%N)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), (file_1, 193%N)); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), (file_1, 193%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_1.v0"), "x"); ((TAtom "iw_1.v11"), "m"); ((TAtom "iw_1.v3"), "m"); ((TAtom "iw_1.v4"), "x"); ((TAtom "iw_1.v5"), "m"); ((TAtom "iw_1.v7"), "m"); ((TAtom "iw_1.v9"), "x"); ((TAtom "iw_2.v0"), "word"); ((TAtom "iw_2.v14"), "word"); ((TAtom "iw_2.v15"), "s"); ((TAtom "iw_2.v2"), "s"); ((TAtom "iw_2.v8"), "word"); ((TAtom "iw_2.v9"), "s"); ((TAtom "iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_3.iw_1.v0"), "c"); ((TAtom "iw_3.iw_1.v12"), "c"); ((TAtom "iw_3.iw_1.v18"), "c"); ((TAtom "iw_3.iw_1.v21"), "c"); ((TAtom "iw_3.iw_1.v6"), "c"); ((TAtom "iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_3.iw_2.v0"), "c"); ((TAtom "iw_3.iw_2.v2"), "c"); ((TAtom "iw_3.pr.1"), "r"); ((TAtom "iw_3.v0"), "c"); ((TAtom "iw_3.v10"), "r"); ((TAtom "iw_3.v11"), "r"); ((TAtom "iw_3.v7"), "c"); ((TAtom "iw_3.v8"), "r"); ((TAtom "iw_3.v9"), "c"); ((TAtom "iw_4.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_4.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_4.iw_1.v0"), "x"); ((TAtom "iw_4.iw_1.v12"), "msb"); ((TAtom "iw_4.iw_1.v3"), "lsb"); ((TAtom "iw_4.iw_1.v5"), "msb"); ((TAtom "iw_4.iw_1.v6"), "x"); ((TAtom "iw_4.iw_1.v7"), "lsb"); ((TAtom "iw_4.iw_1.v9"), "x"); ((TAtom "iw_4.v0"), "x"); ((TAtom "iw_4.v2"), "x"); ((TAtom "iw_5.iw_1.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v0"), "c_in"); ((TAtom "iw_5.iw_1.iw_2.v5"), "c_in"); ((TAtom "iw_5.iw_1.v0"), "x"); ((TAtom "iw_5.iw_1.v12"), "msb"); ((TAtom "iw_5.iw_1.v3"), "lsb"); ((TAtom "iw_5.iw_1.v5"), "msb"); ((TAtom "iw_5.iw_1.v6"), "x"); ((TAtom "iw_5.iw_1.v7"), "lsb"); ((TAtom "iw_5.iw_1.v9"), "x"); ((TAtom "iw_5.iw_2.iw_1.v0"), "c_in"); ((TAtom "iw_5.iw_2.iw_1.v5"), "c_in"); ((TAtom "iw_5.iw_2.v0"), "x"); ((TAtom "iw_5.iw_2.v11"), "m"); ((TAtom "iw_5.iw_2.v3"), "m"); ((TAtom "iw_5.iw_2.v4"), "x"); ((TAtom "iw_5.iw_2.v5"), "m"); ((TAtom "iw_5.iw_2.v7"), "m"); ((TAtom "iw_5.iw_2.v9"), "x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_2.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_3.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_1.iw_4.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_1.v0"), "c"); ((TAtom "iw_5.iw_3.iw_1.v12"), "c"); ((TAtom "iw_5.iw_3.iw_1.v18"), "c"); ((TAtom "iw_5.iw_3.iw_1.v21"), "c"); ((TAtom "iw_5.iw_3.iw_1.v6"), "c"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v0"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v5"), "__x"); ((TAtom "iw_5.iw_3.iw_2.iw_1.v7"), "__x"); ((TAtom "iw_5.iw_3.iw_2.v0"), "c"); ((TAtom "iw_5.iw_3.iw_2.v2"), "c"); ((TAtom "iw_5.iw_3.pr.1"), "r"); ((TAtom "iw_5.iw_3.v0"), "c"); ((TAtom "iw_5.iw_3.v10"), "r"); ((TAtom "iw_5.iw_3.v11"), "r"); ((TAtom "iw_5.iw_3.v7"), "c"); ((TAtom "iw_5.iw_3.v8"), "r"); ((TAtom "iw_5.iw_3.v9"), "c"); ((TAtom "iw_5.pr.1"), "x"); ((TAtom "iw_5.v0"), "x"); ((TAtom "iw_5.v10"), "x"); ((TAtom "iw_5.v6"), "x"); ((TAtom "iw_5.v7"), "x"); ((TAtom "iw_5.v8"), "x"); ((TAtom "iw_5.v9"), "x"); ((TAtom "pr.1"), "word_ptr"); ((TAtom "v0"), "str"); ((TAtom "v10"), "word_ptr"); ((TAtom "v12"), "word_ptr"); ((TAtom "v13"), "word"); ((TAtom "v15"), "word"); ((TAtom "v17"), "s_int"); ((TAtom "v18"), "mask"); ((TAtom "v22"), "mask"); ((TAtom "v24"), "mask"); ((TAtom "v3"), "str"); ((TAtom "v31"), "word_ptr"); ((TAtom "v32"), "word_ptr"); ((TAtom "v33"), "word"); ((TAtom "v34"), "word"); ((TAtom "v38"), "word_ptr"); ((TAtom "v39"), "word"); ((TAtom "v4"), "s_int"); ((TAtom "v43"), "str"); ((TAtom "v6"), "str")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L28")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [(TAtom "v32"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_2.v12"); (TAtom "v10"); (TAtom "v4")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_3.iw_1.iw_1.v22")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_5.iw_3.iw_1.iw_1.v22"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(5%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None, "opaque")]); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)), "opaque")]); ((TAtom "iw_5.start"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].


End fn___strlen.

Module fn___GI___mempcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_27, 32%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_27, 35%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dest"); ((TAtom "v10"), "len"); ((TAtom "v2"), "src"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dest"); ((TAtom "v7"), "src"); ((TAtom "v8"), "len")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___GI___mempcpy.

Module fn___GI_memcpy.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_26, 28%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_26, 37%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "dstpp"); ((TAtom "v2"), "srcpp"); ((TAtom "v4"), "len"); ((TAtom "v6"), "dstpp"); ((TAtom "v7"), "srcpp"); ((TAtom "v8"), "len"); ((TAtom "v9"), "dstpp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [])].


End fn___GI_memcpy.

End HiAtexitSrc08.

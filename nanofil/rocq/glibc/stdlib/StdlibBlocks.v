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


From Glibc Require Import StdlibSrc.
Module StdlibBlocks.

Module fn_malloc___libc_malloc2.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn_malloc___libc_malloc2.

Module fn___GI___libc_malloc.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "v0")]); ((TAtom "iw_1.L76"), [(TAtom "iw_1.v23"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.start"), [(TAtom "v42"); (TAtom "v57")]); ((TAtom "iw_2.iw_1.L22"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L38"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_3.start"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L4"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L18"), [(TAtom "iw_3.v38"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L25"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L26"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.join"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.start"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L7"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L8"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L9"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L22"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L24"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L38"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L39"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L40"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.join"), [(TAtom "iw_4.iw_1.v23"); (TAtom "v0")]); ((TAtom "L72"), [(TAtom "v71")]); ((TAtom "L7"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "iw_1.v23"); (TAtom "v0")]); ((TAtom "iw_1.L76"), [(TAtom "iw_1.v83"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v4"); (TAtom "v42")]); ((TAtom "L43"), [(TAtom "v0"); (TAtom "v42"); (TAtom "v57")]); ((TAtom "iw_2.start"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L22"), [(TAtom "chk4"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_2.iw_1.v26"); (TAtom "iw_2.v8"); (TAtom "v42")]); ((TAtom "iw_2.iw_1.L38"), []); ((TAtom "iw_3.start"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_3.iw_1.iw_1.v33"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_3.iw_1.iw_1.L4"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v14"); (TAtom "iw_4.iw_1.v17"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L25"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_1.v38"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L26"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v22"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v51"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.iw_1.join"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.pr.2"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_4.L18"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "iw_4.v31"); (TAtom "v0")]); ((TAtom "iw_4.L19"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.start"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L7"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.v13"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L8"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.v21"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L9"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L22"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "iw_4.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L24"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.pr.1"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "iw_4.iw_2.v26"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L38"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L39"), [(TAtom "iw_3.v38"); (TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.iw_2.L40"), [(TAtom "iw_4.iw_1.v23"); (TAtom "iw_4.iw_2.pr.1"); (TAtom "v0")]); ((TAtom "iw_4.join"), [(TAtom "v0"); (TAtom "v71")]); ((TAtom "L72"), []); ((TAtom "L7"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.L76"), []); ((TAtom "iw_1.join"), [(3%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v9")), (Some (120)))]); ((TAtom "L26"), []); ((TAtom "L43"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v53")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v54")), None)]); ((TAtom "iw_2.start"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v3")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "iw_2.v8")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v4")), None)]); ((TAtom "iw_2.iw_1.L22"), []); ((TAtom "iw_2.iw_1.L38"), [(2%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v13")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.iw_1.v13")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "iw_2.v8")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v4")), None); (10%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v67")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.iw_1.v67")), (Some (0))); (14%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v71")]), (0), (Some 2), true, false, (Some (TAtom "iw_2.iw_1.v68")), None); (18%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v71")]), (0), (Some 2), false, true, (Some (TAtom "iw_2.iw_1.v68")), None); (21%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v76")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.iw_1.v13")), (Some (8)))]); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_3.iw_1.iw_1.L4"), [(6%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v9")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.v9")), (Some (0))); (11%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v14")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.v10")), None)]); ((TAtom "iw_4.iw_1.L18"), []); ((TAtom "iw_4.iw_1.L25"), [(3%N, (TApp "tmp" [(TAtom "iw_4.iw_1.v30")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (-8)))]); ((TAtom "iw_4.iw_1.L26"), []); ((TAtom "iw_4.iw_1.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.2")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (0)))]); ((TAtom "iw_4.iw_1.join"), []); ((TAtom "iw_4.L18"), [(3%N, (TApp "tmp" [(TAtom "iw_4.v24")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.2")), (Some (-8)))]); ((TAtom "iw_4.L19"), []); ((TAtom "iw_4.iw_2.start"), []); ((TAtom "iw_4.iw_2.L7"), [(1%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L8"), [(3%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L9"), []); ((TAtom "iw_4.iw_2.L22"), []); ((TAtom "iw_4.iw_2.L24"), []); ((TAtom "iw_4.iw_2.L38"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L39"), [(4%N, (TApp "tmp" [(TAtom "iw_4.iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "iw_4.iw_1.pr.1")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_1.pr.1")), (Some (0)))]); ((TAtom "iw_4.iw_2.L40"), [(2%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v67")]), (0), (Some 8), true, false, (Some (TAtom "iw_4.iw_2.v67")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v71")]), (0), (Some 2), true, false, (Some (TAtom "iw_4.iw_2.v68")), None); (10%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v71")]), (0), (Some 2), false, true, (Some (TAtom "iw_4.iw_2.v68")), None); (13%N, (TApp "tmp" [(TAtom "iw_4.iw_2.v76")]), (0), (Some 8), false, true, (Some (TAtom "iw_4.iw_2.pr.1")), (Some (8)))]); ((TAtom "iw_4.join"), []); ((TAtom "L72"), []); ((TAtom "L7"), [])].

End fn___GI___libc_malloc.

Module fn___GI___libc_free.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___libc_free.

Module fn___libc_calloc.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L41"), [(TAtom "v10")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v10")]); ((TAtom "L5"), []); ((TAtom "L41"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L5"), [(2%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 4), false, true, (Some (TAtom "v39")), (Some (0)))]); ((TAtom "L41"), [])].

End fn___libc_calloc.

Module fn_malloc_malloc_printerr.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn_malloc_malloc_printerr.

Module fn___internal_atexit.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L46"), []); ((TAtom "L59"), [(TAtom "chk1"); (TAtom "v54")]); ((TAtom "L60"), [(TAtom "v54"); (TAtom "v61")]); ((TAtom "L71"), [(TAtom "v54")]); ((TAtom "L66"), []); ((TAtom "L48"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L103"), [(TAtom "chk7"); (TAtom "v98")]); ((TAtom "L104"), [(TAtom "v105"); (TAtom "v98")]); ((TAtom "L115"), [(TAtom "v98")]); ((TAtom "L110"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L29"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v27"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L30"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v20"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v14"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L23"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L46"), [(TAtom "chk1"); (TAtom "v54"); (TAtom "v58")]); ((TAtom "L59"), [(TAtom "chk1"); (TAtom "v54"); (TAtom "v61"); (TAtom "v62")]); ((TAtom "L60"), [(TAtom "v54")]); ((TAtom "L71"), []); ((TAtom "L66"), []); ((TAtom "L48"), [(TAtom "chk7"); (TAtom "v102"); (TAtom "v98")]); ((TAtom "L103"), [(TAtom "chk7"); (TAtom "v105"); (TAtom "v106"); (TAtom "v98")]); ((TAtom "L104"), [(TAtom "v98")]); ((TAtom "L115"), []); ((TAtom "L110"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 4), true, true, (Some (TAtom "v20")), (Some (0)))]); ((TAtom "L29"), []); ((TAtom "L30"), []); ((TAtom "L34"), []); ((TAtom "L23"), []); ((TAtom "L46"), [(2%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), true, false, (Some (TAtom "v54")), (Some (0)))]); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), true, true, (Some (TAtom "v54")), (Some (0)))]); ((TAtom "L60"), []); ((TAtom "L71"), []); ((TAtom "L66"), []); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v86")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (16))); (8%N, (TApp "tmp" [(TAtom "v94")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (24))); (10%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), false, true, (Some (TAtom "v45")), (Some (0))); (13%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, false, (Some (TAtom "v98")), (Some (0)))]); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, true, (Some (TAtom "v98")), (Some (0)))]); ((TAtom "L104"), []); ((TAtom "L115"), []); ((TAtom "L110"), [])].

End fn___internal_atexit.

Module fn___GI___cxa_atexit.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___cxa_atexit.

Module fn___new_exitfn.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk1"); (TAtom "v0")]); ((TAtom "L15"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L28"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L47"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0")]); ((TAtom "L17"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L63"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L64"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L70"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L78"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L88"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v87")]); ((TAtom "L72"), [(TAtom "v20")]); ((TAtom "L100"), [(TAtom "pr.2"); (TAtom "v20")]); ((TAtom "L57"), [(TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v20")]); ((TAtom "L58"), [(TAtom "v20")]); ((TAtom "L121"), [(TAtom "pr.5")]); ((TAtom "L123"), [(TAtom "pr.5")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v13")]); ((TAtom "L14"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.6"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L15"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v24")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21"); (TAtom "v30"); (TAtom "v37")]); ((TAtom "L28"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v19"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L47"), [(TAtom "chk1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v55")]); ((TAtom "L17"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L63"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21"); (TAtom "v67")]); ((TAtom "L64"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.7"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L56"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v21")]); ((TAtom "L70"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L78"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20")]); ((TAtom "L79"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v20"); (TAtom "v87")]); ((TAtom "L88"), [(TAtom "v20"); (TAtom "v87")]); ((TAtom "L72"), [(TAtom "pr.2"); (TAtom "v20")]); ((TAtom "L100"), [(TAtom "v108"); (TAtom "v20")]); ((TAtom "L57"), [(TAtom "v116"); (TAtom "v20")]); ((TAtom "L58"), [(TAtom "pr.5")]); ((TAtom "L121"), [(TAtom "pr.5")]); ((TAtom "L123"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 1), true, false, (Some (TAtom "v9")), (Some (0)))]); ((TAtom "L6"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L14"), []); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), (Some (8)))]); ((TAtom "L25"), []); ((TAtom "L26"), [(5%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), None)]); ((TAtom "L28"), []); ((TAtom "L47"), [(2%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 8), false, true, (Some (TAtom "pr.3")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "pr.3")]), (0), (Some 8), true, false, (Some (TAtom "pr.3")), (Some (0)))]); ((TAtom "L17"), []); ((TAtom "L63"), []); ((TAtom "L64"), []); ((TAtom "L56"), []); ((TAtom "L70"), []); ((TAtom "L78"), []); ((TAtom "L79"), []); ((TAtom "L88"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0))); (3%N, (TApp "tmp" [(TAtom "v87")]), (0), (Some 8), false, true, (Some (TAtom "v87")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L72"), []); ((TAtom "L100"), [(3%N, (TApp "tmp" [(TAtom "v111")]), (0), (Some 8), false, true, (Some (TAtom "pr.2")), (Some (8)))]); ((TAtom "L57"), [(6%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 8), false, true, (Some (TAtom "pr.3")), (Some (8)))]); ((TAtom "L58"), []); ((TAtom "L121"), [(1%N, (TApp "tmp" [(TAtom "pr.5")]), (0), (Some 8), false, true, (Some (TAtom "pr.5")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 8), true, false, (Some (TAtom "v129")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 8), false, true, (Some (TAtom "v129")), (Some (0)))]); ((TAtom "L123"), [])].

End fn___new_exitfn.

Module fn_atexit.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn_atexit.

Module fn___GI___errno_location.

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

End fn___GI___errno_location.

Module fn___mbsinit.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "v0")]); ((TAtom "L7"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "v10")]); ((TAtom "L7"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L6"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L7"), [])].

End fn___mbsinit.

Module fn___iswprint.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.start"), [(TAtom "v0")]); ((TAtom "L4"), [(TAtom "v0")]); ((TAtom "iw_2.L16"), [(TAtom "chk8"); (TAtom "iw_2.v11"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.L30"), [(TAtom "chk8"); (TAtom "iw_2.v29"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.L59"), [(TAtom "chk8"); (TAtom "iw_2.v58"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.join"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.start"), []); ((TAtom "L4"), [(TAtom "chk8"); (TAtom "iw_2.v11"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.L16"), [(TAtom "chk8"); (TAtom "iw_2.v29"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.L30"), [(TAtom "chk8"); (TAtom "iw_2.v58"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "iw_2.L59"), [(TAtom "iw_2.v87")]); ((TAtom "iw_2.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "iw_1.start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v0")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 2), true, false, (Some (TAtom "v10")), None)]); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), true, false, (Some (TAtom "v19")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v20")), (Some (0))); (8%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 4), true, false, (Some (TAtom "v22")), (Some (192))); (13%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "v32")), (Some (0))); (15%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v33")), (Some (0))); (22%N, (TApp "tmp" [(TAtom "v41")]), (0), (Some 8), true, false, (Some (TAtom "v35")), None); (24%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 4), true, false, (Some (TAtom "v42")), (Some (0))); (28%N, (TApp "tmp" [(TAtom "iw_2.v14")]), (0), (Some 4), true, false, (Some (TAtom "v42")), (Some (4)))]); ((TAtom "iw_2.L16"), [(5%N, (TApp "tmp" [(TAtom "iw_2.v28")]), (0), (Some 4), true, false, (Some (TAtom "v42")), None)]); ((TAtom "iw_2.L30"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v37")]), (0), (Some 4), true, false, (Some (TAtom "v42")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 4), true, false, (Some (TAtom "v42")), (Some (12))); (14%N, (TApp "tmp" [(TAtom "iw_2.v57")]), (0), (Some 4), true, false, (Some (TAtom "v42")), None)]); ((TAtom "iw_2.L59"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v66")]), (0), (Some 4), true, false, (Some (TAtom "v42")), (Some (16))); (11%N, (TApp "tmp" [(TAtom "iw_2.v81")]), (0), (Some 4), true, false, (Some (TAtom "v42")), None)]); ((TAtom "iw_2.join"), [])].

End fn___iswprint.

Module fn___ctype_b_loc.

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

End fn___ctype_b_loc.

Module fn___ctype_get_mb_cur_max.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), true, false, (Some (TAtom "v1")), (Some (0))); (8%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (160)))])].

End fn___ctype_get_mb_cur_max.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("malloc#__libc_malloc2", app (map fst fn_malloc___libc_malloc2.live_in) (app (map fst fn_malloc___libc_malloc2.live_out) (map fst fn_malloc___libc_malloc2.footprint))); ("__GI___libc_malloc", app (map fst fn___GI___libc_malloc.live_in) (app (map fst fn___GI___libc_malloc.live_out) (map fst fn___GI___libc_malloc.footprint))); ("__GI___libc_free", app (map fst fn___GI___libc_free.live_in) (app (map fst fn___GI___libc_free.live_out) (map fst fn___GI___libc_free.footprint))); ("__libc_calloc", app (map fst fn___libc_calloc.live_in) (app (map fst fn___libc_calloc.live_out) (map fst fn___libc_calloc.footprint))); ("malloc#malloc_printerr", app (map fst fn_malloc_malloc_printerr.live_in) (app (map fst fn_malloc_malloc_printerr.live_out) (map fst fn_malloc_malloc_printerr.footprint))); ("__internal_atexit", app (map fst fn___internal_atexit.live_in) (app (map fst fn___internal_atexit.live_out) (map fst fn___internal_atexit.footprint))); ("__GI___cxa_atexit", app (map fst fn___GI___cxa_atexit.live_in) (app (map fst fn___GI___cxa_atexit.live_out) (map fst fn___GI___cxa_atexit.footprint))); ("__new_exitfn", app (map fst fn___new_exitfn.live_in) (app (map fst fn___new_exitfn.live_out) (map fst fn___new_exitfn.footprint))); ("atexit", app (map fst fn_atexit.live_in) (app (map fst fn_atexit.live_out) (map fst fn_atexit.footprint))); ("__GI___errno_location", app (map fst fn___GI___errno_location.live_in) (app (map fst fn___GI___errno_location.live_out) (map fst fn___GI___errno_location.footprint))); ("__mbsinit", app (map fst fn___mbsinit.live_in) (app (map fst fn___mbsinit.live_out) (map fst fn___mbsinit.footprint))); ("__iswprint", app (map fst fn___iswprint.live_in) (app (map fst fn___iswprint.live_out) (map fst fn___iswprint.footprint))); ("__ctype_b_loc", app (map fst fn___ctype_b_loc.live_in) (app (map fst fn___ctype_b_loc.live_out) (map fst fn___ctype_b_loc.footprint))); ("__ctype_get_mb_cur_max", app (map fst fn___ctype_get_mb_cur_max.live_in) (app (map fst fn___ctype_get_mb_cur_max.live_out) (map fst fn___ctype_get_mb_cur_max.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) StdlibSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End StdlibBlocks.

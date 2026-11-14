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


Module GetoptBlocks03.

Module fn__getopt_internal.

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

End GetoptBlocks03.

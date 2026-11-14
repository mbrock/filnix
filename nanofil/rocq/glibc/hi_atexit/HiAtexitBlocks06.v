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


Module HiAtexitBlocks06.

Module fn__IO_switch_to_main_get_area.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (10%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (12%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16))); (14%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88))); (17%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (20%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (22%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (24%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (72))); (27%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (29%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))])].

End fn__IO_switch_to_main_get_area.

Module fn__IO_switch_to_backup_area.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0))); (7%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (10%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (12%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16))); (14%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88))); (17%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (20%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (22%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (24%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (72))); (27%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (29%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))])].

End fn__IO_switch_to_backup_area.

Module fn___GI__IO_switch_to_get_mode.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v19")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v19")]); ((TAtom "L14"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "v0")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "v0")]); ((TAtom "L46"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk10"); (TAtom "chk11"); (TAtom "chk5"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v19")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v19")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L14"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "v0")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "v0")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk10"); (TAtom "chk11"); (TAtom "chk5"); (TAtom "v0")]); ((TAtom "L46"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "v0")]); ((TAtom "L32"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L2"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v19")), (Some (24)))]); ((TAtom "L14"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L30"), [(3%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80))); (5%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L31"), [(3%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (8%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (11%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L46"), [(2%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (4%N, (TApp "tmp" [(TAtom "v59")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L32"), [(3%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (9%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (11%N, (TApp "tmp" [(TAtom "v73")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (48))); (13%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40))); (15%N, (TApp "tmp" [(TAtom "v69")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (32))); (17%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (20%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))])].

End fn___GI__IO_switch_to_get_mode.

Module fn___GI__IO_free_backup_area.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v12")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v12")]); ((TAtom "iw_1.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72)))]); ((TAtom "iw_1.L4"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (72))); (5%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88))); (8%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (80)))])].

End fn___GI__IO_free_backup_area.

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

Module fn_glibc_genops_save_for_backup.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_1.L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L26"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17")]); ((TAtom "L42"), []); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L52"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L53"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "iw_2.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41"); (TAtom "v91")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v27")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104")]); ((TAtom "L106"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L141"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "L175"), [(TAtom "iw_1.v22"); (TAtom "v171")]); ((TAtom "L176"), [(TAtom "iw_1.v22"); (TAtom "pr.2"); (TAtom "v171")]); ((TAtom "L178"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v11"); (TAtom "iw_1.v15"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L17"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L24"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.v36"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.L26"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.pr.2"); (TAtom "iw_1.v38"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v27")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L42"), []); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L52"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "L53"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41"); (TAtom "v91")]); ((TAtom "iw_2.L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk12"); (TAtom "chk6"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v17"); (TAtom "v41")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104")]); ((TAtom "L106"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk5"); (TAtom "chk6"); (TAtom "iw_1.pr.1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104"); (TAtom "v17")]); ((TAtom "L141"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "iw_1.v22"); (TAtom "iw_1.v9"); (TAtom "v0"); (TAtom "v104")]); ((TAtom "L33"), [(TAtom "iw_1.v22"); (TAtom "v171"); (TAtom "v174")]); ((TAtom "L175"), [(TAtom "iw_1.v22"); (TAtom "pr.2"); (TAtom "v171")]); ((TAtom "L176"), [(TAtom "iw_1.v22"); (TAtom "v171"); (TAtom "v190")]); ((TAtom "L178"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (8%N, (TApp "tmp" [(TAtom "iw_1.v14")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "iw_1.L16"), []); ((TAtom "iw_1.L17"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v28")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.3")), (Some (16)))]); ((TAtom "iw_1.L24"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v28")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.pr.3")), (Some (16)))]); ((TAtom "iw_1.L26"), [(1%N, (TApp "tmp" [(TAtom "iw_1.pr.3")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.3")), (Some (0)))]); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (8%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (10%N, (TApp "tmp" [(TAtom "v20")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72)))]); ((TAtom "L31"), []); ((TAtom "L42"), []); ((TAtom "L44"), []); ((TAtom "L51"), [(3%N, (TApp "tmp" [(TAtom "v60")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (9%N, (TApp "tmp" [(TAtom "v68")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (10%N, (TApp "tmp" [(TAtom "v68")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L52"), [(3%N, (TApp "tmp" [(TAtom "v82")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L53"), [(2%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72)))]); ((TAtom "iw_2.L4"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v93")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (72))); (7%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (88)))]); ((TAtom "L32"), []); ((TAtom "L105"), [(1%N, (TApp "tmp" [(TAtom "v20")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (4%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (88))); (9%N, (TApp "tmp" [(TAtom "v111")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (14%N, (TApp "tmp" [(TAtom "v131")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (15%N, (TApp "tmp" [(TAtom "v131")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L106"), []); ((TAtom "L141"), [(1%N, (TApp "tmp" [(TAtom "v20")]), (-16), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (4%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L33"), [(3%N, (TApp "tmp" [(TAtom "v161")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (72))); (6%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (80))); (9%N, (TApp "tmp" [(TAtom "v167")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (14%N, (TApp "tmp" [(TAtom "v173")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L175"), []); ((TAtom "L176"), [(2%N, (TApp "tmp" [(TAtom "v184")]), (0), (Some 4), true, false, (Some (TAtom "pr.2")), (Some (16))); (6%N, (TApp "tmp" [(TAtom "v184")]), (0), (Some 4), false, true, (Some (TAtom "pr.2")), (Some (16))); (8%N, (TApp "tmp" [(TAtom "pr.2")]), (0), (Some 8), true, false, (Some (TAtom "pr.2")), (Some (0)))]); ((TAtom "L178"), [])].

End fn_glibc_genops_save_for_backup.

Module fn___GI___underflow.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L69"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L113"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L119"), []); ((TAtom "L115"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L128"), [(TAtom "chk8"); (TAtom "v0")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L152"), [(TAtom "chk13"); (TAtom "v0")]); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L169"), [(TAtom "chk0"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L178"), []); ((TAtom "L170"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v176")]); ((TAtom "L188"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L171"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v200")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v200")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L69"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L79"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L81"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L113"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "v0")]); ((TAtom "L119"), []); ((TAtom "L115"), [(TAtom "chk0"); (TAtom "chk7"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L128"), []); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "chk0"); (TAtom "chk13"); (TAtom "chk9"); (TAtom "v0")]); ((TAtom "L152"), []); ((TAtom "L147"), [(TAtom "chk0"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v176")]); ((TAtom "L169"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L178"), []); ((TAtom "L170"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L188"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L171"), [(TAtom "v0"); (TAtom "v200")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v200")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L20"), [(2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L22"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L69"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L79"), [(2%N, (TApp "tmp" [(TAtom "v87")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L81"), [(1%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L62"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L113"), []); ((TAtom "L119"), []); ((TAtom "L115"), [(2%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v135")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L128"), [(1%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (3%N, (TApp "tmp" [(TAtom "v142")]), (0), (Some 1), true, false, (Some (TAtom "v142")), (Some (0)))]); ((TAtom "L130"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L145"), [(3%N, (TApp "tmp" [(TAtom "v156")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L152"), [(1%N, (TApp "tmp" [(TAtom "v156")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (3%N, (TApp "tmp" [(TAtom "v166")]), (0), (Some 1), true, false, (Some (TAtom "v166")), (Some (0)))]); ((TAtom "L147"), [(2%N, (TApp "tmp" [(TAtom "v173")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L169"), [(2%N, (TApp "tmp" [(TAtom "v183")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L178"), []); ((TAtom "L170"), [(2%N, (TApp "tmp" [(TAtom "v192")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L188"), []); ((TAtom "L171"), [(2%N, (TApp "tmp" [(TAtom "v199")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 8), true, false, (Some (TAtom "v200")), (Some (32)))])].

End fn___GI___underflow.

Module fn___GI__IO_setb.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L35"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v21"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L33"), []); ((TAtom "L34"), []); ((TAtom "L35"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L16"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L17"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (64)))]); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L34"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L35"), [])].

End fn___GI__IO_setb.

Module fn___GI__IO_doallocbuf.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "L26"), []); ((TAtom "L13"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L26"), []); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L18"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L19"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v31")), (Some (104)))]); ((TAtom "L26"), []); ((TAtom "L13"), [])].

End fn___GI__IO_doallocbuf.

Module fn___GI__IO_default_uflow.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "L11"), []); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v5")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), []); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v5")), (Some (32)))]); ((TAtom "L11"), []); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 1), true, false, (Some (TAtom "v21")), (Some (0)))])].

End fn___GI__IO_default_uflow.

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

Module fn___GI__IO_default_xsgetn.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v35"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v74")]); ((TAtom "L72"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L45"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L92"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L93"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "pr.2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v35"); (TAtom "v4")]); ((TAtom "L37"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v35"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4"); (TAtom "v53")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.3"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4"); (TAtom "v67")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "pr.9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v74")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4"); (TAtom "v74"); (TAtom "v77"); (TAtom "v79")]); ((TAtom "L72"), [(TAtom "pr.1"); (TAtom "pr.7"); (TAtom "pr.8"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L45"), [(TAtom "pr.5"); (TAtom "v0"); (TAtom "v4"); (TAtom "v86")]); ((TAtom "L16"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L92"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v97")]); ((TAtom "L93"), [(TAtom "pr.2"); (TAtom "pr.4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L14"), [(1%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (3%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L37"), []); ((TAtom "L38"), []); ((TAtom "L43"), [(1%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L44"), []); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L70"), []); ((TAtom "L71"), [(3%N, (TApp "tmp" [(TAtom "pr.9")]), (0), (Some 1), true, false, (Some (TAtom "pr.9")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "pr.7")]), (0), (Some 1), false, true, (Some (TAtom "pr.7")), (Some (0)))]); ((TAtom "L72"), [(2%N, (TApp "tmp" [(TAtom "v82")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L45"), []); ((TAtom "L16"), []); ((TAtom "L92"), []); ((TAtom "L93"), []); ((TAtom "L13"), [])].

End fn___GI__IO_default_xsgetn.

Module fn__IO_default_setbuf.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L21"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v30"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (96)))]); ((TAtom "L6"), []); ((TAtom "L8"), []); ((TAtom "L27"), []); ((TAtom "L28"), []); ((TAtom "L20"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L21"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L22"), [(4%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (48))); (6%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40))); (8%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (32))); (13%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16))); (15%N, (TApp "tmp" [(TAtom "v60")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (17%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24)))])].

End fn__IO_default_setbuf.

Module fn__IO_default_seekpos.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v8")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v8")), (Some (72)))])].

End fn__IO_default_seekpos.

Module fn___GI__IO_default_doallocate.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L4"), []); ((TAtom "L6"), [(TAtom "v0"); (TAtom "v3")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v3")]); ((TAtom "L4"), []); ((TAtom "L6"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L4"), []); ((TAtom "L6"), [])].

End fn___GI__IO_default_doallocate.

Module fn__IO_default_sync.

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

End fn__IO_default_sync.

Module fn___GI__IO_default_finish.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L45"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L55"), []); ((TAtom "L56"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v18")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v30")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v42")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L45"), []); ((TAtom "L55"), []); ((TAtom "L56"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L13"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L14"), []); ((TAtom "L5"), [(1%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (64))); (7%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L7"), [(2%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (96)))]); ((TAtom "L31"), []); ((TAtom "L32"), [(2%N, (TApp "tmp" [(TAtom "v40")]), (0), (Some 8), false, true, (Some (TAtom "pr.1")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L34"), [(2%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L43"), []); ((TAtom "L45"), [(3%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136)))]); ((TAtom "L55"), []); ((TAtom "L56"), [])].

End fn___GI__IO_default_finish.

Module fn___GI__IO_adjust_column.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L19"), [(TAtom "v10"); (TAtom "v23")]); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L11"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v23"); (TAtom "v4")]); ((TAtom "L19"), []); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L11"), []); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 1), true, false, (Some (TAtom "pr.1")), (Some (-1)))]); ((TAtom "L19"), []); ((TAtom "L13"), [])].

End fn___GI__IO_adjust_column.

End HiAtexitBlocks06.

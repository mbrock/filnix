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


From Glibc Require Import PrintfBufferFileSrc.
Module PrintfBufferFileBlocks.

Module fn___printf_buffer_to_file_switch.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L4"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v7")), (Some (40))); (6%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (9%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (48)))]); ((TAtom "L2"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 8), true, false, (Some (TAtom "v22")), (Some (40))); (7%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (10%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (13%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), true, false, (Some (TAtom "v29")), (Some (48))); (15%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L3"), [(3%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v46")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)))])].

End fn___printf_buffer_to_file_switch.

Module fn___printf_buffer_flush_to_file.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L40"), [(TAtom "v0")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L88"), [(TAtom "v0")]); ((TAtom "L76"), []); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L104"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L105"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L127"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "chk25"); (TAtom "v0")]); ((TAtom "L129"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v37"); (TAtom "v45")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.start"), []); ((TAtom "L40"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L62"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_3.start"), []); ((TAtom "L88"), []); ((TAtom "L76"), []); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L104"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk19"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L105"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "chk25"); (TAtom "v0")]); ((TAtom "L127"), [(TAtom "chk1"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L129"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (5%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0))); (13%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (15%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L14"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (8%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (11%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v43")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), true, false, (Some (TAtom "v45")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v50")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)))]); ((TAtom "iw_2.start"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v3")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L40"), []); ((TAtom "L15"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L62"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (3%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L74"), [(2%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v93")]), (0), (Some 1), true, false, (Some (TAtom "v0")), (Some (48)))]); ((TAtom "iw_3.start"), [(2%N, (TApp "tmp" [(TAtom "iw_3.v3")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L88"), []); ((TAtom "L76"), []); ((TAtom "L16"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (4%N, (TApp "tmp" [(TAtom "v110")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (7%N, (TApp "tmp" [(TAtom "v112")]), (0), (Some 8), true, false, (Some (TAtom "v111")), (Some (48)))]); ((TAtom "L104"), []); ((TAtom "L105"), [(2%N, (TApp "tmp" [(TAtom "v121")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (6%N, (TApp "tmp" [(TAtom "v125")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (8%N, (TApp "tmp" [(TAtom "v123")]), (0), (Some 8), false, true, (Some (TAtom "v122")), (Some (40))); (10%N, (TApp "tmp" [(TAtom "v125")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (13%N, (TApp "tmp" [(TAtom "v134")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L127"), [(3%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v144")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L129"), [(2%N, (TApp "tmp" [(TAtom "v150")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0)))])].

End fn___printf_buffer_flush_to_file.

Module fn___printf_buffer_to_file_init.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v11")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8))); (9%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v14")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16))); (12%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v17")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (15%N, (TApp "tmp" [(TAtom "iw_1.iw_1.v19")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32))); (18%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (40)))])].

End fn___printf_buffer_to_file_init.

Module fn___printf_buffer_to_file_done.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L2"), []); ((TAtom "L4"), [])].

End fn___printf_buffer_to_file_done.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__printf_buffer_to_file_switch", app (map fst fn___printf_buffer_to_file_switch.live_in) (app (map fst fn___printf_buffer_to_file_switch.live_out) (map fst fn___printf_buffer_to_file_switch.footprint))); ("__printf_buffer_flush_to_file", app (map fst fn___printf_buffer_flush_to_file.live_in) (app (map fst fn___printf_buffer_flush_to_file.live_out) (map fst fn___printf_buffer_flush_to_file.footprint))); ("__printf_buffer_to_file_init", app (map fst fn___printf_buffer_to_file_init.live_in) (app (map fst fn___printf_buffer_to_file_init.live_out) (map fst fn___printf_buffer_to_file_init.footprint))); ("__printf_buffer_to_file_done", app (map fst fn___printf_buffer_to_file_done.live_in) (app (map fst fn___printf_buffer_to_file_done.live_out) (map fst fn___printf_buffer_to_file_done.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) PrintfBufferFileSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfBufferFileBlocks.

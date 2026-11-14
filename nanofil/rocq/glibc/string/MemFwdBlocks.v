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


From Glibc Require Import MemFwdSrc.
Module MemFwdBlocks.

Module fn___GI_memcpy.

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

End fn___GI_memcpy.

Module fn___GI___mempcpy.

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

End fn___GI___mempcpy.

Module fn___GI_memset.

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

End fn___GI_memset.

Module fn___GI___strdup.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L9"), []); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v5"); (TAtom "v8")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v5"); (TAtom "v8")]); ((TAtom "L9"), []); ((TAtom "L11"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L9"), []); ((TAtom "L11"), [])].

End fn___GI___strdup.

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

Module fn___GI___towlower.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L16"), [(TAtom "chk6"); (TAtom "iw_1.v11"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L30"), [(TAtom "chk6"); (TAtom "iw_1.v29"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L59"), [(TAtom "chk6"); (TAtom "iw_1.v58"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.join"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk6"); (TAtom "iw_1.v11"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L16"), [(TAtom "chk6"); (TAtom "iw_1.v29"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L30"), [(TAtom "chk6"); (TAtom "iw_1.v58"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L59"), [(TAtom "iw_1.v84")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (0))); (8%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v6")), (Some (200))); (13%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (0))); (15%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v17")), (Some (0))); (22%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v19")), None); (24%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (0))); (28%N, (TApp "tmp" [(TAtom "iw_1.v14")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (4)))]); ((TAtom "iw_1.L16"), [(5%N, (TApp "tmp" [(TAtom "iw_1.v28")]), (0), (Some 4), true, false, (Some (TAtom "v26")), None)]); ((TAtom "iw_1.L30"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v37")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "iw_1.v41")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (12))); (14%N, (TApp "tmp" [(TAtom "iw_1.v57")]), (0), (Some 4), true, false, (Some (TAtom "v26")), None)]); ((TAtom "iw_1.L59"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v66")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (16))); (10%N, (TApp "tmp" [(TAtom "iw_1.v80")]), (0), (Some 4), true, false, (Some (TAtom "v26")), None)]); ((TAtom "iw_1.join"), [])].

End fn___GI___towlower.

Module fn___GI___towupper.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_1.L16"), [(TAtom "chk6"); (TAtom "iw_1.v11"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L30"), [(TAtom "chk6"); (TAtom "iw_1.v29"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L59"), [(TAtom "chk6"); (TAtom "iw_1.v58"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.join"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk6"); (TAtom "iw_1.v11"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L16"), [(TAtom "chk6"); (TAtom "iw_1.v29"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L30"), [(TAtom "chk6"); (TAtom "iw_1.v58"); (TAtom "v0"); (TAtom "v26")]); ((TAtom "iw_1.L59"), [(TAtom "iw_1.v84")]); ((TAtom "iw_1.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (0))); (8%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v6")), (Some (200))); (12%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (0))); (14%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v17")), (Some (0))); (21%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v19")), None); (23%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (0))); (27%N, (TApp "tmp" [(TAtom "iw_1.v14")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (4)))]); ((TAtom "iw_1.L16"), [(5%N, (TApp "tmp" [(TAtom "iw_1.v28")]), (0), (Some 4), true, false, (Some (TAtom "v26")), None)]); ((TAtom "iw_1.L30"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v37")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "iw_1.v41")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (12))); (14%N, (TApp "tmp" [(TAtom "iw_1.v57")]), (0), (Some 4), true, false, (Some (TAtom "v26")), None)]); ((TAtom "iw_1.L59"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v66")]), (0), (Some 4), true, false, (Some (TAtom "v26")), (Some (16))); (10%N, (TApp "tmp" [(TAtom "iw_1.v80")]), (0), (Some 4), true, false, (Some (TAtom "v26")), None)]); ((TAtom "iw_1.join"), [])].

End fn___GI___towupper.

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

Module fn___ctype_toupper_loc.

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

End fn___ctype_toupper_loc.

Module fn___ctype_tolower_loc.

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

End fn___ctype_tolower_loc.

Module fn___GI___ctype_init.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v1")]), (0), (Some 8), true, false, (Some (TAtom "v1")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0))); (8%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56))); (11%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (0))); (15%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), true, false, (Some (TAtom "v13")), (Some (0))); (17%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 8), true, false, (Some (TAtom "v14")), (Some (0))); (21%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (64))); (24%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), false, true, (Some (TAtom "v12")), (Some (0))); (28%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v25")), (Some (0))); (30%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), true, false, (Some (TAtom "v26")), (Some (0))); (34%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v28")), (Some (80))); (37%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), false, true, (Some (TAtom "v24")), (Some (0)))])].

End fn___GI___ctype_init.

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
  [("__GI_memcpy", app (map fst fn___GI_memcpy.live_in) (app (map fst fn___GI_memcpy.live_out) (map fst fn___GI_memcpy.footprint))); ("__GI___mempcpy", app (map fst fn___GI___mempcpy.live_in) (app (map fst fn___GI___mempcpy.live_out) (map fst fn___GI___mempcpy.footprint))); ("__GI_memset", app (map fst fn___GI_memset.live_in) (app (map fst fn___GI_memset.live_out) (map fst fn___GI_memset.footprint))); ("__GI___strdup", app (map fst fn___GI___strdup.live_in) (app (map fst fn___GI___strdup.live_out) (map fst fn___GI___strdup.footprint))); ("__GI___errno_location", app (map fst fn___GI___errno_location.live_in) (app (map fst fn___GI___errno_location.live_out) (map fst fn___GI___errno_location.footprint))); ("__mbsinit", app (map fst fn___mbsinit.live_in) (app (map fst fn___mbsinit.live_out) (map fst fn___mbsinit.footprint))); ("__GI___towlower", app (map fst fn___GI___towlower.live_in) (app (map fst fn___GI___towlower.live_out) (map fst fn___GI___towlower.footprint))); ("__GI___towupper", app (map fst fn___GI___towupper.live_in) (app (map fst fn___GI___towupper.live_out) (map fst fn___GI___towupper.footprint))); ("__ctype_b_loc", app (map fst fn___ctype_b_loc.live_in) (app (map fst fn___ctype_b_loc.live_out) (map fst fn___ctype_b_loc.footprint))); ("__ctype_toupper_loc", app (map fst fn___ctype_toupper_loc.live_in) (app (map fst fn___ctype_toupper_loc.live_out) (map fst fn___ctype_toupper_loc.footprint))); ("__ctype_tolower_loc", app (map fst fn___ctype_tolower_loc.live_in) (app (map fst fn___ctype_tolower_loc.live_out) (map fst fn___ctype_tolower_loc.footprint))); ("__GI___ctype_init", app (map fst fn___GI___ctype_init.live_in) (app (map fst fn___GI___ctype_init.live_out) (map fst fn___GI___ctype_init.footprint))); ("__ctype_get_mb_cur_max", app (map fst fn___ctype_get_mb_cur_max.live_in) (app (map fst fn___ctype_get_mb_cur_max.live_out) (map fst fn___ctype_get_mb_cur_max.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) MemFwdSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End MemFwdBlocks.

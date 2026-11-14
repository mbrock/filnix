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


From Glibc Require Import SysSrc.
Module SysBlocks.

Module fn___isatty_nostatus.

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

End fn___isatty_nostatus.

Module fn___GI___libc_write.

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

End fn___GI___libc_write.

Module fn___lseek64.

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

End fn___lseek64.

Module fn___GI___fstat64.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___fstat64.

Module fn___GI___close_nocancel.

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

End fn___GI___close_nocancel.

Module fn___GI___close_nocancel_nostatus.

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

End fn___GI___close_nocancel_nostatus.

Module fn___GI__exit.

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

End fn___GI__exit.

Module fn___GI___libc_cleanup_push_defer.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v3"); (TAtom "v33")]); ((TAtom "L36"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "pr.3"); (TAtom "v0"); (TAtom "v3")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (776))); (6%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (24))); (9%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (792)))]); ((TAtom "L22"), [(3%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 4), true, true, (Some (TAtom "v3")), (Some (792)))]); ((TAtom "L35"), []); ((TAtom "L36"), []); ((TAtom "L15"), []); ((TAtom "L41"), []); ((TAtom "L42"), [(1%N, (TApp "tmp" [(TAtom "v39")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (16))); (4%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (776)))])].

End fn___GI___libc_cleanup_push_defer.

Module fn___GI___libc_cleanup_pop_restore.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L21"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "v3")]); ((TAtom "L41"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "iw_1.start"), [(TAtom "pr.2")]); ((TAtom "L44"), []); ((TAtom "iw_2.L12"), [(TAtom "chk5"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L37"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L14"), [(TAtom "chk5"); (TAtom "iw_2.v3")]); ((TAtom "L15"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v25"); (TAtom "v3")]); ((TAtom "L21"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v3")]); ((TAtom "L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L41"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v3"); (TAtom "v39")]); ((TAtom "L42"), [(TAtom "chk1"); (TAtom "pr.2"); (TAtom "v3")]); ((TAtom "iw_1.start"), []); ((TAtom "L44"), [(TAtom "chk5"); (TAtom "iw_2.v10"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L12"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L37"), [(TAtom "chk5"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk5"); (TAtom "iw_2.pr.2"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L14"), []); ((TAtom "L15"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (24))); (6%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 8), false, true, (Some (TAtom "v3")), (Some (776))); (9%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 4), true, false, (Some (TAtom "v3")), (Some (792))); (12%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L20"), []); ((TAtom "L21"), []); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 4), true, true, (Some (TAtom "v3")), (Some (792)))]); ((TAtom "L41"), []); ((TAtom "L42"), []); ((TAtom "iw_1.start"), []); ((TAtom "L44"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v3")), (Some (1608))); (7%N, (TApp "tmp" [(TAtom "iw_2.v9")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L13"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v32")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L38"), []); ((TAtom "iw_2.L14"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (784)))]); ((TAtom "L15"), [])].

End fn___GI___libc_cleanup_pop_restore.

Module fn___GI___write_nocancel.

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

End fn___GI___write_nocancel.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__isatty_nostatus", app (map fst fn___isatty_nostatus.live_in) (app (map fst fn___isatty_nostatus.live_out) (map fst fn___isatty_nostatus.footprint))); ("__GI___libc_write", app (map fst fn___GI___libc_write.live_in) (app (map fst fn___GI___libc_write.live_out) (map fst fn___GI___libc_write.footprint))); ("__lseek64", app (map fst fn___lseek64.live_in) (app (map fst fn___lseek64.live_out) (map fst fn___lseek64.footprint))); ("__GI___fstat64", app (map fst fn___GI___fstat64.live_in) (app (map fst fn___GI___fstat64.live_out) (map fst fn___GI___fstat64.footprint))); ("__GI___close_nocancel", app (map fst fn___GI___close_nocancel.live_in) (app (map fst fn___GI___close_nocancel.live_out) (map fst fn___GI___close_nocancel.footprint))); ("__GI___close_nocancel_nostatus", app (map fst fn___GI___close_nocancel_nostatus.live_in) (app (map fst fn___GI___close_nocancel_nostatus.live_out) (map fst fn___GI___close_nocancel_nostatus.footprint))); ("__GI__exit", app (map fst fn___GI__exit.live_in) (app (map fst fn___GI__exit.live_out) (map fst fn___GI__exit.footprint))); ("__GI___libc_cleanup_push_defer", app (map fst fn___GI___libc_cleanup_push_defer.live_in) (app (map fst fn___GI___libc_cleanup_push_defer.live_out) (map fst fn___GI___libc_cleanup_push_defer.footprint))); ("__GI___libc_cleanup_pop_restore", app (map fst fn___GI___libc_cleanup_pop_restore.live_in) (app (map fst fn___GI___libc_cleanup_pop_restore.live_out) (map fst fn___GI___libc_cleanup_pop_restore.footprint))); ("__GI___write_nocancel", app (map fst fn___GI___write_nocancel.live_in) (app (map fst fn___GI___write_nocancel.live_out) (map fst fn___GI___write_nocancel.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) SysSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End SysBlocks.

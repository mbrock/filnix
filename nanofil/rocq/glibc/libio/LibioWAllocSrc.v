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


From Glibc Require Import LibioWAllocCode.
Module LibioWAllocSrc.

Definition file_0 : string := "wfiledoalloc.c".

Definition file_1 : string := "wgenops.c".

Module fn___GI__IO_wsetb.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 93%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 96%N)); ((TAtom "L18"), (file_1, 96%N)); ((TAtom "L19"), (file_1, 96%N)); ((TAtom "L8"), (file_1, 97%N)); ((TAtom "L10"), (file_1, 98%N)); ((TAtom "L44"), (file_1, 101%N)); ((TAtom "L45"), (file_1, 103%N)); ((TAtom "L46"), (file_1, 93%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "f"); ((TAtom "v11"), "f"); ((TAtom "v2"), "b"); ((TAtom "v20"), "f"); ((TAtom "v29"), "f"); ((TAtom "v34"), "f"); ((TAtom "v38"), "b"); ((TAtom "v39"), "f"); ((TAtom "v4"), "eb"); ((TAtom "v43"), "eb"); ((TAtom "v47"), "a"); ((TAtom "v48"), "f"); ((TAtom "v6"), "a"); ((TAtom "v61"), "f")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "f", 160)); ((TAtom "chk1"), ((TAtom "v13"), "v13", 48)); ((TAtom "chk11"), ((TAtom "v0"), "f", 116)); ((TAtom "chk12"), ((TAtom "v0"), "f", 116)); ((TAtom "chk14"), ((TAtom "v0"), "f", 116)); ((TAtom "chk2"), ((TAtom "v0"), "f", 116)); ((TAtom "chk4"), ((TAtom "v31"), "v31", 48)); ((TAtom "chk5"), ((TAtom "v0"), "f", 160)); ((TAtom "chk6"), ((TAtom "v36"), "v36", 48)); ((TAtom "chk7"), ((TAtom "v0"), "f", 160)); ((TAtom "chk8"), ((TAtom "v41"), "v41", 56)); ((TAtom "chk9"), ((TAtom "v0"), "f", 116)); ((TAtom "v0"), ((TAtom "v0"), "f", 0)); ((TAtom "v12"), ((TAtom "v0"), "f", 160)); ((TAtom "v14"), ((TAtom "v13"), "v13", 48)); ((TAtom "v2"), ((TAtom "v2"), "b", 0)); ((TAtom "v21"), ((TAtom "v0"), "f", 116)); ((TAtom "v30"), ((TAtom "v0"), "f", 160)); ((TAtom "v32"), ((TAtom "v31"), "v31", 48)); ((TAtom "v35"), ((TAtom "v0"), "f", 160)); ((TAtom "v37"), ((TAtom "v36"), "v36", 48)); ((TAtom "v4"), ((TAtom "v4"), "eb", 0)); ((TAtom "v42"), ((TAtom "v41"), "v41", 56)); ((TAtom "v49"), ((TAtom "v0"), "f", 116)); ((TAtom "v6"), ((TAtom "v6"), "a", 0)); ((TAtom "v62"), ((TAtom "v0"), "f", 116))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L44"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L45"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L46"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v26"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L44"), []); ((TAtom "L45"), []); ((TAtom "L46"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "f->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 8), true, false, (Some (TAtom "v13")), (Some (48)), "f->_wide_data->_IO_buf_base")]); ((TAtom "L18"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "f->_flags2")]); ((TAtom "L19"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "f->_wide_data"); (4%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "v31")), (Some (48)), "f->_wide_data->_IO_buf_base")]); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "f->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), false, true, (Some (TAtom "v36")), (Some (48)), "f->_wide_data->_IO_buf_base"); (7%N, (TApp "tmp" [(TAtom "v35")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "f->_wide_data"); (10%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), false, true, (Some (TAtom "v41")), (Some (56)), "f->_wide_data->_IO_buf_end")]); ((TAtom "L44"), [(2%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "f->_flags2"); (6%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "f->_flags2"); (11%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (116)), "f->_flags2")]); ((TAtom "L45"), [(2%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "f->_flags2"); (6%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)), "f->_flags2"); (11%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (116)), "f->_flags2")]); ((TAtom "L46"), [])].


End fn___GI__IO_wsetb.

Module fn___GI__IO_wdoallocbuf.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 362%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 365%N)); ((TAtom "L2"), (file_1, 366%N)); ((TAtom "L4"), (file_1, 367%N)); ((TAtom "L13"), (file_1, 368%N)); ((TAtom "L20"), (file_1, 369%N)); ((TAtom "L15"), (file_1, 370%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "fp"); ((TAtom "v16"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v35"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v5"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 160)); ((TAtom "chk1"), ((TAtom "v7"), "v7", 48)); ((TAtom "chk2"), ((TAtom "v0"), "fp", 0)); ((TAtom "chk4"), ((TAtom "v25"), "v25", 224)); ((TAtom "chk5"), ((TAtom "v27"), "v27", 104)); ((TAtom "chk7"), ((TAtom "v0"), "fp", 160)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v24"), ((TAtom "v0"), "fp", 160)); ((TAtom "v26"), ((TAtom "v25"), "v25", 224)); ((TAtom "v28"), ((TAtom "v27"), "v27", 104)); ((TAtom "v36"), ((TAtom "v0"), "fp", 160)); ((TAtom "v38"), ((TAtom "v37"), "v37", 216)); ((TAtom "v42"), ((TAtom "v41"), "v41", 216)); ((TAtom "v43"), ((TAtom "v41"), "v41", 220)); ((TAtom "v6"), ((TAtom "v0"), "fp", 160)); ((TAtom "v8"), ((TAtom "v7"), "v7", 48))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L15"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (5%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v7")), (Some (48)), "fp->_wide_data->_IO_buf_base")]); ((TAtom "L2"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L13"), [(1%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (4%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), true, false, (Some (TAtom "v25")), (Some (224)), "opaque"); (7%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v27")), (Some (104)), "opaque")]); ((TAtom "L20"), []); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (4%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data")])].


End fn___GI__IO_wdoallocbuf.

Module fn__IO_wfile_doallocate.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 62%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 69%N)); ((TAtom "L4"), (file_0, 70%N)); ((TAtom "L6"), (file_0, 76%N)); ((TAtom "L24"), (file_0, 78%N)); ((TAtom "L26"), (file_0, 65%N)); ((TAtom "L37"), (file_0, 81%N)); ((TAtom "L39"), (file_0, 82%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "size"); ((TAtom "v0"), "fp"); ((TAtom "v13"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v18"), "fp"); ((TAtom "v23"), "size"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "size"); ((TAtom "v33"), "size"); ((TAtom "v34"), "size"); ((TAtom "v36"), "p"); ((TAtom "v40"), "p"); ((TAtom "v48"), "fp"); ((TAtom "v49"), "p"); ((TAtom "v50"), "p"); ((TAtom "v51"), "size"); ((TAtom "v7"), "fp")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "fp", 56)); ((TAtom "chk1"), ((TAtom "v0"), "fp", 64)); ((TAtom "chk2"), ((TAtom "v0"), "fp", 56)); ((TAtom "chk3"), ((TAtom "v0"), "fp", 0)); ((TAtom "pr.1"), ((TAtom "pr.1"), "size", 0)); ((TAtom "v0"), ((TAtom "v0"), "fp", 0)); ((TAtom "v16"), ((TAtom "v0"), "fp", 64)); ((TAtom "v19"), ((TAtom "v0"), "fp", 56)); ((TAtom "v23"), ((TAtom "v23"), "size", 0)); ((TAtom "v33"), ((TAtom "v33"), "size", 0)); ((TAtom "v36"), ((TAtom "v36"), "p", 0)); ((TAtom "v8"), ((TAtom "v0"), "fp", 56))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11")]); ((TAtom "L24"), [(TAtom "v0"); (TAtom "v11"); (TAtom "v23")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v11")]); ((TAtom "L37"), []); ((TAtom "L39"), [(TAtom "v0"); (TAtom "v35"); (TAtom "v36")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v11")]); ((TAtom "L6"), [(TAtom "v0"); (TAtom "v11"); (TAtom "v23")]); ((TAtom "L24"), [(TAtom "v0"); (TAtom "v11"); (TAtom "v33")]); ((TAtom "L26"), [(TAtom "v0"); (TAtom "v35"); (TAtom "v36")]); ((TAtom "L37"), []); ((TAtom "L39"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "fp->_IO_buf_base")]); ((TAtom "L4"), []); ((TAtom "L6"), [(2%N, (TApp "tmp" [(TAtom "v16")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (64)), "fp->_IO_buf_end"); (5%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)), "fp->_IO_buf_base"); (10%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L24"), []); ((TAtom "L26"), []); ((TAtom "L37"), []); ((TAtom "L39"), [])].


End fn__IO_wfile_doallocate.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiowalloc_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__GI__IO_wsetb"; "__GI__IO_wdoallocbuf"; "_IO_wfile_doallocate"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__GI__IO_wsetb", app (map fst fn___GI__IO_wsetb.block_src) (app (map fst fn___GI__IO_wsetb.live_in) (app (map fst fn___GI__IO_wsetb.live_out) (app (map fst fn___GI__IO_wsetb.footprint) (fn___GI__IO_wsetb.loop_heads))))); ("__GI__IO_wdoallocbuf", app (map fst fn___GI__IO_wdoallocbuf.block_src) (app (map fst fn___GI__IO_wdoallocbuf.live_in) (app (map fst fn___GI__IO_wdoallocbuf.live_out) (app (map fst fn___GI__IO_wdoallocbuf.footprint) (fn___GI__IO_wdoallocbuf.loop_heads))))); ("_IO_wfile_doallocate", app (map fst fn__IO_wfile_doallocate.block_src) (app (map fst fn__IO_wfile_doallocate.live_in) (app (map fst fn__IO_wfile_doallocate.live_out) (app (map fst fn__IO_wfile_doallocate.footprint) (fn__IO_wfile_doallocate.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End LibioWAllocSrc.

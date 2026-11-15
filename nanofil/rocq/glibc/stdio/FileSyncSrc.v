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


From Glibc Require Import FileSyncCode.
Module FileSyncSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "fileops.c".

Module fn__IO_new_file_sync.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 841%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 848%N)); ((TAtom "L4"), (file_1, 849%N)); ((TAtom "L19"), (file_1, 849%N)); ((TAtom "L20"), (file_1, 849%N)); ((TAtom "L21"), (file_1, 849%N)); ((TAtom "L16"), (file_1, 849%N)); ((TAtom "L6"), (file_1, 850%N)); ((TAtom "L73"), (file_1, 853%N)); ((TAtom "L75"), (file_1, 844%N)); ((TAtom "L91"), (file_1, 858%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_1, 858%N)); ((TAtom "L106"), (file_1, 860%N)); ((TAtom "L107"), (file_1, 861%N)); ((TAtom "L119"), (file_1, 861%N)); ((TAtom "L93"), (file_1, 845%N)); ((TAtom "L125"), (file_1, 867%N)); ((TAtom "L127"), (file_1, 870%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "pr.1"), "delta"); ((TAtom "pr.2"), "retval"); ((TAtom "pr.3"), "retval"); ((TAtom "pr.4"), "retval"); ((TAtom "v0"), "fp"); ((TAtom "v10"), "fp"); ((TAtom "v103"), "fp"); ((TAtom "v104"), "delta"); ((TAtom "v105"), "new_pos"); ((TAtom "v109"), "new_pos"); ((TAtom "v113"), "fp"); ((TAtom "v115"), "fp"); ((TAtom "v122"), "__libc_errno"); ((TAtom "v124"), "retval"); ((TAtom "v128"), "retval"); ((TAtom "v131"), "fp"); ((TAtom "v135"), "retval"); ((TAtom "v22"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v27"), "fp"); ((TAtom "v30"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v40"), "fp"); ((TAtom "v41"), "fp"); ((TAtom "v46"), "fp"); ((TAtom "v51"), "fp"); ((TAtom "v64"), "fp"); ((TAtom "v67"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v72"), "delta"); ((TAtom "v76"), "fp"); ((TAtom "v79"), "fp"); ((TAtom "v80"), "delta"); ((TAtom "v81"), "fp"); ((TAtom "v84"), "fp"); ((TAtom "v90"), "delta"); ((TAtom "v94"), "delta"); ((TAtom "v97"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L16"), []); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "v0"); (TAtom "v72")]); ((TAtom "L75"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "v0")]); ((TAtom "L91"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v99")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v99")]); ((TAtom "L106"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "v0")]); ((TAtom "L107"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L119"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L93"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L125"), [(TAtom "chk0"); (TAtom "pr.4"); (TAtom "v0")]); ((TAtom "L127"), [(TAtom "pr.4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "v0")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v39")]); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v60")]); ((TAtom "L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L16"), []); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "v0"); (TAtom "v72")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "v0"); (TAtom "v90")]); ((TAtom "L75"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L91"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v99")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v99")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "chk12"); (TAtom "chk13"); (TAtom "v0")]); ((TAtom "L106"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L107"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L119"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L93"), [(TAtom "chk0"); (TAtom "pr.4"); (TAtom "v0")]); ((TAtom "L125"), [(TAtom "pr.4")]); ((TAtom "L127"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (5%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base")]); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v23")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)), "fp->_mode")]); ((TAtom "L19"), [(1%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base"); (3%N, (TApp "tmp" [(TAtom "v8")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40)), "fp->_IO_write_ptr"); (4%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)), "fp->_IO_write_base")]); ((TAtom "L20"), [(1%N, (TApp "tmp" [(TAtom "v8")]), (120), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (4%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v43")), (Some (24)), "fp->_wide_data->_IO_write_base"); (5%N, (TApp "tmp" [(TAtom "v8")]), (120), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (8%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), true, false, (Some (TAtom "v48")), (Some (32)), "fp->_wide_data->_IO_write_ptr"); (9%N, (TApp "tmp" [(TAtom "v8")]), (120), (Some 8), true, false, (Some (TAtom "v0")), (Some (160)), "fp->_wide_data"); (12%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 8), true, false, (Some (TAtom "v53")), (Some (24)), "fp->_wide_data->_IO_write_base")]); ((TAtom "L21"), []); ((TAtom "L16"), []); ((TAtom "L6"), [(2%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "fp->_IO_read_ptr"); (5%N, (TApp "tmp" [(TAtom "v68")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "fp->_IO_read_end"); (10%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)), "fp->_flags")]); ((TAtom "L73"), [(3%N, (TApp "tmp" [(TAtom "v82")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "fp->_IO_read_ptr"); (6%N, (TApp "tmp" [(TAtom "v85")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "fp->_IO_read_end")]); ((TAtom "L75"), []); ((TAtom "L91"), [(2%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)), "opaque")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v101")]), (0), (Some 8), true, false, (Some (TAtom "v99")), (Some (128)), "opaque")]); ((TAtom "L106"), [(3%N, (TApp "tmp" [(TAtom "v116")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "fp->_IO_read_ptr"); (5%N, (TApp "tmp" [(TAtom "v114")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (16)), "fp->_IO_read_end")]); ((TAtom "L107"), [(2%N, (TApp "tmp" [(TAtom "v121")]), (0), (Some 4), true, false, (Some (TAtom "v121")), (Some (0)), "opaque")]); ((TAtom "L119"), []); ((TAtom "L93"), []); ((TAtom "L125"), [(2%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (144)), "fp->_offset")]); ((TAtom "L127"), [])].


End fn__IO_new_file_sync.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) filesync_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_IO_new_file_sync"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("_IO_new_file_sync", app (map fst fn__IO_new_file_sync.block_src) (app (map fst fn__IO_new_file_sync.live_in) (app (map fst fn__IO_new_file_sync.live_out) (app (map fst fn__IO_new_file_sync.footprint) (fn__IO_new_file_sync.loop_heads)))))].

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

End FileSyncSrc.

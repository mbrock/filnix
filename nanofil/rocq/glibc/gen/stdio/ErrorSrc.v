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


From Glibc Require Import ErrorCode.
Module ErrorSrc.

Definition file_0 : string := "error.c".

Module fn___error_internal.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 234%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 241%N)); ((TAtom "L12"), (file_0, 250%N)); ((TAtom "L13"), (file_0, 254%N)); ((TAtom "iw_2.start"), (file_0, 207%N)); ((TAtom "iw_2.L22"), (file_0, 208%N)); ((TAtom "iw_2.L23"), (file_0, 208%N)); ((TAtom "iw_2.L67"), (file_0, 208%N)); ((TAtom "iw_2.L30"), (file_0, 208%N)); ((TAtom "iw_2.L17"), (file_0, 211%N)); ((TAtom "iw_2.L19"), (file_0, 216%N)); ((TAtom "iw_2.iw_1.start"), (file_0, 177%N)); ((TAtom "iw_2.L92"), (file_0, 220%N)); ((TAtom "iw_2.L100"), (file_0, 226%N)); ((TAtom "iw_2.join"), (file_0, 264%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v1"), "stdout"); ((TAtom "iw_2.iw_1.v0"), "errnum"); ((TAtom "iw_2.iw_1.v4"), "errnum"); ((TAtom "iw_2.iw_1.v5"), "s"); ((TAtom "iw_2.iw_1.v7"), "s"); ((TAtom "iw_2.pr.1"), "__result"); ((TAtom "iw_2.pr.2"), "__result"); ((TAtom "iw_2.v0"), "status"); ((TAtom "iw_2.v103"), "status"); ((TAtom "iw_2.v104"), "status"); ((TAtom "iw_2.v12"), "stderr"); ((TAtom "iw_2.v13"), "message"); ((TAtom "iw_2.v14"), "args"); ((TAtom "iw_2.v15"), "mode_flags"); ((TAtom "iw_2.v16"), "ret"); ((TAtom "iw_2.v2"), "errnum"); ((TAtom "iw_2.v20"), "ret"); ((TAtom "iw_2.v25"), "__libc_errno"); ((TAtom "iw_2.v35"), "__result"); ((TAtom "iw_2.v4"), "message"); ((TAtom "iw_2.v46"), "stderr"); ((TAtom "iw_2.v51"), "stderr"); ((TAtom "iw_2.v55"), "stderr"); ((TAtom "iw_2.v57"), "__result"); ((TAtom "iw_2.v6"), "args"); ((TAtom "iw_2.v71"), "stderr"); ((TAtom "iw_2.v74"), "__result"); ((TAtom "iw_2.v76"), "stderr"); ((TAtom "iw_2.v77"), "__result"); ((TAtom "iw_2.v78"), "__result"); ((TAtom "iw_2.v79"), "__result"); ((TAtom "iw_2.v8"), "mode_flags"); ((TAtom "iw_2.v85"), "stderr"); ((TAtom "iw_2.v88"), "error_message_count"); ((TAtom "iw_2.v89"), "error_message_count"); ((TAtom "iw_2.v93"), "errnum"); ((TAtom "iw_2.v94"), "errnum"); ((TAtom "iw_2.v98"), "stderr"); ((TAtom "v0"), "status"); ((TAtom "v16"), "error_print_progname"); ((TAtom "v2"), "errnum"); ((TAtom "v20"), "error_print_progname"); ((TAtom "v23"), "program_invocation_name"); ((TAtom "v25"), "status"); ((TAtom "v26"), "errnum"); ((TAtom "v27"), "message"); ((TAtom "v28"), "args"); ((TAtom "v29"), "mode_flags"); ((TAtom "v30"), "state"); ((TAtom "v4"), "message"); ((TAtom "v6"), "args"); ((TAtom "v8"), "mode_flags")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v10"), "&state", 0)); ((TAtom "chk1"), ((TAtom "iw_1.v0"), "&stdout", 0)); ((TAtom "chk10"), ((TAtom "iw_2.v84"), "&stderr", 0)); ((TAtom "chk11"), ((TAtom "iw_2.v87"), "&error_message_count", 0)); ((TAtom "chk12"), ((TAtom "iw_2.v87"), "&error_message_count", 0)); ((TAtom "chk13"), ((TAtom "iw_2.v97"), "&stderr", 0)); ((TAtom "chk14"), ((TAtom "v10"), "&state", 0)); ((TAtom "chk2"), ((TAtom "v15"), "&error_print_progname", 0)); ((TAtom "chk3"), ((TAtom "v19"), "&error_print_progname", 0)); ((TAtom "chk5"), ((TAtom "v22"), "&program_invocation_name", 0)); ((TAtom "chk6"), ((TAtom "iw_2.v11"), "&stderr", 0)); ((TAtom "chk7"), ((TAtom "iw_2.v24"), "&__libc_errno", 0)); ((TAtom "chk8"), ((TAtom "iw_2.v70"), "&stderr", 0)); ((TAtom "chk9"), ((TAtom "iw_2.v71"), "stderr", 192)); ((TAtom "iw_1.v0"), ((TAtom "iw_1.v0"), "&stdout", 0)); ((TAtom "iw_1.v1"), ((TAtom "iw_1.v1"), "stdout", 0)); ((TAtom "iw_2.iw_1.v3"), ((TAtom "iw_2.iw_1.v3"), "&errbuf", 0)); ((TAtom "iw_2.iw_1.v5"), ((TAtom "iw_2.iw_1.v5"), "s", 0)); ((TAtom "iw_2.v11"), ((TAtom "iw_2.v11"), "&stderr", 0)); ((TAtom "iw_2.v12"), ((TAtom "iw_2.v12"), "stderr", 0)); ((TAtom "iw_2.v16"), ((TAtom "iw_2.v16"), "ret", 0)); ((TAtom "iw_2.v24"), ((TAtom "iw_2.v24"), "&__libc_errno", 0)); ((TAtom "iw_2.v25"), ((TAtom "iw_2.v25"), "__libc_errno", 0)); ((TAtom "iw_2.v70"), ((TAtom "iw_2.v70"), "&stderr", 0)); ((TAtom "iw_2.v71"), ((TAtom "iw_2.v71"), "stderr", 0)); ((TAtom "iw_2.v72"), ((TAtom "iw_2.v71"), "stderr", 192)); ((TAtom "iw_2.v84"), ((TAtom "iw_2.v84"), "&stderr", 0)); ((TAtom "iw_2.v85"), ((TAtom "iw_2.v85"), "stderr", 0)); ((TAtom "iw_2.v87"), ((TAtom "iw_2.v87"), "&error_message_count", 0)); ((TAtom "iw_2.v88"), ((TAtom "iw_2.v88"), "error_message_count", 0)); ((TAtom "iw_2.v89"), ((TAtom "iw_2.v89"), "error_message_count", 0)); ((TAtom "iw_2.v97"), ((TAtom "iw_2.v97"), "&stderr", 0)); ((TAtom "iw_2.v98"), ((TAtom "iw_2.v98"), "stderr", 0)); ((TAtom "v0"), ((TAtom "v0"), "status", 0)); ((TAtom "v10"), ((TAtom "v10"), "&state", 0)); ((TAtom "v15"), ((TAtom "v15"), "&error_print_progname", 0)); ((TAtom "v16"), ((TAtom "v16"), "error_print_progname", 0)); ((TAtom "v19"), ((TAtom "v19"), "&error_print_progname", 0)); ((TAtom "v2"), ((TAtom "v2"), "errnum", 0)); ((TAtom "v20"), ((TAtom "v20"), "error_print_progname", 0)); ((TAtom "v22"), ((TAtom "v22"), "&program_invocation_name", 0)); ((TAtom "v23"), ((TAtom "v23"), "program_invocation_name", 0)); ((TAtom "v30"), ((TAtom "v30"), "state", 0)); ((TAtom "v4"), ((TAtom "v4"), "message", 0)); ((TAtom "v6"), ((TAtom "v6"), "args", 0)); ((TAtom "v8"), ((TAtom "v8"), "mode_flags", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "iw_2.L22"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L67"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L19"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.iw_1.start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L92"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10")]); ((TAtom "iw_2.L100"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "v10")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6"); (TAtom "v8")]); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L22"), [(TAtom "chk0"); (TAtom "iw_2.v26"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L67"), [(TAtom "chk0"); (TAtom "iw_2.v80"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.L19"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10"); (TAtom "v2")]); ((TAtom "iw_2.iw_1.start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10")]); ((TAtom "iw_2.L92"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v10")]); ((TAtom "iw_2.L100"), [(TAtom "chk0"); (TAtom "v10")]); ((TAtom "iw_2.join"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 4), false, true, (Some (TAtom "v10")), (Some (0)), "opaque"); (6%N, (TApp "tmp" [(TAtom "iw_1.v0")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.v0")), (Some (0)), "opaque"); (10%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 8), true, false, (Some (TAtom "v15")), (Some (0)), "opaque")]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), true, false, (Some (TAtom "v19")), (Some (0)), "opaque")]); ((TAtom "L13"), [(3%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), true, false, (Some (TAtom "v22")), (Some (0)), "opaque")]); ((TAtom "iw_2.start"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v11")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v11")), (Some (0)), "opaque")]); ((TAtom "iw_2.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v24")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v24")), (Some (0)), "opaque")]); ((TAtom "iw_2.L23"), []); ((TAtom "iw_2.L67"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v70")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v70")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "iw_2.v72")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v71")), (Some (192)), "stderr->_mode")]); ((TAtom "iw_2.L30"), []); ((TAtom "iw_2.L17"), [(3%N, (TApp "tmp" [(TAtom "iw_2.v84")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v84")), (Some (0)), "opaque")]); ((TAtom "iw_2.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v87")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v87")), (Some (0)), "opaque"); (5%N, (TApp "tmp" [(TAtom "iw_2.v87")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v87")), (Some (0)), "opaque")]); ((TAtom "iw_2.iw_1.start"), []); ((TAtom "iw_2.L92"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v97")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v97")), (Some (0)), "opaque")]); ((TAtom "iw_2.L100"), []); ((TAtom "iw_2.join"), [(1%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 4), true, false, (Some (TAtom "v10")), (Some (0)), "opaque")])].


End fn___error_internal.

Module fn___error.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 268%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 271%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "status"); ((TAtom "v2"), "errnum"); ((TAtom "v4"), "message"); ((TAtom "v7"), "status"); ((TAtom "v8"), "errnum"); ((TAtom "v9"), "message")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v6"), "&ap", 0)); ((TAtom "v0"), ((TAtom "v0"), "status", 0)); ((TAtom "v2"), ((TAtom "v2"), "errnum", 0)); ((TAtom "v4"), ((TAtom "v4"), "message", 0)); ((TAtom "v6"), ((TAtom "v6"), "&ap", 0))].

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
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), false, true, (Some (TAtom "v6")), (Some (0)), "opaque")])].


End fn___error.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) error_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__error_internal"; "__error"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__error_internal", app (map fst fn___error_internal.block_src) (app (map fst fn___error_internal.live_in) (app (map fst fn___error_internal.live_out) (app (map fst fn___error_internal.footprint) (fn___error_internal.loop_heads))))); ("__error", app (map fst fn___error.block_src) (app (map fst fn___error.live_in) (app (map fst fn___error.live_out) (app (map fst fn___error.footprint) (fn___error.loop_heads)))))].

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

End ErrorSrc.

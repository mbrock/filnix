(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_pad_1_os.

Module PrintfPadOneSrc.

Definition file_0 : string := "../include/printf_buffer.h".

Definition file_1 : string := "./Xprintf_buffer_pad_1.c".

Module fn___printf_buffer_pad_1.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 22%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 115%N)); ((TAtom "L6"), (file_1, 26%N)); ((TAtom "L15"), (file_1, 22%N)); ((TAtom "L30"), (file_1, 33%N)); ((TAtom "L31"), (file_1, 33%N)); ((TAtom "L18"), (file_1, 34%N)); ((TAtom "L20"), (file_1, 35%N)); ((TAtom "L40"), (file_1, 35%N)); ((TAtom "L41"), (file_1, 36%N)); ((TAtom "L65"), (file_1, 37%N)); ((TAtom "L66"), (file_1, 36%N)); ((TAtom "L17"), (file_1, 22%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "buf"); ((TAtom "iw_1.v2"), "buf"); ((TAtom "pr.1"), "count"); ((TAtom "pr.2"), "to_fill"); ((TAtom "v0"), "buf"); ((TAtom "v2"), "ch"); ((TAtom "v21"), "buf"); ((TAtom "v24"), "buf"); ((TAtom "v32"), "buf"); ((TAtom "v4"), "count"); ((TAtom "v42"), "buf"); ((TAtom "v45"), "buf"); ((TAtom "v55"), "buf"); ((TAtom "v58"), "buf"); ((TAtom "v63"), "to_fill"); ((TAtom "v67"), "to_fill"); ((TAtom "v68"), "count"); ((TAtom "v70"), "count"); ((TAtom "v71"), "buf"); ((TAtom "v74"), "ch"); ((TAtom "v75"), "to_fill"); ((TAtom "v77"), "buf"); ((TAtom "v80"), "to_fill"); ((TAtom "v82"), "count"); ((TAtom "v83"), "to_fill"); ((TAtom "v84"), "count"); ((TAtom "v85"), "count"); ((TAtom "v9"), "buf")].

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  [((TAtom "chk0"), ((TAtom "v0"), "buf", 32)); ((TAtom "chk1"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk2"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk3"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk4"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk5"), ((TAtom "v0"), "buf", 16)); ((TAtom "chk6"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk8"), ((TAtom "v0"), "buf", 8)); ((TAtom "chk9"), ((TAtom "v0"), "buf", 8)); ((TAtom "iw_1.v3"), ((TAtom "v0"), "buf", 32)); ((TAtom "pr.1"), ((TAtom "pr.1"), "count", 0)); ((TAtom "pr.2"), ((TAtom "pr.2"), "to_fill", 0)); ((TAtom "v0"), ((TAtom "v0"), "buf", 0)); ((TAtom "v2"), ((TAtom "v2"), "ch", 0)); ((TAtom "v22"), ((TAtom "v0"), "buf", 8)); ((TAtom "v25"), ((TAtom "v0"), "buf", 16)); ((TAtom "v4"), ((TAtom "v4"), "count", 0)); ((TAtom "v43"), ((TAtom "v0"), "buf", 8)); ((TAtom "v46"), ((TAtom "v0"), "buf", 16)); ((TAtom "v56"), ((TAtom "v0"), "buf", 16)); ((TAtom "v59"), ((TAtom "v0"), "buf", 8)); ((TAtom "v63"), ((TAtom "v63"), "to_fill", 0)); ((TAtom "v72"), ((TAtom "v0"), "buf", 8)); ((TAtom "v74"), ((TAtom "v74"), "ch", 0)); ((TAtom "v84"), ((TAtom "v84"), "count", 0))].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L15")].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L18"), []); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L65"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v63")]); ((TAtom "L66"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L17"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v35")]); ((TAtom "L31"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L18"), []); ((TAtom "L20"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v63")]); ((TAtom "L65"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v2"); (TAtom "v63")]); ((TAtom "L66"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v84")]); ((TAtom "L17"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)), "buf->mode")]); ((TAtom "L6"), []); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (5%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->write_end")]); ((TAtom "L30"), []); ((TAtom "L31"), []); ((TAtom "L18"), []); ((TAtom "L20"), [(2%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (5%N, (TApp "tmp" [(TAtom "v46")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->write_end")]); ((TAtom "L40"), []); ((TAtom "L41"), [(2%N, (TApp "tmp" [(TAtom "v56")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)), "buf->write_end"); (5%N, (TApp "tmp" [(TAtom "v59")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr")]); ((TAtom "L65"), []); ((TAtom "L66"), [(1%N, (TApp "tmp" [(TAtom "v59")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (5%N, (TApp "tmp" [(TAtom "v72")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr"); (8%N, (TApp "tmp" [(TAtom "v72")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)), "buf->write_ptr")]); ((TAtom "L17"), [])].


End fn___printf_buffer_pad_1.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("__printf_buffer_pad_1", map b_label (fn_blocks Unit_stdioZ2dcommon_printf_buffer_pad_1_os.fn___printf_buffer_pad_1))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__printf_buffer_pad_1", app (map fst fn___printf_buffer_pad_1.block_src) (app (map fst fn___printf_buffer_pad_1.live_in) (app (map fst fn___printf_buffer_pad_1.live_out) (app (map fst fn___printf_buffer_pad_1.footprint) (fn___printf_buffer_pad_1.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfPadOneSrc.

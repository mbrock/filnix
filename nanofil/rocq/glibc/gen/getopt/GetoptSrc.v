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

From Glibc Require Import Unit_posix_getopt1_os Unit_posix_getopt_os.

From Glibc Require Import GetoptSrcFiles GetoptSrc01 GetoptSrc02 GetoptSrc03.
Module GetoptSrc.
Include GetoptSrcFiles.
Include GetoptSrc01.
Include GetoptSrc02.
Include GetoptSrc03.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("glibc_getopt#process_long_option", map b_label (fn_blocks Unit_posix_getopt_os.fn_glibc_getopt'23process_long_option)); ("_getopt_internal_r", map b_label (fn_blocks Unit_posix_getopt_os.fn__getopt_internal_r)); ("_getopt_internal", map b_label (fn_blocks Unit_posix_getopt_os.fn__getopt_internal)); ("getopt_long", map b_label (fn_blocks Unit_posix_getopt1_os.fn_getopt_long))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("glibc_getopt#process_long_option", app (map fst fn_glibc_getopt_process_long_option.block_src) (app (map fst fn_glibc_getopt_process_long_option.live_in) (app (map fst fn_glibc_getopt_process_long_option.live_out) (app (map fst fn_glibc_getopt_process_long_option.footprint) (fn_glibc_getopt_process_long_option.loop_heads))))); ("_getopt_internal_r", app (map fst fn__getopt_internal_r.block_src) (app (map fst fn__getopt_internal_r.live_in) (app (map fst fn__getopt_internal_r.live_out) (app (map fst fn__getopt_internal_r.footprint) (fn__getopt_internal_r.loop_heads))))); ("_getopt_internal", app (map fst fn__getopt_internal.block_src) (app (map fst fn__getopt_internal.live_in) (app (map fst fn__getopt_internal.live_out) (app (map fst fn__getopt_internal.footprint) (fn__getopt_internal.loop_heads))))); ("getopt_long", app (map fst fn_getopt_long.block_src) (app (map fst fn_getopt_long.live_in) (app (map fst fn_getopt_long.live_out) (app (map fst fn_getopt_long.footprint) (fn_getopt_long.loop_heads)))))].

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

End GetoptSrc.

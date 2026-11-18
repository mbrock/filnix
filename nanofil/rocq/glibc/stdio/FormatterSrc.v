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


From Glibc Require Import FormatterCode FormatterSrcFiles FormatterSrc01 FormatterSrc02.
Module FormatterSrc.
Include FormatterSrcFiles.
Include FormatterSrc01.
Include FormatterSrc02.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) formatter_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__printf_buffer"; "__vfprintf_internal"; "glibc_vfprintf_internal#__printf_buffer_pad"; "glibc_vfprintf_internal#__printf_buffer_putc"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__printf_buffer", app (map fst fn___printf_buffer.block_src) (app (map fst fn___printf_buffer.live_in) (app (map fst fn___printf_buffer.live_out) (app (map fst fn___printf_buffer.footprint) (fn___printf_buffer.loop_heads))))); ("__vfprintf_internal", app (map fst fn___vfprintf_internal.block_src) (app (map fst fn___vfprintf_internal.live_in) (app (map fst fn___vfprintf_internal.live_out) (app (map fst fn___vfprintf_internal.footprint) (fn___vfprintf_internal.loop_heads))))); ("glibc_vfprintf_internal#__printf_buffer_pad", app (map fst fn_glibc_vfprintf_internal___printf_buffer_pad.block_src) (app (map fst fn_glibc_vfprintf_internal___printf_buffer_pad.live_in) (app (map fst fn_glibc_vfprintf_internal___printf_buffer_pad.live_out) (app (map fst fn_glibc_vfprintf_internal___printf_buffer_pad.footprint) (fn_glibc_vfprintf_internal___printf_buffer_pad.loop_heads))))); ("glibc_vfprintf_internal#__printf_buffer_putc", app (map fst fn_glibc_vfprintf_internal___printf_buffer_putc.block_src) (app (map fst fn_glibc_vfprintf_internal___printf_buffer_putc.live_in) (app (map fst fn_glibc_vfprintf_internal___printf_buffer_putc.live_out) (app (map fst fn_glibc_vfprintf_internal___printf_buffer_putc.footprint) (fn_glibc_vfprintf_internal___printf_buffer_putc.loop_heads)))))].

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

End FormatterSrc.

(** The stream invariant walks twelve consecutive pointer fields with one affine offset formula.
    Its base and stride come from the captured C layout, but the remaining fields must also be contiguous.
    This computation checks that property without restricting the formula's domain. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import FileInv LibioReadLayout.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** The pointer formula covers exactly the twelve consecutive fields used by the stream invariant. *)
Lemma off_ptr_layout :
  map (fun i => Some (off_ptr i)) (seq 0 12) =
  map (LibioReadLayout.field_offset "struct _IO_FILE")
    ["_IO_read_ptr"; "_IO_read_end"; "_IO_read_base"; "_IO_write_base";
     "_IO_write_ptr"; "_IO_write_end"; "_IO_buf_base"; "_IO_buf_end";
     "_IO_save_base"; "_IO_backup_base"; "_IO_save_end"; "_markers"].
Proof. reflexivity. Qed.

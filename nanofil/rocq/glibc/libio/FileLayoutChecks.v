(** The stdio invariants use hand-written offsets to describe fields in caller memory.
    These computations compare those constants with the compiler's captured C layouts.
    A changed field offset or a missing table entry prevents this module from compiling.
    Existing proofs retain their constants and do not assume these tables are correct. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import FileInv LibioReadLayout LibioStdfilesLayout SysLayout.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Lemma off_flags_layout : Some off_flags = LibioReadLayout.field_offset "struct _IO_FILE" "_flags".
Proof. reflexivity. Qed.
Lemma off_read_ptr_layout : Some off_read_ptr = LibioReadLayout.field_offset "struct _IO_FILE" "_IO_read_ptr".
Proof. reflexivity. Qed.
Lemma off_write_base_layout : Some off_write_base = LibioReadLayout.field_offset "struct _IO_FILE" "_IO_write_base".
Proof. reflexivity. Qed.
Lemma off_write_ptr_layout : Some off_write_ptr = LibioReadLayout.field_offset "struct _IO_FILE" "_IO_write_ptr".
Proof. reflexivity. Qed.
Lemma off_write_end_layout : Some off_write_end = LibioReadLayout.field_offset "struct _IO_FILE" "_IO_write_end".
Proof. reflexivity. Qed.
Lemma off_buf_base_layout : Some off_buf_base = LibioReadLayout.field_offset "struct _IO_FILE" "_IO_buf_base".
Proof. reflexivity. Qed.
Lemma off_buf_end_layout : Some off_buf_end = LibioReadLayout.field_offset "struct _IO_FILE" "_IO_buf_end".
Proof. reflexivity. Qed.
Lemma off_chain_layout : Some off_chain = LibioReadLayout.field_offset "struct _IO_FILE" "_chain".
Proof. reflexivity. Qed.
Lemma off_fileno_layout : Some off_fileno = LibioReadLayout.field_offset "struct _IO_FILE" "_fileno".
Proof. reflexivity. Qed.
Lemma off_flags2_layout : Some off_flags2 = LibioReadLayout.field_offset "struct _IO_FILE" "_flags2".
Proof. reflexivity. Qed.
Lemma off_old_offset_layout : Some off_old_offset = LibioReadLayout.field_offset "struct _IO_FILE" "_old_offset".
Proof. reflexivity. Qed.
Lemma off_column_layout : Some off_column = LibioReadLayout.field_offset "struct _IO_FILE" "_cur_column".
Proof. reflexivity. Qed.
Lemma off_shortbuf_layout : Some off_shortbuf = LibioReadLayout.field_offset "struct _IO_FILE" "_shortbuf".
Proof. reflexivity. Qed.
Lemma off_lock_layout : Some off_lock = LibioReadLayout.field_offset "struct _IO_FILE" "_lock".
Proof. reflexivity. Qed.
Lemma off_offset_layout : Some off_offset = LibioReadLayout.field_offset "struct _IO_FILE" "_offset".
Proof. reflexivity. Qed.
Lemma off_codecvt_layout : Some off_codecvt = LibioReadLayout.field_offset "struct _IO_FILE" "_codecvt".
Proof. reflexivity. Qed.
Lemma off_wide_layout : Some off_wide = LibioReadLayout.field_offset "struct _IO_FILE" "_wide_data".
Proof. reflexivity. Qed.
Lemma off_freeres_list_layout : Some off_freeres_list = LibioReadLayout.field_offset "struct _IO_FILE" "_freeres_list".
Proof. reflexivity. Qed.
Lemma off_freeres_buf_layout : Some off_freeres_buf = LibioReadLayout.field_offset "struct _IO_FILE" "_freeres_buf".
Proof. reflexivity. Qed.
Lemma off_prevchain_layout : Some off_prevchain = LibioReadLayout.field_offset "struct _IO_FILE" "_prevchain".
Proof. reflexivity. Qed.
Lemma off_mode_layout : Some off_mode = LibioReadLayout.field_offset "struct _IO_FILE" "_mode".
Proof. reflexivity. Qed.
Lemma off_total_written_layout : Some off_total_written = LibioReadLayout.field_offset "struct _IO_FILE" "_total_written".
Proof. reflexivity. Qed.
Lemma off_vtable_layout : Some off_vtable = LibioStdfilesLayout.field_offset "struct _IO_FILE_plus" "vtable".
Proof. reflexivity. Qed.
Lemma off_cleanup_layout : Some off_cleanup = SysLayout.field_offset "struct pthread" "cleanup".
Proof. reflexivity. Qed.
Lemma off_cleanup_jmp_layout : Some off_cleanup_jmp = SysLayout.field_offset "struct pthread" "cleanup_jmp_buf".
Proof. reflexivity. Qed.
Lemma off_cancelhandling_layout : Some off_cancelhandling = SysLayout.field_offset "struct pthread" "cancelhandling".
Proof. reflexivity. Qed.
Lemma off_lk_lock_layout : Some off_lk_lock = LibioReadLayout.field_offset "typedef _IO_lock_t" "lock".
Proof. reflexivity. Qed.
Lemma off_lk_cnt_layout : Some off_lk_cnt = LibioReadLayout.field_offset "typedef _IO_lock_t" "cnt".
Proof. reflexivity. Qed.
Lemma off_lk_owner_layout : Some off_lk_owner = LibioReadLayout.field_offset "typedef _IO_lock_t" "owner".
Proof. reflexivity. Qed.

(** The pointer formula covers exactly the twelve consecutive fields used by the stream invariant. *)
Lemma off_ptr_layout :
  map (fun i => Some (off_ptr i)) (seq 0 12) =
  map (LibioReadLayout.field_offset "struct _IO_FILE")
    ["_IO_read_ptr"; "_IO_read_end"; "_IO_read_base"; "_IO_write_base";
     "_IO_write_ptr"; "_IO_write_end"; "_IO_buf_base"; "_IO_buf_end";
     "_IO_save_base"; "_IO_backup_base"; "_IO_save_end"; "_markers"].
Proof. reflexivity. Qed.

Lemma file_size_layout : Some file_size =
  option_map (fun entry => fst (snd entry))
    (find (fun entry => String.eqb (fst entry) "struct _IO_FILE_plus") LibioStdfilesLayout.records).
Proof. reflexivity. Qed.

Lemma slot_finish_layout : Some slot_finish = LibioReadLayout.field_offset "struct _IO_jump_t" "__finish".
Proof. reflexivity. Qed.
Lemma slot_overflow_layout : Some slot_overflow = LibioReadLayout.field_offset "struct _IO_jump_t" "__overflow".
Proof. reflexivity. Qed.
Lemma slot_xsputn_layout : Some slot_xsputn = LibioReadLayout.field_offset "struct _IO_jump_t" "__xsputn".
Proof. reflexivity. Qed.
Lemma slot_doallocate_layout : Some slot_doallocate = LibioReadLayout.field_offset "struct _IO_jump_t" "__doallocate".
Proof. reflexivity. Qed.
Lemma slot_write_layout : Some slot_write = LibioReadLayout.field_offset "struct _IO_jump_t" "__write".
Proof. reflexivity. Qed.
Lemma slot_close_layout : Some slot_close = LibioReadLayout.field_offset "struct _IO_jump_t" "__close".
Proof. reflexivity. Qed.
Lemma slot_stat_layout : Some slot_stat = LibioReadLayout.field_offset "struct _IO_jump_t" "__stat".
Proof. reflexivity. Qed.

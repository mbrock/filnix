(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20_IO_FILE : record_layout :=
  (mkRecordLayout "struct _IO_FILE" 216 8 [("_flags", 0, 4, 4); ("_IO_read_ptr", 8, 8, 8); ("_IO_read_end", 16, 8, 8); ("_IO_read_base", 24, 8, 8); ("_IO_write_base", 32, 8, 8); ("_IO_write_ptr", 40, 8, 8); ("_IO_write_end", 48, 8, 8); ("_IO_buf_base", 56, 8, 8); ("_IO_buf_end", 64, 8, 8); ("_IO_save_base", 72, 8, 8); ("_IO_backup_base", 80, 8, 8); ("_IO_save_end", 88, 8, 8); ("_markers", 96, 8, 8); ("_chain", 104, 8, 8); ("_fileno", 112, 4, 4); ("_flags2", 116, 4, 4); ("_short_backupbuf", 119, 1, 1); ("_old_offset", 120, 8, 8); ("_cur_column", 128, 2, 2); ("_vtable_offset", 130, 1, 1); ("_shortbuf", 131, 1, 1); ("_lock", 136, 8, 8); ("_offset", 144, 8, 8); ("_codecvt", 152, 8, 8); ("_wide_data", 160, 8, 8); ("_freeres_list", 168, 8, 8); ("_freeres_buf", 176, 8, 8); ("_prevchain", 184, 8, 8); ("_mode", 192, 4, 4); ("_unused3", 196, 4, 4); ("_total_written", 200, 8, 8); ("_unused2", 208, 8, 1)]).

Definition layout_structZ20_IO_codecvt : record_layout :=
  (mkRecordLayout "struct _IO_codecvt" 112 8 [("__cd_in", 0, 56, 8); ("__cd_out", 56, 56, 8)]).

Definition layout_structZ20_IO_jump_t : record_layout :=
  (mkRecordLayout "struct _IO_jump_t" 168 8 [("__dummy", 0, 8, 8); ("__dummy2", 8, 8, 8); ("__finish", 16, 8, 8); ("__overflow", 24, 8, 8); ("__underflow", 32, 8, 8); ("__uflow", 40, 8, 8); ("__pbackfail", 48, 8, 8); ("__xsputn", 56, 8, 8); ("__xsgetn", 64, 8, 8); ("__seekoff", 72, 8, 8); ("__seekpos", 80, 8, 8); ("__setbuf", 88, 8, 8); ("__sync", 96, 8, 8); ("__doallocate", 104, 8, 8); ("__read", 112, 8, 8); ("__write", 120, 8, 8); ("__seek", 128, 8, 8); ("__close", 136, 8, 8); ("__stat", 144, 8, 8); ("__showmanyc", 152, 8, 8); ("__imbue", 160, 8, 8)]).

Definition layout_structZ20_IO_marker : record_layout :=
  (mkRecordLayout "struct _IO_marker" 24 8 [("_next", 0, 8, 8); ("_sbuf", 8, 8, 8); ("_pos", 16, 4, 4)]).

Definition layout_structZ20_IO_wide_data : record_layout :=
  (mkRecordLayout "struct _IO_wide_data" 232 8 [("_IO_read_ptr", 0, 8, 8); ("_IO_read_end", 8, 8, 8); ("_IO_read_base", 16, 8, 8); ("_IO_write_base", 24, 8, 8); ("_IO_write_ptr", 32, 8, 8); ("_IO_write_end", 40, 8, 8); ("_IO_buf_base", 48, 8, 8); ("_IO_buf_end", 56, 8, 8); ("_IO_save_base", 64, 8, 8); ("_IO_backup_base", 72, 8, 8); ("_IO_save_end", 80, 8, 8); ("_IO_state", 88, 8, 4); ("_IO_last_state", 96, 8, 4); ("_codecvt", 104, 112, 8); ("_shortbuf", 216, 4, 4); ("_wide_vtable", 224, 8, 8)]).

Definition layout_structZ20__gconv_step : record_layout :=
  (mkRecordLayout "struct __gconv_step" 104 8 [("__shlib_handle", 0, 8, 8); ("__modname", 8, 8, 8); ("__counter", 16, 4, 4); ("__from_name", 24, 8, 8); ("__to_name", 32, 8, 8); ("__fct", 40, 8, 8); ("__btowc_fct", 48, 8, 8); ("__init_fct", 56, 8, 8); ("__end_fct", 64, 8, 8); ("__min_needed_from", 72, 4, 4); ("__max_needed_from", 76, 4, 4); ("__min_needed_to", 80, 4, 4); ("__max_needed_to", 84, 4, 4); ("__stateful", 88, 4, 4); ("__data", 96, 8, 8)]).

Definition layout_structZ20__gconv_step_data : record_layout :=
  (mkRecordLayout "struct __gconv_step_data" 48 8 [("__outbuf", 0, 8, 8); ("__outbufend", 8, 8, 8); ("__flags", 16, 4, 4); ("__invocation_counter", 20, 4, 4); ("__internal_use", 24, 4, 4); ("__statep", 32, 8, 8); ("__state", 40, 8, 4)]).

Definition layout_typedefZ20FILE : record_layout :=
  (mkRecordLayout "typedef FILE" 216 8 [("_flags", 0, 4, 4); ("_IO_read_ptr", 8, 8, 8); ("_IO_read_end", 16, 8, 8); ("_IO_read_base", 24, 8, 8); ("_IO_write_base", 32, 8, 8); ("_IO_write_ptr", 40, 8, 8); ("_IO_write_end", 48, 8, 8); ("_IO_buf_base", 56, 8, 8); ("_IO_buf_end", 64, 8, 8); ("_IO_save_base", 72, 8, 8); ("_IO_backup_base", 80, 8, 8); ("_IO_save_end", 88, 8, 8); ("_markers", 96, 8, 8); ("_chain", 104, 8, 8); ("_fileno", 112, 4, 4); ("_flags2", 116, 4, 4); ("_short_backupbuf", 119, 1, 1); ("_old_offset", 120, 8, 8); ("_cur_column", 128, 2, 2); ("_vtable_offset", 130, 1, 1); ("_shortbuf", 131, 1, 1); ("_lock", 136, 8, 8); ("_offset", 144, 8, 8); ("_codecvt", 152, 8, 8); ("_wide_data", 160, 8, 8); ("_freeres_list", 168, 8, 8); ("_freeres_buf", 176, 8, 8); ("_prevchain", 184, 8, 8); ("_mode", 192, 4, 4); ("_unused3", 196, 4, 4); ("_total_written", 200, 8, 8); ("_unused2", 208, 8, 1)]).

Definition layout_typedefZ20_IO_iconv_t : record_layout :=
  (mkRecordLayout "typedef _IO_iconv_t" 56 8 [("step", 0, 8, 8); ("step_data", 8, 48, 8)]).

Definition layout_typedefZ20_IO_lock_t : record_layout :=
  (mkRecordLayout "typedef _IO_lock_t" 16 8 [("lock", 0, 4, 4); ("cnt", 4, 4, 4); ("owner", 8, 8, 8)]).

Definition layout_typedefZ20__FILE : record_layout :=
  (mkRecordLayout "typedef __FILE" 216 8 [("_flags", 0, 4, 4); ("_IO_read_ptr", 8, 8, 8); ("_IO_read_end", 16, 8, 8); ("_IO_read_base", 24, 8, 8); ("_IO_write_base", 32, 8, 8); ("_IO_write_ptr", 40, 8, 8); ("_IO_write_end", 48, 8, 8); ("_IO_buf_base", 56, 8, 8); ("_IO_buf_end", 64, 8, 8); ("_IO_save_base", 72, 8, 8); ("_IO_backup_base", 80, 8, 8); ("_IO_save_end", 88, 8, 8); ("_markers", 96, 8, 8); ("_chain", 104, 8, 8); ("_fileno", 112, 4, 4); ("_flags2", 116, 4, 4); ("_short_backupbuf", 119, 1, 1); ("_old_offset", 120, 8, 8); ("_cur_column", 128, 2, 2); ("_vtable_offset", 130, 1, 1); ("_shortbuf", 131, 1, 1); ("_lock", 136, 8, 8); ("_offset", 144, 8, 8); ("_codecvt", 152, 8, 8); ("_wide_data", 160, 8, 8); ("_freeres_list", 168, 8, 8); ("_freeres_buf", 176, 8, 8); ("_prevchain", 184, 8, 8); ("_mode", 192, 4, 4); ("_unused3", 196, 4, 4); ("_total_written", 200, 8, 8); ("_unused2", 208, 8, 1)]).

Definition layout_typedefZ20__mbstate_t : record_layout :=
  (mkRecordLayout "typedef __mbstate_t" 8 4 [("__count", 0, 4, 4); ("__value", 4, 4, 4)]).

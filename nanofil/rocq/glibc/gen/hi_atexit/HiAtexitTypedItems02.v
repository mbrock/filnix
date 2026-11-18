(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitTypedFL HiAtexitTypedIO02 HiAtexitTypedIO03 HiAtexitTypedIO04 HiAtexitTypedIO05 HiAtexitTypedIO06 HiAtexitTypedIO07 HiAtexitTypedIO08 HiAtexitTypedOV HiAtexitTypedObjects01 HiAtexitTypedSA HiAtexitTypedUN.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_items_02 : module :=
  [IFunc hi_fn__IO_new_file_sync;
  IFunc hi_fn__IO_file_sync_mmap;
  IFunc hi_fn__IO_new_file_seekoff;
  IFunc hi_fn__IO_file_seekoff_mmap;
  IFunc hi_fn__IO_file_seekoff_maybe_mmap;
  IFunc hi_fn___GI__IO_file_read;
  IFunc hi_fn___GI__IO_file_seek;
  IFunc hi_fn___GI__IO_file_stat;
  IFunc hi_fn__IO_file_close_mmap;
  IFunc hi_fn___GI__IO_file_close;
  IFunc hi_fn__IO_new_file_write;
  IFunc hi_fn__IO_new_file_xsputn;
  IFunc hi_fn___GI__IO_file_xsgetn;
  IFunc hi_fn__IO_file_xsgetn_mmap;
  IFunc hi_fn__IO_file_xsgetn_maybe_mmap;
  hi_item___GI__IO_file_xsputn;
  hi_item___GI__IO_file_sync;
  hi_item___GI__IO_file_overflow;
  hi_item___GI__IO_file_underflow;
  hi_item___GI__IO_file_setbuf;
  hi_item___GI__IO_file_finish;
  IFunc hi_fn_glibc_genops'23flush_cleanup;
  IFunc hi_fn___GI__IO_un_link;
  IFunc hi_fn__IO_switch_to_main_get_area;
  IFunc hi_fn__IO_switch_to_backup_area;
  IFunc hi_fn___GI__IO_switch_to_get_mode;
  IFunc hi_fn___GI__IO_free_backup_area;
  IFunc hi_fn___GI___overflow;
  IFunc hi_fn_glibc_genops'23save_for_backup;
  IFunc hi_fn___GI___underflow;
  IFunc hi_fn___GI__IO_setb;
  IFunc hi_fn___GI__IO_doallocbuf;
  IFunc hi_fn___GI__IO_default_uflow;
  IFunc hi_fn___GI__IO_default_xsputn;
  IFunc hi_fn___GI__IO_default_xsgetn;
  IFunc hi_fn__IO_default_setbuf;
  IFunc hi_fn__IO_default_seekpos;
  IFunc hi_fn___GI__IO_default_doallocate;
  IFunc hi_fn__IO_default_sync;
  IFunc hi_fn___GI__IO_default_finish;
  IFunc hi_fn___GI__IO_adjust_column;
  IFunc hi_fn___GI__IO_flush_all;
  IFunc hi_fn__IO_cleanup;
  IFunc hi_fn___GI__IO_unsave_markers;
  IFunc hi_fn___GI__IO_default_pbackfail;
  IFunc hi_fn__IO_default_seek;
  IFunc hi_fn__IO_default_stat;
  IFunc hi_fn__IO_default_read;
  IFunc hi_fn__IO_default_write;
  IFunc hi_fn__IO_default_showmanyc;
  IFunc hi_fn__IO_default_imbue;
  hi_item_glibc_genops'23dealloc_buffers;
  hi_item_glibc_genops'23freeres_list;
  hi_item_glibc_genops'23list_all_lock;
  hi_item_glibc_genops'23run_fp;
  IFunc hi_fn__IO_new_fclose;
  hi_item_fclose;
  IFunc hi_fn___GI__IO_puts;
  hi_item_puts;
  IFunc hi_fn_glibc_stdfiles'23_IO_stdfiles_init;
  hi_item__IO_2_1_stderr_;
  hi_item__IO_2_1_stdin_;
  hi_item__IO_2_1_stdout_;
  hi_item___GI__IO_list_all].

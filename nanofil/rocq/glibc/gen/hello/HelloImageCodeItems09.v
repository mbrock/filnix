(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_iofclose_os Unit_libio_iofflush_os Unit_libio_iofopen_os Unit_libio_iofopncook_os Unit_libio_iofputs_os.
From Glibc Require Import Unit_libio_iofwide_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_09 : module :=
  [Unit_libio_fileops_os.item___GI__IO_file_seekoff;
  Unit_libio_fileops_os.item___GI__IO_file_sync;
  Unit_libio_fileops_os.item___GI__IO_file_overflow;
  Unit_libio_fileops_os.item___GI__IO_file_underflow;
  Unit_libio_fileops_os.item___GI__IO_do_write;
  Unit_libio_fileops_os.item___GI__IO_file_setbuf;
  Unit_libio_fileops_os.item___GI__IO_file_fopen;
  Unit_libio_fileops_os.item___GI__IO_file_finish;
  IFunc Unit_libio_genops_os.fn_glibc_genops'23flush_cleanup;
  IFunc Unit_libio_genops_os.fn___GI__IO_un_link;
  IFunc Unit_libio_genops_os.fn___GI__IO_link_in;
  IFunc Unit_libio_genops_os.fn__IO_switch_to_main_get_area;
  IFunc Unit_libio_genops_os.fn__IO_switch_to_backup_area;
  IFunc Unit_libio_genops_os.fn___GI__IO_switch_to_get_mode;
  IFunc Unit_libio_genops_os.fn___GI__IO_free_backup_area;
  IFunc Unit_libio_genops_os.fn___GI___overflow;
  IFunc Unit_libio_genops_os.fn_glibc_genops'23save_for_backup;
  IFunc Unit_libio_genops_os.fn___GI___underflow;
  IFunc Unit_libio_genops_os.fn___GI___uflow;
  IFunc Unit_libio_genops_os.fn___GI__IO_setb;
  IFunc Unit_libio_genops_os.fn___GI__IO_doallocbuf;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_uflow;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_xsputn;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_xsgetn;
  IFunc Unit_libio_genops_os.fn__IO_default_setbuf;
  IFunc Unit_libio_genops_os.fn__IO_default_seekpos;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_doallocate;
  IFunc Unit_libio_genops_os.fn__IO_old_init;
  IFunc Unit_libio_genops_os.fn__IO_no_init;
  IFunc Unit_libio_genops_os.fn__IO_default_sync;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_finish;
  IFunc Unit_libio_genops_os.fn___GI__IO_sputbackc;
  IFunc Unit_libio_genops_os.fn___GI__IO_adjust_column;
  IFunc Unit_libio_genops_os.fn___GI__IO_flush_all;
  IFunc Unit_libio_genops_os.fn__IO_cleanup;
  IFunc Unit_libio_genops_os.fn___GI__IO_unsave_markers;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_pbackfail;
  IFunc Unit_libio_genops_os.fn__IO_default_seek;
  IFunc Unit_libio_genops_os.fn__IO_default_stat;
  IFunc Unit_libio_genops_os.fn__IO_default_read;
  IFunc Unit_libio_genops_os.fn__IO_default_write;
  IFunc Unit_libio_genops_os.fn__IO_default_showmanyc;
  IFunc Unit_libio_genops_os.fn__IO_default_imbue;
  Unit_libio_genops_os.item_glibc_genops'23dealloc_buffers;
  Unit_libio_genops_os.item_glibc_genops'23freeres_list;
  Unit_libio_genops_os.item_glibc_genops'23list_all_lock;
  Unit_libio_genops_os.item_glibc_genops'23run_fp;
  Unit_libio_genops_os.item_glibc_genops'23stdio_needs_locking;
  IFunc Unit_libio_iofclose_os.fn__IO_new_fclose;
  Unit_libio_iofclose_os.item_fclose;
  IFunc Unit_libio_iofflush_os.fn___GI__IO_fflush;
  IFunc Unit_libio_iofopen_os.fn___fopen_maybe_mmap;
  IFunc Unit_libio_iofopen_os.fn___fopen_internal;
  IFunc Unit_libio_iofopen_os.fn__IO_new_fopen;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_read;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_write;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_seek;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_close;
  IFunc Unit_libio_iofopncook_os.fn__IO_cookie_seekoff;
  IFunc Unit_libio_iofputs_os.fn___GI__IO_fputs;
  Unit_libio_iofputs_os.item_fputs;
  IFunc Unit_libio_iofwide_os.fn__IO_fwide;
  IFunc Unit_libio_iofwide_os.fn___libio_codecvt_out;
  IFunc Unit_libio_iofwide_os.fn___libio_codecvt_in].

Lemma hello_image_linked_items_09_zero : zero_nonneg hello_image_linked_items_09 = true.
Proof. reflexivity. Qed.

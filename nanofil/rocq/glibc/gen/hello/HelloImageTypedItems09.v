(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedFL HelloImageTypedFO HelloImageTypedIO04 HelloImageTypedIO05 HelloImageTypedIO06 HelloImageTypedLI HelloImageTypedOV HelloImageTypedObjects03 HelloImageTypedSA HelloImageTypedUF HelloImageTypedUN.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_09 : module :=
  [hello_image_item___GI__IO_file_seekoff;
  hello_image_item___GI__IO_file_sync;
  hello_image_item___GI__IO_file_overflow;
  hello_image_item___GI__IO_file_underflow;
  hello_image_item___GI__IO_do_write;
  hello_image_item___GI__IO_file_setbuf;
  hello_image_item___GI__IO_file_fopen;
  hello_image_item___GI__IO_file_finish;
  IFunc hello_image_fn_glibc_genops'23flush_cleanup;
  IFunc hello_image_fn___GI__IO_un_link;
  IFunc hello_image_fn___GI__IO_link_in;
  IFunc hello_image_fn__IO_switch_to_main_get_area;
  IFunc hello_image_fn__IO_switch_to_backup_area;
  IFunc hello_image_fn___GI__IO_switch_to_get_mode;
  IFunc hello_image_fn___GI__IO_free_backup_area;
  IFunc hello_image_fn___GI___overflow;
  IFunc hello_image_fn_glibc_genops'23save_for_backup;
  IFunc hello_image_fn___GI___underflow;
  IFunc hello_image_fn___GI___uflow;
  IFunc hello_image_fn___GI__IO_setb;
  IFunc hello_image_fn___GI__IO_doallocbuf;
  IFunc hello_image_fn___GI__IO_default_uflow;
  IFunc hello_image_fn___GI__IO_default_xsputn;
  IFunc hello_image_fn___GI__IO_default_xsgetn;
  IFunc hello_image_fn__IO_default_setbuf;
  IFunc hello_image_fn__IO_default_seekpos;
  IFunc hello_image_fn___GI__IO_default_doallocate;
  IFunc hello_image_fn__IO_old_init;
  IFunc hello_image_fn__IO_no_init;
  IFunc hello_image_fn__IO_default_sync;
  IFunc hello_image_fn___GI__IO_default_finish;
  IFunc hello_image_fn___GI__IO_sputbackc;
  IFunc hello_image_fn___GI__IO_adjust_column;
  IFunc hello_image_fn___GI__IO_flush_all;
  IFunc hello_image_fn__IO_cleanup;
  IFunc hello_image_fn___GI__IO_unsave_markers;
  IFunc hello_image_fn___GI__IO_default_pbackfail;
  IFunc hello_image_fn__IO_default_seek;
  IFunc hello_image_fn__IO_default_stat;
  IFunc hello_image_fn__IO_default_read;
  IFunc hello_image_fn__IO_default_write;
  IFunc hello_image_fn__IO_default_showmanyc;
  IFunc hello_image_fn__IO_default_imbue;
  hello_image_item_glibc_genops'23dealloc_buffers;
  hello_image_item_glibc_genops'23freeres_list;
  hello_image_item_glibc_genops'23list_all_lock;
  hello_image_item_glibc_genops'23run_fp;
  hello_image_item_glibc_genops'23stdio_needs_locking;
  IFunc hello_image_fn__IO_new_fclose;
  hello_image_item_fclose;
  IFunc hello_image_fn___GI__IO_fflush;
  IFunc hello_image_fn___fopen_maybe_mmap;
  IFunc hello_image_fn___fopen_internal;
  IFunc hello_image_fn__IO_new_fopen;
  IFunc hello_image_fn__IO_cookie_read;
  IFunc hello_image_fn__IO_cookie_write;
  IFunc hello_image_fn__IO_cookie_seek;
  IFunc hello_image_fn__IO_cookie_close;
  IFunc hello_image_fn__IO_cookie_seekoff;
  IFunc hello_image_fn___GI__IO_fputs;
  hello_image_item_fputs;
  IFunc hello_image_fn__IO_fwide;
  IFunc hello_image_fn___libio_codecvt_out;
  IFunc hello_image_fn___libio_codecvt_in].

Lemma hello_image_items_09_zero : zero_nonneg hello_image_items_09 = true.
Proof. reflexivity. Qed.

(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_io_close_nocancel_nostatus_os Unit_io_fstat64_os Unit_io_fstatat64_os Unit_io_getcwd_os Unit_io_lseek64_os Unit_io_open64_nocancel_os Unit_io_open64_os.
From Glibc Require Import Unit_io_read_nocancel_os Unit_io_read_os Unit_io_stat64_os Unit_io_write_nocancel_os Unit_io_write_os Unit_libio___fpending_os Unit_libio_feof_u_os Unit_libio_ferror_os.
From Glibc Require Import Unit_libio_filedoalloc_os Unit_libio_fileops_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_08 : module :=
  [IFunc Unit_io_close_nocancel_nostatus_os.fn___GI___close_nocancel_nostatus;
  IFunc Unit_io_fstat64_os.fn___GI___fstat64;
  IFunc Unit_io_fstatat64_os.fn___GI___fstatat64;
  IFunc Unit_io_getcwd_os.fn___GI___getcwd;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e242;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e243;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e244;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e245;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e246;
  Unit_io_getcwd_os.item_glibc_getcwd'23str'2e247;
  IFunc Unit_io_lseek64_os.fn___lseek64;
  IFunc Unit_io_open64_os.fn___libc_open64;
  Unit_io_open64_os.item___GI___open;
  IFunc Unit_io_open64_nocancel_os.fn___GI___open64_nocancel;
  Unit_io_open64_nocancel_os.item___GI___open_nocancel;
  IFunc Unit_io_read_os.fn___GI___libc_read;
  Unit_io_read_os.item___GI___read;
  IFunc Unit_io_read_nocancel_os.fn___GI___read_nocancel;
  IFunc Unit_io_stat64_os.fn___GI___stat64;
  IFunc Unit_io_write_os.fn___GI___libc_write;
  Unit_io_write_os.item___GI___write;
  Unit_io_write_os.item___GI_write;
  IFunc Unit_io_write_nocancel_os.fn___GI___write_nocancel;
  IFunc Unit_libio___fpending_os.fn___fpending;
  IFunc Unit_libio_feof_u_os.fn___feof_unlocked;
  IFunc Unit_libio_ferror_os.fn__IO_ferror;
  Unit_libio_ferror_os.item_ferror;
  IFunc Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_init_internal;
  IFunc Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_close_it;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_finish;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_open;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_fopen;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_setbuf;
  IFunc Unit_libio_fileops_os.fn__IO_file_setbuf_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_do_write;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_underflow;
  IFunc Unit_libio_fileops_os.fn_glibc_fileops'23mmap_remap_check;
  IFunc Unit_libio_fileops_os.fn__IO_file_underflow_mmap;
  IFunc Unit_libio_fileops_os.fn_glibc_fileops'23decide_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_file_underflow_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_overflow;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_sync;
  IFunc Unit_libio_fileops_os.fn__IO_file_sync_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_seekoff;
  IFunc Unit_libio_fileops_os.fn__IO_file_seekoff_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_file_seekoff_maybe_mmap;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_read;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_seek;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_stat;
  IFunc Unit_libio_fileops_os.fn__IO_file_close_mmap;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_close;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_write;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_xsputn;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_xsgetn;
  IFunc Unit_libio_fileops_os.fn__IO_file_xsgetn_mmap;
  IFunc Unit_libio_fileops_os.fn__IO_file_xsgetn_maybe_mmap;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e265;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e266;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e267;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e268;
  Unit_libio_fileops_os.item_glibc_fileops'23str'2e269;
  Unit_libio_fileops_os.item___GI__IO_file_xsputn].

Lemma hello_image_linked_items_08_zero : zero_nonneg hello_image_linked_items_08 = true.
Proof. reflexivity. Qed.

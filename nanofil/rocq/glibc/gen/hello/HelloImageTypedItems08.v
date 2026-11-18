(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedCL HelloImageTypedDE HelloImageTypedFE HelloImageTypedFP HelloImageTypedFS HelloImageTypedGE03 HelloImageTypedIO01 HelloImageTypedIO02 HelloImageTypedIO03 HelloImageTypedIO04 HelloImageTypedIO05 HelloImageTypedLI01 HelloImageTypedLS HelloImageTypedMM HelloImageTypedOP HelloImageTypedObjects03 HelloImageTypedRE02 HelloImageTypedST01 HelloImageTypedWR.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_08 : module :=
  [IFunc hello_image_fn___GI___close_nocancel_nostatus;
  IFunc hello_image_fn___GI___fstat64;
  IFunc hello_image_fn___GI___fstatat64;
  IFunc hello_image_fn___GI___getcwd;
  hello_image_item_glibc_getcwd'23str'2e242;
  hello_image_item_glibc_getcwd'23str'2e243;
  hello_image_item_glibc_getcwd'23str'2e244;
  hello_image_item_glibc_getcwd'23str'2e245;
  hello_image_item_glibc_getcwd'23str'2e246;
  hello_image_item_glibc_getcwd'23str'2e247;
  IFunc hello_image_fn___lseek64;
  IFunc hello_image_fn___libc_open64;
  hello_image_item___GI___open;
  IFunc hello_image_fn___GI___open64_nocancel;
  hello_image_item___GI___open_nocancel;
  IFunc hello_image_fn___GI___libc_read;
  hello_image_item___GI___read;
  IFunc hello_image_fn___GI___read_nocancel;
  IFunc hello_image_fn___GI___stat64;
  IFunc hello_image_fn___GI___libc_write;
  hello_image_item___GI___write;
  hello_image_item___GI_write;
  IFunc hello_image_fn___GI___write_nocancel;
  IFunc hello_image_fn___fpending;
  IFunc hello_image_fn___feof_unlocked;
  IFunc hello_image_fn__IO_ferror;
  hello_image_item_ferror;
  IFunc hello_image_fn___GI__IO_file_doallocate;
  IFunc hello_image_fn__IO_new_file_init_internal;
  IFunc hello_image_fn__IO_file_close_maybe_unlink;
  IFunc hello_image_fn__IO_new_file_close_it;
  IFunc hello_image_fn__IO_new_file_finish;
  IFunc hello_image_fn___GI__IO_file_open;
  IFunc hello_image_fn__IO_new_file_fopen;
  IFunc hello_image_fn__IO_new_file_setbuf;
  IFunc hello_image_fn__IO_file_setbuf_mmap;
  IFunc hello_image_fn__IO_new_do_write;
  IFunc hello_image_fn__IO_new_file_underflow;
  IFunc hello_image_fn_glibc_fileops'23mmap_remap_check;
  IFunc hello_image_fn__IO_file_underflow_mmap;
  IFunc hello_image_fn_glibc_fileops'23decide_maybe_mmap;
  IFunc hello_image_fn__IO_file_underflow_maybe_mmap;
  IFunc hello_image_fn__IO_new_file_overflow;
  IFunc hello_image_fn__IO_new_file_sync;
  IFunc hello_image_fn__IO_file_sync_mmap;
  IFunc hello_image_fn__IO_new_file_seekoff;
  IFunc hello_image_fn__IO_file_seekoff_mmap;
  IFunc hello_image_fn__IO_file_seekoff_maybe_mmap;
  IFunc hello_image_fn___GI__IO_file_read;
  IFunc hello_image_fn___GI__IO_file_seek;
  IFunc hello_image_fn___GI__IO_file_stat;
  IFunc hello_image_fn__IO_file_close_mmap;
  IFunc hello_image_fn___GI__IO_file_close;
  IFunc hello_image_fn__IO_new_file_write;
  IFunc hello_image_fn__IO_new_file_xsputn;
  IFunc hello_image_fn___GI__IO_file_xsgetn;
  IFunc hello_image_fn__IO_file_xsgetn_mmap;
  IFunc hello_image_fn__IO_file_xsgetn_maybe_mmap;
  hello_image_item_glibc_fileops'23str'2e265;
  hello_image_item_glibc_fileops'23str'2e266;
  hello_image_item_glibc_fileops'23str'2e267;
  hello_image_item_glibc_fileops'23str'2e268;
  hello_image_item_glibc_fileops'23str'2e269;
  hello_image_item___GI__IO_file_xsputn].

Lemma hello_image_items_08_zero : zero_nonneg hello_image_items_08 = true.
Proof. reflexivity. Qed.

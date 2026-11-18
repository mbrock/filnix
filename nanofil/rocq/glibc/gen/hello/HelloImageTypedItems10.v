(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedCH HelloImageTypedEN HelloImageTypedGE02 HelloImageTypedIO06 HelloImageTypedIO07 HelloImageTypedIO08 HelloImageTypedLI HelloImageTypedObjects03 HelloImageTypedPR01 HelloImageTypedUN HelloImageTypedVA HelloImageTypedVS.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_10 : module :=
  [IFunc hello_image_fn___libio_codecvt_encoding;
  IFunc hello_image_fn___libio_codecvt_length;
  hello_image_item_glibc_iofwide'23str'2e288;
  hello_image_item_glibc_iofwide'23str'2e289;
  hello_image_item_glibc_iofwide'23str'2e290;
  hello_image_item_glibc_iofwide'23str'2e291;
  IFunc hello_image_fn___GI___getdelim;
  IFunc hello_image_fn___GI__IO_getline;
  IFunc hello_image_fn___GI__IO_getline_info;
  IFunc hello_image_fn_glibc_iopopen'23unlock;
  IFunc hello_image_fn__IO_new_proc_close;
  hello_image_item_glibc_iopopen'23proc_file_chain;
  hello_image_item_glibc_iopopen'23proc_file_chain_lock;
  IFunc hello_image_fn___printf_buffer_flush_dprintf;
  IFunc hello_image_fn___libc_message_impl;
  IFunc hello_image_fn___GI___libc_fatal;
  hello_image_item_glibc_libc_fatal'23str'2e298;
  hello_image_item_glibc_libc_fatal'23str'2e299;
  hello_image_item_glibc_libc_fatal'23str'2e300;
  IFunc hello_image_fn__IO_mem_sync;
  IFunc hello_image_fn__IO_mem_finish;
  IFunc hello_image_fn__IO_mem_setbuf;
  IFunc hello_image_fn__IO_mem_doallocate;
  IFunc hello_image_fn___printf_buffer_flush_obstack;
  IFunc hello_image_fn_glibc_stdfiles'23_IO_stdfiles_init;
  hello_image_item__IO_2_1_stderr_;
  hello_image_item__IO_2_1_stdin_;
  hello_image_item__IO_2_1_stdout_;
  hello_image_item___GI__IO_list_all;
  hello_image_item_glibc_stdfiles'23_IO_stdfile_0_lock;
  hello_image_item_glibc_stdfiles'23_IO_stdfile_1_lock;
  hello_image_item_glibc_stdfiles'23_IO_stdfile_2_lock;
  hello_image_item_glibc_stdfiles'23_IO_wide_data_0;
  hello_image_item_glibc_stdfiles'23_IO_wide_data_1;
  hello_image_item_glibc_stdfiles'23_IO_wide_data_2;
  hello_image_item___nanofil_ctor__IO_stdfiles_init;
  hello_image_item_stderr;
  hello_image_item_stdout;
  IFunc hello_image_fn___GI__IO_str_overflow;
  IFunc hello_image_fn___GI__IO_str_underflow;
  IFunc hello_image_fn__IO_str_count;
  IFunc hello_image_fn_glibc_strops'23enlarge_userbuf;
  IFunc hello_image_fn___GI__IO_str_seekoff;
  IFunc hello_image_fn___GI__IO_str_pbackfail;
  IFunc hello_image_fn__IO_str_finish;
  hello_image_item_glibc_strops'23str'2e257;
  hello_image_item_glibc_strops'23str'2e258;
  hello_image_item_glibc_strops'23str'2e259;
  IFunc hello_image_fn___printf_buffer_flush_asprintf;
  IFunc hello_image_fn___vasprintf_internal;
  IFunc hello_image_fn___printf_buffer_flush_snprintf;
  IFunc hello_image_fn___printf_buffer_snprintf_init;
  IFunc hello_image_fn___printf_buffer_snprintf_done;
  IFunc hello_image_fn___vsnprintf_internal;
  IFunc hello_image_fn__IO_vtable_check;
  IFunc hello_image_fn_glibc_vtables'23check_stdfiles_vtables;
  hello_image_item_IO_accept_foreign_vtables;
  hello_image_item___io_vtables;
  hello_image_item_glibc_vtables'23str'2e302;
  hello_image_item___nanofil_ctor_check_stdfiles_vtables;
  IFunc hello_image_fn__IO_wfile_doallocate;
  IFunc hello_image_fn___GI__IO_wdo_write;
  IFunc hello_image_fn___GI__IO_wfile_underflow;
  IFunc hello_image_fn__IO_wfile_underflow_mmap].

Lemma hello_image_items_10_zero : zero_nonneg hello_image_items_10 = true.
Proof. reflexivity. Qed.

(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_libio_iofwide_os Unit_libio_iogetdelim_os Unit_libio_iogetline_os Unit_libio_iopopen_os Unit_libio_iovdprintf_os Unit_libio_libc_fatal_os Unit_libio_memstream_os.
From Glibc Require Import Unit_libio_obprintf_os Unit_libio_stdfiles_os Unit_libio_stdio_os Unit_libio_strops_os Unit_libio_vasprintf_os Unit_libio_vsnprintf_os Unit_libio_vtables_os Unit_libio_wfiledoalloc_os.
From Glibc Require Import Unit_libio_wfileops_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_10 : module :=
  [IFunc Unit_libio_iofwide_os.fn___libio_codecvt_encoding;
  IFunc Unit_libio_iofwide_os.fn___libio_codecvt_length;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e288;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e289;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e290;
  Unit_libio_iofwide_os.item_glibc_iofwide'23str'2e291;
  IFunc Unit_libio_iogetdelim_os.fn___GI___getdelim;
  IFunc Unit_libio_iogetline_os.fn___GI__IO_getline;
  IFunc Unit_libio_iogetline_os.fn___GI__IO_getline_info;
  IFunc Unit_libio_iopopen_os.fn_glibc_iopopen'23unlock;
  IFunc Unit_libio_iopopen_os.fn__IO_new_proc_close;
  Unit_libio_iopopen_os.item_glibc_iopopen'23proc_file_chain;
  Unit_libio_iopopen_os.item_glibc_iopopen'23proc_file_chain_lock;
  IFunc Unit_libio_iovdprintf_os.fn___printf_buffer_flush_dprintf;
  IFunc Unit_libio_libc_fatal_os.fn___libc_message_impl;
  IFunc Unit_libio_libc_fatal_os.fn___GI___libc_fatal;
  Unit_libio_libc_fatal_os.item_glibc_libc_fatal'23str'2e298;
  Unit_libio_libc_fatal_os.item_glibc_libc_fatal'23str'2e299;
  Unit_libio_libc_fatal_os.item_glibc_libc_fatal'23str'2e300;
  IFunc Unit_libio_memstream_os.fn__IO_mem_sync;
  IFunc Unit_libio_memstream_os.fn__IO_mem_finish;
  IFunc Unit_libio_memstream_os.fn__IO_mem_setbuf;
  IFunc Unit_libio_memstream_os.fn__IO_mem_doallocate;
  IFunc Unit_libio_obprintf_os.fn___printf_buffer_flush_obstack;
  IFunc Unit_libio_stdfiles_os.fn_glibc_stdfiles'23_IO_stdfiles_init;
  Unit_libio_stdfiles_os.item__IO_2_1_stderr_;
  Unit_libio_stdfiles_os.item__IO_2_1_stdin_;
  Unit_libio_stdfiles_os.item__IO_2_1_stdout_;
  Unit_libio_stdfiles_os.item___GI__IO_list_all;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_0_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_1_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_stdfile_2_lock;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_0;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_1;
  Unit_libio_stdfiles_os.item_glibc_stdfiles'23_IO_wide_data_2;
  Unit_libio_stdfiles_os.item___nanofil_ctor__IO_stdfiles_init;
  Unit_libio_stdio_os.item_stderr;
  Unit_libio_stdio_os.item_stdout;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_overflow;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_underflow;
  IFunc Unit_libio_strops_os.fn__IO_str_count;
  IFunc Unit_libio_strops_os.fn_glibc_strops'23enlarge_userbuf;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_seekoff;
  IFunc Unit_libio_strops_os.fn___GI__IO_str_pbackfail;
  IFunc Unit_libio_strops_os.fn__IO_str_finish;
  Unit_libio_strops_os.item_glibc_strops'23str'2e257;
  Unit_libio_strops_os.item_glibc_strops'23str'2e258;
  Unit_libio_strops_os.item_glibc_strops'23str'2e259;
  IFunc Unit_libio_vasprintf_os.fn___printf_buffer_flush_asprintf;
  IFunc Unit_libio_vasprintf_os.fn___vasprintf_internal;
  IFunc Unit_libio_vsnprintf_os.fn___printf_buffer_flush_snprintf;
  IFunc Unit_libio_vsnprintf_os.fn___printf_buffer_snprintf_init;
  IFunc Unit_libio_vsnprintf_os.fn___printf_buffer_snprintf_done;
  IFunc Unit_libio_vsnprintf_os.fn___vsnprintf_internal;
  IFunc Unit_libio_vtables_os.fn__IO_vtable_check;
  IFunc Unit_libio_vtables_os.fn_glibc_vtables'23check_stdfiles_vtables;
  Unit_libio_vtables_os.item_IO_accept_foreign_vtables;
  Unit_libio_vtables_os.item___io_vtables;
  Unit_libio_vtables_os.item_glibc_vtables'23str'2e302;
  Unit_libio_vtables_os.item___nanofil_ctor_check_stdfiles_vtables;
  IFunc Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wdo_write;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_underflow;
  IFunc Unit_libio_wfileops_os.fn__IO_wfile_underflow_mmap].

Lemma hello_image_linked_items_10_zero : zero_nonneg hello_image_linked_items_10 = true.
Proof. reflexivity. Qed.

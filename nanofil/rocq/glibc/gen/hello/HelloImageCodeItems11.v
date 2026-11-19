(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_libio_wfileops_os Unit_libio_wgenops_os Unit_libio_wmemstream_os Unit_libio_wprintf_os Unit_libio_wstrops_os Unit_locale_CZ2daddress_os Unit_locale_CZ2dcollate_os.
From Glibc Require Import Unit_locale_CZ2dctype_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_11 : module :=
  [IFunc Unit_libio_wfileops_os.fn__IO_wfile_underflow_maybe_mmap;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_overflow;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_sync;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_seekoff;
  IFunc Unit_libio_wfileops_os.fn___GI__IO_wfile_xsputn;
  Unit_libio_wfileops_os.item_glibc_wfileops'23str'2e254;
  Unit_libio_wfileops_os.item_glibc_wfileops'23str'2e255;
  Unit_libio_wfileops_os.item_glibc_wfileops'23str'2e256;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_least_wmarker;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_switch_to_main_wget_area;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_switch_to_wbackup_area;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wsetb;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_pbackfail;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_finish;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_uflow;
  IFunc Unit_libio_wgenops_os.fn___GI___woverflow;
  IFunc Unit_libio_wgenops_os.fn___GI___wunderflow;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_xsputn;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_xsgetn;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdoallocbuf;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_wdefault_doallocate;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_switch_to_wget_mode;
  IFunc Unit_libio_wgenops_os.fn___GI__IO_free_wbackup_area;
  IFunc Unit_libio_wgenops_os.fn_glibc_wgenops'23save_for_wbackup;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_sync;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_finish;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_setbuf;
  IFunc Unit_libio_wmemstream_os.fn__IO_wmem_doallocate;
  IFunc Unit_libio_wprintf_os.fn___wprintf;
  Unit_libio_wprintf_os.item_wprintf;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_overflow;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_underflow;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_count;
  IFunc Unit_libio_wstrops_os.fn_glibc_wstrops'23enlarge_userbuf;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_seekoff;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_pbackfail;
  IFunc Unit_libio_wstrops_os.fn__IO_wstr_finish;
  Unit_libio_wstrops_os.item_glibc_wstrops'23str'2e257;
  Unit_libio_wstrops_os.item_glibc_wstrops'23str'2e258;
  Unit_libio_wstrops_os.item_glibc_wstrops'23str'2e259;
  Unit_locale_CZ2daddress_os.item__nl_C_LC_ADDRESS;
  Unit_locale_CZ2daddress_os.item_glibc_C_address'23str'2e40;
  Unit_locale_CZ2daddress_os.item_glibc_C_address'23str'2e41;
  Unit_locale_CZ2dcollate_os.item__nl_C_LC_COLLATE;
  Unit_locale_CZ2dcollate_os.item_glibc_C_collate'23collseqmb;
  Unit_locale_CZ2dcollate_os.item_glibc_C_collate'23collseqwc;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class32;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_alnum;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_alpha;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_blank;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_cntrl;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_digit;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_graph;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_lower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_print;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_punct;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_space;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_upper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_xdigit;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_map_tolower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_map_toupper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_tolower].

Lemma hello_image_linked_items_11_zero : zero_nonneg hello_image_linked_items_11 = true.
Proof. reflexivity. Qed.

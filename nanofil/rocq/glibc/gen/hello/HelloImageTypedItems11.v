(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedEN HelloImageTypedIO13 HelloImageTypedIO14 HelloImageTypedIO15 HelloImageTypedIO16 HelloImageTypedObjects03 HelloImageTypedSA HelloImageTypedWO HelloImageTypedWP01 HelloImageTypedWU.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_11 : module :=
  [IFunc hello_image_fn__IO_wfile_underflow_maybe_mmap;
  IFunc hello_image_fn___GI__IO_wfile_overflow;
  IFunc hello_image_fn___GI__IO_wfile_sync;
  IFunc hello_image_fn___GI__IO_wfile_seekoff;
  IFunc hello_image_fn___GI__IO_wfile_xsputn;
  hello_image_item_glibc_wfileops'23str'2e254;
  hello_image_item_glibc_wfileops'23str'2e255;
  hello_image_item_glibc_wfileops'23str'2e256;
  IFunc hello_image_fn___GI__IO_least_wmarker;
  IFunc hello_image_fn___GI__IO_switch_to_main_wget_area;
  IFunc hello_image_fn___GI__IO_switch_to_wbackup_area;
  IFunc hello_image_fn___GI__IO_wsetb;
  IFunc hello_image_fn___GI__IO_wdefault_pbackfail;
  IFunc hello_image_fn___GI__IO_wdefault_finish;
  IFunc hello_image_fn___GI__IO_wdefault_uflow;
  IFunc hello_image_fn___GI___woverflow;
  IFunc hello_image_fn___GI___wunderflow;
  IFunc hello_image_fn___GI__IO_wdefault_xsputn;
  IFunc hello_image_fn___GI__IO_wdefault_xsgetn;
  IFunc hello_image_fn___GI__IO_wdoallocbuf;
  IFunc hello_image_fn___GI__IO_wdefault_doallocate;
  IFunc hello_image_fn___GI__IO_switch_to_wget_mode;
  IFunc hello_image_fn___GI__IO_free_wbackup_area;
  IFunc hello_image_fn_glibc_wgenops'23save_for_wbackup;
  IFunc hello_image_fn__IO_wmem_sync;
  IFunc hello_image_fn__IO_wmem_finish;
  IFunc hello_image_fn__IO_wmem_setbuf;
  IFunc hello_image_fn__IO_wmem_doallocate;
  IFunc hello_image_fn___wprintf;
  hello_image_item_wprintf;
  IFunc hello_image_fn__IO_wstr_overflow;
  IFunc hello_image_fn__IO_wstr_underflow;
  IFunc hello_image_fn__IO_wstr_count;
  IFunc hello_image_fn_glibc_wstrops'23enlarge_userbuf;
  IFunc hello_image_fn__IO_wstr_seekoff;
  IFunc hello_image_fn__IO_wstr_pbackfail;
  IFunc hello_image_fn__IO_wstr_finish;
  hello_image_item_glibc_wstrops'23str'2e257;
  hello_image_item_glibc_wstrops'23str'2e258;
  hello_image_item_glibc_wstrops'23str'2e259;
  hello_image_item__nl_C_LC_ADDRESS;
  hello_image_item_glibc_C_address'23str'2e40;
  hello_image_item_glibc_C_address'23str'2e41;
  hello_image_item__nl_C_LC_COLLATE;
  hello_image_item_glibc_C_collate'23collseqmb;
  hello_image_item_glibc_C_collate'23collseqwc;
  hello_image_item__nl_C_LC_CTYPE;
  hello_image_item__nl_C_LC_CTYPE_class;
  hello_image_item__nl_C_LC_CTYPE_class32;
  hello_image_item__nl_C_LC_CTYPE_class_alnum;
  hello_image_item__nl_C_LC_CTYPE_class_alpha;
  hello_image_item__nl_C_LC_CTYPE_class_blank;
  hello_image_item__nl_C_LC_CTYPE_class_cntrl;
  hello_image_item__nl_C_LC_CTYPE_class_digit;
  hello_image_item__nl_C_LC_CTYPE_class_graph;
  hello_image_item__nl_C_LC_CTYPE_class_lower;
  hello_image_item__nl_C_LC_CTYPE_class_print;
  hello_image_item__nl_C_LC_CTYPE_class_punct;
  hello_image_item__nl_C_LC_CTYPE_class_space;
  hello_image_item__nl_C_LC_CTYPE_class_upper;
  hello_image_item__nl_C_LC_CTYPE_class_xdigit;
  hello_image_item__nl_C_LC_CTYPE_map_tolower;
  hello_image_item__nl_C_LC_CTYPE_map_toupper;
  hello_image_item__nl_C_LC_CTYPE_tolower].

Lemma hello_image_items_11_zero : zero_nonneg hello_image_items_11 = true.
Proof. reflexivity. Qed.

(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImage_hello HelloImage_versionZ2detc HelloImage_xallocZ2ddie HelloImage_xmalloc Unit_assert___libc_assert_fail_os Unit_csu_errnoZ2dloc_os Unit_csu_errno_os.
From Glibc Require Import Unit_ctype_ctypeZ2dinfo_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_02 : module :=
  [HelloImage_versionZ2detc.item_version'2detc'23str'2e53;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e54;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e55;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e56;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e57;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e58;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e59;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e60;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e61;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e62;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e63;
  HelloImage_versionZ2detc.item_version'2detc'23str'2e64;
  IFunc HelloImage_xallocZ2ddie.fn_xalloc_die;
  HelloImage_xallocZ2ddie.item_xalloc'2ddie'23str'2e41;
  HelloImage_xallocZ2ddie.item_xalloc'2ddie'23str'2e42;
  HelloImage_xallocZ2ddie.item_xalloc'2ddie'23str'2e43;
  IFunc HelloImage_xmalloc.fn_xmalloc;
  IFunc HelloImage_xmalloc.fn_xcharalloc;
  IFunc HelloImage_xmalloc.fn_xrealloc;
  IFunc HelloImage_xmalloc.fn_xpalloc;
  IFunc HelloImage_hello.fn_main;
  HelloImage_hello.item_hello'23parse_options'2elongopts'2e64;
  HelloImage_hello.item_hello'23str'2e54;
  HelloImage_hello.item_hello'23str'2e55;
  HelloImage_hello.item_hello'23str'2e56;
  HelloImage_hello.item_hello'23str'2e57;
  HelloImage_hello.item_hello'23str'2e58;
  HelloImage_hello.item_hello'23str'2e59;
  HelloImage_hello.item_hello'23str'2e60;
  HelloImage_hello.item_hello'23str'2e61;
  HelloImage_hello.item_hello'23str'2e62;
  HelloImage_hello.item_hello'23str'2e63;
  HelloImage_hello.item_hello'23str'2e65;
  HelloImage_hello.item_hello'23str'2e66;
  HelloImage_hello.item_hello'23str'2e67;
  HelloImage_hello.item_hello'23str'2e68;
  HelloImage_hello.item_hello'23str'2e69;
  HelloImage_hello.item_hello'23str'2e70;
  HelloImage_hello.item_hello'23str'2e71;
  HelloImage_hello.item_hello'23str'2e72;
  HelloImage_hello.item_hello'23str'2e73;
  HelloImage_hello.item_hello'23str'2e74;
  HelloImage_hello.item_hello'23str'2e75;
  HelloImage_hello.item_hello'23str'2e76;
  HelloImage_hello.item_hello'23str'2e77;
  HelloImage_hello.item_hello'23str'2e78;
  HelloImage_hello.item_hello'23str'2e79;
  HelloImage_hello.item_hello'23str'2e80;
  HelloImage_hello.item_hello'23str'2e81;
  HelloImage_hello.item_hello'23str'2e82;
  HelloImage_hello.item_hello'23str'2e83;
  IFunc Unit_assert___libc_assert_fail_os.fn___libc_assert_fail;
  Unit_assert___libc_assert_fail_os.item_glibc___libc_assert_fail'23str'2e21;
  Unit_assert___libc_assert_fail_os.item_glibc___libc_assert_fail'23str'2e22;
  IFunc Unit_csu_errnoZ2dloc_os.fn___GI___errno_location;
  Unit_csu_errnoZ2dloc_os.item___errno_location;
  Unit_csu_errno_os.item___libc_errno;
  Unit_csu_errno_os.item_errno;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___ctype_b_loc;
  IFunc Unit_ctype_ctypeZ2dinfo_os.fn___GI___ctype_init;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype32_b;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype32_tolower;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype32_toupper;
  Unit_ctype_ctypeZ2dinfo_os.item___ctype_b].

Lemma hello_image_linked_items_02_zero : zero_nonneg hello_image_linked_items_02 = true.
Proof. reflexivity. Qed.

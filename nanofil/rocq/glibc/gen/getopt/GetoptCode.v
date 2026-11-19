(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_posix_getopt1_os Unit_posix_getopt_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition getopt_module : module :=
  [IFunc Unit_posix_getopt_os.fn_glibc_getopt'23process_long_option;
  IFunc Unit_posix_getopt_os.fn__getopt_internal_r;
  IFunc Unit_posix_getopt_os.fn__getopt_internal;
  Unit_posix_getopt_os.item_glibc_getopt'23getopt_data;
  Unit_posix_getopt_os.item_optarg;
  Unit_posix_getopt_os.item_opterr;
  Unit_posix_getopt_os.item_optind;
  Unit_posix_getopt_os.item_optopt;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e138;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e139;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e140;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e141;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e142;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e143;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e144;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e145;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e146;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e147;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e148;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e149;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e150;
  IFunc Unit_posix_getopt1_os.fn_getopt_long].

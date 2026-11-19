(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_posix_getopt1_os Unit_posix_getopt_os Unit_posix_sysconf_os Unit_posix_wait4_os Unit_posix_waitpid_os Unit_resource_getrlimit64_os Unit_setjmp_longjmp_os.
From Glibc Require Import Unit_stdioZ2dcommon__fitoa_word_os Unit_stdioZ2dcommon_asprintf_os Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_18 : module :=
  [Unit_posix_getopt_os.item_glibc_getopt'23str'2e148;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e149;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e150;
  IFunc Unit_posix_getopt1_os.fn_getopt_long;
  IFunc Unit_posix_sysconf_os.fn___GI___sysconf;
  IFunc Unit_posix_sysconf_os.fn_glibc_sysconf'23posix_sysconf;
  IFunc Unit_posix_sysconf_os.fn_glibc_sysconf'23__sysconf_check_spec;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e302;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e303;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e304;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e305;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e306;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e307;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e308;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e309;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e348;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e349;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e350;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e351;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e353;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e354;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e355;
  Unit_posix_sysconf_os.item_glibc_sysconf'23str'2e356;
  IFunc Unit_posix_wait4_os.fn___GI___wait4;
  IFunc Unit_posix_waitpid_os.fn___GI___waitpid;
  IFunc Unit_resource_getrlimit64_os.fn___GI___getrlimit64;
  Unit_resource_getrlimit64_os.item___GI___getrlimit;
  IFunc Unit_setjmp_longjmp_os.fn___libc_siglongjmp;
  Unit_setjmp_longjmp_os.item___libc_longjmp;
  IFunc Unit_stdioZ2dcommon__fitoa_word_os.fn__itoa_word;
  IFunc Unit_stdioZ2dcommon_asprintf_os.fn____asprintf;
  Unit_stdioZ2dcommon_asprintf_os.item___GI___asprintf;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item__sys_errlist_internal;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item__sys_errlist_internal_len;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e247;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e248;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e249;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e250;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e251;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e252;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e253;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e254;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e255;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e256;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e257;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e258;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e259;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e260;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e261;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e262;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e263;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e264;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e265;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e266;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e267;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e268;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e269;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e270;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e271;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e272;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e273;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e274;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e275;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e276].

Lemma hello_image_linked_items_18_zero : zero_nonneg hello_image_linked_items_18 = true.
Proof. reflexivity. Qed.

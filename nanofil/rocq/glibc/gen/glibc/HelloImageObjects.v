(** This file defines captured glibc objects used only by one linked image.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRBytes IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

(** This file defines checked IR from glibc’s `debug/chk_fail.os` object. *)
Module Unit_debug_chk_fail_os.
Definition fn___GI___chk_fail : func :=
  ir_fn{ "export" "__GI___chk_fail"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_chk_fail#str.134";
    call void $"__GI___fortify_fail"(P %"v0")
    => ret void
} }.

Definition item_glibc_chk_fail'23str'2e134 : item :=
  (IData (a "glibc_chk_fail#str.134") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 102); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).
End Unit_debug_chk_fail_os.

(** This file defines checked IR from glibc’s `debug/fortify_fail.os` object. *)
Module Unit_debug_fortify_fail_os.
Definition fn___GI___fortify_fail : func :=
  ir_fn{ "export" "__GI___fortify_fail"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_fortify_fail#str.19";
    %"v3" : P = Copy $"glibc_fortify_fail#str.20";
    call void $"__libc_message_impl"(P %"v2", P %"v3", P %"v0")
    => ret void
} }.

Definition item_glibc_fortify_fail'23str'2e19 : item :=
  (IData (a "glibc_fortify_fail#str.19") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_fortify_fail'23str'2e20 : item :=
  (IData (a "glibc_fortify_fail#str.20") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 58); (Item Wb 32); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 10); (Item Wb 0)]).
End Unit_debug_fortify_fail_os.

(** This file defines checked IR from glibc’s `debug/readonly-area.os` object. *)
Module Unit_debug_readonlyZ2darea_os.
Definition fn___readonly_area : func :=
  ir_fn{ "export" "__readonly_area"(P %"v0", L %"v2") -> (RClass W) {
  @"start":
    call %"v6" : W = $"__readonly_area_fallback"(P %"v0", L %"v2")
    => ret %"v6"
} }.
End Unit_debug_readonlyZ2darea_os.

(** This file defines checked IR from glibc’s `dirent/closedir.os` object. *)
Module Unit_dirent_closedir_os.
Definition fn___closedir : func :=
  ir_fn{ "export" "__closedir"(P %"v0") -> (RClass W) {
  @"start":
    %"v7" : L = Ptoi %"v0";
    %"v8" : L = Ptoi #0;
    %"v9" : W = (Cmp Eq L) %"v7", %"v8"
    => br %"v9" ? "L3" : "L5";
  @"L3":
    %"v10" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk0" + 0] <- #22
    => ret #4294967295;
  @"L5":
    %"chk1" : A = (Check 0 4 Read 1) %"v0";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call void $"free"(P %"v0");
    call %"v17" : W = $"__GI___close_nocancel"(W %"v14")
    => ret %"v17"
} }.
End Unit_dirent_closedir_os.

(** This file defines checked IR from glibc’s `dirent/getdents64.os` object. *)
Module Unit_dirent_getdents64_os.
Definition fn___GI___getdents64 : func :=
  ir_fn{ "export" "__GI___getdents64"(W %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call %"v9" : W = $"zsys_getdents"(W %"v0", P %"v2", L %"v4");
    %"v10" : L = (Ext Sw) %"v9"
    => ret %"v10"
} }.
End Unit_dirent_getdents64_os.

(** This file defines checked IR from glibc’s `elf/dl-libc.os` object. *)
Module Unit_elf_dlZ2dlibc_os.
Definition fn___libc_dlclose : func :=
  ir_fn{ "export" "__libc_dlclose"(P %"v0") -> (RClass W) {
  @"start":
    => ret #0
} }.

Definition fn___libc_dlopen_mode : func :=
  ir_fn{ "export" "__libc_dlopen_mode"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"zsys_dlopen"(P %"v0", W %"v2")
    => ret %"v6"
} }.

Definition fn___libc_dlsym : func :=
  ir_fn{ "export" "__libc_dlsym"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"zsys_dlsym"(P %"v0", P %"v2")
    => ret %"v6"
} }.
End Unit_elf_dlZ2dlibc_os.

(** This file defines checked IR from glibc’s `io/fcntl_nocancel.os` object. *)
Module Unit_io_fcntl_nocancel_os.
Definition fn___GI___fcntl64_nocancel : func :=
  ir_fn{ "export" "__GI___fcntl64_nocancel"(W %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"va_args" : P = VaArgs #16;
    %"v4" : P = Copy $"zsys_fcntl";
    %"v5" : P = VaArgs #0;
    call %"v6" : P = $"zcall"(P %"v4", P %"v5");
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret %"v7"
} }.
End Unit_io_fcntl_nocancel_os.

(** This file defines checked IR from glibc’s `io/fstatat64.os` object. *)
Module Unit_io_fstatat64_os.
Definition fn___GI___fstatat64 : func :=
  ir_fn{ "export" "__GI___fstatat64"(W %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    call %"v12" : W = $"zsys_fstatat"(W %"v0", P %"v2", P %"v4", W %"v6")
    => ret %"v12"
} }.
End Unit_io_fstatat64_os.

(** This file defines checked IR from glibc’s `io/open64_nocancel.os` object. *)
Module Unit_io_open64_nocancel_os.
Definition fn___GI___open64_nocancel : func :=
  ir_fn{ "export" "__GI___open64_nocancel"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"va_args" : P = VaArgs #16;
    %"v4" : P = Copy $"zsys_open";
    %"v5" : P = VaArgs #0;
    call %"v6" : P = $"zcall"(P %"v4", P %"v5");
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret %"v7"
} }.

Definition item___GI___open_nocancel : item :=
  (IAlias (a "__GI___open_nocancel") (a "export") (a "__GI___open64_nocancel")).
End Unit_io_open64_nocancel_os.

(** This file defines checked IR from glibc’s `io/open64.os` object. *)
Module Unit_io_open64_os.
Definition item___GI___open : item :=
  (IAlias (a "__GI___open") (a "export") (a "__libc_open64")).

Definition fn___libc_open64 : func :=
  ir_fn{ "export" "__libc_open64"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"va_args" : P = VaArgs #16;
    %"v4" : P = Copy $"zsys_open";
    %"v5" : P = VaArgs #0;
    call %"v6" : P = $"zcall"(P %"v4", P %"v5");
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret %"v7"
} }.
End Unit_io_open64_os.

(** This file defines checked IR from glibc’s `io/read_nocancel.os` object. *)
Module Unit_io_read_nocancel_os.
Definition fn___GI___read_nocancel : func :=
  ir_fn{ "export" "__GI___read_nocancel"(W %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call %"v9" : L = $"zsys_read"(W %"v0", P %"v2", L %"v4")
    => ret %"v9"
} }.
End Unit_io_read_nocancel_os.

(** This file defines checked IR from glibc’s `io/read.os` object. *)
Module Unit_io_read_os.
Definition fn___GI___libc_read : func :=
  ir_fn{ "export" "__GI___libc_read"(W %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call %"v9" : L = $"zsys_read"(W %"v0", P %"v2", L %"v4")
    => ret %"v9"
} }.

Definition item___GI___read : item :=
  (IAlias (a "__GI___read") (a "export") (a "__GI___libc_read")).
End Unit_io_read_os.

(** This file defines checked IR from glibc’s `io/stat64.os` object. *)
Module Unit_io_stat64_os.
Definition fn___GI___stat64 : func :=
  ir_fn{ "export" "__GI___stat64"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v7" : W = $"__GI___fstatat64"(W #4294967196, P %"v0", P %"v2", W #0)
    => ret %"v7"
} }.
End Unit_io_stat64_os.

(** This file defines checked IR from glibc’s `libio/feof_u.os` object. *)
Module Unit_libio_feof_u_os.
Definition fn___feof_unlocked : func :=
  ir_fn{ "export" "__feof_unlocked"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #16;
    %"v8" : W = (Cmp Ne W) %"v7", #0
    => ret %"v8"
} }.
End Unit_libio_feof_u_os.

(** This file defines checked IR from glibc’s `libio/iofputws_u.os` object. *)
Module Unit_libio_iofputws_u_os.
Definition fn___GI_fputws_unlocked : func :=
  ir_fn{ "export" "__GI_fputws_unlocked"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v6" : L = $"__wcslen"(P %"v0");
    call %"v57" : W = $"_IO_fwide"(P %"v2", W #1);
    %"v59" : W = (Cmp Eq W) %"v57", #1
    => br %"v59" ? "L60" : "L61";
  @"L60":
    %"v63" = %"v2" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v64";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v66" = %"v64" +p #56;
    %"chk1" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v67";
    rawcall %"v71" : L = %"chk2"(P %"v2", P %"v0", L %"v6");
    %"v73" : W = (Cmp Eq L) %"v71", %"v6"
    => goto "L61";
  @"L61" [%"v75" : W = phi("start" => #0, "iw_1.join" => %"v73")]:
    => br %"v75" ? "L14" : "L13";
  @"L13":
    => goto "L14";
  @"L14" [%"pr.1" : W = phi("L13" => #4294967295, "L61" => #1)]:
    => ret %"pr.1"
} }.
End Unit_libio_iofputws_u_os.

(** This file defines checked IR from glibc’s `locale/C-address.os` object. *)
Module Unit_locale_CZ2daddress_os.
Definition item__nl_C_LC_ADDRESS : item :=
  (IData (a "_nl_C_LC_ADDRESS") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 13); (Zero 4); (Sym (a "glibc_C_address#str.40") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Item Ww 0); (Zero 4); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "glibc_C_address#str.41") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_address'23str'2e40 : item :=
  (IData (a "glibc_C_address#str.40") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 97); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 102); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 100); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 98); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 37); (Item Wb 104); (Item Wb 32); (Item Wb 37); (Item Wb 101); (Item Wb 32); (Item Wb 37); (Item Wb 114); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 67); (Item Wb 45); (Item Wb 37); (Item Wb 122); (Item Wb 32); (Item Wb 37); (Item Wb 84); (Item Wb 37); (Item Wb 78); (Item Wb 37); (Item Wb 99); (Item Wb 37); (Item Wb 78); (Item Wb 0)]).

Definition item_glibc_C_address'23str'2e41 : item :=
  (IData (a "glibc_C_address#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).
End Unit_locale_CZ2daddress_os.

(** This file defines checked IR from glibc’s `locale/C-measurement.os` object. *)
Module Unit_locale_CZ2dmeasurement_os.
Definition item__nl_C_LC_MEASUREMENT : item :=
  (IData (a "_nl_C_LC_MEASUREMENT") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 2); (Zero 4); (Sym (a "glibc_C_measurement#str.40") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_measurement'23str'2e40 : item :=
  (IData (a "glibc_C_measurement#str.40") (LRo (a "local")) 1 [(Item Wb 1); (Item Wb 0)]).
End Unit_locale_CZ2dmeasurement_os.

(** This file defines checked IR from glibc’s `locale/C-messages.os` object. *)
Module Unit_locale_CZ2dmessages_os.
Definition item__nl_C_LC_MESSAGES : item :=
  (IData (a "_nl_C_LC_MESSAGES") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 5); (Zero 4); (Sym (a "glibc_C_messages#str.40") 0); (Sym (a "glibc_C_messages#str.41") 0); (Sym (a "glibc_C_messages#str.42") 0); (Sym (a "glibc_C_messages#str.42") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_messages'23str'2e40 : item :=
  (IData (a "glibc_C_messages#str.40") (LRo (a "local")) 1 [(Item Wb 94); (Item Wb 91); (Item Wb 121); (Item Wb 89); (Item Wb 93); (Item Wb 0)]).

Definition item_glibc_C_messages'23str'2e41 : item :=
  (IData (a "glibc_C_messages#str.41") (LRo (a "local")) 1 [(Item Wb 94); (Item Wb 91); (Item Wb 110); (Item Wb 78); (Item Wb 93); (Item Wb 0)]).

Definition item_glibc_C_messages'23str'2e42 : item :=
  (IData (a "glibc_C_messages#str.42") (LRo (a "local")) 1 [(Item Wb 0)]).
End Unit_locale_CZ2dmessages_os.

(** This file defines checked IR from glibc’s `locale/C-name.os` object. *)
Module Unit_locale_CZ2dname_os.
Definition item__nl_C_LC_NAME : item :=
  (IData (a "_nl_C_LC_NAME") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 7); (Zero 4); (Sym (a "glibc_C_name#str.40") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "glibc_C_name#str.41") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_name'23str'2e40 : item :=
  (IData (a "glibc_C_name#str.40") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 112); (Item Wb 37); (Item Wb 116); (Item Wb 37); (Item Wb 103); (Item Wb 37); (Item Wb 116); (Item Wb 37); (Item Wb 109); (Item Wb 37); (Item Wb 116); (Item Wb 37); (Item Wb 102); (Item Wb 0)]).

Definition item_glibc_C_name'23str'2e41 : item :=
  (IData (a "glibc_C_name#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).
End Unit_locale_CZ2dname_os.

(** This file defines checked IR from glibc’s `locale/C-numeric.os` object. *)
Module Unit_locale_CZ2dnumeric_os.
Definition item__nl_C_LC_NUMERIC : item :=
  (IData (a "_nl_C_LC_NUMERIC") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 6); (Zero 4); (Sym (a "glibc_C_numeric#str.40") 0); (Sym (a "glibc_C_numeric#str.41") 0); (Sym (a "glibc_C_numeric#str.41") 0); (Item Ww 46); (Zero 4); (Item Ww 0); (Zero 4); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_numeric'23str'2e40 : item :=
  (IData (a "glibc_C_numeric#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 0)]).

Definition item_glibc_C_numeric'23str'2e41 : item :=
  (IData (a "glibc_C_numeric#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).
End Unit_locale_CZ2dnumeric_os.

(** This file defines checked IR from glibc’s `locale/C-paper.os` object. *)
Module Unit_locale_CZ2dpaper_os.
Definition item__nl_C_LC_PAPER : item :=
  (IData (a "_nl_C_LC_PAPER") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 3); (Zero 4); (Item Ww 297); (Zero 4); (Item Ww 210); (Zero 4); (Sym (a "_nl_C_codeset") 0)]).
End Unit_locale_CZ2dpaper_os.

(** This file defines checked IR from glibc’s `locale/C-telephone.os` object. *)
Module Unit_locale_CZ2dtelephone_os.
Definition item__nl_C_LC_TELEPHONE : item :=
  (IData (a "_nl_C_LC_TELEPHONE") (LRo (a "export")) 8 [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 5); (Zero 4); (Sym (a "glibc_C_telephone#str.40") 0); (Sym (a "glibc_C_telephone#str.41") 0); (Sym (a "glibc_C_telephone#str.41") 0); (Sym (a "glibc_C_telephone#str.41") 0); (Sym (a "_nl_C_codeset") 0)]).

Definition item_glibc_C_telephone'23str'2e40 : item :=
  (IData (a "glibc_C_telephone#str.40") (LRo (a "local")) 1 [(Item Wb 43); (Item Wb 37); (Item Wb 99); (Item Wb 32); (Item Wb 37); (Item Wb 97); (Item Wb 32); (Item Wb 37); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_C_telephone'23str'2e41 : item :=
  (IData (a "glibc_C_telephone#str.41") (LRo (a "local")) 1 [(Item Wb 0)]).
End Unit_locale_CZ2dtelephone_os.

(** This file defines checked IR from glibc’s `locale/xlocale.os` object. *)
Module Unit_locale_xlocale_os.
Definition item__nl_C_locobj : item :=
  (IData (a "_nl_C_locobj") (LRo (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE") 0); (Sym (a "_nl_C_LC_NUMERIC") 0); (Sym (a "_nl_C_LC_TIME") 0); (Sym (a "_nl_C_LC_COLLATE") 0); (Sym (a "_nl_C_LC_MONETARY") 0); (Sym (a "_nl_C_LC_MESSAGES") 0); (Zero 8); (Sym (a "_nl_C_LC_PAPER") 0); (Sym (a "_nl_C_LC_NAME") 0); (Sym (a "_nl_C_LC_ADDRESS") 0); (Sym (a "_nl_C_LC_TELEPHONE") 0); (Sym (a "_nl_C_LC_MEASUREMENT") 0); (Sym (a "_nl_C_LC_IDENTIFICATION") 0); (Sym (a "_nl_C_LC_CTYPE_class") 256); (Sym (a "_nl_C_LC_CTYPE_tolower") 512); (Sym (a "_nl_C_LC_CTYPE_toupper") 512); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0)]).
End Unit_locale_xlocale_os.

(** This file defines checked IR from glibc’s `misc/getclktck.os` object. *)
Module Unit_misc_getclktck_os.
Definition fn___getclktck : func :=
  ir_fn{ "export" "__getclktck"() -> (RClass W) {
  @"start":
    %"v0" : P = Copy $"_dl_clktck";
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v1" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => br %"v1" ? "L4" : "L3";
  @"L3":
    => goto "L4";
  @"L4" [%"v5" : W = phi("L3" => #100, "start" => %"v1")]:
    => ret %"v5"
} }.
End Unit_misc_getclktck_os.

(** This file defines checked IR from glibc’s `misc/getdtsz.os` object. *)
Module Unit_misc_getdtsz_os.
Definition fn___getdtablesize : func :=
  ir_fn{ "export" "__getdtablesize"() -> (RClass W) {
  @"start":
    %"v0" : P = (Alloc 8) #16;
    call %"v4" : W = $"__GI___getrlimit"(W #7, P %"v0");
    %"v5" : W = (Cmp Slt W) %"v4", #0
    => br %"v5" ? "L3" : "L2";
  @"L2":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v6" : L = (RawLoad LdL 0) %"chk0"
    => goto "L3";
  @"L3" [%"v7" : L = phi("L2" => %"v6", "start" => #256)]:
    => ret %"v7"
} }.
End Unit_misc_getdtsz_os.

(** This file defines checked IR from glibc’s `misc/mremap.os` object. *)
Module Unit_misc_mremap_os.
Definition fn___GI___mremap : func :=
  ir_fn{ "export" "__GI___mremap"(P %"v0", L %"v2", L %"v4", W %"v6") -> (RClass P) {
  @"start":
    %"v8" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #32;
    %"v17" : W = And %"v6", #4294967288
    => br %"v17" ? "L10" : "L12";
  @"L10":
    %"v18" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v18";
    store Ww [%"chk0" + 0] <- #22;
    (Flight (a "v21") Copy [(FValue (Const 18446744073709551615))] LowerNone)
    => ret %"v21";
  @"L12":
    %"v28" : W = And %"v6", #6
    => br %"v28" ? "L23" : "L25";
  @"L23":
    %"chk1" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk1" + 0] <- %"va_args";
    %"v29" : P = VaArg %"v8"
    => goto "L25";
  @"L25" [%"pr.1" : P = phi("L23" => %"v29", "L12" => #0)]:
    call %"v35" : P = $"zsys_mremap"(P %"v0", L %"v2", L %"v4", W %"v6", P %"pr.1")
    => ret %"v35"
} }.
End Unit_misc_mremap_os.

(** This file defines checked IR from glibc’s `misc/munmap.os` object. *)
Module Unit_misc_munmap_os.
Definition item___GI___munmap : item :=
  (IAlias (a "__GI___munmap") (a "export") (a "__munmap")).

Definition item___munmap : item :=
  (IOutside (a "__munmap") (TApp "func" [(a "__munmap"); (a "export"); (a "data"); (TList []); (TList [(TApp "block" [(a "start"); (TList []); (TList [(TApp "let" [(TApp "tmp" [(a "v0")]); (a "p"); (a "copy"); (TList [(TApp "global" [(a "zsys_munmap")])])]); (TApp "let" [(TApp "tmp" [(a "v1")]); (a "p"); (a "va_args"); (TList [(TApp "const" [(TInt 0)])])]); (TApp "call" [(TApp "result" [(TApp "tmp" [(a "v2")]); (a "p")]); (TApp "global" [(a "zcall")]); (TList [(TApp "arg" [(a "p"); (TApp "tmp" [(a "v0")])]); (TApp "arg" [(a "p"); (TApp "tmp" [(a "v1")])])])])]); (TApp "ret" [(TApp "tmp" [(a "v2")])])])])])).
End Unit_misc_munmap_os.

(** This file defines checked IR from glibc’s `misc/sysinfo.os` object. *)
Module Unit_misc_sysinfo_os.
Definition item___sysinfo : item :=
  (IOutside (a "__sysinfo") (TApp "func" [(a "__sysinfo"); (a "export"); (a "data"); (TList []); (TList [(TApp "block" [(a "start"); (TList []); (TList [(TApp "let" [(TApp "tmp" [(a "v0")]); (a "p"); (a "copy"); (TList [(TApp "global" [(a "zsys_sysinfo")])])]); (TApp "let" [(TApp "tmp" [(a "v1")]); (a "p"); (a "va_args"); (TList [(TApp "const" [(TInt 0)])])]); (TApp "call" [(TApp "result" [(TApp "tmp" [(a "v2")]); (a "p")]); (TApp "global" [(a "zcall")]); (TList [(TApp "arg" [(a "p"); (TApp "tmp" [(a "v0")])]); (TApp "arg" [(a "p"); (TApp "tmp" [(a "v1")])])])])]); (TApp "ret" [(TApp "tmp" [(a "v2")])])])])])).
End Unit_misc_sysinfo_os.

(** This file defines checked IR from glibc’s `nptl/lowlevellock.os` object. *)
Module Unit_nptl_lowlevellock_os.
Definition fn___GI___lll_lock_wait_private : func :=
  ir_fn{ "export" "__GI___lll_lock_wait_private"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = (Cmp Eq W) %"v6", #2
    => br %"v7" ? "iw_1.L29" : "L10";
  @"L10":
    %"chk1" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L15";
  @"L15" [%"v17" : W = phi("L10" => %"v14", "L15" => %"v18")]:
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v0";
    %"v18" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"v17", #2;
    %"v19" : W = (Cmp Eq W) %"v18", %"v17"
    => br %"v19" ? "L16" : poll "L15";
  @"L16":
    %"v20" : W = (Cmp Ne W) %"v17", #0
    => br %"v20" ? "iw_1.L29" : "L12";
  @"iw_1.L29":
    call void $"zsys_futex_wait"(P %"v0", W #2, W #1)
    => goto poll "L10";
  @"L12":
    => ret void
} }.

Definition fn___GI___lll_lock_wake_private : func :=
  ir_fn{ "export" "__GI___lll_lock_wake_private"(P %"v0") -> RVoid {
  @"start":
    call void $"zsys_futex_wake"(P %"v0", W #1, W #1)
    => ret void
} }.
End Unit_nptl_lowlevellock_os.

(** This file defines checked IR from glibc’s `nptl/pthread_rwlock_init.os` object. *)
Module Unit_nptl_pthread_rwlock_init_os.
Definition item___GI___pthread_rwlock_init : item :=
  (IAlias (a "__GI___pthread_rwlock_init") (a "export") (a "___pthread_rwlock_init")).

Definition fn____pthread_rwlock_init : func :=
  ir_fn{ "export" "___pthread_rwlock_init"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v6" : L = Ptoi %"v2";
    %"v7" : W = (Cmp Ne L) %"v6", #0
    => br %"v7" ? "L10" : "L9";
  @"L9":
    %"v11" : P = Copy $"glibc_pthread_rwlock_init#default_rwlockattr"
    => goto "L10";
  @"L10" [%"v12" : P = phi("L9" => %"v11", "start" => %"v2")]:
    call %"v14" : P = $"__GI_memset"(P %"v0", W #0, L #56);
    %"v16" = %"v0" +p #48;
    %"chk0" : A = (Check 0 4 Read 1) %"v12";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk1" + 0] <- %"v18";
    %"v20" = %"v0" +p #28;
    %"v22" = %"v12" +p #4;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v22";
    %"v23" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v24" : W = (Cmp Ne W) %"v23", #0;
    %"chk3" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"v20";
    store Ww [%"chk3" + 0] <- %"v24"
    => ret #0
} }.

Definition item_glibc_pthread_rwlock_init'23default_rwlockattr : item :=
  (IData (a "glibc_pthread_rwlock_init#default_rwlockattr") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0)]).
End Unit_nptl_pthread_rwlock_init_os.

(** This file defines checked IR from glibc’s `nss/hash-string.os` object. *)
Module Unit_nss_hashZ2dstring_os.
Definition fn___hash_string : func :=
  ir_fn{ "export" "__hash_string"(P %"v0") -> (RClass L) {
  @"start":
    => goto "L6";
  @"L6" [%"pr.3" : P = phi("start" => %"v0", "L25" => %"v16", "L7" => %"v16"); %"pr.2" : L = phi("start" => #0, "L25" => %"v37", "L7" => %"v20")]:
    %"chk0" : A = (Check 0 1 Read 1) %"pr.3";
    %"v10" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v11" : W = (Cmp Ne W) %"v10", #0
    => br %"v11" ? "L7" : "L8";
  @"L7":
    %"v13" : L = Shl %"pr.2", #4;
    %"v16" = %"pr.3" +p #1;
    %"v17" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v18" : W = (Ext Ub) %"v17";
    %"v19" : L = (Ext Uw) %"v18";
    %"v20" : L = Add %"v13", %"v19";
    %"v24" : L = And %"v20", #4026531840;
    %"v29" : W = (Cmp Ne L) %"v24", #0
    => br %"v29" ? "L25" : poll "L6";
  @"L25":
    %"v33" : L = Shr %"v24", #24;
    %"v34" : L = Xor %"v20", %"v33";
    %"v37" : L = Xor %"v34", %"v24"
    => goto poll "L6";
  @"L8":
    => ret %"pr.2"
} }.
End Unit_nss_hashZ2dstring_os.

(** This file defines checked IR from glibc’s `posix/get_child_max.os` object. *)
Module Unit_posix_get_child_max_os.
Definition fn___get_child_max : func :=
  ir_fn{ "export" "__get_child_max"() -> (RClass L) {
  @"start":
    %"v0" : P = (Alloc 8) #16;
    call %"v4" : W = $"__GI___getrlimit"(W #6, P %"v0");
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => br %"v5" ? "L6" : "L7";
  @"L6":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v8" : L = (RawLoad LdL 0) %"chk0";
    %"v11" : W = (Cmp Ne L) %"v8", #18446744073709551615
    => goto "L7";
  @"L7" [%"v13" : W = phi("start" => #0, "L6" => %"v11")]:
    => br %"v13" ? "L1" : "L3";
  @"L1":
    %"chk1" : A = (Check 0 8 Read 1) %"v0";
    %"v14" : L = (RawLoad LdL 0) %"chk1"
    => ret %"v14";
  @"L3":
    => ret #18446744073709551615
} }.
End Unit_posix_get_child_max_os.

(** This file defines checked IR from glibc’s `posix/sched_cpucount.os` object. *)
Module Unit_posix_sched_cpucount_os.
Definition fn___GI___sched_cpucount : func :=
  ir_fn{ "export" "__GI___sched_cpucount"(L %"v0", P %"v2") -> (RClass W) {
  @"start":
    => goto "L6";
  @"L6" [%"pr.2" : W = phi("iw_1.join" => %"v25", "start" => #0); %"pr.1" : W = phi("iw_1.join" => %"v23", "start" => #0)]:
    %"v12" : L = Shr %"v0", #3;
    %"v13" : L = (Ext Sw) %"pr.2";
    %"v14" : W = (Cmp Ult L) %"v13", %"v12"
    => br %"v14" ? "L7" : "L9";
  @"L7":
    %"v19" : L = Shl %"v13", #3;
    %"v20" = %"v2" +p %"v19";
    %"chk0" : A = (Check 0 8 Read 1) %"v20";
    %"v21" : L = (RawLoad LdL 0) %"chk0"
    => goto "iw_1.L3";
  @"iw_1.L3" [%"iw_1.pr.2" : W = phi("iw_1.L4" => %"iw_1.v14", "L7" => #0); %"iw_1.pr.1" : L = phi("iw_1.L4" => %"iw_1.v12", "L7" => %"v21")]:
    %"iw_1.v8" : W = (Cmp Ne L) %"iw_1.pr.1", #0
    => br %"iw_1.v8" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    %"iw_1.v11" : L = Sub %"iw_1.pr.1", #1;
    %"iw_1.v12" : L = And %"iw_1.pr.1", %"iw_1.v11";
    %"iw_1.v14" : W = Add %"iw_1.pr.2", #1
    => goto poll "iw_1.L3";
  @"iw_1.join":
    %"v23" : W = Add %"pr.1", %"iw_1.pr.2";
    %"v25" : W = Add %"pr.2", #1
    => goto poll "L6";
  @"L9":
    => ret %"pr.1"
} }.
End Unit_posix_sched_cpucount_os.

(** This file defines checked IR from glibc’s `posix/wait4.os` object. *)
Module Unit_posix_wait4_os.
Definition fn___GI___wait4 : func :=
  ir_fn{ "export" "__GI___wait4"(W %"v0", P %"v2", W %"v4", P %"v6") -> (RClass W) {
  @"start":
    call %"v12" : W = $"zsys_wait4"(W %"v0", P %"v2", W %"v4", P %"v6")
    => ret %"v12"
} }.
End Unit_posix_wait4_os.

(** This file defines checked IR from glibc’s `posix/waitpid.os` object. *)
Module Unit_posix_waitpid_os.
Definition fn___GI___waitpid : func :=
  ir_fn{ "export" "__GI___waitpid"(W %"v0", P %"v2", W %"v4") -> (RClass W) {
  @"start":
    call %"v9" : W = $"__GI___wait4"(W %"v0", P %"v2", W %"v4", P #0)
    => ret %"v9"
} }.
End Unit_posix_waitpid_os.

(** This file defines checked IR from glibc’s `setjmp/longjmp.os` object. *)
Module Unit_setjmp_longjmp_os.
Definition item___libc_longjmp : item :=
  (IAlias (a "__libc_longjmp") (a "export") (a "__libc_siglongjmp")).

Definition fn___libc_siglongjmp : func :=
  ir_fn{ "export" "__libc_siglongjmp"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"zlongjmp"(P %"v5", W %"v2")
    => ret void
} }.
End Unit_setjmp_longjmp_os.

(** This file defines checked IR from glibc’s `stdio-common/asprintf.os` object. *)
Module Unit_stdioZ2dcommon_asprintf_os.
Definition item___GI___asprintf : item :=
  (IAlias (a "__GI___asprintf") (a "export") (a "___asprintf")).

Definition fn____asprintf : func :=
  ir_fn{ "export" "___asprintf"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- %"va_args";
    call %"v8" : W = $"__vasprintf_internal"(P %"v0", P %"v2", P %"v4", W #0)
    => ret %"v8"
} }.
End Unit_stdioZ2dcommon_asprintf_os.

(** This file defines checked IR from glibc’s `stdio-common/itoa-digits.os` object. *)
Module Unit_stdioZ2dcommon_itoaZ2ddigits_os.
Definition item___GI__itoa_lower_digits : item :=
  (IData (a "__GI__itoa_lower_digits") (LRo (a "export")) 1 ["0123456789abcdefghijklmnopqrstuvwxyz"%irbytes]).
End Unit_stdioZ2dcommon_itoaZ2ddigits_os.

(** This file defines checked IR from glibc’s `stdio-common/itoa-udigits.os` object. *)
Module Unit_stdioZ2dcommon_itoaZ2dudigits_os.
Definition item___GI__itoa_upper_digits : item :=
  (IData (a "__GI__itoa_upper_digits") (LRo (a "export")) 1 ["0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"%irbytes]).
End Unit_stdioZ2dcommon_itoaZ2dudigits_os.

(** This file defines checked IR from glibc’s `stdio-common/itowa-digits.os` object. *)
Module Unit_stdioZ2dcommon_itowaZ2ddigits_os.
Definition item__itowa_lower_digits : item :=
  (IData (a "_itowa_lower_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 97; 0; 0; 0; 98; 0; 0; 0; 99; 0; 0; 0; 100; 0; 0; 0; 101; 0; 0; 0; 102; 0; 0; 0; 103; 0; 0; 0; 104; 0; 0; 0]) (app [105; 0; 0; 0; 106; 0; 0; 0; 107; 0; 0; 0; 108; 0; 0; 0; 109; 0; 0; 0; 110; 0; 0; 0; 111; 0; 0; 0; 112; 0; 0; 0; 113; 0; 0; 0] [114; 0; 0; 0; 115; 0; 0; 0; 116; 0; 0; 0; 117; 0; 0; 0; 118; 0; 0; 0; 119; 0; 0; 0; 120; 0; 0; 0; 121; 0; 0; 0; 122; 0; 0; 0])))]).

Definition item__itowa_upper_digits : item :=
  (IData (a "_itowa_upper_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 65; 0; 0; 0; 66; 0; 0; 0; 67; 0; 0; 0; 68; 0; 0; 0; 69; 0; 0; 0; 70; 0; 0; 0; 71; 0; 0; 0; 72; 0; 0; 0]) (app [73; 0; 0; 0; 74; 0; 0; 0; 75; 0; 0; 0; 76; 0; 0; 0; 77; 0; 0; 0; 78; 0; 0; 0; 79; 0; 0; 0; 80; 0; 0; 0; 81; 0; 0; 0] [82; 0; 0; 0; 83; 0; 0; 0; 84; 0; 0; 0; 85; 0; 0; 0; 86; 0; 0; 0; 87; 0; 0; 0; 88; 0; 0; 0; 89; 0; 0; 0; 90; 0; 0; 0])))]).
End Unit_stdioZ2dcommon_itowaZ2ddigits_os.

(** This file defines checked IR from glibc’s `stdio-common/reg-printf.os` object. *)
Module Unit_stdioZ2dcommon_regZ2dprintf_os.
Definition item___printf_arginfo_table : item :=
  (IData (a "__printf_arginfo_table") LExport 8 [(Zero 8)]).

Definition item___printf_function_table : item :=
  (IData (a "__printf_function_table") LExport 8 [(Zero 8)]).
End Unit_stdioZ2dcommon_regZ2dprintf_os.

(** This file defines checked IR from glibc’s `stdio-common/reg-type.os` object. *)
Module Unit_stdioZ2dcommon_regZ2dtype_os.
Definition item___printf_va_arg_table : item :=
  (IData (a "__printf_va_arg_table") LExport 8 [(Zero 8)]).
End Unit_stdioZ2dcommon_regZ2dtype_os.

(** This file defines checked IR from glibc’s `stdlib/abs.os` object. *)
Module Unit_stdlib_abs_os.
Definition fn_abs : func :=
  ir_fn{ "export" "abs"(W %"v0") -> (RClass W) {
  @"start":
    %"v6" : W = (Cmp Slt W) %"v0", #0
    => br %"v6" ? "L2" : "L4";
  @"L2":
    %"v8" : W = Neg %"v0"
    => goto "L4";
  @"L4" [%"v10" : W = phi("L2" => %"v8", "start" => %"v0")]:
    => ret %"v10"
} }.
End Unit_stdlib_abs_os.

(** This file defines checked IR from glibc’s `stdlib/add_n.os` object. *)
Module Unit_stdlib_add_n_os.
Definition fn___mpn_add_n : func :=
  ir_fn{ "export" "__mpn_add_n"(P %"v0", P %"v2", P %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v13" : L = Neg %"v6";
    %"v16" : L = Shl %"v13", #3;
    (Flight (a "v17") Sub [(FAddress (t "v2")); (FValue (t "v16"))] (LowerOf (t "v2")));
    (Flight (a "v21") Sub [(FAddress (t "v4")); (FValue (t "v16"))] (LowerOf (t "v4")));
    (Flight (a "v25") Sub [(FAddress (t "v0")); (FValue (t "v16"))] (LowerOf (t "v0")))
    => goto "L26";
  @"L26" [%"pr.2" : L = phi("L26" => %"v61", "start" => %"v13"); %"pr.1" : L = phi("L26" => %"v54", "start" => #0)]:
    %"v31" : L = Shl %"pr.2", #3;
    %"v32" = %"v21" +p %"v31";
    %"chk0" : A = (Check 0 8 Read 1) %"v32";
    %"v33" : L = (RawLoad LdL 0) %"chk0";
    %"v37" = %"v17" +p %"v31";
    %"chk1" : A = (Check 0 8 Read 1) %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk1";
    %"v41" : L = Add %"v33", %"pr.1";
    %"v44" : W = (Cmp Ult L) %"v41", %"pr.1";
    %"v45" : L = (Ext Sw) %"v44";
    %"v48" : L = Add %"v38", %"v41";
    %"v51" : W = (Cmp Ult L) %"v48", %"v38";
    %"v53" : L = (Ext Sw) %"v51";
    %"v54" : L = Add %"v53", %"v45";
    %"v58" = %"v25" +p %"v31";
    %"chk2" : A = (Check 0 8 Write 1) %"v58";
    store Wl [%"chk2" + 0] <- %"v48";
    %"v61" : L = Add %"pr.2", #1;
    %"v62" : W = (Cmp Ne L) %"v61", #0
    => br %"v62" ? poll "L26" : "L28";
  @"L28":
    => ret %"v54"
} }.
End Unit_stdlib_add_n_os.

(** This file defines checked IR from glibc’s `stdlib/bsearch.os` object. *)
Module Unit_stdlib_bsearch_os.
Definition fn___GI_bsearch : func :=
  ir_fn{ "export" "__GI_bsearch"(P %"v0", P %"v2", L %"v4", L %"v6", P %"v8") -> (RClass P) {
  @"start":
    => goto "L12";
  @"L12" [%"pr.3" : L = phi("L36" => %"v45", "start" => %"v4"); %"pr.1" : P = phi("L36" => %"pr.2", "start" => %"v2")]:
    %"v16" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v16" ? "L13" : "L14";
  @"L13":
    %"v19" : L = Shr %"pr.3", #1;
    %"v21" : L = Mul %"v19", %"v6";
    %"v22" = %"pr.1" +p %"v21";
    %"chk0" : F = CheckFunction %"v8";
    rawcall %"v26" : W = %"chk0"(P %"v0", P %"v22");
    %"v31" : W = (Cmp Eq W) %"v26", #0
    => br %"v31" ? "L27" : "L29";
  @"L27":
    => ret %"v22";
  @"L29":
    %"v38" : W = (Cmp Sgt W) %"v26", #0
    => br %"v38" ? "L34" : "L36";
  @"L34":
    %"v41" = %"v22" +p %"v6";
    %"v43" : L = Sub %"pr.3", #1
    => goto "L36";
  @"L36" [%"pr.4" : L = phi("L34" => %"v43", "L29" => %"pr.3"); %"pr.2" : P = phi("L34" => %"v41", "L29" => %"pr.1")]:
    %"v45" : L = Shr %"pr.4", #1
    => goto poll "L12";
  @"L14":
    => ret #0
} }.
End Unit_stdlib_bsearch_os.

(** This file defines checked IR from glibc’s `stdlib/cmp.os` object. *)
Module Unit_stdlib_cmp_os.
Definition fn___mpn_cmp : func :=
  ir_fn{ "export" "__mpn_cmp"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v10" : L = Sub %"v4", #1
    => goto "L11";
  @"L11" [%"pr.1" : L = phi("L13" => %"v36", "start" => %"v10")]:
    %"v16" : W = (Cmp Sge L) %"pr.1", #0
    => br %"v16" ? "L12" : "L14";
  @"L12":
    %"v19" : L = Shl %"pr.1", #3;
    %"v20" = %"v0" +p %"v19";
    %"chk0" : A = (Check 0 8 Read 1) %"v20";
    %"v21" : L = (RawLoad LdL 0) %"chk0";
    %"v25" = %"v2" +p %"v19";
    %"chk1" : A = (Check 0 8 Read 1) %"v25";
    %"v26" : L = (RawLoad LdL 0) %"chk1";
    %"v32" : W = (Cmp Ne L) %"v21", %"v26"
    => br %"v32" ? "L33" : "L13";
  @"L13":
    %"v36" : L = Sub %"pr.1", #1
    => goto poll "L11";
  @"L14":
    => ret #0;
  @"L33":
    %"v42" : W = (Cmp Ugt L) %"v21", %"v26"
    => br %"v42" ? "L39" : "L38";
  @"L38":
    => goto "L39";
  @"L39" [%"v44" : W = phi("L38" => #4294967295, "L33" => #1)]:
    => ret %"v44"
} }.
End Unit_stdlib_cmp_os.

(** This file defines checked IR from glibc’s `stdlib/lshift.os` object. *)
Module Unit_stdlib_lshift_os.
Definition fn___mpn_lshift : func :=
  ir_fn{ "export" "__mpn_lshift"(P %"v0", P %"v2", L %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v16" = %"v0" +p #8;
    %"v18" : W = Sub #64, %"v6";
    %"v20" : L = Sub %"v4", #1;
    %"v23" : L = Shl %"v20", #3;
    %"v24" = %"v2" +p %"v23";
    %"chk0" : A = (Check 0 8 Read 1) %"v24";
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"v28" : L = Shr %"v25", %"v18"
    => goto "L30";
  @"L30" [%"pr.2" : L = phi("L31" => %"v34", "start" => %"v20"); %"pr.1" : L = phi("L31" => %"v40", "start" => %"v25")]:
    %"v34" : L = Sub %"pr.2", #1;
    %"v35" : W = (Cmp Sge L) %"v34", #0
    => br %"v35" ? "L31" : "L32";
  @"L31":
    %"v38" : L = Shl %"v34", #3;
    %"v39" = %"v2" +p %"v38";
    %"chk1" : A = (Check 0 8 Read 1) %"v39";
    %"v40" : L = (RawLoad LdL 0) %"chk1";
    %"v44" = %"v16" +p %"v38";
    %"v47" : L = Shl %"pr.1", %"v6";
    %"v50" : L = Shr %"v40", %"v18";
    %"v51" : L = Or %"v47", %"v50";
    %"chk2" : A = (Check 0 8 Write 1) %"v44";
    store Wl [%"chk2" + 0] <- %"v51"
    => goto poll "L30";
  @"L32":
    %"v55" : L = Shl %"v34", #3;
    %"v56" = %"v16" +p %"v55";
    %"v59" : L = Shl %"pr.1", %"v6";
    %"chk3" : A = (Check 0 8 Write 1) %"v56";
    store Wl [%"chk3" + 0] <- %"v59"
    => ret %"v28"
} }.
End Unit_stdlib_lshift_os.

(** This file defines checked IR from glibc’s `stdlib/secure-getenv.os` object. *)
Module Unit_stdlib_secureZ2dgetenv_os.
Definition fn___GI___libc_secure_getenv : func :=
  ir_fn{ "export" "__GI___libc_secure_getenv"(P %"v0") -> (RClass P) {
  @"start":
    %"v5" : P = Copy $"__libc_enable_secure";
    %"chk0" : A = (Check 0 4 Read 1) %"v5";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => br %"v6" ? "L4" : "L3";
  @"L3":
    call %"v8" : P = $"__GI_getenv"(P %"v0")
    => goto "L4";
  @"L4" [%"v9" : P = phi("L3" => %"v8", "start" => #0)]:
    => ret %"v9"
} }.

Definition item_secure_getenv : item :=
  (IAlias (a "secure_getenv") (a "weak") (a "__GI___libc_secure_getenv")).
End Unit_stdlib_secureZ2dgetenv_os.

(** This file defines checked IR from glibc’s `stdlib/strtol.os` object. *)
Module Unit_stdlib_strtol_os.
Definition fn___GI___isoc23_strtol : func :=
  ir_fn{ "export" "__GI___isoc23_strtol"(P %"v0", P %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v10" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v12" : L = $"__GI_____strtol_l_internal"(P %"v0", P %"v2", W %"v4", W #0, W #1, P %"v11")
    => ret %"v12"
} }.
End Unit_stdlib_strtol_os.

(** This file defines checked IR from glibc’s `stdlib/strtoul.os` object. *)
Module Unit_stdlib_strtoul_os.
Definition fn___GI___isoc23_strtoul : func :=
  ir_fn{ "export" "__GI___isoc23_strtoul"(P %"v0", P %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v10" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v12" : L = $"__GI_____strtoul_l_internal"(P %"v0", P %"v2", W %"v4", W #0, W #1, P %"v11")
    => ret %"v12"
} }.
End Unit_stdlib_strtoul_os.

(** This file defines checked IR from glibc’s `stdlib/sub_n.os` object. *)
Module Unit_stdlib_sub_n_os.
Definition fn___mpn_sub_n : func :=
  ir_fn{ "export" "__mpn_sub_n"(P %"v0", P %"v2", P %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v13" : L = Neg %"v6";
    %"v16" : L = Shl %"v13", #3;
    (Flight (a "v17") Sub [(FAddress (t "v2")); (FValue (t "v16"))] (LowerOf (t "v2")));
    (Flight (a "v21") Sub [(FAddress (t "v4")); (FValue (t "v16"))] (LowerOf (t "v4")));
    (Flight (a "v25") Sub [(FAddress (t "v0")); (FValue (t "v16"))] (LowerOf (t "v0")))
    => goto "L26";
  @"L26" [%"pr.2" : L = phi("L26" => %"v61", "start" => %"v13"); %"pr.1" : L = phi("L26" => %"v54", "start" => #0)]:
    %"v31" : L = Shl %"pr.2", #3;
    %"v32" = %"v21" +p %"v31";
    %"chk0" : A = (Check 0 8 Read 1) %"v32";
    %"v33" : L = (RawLoad LdL 0) %"chk0";
    %"v37" = %"v17" +p %"v31";
    %"chk1" : A = (Check 0 8 Read 1) %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk1";
    %"v41" : L = Add %"v33", %"pr.1";
    %"v44" : W = (Cmp Ult L) %"v41", %"pr.1";
    %"v45" : L = (Ext Sw) %"v44";
    %"v48" : L = Sub %"v38", %"v41";
    %"v51" : W = (Cmp Ugt L) %"v48", %"v38";
    %"v53" : L = (Ext Sw) %"v51";
    %"v54" : L = Add %"v53", %"v45";
    %"v58" = %"v25" +p %"v31";
    %"chk2" : A = (Check 0 8 Write 1) %"v58";
    store Wl [%"chk2" + 0] <- %"v48";
    %"v61" : L = Add %"pr.2", #1;
    %"v62" : W = (Cmp Ne L) %"v61", #0
    => br %"v62" ? poll "L26" : "L28";
  @"L28":
    => ret %"v54"
} }.
End Unit_stdlib_sub_n_os.

(** This file defines checked IR from glibc’s `string/argz-next.os` object. *)
Module Unit_string_argzZ2dnext_os.
Definition fn___GI___argz_next : func :=
  ir_fn{ "export" "__GI___argz_next"(P %"v0", L %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v10" : L = Ptoi %"v4";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L6" : "L7";
  @"L6":
    %"v18" = %"v0" +p %"v2";
    %"v20" : L = Ptoi %"v18";
    %"v21" : W = (Cmp Ult L) %"v10", %"v20"
    => br %"v21" ? "L12" : "L14";
  @"L12":
    call %"v23" : P = $"__GI_strchr"(P %"v4", W #0);
    %"v24" = %"v23" +p #1
    => goto "L14";
  @"L14" [%"pr.1" : P = phi("L12" => %"v24", "L6" => %"v4")]:
    %"v32" : L = Ptoi %"pr.1";
    %"v34" : W = (Cmp Uge L) %"v32", %"v20"
    => br %"v34" ? "L27" : "L26";
  @"L26":
    => goto "L27";
  @"L27" [%"v36" : P = phi("L26" => %"pr.1", "L14" => #0)]:
    => ret %"v36";
  @"L7":
    %"v42" : W = (Cmp Ugt L) %"v2", #0
    => br %"v42" ? "L38" : "L39";
  @"L38":
    => ret %"v0";
  @"L39":
    => ret #0
} }.
End Unit_string_argzZ2dnext_os.

(** This file defines checked IR from glibc’s `string/memmove.os` object. *)
Module Unit_string_memmove_os.
Definition fn___GI_memmove : func :=
  ir_fn{ "export" "__GI_memmove"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    call void $"zmemmove"(P %"v0", P %"v2", L %"v4")
    => ret %"v0"
} }.
End Unit_string_memmove_os.

(** This file defines checked IR from glibc’s `string/strcpy.os` object. *)
Module Unit_string_strcpy_os.
Definition fn___GI_strcpy : func :=
  ir_fn{ "export" "__GI_strcpy"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"__GI___stpcpy"(P %"v0", P %"v2")
    => ret %"v0"
} }.
End Unit_string_strcpy_os.

(** This file defines checked IR from glibc’s `string/strndup.os` object. *)
Module Unit_string_strndup_os.
Definition fn___GI___strndup : func :=
  ir_fn{ "export" "__GI___strndup"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    call %"v7" : L = $"__GI___strnlen"(P %"v0", L %"v2");
    %"v10" : L = Add %"v7", #1;
    call %"v11" : P = $"malloc"(L %"v10");
    %"v16" : L = Ptoi %"v11";
    %"v17" : L = Ptoi #0;
    %"v18" : W = (Cmp Eq L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L14";
  @"L12":
    => ret #0;
  @"L14":
    %"v22" = %"v11" +p %"v7";
    %"chk0" : A = (Check 0 1 Write 1) %"v22";
    store Wb [%"chk0" + 0] <- #0;
    call %"v26" : P = $"__GI_memcpy"(P %"v11", P %"v0", L %"v7")
    => ret %"v26"
} }.
End Unit_string_strndup_os.

(** This file defines checked IR from glibc’s `wcsmbs/mbrtoc32.os` object. *)
Module Unit_wcsmbs_mbrtoc32_os.
Definition item_glibc_mbrtoc32'23state : item :=
  (IData (a "glibc_mbrtoc32#state") LLocal 4 [(Zero 8)]).

Definition fn_mbrtoc32 : func :=
  ir_fn{ "export" "mbrtoc32"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v6";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    %"v15" : P = Copy $"glibc_mbrtoc32#state"
    => goto "L10";
  @"L10" [%"pr.1" : P = phi("L8" => %"v15", "start" => %"v6")]:
    call %"v20" : L = $"__GI_mbrtowc"(P %"v0", P %"v2", L %"v4", P %"pr.1")
    => ret %"v20"
} }.
End Unit_wcsmbs_mbrtoc32_os.

(** This file defines checked IR from glibc’s `wcsmbs/mbsrtowcs.os` object. *)
Module Unit_wcsmbs_mbsrtowcs_os.
Definition fn___mbsrtowcs : func :=
  ir_fn{ "export" "__mbsrtowcs"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v6";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L16" : "L15";
  @"L15":
    %"v17" : P = Copy $"glibc_mbsrtowcs#state"
    => goto "L16";
  @"L16" [%"v18" : P = phi("L15" => %"v17", "start" => %"v6")]:
    %"v19" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v21" : L = $"__mbsrtowcs_l"(P %"v0", P %"v2", L %"v4", P %"v18", P %"v20")
    => ret %"v21"
} }.

Definition item_glibc_mbsrtowcs'23state : item :=
  (IData (a "glibc_mbsrtowcs#state") LLocal 4 [(Zero 8)]).
End Unit_wcsmbs_mbsrtowcs_os.

(** This file defines checked IR from glibc’s `wcsmbs/wcsnlen.os` object. *)
Module Unit_wcsmbs_wcsnlen_os.
Definition fn___wcsnlen : func :=
  ir_fn{ "export" "__wcsnlen"(P %"v0", L %"v2") -> (RClass L) {
  @"start":
    call %"v7" : P = $"__GI___wmemchr"(P %"v0", W #0, L %"v2");
    %"v12" : L = Ptoi %"v7";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L8" : "L10";
  @"L8":
    %"v17" : L = Ptoi %"v0";
    %"v18" : L = Sub %"v12", %"v17";
    %"v19" : L = Div %"v18", #4
    => goto "L10";
  @"L10" [%"pr.1" : L = phi("L8" => %"v19", "start" => %"v2")]:
    => ret %"pr.1"
} }.
End Unit_wcsmbs_wcsnlen_os.

(** This file defines checked IR from glibc’s `wcsmbs/wmemmove.os` object. *)
Module Unit_wcsmbs_wmemmove_os.
Definition fn___wmemmove : func :=
  ir_fn{ "export" "__wmemmove"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v9" : L = Shl %"v4", #2;
    call %"v10" : P = $"__GI_memmove"(P %"v0", P %"v2", L %"v9")
    => ret %"v10"
} }.
End Unit_wcsmbs_wmemmove_os.

(** This file defines checked IR from glibc’s `elf/dl-support.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___libc_stack_end : item :=
  (IData (a "__libc_stack_end") LExport 8 [(Zero 8)]).

Definition item__dl_auxv : item :=
  (IData (a "_dl_auxv") LExport 8 [(Zero 8)]).

Definition item__dl_clktck : item :=
  (IData (a "_dl_clktck") LExport 4 [(Zero 4)]).

Definition item__dl_debug_mask : item :=
  (IData (a "_dl_debug_mask") LExport 4 [(Zero 4)]).

Definition item__dl_hwcap : item :=
  (IData (a "_dl_hwcap") LExport 8 [(Zero 8)]).

Definition item__dl_hwcap2 : item :=
  (IData (a "_dl_hwcap2") LExport 8 [(Zero 8)]).

Definition item__dl_minsigstacksize : item :=
  (IData (a "_dl_minsigstacksize") LExport 8 [(Item Wl 0)]).

Definition item__dl_pagesize : item :=
  (IData (a "_dl_pagesize") LExport 8 [(Item Wl 4096)]).

Definition item__dl_platform : item :=
  (IData (a "_dl_platform") LExport 8 [(Zero 8)]).

Definition item__dl_thp_mode : item :=
  (IData (a "_dl_thp_mode") LExport 4 [(Zero 4)]).

Definition item__dl_x86_cpu_features : item :=
  (IData (a "_dl_x86_cpu_features") LExport 8 [(Zero 528)]).

Definition item__dl_x86_feature_control : item :=
  (IData (a "_dl_x86_feature_control") LExport 4 [(Item Wb 0); (Zero 3)]).

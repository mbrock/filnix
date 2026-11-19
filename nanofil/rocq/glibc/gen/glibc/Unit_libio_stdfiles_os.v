(** This file defines checked IR from glibc’s `libio/stdfiles.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__IO_2_1_stderr_ : item :=
  (IData (a "_IO_2_1_stderr_") LExport 8 [(Item Ww (-72540026)); (Zero 4); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_2_1_stdout_") 0); (Item Ww 2); (Item Wb 0); (Item Wb 0); (Item Wb 0); (Str [0]); (Item Wl (-1)); (Item Wh 0); (Item Wb 0); (Str [0]); (Zero 4); (Sym (a "glibc_stdfiles#_IO_stdfile_2_lock") 0); (Item Wl (-1)); (Item Wl 0); (Sym (a "glibc_stdfiles#_IO_wide_data_2") 0); (Item Wl 0); (Zero 40); (Sym (a "__io_vtables") 336)]).

Definition item__IO_2_1_stdin_ : item :=
  (IData (a "_IO_2_1_stdin_") LExport 8 [(Item Ww (-72540024)); (Zero 4); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Item Wb 0); (Item Wb 0); (Item Wb 0); (Str [0]); (Item Wl (-1)); (Item Wh 0); (Item Wb 0); (Str [0]); (Zero 4); (Sym (a "glibc_stdfiles#_IO_stdfile_0_lock") 0); (Item Wl (-1)); (Item Wl 0); (Sym (a "glibc_stdfiles#_IO_wide_data_0") 0); (Item Wl 0); (Zero 40); (Sym (a "__io_vtables") 336)]).

Definition item__IO_2_1_stdout_ : item :=
  (IData (a "_IO_2_1_stdout_") LExport 8 [(Item Ww (-72540028)); (Zero 4); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_2_1_stdin_") 0); (Item Ww 1); (Item Wb 0); (Item Wb 0); (Item Wb 0); (Str [0]); (Item Wl (-1)); (Item Wh 0); (Item Wb 0); (Str [0]); (Zero 4); (Sym (a "glibc_stdfiles#_IO_stdfile_1_lock") 0); (Item Wl (-1)); (Item Wl 0); (Sym (a "glibc_stdfiles#_IO_wide_data_1") 0); (Item Wl 0); (Zero 40); (Sym (a "__io_vtables") 336)]).

Definition item___GI__IO_list_all : item :=
  (IData (a "__GI__IO_list_all") LExport 8 [(Sym (a "_IO_2_1_stderr_") 0)]).

Definition item___nanofil_ctor__IO_stdfiles_init : item :=
  (IData (a "__nanofil_ctor__IO_stdfiles_init") (LInit (a "ctor") (a "none")) 8 [(Sym (a "glibc_stdfiles#_IO_stdfiles_init") 0)]).

Definition item_glibc_stdfiles'23_IO_stdfile_0_lock : item :=
  (IData (a "glibc_stdfiles#_IO_stdfile_0_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition item_glibc_stdfiles'23_IO_stdfile_1_lock : item :=
  (IData (a "glibc_stdfiles#_IO_stdfile_1_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition item_glibc_stdfiles'23_IO_stdfile_2_lock : item :=
  (IData (a "glibc_stdfiles#_IO_stdfile_2_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition fn_glibc_stdfiles'23_IO_stdfiles_init : func :=
  ir_fn{ "local" "glibc_stdfiles#_IO_stdfiles_init"() -> RVoid {
  @"start":
    %"v1" : P = Copy $"__GI__IO_list_all"
    => goto "L2";
  @"L2" [%"pr.1" : P = phi("L3" => %"v17", "start" => %"v1")]:
    %"chk0" : A = (Check 0 8 Read 8) %"pr.1";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" : L = Ptoi %"v7";
    %"v9" : L = Ptoi #0;
    %"v10" : W = (Cmp Ne L) %"v8", %"v9"
    => br %"v10" ? "L3" : "L5";
  @"L3":
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #184;
    %"chk2" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk2" + 0] <- %"pr.1";
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"pr.1";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v17" = %"v16" +p #104
    => goto poll "L2";
  @"L5":
    => ret void
} }.

Definition item_glibc_stdfiles'23_IO_wide_data_0 : item :=
  (IData (a "glibc_stdfiles#_IO_wide_data_0") LLocal 8 [(Zero 224); (Sym (a "__io_vtables") 840)]).

Definition item_glibc_stdfiles'23_IO_wide_data_1 : item :=
  (IData (a "glibc_stdfiles#_IO_wide_data_1") LLocal 8 [(Zero 224); (Sym (a "__io_vtables") 840)]).

Definition item_glibc_stdfiles'23_IO_wide_data_2 : item :=
  (IData (a "glibc_stdfiles#_IO_wide_data_2") LLocal 8 [(Zero 224); (Sym (a "__io_vtables") 840)]).

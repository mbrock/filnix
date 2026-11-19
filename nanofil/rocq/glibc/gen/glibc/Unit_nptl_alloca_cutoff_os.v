(** This file defines checked IR from glibc’s `nptl/alloca_cutoff.os` object.
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

Definition fn___GI___libc_alloca_cutoff : func :=
  ir_fn{ "export" "__GI___libc_alloca_cutoff"(L %"v0") -> (RClass W) {
  @"start":
    call %"v6" : P = $"zthread_self_cookie"();
    %"v7" = %"v6" +p #1720;
    %"chk0" : A = (Check 0 8 Read 1) %"v7";
    %"v8" : L = (RawLoad LdL 0) %"chk0";
    %"v9" : L = Shr %"v8", #2;
    %"v10" : W = (Cmp Ne L) %"v9", #0
    => br %"v10" ? "L13" : "L12";
  @"L12":
    => goto "L13";
  @"L13" [%"v16" : L = phi("L12" => #262144, "start" => %"v9")]:
    %"v17" : W = (Cmp Ugt L) %"v16", #65536
    => br %"v17" ? "L5" : "L4";
  @"L4":
    call %"v18" : P = $"zthread_self_cookie"();
    %"v19" = %"v18" +p #1720;
    %"chk1" : A = (Check 0 8 Read 1) %"v19";
    %"v20" : L = (RawLoad LdL 0) %"chk1";
    %"v21" : L = Shr %"v20", #2;
    %"v22" : W = (Cmp Ne L) %"v21", #0
    => br %"v22" ? "L5" : "L24";
  @"L24":
    => goto "L5";
  @"L5" [%"v29" : L = phi("L13" => #65536, "L24" => #262144, "L4" => %"v21")]:
    %"v30" : W = (Cmp Ule L) %"v0", %"v29"
    => ret %"v30"
} }.

Definition item___libc_alloca_cutoff : item :=
  (IAlias (a "__libc_alloca_cutoff") (a "export") (a "__GI___libc_alloca_cutoff")).

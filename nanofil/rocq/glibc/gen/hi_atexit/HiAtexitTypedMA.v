(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_fn_main : func :=
  mkFunc (a "main") (a "export") (RClass W) [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "hi_atexit#close_stdout_hi"))]);
      (Call (CResult (a "v1") W) (Global (a "atexit")) [(Arg P (t "v0"))]);
      (Let (a "v2") P Copy [(Global (a "hi_atexit#str.0"))]);
      (Call (CResult (a "v3") W) (Global (a "puts")) [(Arg P (t "v2"))]);
      (Call CVoid (Global (a "exit")) [(Arg W (Const 0))])] (JRet (Const 0)))].

Definition hi_fn_glibc_malloc'23malloc_printerr : func :=
  mkFunc (a "glibc_malloc#malloc_printerr") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P Copy [(Global (a "glibc_malloc#str.407"))]);
      (Let (a "v3") P Copy [(Global (a "glibc_malloc#str.408"))]);
      (Call CVoid (Global (a "__libc_message_impl")) [(Arg P (t "v2")); (Arg P (t "v3")); (Arg P (t "v0"))])] JUnreachable)].

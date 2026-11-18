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

Definition hello_image_fn___GI___fcntl64_nocancel : func :=
  mkFunc (a "__GI___fcntl64_nocancel") (a "export") (RClass W) [(W, (a "v0")); (W, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "va_args") P VaArgs [(Const 16)]);
      (Let (a "v4") P Copy [(Global (a "zsys_fcntl"))]);
      (Let (a "v5") P VaArgs [(Const 0)]);
      (Call (CResult (a "v6") P) (Global (a "zcall")) [(Arg P (t "v4")); (Arg P (t "v5"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v6")]);
      (Let (a "v7") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")])] (JRet (t "v7")))].

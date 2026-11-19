(** This file defines checked IR from glibc’s `misc/sysinfo.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___sysinfo : item :=
  (IOutside (a "__sysinfo") (TApp "func" [(a "__sysinfo"); (a "export"); (a "data"); (TList []); (TList [(TApp "block" [(a "start"); (TList []); (TList [(TApp "let" [(TApp "tmp" [(a "v0")]); (a "p"); (a "copy"); (TList [(TApp "global" [(a "zsys_sysinfo")])])]); (TApp "let" [(TApp "tmp" [(a "v1")]); (a "p"); (a "va_args"); (TList [(TApp "const" [(TInt 0)])])]); (TApp "call" [(TApp "result" [(TApp "tmp" [(a "v2")]); (a "p")]); (TApp "global" [(a "zcall")]); (TList [(TApp "arg" [(a "p"); (TApp "tmp" [(a "v0")])]); (TApp "arg" [(a "p"); (TApp "tmp" [(a "v1")])])])])]); (TApp "ret" [(TApp "tmp" [(a "v2")])])])])])).

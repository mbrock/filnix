(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


Module FormatterSrcFiles.

Definition file_0 : string := "../include/printf_buffer.h".

Definition file_1 : string := "./vfprintf-process-arg.c".

Definition file_2 : string := "vfprintf-internal.c".

End FormatterSrcFiles.

(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20_IO_FILE_plus : record_layout :=
  (mkRecordLayout "struct _IO_FILE_plus" 224 8 [("file", 0, 216, 8); ("vtable", 216, 8, 8)]).

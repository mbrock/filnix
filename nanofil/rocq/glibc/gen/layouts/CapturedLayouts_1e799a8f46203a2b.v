(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20timespec : record_layout :=
  (mkRecordLayout "struct timespec" 16 8 [("tv_sec", 0, 8, 8); ("tv_nsec", 8, 8, 8)]).

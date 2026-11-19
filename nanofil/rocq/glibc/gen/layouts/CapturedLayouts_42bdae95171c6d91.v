(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_glibc_fileopsZ3aanonymousZ20unionZ23230 : record_layout :=
  (mkRecordLayout "glibc_fileops:anonymous union#230" 4 4 [("__wch", 0, 4, 4); ("__wchb", 0, 4, 1)]).

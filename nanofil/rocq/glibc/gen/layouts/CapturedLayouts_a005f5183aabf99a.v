(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_typedefZ20mbstate_t : record_layout :=
  (mkRecordLayout "typedef mbstate_t" 8 4 [("__count", 0, 4, 4); ("__value", 4, 4, 4)]).

(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20__gconv_loaded_object : record_layout :=
  (mkRecordLayout "struct __gconv_loaded_object" 48 8 [("name", 0, 8, 8); ("counter", 8, 4, 4); ("handle", 16, 8, 8); ("fct", 24, 8, 8); ("init_fct", 32, 8, 8); ("end_fct", 40, 8, 8)]).

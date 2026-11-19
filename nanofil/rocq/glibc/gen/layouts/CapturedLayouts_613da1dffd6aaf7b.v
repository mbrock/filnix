(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20__printf_buffer : record_layout :=
  (mkRecordLayout "struct __printf_buffer" 40 8 [("write_base", 0, 8, 8); ("write_ptr", 8, 8, 8); ("write_end", 16, 8, 8); ("written", 24, 8, 8); ("mode", 32, 4, 4)]).

(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20__locale_data : record_layout :=
  (mkRecordLayout "struct __locale_data" 56 8 [("name", 0, 8, 8); ("filedata", 8, 8, 8); ("filesize", 16, 8, 8); ("alloc", 24, 4, 4); ("private", 32, 8, 8); ("usage_count", 40, 4, 4); ("use_translit", 44, 4, 4); ("nstrings", 48, 4, 4); ("values", 56, 0, 8)]).

Definition layout_structZ20__locale_struct : record_layout :=
  (mkRecordLayout "struct __locale_struct" 232 8 [("__locales", 0, 104, 8); ("__ctype_b", 104, 8, 8); ("__ctype_tolower", 112, 8, 8); ("__ctype_toupper", 120, 8, 8); ("__names", 128, 104, 8)]).

Definition layout_unionZ20locale_data_value : record_layout :=
  (mkRecordLayout "union locale_data_value" 8 8 [("wstr", 0, 8, 8); ("string", 0, 8, 8); ("word", 0, 4, 4)]).

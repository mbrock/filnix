(** The extracted loader places these symbols in the linked image. Each row gives
    the symbol, its address and its region end. Functions occupy no data region.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition placement : list (string * Z * Z) :=
  [("__gconv_transform_internal_ascii", 82992, 82992);
   ("__libc_tsd_LOCALE", 165600, 165608);
   ("_nl_global_locale", 165632, 165864);
   ("_nl_C_LC_CTYPE", 99072, 99816);
   ("glibc_wcsmbsload#to_mb", 214096, 214200);
   ("glibc_C_ctype#str.280", 157424, 157432);
   ("glibc_C_ctype#translit_from_idx", 106464, 113104);
   ("glibc_C_ctype#translit_from_tbl", 113120, 126392);
   ("glibc_C_ctype#translit_to_idx", 126416, 133056);
   ("glibc_C_ctype#translit_to_tbl", 133072, 156624)].

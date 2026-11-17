(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    Offset checks compare hand-written constants against these tables without changing existing proofs.
    Layouts remain advisory data, not premises of soundness theorems.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module PostloadCtypeLayout.

(** Each named record has its complete size and record alignment in bytes. *)
Definition records : list (string * (Z * Z)) :=
  [("struct __locale_data", (56, 8)); ("struct __locale_struct", (232, 8)); ("union locale_data_value", (8, 8))].

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := [].

(** Each field has a tag, name, byte offset, type size and type alignment.
    Flexible arrays have zero size; bit-fields retain their declared type's size and alignment. *)
Definition fields : list (string * string * Z * Z * Z) :=
  [("struct __locale_data", "name", 0, 8, 8); ("struct __locale_data", "filedata", 8, 8, 8); ("struct __locale_data", "filesize", 16, 8, 8); ("struct __locale_data", "alloc", 24, 4, 4); ("struct __locale_data", "private", 32, 8, 8); ("struct __locale_data", "usage_count", 40, 4, 4); ("struct __locale_data", "use_translit", 44, 4, 4); ("struct __locale_data", "nstrings", 48, 4, 4); ("struct __locale_data", "values", 56, 0, 8); ("struct __locale_struct", "__locales", 0, 104, 8); ("struct __locale_struct", "__ctype_b", 104, 8, 8); ("struct __locale_struct", "__ctype_tolower", 112, 8, 8); ("struct __locale_struct", "__ctype_toupper", 120, 8, 8); ("struct __locale_struct", "__names", 128, 104, 8); ("union locale_data_value", "wstr", 0, 8, 8); ("union locale_data_value", "string", 0, 8, 8); ("union locale_data_value", "word", 0, 4, 4)].

(** Missing fields return [None], so an offset check cannot accept an invented entry. *)
Definition field_offset (tag field : string) : option Z :=
  option_map (fun entry => let '(_, _, offset, _, _) := entry in offset)
    (find (fun entry => let '(t, f, _, _, _) := entry in
      andb (String.eqb t tag) (String.eqb f field)) fields).

End PostloadCtypeLayout.

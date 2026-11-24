(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module GetoptLayout.

Local Definition layouts : list record_layout :=
  [(mkRecordLayout "struct _getopt_data" 56 8 [("optind", 0, 4, 4); ("opterr", 4, 4, 4); ("optopt", 8, 4, 4); ("optarg", 16, 8, 8); ("__initialized", 24, 4, 4); ("__nextchar", 32, 8, 8); ("__ordering", 40, 4, 4); ("__first_nonopt", 44, 4, 4); ("__last_nonopt", 48, 4, 4)])].

(** Each named record has its complete size and record alignment in bytes. *)
Definition records := layout_records layouts.

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := [].

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End GetoptLayout.

(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
From Glibc Require CapturedLayouts_59b4016e4aa9f3ae.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module PostloadCtypeLayout.

Local Definition layouts : list record_layout :=
  [CapturedLayouts_59b4016e4aa9f3ae.layout_structZ20__locale_data;
   CapturedLayouts_59b4016e4aa9f3ae.layout_structZ20__locale_struct;
   CapturedLayouts_59b4016e4aa9f3ae.layout_unionZ20locale_data_value].

(** Each named record has its complete size and record alignment in bytes. *)
Definition records := layout_records layouts.

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := [].

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End PostloadCtypeLayout.

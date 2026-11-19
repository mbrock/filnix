(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
From Glibc Require CapturedLayouts_42bdae95171c6d91 CapturedLayouts_5eff1a7224b7055c CapturedLayouts_9e4d2f33f82e0bd9 CapturedLayouts_a005f5183aabf99a CapturedLayouts_a38737c4e5c2f0a3.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module LibioCloseItLayout.

Local Definition layouts : list record_layout :=
  [CapturedLayouts_42bdae95171c6d91.layout_glibc_fileopsZ3aanonymousZ20unionZ23230;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_FILE;
   CapturedLayouts_5eff1a7224b7055c.layout_structZ20_IO_FILE_plus;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_codecvt;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_jump_t;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_marker;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_wide_data;
   CapturedLayouts_9e4d2f33f82e0bd9.layout_structZ20__gconv_loaded_object;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20__gconv_step;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20__gconv_step_data;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20FILE;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20_IO_iconv_t;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20_IO_lock_t;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20__FILE;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20__mbstate_t;
   CapturedLayouts_a005f5183aabf99a.layout_typedefZ20mbstate_t].

(** Each named record has its complete size and record alignment in bytes. *)
Definition records := layout_records layouts.

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := [].

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End LibioCloseItLayout.

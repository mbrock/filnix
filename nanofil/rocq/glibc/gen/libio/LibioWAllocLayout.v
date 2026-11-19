(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
From Glibc Require CapturedLayouts_a005f5183aabf99a CapturedLayouts_a38737c4e5c2f0a3.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module LibioWAllocLayout.

Local Definition layouts : list record_layout :=
  [(mkRecordLayout "glibc_wfiledoalloc:anonymous union#230" 4 4 [("__wch", 0, 4, 4); ("__wchb", 0, 4, 1)]);
   (mkRecordLayout "glibc_wgenops:anonymous union#230" 4 4 [("__wch", 0, 4, 4); ("__wchb", 0, 4, 1)]);
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_FILE;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_codecvt;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_jump_t;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_marker;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_wide_data;
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
Definition unavailable : list string := ["struct __gconv_loaded_object"].

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End LibioWAllocLayout.

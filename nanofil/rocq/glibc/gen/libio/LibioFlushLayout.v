(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
From Glibc Require CapturedLayouts_5eff1a7224b7055c CapturedLayouts_a38737c4e5c2f0a3 CapturedLayouts_a77a748a56cc58ee CapturedLayouts_d1ea51a67ff602b1 CapturedLayouts_fc43b3f492b2969a.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module LibioFlushLayout.

Local Definition layouts : list record_layout :=
  [CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20structZ23170;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20structZ23212;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20structZ23214;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20structZ23217;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20structZ23219;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20unionZ23169;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20unionZ23200;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20unionZ23213;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20unionZ23218;
   CapturedLayouts_a77a748a56cc58ee.layout_glibc_genopsZ3aanonymousZ20unionZ23224;
   CapturedLayouts_d1ea51a67ff602b1.layout_glibc_genopsZ3aanonymousZ20unionZ23230;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_FILE;
   CapturedLayouts_5eff1a7224b7055c.layout_structZ20_IO_FILE_plus;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_codecvt;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_jump_t;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_marker;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20_IO_wide_data;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20_Unwind_Exception;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20__gconv_step;
   CapturedLayouts_a38737c4e5c2f0a3.layout_structZ20__gconv_step_data;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20__res_state;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20_internal_sigset_t;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20_pthread_cleanup_buffer;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20dtv_pointer;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20in6_addr;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20in_addr;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20list_head;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20priority_protection_data;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20pthread;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20pthread_key_data;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20pthread_unwind_buf;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20robust_list_head;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20sched_param;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20sockaddr_in;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20sockaddr_in6;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20td_thr_events;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20tls_internal_t;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20FILE;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20_IO_iconv_t;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20_IO_lock_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20__128bits;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20__FILE;
   CapturedLayouts_a38737c4e5c2f0a3.layout_typedefZ20__mbstate_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20dtv_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20internal_sigset_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20list_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20tcbhead_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20td_eventbuf_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20td_thr_events_t;
   CapturedLayouts_fc43b3f492b2969a.layout_unionZ20dtv].

(** Each named record has its complete size and record alignment in bytes. *)
Definition records := layout_records layouts.

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := ["struct __gconv_loaded_object"; "struct rtld_catch"].

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End LibioFlushLayout.

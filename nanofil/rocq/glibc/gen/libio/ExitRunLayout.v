(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
From Glibc Require CapturedLayouts_fc43b3f492b2969a.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module ExitRunLayout.

Local Definition layouts : list record_layout :=
  [(mkRecordLayout "glibc_exit:anonymous struct#188" 32 8 [("exception_class", 0, 8, 8); ("exception_cleanup", 8, 8, 8); ("private_1", 16, 8, 8); ("private_2", 24, 8, 8)]);
   (mkRecordLayout "glibc_exit:anonymous struct#230" 8 4 [("addr", 0, 4, 4); ("mask", 4, 4, 4)]);
   (mkRecordLayout "glibc_exit:anonymous struct#232" 56 8 [("nscount", 0, 2, 2); ("nsmap", 2, 6, 2); ("nssocks", 8, 12, 4); ("nscount6", 20, 2, 2); ("nsinit", 22, 2, 2); ("nsaddrs", 24, 24, 8); ("__glibc_extension_index", 48, 8, 8)]);
   (mkRecordLayout "glibc_exit:anonymous struct#235" 72 8 [("jmp_buf", 0, 64, 8); ("mask_was_saved", 64, 4, 4)]);
   (mkRecordLayout "glibc_exit:anonymous struct#237" 24 8 [("prev", 0, 8, 8); ("cleanup", 8, 8, 8); ("canceltype", 16, 4, 4)]);
   (mkRecordLayout "glibc_exit:anonymous struct#268" 16 8 [("fn", 0, 8, 8); ("arg", 8, 8, 8)]);
   (mkRecordLayout "glibc_exit:anonymous struct#269" 24 8 [("fn", 0, 8, 8); ("arg", 8, 8, 8); ("dso_handle", 16, 8, 8)]);
   (mkRecordLayout "glibc_exit:anonymous union#187" 32 16 [("unwind_exception_align", 0, 16, 8); ("exception_class", 0, 8, 8); ("exception_cleanup", 8, 8, 8); ("private_1", 16, 8, 8); ("private_2", 24, 8, 8)]);
   (mkRecordLayout "glibc_exit:anonymous union#218" 16 4 [("__u6_addr8", 0, 16, 1); ("__u6_addr16", 0, 16, 2); ("__u6_addr32", 0, 16, 4)]);
   (mkRecordLayout "glibc_exit:anonymous union#231" 56 8 [("pad", 0, 52, 1); ("_ext", 0, 56, 8)]);
   (mkRecordLayout "glibc_exit:anonymous union#236" 32 8 [("pad", 0, 32, 8); ("data", 0, 24, 8)]);
   (mkRecordLayout "glibc_exit:anonymous union#242" 704 32 [("header", 0, 704, 32); ("__padding", 0, 192, 8)]);
   (mkRecordLayout "glibc_exit:anonymous union#267" 24 8 [("at", 0, 8, 8); ("on", 0, 16, 8); ("cxa", 0, 24, 8)]);
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20_Unwind_Exception;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20__res_state;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20_internal_sigset_t;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20_pthread_cleanup_buffer;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20dtv_pointer;
   (mkRecordLayout "struct exit_function" 32 8 [("flavor", 0, 8, 8); ("func", 8, 24, 8)]);
   (mkRecordLayout "struct exit_function_list" 1040 8 [("next", 0, 8, 8); ("idx", 8, 8, 8); ("fns", 16, 1024, 8)]);
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
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20__128bits;
   (mkRecordLayout "typedef __libc_lock_recursive_t" 16 8 [("lock", 0, 4, 4); ("cnt", 4, 4, 4); ("owner", 8, 8, 8)]);
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
Definition unavailable : list string := ["struct rtld_catch"].

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End ExitRunLayout.

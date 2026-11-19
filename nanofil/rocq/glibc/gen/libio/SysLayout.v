(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
From Glibc Require CapturedLayouts_1e799a8f46203a2b CapturedLayouts_7e40ea486e4fb1fa CapturedLayouts_fc43b3f492b2969a.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module SysLayout.

Local Definition layouts : list record_layout :=
  [(mkRecordLayout "glibc_libc_cleanup:anonymous struct#169" 32 8 [("exception_class", 0, 8, 8); ("exception_cleanup", 8, 8, 8); ("private_1", 16, 8, 8); ("private_2", 24, 8, 8)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous struct#211" 8 4 [("addr", 0, 4, 4); ("mask", 4, 4, 4)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous struct#213" 56 8 [("nscount", 0, 2, 2); ("nsmap", 2, 6, 2); ("nssocks", 8, 12, 4); ("nscount6", 20, 2, 2); ("nsinit", 22, 2, 2); ("nsaddrs", 24, 24, 8); ("__glibc_extension_index", 48, 8, 8)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous struct#216" 72 8 [("jmp_buf", 0, 64, 8); ("mask_was_saved", 64, 4, 4)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous struct#218" 24 8 [("prev", 0, 8, 8); ("cleanup", 8, 8, 8); ("canceltype", 16, 4, 4)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous union#168" 32 16 [("unwind_exception_align", 0, 16, 8); ("exception_class", 0, 8, 8); ("exception_cleanup", 8, 8, 8); ("private_1", 16, 8, 8); ("private_2", 24, 8, 8)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous union#199" 16 4 [("__u6_addr8", 0, 16, 1); ("__u6_addr16", 0, 16, 2); ("__u6_addr32", 0, 16, 4)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous union#212" 56 8 [("pad", 0, 52, 1); ("_ext", 0, 56, 8)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous union#217" 32 8 [("pad", 0, 32, 8); ("data", 0, 24, 8)]);
   (mkRecordLayout "glibc_libc_cleanup:anonymous union#223" 704 32 [("header", 0, 704, 32); ("__padding", 0, 192, 8)]);
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20_Unwind_Exception;
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
   CapturedLayouts_7e40ea486e4fb1fa.layout_structZ20stat64;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20td_thr_events;
   (mkRecordLayout "struct termios2" 44 4 [("c_iflag", 0, 4, 4); ("c_oflag", 4, 4, 4); ("c_cflag", 8, 4, 4); ("c_lflag", 12, 4, 4); ("c_line", 16, 1, 1); ("c_cc", 17, 19, 1); ("c_ispeed", 36, 4, 4); ("c_ospeed", 40, 4, 4)]);
   CapturedLayouts_1e799a8f46203a2b.layout_structZ20timespec;
   CapturedLayouts_fc43b3f492b2969a.layout_structZ20tls_internal_t;
   CapturedLayouts_fc43b3f492b2969a.layout_typedefZ20__128bits;
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

End SysLayout.

(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20_Unwind_Exception : record_layout :=
  (mkRecordLayout "struct _Unwind_Exception" 32 16 [("unwind_exception_align", 0, 16, 8); ("exception_class", 0, 8, 8); ("exception_cleanup", 8, 8, 8); ("private_1", 16, 8, 8); ("private_2", 24, 8, 8)]).

Definition layout_structZ20__res_state : record_layout :=
  (mkRecordLayout "struct __res_state" 568 8 [("retrans", 0, 4, 4); ("retry", 4, 4, 4); ("options", 8, 8, 8); ("nscount", 16, 4, 4); ("nsaddr_list", 20, 48, 4); ("id", 68, 2, 2); ("dnsrch", 72, 56, 8); ("defdname", 128, 256, 1); ("pfcode", 384, 8, 8); ("ndots", 392, 4, 4); ("nsort", 392, 4, 4); ("ipv6_unavail", 392, 4, 4); ("unused", 392, 4, 4); ("sort_list", 396, 80, 4); ("__glibc_unused_qhook", 480, 8, 8); ("__glibc_unused_rhook", 488, 8, 8); ("res_h_errno", 496, 4, 4); ("_vcsock", 500, 4, 4); ("_flags", 504, 4, 4); ("_u", 512, 56, 8)]).

Definition layout_structZ20_internal_sigset_t : record_layout :=
  (mkRecordLayout "struct _internal_sigset_t" 128 8 [("__val", 0, 128, 8)]).

Definition layout_structZ20_pthread_cleanup_buffer : record_layout :=
  (mkRecordLayout "struct _pthread_cleanup_buffer" 32 8 [("__routine", 0, 8, 8); ("__arg", 8, 8, 8); ("__canceltype", 16, 4, 4); ("__prev", 24, 8, 8)]).

Definition layout_structZ20dtv_pointer : record_layout :=
  (mkRecordLayout "struct dtv_pointer" 16 8 [("val", 0, 8, 8); ("to_free", 8, 8, 8)]).

Definition layout_structZ20in6_addr : record_layout :=
  (mkRecordLayout "struct in6_addr" 16 4 [("__in6_u", 0, 16, 4)]).

Definition layout_structZ20in_addr : record_layout :=
  (mkRecordLayout "struct in_addr" 4 4 [("s_addr", 0, 4, 4)]).

Definition layout_structZ20list_head : record_layout :=
  (mkRecordLayout "struct list_head" 16 8 [("next", 0, 8, 8); ("prev", 8, 8, 8)]).

Definition layout_structZ20priority_protection_data : record_layout :=
  (mkRecordLayout "struct priority_protection_data" 4 4 [("priomax", 0, 4, 4); ("priomap", 4, 0, 4)]).

Definition layout_structZ20pthread : record_layout :=
  (mkRecordLayout "struct pthread" 2496 64 [("list", 704, 16, 8); ("tid", 720, 4, 4); ("zthread", 728, 8, 8); ("dead", 736, 4, 4); ("robust_prev", 744, 8, 8); ("robust_head", 752, 24, 8); ("cleanup", 776, 8, 8); ("cleanup_jmp_buf", 784, 8, 8); ("cancelhandling", 792, 4, 4); ("flags", 796, 4, 4); ("specific_1stblock", 800, 512, 8); ("specific", 1312, 256, 8); ("specific_used", 1568, 1, 1); ("report_events", 1569, 1, 1); ("stack_mode", 1572, 4, 4); ("stopped_start", 1576, 1, 1); ("setup_failed", 1580, 4, 4); ("lock", 1584, 4, 4); ("setxid_futex", 1588, 4, 4); ("joinstate", 1592, 4, 4); ("joinid", 1600, 8, 8); ("result", 1608, 8, 8); ("schedparam", 1616, 4, 4); ("schedpolicy", 1620, 4, 4); ("start_routine", 1624, 8, 8); ("arg", 1632, 8, 8); ("eventbuf", 1640, 24, 8); ("nextevent", 1664, 8, 8); ("exc", 1680, 32, 16); ("stackblock", 1712, 8, 8); ("stackblock_size", 1720, 8, 8); ("guardsize", 1728, 8, 8); ("reported_guardsize", 1736, 8, 8); ("tpp", 1744, 8, 8); ("res", 1752, 568, 8); ("sigmask", 2320, 128, 8); ("rtld_catch", 2448, 8, 8); ("c11", 2456, 1, 1); ("exiting", 2457, 1, 1); ("exit_lock", 2460, 4, 4); ("tls_state", 2464, 16, 8); ("getrandom_buf", 2480, 8, 8); ("header", 0, 704, 32); ("__padding", 0, 192, 8)]).

Definition layout_structZ20pthread_key_data : record_layout :=
  (mkRecordLayout "struct pthread_key_data" 16 8 [("seq", 0, 8, 8); ("data", 8, 8, 8)]).

Definition layout_structZ20pthread_unwind_buf : record_layout :=
  (mkRecordLayout "struct pthread_unwind_buf" 104 8 [("cancel_jmp_buf", 0, 72, 8); ("priv", 72, 32, 8)]).

Definition layout_structZ20robust_list_head : record_layout :=
  (mkRecordLayout "struct robust_list_head" 24 8 [("list", 0, 8, 8); ("futex_offset", 8, 8, 8); ("list_op_pending", 16, 8, 8)]).

Definition layout_structZ20sched_param : record_layout :=
  (mkRecordLayout "struct sched_param" 4 4 [("sched_priority", 0, 4, 4)]).

Definition layout_structZ20sockaddr_in : record_layout :=
  (mkRecordLayout "struct sockaddr_in" 16 4 [("sin_family", 0, 2, 2); ("sin_port", 2, 2, 2); ("sin_addr", 4, 4, 4); ("sin_zero", 8, 8, 1)]).

Definition layout_structZ20sockaddr_in6 : record_layout :=
  (mkRecordLayout "struct sockaddr_in6" 28 4 [("sin6_family", 0, 2, 2); ("sin6_port", 2, 2, 2); ("sin6_flowinfo", 4, 4, 4); ("sin6_addr", 8, 16, 4); ("sin6_scope_id", 24, 4, 4)]).

Definition layout_structZ20td_thr_events : record_layout :=
  (mkRecordLayout "struct td_thr_events" 8 4 [("event_bits", 0, 8, 4)]).

Definition layout_structZ20tls_internal_t : record_layout :=
  (mkRecordLayout "struct tls_internal_t" 16 8 [("strsignal_buf", 0, 8, 8); ("strerror_l_buf", 8, 8, 8)]).

Definition layout_typedefZ20__128bits : record_layout :=
  (mkRecordLayout "typedef __128bits" 16 4 [("i", 0, 16, 4)]).

Definition layout_typedefZ20dtv_t : record_layout :=
  (mkRecordLayout "typedef dtv_t" 16 8 [("counter", 0, 8, 8); ("pointer", 0, 16, 8)]).

Definition layout_typedefZ20internal_sigset_t : record_layout :=
  (mkRecordLayout "typedef internal_sigset_t" 128 8 [("__val", 0, 128, 8)]).

Definition layout_typedefZ20list_t : record_layout :=
  (mkRecordLayout "typedef list_t" 16 8 [("next", 0, 8, 8); ("prev", 8, 8, 8)]).

Definition layout_typedefZ20tcbhead_t : record_layout :=
  (mkRecordLayout "typedef tcbhead_t" 704 32 [("tcb", 0, 8, 8); ("dtv", 8, 8, 8); ("self", 16, 8, 8); ("multiple_threads", 24, 4, 4); ("gscope_flag", 28, 4, 4); ("sysinfo", 32, 8, 8); ("stack_guard", 40, 8, 8); ("__unused", 48, 8, 8); ("unused_vgetcpu_cache", 56, 16, 8); ("feature_1", 72, 4, 4); ("__glibc_unused1", 76, 4, 4); ("__private_tm", 80, 32, 8); ("__private_ss", 112, 8, 8); ("ssp_base", 120, 8, 8); ("__glibc_unused2", 128, 512, 4); ("__padding", 640, 64, 8)]).

Definition layout_typedefZ20td_eventbuf_t : record_layout :=
  (mkRecordLayout "typedef td_eventbuf_t" 24 8 [("eventmask", 0, 8, 4); ("eventnum", 8, 4, 4); ("eventdata", 16, 8, 8)]).

Definition layout_typedefZ20td_thr_events_t : record_layout :=
  (mkRecordLayout "typedef td_thr_events_t" 8 4 [("event_bits", 0, 8, 4)]).

Definition layout_unionZ20dtv : record_layout :=
  (mkRecordLayout "union dtv" 16 8 [("counter", 0, 8, 8); ("pointer", 0, 16, 8)]).

(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_item_hi_atexit'23str'2e0 : item :=
  (IData (a "hi_atexit#str.0") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition hi_item_malloc : item :=
  (IAlias (a "malloc") (a "export") (a "__GI___libc_malloc")).

Definition hi_item_free : item :=
  (IAlias (a "free") (a "export") (a "__GI___libc_free")).

Definition hi_item_calloc : item :=
  (IAlias (a "calloc") (a "weak") (a "__libc_calloc")).

Definition hi_item_glibc_malloc'23__always_fail_morecore : item :=
  (IData (a "glibc_malloc#__always_fail_morecore") LLocal 1 [(Item Wb 0)]).

Definition hi_item_glibc_malloc'23__tcache_dummy : item :=
  (IData (a "glibc_malloc#__tcache_dummy") (LRo (a "local")) 8 [(Zero 768)]).

Definition hi_item_glibc_malloc'23main_arena : item :=
  (IData (a "glibc_malloc#main_arena") LLocal 8 [(Item Ww 0); (Zero 2068); (Sym (a "glibc_malloc#main_arena") 0); (Zero 8); (Item Wl 1); (Zero 16)]).

Definition hi_item_glibc_malloc'23mp_ : item :=
  (IData (a "glibc_malloc#mp_") LLocal 8 [(Item Wl 131072); (Item Wl 131072); (Item Wl 131072); (Item Wl 8); (Zero 8); (Item Ww 0); (Zero 28); (Item Ww 65536); (Zero 36); (Item Wl 64); (Item Wl 1041); (Item Wl 16)]).

Definition hi_item_glibc_malloc'23perturb_byte : item :=
  (IData (a "glibc_malloc#perturb_byte") LLocal 4 [(Zero 4)]).

Definition hi_item_tcache : item :=
  (IData (a "tcache") (LTls (a "local")) 8 [(Sym (a "glibc_malloc#__tcache_dummy") 0)]).

Definition hi_item_glibc_malloc'23tcache_key : item :=
  (IData (a "glibc_malloc#tcache_key") LLocal 8 [(Zero 8)]).

Definition hi_item_thread_arena : item :=
  (IData (a "thread_arena") (LTls (a "local")) 8 [(Zero 8)]).

Definition hi_item_glibc_malloc'23str'2e407 : item :=
  (IData (a "glibc_malloc#str.407") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition hi_item_glibc_malloc'23str'2e408 : item :=
  (IData (a "glibc_malloc#str.408") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hi_item_glibc_malloc'23str'2e421 : item :=
  (IData (a "glibc_malloc#str.421") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 40); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 116); (Item Wb 99); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 117); (Item Wb 110); (Item Wb 107); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hi_item___exit_funcs : item :=
  (IData (a "__exit_funcs") LExport 8 [(Sym (a "glibc_cxa_atexit#initial") 0)]).

Definition hi_item___exit_funcs_lock : item :=
  (IData (a "__exit_funcs_lock") LExport 4 [(Zero 4)]).

Definition hi_item___new_exitfn_called : item :=
  (IData (a "__new_exitfn_called") LExport 8 [(Zero 8)]).

Definition hi_item_glibc_cxa_atexit'23initial : item :=
  (IData (a "glibc_cxa_atexit#initial") LLocal 8 [(Zero 1040)]).

Definition hi_item_glibc_cxa_atexit'23str'2e233 : item :=
  (IData (a "glibc_cxa_atexit#str.233") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 110); (Item Wb 99); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hi_item_glibc_cxa_atexit'23str'2e234 : item :=
  (IData (a "glibc_cxa_atexit#str.234") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 120); (Item Wb 97); (Item Wb 95); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hi_item_glibc_cxa_atexit'23str'2e235 : item :=
  (IData (a "glibc_cxa_atexit#str.235") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 95); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition hi_item_glibc_cxa_atexit'23str'2e236 : item :=
  (IData (a "glibc_cxa_atexit#str.236") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hi_item_glibc_cxa_atexit'23str'2e237 : item :=
  (IData (a "glibc_cxa_atexit#str.237") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 110); (Item Wb 101); (Item Wb 119); (Item Wb 95); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 102); (Item Wb 110); (Item Wb 0)]).

Definition hi_item___cxa_atexit : item :=
  (IAlias (a "__cxa_atexit") (a "export") (a "__GI___cxa_atexit")).

Definition hi_item___libc_errno : item :=
  (IAlias (a "__libc_errno") (a "export") (a "errno")).

Definition hi_item_errno : item :=
  (IData (a "errno") (LTls (a "export")) 4 [(Zero 4)]).

Definition hi_item_ferror : item :=
  (IAlias (a "ferror") (a "weak") (a "_IO_ferror")).

Definition hi_item___GI__IO_file_xsputn : item :=
  (IAlias (a "__GI__IO_file_xsputn") (a "export") (a "_IO_new_file_xsputn")).

Definition hi_item___GI__IO_file_sync : item :=
  (IAlias (a "__GI__IO_file_sync") (a "export") (a "_IO_new_file_sync")).

Definition hi_item___GI__IO_file_overflow : item :=
  (IAlias (a "__GI__IO_file_overflow") (a "export") (a "_IO_new_file_overflow")).

Definition hi_item___GI__IO_file_underflow : item :=
  (IAlias (a "__GI__IO_file_underflow") (a "export") (a "_IO_new_file_underflow")).

Definition hi_item___GI__IO_file_setbuf : item :=
  (IAlias (a "__GI__IO_file_setbuf") (a "export") (a "_IO_new_file_setbuf")).

Definition hi_item___GI__IO_file_finish : item :=
  (IAlias (a "__GI__IO_file_finish") (a "export") (a "_IO_new_file_finish")).

Definition hi_item_glibc_genops'23dealloc_buffers : item :=
  (IData (a "glibc_genops#dealloc_buffers") LLocal 1 [(Zero 1)]).

Definition hi_item_glibc_genops'23freeres_list : item :=
  (IData (a "glibc_genops#freeres_list") LLocal 8 [(Zero 8)]).

Definition hi_item_glibc_genops'23list_all_lock : item :=
  (IData (a "glibc_genops#list_all_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition hi_item_glibc_genops'23run_fp : item :=
  (IData (a "glibc_genops#run_fp") LLocal 8 [(Zero 8)]).

Definition hi_item_fclose : item :=
  (IAlias (a "fclose") (a "export") (a "_IO_new_fclose")).

Definition hi_item_puts : item :=
  (IAlias (a "puts") (a "export") (a "__GI__IO_puts")).

Definition hi_item__IO_2_1_stderr_ : item :=
  (IData (a "_IO_2_1_stderr_") LExport 8 [(Item Ww (-72540026)); (Zero 4); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_2_1_stdout_") 0); (Item Ww 2); (Item Wb 0); (Item Wb 0); (Item Wb 0); (Str [0]); (Item Wl (-1)); (Item Wh 0); (Item Wb 0); (Str [0]); (Zero 4); (Sym (a "glibc_stdfiles#_IO_stdfile_2_lock") 0); (Item Wl (-1)); (Item Wl 0); (Sym (a "glibc_stdfiles#_IO_wide_data_2") 0); (Item Wl 0); (Zero 40); (Sym (a "__io_vtables") 336)]).

Definition hi_item__IO_2_1_stdin_ : item :=
  (IData (a "_IO_2_1_stdin_") LExport 8 [(Item Ww (-72540024)); (Zero 4); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Item Wb 0); (Item Wb 0); (Item Wb 0); (Str [0]); (Item Wl (-1)); (Item Wh 0); (Item Wb 0); (Str [0]); (Zero 4); (Sym (a "glibc_stdfiles#_IO_stdfile_0_lock") 0); (Item Wl (-1)); (Item Wl 0); (Sym (a "glibc_stdfiles#_IO_wide_data_0") 0); (Item Wl 0); (Zero 40); (Sym (a "__io_vtables") 336)]).

Definition hi_item__IO_2_1_stdout_ : item :=
  (IData (a "_IO_2_1_stdout_") LExport 8 [(Item Ww (-72540028)); (Zero 4); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_2_1_stdin_") 0); (Item Ww 1); (Item Wb 0); (Item Wb 0); (Item Wb 0); (Str [0]); (Item Wl (-1)); (Item Wh 0); (Item Wb 0); (Str [0]); (Zero 4); (Sym (a "glibc_stdfiles#_IO_stdfile_1_lock") 0); (Item Wl (-1)); (Item Wl 0); (Sym (a "glibc_stdfiles#_IO_wide_data_1") 0); (Item Wl 0); (Zero 40); (Sym (a "__io_vtables") 336)]).

Definition hi_item___GI__IO_list_all : item :=
  (IData (a "__GI__IO_list_all") LExport 8 [(Sym (a "_IO_2_1_stderr_") 0)]).

Definition hi_item_glibc_stdfiles'23_IO_stdfile_0_lock : item :=
  (IData (a "glibc_stdfiles#_IO_stdfile_0_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition hi_item_glibc_stdfiles'23_IO_stdfile_1_lock : item :=
  (IData (a "glibc_stdfiles#_IO_stdfile_1_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition hi_item_glibc_stdfiles'23_IO_stdfile_2_lock : item :=
  (IData (a "glibc_stdfiles#_IO_stdfile_2_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition hi_item_glibc_stdfiles'23_IO_wide_data_0 : item :=
  (IData (a "glibc_stdfiles#_IO_wide_data_0") LLocal 8 [(Zero 224); (Sym (a "__io_vtables") 840)]).

Definition hi_item_glibc_stdfiles'23_IO_wide_data_1 : item :=
  (IData (a "glibc_stdfiles#_IO_wide_data_1") LLocal 8 [(Zero 224); (Sym (a "__io_vtables") 840)]).

Definition hi_item_glibc_stdfiles'23_IO_wide_data_2 : item :=
  (IData (a "glibc_stdfiles#_IO_wide_data_2") LLocal 8 [(Zero 224); (Sym (a "__io_vtables") 840)]).

Definition hi_item___nanofil_ctor__IO_stdfiles_init : item :=
  (IData (a "__nanofil_ctor__IO_stdfiles_init") (LInit (a "ctor") (a "none")) 8 [(Sym (a "glibc_stdfiles#_IO_stdfiles_init") 0)]).

Definition hi_item_stdout : item :=
  (IData (a "stdout") LExport 8 [(Sym (a "_IO_2_1_stdout_") 0)]).

Definition hi_item_IO_accept_foreign_vtables : item :=
  (IData (a "IO_accept_foreign_vtables") LExport 8 [(Zero 8)]).

Definition hi_item___io_vtables : item :=
  (IData (a "__io_vtables") (LRo (a "export")) 8 (app (app (app [(Item Wl 0); (Item Wl 0); (Sym (a "_IO_str_finish") 0); (Sym (a "__GI__IO_str_overflow") 0); (Sym (a "__GI__IO_str_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_str_pbackfail") 0); (Sym (a "__GI__IO_default_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "__GI__IO_str_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_default_setbuf") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "__GI__IO_default_doallocate") 0); (Sym (a "_IO_default_read") 0); (Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_wstr_finish") 0); (Sym (a "_IO_wstr_overflow") 0); (Sym (a "_IO_wstr_underflow") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "_IO_wstr_pbackfail") 0); (Sym (a "__GI__IO_wdefault_xsputn") 0); (Sym (a "__GI__IO_wdefault_xsgetn") 0); (Sym (a "_IO_wstr_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_default_setbuf") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "__GI__IO_wdefault_doallocate") 0); (Sym (a "_IO_default_read") 0)] [(Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "__GI__IO_file_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "__GI__IO_file_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "_IO_new_file_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_new_file_setbuf") 0); (Sym (a "_IO_new_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "_IO_file_underflow_mmap") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "_IO_new_file_xsputn") 0); (Sym (a "_IO_file_xsgetn_mmap") 0); (Sym (a "_IO_file_seekoff_mmap") 0)]) (app [(Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "_IO_file_sync_mmap") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "_IO_file_close_mmap") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "_IO_file_underflow_maybe_mmap") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "_IO_new_file_xsputn") 0); (Sym (a "_IO_file_xsgetn_maybe_mmap") 0); (Sym (a "_IO_file_seekoff_maybe_mmap") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "_IO_new_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "__GI__IO_wfile_overflow") 0); (Sym (a "__GI__IO_wfile_underflow") 0)] [(Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "__GI__IO_wdefault_pbackfail") 0); (Sym (a "__GI__IO_wfile_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "__GI__IO_wfile_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_new_file_setbuf") 0); (Sym (a "__GI__IO_wfile_sync") 0); (Sym (a "_IO_wfile_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "__GI__IO_wfile_overflow") 0); (Sym (a "_IO_wfile_underflow_mmap") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "__GI__IO_wdefault_pbackfail") 0); (Sym (a "__GI__IO_wfile_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "__GI__IO_wfile_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "__GI__IO_wfile_sync") 0); (Sym (a "_IO_wfile_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "_IO_file_close_mmap") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0)])) (app (app [(Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "__GI__IO_wfile_overflow") 0); (Sym (a "_IO_wfile_underflow_maybe_mmap") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "__GI__IO_wdefault_pbackfail") 0); (Sym (a "__GI__IO_wfile_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "__GI__IO_wfile_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "__GI__IO_wfile_sync") 0); (Sym (a "_IO_wfile_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "__GI__IO_file_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "__GI__IO_file_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "_IO_cookie_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "__GI__IO_file_setbuf") 0); (Sym (a "__GI__IO_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "_IO_cookie_read") 0)] [(Sym (a "_IO_cookie_write") 0); (Sym (a "_IO_cookie_seek") 0); (Sym (a "_IO_cookie_close") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "_IO_new_file_overflow") 0); (Sym (a "_IO_new_file_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "_IO_new_file_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "_IO_new_file_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_new_file_setbuf") 0); (Sym (a "_IO_new_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "_IO_new_proc_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_mem_finish") 0); (Sym (a "__GI__IO_str_overflow") 0); (Sym (a "__GI__IO_str_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_str_pbackfail") 0); (Sym (a "__GI__IO_default_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "__GI__IO_str_seekoff") 0)]) (app [(Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_mem_setbuf") 0); (Sym (a "_IO_mem_sync") 0); (Sym (a "_IO_mem_doallocate") 0); (Sym (a "_IO_default_read") 0); (Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_wmem_finish") 0); (Sym (a "_IO_wstr_overflow") 0); (Sym (a "_IO_wstr_underflow") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "_IO_wstr_pbackfail") 0); (Sym (a "__GI__IO_wdefault_xsputn") 0); (Sym (a "__GI__IO_wdefault_xsgetn") 0); (Sym (a "_IO_wstr_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_wmem_setbuf") 0); (Sym (a "_IO_wmem_sync") 0); (Sym (a "_IO_wmem_doallocate") 0); (Sym (a "_IO_default_read") 0); (Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "__printf_buffer_as_file_overflow") 0); (Item Wl 0)] [(Item Wl 0); (Item Wl 0); (Sym (a "__printf_buffer_as_file_xsputn") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "__wprintf_buffer_as_file_overflow") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "__wprintf_buffer_as_file_xsputn") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0)])))).

Definition hi_item_glibc_vtables'23str'2e302 : item :=
  (IData (a "glibc_vtables#str.302") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 100); (Item Wb 105); (Item Wb 111); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 10); (Item Wb 0)]).

Definition hi_item___nanofil_ctor_check_stdfiles_vtables : item :=
  (IData (a "__nanofil_ctor_check_stdfiles_vtables") (LInit (a "ctor") (a "none")) 8 [(Sym (a "glibc_vtables#check_stdfiles_vtables") 0)]).

Definition hi_item___GI___write : item :=
  (IAlias (a "__GI___write") (a "export") (a "__GI___libc_write")).

Definition hi_item__exit : item :=
  (IAlias (a "_exit") (a "export") (a "__GI__exit")).

Definition hi_item___exit_funcs_done : item :=
  (IData (a "__exit_funcs_done") LExport 1 [(Item Wb 0)]).

Definition hi_item_glibc_exit'23__exit_lock : item :=
  (IData (a "glibc_exit#__exit_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition hi_item_exit : item :=
  (IAlias (a "exit") (a "export") (a "__GI_exit")).

Definition hi_item___libc_single_threaded_internal : item :=
  (IAlias (a "__libc_single_threaded_internal") (a "export") (a "__libc_single_threaded")).

Definition hi_item___libc_single_threaded : item :=
  (IData (a "__libc_single_threaded") LExport 1 [(Zero 1)]).

Definition hi_item___GI_strlen : item :=
  (IAlias (a "__GI_strlen") (a "weak") (a "__strlen")).

Definition hi_item___GI_mempcpy : item :=
  (IAlias (a "__GI_mempcpy") (a "export") (a "__GI___mempcpy")).

Definition hi_item___x86_data_cache_size : item :=
  (IData (a "__x86_data_cache_size") LExport 8 [(Item Wl 32768)]).

Definition hi_item___x86_data_cache_size_half : item :=
  (IData (a "__x86_data_cache_size_half") LExport 8 [(Item Wl 16384)]).

Definition hi_item___x86_memset_non_temporal_threshold : item :=
  (IData (a "__x86_memset_non_temporal_threshold") LExport 8 [(Zero 8)]).

Definition hi_item___x86_rep_movsb_stop_threshold : item :=
  (IData (a "__x86_rep_movsb_stop_threshold") LExport 8 [(Zero 8)]).

Definition hi_item___x86_rep_movsb_threshold : item :=
  (IData (a "__x86_rep_movsb_threshold") LExport 8 [(Item Wl 2048)]).

Definition hi_item___x86_rep_stosb_threshold : item :=
  (IData (a "__x86_rep_stosb_threshold") LExport 8 [(Item Wl 2048)]).

Definition hi_item___x86_shared_cache_size : item :=
  (IData (a "__x86_shared_cache_size") LExport 8 [(Item Wl 1048576)]).

Definition hi_item___x86_shared_cache_size_half : item :=
  (IData (a "__x86_shared_cache_size_half") LExport 8 [(Item Wl 524288)]).

Definition hi_item___x86_shared_non_temporal_threshold : item :=
  (IData (a "__x86_shared_non_temporal_threshold") LExport 8 [(Zero 8)]).

Definition hi_item___x86_string_control : item :=
  (IData (a "__x86_string_control") LExport 4 [(Zero 4)]).

Definition hi_item__dl_x86_features_tlsdesc_state_size : item :=
  (IData (a "_dl_x86_features_tlsdesc_state_size") LExport 8 [(Zero 8)]).

Definition hi_item_glibc_libc_start'23intel_02_known : item :=
  (IData (a "glibc_libc_start#intel_02_known") (LRo (a "local")) 4 (app (app (app [(Item Wb 6); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 8192); (Item Wb 8); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 16384); (Item Wb 9); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 32768); (Item Wb 10); (Item Wb 2); (Item Wb 32); (Item Wb 3); (Item Ww 8192); (Item Wb 12); (Item Wb 4); (Item Wb 32); (Item Wb 3); (Item Ww 16384); (Item Wb 13); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 14); (Item Wb 6); (Item Wb 64); (Item Wb 3); (Item Ww 24576); (Item Wb 33); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 34); (Item Wb 4)] [(Item Wb 64); (Item Wb 9); (Item Ww 524288); (Item Wb 35); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 37); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 41); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 44); (Item Wb 8); (Item Wb 64); (Item Wb 3); (Item Ww 32768); (Item Wb 48); (Item Wb 8); (Item Wb 64); (Item Wb 0); (Item Ww 32768); (Item Wb 57); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 131072); (Item Wb 58); (Item Wb 6); (Item Wb 64); (Item Wb 6); (Item Ww 196608); (Item Wb 59); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 131072)]) (app [(Item Wb 60); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 61); (Item Wb 6); (Item Wb 64); (Item Wb 6); (Item Ww 393216); (Item Wb 62); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 63); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 65); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 131072); (Item Wb 66); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 262144); (Item Wb 67); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 524288); (Item Wb 68); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 1048576); (Item Wb 69); (Item Wb 4)] [(Item Wb 32); (Item Wb 6); (Item Ww 2097152); (Item Wb 70); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 71); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 72); (Item Wb 12); (Item Wb 64); (Item Wb 6); (Item Ww 3145728); (Item Wb 73); (Item Wb 16); (Item Wb 64); (Item Wb 6); (Item Ww 4194304); (Item Wb 74); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 6291456); (Item Wb 75); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 76); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 12582912); (Item Wb 77); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 16777216)])) (app (app [(Item Wb 78); (Item Wb 24); (Item Wb 64); (Item Wb 6); (Item Ww 6291456); (Item Wb 96); (Item Wb 8); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 102); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 8192); (Item Wb 103); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 104); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 32768); (Item Wb 120); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 121); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 131072); (Item Wb 122); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 123); (Item Wb 8)] [(Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 124); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 125); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 2097152); (Item Wb 127); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 128); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 130); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 262144); (Item Wb 131); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 524288); (Item Wb 132); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 1048576); (Item Wb 133); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 2097152)]) (app [(Item Wb 134); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 135); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 208); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 524288); (Item Wb 209); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 210); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 214); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 215); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 216); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 220); (Item Wb 12)] [(Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 221); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 222); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 226); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 227); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 228); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 234); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 12582912); (Item Wb 235); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 18874368); (Item Wb 236); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 25165824)])))).

Definition hi_item_glibc_libc_start'23sigall_set : item :=
  (IData (a "glibc_libc_start#sigall_set") (LRo (a "local")) 8 [(Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615)]).

Definition hi_item_glibc_libc_start'23str'2e301 : item :=
  (IData (a "glibc_libc_start#str.301") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 102); (Item Wb 102); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 50); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e302 : item :=
  (IData (a "glibc_libc_start#str.302") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 120); (Item Wb 56); (Item Wb 54); (Item Wb 47); (Item Wb 100); (Item Wb 108); (Item Wb 45); (Item Wb 99); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e303 : item :=
  (IData (a "glibc_libc_start#str.303") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 108); (Item Wb 95); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 99); (Item Wb 107); (Item Wb 95); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 100); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e304 : item :=
  (IData (a "glibc_libc_start#str.304") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 122); (Item Wb 104); (Item Wb 97); (Item Wb 111); (Item Wb 120); (Item Wb 105); (Item Wb 110); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e319 : item :=
  (IData (a "glibc_libc_start#str.319") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110)] [(Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 10); (Item Wb 9); (Item Wb 0)])).

Definition hi_item_glibc_libc_start'23str'2e320 : item :=
  (IData (a "glibc_libc_start#str.320") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 103); (Item Wb 114); (Item Wb 97); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 10); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e321 : item :=
  (IData (a "glibc_libc_start#str.321") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 116); (Item Wb 114); (Item Wb 111); (Item Wb 108); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 10); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e322 : item :=
  (IData (a "glibc_libc_start#str.322") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e323 : item :=
  (IData (a "glibc_libc_start#str.323") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 110); (Item Wb 112); (Item Wb 116); (Item Wb 108); (Item Wb 47); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e324 : item :=
  (IData (a "glibc_libc_start#str.324") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 107); (Item Wb 101); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e325 : item :=
  (IData (a "glibc_libc_start#str.325") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e326 : item :=
  (IData (a "glibc_libc_start#str.326") (LRo (a "local")) 1 [(Item Wb 120); (Item Wb 101); (Item Wb 111); (Item Wb 110); (Item Wb 95); (Item Wb 112); (Item Wb 104); (Item Wb 105); (Item Wb 0)]).

Definition hi_item_glibc_libc_start'23str'2e327 : item :=
  (IData (a "glibc_libc_start#str.327") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 97); (Item Wb 115); (Item Wb 119); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 0)]).

Definition hi_item___pthread_initialize_minimal : item :=
  (IData (a "__pthread_initialize_minimal") LExternWeak 1 []).

Definition hi_item___libc_initial : item :=
  (IData (a "__libc_initial") LExport 1 [(Zero 1)]).

Definition hi_item___nptl_initial_report_events : item :=
  (IData (a "__nptl_initial_report_events") LExport 1 [(Zero 1)]).

Definition hi_item___libc_tsd_CTYPE_B : item :=
  (IData (a "__libc_tsd_CTYPE_B") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_class") 256)]).

Definition hi_item___libc_tsd_CTYPE_TOLOWER : item :=
  (IData (a "__libc_tsd_CTYPE_TOLOWER") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_tolower") 512)]).

Definition hi_item___libc_tsd_CTYPE_TOUPPER : item :=
  (IData (a "__libc_tsd_CTYPE_TOUPPER") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_toupper") 512)]).

Definition hi_item___GI___default_pthread_attr : item :=
  (IData (a "__GI___default_pthread_attr") LExport 8 [(Zero 56)]).

Definition hi_item___GI___nptl_nthreads : item :=
  (IData (a "__GI___nptl_nthreads") LExport 4 [(Item Ww 1)]).

Definition hi_item___GI___mutex_aconf : item :=
  (IData (a "__GI___mutex_aconf") LExport 4 [(Item Ww 100)]).

Definition hi_item___environ : item :=
  (IData (a "__environ") LExport 8 [(Item Wl 0)]).

Definition hi_item___libc_dlerror_result_string : item :=
  (IData (a "__libc_dlerror_result_string") (LTls (a "export")) 8 [(Zero 8)]).

Definition hi_item___libc_enable_secure : item :=
  (IData (a "__libc_enable_secure") LExport 4 [(Item Ww 1)]).

Definition hi_item_glibc_dl_tunables'23tunable_list : item :=
  (IData (a "glibc_dl_tunables#tunable_list") LLocal 8 (app (app (app [(Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 104; 119; 99; 97; 112; 115]); (Zero 32); (Item Ww 3); (Zero 4); (Item Wl 0); (Item Wl 0); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 112; 108; 116; 95; 114; 101; 119; 114; 105; 116; 101]); (Zero 27); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 2); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 112; 114; 101; 102; 101; 114; 95; 109; 97; 112; 95; 51; 50; 98; 105; 116; 95; 101; 120; 101; 99]); (Zero 17); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [76; 68; 95; 80; 82; 69; 70; 69; 82; 95; 77; 65; 80; 95; 51; 50; 66; 73; 84; 95; 69; 88; 69; 67]); (Zero 6); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 100; 97; 116; 97; 95; 99; 97; 99; 104; 101; 95; 115; 105; 122; 101]); (Zero 19); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 105; 98; 116]); (Zero 31); (Item Ww 3); (Zero 4); (Item Wl 0); (Item Wl 0); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0])] [(Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 109; 101; 109; 115; 101; 116; 95; 110; 111; 110; 95; 116; 101; 109; 112; 111; 114; 97; 108; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 5); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 110; 111; 110; 95; 116; 101; 109; 112; 111; 114; 97; 108; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 12); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 114; 101; 112; 95; 109; 111; 118; 115; 98; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 15); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 114; 101; 112; 95; 115; 116; 111; 115; 98; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 15); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Item Wl 2048); (Zero 8); (Item Wl 2048); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 115; 104; 97; 114; 101; 100; 95; 99; 97; 99; 104; 101; 95; 115; 105; 122; 101]); (Zero 17); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1))]) (app [(Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 115; 104; 115; 116; 107]); (Zero 29); (Item Ww 3); (Zero 4); (Item Wl 0); (Item Wl 0); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 101; 108; 102; 46; 116; 104; 112]); (Zero 35); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 103; 109; 111; 110; 46; 109; 97; 120; 97; 114; 99; 115]); (Zero 30); (Item Ww 0); (Zero 4); (Item Wl 50); (Item Wl 2147483647); (Item Wl 1048576); (Zero 8); (Item Wl 1048576); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 103; 109; 111; 110; 46; 109; 105; 110; 97; 114; 99; 115]); (Zero 30); (Item Ww 0); (Zero 4); (Item Wl 50); (Item Wl 2147483647); (Item Wl 50); (Zero 8); (Item Wl 50); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0])] [(Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 97; 114; 101; 110; 97; 95; 109; 97; 120]); (Zero 26); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 65; 82; 69; 78; 65; 95; 77; 65; 88]); (Zero 14); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 97; 114; 101; 110; 97; 95; 116; 101; 115; 116]); (Zero 25); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 65; 82; 69; 78; 65; 95; 84; 69; 83; 84]); (Zero 13); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 99; 104; 101; 99; 107]); (Zero 30); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 3); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 67; 72; 69; 67; 75; 95]); (Zero 17); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 104; 117; 103; 101; 116; 108; 98]); (Zero 28); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 109; 109; 97; 112; 95; 109; 97; 120]); (Zero 27); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 2147483647); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 77; 77; 65; 80; 95; 77; 65; 88; 95])])) (app (app [(Zero 14); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 109; 109; 97; 112; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 21); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 77; 77; 65; 80; 95; 84; 72; 82; 69; 83; 72; 79; 76; 68; 95]); (Zero 8); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 109; 120; 102; 97; 115; 116]); (Zero 29); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 112; 101; 114; 116; 117; 114; 98]); (Zero 28); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 255); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 80; 69; 82; 84; 85; 82; 66; 95]); (Zero 15); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 99; 97; 99; 104; 101; 95; 99; 111; 117; 110; 116]); (Zero 23); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 99; 97; 99; 104; 101; 95; 109; 97; 120]); (Zero 25); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0)] [(Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 111; 112; 95; 112; 97; 100]); (Zero 28); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Item Wl 131072); (Zero 8); (Item Wl 131072); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 84; 79; 80; 95; 80; 65; 68; 95]); (Zero 15); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 114; 105; 109; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 21); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 84; 82; 73; 77; 95; 84; 72; 82; 69; 83; 72; 79; 76; 68; 95]); (Zero 8); (Str [103; 108; 105; 98; 99; 46; 109; 101; 109; 46; 100; 101; 99; 111; 114; 97; 116; 101; 95; 109; 97; 112; 115]); (Zero 25); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 109; 117; 116; 101; 120; 95; 115; 112; 105; 110; 95; 99; 111; 117; 110; 116]); (Zero 18); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 32767); (Item Wl 100); (Zero 8); (Item Wl 100); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 114; 115; 101; 113]); (Zero 30); (Item Ww 0)]) (app [(Zero 4); (Item Wl 0); (Item Wl 1); (Item Wl 1); (Zero 8); (Item Wl 1); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 115; 116; 97; 99; 107; 95; 99; 97; 99; 104; 101; 95; 115; 105; 122; 101]); (Zero 18); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Item Wl 41943040); (Zero 8); (Item Wl 41943040); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 115; 116; 97; 99; 107; 95; 104; 117; 103; 101; 116; 108; 98]); (Zero 21); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Item Wl 1); (Zero 8); (Item Wl 1); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 100; 121; 110; 97; 109; 105; 99; 95; 115; 111; 114; 116]); (Zero 25); (Item Ww 0); (Zero 4); (Item Wl 1); (Item Wl 2); (Item Wl 2); (Zero 8); (Item Wl 2); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 101; 110; 97; 98; 108; 101; 95; 115; 101; 99; 117; 114; 101])] [(Zero 24); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Item Wl 0); (Zero 8); (Item Wl 0); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 101; 120; 101; 99; 115; 116; 97; 99; 107]); (Zero 28); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 2); (Item Wl 1); (Zero 8); (Item Wl 1); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 110; 110; 115]); (Zero 34); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl 16); (Item Wl 4); (Zero 8); (Item Wl 4); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 111; 112; 116; 105; 111; 110; 97; 108; 95; 115; 116; 97; 116; 105; 99; 95; 116; 108; 115]); (Zero 18); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Item Wl 512); (Zero 8); (Item Wl 512); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29)])))).

Definition hi_item___libc_stack_end : item :=
  (IData (a "__libc_stack_end") LExport 8 [(Zero 8)]).

Definition hi_item__dl_auxv : item :=
  (IData (a "_dl_auxv") LExport 8 [(Zero 8)]).

Definition hi_item__dl_debug_mask : item :=
  (IData (a "_dl_debug_mask") LExport 4 [(Zero 4)]).

Definition hi_item__dl_hwcap : item :=
  (IData (a "_dl_hwcap") LExport 8 [(Zero 8)]).

Definition hi_item__dl_hwcap2 : item :=
  (IData (a "_dl_hwcap2") LExport 8 [(Zero 8)]).

Definition hi_item__dl_minsigstacksize : item :=
  (IData (a "_dl_minsigstacksize") LExport 8 [(Item Wl 0)]).

Definition hi_item__dl_pagesize : item :=
  (IData (a "_dl_pagesize") LExport 8 [(Item Wl 4096)]).

Definition hi_item__dl_platform : item :=
  (IData (a "_dl_platform") LExport 8 [(Zero 8)]).

Definition hi_item__dl_thp_mode : item :=
  (IData (a "_dl_thp_mode") LExport 4 [(Zero 4)]).

Definition hi_item__dl_x86_cpu_features : item :=
  (IData (a "_dl_x86_cpu_features") LExport 8 [(Zero 528)]).

Definition hi_item__dl_x86_feature_control : item :=
  (IData (a "_dl_x86_feature_control") LExport 4 [(Item Wb 0); (Zero 3)]).

Definition hi_item___GI___getrlimit : item :=
  (IAlias (a "__GI___getrlimit") (a "export") (a "__GI___getrlimit64")).

Definition hi_item___libc_argc : item :=
  (IData (a "__libc_argc") LExport 4 [(Zero 4)]).

Definition hi_item___libc_argv : item :=
  (IData (a "__libc_argv") LExport 8 [(Zero 8)]).

Definition hi_item___nanofil_ctor__init_first : item :=
  (IData (a "__nanofil_ctor__init_first") (LInit (a "ctor") (a "none")) 8 [(Sym (a "glibc_init_first#_init_first") 0)]).

Definition hi_item___progname : item :=
  (IData (a "__progname") LExport 8 [(Sym (a "glibc_init_misc#str.61") 0)]).

Definition hi_item___progname_full : item :=
  (IData (a "__progname_full") LExport 8 [(Sym (a "glibc_init_misc#str.61") 0)]).

Definition hi_item_glibc_init_misc'23str'2e61 : item :=
  (IData (a "glibc_init_misc#str.61") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hi_item___libc_tsd_LOCALE : item :=
  (IData (a "__libc_tsd_LOCALE") (LTls (a "export")) 8 [(Sym (a "_nl_global_locale") 0)]).

Definition hi_item__nl_global_locale : item :=
  (IData (a "_nl_global_locale") LExport 8 [(Sym (a "_nl_C_LC_CTYPE") 0); (Sym (a "_nl_C_LC_NUMERIC") 0); (Sym (a "_nl_C_LC_TIME") 0); (Sym (a "_nl_C_LC_COLLATE") 0); (Sym (a "_nl_C_LC_MONETARY") 0); (Sym (a "_nl_C_LC_MESSAGES") 0); (Zero 8); (Sym (a "_nl_C_LC_PAPER") 0); (Sym (a "_nl_C_LC_NAME") 0); (Sym (a "_nl_C_LC_ADDRESS") 0); (Sym (a "_nl_C_LC_TELEPHONE") 0); (Sym (a "_nl_C_LC_MEASUREMENT") 0); (Sym (a "_nl_C_LC_IDENTIFICATION") 0); (Sym (a "_nl_C_LC_CTYPE_class") 256); (Sym (a "_nl_C_LC_CTYPE_tolower") 512); (Sym (a "_nl_C_LC_CTYPE_toupper") 512); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0)]).

Definition hi_item__nl_C_LC_ADDRESS : item :=
  (IData (a "_nl_C_LC_ADDRESS") LExternWeak 1 []).

Definition hi_item__nl_C_LC_COLLATE : item :=
  (IData (a "_nl_C_LC_COLLATE") LExternWeak 1 []).

Definition hi_item__nl_C_LC_IDENTIFICATION : item :=
  (IData (a "_nl_C_LC_IDENTIFICATION") LExternWeak 1 []).

Definition hi_item__nl_C_LC_MEASUREMENT : item :=
  (IData (a "_nl_C_LC_MEASUREMENT") LExternWeak 1 []).

Definition hi_item__nl_C_LC_MESSAGES : item :=
  (IData (a "_nl_C_LC_MESSAGES") LExternWeak 1 []).

Definition hi_item__nl_C_LC_MONETARY : item :=
  (IData (a "_nl_C_LC_MONETARY") LExternWeak 1 []).

Definition hi_item__nl_C_LC_NAME : item :=
  (IData (a "_nl_C_LC_NAME") LExternWeak 1 []).

Definition hi_item__nl_C_LC_NUMERIC : item :=
  (IData (a "_nl_C_LC_NUMERIC") LExternWeak 1 []).

Definition hi_item__nl_C_LC_PAPER : item :=
  (IData (a "_nl_C_LC_PAPER") LExternWeak 1 []).

Definition hi_item__nl_C_LC_TELEPHONE : item :=
  (IData (a "_nl_C_LC_TELEPHONE") LExternWeak 1 []).

Definition hi_item__nl_C_LC_TIME : item :=
  (IData (a "_nl_C_LC_TIME") LExternWeak 1 []).

Definition hi_item__nl_C_LC_CTYPE : item :=
  (IData (a "_nl_C_LC_CTYPE") (LRo (a "export")) 8 (app [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Sym (a "glibc_C_ctype#lc_ctype_data") 0); (Item Ww 4294967295); (Item Ww 1); (Item Ww 86); (Zero 4); (Sym (a "_nl_C_LC_CTYPE_class") 0); (Sym (a "_nl_C_LC_CTYPE_toupper") 0); (Item Wl 0); (Sym (a "_nl_C_LC_CTYPE_tolower") 0); (Item Wl 0); (Sym (a "_nl_C_LC_CTYPE_class32") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "glibc_C_ctype#str.258") 0); (Sym (a "glibc_C_ctype#str.259") 0); (Sym (a "_nl_C_LC_CTYPE_width") 0); (Item Ww 1); (Zero 4); (Sym (a "_nl_C_codeset") 0); (Sym (a "_nl_C_LC_CTYPE_toupper") 512); (Sym (a "_nl_C_LC_CTYPE_tolower") 512); (Item Ww 72); (Zero 4); (Item Ww 84); (Zero 4); (Item Ww 1); (Zero 4); (Sym (a "glibc_C_ctype#str.260") 0); (Sym (a "glibc_C_ctype#str.261") 0); (Sym (a "glibc_C_ctype#str.262") 0); (Sym (a "glibc_C_ctype#str.263") 0); (Sym (a "glibc_C_ctype#str.264") 0); (Sym (a "glibc_C_ctype#str.265") 0); (Sym (a "glibc_C_ctype#str.266") 0); (Sym (a "glibc_C_ctype#str.267") 0); (Sym (a "glibc_C_ctype#str.268") 0); (Sym (a "glibc_C_ctype#str.269") 0); (Item Ww 1); (Zero 4); (Sym (a "glibc_C_ctype#str.270") 0); (Sym (a "glibc_C_ctype#str.271") 0); (Sym (a "glibc_C_ctype#str.272") 0); (Sym (a "glibc_C_ctype#str.273") 0); (Sym (a "glibc_C_ctype#str.274") 0); (Sym (a "glibc_C_ctype#str.275") 0); (Sym (a "glibc_C_ctype#str.276") 0); (Sym (a "glibc_C_ctype#str.277") 0); (Sym (a "glibc_C_ctype#str.278") 0); (Sym (a "glibc_C_ctype#str.279") 0); (Sym (a "glibc_C_ctype#str.260") 0); (Sym (a "glibc_C_ctype#str.261") 0)] [(Sym (a "glibc_C_ctype#str.262") 0); (Sym (a "glibc_C_ctype#str.263") 0); (Sym (a "glibc_C_ctype#str.264") 0); (Sym (a "glibc_C_ctype#str.265") 0); (Sym (a "glibc_C_ctype#str.266") 0); (Sym (a "glibc_C_ctype#str.267") 0); (Sym (a "glibc_C_ctype#str.268") 0); (Sym (a "glibc_C_ctype#str.269") 0); (Item Ww 48); (Zero 4); (Item Ww 49); (Zero 4); (Item Ww 50); (Zero 4); (Item Ww 51); (Zero 4); (Item Ww 52); (Zero 4); (Item Ww 53); (Zero 4); (Item Ww 54); (Zero 4); (Item Ww 55); (Zero 4); (Item Ww 56); (Zero 4); (Item Ww 57); (Zero 4); (Item Ww 1659); (Zero 4); (Sym (a "glibc_C_ctype#translit_from_idx") 0); (Sym (a "glibc_C_ctype#translit_from_tbl") 0); (Sym (a "glibc_C_ctype#translit_to_idx") 0); (Sym (a "glibc_C_ctype#translit_to_tbl") 0); (Item Ww 1); (Zero 4); (Sym (a "glibc_C_ctype#str.280") 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Ww 0); (Zero 4); (Sym (a "_nl_C_LC_CTYPE_class_upper") 32); (Sym (a "_nl_C_LC_CTYPE_class_lower") 32); (Sym (a "_nl_C_LC_CTYPE_class_alpha") 32); (Sym (a "_nl_C_LC_CTYPE_class_digit") 32); (Sym (a "_nl_C_LC_CTYPE_class_xdigit") 32); (Sym (a "_nl_C_LC_CTYPE_class_space") 32); (Sym (a "_nl_C_LC_CTYPE_class_print") 32); (Sym (a "_nl_C_LC_CTYPE_class_graph") 32); (Sym (a "_nl_C_LC_CTYPE_class_blank") 32); (Sym (a "_nl_C_LC_CTYPE_class_cntrl") 32); (Sym (a "_nl_C_LC_CTYPE_class_punct") 32); (Sym (a "_nl_C_LC_CTYPE_class_alnum") 32); (Sym (a "_nl_C_LC_CTYPE_map_toupper") 0); (Sym (a "_nl_C_LC_CTYPE_map_tolower") 0)])).

Definition hi_item__nl_C_LC_CTYPE_class : item :=
  (IData (a "_nl_C_LC_CTYPE_class") (LRo (a "export")) 2 [(Str (app (app (app (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) (app (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 3; 32; 2; 32; 2; 32; 2; 32; 2; 32; 2; 0; 2; 0]) (app [2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 2; 0; 1; 96; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192] [4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 8; 216; 8; 216; 8; 216; 8; 216; 8; 216; 8; 216; 8; 216; 8; 216; 8; 216; 8; 216; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192]))) (app (app (app [4; 192; 8; 213; 8; 213; 8; 213; 8; 213; 8; 213; 8; 213; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197; 8; 197] [8; 197; 8; 197; 8; 197; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 4; 192; 8; 214; 8; 214; 8; 214; 8; 214; 8; 214; 8; 214; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198]) (app [8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 8; 198; 4; 192; 4; 192; 4; 192; 4; 192; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) (app (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])))))]).

Definition hi_item__nl_C_LC_CTYPE_class32 : item :=
  (IData (a "_nl_C_LC_CTYPE_class32") (LRo (a "export")) 4 [(Str (app (app (app (app [0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 3; 32; 0; 0; 2; 32; 0; 0; 2; 32; 0; 0; 2; 32; 0; 0; 2; 32; 0; 0; 2; 0; 0; 0; 2; 0] [0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0; 0; 0; 2; 0]) (app [0; 0; 1; 96; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192] [0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 8; 216; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192])) (app (app [0; 0; 4; 192; 0; 0; 8; 213; 0; 0; 8; 213; 0; 0; 8; 213; 0; 0; 8; 213; 0; 0; 8; 213; 0; 0; 8; 213; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197] [0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 8; 197; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192]) (app [0; 0; 4; 192; 0; 0; 8; 214; 0; 0; 8; 214; 0; 0; 8; 214; 0; 0; 8; 214; 0; 0; 8; 214; 0; 0; 8; 214; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198] [0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 8; 198; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 4; 192; 0; 0; 2; 0]))) (app (app (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) (app (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) (app [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])))))]).

Definition hi_item__nl_C_LC_CTYPE_class_alnum : item :=
  (IData (a "_nl_C_LC_CTYPE_class_alnum") (LRo (a "export")) 4 [(Str [0; 0; 0; 0; 0; 0; 255; 3; 254; 255; 255; 7; 254; 255; 255; 7; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [7; 0; 0; 0; 1; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0]); (Item Ww 24); (Item Ww 28); (Str [0; 0; 0; 0; 0; 0; 255; 3; 254; 255; 255; 7; 254; 255; 255; 7])]).

Definition hi_item__nl_C_LC_CTYPE_class_alpha : item :=
  (IData (a "_nl_C_LC_CTYPE_class_alpha") (LRo (a "export")) 4 [(Str [0; 0; 0; 0; 0; 0; 0; 0; 254; 255; 255; 7; 254; 255; 255; 7; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [7; 0; 0; 0; 1; 0; 0; 0; 6; 0; 0; 0; 1; 0; 0; 0; 1; 0; 0; 0]); (Item Ww 24); (Item Ww 0); (Item Ww 32); (Str [254; 255; 255; 7; 254; 255; 255; 7])]).

Definition hi_item__nl_C_LC_CTYPE_class_blank : item :=
  (IData (a "_nl_C_LC_CTYPE_class_blank") (LRo (a "export")) 4 [(Str [0; 2; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [6; 0; 0; 0; 1; 0; 0; 0; 6; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]); (Item Ww 24); (Item Ww 28); (Str [0; 2; 0; 0; 1; 0; 0; 0])]).

Definition hi_item__nl_C_LC_CTYPE_class_cntrl : item :=
  (IData (a "_nl_C_LC_CTYPE_class_cntrl") (LRo (a "export")) 4 [(Str [255; 255; 255; 255; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [7; 0; 0; 0; 1; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0]); (Item Ww 24); (Item Ww 28); (Str [255; 255; 255; 255; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128])]).

Definition hi_item__nl_C_LC_CTYPE_class_digit : item :=
  (IData (a "_nl_C_LC_CTYPE_class_digit") (LRo (a "export")) 4 [(Str [0; 0; 0; 0; 0; 0; 255; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [6; 0; 0; 0; 1; 0; 0; 0; 6; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]); (Item Ww 24); (Item Ww 28); (Str [0; 0; 0; 0; 0; 0; 255; 3])]).

Definition hi_item__nl_C_LC_CTYPE_class_graph : item :=
  (IData (a "_nl_C_LC_CTYPE_class_graph") (LRo (a "export")) 4 [(Str [0; 0; 0; 0; 254; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 127; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [7; 0; 0; 0; 1; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0]); (Item Ww 24); (Item Ww 28); (Str [0; 0; 0; 0; 254; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 127])]).

Definition hi_item__nl_C_LC_CTYPE_class_lower : item :=
  (IData (a "_nl_C_LC_CTYPE_class_lower") (LRo (a "export")) 4 [(Str [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 254; 255; 255; 7; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [7; 0; 0; 0; 1; 0; 0; 0; 6; 0; 0; 0; 1; 0; 0; 0; 1; 0; 0; 0]); (Item Ww 24); (Item Ww 0); (Item Ww 32); (Str [0; 0; 0; 0; 254; 255; 255; 7])]).

Definition hi_item__nl_C_LC_CTYPE_class_print : item :=
  (IData (a "_nl_C_LC_CTYPE_class_print") (LRo (a "export")) 4 [(Str [0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 127; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [7; 0; 0; 0; 1; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0]); (Item Ww 24); (Item Ww 28); (Str [0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 127])]).

Definition hi_item__nl_C_LC_CTYPE_class_punct : item :=
  (IData (a "_nl_C_LC_CTYPE_class_punct") (LRo (a "export")) 4 [(Str [0; 0; 0; 0; 254; 255; 0; 252; 1; 0; 0; 248; 1; 0; 0; 120; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]); (Str [7; 0; 0; 0; 1; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0]); (Item Ww 24); (Item Ww 28); (Str [0; 0; 0; 0; 254; 255; 0; 252; 1; 0; 0; 248; 1; 0; 0; 120])]).

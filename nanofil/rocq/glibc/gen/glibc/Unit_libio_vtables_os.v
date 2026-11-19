(** This file defines checked IR from glibc’s `libio/vtables.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item_IO_accept_foreign_vtables : item :=
  (IData (a "IO_accept_foreign_vtables") LExport 8 [(Zero 8)]).

Definition fn__IO_vtable_check : func :=
  ir_fn{ "export" "_IO_vtable_check"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_vtables#str.302";
    call void $"__GI___libc_fatal"(P %"v0")
    => ret void
} }.

Definition item___io_vtables : item :=
  (IData (a "__io_vtables") (LRo (a "export")) 8 (app (app (app [(Item Wl 0); (Item Wl 0); (Sym (a "_IO_str_finish") 0); (Sym (a "__GI__IO_str_overflow") 0); (Sym (a "__GI__IO_str_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_str_pbackfail") 0); (Sym (a "__GI__IO_default_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "__GI__IO_str_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_default_setbuf") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "__GI__IO_default_doallocate") 0); (Sym (a "_IO_default_read") 0); (Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_wstr_finish") 0); (Sym (a "_IO_wstr_overflow") 0); (Sym (a "_IO_wstr_underflow") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "_IO_wstr_pbackfail") 0); (Sym (a "__GI__IO_wdefault_xsputn") 0); (Sym (a "__GI__IO_wdefault_xsgetn") 0); (Sym (a "_IO_wstr_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_default_setbuf") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "__GI__IO_wdefault_doallocate") 0); (Sym (a "_IO_default_read") 0)] [(Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "__GI__IO_file_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "__GI__IO_file_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "_IO_new_file_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_new_file_setbuf") 0); (Sym (a "_IO_new_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "_IO_file_underflow_mmap") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "_IO_new_file_xsputn") 0); (Sym (a "_IO_file_xsgetn_mmap") 0); (Sym (a "_IO_file_seekoff_mmap") 0)]) (app [(Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "_IO_file_sync_mmap") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "_IO_file_close_mmap") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "_IO_file_underflow_maybe_mmap") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "_IO_new_file_xsputn") 0); (Sym (a "_IO_file_xsgetn_maybe_mmap") 0); (Sym (a "_IO_file_seekoff_maybe_mmap") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "_IO_new_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "__GI__IO_wfile_overflow") 0); (Sym (a "__GI__IO_wfile_underflow") 0)] [(Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "__GI__IO_wdefault_pbackfail") 0); (Sym (a "__GI__IO_wfile_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "__GI__IO_wfile_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_new_file_setbuf") 0); (Sym (a "__GI__IO_wfile_sync") 0); (Sym (a "_IO_wfile_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "__GI__IO_wfile_overflow") 0); (Sym (a "_IO_wfile_underflow_mmap") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "__GI__IO_wdefault_pbackfail") 0); (Sym (a "__GI__IO_wfile_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "__GI__IO_wfile_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "__GI__IO_wfile_sync") 0); (Sym (a "_IO_wfile_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "_IO_file_close_mmap") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0)])) (app (app [(Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "__GI__IO_wfile_overflow") 0); (Sym (a "_IO_wfile_underflow_maybe_mmap") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "__GI__IO_wdefault_pbackfail") 0); (Sym (a "__GI__IO_wfile_xsputn") 0); (Sym (a "__GI__IO_file_xsgetn") 0); (Sym (a "__GI__IO_wfile_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_file_setbuf_mmap") 0); (Sym (a "__GI__IO_wfile_sync") 0); (Sym (a "_IO_wfile_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "__GI__IO_file_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "__GI__IO_file_finish") 0); (Sym (a "__GI__IO_file_overflow") 0); (Sym (a "__GI__IO_file_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "__GI__IO_file_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "_IO_cookie_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "__GI__IO_file_setbuf") 0); (Sym (a "__GI__IO_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "_IO_cookie_read") 0)] [(Sym (a "_IO_cookie_write") 0); (Sym (a "_IO_cookie_seek") 0); (Sym (a "_IO_cookie_close") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_new_file_finish") 0); (Sym (a "_IO_new_file_overflow") 0); (Sym (a "_IO_new_file_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_default_pbackfail") 0); (Sym (a "_IO_new_file_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "_IO_new_file_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_new_file_setbuf") 0); (Sym (a "_IO_new_file_sync") 0); (Sym (a "__GI__IO_file_doallocate") 0); (Sym (a "__GI__IO_file_read") 0); (Sym (a "_IO_new_file_write") 0); (Sym (a "__GI__IO_file_seek") 0); (Sym (a "_IO_new_proc_close") 0); (Sym (a "__GI__IO_file_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_mem_finish") 0); (Sym (a "__GI__IO_str_overflow") 0); (Sym (a "__GI__IO_str_underflow") 0); (Sym (a "__GI__IO_default_uflow") 0); (Sym (a "__GI__IO_str_pbackfail") 0); (Sym (a "__GI__IO_default_xsputn") 0); (Sym (a "__GI__IO_default_xsgetn") 0); (Sym (a "__GI__IO_str_seekoff") 0)]) (app [(Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_mem_setbuf") 0); (Sym (a "_IO_mem_sync") 0); (Sym (a "_IO_mem_doallocate") 0); (Sym (a "_IO_default_read") 0); (Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Sym (a "_IO_wmem_finish") 0); (Sym (a "_IO_wstr_overflow") 0); (Sym (a "_IO_wstr_underflow") 0); (Sym (a "__GI__IO_wdefault_uflow") 0); (Sym (a "_IO_wstr_pbackfail") 0); (Sym (a "__GI__IO_wdefault_xsputn") 0); (Sym (a "__GI__IO_wdefault_xsgetn") 0); (Sym (a "_IO_wstr_seekoff") 0); (Sym (a "_IO_default_seekpos") 0); (Sym (a "_IO_wmem_setbuf") 0); (Sym (a "_IO_wmem_sync") 0); (Sym (a "_IO_wmem_doallocate") 0); (Sym (a "_IO_default_read") 0); (Sym (a "_IO_default_write") 0); (Sym (a "_IO_default_seek") 0); (Sym (a "_IO_default_sync") 0); (Sym (a "_IO_default_stat") 0); (Sym (a "_IO_default_showmanyc") 0); (Sym (a "_IO_default_imbue") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "__printf_buffer_as_file_overflow") 0); (Item Wl 0)] [(Item Wl 0); (Item Wl 0); (Sym (a "__printf_buffer_as_file_xsputn") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "__wprintf_buffer_as_file_overflow") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Sym (a "__wprintf_buffer_as_file_xsputn") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0)])))).

Definition item___nanofil_ctor_check_stdfiles_vtables : item :=
  (IData (a "__nanofil_ctor_check_stdfiles_vtables") (LInit (a "ctor") (a "none")) 8 [(Sym (a "glibc_vtables#check_stdfiles_vtables") 0)]).

Definition fn_glibc_vtables'23check_stdfiles_vtables : func :=
  ir_fn{ "local" "glibc_vtables#check_stdfiles_vtables"() -> RVoid {
  @"start":
    %"v3" : P = Copy $"_IO_2_1_stdin_";
    %"v4" = %"v3" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v6" : P = Copy $"__io_vtables";
    %"v7" = %"v6" +p #336;
    %"v8" : L = Ptoi %"v5";
    %"v9" : L = Ptoi %"v7";
    %"v10" : W = (Cmp Ne L) %"v8", %"v9"
    => br %"v10" ? "L12" : "L11";
  @"L11":
    %"v13" : P = Copy $"_IO_2_1_stdout_";
    %"v14" = %"v13" +p #216;
    %"chk1" : A = (Check 0 8 Read 8) %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" : P = Copy $"__io_vtables";
    %"v17" = %"v16" +p #336;
    %"v18" : L = Ptoi %"v15";
    %"v19" : L = Ptoi %"v17";
    %"v20" : W = (Cmp Ne L) %"v18", %"v19"
    => goto "L12";
  @"L12" [%"v22" : W = phi("start" => #1, "L11" => %"v20")]:
    => br %"v22" ? "L24" : "L23";
  @"L23":
    %"v25" : P = Copy $"_IO_2_1_stderr_";
    %"v26" = %"v25" +p #216;
    %"chk2" : A = (Check 0 8 Read 8) %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v28" : P = Copy $"__io_vtables";
    %"v29" = %"v28" +p #336;
    %"v30" : L = Ptoi %"v27";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => goto "L24";
  @"L24" [%"v34" : W = phi("L12" => #1, "L23" => %"v32")]:
    => br %"v34" ? "L0" : "L2";
  @"L0":
    %"v35" : P = Copy $"_IO_vtable_check";
    %"iw_1.v6" : P = Copy $"IO_accept_foreign_vtables";
    %"chk3" : A = (Check 0 8 Write 8) %"iw_1.v6";
    (RawStorePointer 0 (t "v35") (t "chk3") [AtomicWrite])
    => goto "L2";
  @"L2":
    => ret void
} }.

Definition item_glibc_vtables'23str'2e302 : item :=
  (IData (a "glibc_vtables#str.302") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 100); (Item Wb 105); (Item Wb 111); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 10); (Item Wb 0)]).

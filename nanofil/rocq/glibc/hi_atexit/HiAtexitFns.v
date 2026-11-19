From Glibc Require Import Unit_io_close_nocancel_os Unit_io_fstat64_os Unit_io_lseek64_os Unit_io_write_nocancel_os Unit_io_write_os.
From Glibc Require Import Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import Unit_libio_iofclose_os Unit_libio_ioputs_os Unit_libio_stdfiles_os Unit_misc_makedev_os Unit_nptl_libcZ2dcleanup_os.
From Glibc Require Import Unit_posix__exit_os Unit_stdlib_cxa_thread_atexit_impl_os Unit_stdlib_exit_os Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram.
(** The proofs of glibc's functions were made over small fixtures,
    one group of functions at a time. To use them for the whole linked
    program, each function the program calls must be the same function
    there. This file shows that it is: hi_atexit/code.sh links every
    unit under the object name its fixture uses, so a call of each name
    in the linked program runs the function its fixture defines, and
    each lemma below is checked by computation.

    The genv [hi_ge] is the linked module with its globals and any free
    function the runtime supplies. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics.
From Glibc Require Import HiAtexitModule StrlenLogic AllocLogic AtexitLogic.
Open Scope string_scope.

Section fns.
(** The runtime's free, which the genv carries. *)
Variable fre : word -> mem -> option (res unit * mem).

(** The genv of the linked module, its symbols laid out. *)
Definition hi_ge : genv := mkGenv hi_module hi_globals fre.

(** A call of `__fpending` runs [Unit_libio___fpending_os.fn___fpending]. *)
Definition HiAtexitFns_hi_ge_program_table : list (string * func) :=
  ("__fpending", Unit_libio___fpending_os.fn___fpending) ::
  ("_IO_ferror", Unit_libio_ferror_os.fn__IO_ferror) ::
  ("ferror", Unit_libio_ferror_os.fn__IO_ferror) ::
  ("__GI__IO_file_doallocate", Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate) ::
  ("_IO_file_close_maybe_unlink", Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink) ::
  ("_IO_new_file_finish", Unit_libio_fileops_os.fn__IO_new_file_finish) ::
  ("_IO_new_do_write", Unit_libio_fileops_os.fn__IO_new_do_write) ::
  ("_IO_new_file_overflow", Unit_libio_fileops_os.fn__IO_new_file_overflow) ::
  ("__GI__IO_file_stat", Unit_libio_fileops_os.fn___GI__IO_file_stat) ::
  ("__GI__IO_file_close", Unit_libio_fileops_os.fn___GI__IO_file_close) ::
  ("_IO_new_file_write", Unit_libio_fileops_os.fn__IO_new_file_write) ::
  ("_IO_new_file_xsputn", Unit_libio_fileops_os.fn__IO_new_file_xsputn) ::
  ("__GI__IO_un_link", Unit_libio_genops_os.fn___GI__IO_un_link) ::
  ("__GI___overflow", Unit_libio_genops_os.fn___GI___overflow) ::
  ("__GI__IO_setb", Unit_libio_genops_os.fn___GI__IO_setb) ::
  ("__GI__IO_doallocbuf", Unit_libio_genops_os.fn___GI__IO_doallocbuf) ::
  ("__GI__IO_default_xsputn", Unit_libio_genops_os.fn___GI__IO_default_xsputn) ::
  ("__GI__IO_default_finish", Unit_libio_genops_os.fn___GI__IO_default_finish) ::
  ("__GI__IO_flush_all", Unit_libio_genops_os.fn___GI__IO_flush_all) ::
  ("_IO_cleanup", Unit_libio_genops_os.fn__IO_cleanup) ::
  ("__GI__IO_unsave_markers", Unit_libio_genops_os.fn___GI__IO_unsave_markers) ::
  ("_IO_new_fclose", Unit_libio_iofclose_os.fn__IO_new_fclose) ::
  ("fclose", Unit_libio_iofclose_os.fn__IO_new_fclose) ::
  ("__GI__IO_puts", Unit_libio_ioputs_os.fn___GI__IO_puts) ::
  ("puts", Unit_libio_ioputs_os.fn___GI__IO_puts) ::
  ("glibc_stdfiles#_IO_stdfiles_init", Unit_libio_stdfiles_os.fn_glibc_stdfiles'23_IO_stdfiles_init) ::
  ("__isatty_nostatus", Unit_termios_isatty_nostatus_os.fn___isatty_nostatus) ::
  ("__GI___libc_write", Unit_io_write_os.fn___GI___libc_write) ::
  ("__GI___write", Unit_io_write_os.fn___GI___libc_write) ::
  ("__GI___write_nocancel", Unit_io_write_nocancel_os.fn___GI___write_nocancel) ::
  ("__lseek64", Unit_io_lseek64_os.fn___lseek64) ::
  ("__GI___fstat64", Unit_io_fstat64_os.fn___GI___fstat64) ::
  ("__GI___close_nocancel", Unit_io_close_nocancel_os.fn___GI___close_nocancel) ::
  ("__GI__exit", Unit_posix__exit_os.fn___GI__exit) ::
  ("_exit", Unit_posix__exit_os.fn___GI__exit) ::
  ("__run_exit_handlers", Unit_stdlib_exit_os.fn___run_exit_handlers) ::
  ("__GI_exit", Unit_stdlib_exit_os.fn___GI_exit) ::
  ("exit", Unit_stdlib_exit_os.fn___GI_exit) ::
  ("__GI___call_tls_dtors", Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors) ::
  ("__GI___libc_cleanup_push_defer", Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer) ::
  ("__GI___libc_cleanup_pop_restore", Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore) ::
  ("__gnu_dev_major", Unit_misc_makedev_os.fn___gnu_dev_major) ::
  ("__GI_strlen", glibc_strlen) ::
  ("__GI___mempcpy", Unit_string_mempcpy_os.fn___GI___mempcpy) ::
  ("__GI_mempcpy", Unit_string_mempcpy_os.fn___GI___mempcpy) ::
  ("__GI_memcpy", Unit_string_memcpy_os.fn___GI_memcpy) ::
  ("__GI___libc_malloc", malloc_fn) ::
  ("malloc", malloc_fn) ::
  ("glibc_malloc#__libc_malloc2", malloc2_fn) ::
  ("__GI___libc_free", free_fn) ::
  ("free", free_fn) ::
  ("__new_exitfn", new_exitfn_fn) ::
  ("__internal_atexit", internal_atexit_fn) ::
  ("__cxa_atexit", cxa_atexit_fn) ::
  ("atexit", atexit_fn) :: nil.
Lemma HiAtexitFns_hi_ge_program_table_correct :
  List.Forall (fun '(n, f) => find_fn hi_ge (TAtom n) = Some (Defined f)) HiAtexitFns_hi_ge_program_table.
Proof using Type.
  apply defines_table_of_map.
  vm_cast_no_check (eq_refl (List.map (fun '(_, f) => Some (Defined f)) HiAtexitFns_hi_ge_program_table)).
Qed.
#[global] Instance HiAtexitFns_hi_ge_program_table_instance : ProgramTable hi_ge :=
  {| program_table := HiAtexitFns_hi_ge_program_table; program_table_correct := HiAtexitFns_hi_ge_program_table_correct |}.
Lemma hi_find___fpending : Defines hi_ge "__fpending" Unit_libio___fpending_os.fn___fpending.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 0 "__fpending" Unit_libio___fpending_os.fn___fpending HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___fpending.

(** A call of `_IO_ferror` runs [Unit_libio_ferror_os.fn__IO_ferror]. *)
Lemma hi_find__IO_ferror : Defines hi_ge "_IO_ferror" Unit_libio_ferror_os.fn__IO_ferror.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 1 "_IO_ferror" Unit_libio_ferror_os.fn__IO_ferror HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_ferror.

(** A call of `ferror` runs [Unit_libio_ferror_os.fn__IO_ferror]. *)
Lemma hi_find_ferror : Defines hi_ge "ferror" Unit_libio_ferror_os.fn__IO_ferror.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 2 "ferror" Unit_libio_ferror_os.fn__IO_ferror HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_ferror.

(** A call of `__GI__IO_file_doallocate` runs [Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate]. *)
Lemma hi_find___GI__IO_file_doallocate : Defines hi_ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 3 "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_file_doallocate.

(** A call of `_IO_file_close_maybe_unlink` runs [Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink]. *)
Lemma hi_find__IO_file_close_maybe_unlink : Defines hi_ge "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 4 "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_file_close_maybe_unlink.

(** A call of `_IO_new_file_finish` runs [Unit_libio_fileops_os.fn__IO_new_file_finish]. *)
Lemma hi_find__IO_new_file_finish : Defines hi_ge "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 5 "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_finish.

(** A call of `_IO_new_do_write` runs [Unit_libio_fileops_os.fn__IO_new_do_write]. *)
Lemma hi_find__IO_new_do_write : Defines hi_ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 6 "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_do_write.

(** A call of `_IO_new_file_overflow` runs [Unit_libio_fileops_os.fn__IO_new_file_overflow]. *)
Lemma hi_find__IO_new_file_overflow : Defines hi_ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 7 "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_overflow.

(** A call of `__GI__IO_file_stat` runs [Unit_libio_fileops_os.fn___GI__IO_file_stat]. *)
Lemma hi_find___GI__IO_file_stat : Defines hi_ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 8 "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_file_stat.

(** A call of `__GI__IO_file_close` runs [Unit_libio_fileops_os.fn___GI__IO_file_close]. *)
Lemma hi_find___GI__IO_file_close : Defines hi_ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 9 "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_file_close.

(** A call of `_IO_new_file_write` runs [Unit_libio_fileops_os.fn__IO_new_file_write]. *)
Lemma hi_find__IO_new_file_write : Defines hi_ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 10 "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_write.

(** A call of `_IO_new_file_xsputn` runs [Unit_libio_fileops_os.fn__IO_new_file_xsputn]. *)
Lemma hi_find__IO_new_file_xsputn : Defines hi_ge "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 11 "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_xsputn.

(** A call of `__GI__IO_un_link` runs [Unit_libio_genops_os.fn___GI__IO_un_link]. *)
Lemma hi_find___GI__IO_un_link : Defines hi_ge "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 12 "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_un_link.

(** A call of `__GI___overflow` runs [Unit_libio_genops_os.fn___GI___overflow]. *)
Lemma hi_find___GI___overflow : Defines hi_ge "__GI___overflow" Unit_libio_genops_os.fn___GI___overflow.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 13 "__GI___overflow" Unit_libio_genops_os.fn___GI___overflow HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___overflow.

(** A call of `__GI__IO_setb` runs [Unit_libio_genops_os.fn___GI__IO_setb]. *)
Lemma hi_find___GI__IO_setb : Defines hi_ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 14 "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_setb.

(** A call of `__GI__IO_doallocbuf` runs [Unit_libio_genops_os.fn___GI__IO_doallocbuf]. *)
Lemma hi_find___GI__IO_doallocbuf : Defines hi_ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 15 "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_doallocbuf.

(** A call of `__GI__IO_default_xsputn` runs [Unit_libio_genops_os.fn___GI__IO_default_xsputn]. *)
Lemma hi_find___GI__IO_default_xsputn : Defines hi_ge "__GI__IO_default_xsputn" Unit_libio_genops_os.fn___GI__IO_default_xsputn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 16 "__GI__IO_default_xsputn" Unit_libio_genops_os.fn___GI__IO_default_xsputn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_default_xsputn.

(** A call of `__GI__IO_default_finish` runs [Unit_libio_genops_os.fn___GI__IO_default_finish]. *)
Lemma hi_find___GI__IO_default_finish : Defines hi_ge "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 17 "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_default_finish.

(** A call of `__GI__IO_flush_all` runs [Unit_libio_genops_os.fn___GI__IO_flush_all]. *)
Lemma hi_find___GI__IO_flush_all : Defines hi_ge "__GI__IO_flush_all" Unit_libio_genops_os.fn___GI__IO_flush_all.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 18 "__GI__IO_flush_all" Unit_libio_genops_os.fn___GI__IO_flush_all HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_flush_all.

(** A call of `_IO_cleanup` runs [Unit_libio_genops_os.fn__IO_cleanup]. *)
Lemma hi_find__IO_cleanup : Defines hi_ge "_IO_cleanup" Unit_libio_genops_os.fn__IO_cleanup.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 19 "_IO_cleanup" Unit_libio_genops_os.fn__IO_cleanup HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_cleanup.

(** A call of `__GI__IO_unsave_markers` runs [Unit_libio_genops_os.fn___GI__IO_unsave_markers]. *)
Lemma hi_find___GI__IO_unsave_markers : Defines hi_ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 20 "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_unsave_markers.

(** A call of `_IO_new_fclose` runs [Unit_libio_iofclose_os.fn__IO_new_fclose]. *)
Lemma hi_find__IO_new_fclose : Defines hi_ge "_IO_new_fclose" Unit_libio_iofclose_os.fn__IO_new_fclose.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 21 "_IO_new_fclose" Unit_libio_iofclose_os.fn__IO_new_fclose HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_fclose.

(** A call of `fclose` runs [Unit_libio_iofclose_os.fn__IO_new_fclose]. *)
Lemma hi_find_fclose : Defines hi_ge "fclose" Unit_libio_iofclose_os.fn__IO_new_fclose.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 22 "fclose" Unit_libio_iofclose_os.fn__IO_new_fclose HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_fclose.

(** A call of `__GI__IO_puts` runs [Unit_libio_ioputs_os.fn___GI__IO_puts]. *)
Lemma hi_find___GI__IO_puts : Defines hi_ge "__GI__IO_puts" Unit_libio_ioputs_os.fn___GI__IO_puts.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 23 "__GI__IO_puts" Unit_libio_ioputs_os.fn___GI__IO_puts HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_puts.

(** A call of `puts` runs [Unit_libio_ioputs_os.fn___GI__IO_puts]. *)
Lemma hi_find_puts : Defines hi_ge "puts" Unit_libio_ioputs_os.fn___GI__IO_puts.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 24 "puts" Unit_libio_ioputs_os.fn___GI__IO_puts HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_puts.

(** A call of `glibc_stdfiles#_IO_stdfiles_init` runs [Unit_libio_stdfiles_os.fn_glibc_stdfiles'23_IO_stdfiles_init]. *)
Lemma hi_find_glibc_stdfiles__IO_stdfiles_init : Defines hi_ge "glibc_stdfiles#_IO_stdfiles_init" Unit_libio_stdfiles_os.fn_glibc_stdfiles'23_IO_stdfiles_init.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 25 "glibc_stdfiles#_IO_stdfiles_init" Unit_libio_stdfiles_os.fn_glibc_stdfiles'23_IO_stdfiles_init HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_glibc_stdfiles__IO_stdfiles_init.

(** A call of `__isatty_nostatus` runs [Unit_termios_isatty_nostatus_os.fn___isatty_nostatus]. *)
Lemma hi_find___isatty_nostatus : Defines hi_ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 26 "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___isatty_nostatus.

(** A call of `__GI___libc_write` runs [Unit_io_write_os.fn___GI___libc_write]. *)
Lemma hi_find___GI___libc_write : Defines hi_ge "__GI___libc_write" Unit_io_write_os.fn___GI___libc_write.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 27 "__GI___libc_write" Unit_io_write_os.fn___GI___libc_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_write.

(** A call of `__GI___write` runs [Unit_io_write_os.fn___GI___libc_write]. *)
Lemma hi_find___GI___write : Defines hi_ge "__GI___write" Unit_io_write_os.fn___GI___libc_write.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 28 "__GI___write" Unit_io_write_os.fn___GI___libc_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___write.

(** A call of `__GI___write_nocancel` runs [Unit_io_write_nocancel_os.fn___GI___write_nocancel]. *)
Lemma hi_find___GI___write_nocancel : Defines hi_ge "__GI___write_nocancel" Unit_io_write_nocancel_os.fn___GI___write_nocancel.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 29 "__GI___write_nocancel" Unit_io_write_nocancel_os.fn___GI___write_nocancel HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___write_nocancel.

(** A call of `__lseek64` runs [Unit_io_lseek64_os.fn___lseek64]. *)
Lemma hi_find___lseek64 : Defines hi_ge "__lseek64" Unit_io_lseek64_os.fn___lseek64.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 30 "__lseek64" Unit_io_lseek64_os.fn___lseek64 HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___lseek64.

(** A call of `__GI___fstat64` runs [Unit_io_fstat64_os.fn___GI___fstat64]. *)
Lemma hi_find___GI___fstat64 : Defines hi_ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 31 "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64 HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___fstat64.

(** A call of `__GI___close_nocancel` runs [Unit_io_close_nocancel_os.fn___GI___close_nocancel]. *)
Lemma hi_find___GI___close_nocancel : Defines hi_ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 32 "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___close_nocancel.

(** A call of `__GI__exit` runs [Unit_posix__exit_os.fn___GI__exit]. *)
Lemma hi_find___GI__exit : Defines hi_ge "__GI__exit" Unit_posix__exit_os.fn___GI__exit.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 33 "__GI__exit" Unit_posix__exit_os.fn___GI__exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__exit.

(** A call of `_exit` runs [Unit_posix__exit_os.fn___GI__exit]. *)
Lemma hi_find__exit : Defines hi_ge "_exit" Unit_posix__exit_os.fn___GI__exit.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 34 "_exit" Unit_posix__exit_os.fn___GI__exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__exit.

(** A call of `__run_exit_handlers` runs [Unit_stdlib_exit_os.fn___run_exit_handlers]. *)
Lemma hi_find___run_exit_handlers : Defines hi_ge "__run_exit_handlers" Unit_stdlib_exit_os.fn___run_exit_handlers.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 35 "__run_exit_handlers" Unit_stdlib_exit_os.fn___run_exit_handlers HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___run_exit_handlers.

(** A call of `__GI_exit` runs [Unit_stdlib_exit_os.fn___GI_exit]. *)
Lemma hi_find___GI_exit : Defines hi_ge "__GI_exit" Unit_stdlib_exit_os.fn___GI_exit.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 36 "__GI_exit" Unit_stdlib_exit_os.fn___GI_exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_exit.

(** A call of `exit` runs [Unit_stdlib_exit_os.fn___GI_exit]. *)
Lemma hi_find_exit : Defines hi_ge "exit" Unit_stdlib_exit_os.fn___GI_exit.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 37 "exit" Unit_stdlib_exit_os.fn___GI_exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_exit.

(** A call of `__GI___call_tls_dtors` runs [Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors]. *)
Lemma hi_find___GI___call_tls_dtors : Defines hi_ge "__GI___call_tls_dtors" Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 38 "__GI___call_tls_dtors" Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___call_tls_dtors.

(** A call of `__GI___libc_cleanup_push_defer` runs [Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer]. *)
Lemma hi_find___GI___libc_cleanup_push_defer : Defines hi_ge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 39 "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_cleanup_push_defer.

(** A call of `__GI___libc_cleanup_pop_restore` runs [Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore]. *)
Lemma hi_find___GI___libc_cleanup_pop_restore : Defines hi_ge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 40 "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_cleanup_pop_restore.

(** A call of `__gnu_dev_major` runs [Unit_misc_makedev_os.fn___gnu_dev_major]. *)
Lemma hi_find___gnu_dev_major : Defines hi_ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 41 "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___gnu_dev_major.

(** A call of `__GI_strlen` runs [glibc_strlen]. *)
Lemma hi_find___GI_strlen : Defines hi_ge "__GI_strlen" glibc_strlen.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 42 "__GI_strlen" glibc_strlen HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_strlen.

(** A call of `__GI___mempcpy` runs [Unit_string_mempcpy_os.fn___GI___mempcpy]. *)
Lemma hi_find___GI___mempcpy : Defines hi_ge "__GI___mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 43 "__GI___mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___mempcpy.

(** A call of `__GI_mempcpy` runs [Unit_string_mempcpy_os.fn___GI___mempcpy]. *)
Lemma hi_find___GI_mempcpy : Defines hi_ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 44 "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_mempcpy.

(** A call of `__GI_memcpy` runs [Unit_string_memcpy_os.fn___GI_memcpy]. *)
Lemma hi_find___GI_memcpy : Defines hi_ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 45 "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_memcpy.

(** A call of `__GI___libc_malloc` runs [malloc_fn]. *)
Lemma hi_find___GI___libc_malloc : Defines hi_ge "__GI___libc_malloc" malloc_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 46 "__GI___libc_malloc" malloc_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_malloc.

(** A call of `malloc` runs [malloc_fn]. *)
Lemma hi_find_malloc : Defines hi_ge "malloc" malloc_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 47 "malloc" malloc_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_malloc.

(** A call of `glibc_malloc#__libc_malloc2` runs [malloc2_fn]. *)
Lemma hi_find_malloc___libc_malloc2 : Defines hi_ge "glibc_malloc#__libc_malloc2" malloc2_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 48 "glibc_malloc#__libc_malloc2" malloc2_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_malloc___libc_malloc2.

(** A call of `__GI___libc_free` runs [free_fn]. *)
Lemma hi_find___GI___libc_free : Defines hi_ge "__GI___libc_free" free_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 49 "__GI___libc_free" free_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_free.

(** A call of `free` runs [free_fn]. *)
Lemma hi_find_free : Defines hi_ge "free" free_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 50 "free" free_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_free.

(** A call of `__new_exitfn` runs [new_exitfn_fn]. *)
Lemma hi_find___new_exitfn : Defines hi_ge "__new_exitfn" new_exitfn_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 51 "__new_exitfn" new_exitfn_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___new_exitfn.

(** A call of `__internal_atexit` runs [internal_atexit_fn]. *)
Lemma hi_find___internal_atexit : Defines hi_ge "__internal_atexit" internal_atexit_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 52 "__internal_atexit" internal_atexit_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___internal_atexit.

(** A call of `__cxa_atexit` runs [cxa_atexit_fn]. *)
Lemma hi_find___cxa_atexit : Defines hi_ge "__cxa_atexit" cxa_atexit_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 53 "__cxa_atexit" cxa_atexit_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___cxa_atexit.

(** A call of `atexit` runs [atexit_fn]. *)
Lemma hi_find_atexit : Defines hi_ge "atexit" atexit_fn.
Proof using Type. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 54 "atexit" atexit_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_atexit.

End fns.

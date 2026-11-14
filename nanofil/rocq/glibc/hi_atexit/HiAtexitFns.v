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
From Glibc Require Import HiAtexitModule StrlenLogic MemFwdCode StdlibCode AllocLogic AtexitLogic SysCode
  LibioReadCode LibioDoWriteCode LibioGenCode LibioXsputnCode LibioPutsCode LibioUnlinkCode LibioCloseItCode
  LibioFcloseCode LibioFlushCode LibioCleanupCode ExitRunCode LibioStdfilesCode.
Open Scope string_scope.

Section fns.
(** The runtime's free, which the genv carries. *)
Variable fre : word -> mem -> option (res unit * mem).

(** The genv of the linked module, its symbols laid out. *)
Definition hi_ge : genv := mkGenv hi_module hi_globals fre.

(** A call of `__fpending` runs [glibc___fpending]. *)
Definition HiAtexitFns_hi_ge_program_table : list (string * func) :=
  ("__fpending", glibc___fpending) ::
  ("_IO_ferror", glibc__IO_ferror) ::
  ("ferror", glibc__IO_ferror) ::
  ("__GI__IO_file_doallocate", glibc__IO_file_doallocate) ::
  ("_IO_file_close_maybe_unlink", glibc__IO_file_close_maybe_unlink) ::
  ("_IO_new_file_finish", glibc__IO_new_file_finish) ::
  ("_IO_new_do_write", glibc__IO_new_do_write) ::
  ("_IO_new_file_overflow", glibc__IO_new_file_overflow) ::
  ("__GI__IO_file_stat", glibc__IO_file_stat) ::
  ("__GI__IO_file_close", glibc__IO_file_close) ::
  ("_IO_new_file_write", glibc__IO_new_file_write) ::
  ("_IO_new_file_xsputn", glibc__IO_new_file_xsputn) ::
  ("__GI__IO_un_link", glibc__IO_un_link) ::
  ("__GI___overflow", glibc___overflow) ::
  ("__GI__IO_setb", glibc__IO_setb) ::
  ("__GI__IO_doallocbuf", glibc__IO_doallocbuf) ::
  ("__GI__IO_default_xsputn", glibc__IO_default_xsputn) ::
  ("__GI__IO_default_finish", glibc__IO_default_finish) ::
  ("__GI__IO_flush_all", glibc__IO_flush_all) ::
  ("_IO_cleanup", glibc__IO_cleanup) ::
  ("__GI__IO_unsave_markers", glibc__IO_unsave_markers) ::
  ("_IO_new_fclose", glibc__IO_new_fclose) ::
  ("fclose", glibc__IO_new_fclose) ::
  ("__GI__IO_puts", glibc__IO_puts) ::
  ("puts", glibc__IO_puts) ::
  ("glibc_stdfiles#_IO_stdfiles_init", glibc_glibc_stdfiles__IO_stdfiles_init) ::
  ("__isatty_nostatus", glibc___isatty_nostatus) ::
  ("__GI___libc_write", glibc___libc_write) ::
  ("__GI___write", glibc___libc_write) ::
  ("__GI___write_nocancel", glibc___write_nocancel) ::
  ("__lseek64", glibc___lseek64) ::
  ("__GI___fstat64", glibc___fstat64) ::
  ("__GI___close_nocancel", glibc___close_nocancel) ::
  ("__GI__exit", glibc__exit) ::
  ("_exit", glibc__exit) ::
  ("__run_exit_handlers", glibc___run_exit_handlers) ::
  ("__GI_exit", glibc_exit) ::
  ("exit", glibc_exit) ::
  ("__GI___call_tls_dtors", glibc___call_tls_dtors) ::
  ("__GI___libc_cleanup_push_defer", glibc___libc_cleanup_push_defer) ::
  ("__GI___libc_cleanup_pop_restore", glibc___libc_cleanup_pop_restore) ::
  ("__gnu_dev_major", glibc___gnu_dev_major) ::
  ("__GI_strlen", glibc_strlen) ::
  ("__GI___mempcpy", glibc_mempcpy) ::
  ("__GI_mempcpy", glibc_mempcpy) ::
  ("__GI_memcpy", glibc_memcpy) ::
  ("__GI___libc_malloc", malloc_fn) ::
  ("malloc", malloc_fn) ::
  ("malloc#__libc_malloc2", malloc2_fn) ::
  ("__GI___libc_free", free_fn) ::
  ("free", free_fn) ::
  ("__new_exitfn", new_exitfn_fn) ::
  ("__internal_atexit", internal_atexit_fn) ::
  ("__cxa_atexit", cxa_atexit_fn) ::
  ("atexit", atexit_fn) :: nil.
Lemma HiAtexitFns_hi_ge_program_table_correct :
  List.Forall (fun '(n, f) => find_fn hi_ge (TAtom n) = Some (Defined f)) HiAtexitFns_hi_ge_program_table.
Proof.
  apply defines_table_of_map.
  vm_cast_no_check (eq_refl (List.map (fun '(_, f) => Some (Defined f)) HiAtexitFns_hi_ge_program_table)).
Qed.
#[global] Instance HiAtexitFns_hi_ge_program_table_instance : ProgramTable hi_ge :=
  {| program_table := HiAtexitFns_hi_ge_program_table; program_table_correct := HiAtexitFns_hi_ge_program_table_correct |}.
Lemma hi_find___fpending : Defines hi_ge "__fpending" glibc___fpending.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 0 "__fpending" glibc___fpending HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___fpending.

(** A call of `_IO_ferror` runs [glibc__IO_ferror]. *)
Lemma hi_find__IO_ferror : Defines hi_ge "_IO_ferror" glibc__IO_ferror.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 1 "_IO_ferror" glibc__IO_ferror HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_ferror.

(** A call of `ferror` runs [glibc__IO_ferror]. *)
Lemma hi_find_ferror : Defines hi_ge "ferror" glibc__IO_ferror.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 2 "ferror" glibc__IO_ferror HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_ferror.

(** A call of `__GI__IO_file_doallocate` runs [glibc__IO_file_doallocate]. *)
Lemma hi_find___GI__IO_file_doallocate : Defines hi_ge "__GI__IO_file_doallocate" glibc__IO_file_doallocate.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 3 "__GI__IO_file_doallocate" glibc__IO_file_doallocate HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_file_doallocate.

(** A call of `_IO_file_close_maybe_unlink` runs [glibc__IO_file_close_maybe_unlink]. *)
Lemma hi_find__IO_file_close_maybe_unlink : Defines hi_ge "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 4 "_IO_file_close_maybe_unlink" glibc__IO_file_close_maybe_unlink HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_file_close_maybe_unlink.

(** A call of `_IO_new_file_finish` runs [glibc__IO_new_file_finish]. *)
Lemma hi_find__IO_new_file_finish : Defines hi_ge "_IO_new_file_finish" glibc__IO_new_file_finish.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 5 "_IO_new_file_finish" glibc__IO_new_file_finish HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_finish.

(** A call of `_IO_new_do_write` runs [glibc__IO_new_do_write]. *)
Lemma hi_find__IO_new_do_write : Defines hi_ge "_IO_new_do_write" glibc__IO_new_do_write.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 6 "_IO_new_do_write" glibc__IO_new_do_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_do_write.

(** A call of `_IO_new_file_overflow` runs [glibc__IO_new_file_overflow]. *)
Lemma hi_find__IO_new_file_overflow : Defines hi_ge "_IO_new_file_overflow" glibc__IO_new_file_overflow.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 7 "_IO_new_file_overflow" glibc__IO_new_file_overflow HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_overflow.

(** A call of `__GI__IO_file_stat` runs [glibc__IO_file_stat]. *)
Lemma hi_find___GI__IO_file_stat : Defines hi_ge "__GI__IO_file_stat" glibc__IO_file_stat.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 8 "__GI__IO_file_stat" glibc__IO_file_stat HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_file_stat.

(** A call of `__GI__IO_file_close` runs [glibc__IO_file_close]. *)
Lemma hi_find___GI__IO_file_close : Defines hi_ge "__GI__IO_file_close" glibc__IO_file_close.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 9 "__GI__IO_file_close" glibc__IO_file_close HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_file_close.

(** A call of `_IO_new_file_write` runs [glibc__IO_new_file_write]. *)
Lemma hi_find__IO_new_file_write : Defines hi_ge "_IO_new_file_write" glibc__IO_new_file_write.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 10 "_IO_new_file_write" glibc__IO_new_file_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_write.

(** A call of `_IO_new_file_xsputn` runs [glibc__IO_new_file_xsputn]. *)
Lemma hi_find__IO_new_file_xsputn : Defines hi_ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 11 "_IO_new_file_xsputn" glibc__IO_new_file_xsputn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_file_xsputn.

(** A call of `__GI__IO_un_link` runs [glibc__IO_un_link]. *)
Lemma hi_find___GI__IO_un_link : Defines hi_ge "__GI__IO_un_link" glibc__IO_un_link.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 12 "__GI__IO_un_link" glibc__IO_un_link HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_un_link.

(** A call of `__GI___overflow` runs [glibc___overflow]. *)
Lemma hi_find___GI___overflow : Defines hi_ge "__GI___overflow" glibc___overflow.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 13 "__GI___overflow" glibc___overflow HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___overflow.

(** A call of `__GI__IO_setb` runs [glibc__IO_setb]. *)
Lemma hi_find___GI__IO_setb : Defines hi_ge "__GI__IO_setb" glibc__IO_setb.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 14 "__GI__IO_setb" glibc__IO_setb HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_setb.

(** A call of `__GI__IO_doallocbuf` runs [glibc__IO_doallocbuf]. *)
Lemma hi_find___GI__IO_doallocbuf : Defines hi_ge "__GI__IO_doallocbuf" glibc__IO_doallocbuf.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 15 "__GI__IO_doallocbuf" glibc__IO_doallocbuf HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_doallocbuf.

(** A call of `__GI__IO_default_xsputn` runs [glibc__IO_default_xsputn]. *)
Lemma hi_find___GI__IO_default_xsputn : Defines hi_ge "__GI__IO_default_xsputn" glibc__IO_default_xsputn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 16 "__GI__IO_default_xsputn" glibc__IO_default_xsputn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_default_xsputn.

(** A call of `__GI__IO_default_finish` runs [glibc__IO_default_finish]. *)
Lemma hi_find___GI__IO_default_finish : Defines hi_ge "__GI__IO_default_finish" glibc__IO_default_finish.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 17 "__GI__IO_default_finish" glibc__IO_default_finish HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_default_finish.

(** A call of `__GI__IO_flush_all` runs [glibc__IO_flush_all]. *)
Lemma hi_find___GI__IO_flush_all : Defines hi_ge "__GI__IO_flush_all" glibc__IO_flush_all.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 18 "__GI__IO_flush_all" glibc__IO_flush_all HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_flush_all.

(** A call of `_IO_cleanup` runs [glibc__IO_cleanup]. *)
Lemma hi_find__IO_cleanup : Defines hi_ge "_IO_cleanup" glibc__IO_cleanup.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 19 "_IO_cleanup" glibc__IO_cleanup HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_cleanup.

(** A call of `__GI__IO_unsave_markers` runs [glibc__IO_unsave_markers]. *)
Lemma hi_find___GI__IO_unsave_markers : Defines hi_ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 20 "__GI__IO_unsave_markers" glibc__IO_unsave_markers HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_unsave_markers.

(** A call of `_IO_new_fclose` runs [glibc__IO_new_fclose]. *)
Lemma hi_find__IO_new_fclose : Defines hi_ge "_IO_new_fclose" glibc__IO_new_fclose.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 21 "_IO_new_fclose" glibc__IO_new_fclose HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__IO_new_fclose.

(** A call of `fclose` runs [glibc__IO_new_fclose]. *)
Lemma hi_find_fclose : Defines hi_ge "fclose" glibc__IO_new_fclose.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 22 "fclose" glibc__IO_new_fclose HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_fclose.

(** A call of `__GI__IO_puts` runs [glibc__IO_puts]. *)
Lemma hi_find___GI__IO_puts : Defines hi_ge "__GI__IO_puts" glibc__IO_puts.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 23 "__GI__IO_puts" glibc__IO_puts HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__IO_puts.

(** A call of `puts` runs [glibc__IO_puts]. *)
Lemma hi_find_puts : Defines hi_ge "puts" glibc__IO_puts.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 24 "puts" glibc__IO_puts HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_puts.

(** A call of `glibc_stdfiles#_IO_stdfiles_init` runs [glibc_glibc_stdfiles__IO_stdfiles_init]. *)
Lemma hi_find_glibc_stdfiles__IO_stdfiles_init : Defines hi_ge "glibc_stdfiles#_IO_stdfiles_init" glibc_glibc_stdfiles__IO_stdfiles_init.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 25 "glibc_stdfiles#_IO_stdfiles_init" glibc_glibc_stdfiles__IO_stdfiles_init HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_glibc_stdfiles__IO_stdfiles_init.

(** A call of `__isatty_nostatus` runs [glibc___isatty_nostatus]. *)
Lemma hi_find___isatty_nostatus : Defines hi_ge "__isatty_nostatus" glibc___isatty_nostatus.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 26 "__isatty_nostatus" glibc___isatty_nostatus HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___isatty_nostatus.

(** A call of `__GI___libc_write` runs [glibc___libc_write]. *)
Lemma hi_find___GI___libc_write : Defines hi_ge "__GI___libc_write" glibc___libc_write.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 27 "__GI___libc_write" glibc___libc_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_write.

(** A call of `__GI___write` runs [glibc___libc_write]. *)
Lemma hi_find___GI___write : Defines hi_ge "__GI___write" glibc___libc_write.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 28 "__GI___write" glibc___libc_write HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___write.

(** A call of `__GI___write_nocancel` runs [glibc___write_nocancel]. *)
Lemma hi_find___GI___write_nocancel : Defines hi_ge "__GI___write_nocancel" glibc___write_nocancel.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 29 "__GI___write_nocancel" glibc___write_nocancel HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___write_nocancel.

(** A call of `__lseek64` runs [glibc___lseek64]. *)
Lemma hi_find___lseek64 : Defines hi_ge "__lseek64" glibc___lseek64.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 30 "__lseek64" glibc___lseek64 HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___lseek64.

(** A call of `__GI___fstat64` runs [glibc___fstat64]. *)
Lemma hi_find___GI___fstat64 : Defines hi_ge "__GI___fstat64" glibc___fstat64.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 31 "__GI___fstat64" glibc___fstat64 HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___fstat64.

(** A call of `__GI___close_nocancel` runs [glibc___close_nocancel]. *)
Lemma hi_find___GI___close_nocancel : Defines hi_ge "__GI___close_nocancel" glibc___close_nocancel.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 32 "__GI___close_nocancel" glibc___close_nocancel HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___close_nocancel.

(** A call of `__GI__exit` runs [glibc__exit]. *)
Lemma hi_find___GI__exit : Defines hi_ge "__GI__exit" glibc__exit.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 33 "__GI__exit" glibc__exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI__exit.

(** A call of `_exit` runs [glibc__exit]. *)
Lemma hi_find__exit : Defines hi_ge "_exit" glibc__exit.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 34 "_exit" glibc__exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find__exit.

(** A call of `__run_exit_handlers` runs [glibc___run_exit_handlers]. *)
Lemma hi_find___run_exit_handlers : Defines hi_ge "__run_exit_handlers" glibc___run_exit_handlers.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 35 "__run_exit_handlers" glibc___run_exit_handlers HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___run_exit_handlers.

(** A call of `__GI_exit` runs [glibc_exit]. *)
Lemma hi_find___GI_exit : Defines hi_ge "__GI_exit" glibc_exit.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 36 "__GI_exit" glibc_exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_exit.

(** A call of `exit` runs [glibc_exit]. *)
Lemma hi_find_exit : Defines hi_ge "exit" glibc_exit.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 37 "exit" glibc_exit HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_exit.

(** A call of `__GI___call_tls_dtors` runs [glibc___call_tls_dtors]. *)
Lemma hi_find___GI___call_tls_dtors : Defines hi_ge "__GI___call_tls_dtors" glibc___call_tls_dtors.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 38 "__GI___call_tls_dtors" glibc___call_tls_dtors HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___call_tls_dtors.

(** A call of `__GI___libc_cleanup_push_defer` runs [glibc___libc_cleanup_push_defer]. *)
Lemma hi_find___GI___libc_cleanup_push_defer : Defines hi_ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 39 "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_cleanup_push_defer.

(** A call of `__GI___libc_cleanup_pop_restore` runs [glibc___libc_cleanup_pop_restore]. *)
Lemma hi_find___GI___libc_cleanup_pop_restore : Defines hi_ge "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 40 "__GI___libc_cleanup_pop_restore" glibc___libc_cleanup_pop_restore HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_cleanup_pop_restore.

(** A call of `__gnu_dev_major` runs [glibc___gnu_dev_major]. *)
Lemma hi_find___gnu_dev_major : Defines hi_ge "__gnu_dev_major" glibc___gnu_dev_major.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 41 "__gnu_dev_major" glibc___gnu_dev_major HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___gnu_dev_major.

(** A call of `__GI_strlen` runs [glibc_strlen]. *)
Lemma hi_find___GI_strlen : Defines hi_ge "__GI_strlen" glibc_strlen.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 42 "__GI_strlen" glibc_strlen HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_strlen.

(** A call of `__GI___mempcpy` runs [glibc_mempcpy]. *)
Lemma hi_find___GI___mempcpy : Defines hi_ge "__GI___mempcpy" glibc_mempcpy.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 43 "__GI___mempcpy" glibc_mempcpy HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___mempcpy.

(** A call of `__GI_mempcpy` runs [glibc_mempcpy]. *)
Lemma hi_find___GI_mempcpy : Defines hi_ge "__GI_mempcpy" glibc_mempcpy.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 44 "__GI_mempcpy" glibc_mempcpy HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_mempcpy.

(** A call of `__GI_memcpy` runs [glibc_memcpy]. *)
Lemma hi_find___GI_memcpy : Defines hi_ge "__GI_memcpy" glibc_memcpy.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 45 "__GI_memcpy" glibc_memcpy HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI_memcpy.

(** A call of `__GI___libc_malloc` runs [malloc_fn]. *)
Lemma hi_find___GI___libc_malloc : Defines hi_ge "__GI___libc_malloc" malloc_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 46 "__GI___libc_malloc" malloc_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_malloc.

(** A call of `malloc` runs [malloc_fn]. *)
Lemma hi_find_malloc : Defines hi_ge "malloc" malloc_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 47 "malloc" malloc_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_malloc.

(** A call of `malloc#__libc_malloc2` runs [malloc2_fn]. *)
Lemma hi_find_malloc___libc_malloc2 : Defines hi_ge "malloc#__libc_malloc2" malloc2_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 48 "malloc#__libc_malloc2" malloc2_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_malloc___libc_malloc2.

(** A call of `__GI___libc_free` runs [free_fn]. *)
Lemma hi_find___GI___libc_free : Defines hi_ge "__GI___libc_free" free_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 49 "__GI___libc_free" free_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___GI___libc_free.

(** A call of `free` runs [free_fn]. *)
Lemma hi_find_free : Defines hi_ge "free" free_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 50 "free" free_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_free.

(** A call of `__new_exitfn` runs [new_exitfn_fn]. *)
Lemma hi_find___new_exitfn : Defines hi_ge "__new_exitfn" new_exitfn_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 51 "__new_exitfn" new_exitfn_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___new_exitfn.

(** A call of `__internal_atexit` runs [internal_atexit_fn]. *)
Lemma hi_find___internal_atexit : Defines hi_ge "__internal_atexit" internal_atexit_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 52 "__internal_atexit" internal_atexit_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___internal_atexit.

(** A call of `__cxa_atexit` runs [cxa_atexit_fn]. *)
Lemma hi_find___cxa_atexit : Defines hi_ge "__cxa_atexit" cxa_atexit_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 53 "__cxa_atexit" cxa_atexit_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find___cxa_atexit.

(** A call of `atexit` runs [atexit_fn]. *)
Lemma hi_find_atexit : Defines hi_ge "atexit" atexit_fn.
Proof. exact (defines_from_table_nth hi_ge HiAtexitFns_hi_ge_program_table 54 "atexit" atexit_fn HiAtexitFns_hi_ge_program_table_correct eq_refl). Qed.
#[global] Existing Instance hi_find_atexit.

End fns.

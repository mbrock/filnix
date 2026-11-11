(** The proofs of glibc's functions were made over small fixtures,
    one group of functions at a time. To use them for the whole linked
    program, each function the program calls must be the same function
    there. This file shows that it is: hi_atexit/code.sh links every
    unit under the object name its fixture uses, so a call of each name
    in the linked program runs the function its fixture defines, and
    each lemma below is checked by computation.

    The genv [hi_ge] is the linked module with its globals and any free
    function the runtime supplies. *)

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
Lemma hi_find___fpending : find_fn hi_ge (TAtom "__fpending") = Some (Defined glibc___fpending).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_ferror` runs [glibc__IO_ferror]. *)
Lemma hi_find__IO_ferror : find_fn hi_ge (TAtom "_IO_ferror") = Some (Defined glibc__IO_ferror).
Proof. vm_compute. reflexivity. Qed.

(** A call of `ferror` runs [glibc__IO_ferror]. *)
Lemma hi_find_ferror : find_fn hi_ge (TAtom "ferror") = Some (Defined glibc__IO_ferror).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_file_doallocate` runs [glibc__IO_file_doallocate]. *)
Lemma hi_find___GI__IO_file_doallocate : find_fn hi_ge (TAtom "__GI__IO_file_doallocate") = Some (Defined glibc__IO_file_doallocate).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_file_close_maybe_unlink` runs [glibc__IO_file_close_maybe_unlink]. *)
Lemma hi_find__IO_file_close_maybe_unlink : find_fn hi_ge (TAtom "_IO_file_close_maybe_unlink") = Some (Defined glibc__IO_file_close_maybe_unlink).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_new_file_finish` runs [glibc__IO_new_file_finish]. *)
Lemma hi_find__IO_new_file_finish : find_fn hi_ge (TAtom "_IO_new_file_finish") = Some (Defined glibc__IO_new_file_finish).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_new_do_write` runs [glibc__IO_new_do_write]. *)
Lemma hi_find__IO_new_do_write : find_fn hi_ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_new_file_overflow` runs [glibc__IO_new_file_overflow]. *)
Lemma hi_find__IO_new_file_overflow : find_fn hi_ge (TAtom "_IO_new_file_overflow") = Some (Defined glibc__IO_new_file_overflow).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_file_stat` runs [glibc__IO_file_stat]. *)
Lemma hi_find___GI__IO_file_stat : find_fn hi_ge (TAtom "__GI__IO_file_stat") = Some (Defined glibc__IO_file_stat).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_file_close` runs [glibc__IO_file_close]. *)
Lemma hi_find___GI__IO_file_close : find_fn hi_ge (TAtom "__GI__IO_file_close") = Some (Defined glibc__IO_file_close).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_new_file_write` runs [glibc__IO_new_file_write]. *)
Lemma hi_find__IO_new_file_write : find_fn hi_ge (TAtom "_IO_new_file_write") = Some (Defined glibc__IO_new_file_write).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_new_file_xsputn` runs [glibc__IO_new_file_xsputn]. *)
Lemma hi_find__IO_new_file_xsputn : find_fn hi_ge (TAtom "_IO_new_file_xsputn") = Some (Defined glibc__IO_new_file_xsputn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_un_link` runs [glibc__IO_un_link]. *)
Lemma hi_find___GI__IO_un_link : find_fn hi_ge (TAtom "__GI__IO_un_link") = Some (Defined glibc__IO_un_link).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___overflow` runs [glibc___overflow]. *)
Lemma hi_find___GI___overflow : find_fn hi_ge (TAtom "__GI___overflow") = Some (Defined glibc___overflow).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_setb` runs [glibc__IO_setb]. *)
Lemma hi_find___GI__IO_setb : find_fn hi_ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_doallocbuf` runs [glibc__IO_doallocbuf]. *)
Lemma hi_find___GI__IO_doallocbuf : find_fn hi_ge (TAtom "__GI__IO_doallocbuf") = Some (Defined glibc__IO_doallocbuf).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_default_xsputn` runs [glibc__IO_default_xsputn]. *)
Lemma hi_find___GI__IO_default_xsputn : find_fn hi_ge (TAtom "__GI__IO_default_xsputn") = Some (Defined glibc__IO_default_xsputn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_default_finish` runs [glibc__IO_default_finish]. *)
Lemma hi_find___GI__IO_default_finish : find_fn hi_ge (TAtom "__GI__IO_default_finish") = Some (Defined glibc__IO_default_finish).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_flush_all` runs [glibc__IO_flush_all]. *)
Lemma hi_find___GI__IO_flush_all : find_fn hi_ge (TAtom "__GI__IO_flush_all") = Some (Defined glibc__IO_flush_all).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_cleanup` runs [glibc__IO_cleanup]. *)
Lemma hi_find__IO_cleanup : find_fn hi_ge (TAtom "_IO_cleanup") = Some (Defined glibc__IO_cleanup).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_unsave_markers` runs [glibc__IO_unsave_markers]. *)
Lemma hi_find___GI__IO_unsave_markers : find_fn hi_ge (TAtom "__GI__IO_unsave_markers") = Some (Defined glibc__IO_unsave_markers).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_IO_new_fclose` runs [glibc__IO_new_fclose]. *)
Lemma hi_find__IO_new_fclose : find_fn hi_ge (TAtom "_IO_new_fclose") = Some (Defined glibc__IO_new_fclose).
Proof. vm_compute. reflexivity. Qed.

(** A call of `fclose` runs [glibc__IO_new_fclose]. *)
Lemma hi_find_fclose : find_fn hi_ge (TAtom "fclose") = Some (Defined glibc__IO_new_fclose).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__IO_puts` runs [glibc__IO_puts]. *)
Lemma hi_find___GI__IO_puts : find_fn hi_ge (TAtom "__GI__IO_puts") = Some (Defined glibc__IO_puts).
Proof. vm_compute. reflexivity. Qed.

(** A call of `puts` runs [glibc__IO_puts]. *)
Lemma hi_find_puts : find_fn hi_ge (TAtom "puts") = Some (Defined glibc__IO_puts).
Proof. vm_compute. reflexivity. Qed.

(** A call of `glibc_stdfiles#_IO_stdfiles_init` runs [glibc_glibc_stdfiles__IO_stdfiles_init]. *)
Lemma hi_find_glibc_stdfiles__IO_stdfiles_init : find_fn hi_ge (TAtom "glibc_stdfiles#_IO_stdfiles_init") = Some (Defined glibc_glibc_stdfiles__IO_stdfiles_init).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__isatty_nostatus` runs [glibc___isatty_nostatus]. *)
Lemma hi_find___isatty_nostatus : find_fn hi_ge (TAtom "__isatty_nostatus") = Some (Defined glibc___isatty_nostatus).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___libc_write` runs [glibc___libc_write]. *)
Lemma hi_find___GI___libc_write : find_fn hi_ge (TAtom "__GI___libc_write") = Some (Defined glibc___libc_write).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___write` runs [glibc___libc_write]. *)
Lemma hi_find___GI___write : find_fn hi_ge (TAtom "__GI___write") = Some (Defined glibc___libc_write).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___write_nocancel` runs [glibc___write_nocancel]. *)
Lemma hi_find___GI___write_nocancel : find_fn hi_ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__lseek64` runs [glibc___lseek64]. *)
Lemma hi_find___lseek64 : find_fn hi_ge (TAtom "__lseek64") = Some (Defined glibc___lseek64).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___fstat64` runs [glibc___fstat64]. *)
Lemma hi_find___GI___fstat64 : find_fn hi_ge (TAtom "__GI___fstat64") = Some (Defined glibc___fstat64).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___close_nocancel` runs [glibc___close_nocancel]. *)
Lemma hi_find___GI___close_nocancel : find_fn hi_ge (TAtom "__GI___close_nocancel") = Some (Defined glibc___close_nocancel).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI__exit` runs [glibc__exit]. *)
Lemma hi_find___GI__exit : find_fn hi_ge (TAtom "__GI__exit") = Some (Defined glibc__exit).
Proof. vm_compute. reflexivity. Qed.

(** A call of `_exit` runs [glibc__exit]. *)
Lemma hi_find__exit : find_fn hi_ge (TAtom "_exit") = Some (Defined glibc__exit).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__run_exit_handlers` runs [glibc___run_exit_handlers]. *)
Lemma hi_find___run_exit_handlers : find_fn hi_ge (TAtom "__run_exit_handlers") = Some (Defined glibc___run_exit_handlers).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI_exit` runs [glibc_exit]. *)
Lemma hi_find___GI_exit : find_fn hi_ge (TAtom "__GI_exit") = Some (Defined glibc_exit).
Proof. vm_compute. reflexivity. Qed.

(** A call of `exit` runs [glibc_exit]. *)
Lemma hi_find_exit : find_fn hi_ge (TAtom "exit") = Some (Defined glibc_exit).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___call_tls_dtors` runs [glibc___call_tls_dtors]. *)
Lemma hi_find___GI___call_tls_dtors : find_fn hi_ge (TAtom "__GI___call_tls_dtors") = Some (Defined glibc___call_tls_dtors).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___libc_cleanup_push_defer` runs [glibc___libc_cleanup_push_defer]. *)
Lemma hi_find___GI___libc_cleanup_push_defer : find_fn hi_ge (TAtom "__GI___libc_cleanup_push_defer") = Some (Defined glibc___libc_cleanup_push_defer).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___libc_cleanup_pop_restore` runs [glibc___libc_cleanup_pop_restore]. *)
Lemma hi_find___GI___libc_cleanup_pop_restore : find_fn hi_ge (TAtom "__GI___libc_cleanup_pop_restore") = Some (Defined glibc___libc_cleanup_pop_restore).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__gnu_dev_major` runs [glibc___gnu_dev_major]. *)
Lemma hi_find___gnu_dev_major : find_fn hi_ge (TAtom "__gnu_dev_major") = Some (Defined glibc___gnu_dev_major).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI_strlen` runs [glibc_strlen]. *)
Lemma hi_find___GI_strlen : find_fn hi_ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___mempcpy` runs [glibc_mempcpy]. *)
Lemma hi_find___GI___mempcpy : find_fn hi_ge (TAtom "__GI___mempcpy") = Some (Defined glibc_mempcpy).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI_mempcpy` runs [glibc_mempcpy]. *)
Lemma hi_find___GI_mempcpy : find_fn hi_ge (TAtom "__GI_mempcpy") = Some (Defined glibc_mempcpy).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI_memcpy` runs [glibc_memcpy]. *)
Lemma hi_find___GI_memcpy : find_fn hi_ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___libc_malloc` runs [malloc_fn]. *)
Lemma hi_find___GI___libc_malloc : find_fn hi_ge (TAtom "__GI___libc_malloc") = Some (Defined malloc_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `malloc` runs [malloc_fn]. *)
Lemma hi_find_malloc : find_fn hi_ge (TAtom "malloc") = Some (Defined malloc_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `malloc#__libc_malloc2` runs [malloc2_fn]. *)
Lemma hi_find_malloc___libc_malloc2 : find_fn hi_ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__GI___libc_free` runs [free_fn]. *)
Lemma hi_find___GI___libc_free : find_fn hi_ge (TAtom "__GI___libc_free") = Some (Defined free_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `free` runs [free_fn]. *)
Lemma hi_find_free : find_fn hi_ge (TAtom "free") = Some (Defined free_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__new_exitfn` runs [new_exitfn_fn]. *)
Lemma hi_find___new_exitfn : find_fn hi_ge (TAtom "__new_exitfn") = Some (Defined new_exitfn_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__internal_atexit` runs [internal_atexit_fn]. *)
Lemma hi_find___internal_atexit : find_fn hi_ge (TAtom "__internal_atexit") = Some (Defined internal_atexit_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `__cxa_atexit` runs [cxa_atexit_fn]. *)
Lemma hi_find___cxa_atexit : find_fn hi_ge (TAtom "__cxa_atexit") = Some (Defined cxa_atexit_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `atexit` runs [atexit_fn]. *)
Lemma hi_find_atexit : find_fn hi_ge (TAtom "atexit") = Some (Defined atexit_fn).
Proof. vm_compute. reflexivity. Qed.

End fns.

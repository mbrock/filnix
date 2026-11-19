(** Startup proofs unfold the bodies of the glibc functions as they step through
    the captured IR. These names refer to the captured object files so that each
    program can establish the link to its own image. *)

From Glibc Require Import Unit_csu_libcZ2dstart_os Unit_csu_libcZ2dtls_os Unit_ctype_ctypeZ2dinfo_os Unit_elf_dlZ2dtls_init_tp_os Unit_elf_dlZ2dtunables_os.
From Glibc Require Import Unit_libio_vtables_os Unit_nptl_pthread_mutex_conf_os.
From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics.
Import ListNotations.
Open Scope string_scope.

(** ## Thread setup

    Two functions give the process its thread object. Their bodies come
    first because the other startup proofs run after them. *)

(** This constant is the body of `c: __libc_setup_tls`, which allocates
    the thread object and makes it the thread's cookie. *)
Definition start_setup_tls_fn : func := Unit_csu_libcZ2dtls_os.fn___libc_setup_tls.

(** This constant is the body of `c: __tls_init_tp`, which fills in the
    thread object's own fields. *)
Definition start_tls_init_tp_fn : func := Unit_elf_dlZ2dtls_init_tp_os.fn___tls_init_tp.

(** ## The two handlers

    `c: __libc_start_main` registers an errno handler and a dlerror
    handler with the runtime. The errno handler's body is already fixed
    by its registration contract, so only the dlerror handler's body
    appears here. *)

(** This constant is the body of the dlerror handler that
    `c: __libc_start_main` registers. *)
Definition start_dlerror_handler_fn : func := Unit_csu_libcZ2dstart_os.fn_glibc_libc_start'23dlerror_handler.

(** ## Early initialization

    `c: __libc_early_init` sets up the character tables, reads several
    tunables and starts the allocator. The bodies below are the parts of
    that work which the proofs so far cover. *)

(** This constant is the body of `c: __tunable_get_val`, which copies a
    tunable's value out of the tunable table. *)
Definition start_tunable_get_val_fn : func := Unit_elf_dlZ2dtunables_os.fn___tunable_get_val.

(** This constant is the body of `c: __pthread_tunables_init`, which
    reads the mutex spin-count tunable. *)
Definition start_pthread_tunables_init_fn : func := Unit_nptl_pthread_mutex_conf_os.fn___pthread_tunables_init.

(** This constant is the body of `c: __ctype_init`, which points the
    thread's character-class tables at the C locale's. *)
Definition start_ctype_init_fn : func := Unit_ctype_ctypeZ2dinfo_os.fn___GI___ctype_init.

(** ## Constructors

    The image registers three constructors, which the runner calls before
    `c: main`. Their bodies come from the same image. *)

(** This constant is the body of `c: check_stdfiles_vtables`, which
    checks that the three standard streams use glibc's own jump table. *)
Definition start_check_vtables_fn : func := Unit_libio_vtables_os.fn_glibc_vtables'23check_stdfiles_vtables.

(** The linked hi_atexit image binds the startup functions to the bodies used in glibc’s proofs. *)

From Stdlib Require Import String.
From Nanofil Require Import Term Syntax Semantics.
From Glibc Require Import HiAtexitModule StartCallMain StartClockGettime StartCode StartCtypeInit StartEarlyInit StartGetrlimit StartInitFirst StartInitMisc StartLibcStartMain StartPtmallocInit StartTunableIsInitialized.
Open Scope string_scope.

(** The image defines `c: __libc_start_call_main` with that body. *)
Lemma start_call_main_defined :
  find_direct (TAtom "glibc_libc_start#__libc_start_call_main") hi_module = Some (Defined start_call_main_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __GI___clock_gettime` with that body. *)
Lemma start_clock_gettime_defined :
  find_direct (TAtom "__GI___clock_gettime") hi_module = Some (Defined start_clock_gettime_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: check_stdfiles_vtables` with that body. *)
Lemma start_check_vtables_defined :
  find_direct (TAtom "glibc_vtables#check_stdfiles_vtables") hi_module = Some (Defined start_check_vtables_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __GI___ctype_init` with that body. *)
Lemma start_ctype_init_defined :
  find_direct (TAtom "__GI___ctype_init") hi_module = Some (Defined start_ctype_init_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __pthread_tunables_init` with that body. *)
Lemma start_pthread_tunables_init_defined :
  find_direct (TAtom "__pthread_tunables_init") hi_module = Some (Defined start_pthread_tunables_init_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __tunable_get_val` with that body. *)
Lemma start_tunable_get_val_defined :
  find_direct (TAtom "__tunable_get_val") hi_module = Some (Defined start_tunable_get_val_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines the dlerror handler with that body. *)
Lemma start_dlerror_handler_defined :
  find_direct (TAtom "glibc_libc_start#dlerror_handler") hi_module = Some (Defined start_dlerror_handler_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __tls_init_tp` with that body. *)
Lemma start_tls_init_tp_defined :
  find_direct (TAtom "__tls_init_tp") hi_module = Some (Defined start_tls_init_tp_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __libc_setup_tls` with that body. *)
Lemma start_setup_tls_defined :
  find_direct (TAtom "__libc_setup_tls") hi_module = Some (Defined start_setup_tls_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines both functions with those bodies. *)
Lemma start_early_init_defined :
  find_direct (TAtom "__libc_early_init") hi_module = Some (Defined start_early_init_fn) /\
  find_direct (TAtom "__getrandom_early_init") hi_module = Some (Defined start_getrandom_early_init_fn).
Proof. split; vm_compute; reflexivity. Qed.

(** Callers name the function `c: __GI___getrlimit`, which the image
    declares as an alias of that body. *)
Lemma start_getrlimit_alias :
  find_alias (TAtom "__GI___getrlimit") hi_module = Some (TAtom "__GI___getrlimit64").
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __GI___getrlimit64` with that body. *)
Lemma start_getrlimit_defined :
  find_direct (TAtom "__GI___getrlimit64") hi_module = Some (Defined start_getrlimit_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: _init_first` with that body. *)
Lemma start_init_first_defined :
  find_direct (TAtom "glibc_init_first#_init_first") hi_module = Some (Defined start_init_first_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __init_misc` with that body. *)
Lemma start_init_misc_defined :
  find_direct (TAtom "__init_misc") hi_module = Some (Defined start_init_misc_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __libc_start_main` with that body. *)
Lemma start_libc_start_main_defined :
  find_direct (TAtom "__libc_start_main") HiAtexitModule.hi_module = Some (Defined start_libc_start_main_fn).
Proof. vm_compute. reflexivity. Qed.

(** The image defines `c: __ptmalloc_init` with that body. *)
Lemma start_ptmalloc_init_defined :
  find_direct (TAtom "__ptmalloc_init") hi_module = Some (Defined start_ptmalloc_init_fn).
Proof. vm_compute. reflexivity. Qed.

(** The linked image contains that body under this name. *)
Lemma start_tunable_is_initialized_defined :
  find_direct (TAtom "__tunable_is_initialized") hi_module = Some (Defined start_tunable_is_initialized_fn).
Proof. vm_compute. reflexivity. Qed.

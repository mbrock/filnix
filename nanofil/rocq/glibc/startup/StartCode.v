(** The proofs of glibc's startup functions need each function's body as
    a Rocq constant, so that a rule can unfold it block by block. This
    file takes those bodies from the linked hi_atexit image. The bodies
    do not mention any address, so a later relink of the image that moves
    its globals leaves them unchanged.

    ## How the bodies are named

    Each constant is the image's definition of one symbol, found without
    following aliases. A lemma next to each one records that the image
    defines the symbol with that body, and a proof about a program cites
    it through its own genv. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics.
From Glibc Require Import HiAtexitModule.
Import ListNotations.
Open Scope string_scope.

(** This function returns the image's body for a symbol, or an empty
    function when the image does not define it. *)
Definition start_fn (n : string) : func :=
  match find_direct (TAtom n) hi_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "local") RVoid [] []
  end.

(** ## Thread setup *)

(** This constant is the body of `c: __libc_setup_tls`, which allocates
    the thread object and makes it the thread's cookie. *)
Definition start_setup_tls_fn : func := Eval vm_compute in start_fn "__libc_setup_tls".

(** The image defines `c: __libc_setup_tls` with that body. *)
Lemma start_setup_tls_defined :
  find_direct (TAtom "__libc_setup_tls") hi_module = Some (Defined start_setup_tls_fn).
Proof. vm_compute. reflexivity. Qed.

(** This constant is the body of `c: __tls_init_tp`, which fills in the
    thread object's own fields. *)
Definition start_tls_init_tp_fn : func := Eval vm_compute in start_fn "__tls_init_tp".

(** The image defines `c: __tls_init_tp` with that body. *)
Lemma start_tls_init_tp_defined :
  find_direct (TAtom "__tls_init_tp") hi_module = Some (Defined start_tls_init_tp_fn).
Proof. vm_compute. reflexivity. Qed.

(** ## The two handlers *)

(** This constant is the body of the dlerror handler that
    `c: __libc_start_main` registers. *)
Definition start_dlerror_handler_fn : func := Eval vm_compute in start_fn "glibc_libc_start#dlerror_handler".

(** The image defines the dlerror handler with that body. *)
Lemma start_dlerror_handler_defined :
  find_direct (TAtom "glibc_libc_start#dlerror_handler") hi_module = Some (Defined start_dlerror_handler_fn).
Proof. vm_compute. reflexivity. Qed.

(** ## Early initialization *)

(** This constant is the body of `c: __tunable_get_val`, which copies a
    tunable's value out of the tunable table. *)
Definition start_tunable_get_val_fn : func := Eval vm_compute in start_fn "__tunable_get_val".

(** The image defines `c: __tunable_get_val` with that body. *)
Lemma start_tunable_get_val_defined :
  find_direct (TAtom "__tunable_get_val") hi_module = Some (Defined start_tunable_get_val_fn).
Proof. vm_compute. reflexivity. Qed.

(** This constant is the body of `c: __pthread_tunables_init`, which
    reads the mutex spin-count tunable. *)
Definition start_pthread_tunables_init_fn : func := Eval vm_compute in start_fn "__pthread_tunables_init".

(** The image defines `c: __pthread_tunables_init` with that body. *)
Lemma start_pthread_tunables_init_defined :
  find_direct (TAtom "__pthread_tunables_init") hi_module = Some (Defined start_pthread_tunables_init_fn).
Proof. vm_compute. reflexivity. Qed.

(** This constant is the body of `c: __ctype_init`, which points the
    thread's character-class tables at the C locale's. *)
Definition start_ctype_init_fn : func := Eval vm_compute in start_fn "__GI___ctype_init".

(** The image defines `c: __ctype_init` with that body. *)
Lemma start_ctype_init_defined :
  find_direct (TAtom "__GI___ctype_init") hi_module = Some (Defined start_ctype_init_fn).
Proof. vm_compute. reflexivity. Qed.

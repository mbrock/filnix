(** A proof that the hi_atexit program never panics has to start from
    its real linked image, beginning at `c: __libc_start_main`. The
    startup world, its contracts and the constructor runner are defined
    for any linked image, so a few facts must tie them to this one. This
    module checks those facts by computation for [hi_module], which is
    the decoded image with the runner appended.

    ## What is checked

    Two facts about the image matter for startup. First, appending the
    runner must not move any existing global. It moves none, because the
    image uses none of the three names that the runner adds, and the
    appended runner then defines `c: zrun_deferred_global_ctors`. Second,
    the image registers exactly the errno handler that the registration
    contract names, and that handler stores its argument to the global
    `c: __libc_errno`. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Run.
From Glibc Require Import HiAtexitModule OsStartCalls StartCtors.
Import ListNotations.
Open Scope string_scope.

(** ## The image with its runner

    [hi_module] is the decoded image followed by its runner. These
    lemmas check that the decoded image allows the runner and that
    appending it moves nothing. *)

(** No item of the decoded image uses a runner name. *)
Lemma hi_ctor_names_fresh : ctor_names_fresh hi_linked = true.
Proof. vm_compute. reflexivity. Qed.

(** The image registers its three constructors: `c: _IO_stdfiles_init`,
    `c: check_stdfiles_vtables` and `c: _init_first`. *)
Lemma hi_ctor_names :
  ctor_names hi_linked = [TAtom "glibc_stdfiles#_IO_stdfiles_init"; TAtom "glibc_vtables#check_stdfiles_vtables";
                           TAtom "glibc_init_first#_init_first"].
Proof. vm_compute. reflexivity. Qed.

(** In the program, the runner symbol is the runner for three
    constructors. *)
Lemma hi_start_runner : find_direct ctor_runner_name hi_module = Some (Defined (ctor_runner 3)).
Proof. rewrite hi_module_runner. exact (with_ctor_runner_defines _ hi_ctor_names_fresh). Qed.

(** Appending the runner keeps the address and capability of every
    symbol of the decoded image. [initial_memory_globals] relates this
    layout to the one [initial_memory] gives. *)
Lemma hi_start_keeps_globals :
  match module_globals hi_linked with
  | Some g0 => forallb (fun '(n, p) =>
      match lookup n hi_globals with
      | Some q => andb (Z.eqb (ptr_addr p) (ptr_addr q)) (cap_eqb (ptr_cap p) (ptr_cap q))
      | None => false
      end) g0
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** ## The errno handler *)

(** The image defines the errno handler as [errno_handler_fn]. *)
Lemma hi_errno_handler : find_direct errno_handler_name hi_module = Some (Defined errno_handler_fn).
Proof. vm_compute. reflexivity. Qed.

(** The proofs of `c: main` assume that `c: errno` lives at one fixed
    address. The handler stores to `c: __libc_errno`, and this lemma shows
    that it is the 4-byte-aligned global at 70608, which is the errno
    cell those proofs use. *)
Lemma hi_errno_cell : lookup (TAtom "__libc_errno") hi_globals = Some (mkPtr 70608 (Obj 70608)).
Proof. vm_compute. reflexivity. Qed.

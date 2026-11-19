(** A proof about hi_atexit.c has to run the program together with the
    glibc code it calls, so it needs that whole program as one Rocq
    module. This file takes the linked module from HiAtexitCode and
    appends the constructor runner that libpizlo provides
    as `c: zrun_deferred_global_ctors`, which `c: __libc_start_main`
    calls. The result is the program's single module. The file also
    lays out its globals, the addresses every symbol gets in the
    program's initial memory.

    The runner's three items come after every linked item, so they move
    no existing symbol; [HiStartImage] checks that by computation. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Transport Semantics Run.
From Glibc Require Export HiAtexitCode.
From Glibc Require Import StartCtors.
Import ListNotations.
Open Scope string_scope.

(** The program is the linked module followed by its constructor
    runner. *)
Definition hi_module : module := with_ctor_runner hi_linked.

(** The program is exactly the linked module with the runner appended. *)
Lemma hi_module_runner : hi_module = with_ctor_runner hi_linked.
Proof. reflexivity. Qed.

(** Laying out the program places each of its symbols at this pointer. *)
Definition hi_globals : list (name * ptr) := Eval vm_compute in
  match initial_memory hi_module with Some (g, _) => g | None => [] end.

(** Laying out the module gives [hi_globals]. *)
Lemma hi_layout : option_map fst (initial_memory hi_module) = Some hi_globals.
Proof. vm_compute. reflexivity. Qed.

(** This image retains the internal mempcpy alias and omits the unused stpcpy alias. *)
From Glibc Require Import Unit_string_mempcpy_os.
Example hi_gettext_link_gaps :
  find_alias (TAtom "__GI_mempcpy") hi_module = Some (TAtom "__GI___mempcpy") /\
  find_direct (TAtom "__GI___mempcpy") hi_module = Some (Defined Unit_string_mempcpy_os.fn___GI___mempcpy) /\
  find_direct (TAtom "__GI_stpcpy") hi_module = None /\ find_alias (TAtom "__GI_stpcpy") hi_module = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

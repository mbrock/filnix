(** A proof about hi_atexit.c has to run the program together with the
    glibc code it calls, so it needs that whole program as one Rocq
    module. This file decodes the linked term that hi_atexit/code.sh
    printed into that module and lays out its globals, the addresses
    every symbol gets in the program's initial memory.

    | Name | Meaning |
    |---|---|
    | [hi_module] | the decoded module |
    | [hi_decodes] | the term decodes to it |
    | [hi_globals], [hi_layout] | the globals its initial memory places | *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Transport Semantics Run.
From Glibc Require Import HiAtexitTerm.
Import ListNotations.
Open Scope string_scope.

(** The linked module. *)
Definition hi_module : module := Eval vm_compute in
  match decode_module hi_atexit_term with Some md => md | None => [] end.

(** The term decodes to [hi_module]. *)
Lemma hi_decodes : decode_module hi_atexit_term = Some hi_module.
Proof. vm_compute. reflexivity. Qed.

(** The module's symbols, as laying it out places them. *)
Definition hi_globals : list (name * ptr) := Eval vm_compute in
  match initial_memory hi_module with Some (g, _) => g | None => [] end.

(** Laying out the module gives [hi_globals]. *)
Lemma hi_layout : option_map fst (initial_memory hi_module) = Some hi_globals.
Proof. vm_compute. reflexivity. Qed.

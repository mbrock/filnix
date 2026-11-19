(** This file checks the entry points of glibc's linked option parser.
    The captured objects retain the real short-option scanner, long-option
    matcher, permutation loops and diagnostic calls. These lookup facts
    identify bodies; they do not prove that a parser call is safe. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Semantics.
From Glibc Require Import GetoptCode Unit_posix_getopt_os Unit_posix_getopt1_os.
Import ListNotations.
Open Scope string_scope.

(** This module contains the parser and its public wrappers. *)
Definition getopt_module : module := GetoptCode.getopt_module.

(** The reentrant scanner owns its caller-supplied private state. *)
Definition glibc_getopt_internal_r : func := Unit_posix_getopt_os.fn__getopt_internal_r.
(** The global wrapper transfers the public option cells into private state. *)
Definition glibc_getopt_internal : func := Unit_posix_getopt_os.fn__getopt_internal.
(** The long-option entry selects ordinary rather than long-only parsing. *)
Definition glibc_getopt_long : func := Unit_posix_getopt1_os.fn_getopt_long.
(** The internal matcher checks exact names and permitted abbreviations. *)
Definition glibc_process_long_option : func := Unit_posix_getopt_os.fn_glibc_getopt'23process_long_option.

(** The linked module resolves the scanner to its captured function. *)
Lemma getopt_internal_r_lookup :
  find_direct (TAtom "_getopt_internal_r") getopt_module = Some (Defined glibc_getopt_internal_r).
Proof. reflexivity. Qed.
(** The global wrapper is present in the linked module. *)
Lemma getopt_internal_lookup :
  find_direct (TAtom "_getopt_internal") getopt_module = Some (Defined glibc_getopt_internal).
Proof. reflexivity. Qed.
(** The exported long-option entry is present in the linked module. *)
Lemma getopt_long_lookup :
  find_direct (TAtom "getopt_long") getopt_module = Some (Defined glibc_getopt_long).
Proof. reflexivity. Qed.
(** The local long-option matcher retains its translation-unit prefix. *)
Lemma getopt_process_long_lookup :
  find_direct (TAtom "glibc_getopt#process_long_option") getopt_module = Some (Defined glibc_process_long_option).
Proof. reflexivity. Qed.

Global Opaque getopt_module glibc_getopt_internal_r glibc_getopt_internal
  glibc_getopt_long glibc_process_long_option.

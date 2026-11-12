(** This file decodes glibc's option parser and checks its linked entry points.
    The generated slices retain the real short-option scanner, long-option
    matcher, permutation loops and diagnostic calls. These lookup facts
    identify bodies; they do not prove that a parser call is safe. *)

From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Transport Semantics.
From Glibc Require Import GetoptTerm.
Import ListNotations.
Open Scope string_scope.

(** The decoded module contains both captured getopt translation units. *)
Definition getopt_module : module := Eval vm_compute in
  match decode_module getopt_term with Some md => md | None => [] end.

(** Every linked item belongs to the supported checked-IR syntax. *)
Lemma getopt_decodes : decode_module getopt_term = Some getopt_module.
Proof. vm_compute. reflexivity. Qed.

(** Function extraction uses the same linked names as the final program. *)
Definition getopt_fn (n : string) : func :=
  match find_direct (TAtom n) getopt_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** The reentrant scanner owns its caller-supplied private state. *)
Definition glibc_getopt_internal_r : func := Eval vm_compute in getopt_fn "_getopt_internal_r".
(** The global wrapper transfers the public option cells into private state. *)
Definition glibc_getopt_internal : func := Eval vm_compute in getopt_fn "_getopt_internal".
(** The long-option entry selects ordinary rather than long-only parsing. *)
Definition glibc_getopt_long : func := Eval vm_compute in getopt_fn "getopt_long".
(** The internal matcher checks exact names and permitted abbreviations. *)
Definition glibc_process_long_option : func := Eval vm_compute in getopt_fn "glibc_getopt#process_long_option".

(** The scanner lookup cannot silently select the empty fallback body. *)
Lemma getopt_internal_r_lookup :
  find_direct (TAtom "_getopt_internal_r") getopt_module = Some (Defined glibc_getopt_internal_r).
Proof. vm_compute. reflexivity. Qed.
(** The global wrapper is present in the linked module. *)
Lemma getopt_internal_lookup :
  find_direct (TAtom "_getopt_internal") getopt_module = Some (Defined glibc_getopt_internal).
Proof. vm_compute. reflexivity. Qed.
(** The exported long-option entry is present in the linked module. *)
Lemma getopt_long_lookup :
  find_direct (TAtom "getopt_long") getopt_module = Some (Defined glibc_getopt_long).
Proof. vm_compute. reflexivity. Qed.
(** The local long-option matcher retains its translation-unit prefix. *)
Lemma getopt_process_long_lookup :
  find_direct (TAtom "glibc_getopt#process_long_option") getopt_module = Some (Defined glibc_process_long_option).
Proof. vm_compute. reflexivity. Qed.

Global Opaque getopt_module glibc_getopt_internal_r glibc_getopt_internal
  glibc_getopt_long glibc_process_long_option.

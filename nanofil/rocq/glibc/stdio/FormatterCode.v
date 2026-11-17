(** This module decodes the complete captured formatter, including its
    unsupported paths. The decoding equality is not a formatting contract.
    stdio/code.sh regenerates this file from the pinned capture. Do not edit. *)
From Stdlib Require Import String ZArith List.
From Glibc Require Import CodePrelude FormatterTerm.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Nanofil Require Import Syntax Transport Semantics.

(** The module, decoded. *)
Definition formatter_module : module := Eval vm_compute in
  match decode_module formatter_term with Some md => md | None => [] end.

(** The term decodes to the module. *)
Lemma formatter_decodes : decode_module formatter_term = Some formatter_module.
Proof. vm_compute. reflexivity. Qed.

(** Lookup selects the named function, with an empty fallback when it is absent. *)
Definition formatter_fn (n : string) : func :=
  match find_direct (TAtom n) formatter_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** glibc's `__vfprintf_internal`. *)
Definition glibc_vfprintf_internal : func := Eval vm_compute in formatter_fn "__vfprintf_internal".
(** The module defines `__vfprintf_internal` as [glibc_vfprintf_internal]. *)
Lemma glibc_vfprintf_internal_found : find_direct (TAtom "__vfprintf_internal") formatter_module = Some (Defined glibc_vfprintf_internal).
Proof. vm_compute. reflexivity. Qed.

(** glibc's `__printf_buffer`. *)
Definition glibc_printf_buffer : func := Eval vm_compute in formatter_fn "__printf_buffer".
(** The module defines `__printf_buffer` as [glibc_printf_buffer]. *)
Lemma glibc_printf_buffer_found : find_direct (TAtom "__printf_buffer") formatter_module = Some (Defined glibc_printf_buffer).
Proof. vm_compute. reflexivity. Qed.

(** glibc's `glibc_vfprintf_internal#__printf_buffer_putc`. *)
Definition glibc_printf_buffer_putc : func := Eval vm_compute in formatter_fn "glibc_vfprintf_internal#__printf_buffer_putc".
(** The module defines `glibc_vfprintf_internal#__printf_buffer_putc` as [glibc_printf_buffer_putc]. *)
Lemma glibc_printf_buffer_putc_found : find_direct (TAtom "glibc_vfprintf_internal#__printf_buffer_putc") formatter_module = Some (Defined glibc_printf_buffer_putc).
Proof. vm_compute. reflexivity. Qed.

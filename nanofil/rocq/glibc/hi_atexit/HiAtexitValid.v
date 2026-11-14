(** nanofil's validator must accept a module before the compiler
    trusts its checks, and the linked hi_atexit program is no
    exception. This file runs the validator on the whole program,
    hi_atexit.c with its 32 glibc units, and shows that it accepts it. *)

From Glibc Require Import GlibcTactics.
From Nanofil Require Import Syntax ValidFast.
From Glibc Require Import HiAtexitModule.

(** [valid_fast] accepts [hi_module]. *)
Lemma hi_valid : valid_fast hi_module = Some true.
Proof. vm_cast_no_check (eq_refl (Some true)). Qed.

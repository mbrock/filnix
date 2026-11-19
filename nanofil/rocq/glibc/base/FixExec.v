(** Proofs that use the abstract interpreter share its soundness theorem for the program logic. *)
From Nanofil Require Import AbsSound.
From Glibc Require Import Fix.

Module AS0 := AbsSoundOn R LG0.

(** The loader checks the zero runs in each global initializer. The
    generated image checks consecutive groups of items separately, and
    this lemma combines those results in link order. *)

From Stdlib Require Import List Bool.
From Nanofil Require Import Syntax.
From Glibc Require Import HelloImageEraseMem.
Open Scope list_scope.

(** The zero-run check holds for a joined module when it holds for each part. *)
Lemma zero_nonneg_app a b : zero_nonneg (a ++ b) = zero_nonneg a && zero_nonneg b.
Proof. apply forallb_app. Qed.

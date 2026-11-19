(** The option scanner branches on signed integers in registers. These tactics
    decide branches once the proof supplies bounds on the register values. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Run Logic.
From Glibc Require Import Fix GlibcTactics.
Import Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** Signed comparison of a nonnegative 32-bit integer reads its value. *)
Lemma sx_small x : 0 <= x < 2 ^ 31 -> sign_extension (2 ^ 32) (2 ^ 31) (x mod 2 ^ 32) = x.
Proof.
  intros H. unfold sign_extension. rewrite !Z.mod_small; try lia.
  rewrite (proj2 (Z.leb_gt _ _)); lia.
Qed.

(** Signed comparisons of nonnegative 32-bit values read the values. *)
Ltac sx := repeat match goal with |- context [sign_extension (2 ^ 32) (2 ^ 31) (?x mod 2 ^ 32)] =>
  rewrite (sx_small x); [|lia] end.

(** This tactic decides a branch whose condition arithmetic settles. *)
Ltac brz :=
  iApply wp_branch; [vx | iNext]; sx;
  repeat match goal with
    | |- context [?x <? ?y] =>
        first [rewrite (proj2 (Z.ltb_lt x y)); [|lia] | rewrite (proj2 (Z.ltb_ge x y)); [|lia]]
    | |- context [?x =? ?y] =>
        first [rewrite (proj2 (Z.eqb_eq x y)); [|lia] | rewrite (proj2 (Z.eqb_neq x y)); [|lia]]
    end;
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** This tactic decides a branch whose condition has become closed. *)
Ltac close_br :=
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

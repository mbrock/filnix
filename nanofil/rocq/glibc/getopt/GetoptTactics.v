(** The option scanner branches on signed integers in registers. These tactics
    decide branches once the proof supplies bounds on the register values. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Ops Symbolic Semantics Run Logic.
From Glibc Require Import WordString GlibcEnv OsTactics Fix GlibcTactics.
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

(** Sign extension keeps a nonnegative signed 32-bit value. *)
Lemma sx_nonneg x : 0 <= x < 2 ^ 31 -> sign_extension (2 ^ 32) (2 ^ 31) x = x.
Proof. intros H. unfold sign_extension. rewrite Z.mod_small; [|lia]. rewrite (proj2 (Z.leb_gt _ _)); lia. Qed.

(** This tactic unfolds a precomputed block that the goal executes. *)
Ltac unfold_blk := repeat match goal with |- context [b_insts ?B] => progress unfold B end.

(** This tactic reduces an index computation of the form base plus offset, scaled by eight. *)
Ltac idx x := norm; rewrite (sx_nonneg x); [|lia]; change (2 ^ (3 mod 64)) with 8; norm.

(** A run of assignments to loop names keeps the lookups at names that avoid them. *)
Ltac xkeep := repeat (match goal with H : avoids _ ?Wl = true |- _ => apply keeps_put_avoid with (W := Wl); [vm_compute; reflexivity | exact H |] end);
  first [apply keeps_refl | assumption].

(** This tactic computes a value whose arithmetic needs range facts. *)
Ltac vxn :=
  cbn -[put];
  repeat match goal with
    |- context [lookup ?k ?E] =>
      let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H
    end;
  unwrap; reflexivity.

(** This tactic shows that an address inside the table keeps its eight-byte alignment. *)
Ltac al8 := unfold raw_address, ptr_add; cbn [ptr_addr]; repeat (rewrite (Z.mod_small _ (2 ^ 64)); [|lia]); Z.div_mod_to_equations; lia.

(** This tactic computes call arguments whose last one is the option character c. *)
Ltac vxc c := cbn -[put];
  repeat match goal with |- context [lookup ?k ?E] =>
    let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H end;
  cbn; rewrite (Z.mod_small c); [reflexivity | lia].

(** This tactic rebuilds an integer field from its rewritten bytes. *)
Ltac icell := iSplit; [iPureIntro; lia | iAssumption].

(** This tactic reads a lookup through names that a report keeps. *)
Ltac viakeep H := erewrite (keeps_in _ _ _ _ H); [lk_prove | cbn; tauto].

(** A later block may read a register that several earlier blocks preserved.
    Follow each preservation fact back to the environment that supplied the value. *)
Ltac kept_lookup :=
  first [assumption | match goal with
    | H : keeps ?ks ?before ?after |- lookup ?k ?after = _ =>
        rewrite (keeps_in ks k before after H); [clear H; kept_lookup | cbn; tauto]
    end].

(** This tactic closes a bound on a raw address inside a shared string. *)
Ltac rawa := unfold raw_address, ptr_add; cbn [ptr_addr]; rewrite ?(Z.mod_small _ (2 ^ 64)); lia.

(** A run of assignments to other names keeps the listed lookups. *)
Ltac keep := repeat (apply keeps_put; [vm_compute; reflexivity |]); first [apply keeps_refl | assumption].

(** This tactic proves a lookup through assignments and kept lookups. *)
Ltac lk :=
  first [ apply Symbolic.lookup_after_put_same
        | eapply lookup_put_miss; [vm_compute; reflexivity | lk]
        | eassumption
        | match goal with H : lookup ?k ?E = lookup ?k ?E1 |- lookup ?k ?E = _ => rewrite H; lk end ].

(** String scans carry a pointer through several words of memory. These tactics
    reduce address arithmetic and find the temporary that holds the next pointer. *)

From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Run Symbolic.
Open Scope Z_scope.

(** The tactic [unwrap] removes 64-bit and 32-bit modulo wraps whenever
    `lia` can prove the operand is already in range. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|lia]
    end.

(** The tactic [clear_junk] discards non-arithmetic hypotheses from the
    context so `lia` runs quickly on the remaining bounds. *)
Ltac clear_junk :=
  repeat match goal with
    H : ?T |- _ =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | and (Z.le _ _) _ => fail
      | lt _ _ => fail | le _ _ => fail
      | _ => clear H
      end
    end.
(** The tactic [pow_closed] evaluates closed shift multipliers of the
    form `2 ^ (n mod m)` by computation. *)
Ltac pow_closed :=
  repeat match goal with |- context [2 ^ (?n mod ?m)] =>
    let v := fresh "v" in let Ev := fresh "Ev" in
    remember (2 ^ (n mod m)) as v eqn:Ev; vm_compute in Ev; subst v end.
(** Address arithmetic and bounds checks leave integer side conditions
    at every step. The tactic [arith] strips non-arithmetic hypotheses,
    evaluates closed shift powers, removes redundant modulo wraps, and
    solves the remaining inequalities with `lia`. *)
Ltac arith := cbn [ptr_addr ptr_cap extension]; unfold raw_address; clear_junk; pow_closed; unwrap;
  first [lia | Z.div_mod_to_equations; lia].

(** The tactic [close_if] reduces a branch target when its boolean
    condition evaluates to true or false. *)
Ltac close_if :=
  match goal with |- context [edge_label (if ?c then _ else _)] =>
    first [change c with true | change c with false]
  end; cbn [edge_label].

(** The tactic [look] resolves the lookup of `v4` in the environment
    after earlier temporary assignments in the block. *)
Ltac look H := repeat (rewrite lookup_after_put_other; [|reflexivity]); exact H.

(** The tactic [set_int] rewrites the integer stored in temporary `name`
    to its symbolic expression v. *)
Ltac set_int name v :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by first [reflexivity | arith] end.
(** The tactic [set_ptr] rewrites the address of the pointer stored in
    temporary `name` to its symbolic expression v. *)
Ltac set_ptr name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by first [reflexivity | arith] end.

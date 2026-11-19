(** Stream proofs discharge bounds involving the layout and flags of a glibc FILE. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Glibc Require Import GlibcTactics OsTactics FileInv.

(** A pure premise left by an [iApply], by arithmetic or a lookup; the
    proof-mode goal is left alone, so [try side] after an [iApply]
    takes all its premises. *)
Ltac libio_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | _ => first [done | lia | unfold file_size; lia | unfold io_is_appending; lia | cbn; lia | lk_prove]
  end.

(** A pure premise of a write-loop rule, the [side] of v with
    [lookups] for environments past the call. *)
Ltac wside :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | _ => first [done | unfold file_size; lia | lia | cbn; lia | lookups; first [reflexivity | do 2 f_equal; arith]]
  end.

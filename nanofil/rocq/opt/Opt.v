(** This module implements the top-level middle-end optimization driver,
    matching `opt.pl`. It selects an ordered pass sequence from an optimization
    level or explicit pass subset and runs each pass over unchecked,
    ordinary-address IR while leaving checked modules and modules already
    containing local storage unchanged.

    Pass ordering stays fixed as `[inline, promote, copy, simplify,
    local_storage]` because `local_storage` introduces named local objects that
    earlier passes do not consume. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Ops Semantics.
From Backend Require Import Pizlonate.
From Opt Require Import OptIr OptPromote OptCopy Simplify Inline LocalStorage.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Optimization options and passes

    The datatypes below represent the option forms accepted by `opt:optimize/3`
    and `opt:optimize_pass/3`. *)

(** Inlining selection for `o1(Inline, Simplify)`. *)
Inductive opt_inline : Type :=
| InlNone
| InlSmall
| InlWide (attrs : list (string * string)).

(** Simplification selection for `o1(Inline, Simplify)`. *)
Inductive opt_simplify : Type :=
| SimpNone
| SimpFull.

(** Individual middle-end passes accepted by [optimize_pass]. *)
Inductive opt_pass : Type :=
| PassInline
| PassInlineSimplified
| PassInlineWide (prep_simplified : bool) (attrs : list (string * string))
| PassPromote
| PassCopy
| PassSimplify
| PassLocalStorage.

(** Top-level optimization selections matching `opt:optimize/3`. *)
Inductive opt_level : Type :=
| OptO0
| OptO1
| OptO1Small
| OptO1Full (inl : opt_inline) (simp : opt_simplify)
| OptPasses (passes : list opt_pass).

(** ## Pass ordering and dispatch

    Explicit pass lists must form an increasing subsequence of the canonical
    pipeline order, with `inline_simplified` occupying the `inline` slot. *)

(** Mapping a pass to its pipeline slot rank checks ordering without
    duplicating the pass list. *)
Definition pass_rank (p : opt_pass) : nat :=
  match p with
  | PassInline | PassInlineSimplified | PassInlineWide _ _ => 0%nat
  | PassPromote => 1%nat
  | PassCopy => 2%nat
  | PassSimplify => 3%nat
  | PassLocalStorage => 4%nat
  end.

(** Testing whether [ps] is a strictly increasing subsequence of the canonical
    pipeline rejects reordered or repeated passes, matching
    `ordered_passes/2`. *)
Fixpoint passes_ordered (min_rank : nat) (ps : list opt_pass) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      let r := pass_rank p in
      Nat.leb min_rank r && passes_ordered (S r) rest
  end.

(** Computing the selected pass sequence for [opts] matches
    `optimization_passes/2`. *)
Definition optimization_passes (opts : opt_level) : option (list opt_pass) :=
  match opts with
  | OptO0 => Some []
  | OptO1 => Some [PassPromote; PassCopy; PassLocalStorage]
  | OptO1Small => Some [PassInline; PassPromote; PassCopy; PassLocalStorage]
  | OptO1Full inlining simp =>
      let inl_ps :=
        match inlining, simp with
        | InlNone, _ => []
        | InlSmall, SimpNone => [PassInline]
        | InlSmall, SimpFull => [PassInlineSimplified]
        | InlWide attrs, SimpNone => [PassInlineWide false attrs]
        | InlWide attrs, SimpFull => [PassInlineWide true attrs]
        end in
      let simp_ps :=
        match simp with
        | SimpNone => []
        | SimpFull => [PassSimplify]
        end in
      Some (inl_ps ++ [PassPromote; PassCopy] ++ simp_ps ++ [PassLocalStorage])
  | OptPasses ps =>
      if passes_ordered 0%nat ps then Some ps else None
  end.

(** Running one named pass on unchecked, non-local-storage IR leaves checked
    modules and modules with existing `local_alloc/2` instructions unchanged,
    matching `optimize_pass/3`. *)
Definition optimize_pass (p : opt_pass) (m0 : term) : option term :=
  match m0 with
  | TApp f [TList items] =>
      if negb (f == "module") then None else
      if module_checked items || module_has_local_storage items then Some m0
      else
        match p with
        | PassInline => inline_module_small false m0
        | PassInlineSimplified => inline_module_small true m0
        | PassInlineWide prep attrs => inline_module_wide prep attrs m0
        | PassPromote => promote_module m0
        | PassCopy => copy_module m0
        | PassSimplify => simplify_module m0
        | PassLocalStorage => local_storage_module m0
        end
  | _ => None
  end.

(** Running the full optimization pipeline selected by [opts] folds
    [optimize_pass] across the selected sequence, matching `optimize/3`. *)
Definition optimize (opts : opt_level) (m0 : term) : option term :=
  let* ps := optimization_passes opts in
  fold_left (fun acc p => let* m := acc in optimize_pass p m) ps (Some m0).

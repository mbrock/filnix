#!/usr/bin/env bash
# tests/parse.sh [FILE.v...]: check rocq_syntax.pl against Rocq itself.
# Each file (default: every .v file under nanofil) is compiled as it is,
# then reprinted from its tree with every subterm in parentheses
# (reprint.pl) and compiled again in its place: if the reprint still
# type-checks and its proofs still go through, the grammar read every
# operator at Rocq's precedence and every binder where Rocq puts it. A
# sentence the grammar does not read fails too. Needs swipl and rocq (or
# coqc) with the Stdlib on ROCQPATH, as the flake's nixpkgs gives them:
#   nix shell --impure --expr 'with import (builtins.getFlake (toString ./.)).inputs.nixpkgs {}; [ swi-prolog coq coqPackages.stdlib ]'
# A file in a project (a _RocqProject or _CoqProject above it) is
# compiled with the project's -R/-Q flags, after the files it imports.
# With a _RocqProject, one make compiles the originals and checks the
# reprints, each reprint as soon as its file's imports are compiled.
# PARSE_IN_PLACE=1 compiles the originals where they are, not in a copy;
# nix/rocq.nix uses it with --check to check one theory against the
# compiled objects of its imports.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
coqc=$(command -v rocq >/dev/null && echo "rocq c" || echo coqc)
rocqdep=$(command -v rocq >/dev/null && echo "rocq dep" || echo coqdep)
makefile=$(command -v rocq >/dev/null && echo "rocq makefile" || echo coq_makefile)
jobs=${NIX_BUILD_CORES:-$(nproc 2>/dev/null || echo 1)}
[ "$jobs" -ge 1 ] 2>/dev/null || jobs=1

# project FILE: the directory of the project file above FILE, or FILE's own.
project() {
  local d
  d=$(cd "$(dirname "$1")" && pwd)
  while [ "$d" != / ]; do
    if [ -e "$d/_RocqProject" ] || [ -e "$d/_CoqProject" ]; then echo "$d"; return; fi
    d=$(dirname "$d")
  done
  cd "$(dirname "$1")" && pwd
}

# flags DIR: the project's -R and -Q flags. A directory outside the
# project (rocq/spikes reads ../theories) is the original's, compiled.
flags() {
  local p
  for p in "$1/_RocqProject" "$1/_CoqProject"; do
    [ -e "$p" ] && grep -oE '^-[RQ] +[^ ]+ +[^ ]+' "$p" | outside "$1" | tr '\n' ' ' && return
  done
  echo "-Q . Top"
}
outside() { sed -E "s#^(-[RQ] +)(\.\./)#\1$1/\2#"; }

# order DIR: the project's .v files in the order its project file lists them.
order() {
  local p
  for p in "$1/_RocqProject" "$1/_CoqProject"; do
    [ -e "$p" ] && grep -E '\.v$' "$p" && return
  done
  (cd "$1" && find . -name '*.v' | sed 's|^\./||' | sort)
}

# orig PROJ: where the project's originals are compiled, a copy in the
# run's directory or, with PARSE_IN_PLACE (the model's build), PROJ itself.
orig_of() {
  if [ -n "${PARSE_IN_PLACE-}" ]; then echo "$1"; else echo "$tmp/orig$(echo "$1" | tr / _)"; fi
}

# check N F: reprint F and compile the reprint alone, under the project's
# names, with the original's compiled imports, which is all it needs: its
# reprint can start as soon as they are compiled. The verdict goes to
# $tmp/verdict-N and is printed, a failure's log with it on stderr.
check() {
  local n=$1 f=$2 proj rel orig dir fl i k p l over=
  local -a words args=()
  proj=$(project "$f")
  rel=${f#"$proj"/}
  orig=$(orig_of "$proj")
  fl=$(flags "$proj")
  dir=$tmp/reprint-$n
  mkdir "$dir"
  (cd "$orig" && find . -type d) | (cd "$dir" && xargs mkdir -p)
  read -ra words <<<"$fl"
  for ((i = 0; i + 2 < ${#words[@]}; i += 3)); do
    k=${words[i]} p=${words[i + 1]%/} l=${words[i + 2]}
    case $p in /*) args+=("$k" "$p" "$l") ;; *) args+=("$k" "$orig/$p" "$l") ;; esac
    # The binding F is under names the reprint too, from its own tree.
    case $p in /*) ;; *) if [ "$p" = . ] || [[ $rel == "$p"/* ]]; then
      if [ -z "$over" ] || [ ${#p} -gt ${#over} ]; then over=$p; fi; fi ;; esac
  done
  if [ -n "$over" ]; then
    for ((i = 0; i + 2 < ${#words[@]}; i += 3)); do
      [ "${words[i + 1]%/}" = "$over" ] && args+=("${words[i]}" "$dir/$over" "${words[i + 2]}") && break
    done
  fi
  # Each verdict says how long the reprint took to print and to compile,
  # so a slow gate names its slow files.
  local t0=$EPOCHREALTIME t1 took
  if ! swipl "$here/reprint.pl" "$f" --strict >"$dir/$rel" </dev/null 2>"$tmp/verdict-$n.log"; then
    echo "FAIL $f: the grammar does not read it" >"$tmp/verdict-$n"
  elif t1=$EPOCHREALTIME; (cd "$dir" && $coqc "${args[@]}" "$rel" >"$tmp/verdict-$n.log" 2>&1); then
    took=$(awk -v a="$t0" -v b="$t1" -v c="$EPOCHREALTIME" 'BEGIN { printf "print %.1fs, compile %.1fs", b - a, c - b }')
    echo "ok   $f ($took)" >"$tmp/verdict-$n"
  else
    echo "FAIL $f: the reprint does not compile" >"$tmp/verdict-$n"
    sed -i 's/^/  /' "$tmp/verdict-$n.log"
  fi
  rm -rf "$dir"
  case $(cat "$tmp/verdict-$n") in
    ok*) cat "$tmp/verdict-$n" ;;
    *) cat "$tmp/verdict-$n" "$tmp/verdict-$n.log" >&2 ;;
  esac
}

# pool N...: check those files, up to $jobs at a time.
pool() {
  local n
  for n; do
    while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do wait -n || true; done
    check "$n" "${paths[$n]}" &
  done
  wait
}

# A make recipe's call (below): check one file of this run.
if [ "${1-}" = --check ]; then
  tmp=$PARSE_TMP
  check "$2" "$3"
  exit 0
fi

# build ORIG PROJ: compile a project without a makefile one file at a
# time, in order.
build() {
  local orig=$1 proj=$2 fl v
  echo "build $proj"
  fl=$(flags "$proj")
  while read -r v; do
    (cd "$orig" && $coqc $fl "$v" >"$tmp/log" 2>&1) || {
      echo "skip $proj/$v: it does not compile as it is" >&2
      sed 's/^/  /' "$tmp/log" >&2
    }
  done < <(order "$proj")
}

# --fixtures: only the built-in fixtures below (nix/rocq.nix checks each
# theory in its own derivation).
if [ "${1-}" = --fixtures ]; then
  shift
elif [ $# -eq 0 ]; then
  mapfile -t files < <(cd "$root" && find nanofil -name '*.v' -not -path '*/_build/*' | sort)
  set -- "${files[@]/#/$root/}"
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT


# Compile the Ltac tree too: asymmetric branches expose a wrong scope for
# repeat/try, sequence, choice or dispatch even if a simple proof passes.
mkdir "$tmp/tactics"
cat >"$tmp/tactics/Tactics.v" <<'ROCQ'
From Stdlib Require Import Arith.
Ltac cases H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x eqn:?; cbv beta iota zeta in H; try discriminate H
  end.
Ltac context_case :=
  match goal with
  | H : context [match ?x with _ => _ end] |- _ => destruct x; simpl in H; try discriminate H
  end.
Ltac finish H :=
  lazymatch type of H with
  | ?P /\ ?Q => destruct H as [Hp Hq]; first [exact Hq | exact Hp]
  | _ => exact H
  end.
Ltac from_context :=
  multimatch goal with
  | [ H : ?P /\ ?Q |- ?Q ] => exact (proj2 H)
  end.
(* Local recursion retains its parameters and nested let boundaries. *)
Ltac successor_count n :=
  let rec count x acc :=
    lazymatch x with
    | O => acc
    | S ?k => let next := constr:(S acc) in count k next
    end in
  count n constr:(2).
(* The first in belongs to eval, and the second belongs to let. *)
Ltac computed_count n :=
  let x := eval vm_compute in (n + 3) in
  let y := successor_count x in
  exact y.
Goal nat.
Proof.
  let x := eval cbn [Nat.add] in (2 + 5) in
  let y := successor_count x in
  constr_eq y constr:(9); exact y.
Defined.
Definition counted : nat.
Proof. computed_count 6. Defined.
Goal counted = 11.
Proof. reflexivity. Qed.
Goal forall P Q : Prop, P /\ Q -> Q.
Proof. intros P Q H. finish H. Qed.
Goal forall P Q : Prop, P /\ Q -> Q.
Proof. intros P Q H. from_context. Qed.
Goal forall b : bool, (if b then 1 else 2) = 1 -> b = true.
Proof. intros b H. context_case. reflexivity. Qed.
Goal forall P Q : Prop, P \/ (True /\ Q) -> Q \/ P.
Proof. intros P Q [Hp | (_ & Hq)]; [right; exact Hp | left; exact Hq]. Qed.
Goal True /\ (True /\ True).
Proof. repeat split; exact I. Qed.
Goal True /\ True.
Proof. split || fail; exact I. Qed.
Goal forall n : nat, n = n.
Proof.
  fix IH 1. intros n. assert (Ha := Nat.add_0_r n).
  all: try (rewrite Ha by reflexivity).
  destruct n as [|k] eqn:En; cbn -[Nat.add] in Ha; [reflexivity|].
  (* A comment after a focus bullet. *)
  - reflexivity.
Qed.
Goal forall a b : nat, S a = S b -> a = b.
Proof. intros a b E. injection E as <-. reflexivity. Qed.
Goal forall P : Prop, P -> P /\ True.
Proof. intros P H. split; [exact H|exact I]. Qed.
Goal forall n : nat, n + 0 = n.
Proof. intro n. assert (n + 0 = n) by (apply Nat.add_0_r; auto). assumption. Qed.
(* Numeric prefixes must keep their count and bind before semicolon. *)
Ltac introduce n := do n intro.
Goal forall a b : nat, a = a /\ b = b.
Proof. do 2 intro; split; reflexivity. Qed.
Goal forall a : nat, a = a.
Proof. do 0 intro. intro a. reflexivity. Qed.
Goal True /\ True.
Proof. do 2 split || (split; exact I). Qed.
(* A list selects nonadjacent goals without changing the intervening goal. *)
Goal (1 = 1) /\ ((2 = 2) /\ (3 = 3)).
Proof.
  split; [|split].
  1,3: reflexivity.
  change (2 = 2). reflexivity.
Qed.
(* The first tactic after a focus opener must not be swallowed. *)
Goal True /\ (True /\ True).
Proof.
  split.
  2: { split. 2: { pose proof I as H2. exact H2. } 1: { exact I. } }
  1: { pose proof I as H1. exact H1. }
Qed.
(* context is a match-pattern form, not a parenthesized Gallina term. *)
Ltac goal_case :=
  match goal with
  | |- context [if ?b then _ else _] => destruct b
  end.
Ltac hypothesis_and_goal :=
  match goal with
  | [ H : True |- context [if ?b then _ else _] ] => clear H; destruct b
  end.
Goal forall b : bool, (if b then 0 else 1) = (if b then 0 else 1).
Proof. intro b. goal_case; reflexivity. Qed.
Goal forall b : bool, True -> (if b then 0 else 1) = (if b then 0 else 1).
Proof. intros b H. hypothesis_and_goal; reflexivity. Qed.
ROCQ
set -- "$@" "$tmp/tactics/Tactics.v"

# The forms Rocq prints in proof states. m is the head of the list only if
# "as" binds tighter than "::", so m + n type-checks only when the grammar
# reads it as Rocq does.
mkdir "$tmp/terms"
cat >"$tmp/terms/Terms.v" <<'ROCQ'
From Stdlib Require Import List PArith.
Import ListNotations.
Definition unfolded (l : list nat) : nat :=
  (fix len (xs : list nat) (acc : nat) {struct xs} : nat :=
     match xs with [] => acc | _ :: ys => len ys (S acc) end) l 0.
Definition aliased (l : list nat) : nat :=
  match l with
  | S n as m :: _ => m + n
  | [O as z; _] => z
  | _ => 0
  end.
Definition named : nat := @fst nat bool (pair (A:=nat) (B:=bool) 1 true).
Definition paired : list nat := map (fun '(a, b) => a + b) [(1, 2); (3, 4)].
Definition digits : positive := (xH)~0~1.
Module Type Value.
  Parameter value : nat.
End Value.
Module Left : Value.
  Definition value := 2.
End Left.
Module Right : Value.
  Definition value := 5.
End Right.
Module Sealed : Value := Left.
Definition sealed_value : nat := Sealed.value.
Module Type Sum (A B : Value).
  Parameter total : nat.
  Parameter correct : total = A.value + B.value.
End Sum.
Module Applied : Sum Left Right.
  Definition total := Left.value + Right.value.
  Lemma correct : total = Left.value + Right.value.
  Proof. reflexivity. Qed.
End Applied.
Module Alias := Applied.
Example applied_total : Alias.total = Left.value + Right.value.
Proof. exact Alias.correct. Qed.
ROCQ
set -- "$@" "$tmp/terms/Terms.v"

mkdir "$tmp/by"
cat >"$tmp/by/By.v" <<'ROCQ'
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
Section by_tactics.
Context {Σ : gFunctors}.
Lemma by_sequence : ⊢ (∃ xs : list nat, True ∨ ⌜xs = [1]⌝ : iProp Σ).
Proof. by (iExists []; iLeft). Qed.
Lemma by_ungrouped_sequence : ⊢ (∃ xs : list nat, True ∨ ⌜xs = [1]⌝ : iProp Σ).
Proof. by iExists []; iLeft. Qed.
Lemma by_choice : ⊢ (True : iProp Σ).
Proof. by (fail || iPureIntro). Qed.
Lemma by_ungrouped_choice : ⊢ (True : iProp Σ).
Proof. by fail || iPureIntro. Qed.
Lemma by_dispatch : ⊢ (True ∧ True : iProp Σ).
Proof. by (iSplit; [iPureIntro | iPureIntro]). Qed.
Lemma by_ungrouped_dispatch : ⊢ (True ∧ True : iProp Σ).
Proof. by iSplit; [iPureIntro | iPureIntro]. Qed.
Lemma by_prefix : ⊢ (True : iProp Σ).
Proof. by try iPureIntro. Qed.
Lemma by_do : ⊢ (True : iProp Σ).
Proof. by do 1 iPureIntro. Qed.
Lemma by_first : ⊢ (True : iProp Σ).
Proof. by first [fail | iPureIntro]. Qed.
Lemma by_let : ⊢ (True : iProp Σ).
Proof. by let t := constr:(I) in iPureIntro; exact t. Qed.
Lemma by_match : ⊢ (True : iProp Σ).
Proof. by lazymatch goal with _ => iPureIntro end. Qed.
End by_tactics.
ROCQ
set -- "$@" "$tmp/by/By.v"

# Iris's notations and proof mode, where Iris is on ROCQPATH (the logic
# spikes' check, nix/spikes.nix): each lemma fails to type-check, or its
# proof to go through, if one of its operators is read at another level.
mkdir "$tmp/iris"
if echo 'From iris.heap_lang Require Import proofmode.' >"$tmp/iris/Probe.v" &&
   (cd "$tmp/iris" && $coqc Probe.v) >/dev/null 2>&1; then
  rm -f "$tmp/iris"/Probe.*
  cat >"$tmp/iris/Iris.v" <<'ROCQ'
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import auth excl.
From iris.heap_lang Require Import lang proofmode notation.
Definition testΣ : gFunctors := #[invΣ; gen_heapΣ nat nat].
Section iris.
Context `{!heapGS Σ}.
Implicit Types P Q R : iProp Σ.
(* ∗ binds tighter than -∗, which associates to the right. *)
Lemma sep_wand P Q R : (P ∗ Q -∗ R) ⊢ P -∗ Q -∗ R.
Proof. iIntros "H HP HQ". iApply ("H" with "[$HP $HQ]"). Qed.
(* ▷ and □ take an operand, not the conjunction after it. *)
Lemma later_sep P Q : ▷ P ∗ Q ⊢ Q ∗ ▷ P.
Proof. iIntros "[HP HQ]". iFrame. Qed.
Lemma box_dup P : □ P ⊢ □ P ∗ □ P.
Proof. iIntros "#H". iSplitL; iModIntro; iExact "H". Qed.
Lemma pers_and P Q : <pers> P ∧ Q ⊢ <pers> P.
Proof. apply bi.and_elim_l. Qed.
Lemma löb (P : iProp Σ) : □ (▷ P -∗ P) ⊢ P.
Proof. iIntros "#H". iLöb as "IH". iApply "H". iExact "IH". Qed.
Lemma sep_comm' P Q : P ∗ Q ⊣⊢ Q ∗ P.
Proof. iSplit; iIntros "[A B]"; iFrame. Qed.
Lemma bupd' P : P ==∗ P.
Proof. iIntros "H". by iModIntro. Qed.
Lemma fupd' E P : P ⊢ |={E}=> P.
Proof. iIntros "H". by iModIntro. Qed.
(* An existential's body runs to the end: iExists needs it on top. *)
Lemma ex_sep (Φ : nat → iProp Σ) P : (∃ n, Φ n) ∗ P -∗ ∃ n, Φ n ∗ P.
Proof. iIntros "[[%n H] HP]". iExists n. iFrame. Qed.
Lemma all_zero (Φ : nat → iProp Σ) : (∀ n, Φ n) ⊢ Φ 0.
Proof. iIntros "H". iApply "H". Qed.
Lemma pure_sep (φ : Prop) P : φ → P ⊢ ⌜φ⌝ ∗ P.
Proof. iIntros (Hφ) "HP". iSplitR; [by iPureIntro | iExact "HP"]. Qed.
Lemma pure_destruct (φ : Prop) P : ⌜φ ∧ True⌝ ∗ P ⊢ P ∗ ⌜φ⌝.
Proof. iIntros "[%Hφ HP]". iDestruct "HP" as "HP". iFrame. iPureIntro. apply Hφ. Qed.
Lemma inv_open N P E : ↑N ⊆ E → inv N P ⊢ |={E, E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N, E}=∗ True).
Proof. iIntros (?) "#HI". iApply (inv_acc with "HI"). done. Qed.
Lemma frac (ℓ : loc) (q : Qp) (v : val) : ℓ ↦{#q} v ∗ ℓ ↦□ v ⊢ ℓ ↦□ v ∗ ℓ ↦{#q} v.
Proof. iIntros "[H1 H2]". iFrame. Qed.
Lemma wp_frame' P e Φ : P ∗ WP e {{ Φ }} ⊢ WP e {{ v, P ∗ Φ v }}.
Proof. iIntros "[HP Hwp]". iApply (wp_wand with "Hwp"). iIntros (v) "HΦ". iFrame. Qed.
Lemma wp_masks e E Φ : WP e @ NotStuck; E {{ Φ }} ⊢ WP e @ E {{ v, Φ v }}.
Proof. iIntros "H". iExact "H". Qed.
Lemma load_spec (ℓ : loc) (v : val) : {{{ ℓ ↦ v }}} ! #ℓ {{{ RET v; ℓ ↦ v }}}.
Proof. iIntros (Φ) "Hl HΦ". wp_load. iApply "HΦ". iExact "Hl". Qed.
Lemma alloc_spec : {{{ True }}} ref #1 {{{ ℓ, RET #ℓ; ℓ ↦ #1 }}}.
Proof. iIntros (Φ) "_ HΦ". wp_alloc ℓ as "Hl". iApply "HΦ". iExact "Hl". Qed.
Lemma big_list (l : list nat) (Φ : nat → iProp Σ) : ([∗ list] k ↦ x ∈ l, Φ x) ⊢ [∗ list] x ∈ l, Φ x.
Proof. iIntros "H". iExact "H". Qed.
Lemma big_map (m : gmap nat nat) (Φ : nat → nat → iProp Σ) P :
  ([∗ map] k↦x ∈ m, Φ k x) ∗ P ⊢ P ∗ ([∗ map] k ↦ x ∈ m, Φ k x).
Proof. iIntros "[H HP]". iFrame. Qed.
Lemma big_set (X : gset nat) (l1 l2 : list nat) (Φ : nat → iProp Σ) (Ψ : nat → nat → iProp Σ) (Ps : list (iProp Σ)) :
  ([∗ set] x ∈ X, Φ x) ∗ ([∗ list] x;y ∈ l1;l2, Ψ x y) ∗ [∗] Ps ⊢ [∗] Ps ∗ ([∗ set] x ∈ X, Φ x).
Proof. iIntros "(H1 & _ & H3)". iFrame. Qed.
Lemma own_excl `{!inG Σ (exclR unitO)} γ : own γ (Excl ()) ⊢ |==> own γ (Excl ()).
Proof. iIntros "H". by iModIntro. Qed.
Lemma auth_split `{!inG Σ (authR natUR)} γ (n : nat) : own γ (● n ⋅ ◯ n) ⊢ own γ (● n) ∗ own γ (◯ n).
Proof. iIntros "[Ha Hf]". iFrame. Qed.
Lemma specialize (Φ : nat → iProp Σ) P : (∀ n, P -∗ Φ n) ∗ P ⊢ Φ 1.
Proof. iIntros "[H HP]". iApply ("H" $! 1 with "HP"). Qed.
Lemma destruct_ex (Φ : nat → iProp Σ) : (∃ n, ⌜n = 1⌝ ∗ Φ n) ⊢ Φ 1.
Proof. iIntros "H". iDestruct "H" as (n) "[%Hn H]". subst n. iExact "H". Qed.
Lemma mod_intro P : (|==> P) ⊢ |==> P ∗ True.
Proof. iIntros "H". iMod "H" as "H". iModIntro. iSplitL "H"; [iExact "H" | done]. Qed.
(* An update's later and its count bind into the arrow, not the operand. *)
Lemma step_wand E P Q n : (P ={E}▷=∗^n Q) ∗ P ⊢ |={E}▷=>^n Q.
Proof. iIntros "[H HP]". iApply ("H" with "HP"). Qed.
Lemma step_one E P : (|={E}▷=> P) ⊢ |={E}▷=> P.
Proof. iIntros "H". iExact "H". Qed.
Lemma laters n P Q : ▷^n P ∗ Q ⊢ Q ∗ ▷^n P.
Proof. iIntros "[A B]". iFrame. Qed.
Lemma credits n : £ (S n) ∗ £ n ⊢ £ n ∗ £ (S n).
Proof. iIntros "[A B]". iFrame. Qed.
Lemma ghost_elems `{!ghost_mapG Σ nat nat} γ (k v : nat) (q : Qp) :
  k ↪[γ]{#q} v ∗ k ↪[γ]□ v ⊢ k ↪[γ]□ v ∗ k ↪[γ]{#q} v.
Proof. iIntros "[A B]". iFrame. Qed.
End iris.
(* ⋅ binds tighter than ≼{n}; the index is the relation's. *)
Lemma included_op {A : cmra} n (x : A) : x ≼{n} x ⋅ x.
Proof. by exists x. Qed.
Lemma dist_refl' {A : ofe} n (x : A) : x ≡{n}≡ x.
Proof. reflexivity. Qed.
Lemma update_refl {A : cmra} (x : A) : x ~~> x.
Proof. reflexivity. Qed.
Lemma valid_unit n : ✓{n} (ε : natUR) ∧ ✓ (ε : natUR).
Proof. split; [apply ucmra_unit_validN | apply ucmra_unit_valid]. Qed.
Record holds := { holds_at : nat → nat → Prop }.
Definition always : holds := {| holds_at n x := n = n ∧ x = x |}.
Lemma lookup_ins (m : gmap nat nat) k v : <[k := v]> m !! k = Some v.
Proof. apply lookup_insert_Some. left. split; reflexivity. Qed.
Lemma projections (p : nat * nat) (ps : list (nat * nat)) : p.1 :: ps.*1 = (fst <$> p :: ps).
Proof. reflexivity. Qed.
Definition twice : nat → nat := λ n, n + n.
Definition dfun : ofe := nat -d> nat -d> natO.
Definition nfun : ofe := natO -n> natO -n> natO.
Definition dollar : nat := S $ S $ 0.
Definition stuck_p (s : stuckness) : Prop := if s is NotStuck then True else False.
(* ∘ binds tighter than =, ¬ takes the existential after it. *)
Lemma compose_snd (p : nat * (nat * nat)) : (fst ∘ snd) p = p.2.1 ∧ ¬ ∃ n : nat, n < 0.
Proof. split; [reflexivity | intros [n Hn]; inversion Hn]. Qed.
ROCQ
  set -- "$@" "$tmp/iris/Iris.v"
fi

# Each project with a _RocqProject compiles its originals and checks its
# files' reprints in one make: a reprint is a target that depends on the
# file's imports, so it starts as soon as they are compiled, beside the
# compiles still running. Other projects (the fixtures above) compile one
# file at a time, then check their files.
declare -a paths=() projects=()
declare -A seen=()
for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  paths+=("$f")
  proj=$(project "$f")
  if [ -z "${seen[$proj]-}" ]; then
    seen[$proj]=1
    projects+=("$proj")
    orig=$(orig_of "$proj")
    if [ "$orig" != "$proj" ]; then
      # Preserve checked objects' timestamps when the Nix model supplies
      # them; make still builds the originals in a source-only checkout.
      cp -rp "$proj" "$orig"
      for p in "$orig/_RocqProject" "$orig/_CoqProject"; do
        if [ -e "$p" ]; then outside "$proj" <"$p" >"$p.abs" && mv "$p.abs" "$p"; fi
      done
    fi
  fi
done
declare -a later=() sequential=()
for proj in "${projects[@]}"; do
  orig=$(orig_of "$proj")
  declare -A listed=()
  if [ -e "$orig/_RocqProject" ] &&
     (cd "$orig" && $makefile -f _RocqProject -o Makefile.parse >/dev/null 2>&1 &&
      $rocqdep -f _RocqProject >"$tmp/deps" 2>/dev/null); then
    while read -r v; do listed[$v]=1; done < <(order "$proj")
    goals=()
    {
      for n in "${!paths[@]}"; do
        f=${paths[$n]}
        [ "$(project "$f")" = "$proj" ] || continue
        rel=${f#"$proj"/}
        if [ -z "${listed[$rel]-}" ]; then later+=("$n"); continue; fi
        # Its imports: the .vo prerequisites rocq dep gives its .vo.
        printf 'reprint-%s: %s\n' "$n" "$(awk -v t="${rel%.v}.vo" '$1 == t {
          for (i = 2; i <= NF; i++) if ($i ~ /\.vo$/ && $i != t) print $i }' "$tmp/deps" | tr '\n' ' ')"
        printf '\t@bash %q --check %s %q\n' "$here/parse.sh" "$n" "$f"
        goals+=("reprint-$n")
      done
      for v in "${!listed[@]}"; do goals+=("${v%.v}.vo"); done
      echo "parse-all: ${goals[*]}"
      echo ".PHONY: parse-all $(printf '%s\n' "${goals[@]}" | grep '^reprint-' | tr '\n' ' ')"
    } >"$orig/Makefile.reprint"
    echo "build and reprint $proj with -j$jobs"
    (cd "$orig" && PARSE_TMP=$tmp make -k -j"$jobs" -f Makefile.parse -f Makefile.reprint parse-all) ||
      echo "make: an original of $proj does not compile; the reprints of its importers are not checked" >&2
  else
    sequential+=("$proj")
  fi
  unset listed
done
for proj in "${sequential[@]}"; do
  build "$(orig_of "$proj")" "$proj"
  for n in "${!paths[@]}"; do [ "$(project "${paths[$n]}")" = "$proj" ] && later+=("$n"); done
done
pool "${later[@]}"

status=0
for n in "${!paths[@]}"; do
  if [ ! -e "$tmp/verdict-$n" ]; then
    echo "FAIL ${paths[$n]}: not checked, since a file it imports does not compile" >&2
    status=1
  elif ! grep -q '^ok' "$tmp/verdict-$n"; then
    status=1
  fi
done
exit $status

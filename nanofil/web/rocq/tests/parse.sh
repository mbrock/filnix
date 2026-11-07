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
# compiled with the project's -R/-Q flags, after the files listed before
# it, so a development whose files import each other is checked in order.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
if [ $# -eq 0 ]; then
  mapfile -t files < <(cd "$root" && find nanofil -name '*.v' -not -path '*/_build/*' | sort)
  set -- "${files[@]/#/$root/}"
fi
coqc=$(command -v rocq >/dev/null && echo "rocq c" || echo coqc)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
status=0

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

# flags DIR: the project's -R and -Q flags.
flags() {
  local p
  for p in "$1/_RocqProject" "$1/_CoqProject"; do
    [ -e "$p" ] && grep -oE '^-[RQ] +[^ ]+ +[^ ]+' "$p" | tr '\n' ' ' && return
  done
  echo "-Q . Top"
}

# order DIR: the project's .v files in the order its project file lists them.
order() {
  local p
  for p in "$1/_RocqProject" "$1/_CoqProject"; do
    [ -e "$p" ] && grep -E '\.v$' "$p" && return
  done
  (cd "$1" && find . -name '*.v' | sed 's|^\./||' | sort)
}

# build ORIG PROJ: compile the project's files in ORIG, the project file's
# makefile in parallel where there is one, else one at a time in order.
jobs=${NIX_BUILD_CORES:-$(nproc 2>/dev/null || echo 1)}
[ "$jobs" -ge 1 ] 2>/dev/null || jobs=1
makefile=$(command -v rocq >/dev/null && echo "rocq makefile" || echo coq_makefile)
build() {
  local orig=$1 proj=$2 fl v
  echo "build $proj with -j$jobs"
  if [ -e "$orig/_RocqProject" ] &&
     (cd "$orig" && $makefile -f _RocqProject -o Makefile.parse >/dev/null 2>&1 &&
      make -j"$jobs" -f Makefile.parse >"$tmp/log" 2>&1); then
    return
  fi
  fl=$(flags "$proj")
  while read -r v; do
    (cd "$orig" && $coqc $fl "$v" >"$tmp/log" 2>&1) || {
      echo "skip $proj/$v: it does not compile as it is" >&2
      sed 's/^/  /' "$tmp/log" >&2
    }
  done < <(order "$proj")
}

# check N F: reprint F in a copy of its compiled project and compile the
# reprint there; the verdict goes to $tmp/verdict-N, its log after it.
check() {
  local n=$1 f=$2 proj rel fl key orig dir
  proj=$(project "$f")
  rel=${f#"$proj"/}
  fl=$(flags "$proj")
  key=$(echo "$proj" | tr / _)
  orig=$tmp/orig$key
  dir=$tmp/reprint-$n
  cp -r "$orig" "$dir"
  if ! swipl "$here/reprint.pl" "$f" --strict >"$dir/$rel" </dev/null 2>"$tmp/verdict-$n.log"; then
    echo "FAIL $f: the grammar does not read it" >"$tmp/verdict-$n"
  elif (cd "$dir" && $coqc $fl "$rel" >"$tmp/verdict-$n.log" 2>&1); then
    echo "ok   $f" >"$tmp/verdict-$n"
  else
    echo "FAIL $f: the reprint does not compile" >"$tmp/verdict-$n"
    sed -i 's/^/  /' "$tmp/verdict-$n.log"
  fi
  rm -rf "$dir"
}

# report N: print check N's verdict as it finishes; a failure's log goes
# to stderr with it.
report() {
  local v
  v=$(cat "$tmp/verdict-$1")
  case $v in
    ok*) echo "$v" ;;
    *) { echo "$v"; cat "$tmp/verdict-$1.log"; } >&2; status=1 ;;
  esac
}

# Each project is compiled once; then every file's reprint is checked in
# its own copy, up to $jobs at a time.
declare -a paths=()
for f in "$@"; do
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  paths+=("$f")
  proj=$(project "$f")
  orig=$tmp/orig$(echo "$proj" | tr / _)
  if [ ! -d "$orig" ]; then
    cp -r "$proj" "$orig"
    build "$orig" "$proj"
  fi
done
declare -A running=()
for n in "${!paths[@]}"; do
  while [ "${#running[@]}" -ge "$jobs" ]; do
    wait -n || true
    for k in "${!running[@]}"; do
      if ! kill -0 "${running[$k]}" 2>/dev/null; then report "$k"; unset "running[$k]"; fi
    done
  done
  check "$n" "${paths[$n]}" &
  running[$n]=$!
done
wait || true
for k in "${!running[@]}"; do report "$k"; done
exit $status

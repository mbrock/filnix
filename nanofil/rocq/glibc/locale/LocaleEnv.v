(** GNU Hello calls `c: setlocale(LC_ALL, "")`, and glibc then picks
    each category's locale from the process environment. A name other
    than "C" or "POSIX" sends glibc into its locale archive and locale
    files, which open, map and parse files and may load gconv modules.
    The OS model has no files, so Hello's safety proof covers only the
    environments in which every category resolves to the built-in C
    locale. This module states that condition as one premise of the
    safety theorem.

    The premise follows the code of user glibc 2.44. The function
    `c: _nl_find_locale` in locale/findlocale.c handles a category whose
    requested name is empty. It reads `c: getenv("LC_ALL")`, then the
    variable named after the category, then `c: getenv("LANG")`. It takes
    the first value that is present, which means not null and not empty,
    and otherwise it falls back to "C". When the chosen name equals "C"
    or "POSIX", the function returns the built-in data and never touches
    a file. The function `c: setlocale` in locale/setlocale.c also reads
    LOCPATH and builds a search path only when that value is present.
    The twelve category names come from locale/categories.def. *)

From Stdlib Require Import String Ascii ZArith List.
From Nanofil Require Import Values Memory.
From Glibc Require Import StartState.
Import ListNotations.
Open Scope Z_scope.

(** The function [lit] gives the bytes of a string literal, one per character. *)
Definition lit (s : string) : list Z := map (fun c => Z.of_N (N_of_ascii c)) (list_ascii_of_string s).

(** These are the environment variables whose values decide a
    category's locale: LC_ALL, the twelve categories of
    locale/categories.def, and LANG. *)
Definition locale_vars : list (list Z) :=
  map lit ["LC_ALL"; "LC_COLLATE"; "LC_CTYPE"; "LC_MONETARY"; "LC_NUMERIC"; "LC_TIME"; "LC_MESSAGES";
           "LC_PAPER"; "LC_NAME"; "LC_ADDRESS"; "LC_TELEPHONE"; "LC_MEASUREMENT"; "LC_IDENTIFICATION";
           "LANG"]%string.

(** A locale variable may be empty, which `c: _nl_find_locale` treats
    as unset, or it may name the C locale by either of its two names. *)
Definition c_locale_values : list (list Z) := map lit [""; "C"; "POSIX"]%string.

(** The environment strings ss select the C locale when every entry of
    a locale variable has one of those values and every LOCPATH entry is
    empty. A variable without an entry also qualifies, because getenv
    then returns null. The byte 61 is the equals sign that ends the
    variable's name. *)
Definition c_locale_env (ss : list (list Z)) : Prop :=
  (forall n v, In (n ++ 61 :: v) ss -> In n locale_vars -> In v c_locale_values) /\
  (forall v, In (lit "LOCPATH" ++ 61 :: v) ss -> v = []).

(** The start state with memory m and entry arguments xs selects the C
    locale when the environment array it passes to
    `c: __libc_start_main`, the fourth argument, holds strings that
    select it. *)
Definition start_c_locale (m : mem) (xs : list word) : Prop :=
  forall b ss, nth_error xs 3 = Some (WPtr (mkPtr b (Obj b))) -> string_array m b ss ->
    c_locale_env (map snd ss).

(** The empty environment selects the C locale. *)
Lemma c_locale_env_nil : c_locale_env [].
Proof. split; intros; contradiction. Qed.

(** An environment that sets LANG to "POSIX" and LC_ALL to the empty
    string selects the C locale. *)
Example c_locale_env_posix : c_locale_env [lit "LANG=POSIX"; lit "LC_ALL="; lit "HOME=/"].
Proof.
  split.
  - intros n v Hin Hn. cbn in Hn.
    destruct Hin as [H|[H|[H|[]]]]; vm_compute in H;
      repeat (destruct n as [|? n]; [cbn in H; try discriminate; inversion H; subst; cbn; tauto|];
              cbn in H; injection H as <- H; try (vm_compute in Hn; intuition discriminate)).
  - intros v Hin. destruct Hin as [H|[H|[H|[]]]]; vm_compute in H; discriminate.
Qed.

(** An environment that sets LANG to a real locale's name does not
    select the C locale, so the premise excludes it. *)
Example c_locale_env_de : ~ c_locale_env [lit "LANG=de_DE.UTF-8"].
Proof.
  intros [H _]. specialize (H (lit "LANG") (lit "de_DE.UTF-8") (or_introl eq_refl)).
  vm_compute in H. intuition discriminate.
Qed.

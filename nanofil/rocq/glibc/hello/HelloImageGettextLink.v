(** HelloGettextImage.v checks gettext's link record against a selection
    of Hello's image: the names that gettext calls and their alias
    targets. A proof about all of Hello needs the record for the whole
    linked image instead, because another unit of that image could define
    one of those names, and the selection alone cannot rule that out.
    HelloImageCode.v assembles the whole image, so this file checks
    every lookup that gettext makes against the whole linked module and
    derives the record for it, with the symbols that the loader computes.

    The record says which function each call finds. It does not say that
    Hello starts from this image, or that the proofs of Hello's entry
    run with this environment. *)

From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Values Memory Run Semantics.
From Glibc Require Import HelloGettextImageCode HelloGettextLink HelloGettextImage.
From Glibc Require Import HelloImageEraseMem HelloImageModule HelloImageLoad.
Import ListNotations.

(** ## The lookups in the whole image *)

(** For every name that gettext calls or reaches through an alias, the
    whole image answers a direct lookup and an alias lookup exactly as
    the selection does. *)
Lemma hello_image_lookups : Forall (lookup_agrees hello_image_module hellogettextimage_module) HelloGettextImage.hello_image_names.
Proof. repeat constructor; reflexivity. Qed.

(** No function, outside function, data object or alias of the whole
    image is named memmove. *)
Lemma hello_image_no_zmemmove :
  find_direct (TAtom "zmemmove") hello_image_module = None /\
  find_alias (TAtom "zmemmove") hello_image_module = None /\
  existsb (name_eqb (TAtom "zmemmove")) (map item_key hello_image_module) = false.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.

(** ## Gettext's record in the whole image *)

(** A call that runs the wrong function would void every proof about
    gettext. In the whole image, each of gettext's calls runs the
    function its proofs expect, and nothing there is named memmove. *)
Theorem hello_image_gettext_link g m fr :
  initial_memory hello_image_module = Some (g, m) -> hello_gettext_link (mkGenv hello_image_module g fr).
Proof.
  intros Hi. destruct hello_image_no_zmemmove as (Hd & Ha & Hk).
  apply hello_gettext_link_of_agree; cbn [ge_module ge_globals].
  - exact hello_image_lookups.
  - unfold find_fn. cbn [ge_module]. rewrite Hd, Ha. reflexivity.
  - apply (loaded_absent _ _ m _ Hi). intros Hin.
    assert (E : existsb (name_eqb (TAtom "zmemmove")) (map item_key hello_image_module) = true).
    { apply existsb_exists. exists (TAtom "zmemmove"). split; [exact Hin | apply term_eqb_refl]. }
    congruence.
Qed.

(** The loader succeeds on the whole image, so the record holds for the
    symbols it actually produces. *)
Corollary hello_image_loaded_gettext_link :
  exists g m, initial_memory hello_image_module = Some (g, m) /\
    forall fr, hello_gettext_link (mkGenv hello_image_module g fr).
Proof.
  destruct hello_image_memory as (g & m & E). exists g, m. split; [exact E|].
  intros fr. exact (hello_image_gettext_link g m fr E).
Qed.

(** ## The whole image is not the selection

    The agreement above would be trivial if the whole image were the
    selection itself. It holds about seventeen hundred more items, including
    functions that gettext never calls, and the agreement still holds.
    HelloGettextImage.v already shows that the same agreement refuses a
    module whose stpcpy alias is retargeted or whose stpcpy body is
    replaced, so an extra unrelated definition is accepted and a changed
    one is not. *)
Example hello_image_larger :
  length hello_image_module = 1713 /\ length hellogettextimage_module = 13 /\
  find_direct (TAtom "main") hello_image_module <> None /\ find_direct (TAtom "main") hellogettextimage_module = None.
Proof. vm_compute. split; [reflexivity | split; [reflexivity | split; [discriminate | reflexivity]]]. Qed.

(** A changed alias or body is refused by the same check as before. *)
Example hello_image_changed_refused := hello_image_changed_stpcpy.

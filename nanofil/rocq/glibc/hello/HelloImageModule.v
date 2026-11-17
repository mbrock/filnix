(** The real libc.so's start does not call the C constructors itself: it
    calls libpizlo's `c: zrun_deferred_global_ctors`, which runs every
    constructor that the loader recorded. The decoded Hello image cannot
    define that function, because no C unit does. This file appends the
    constructor runner of StartCtors.v to the decoded image, after every
    other item, so that the runner is defined and no existing symbol
    moves. Every Hello image proof reads this module. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Semantics.
From Glibc Require Import HelloImageEraseMem HelloImageChunks HelloImageCode StartCtors.
Import ListNotations.

(** The linked Hello image is the decoded image followed by the runner. *)
Definition hello_image_module : module := with_ctor_runner hello_image_decoded.

(** No item of the decoded image already uses a runner name, so the
    appended runner is the definition of its symbol. *)
Lemma hello_image_runner_fresh : ctor_names_fresh hello_image_decoded = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The image defines the runner for its own constructors. *)
Lemma hello_image_runner :
  find_direct ctor_runner_name hello_image_module =
    Some (Defined (ctor_runner (length (ctor_names hello_image_decoded)))).
Proof. exact (with_ctor_runner_defines _ hello_image_runner_fresh). Qed.

(** No run of zeros in the linked image is negative. *)
Lemma hello_image_zero : zero_nonneg hello_image_module = true.
Proof.
  unfold hello_image_module, with_ctor_runner.
  rewrite zero_nonneg_app, hello_image_decoded_zero. vm_compute. reflexivity.
Qed.

(** A proof that the linked Hello image holds some constants must first
    know that the loader builds a memory for the image at all, and that
    the image avoids the shapes that let one object's bytes land inside
    another. The generated decoding already checks that no run of zeros
    is negative. This file checks that no two items share a name, and it
    runs the loader on the decoded image itself, not on an erased copy.

    A successful load means only that the loader finishes on these
    items. It does not mean that Hello starts from this memory, that a
    constructor has run, or that a proof of Hello's entry runs this
    module. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Run.
From Glibc Require Import HelloImageEraseMem HelloImageCode.
Import ListNotations.

(** No two items of the linked image share a name. *)
Lemma hello_image_names : NoDup (map item_key hello_image_module).
Proof. apply names_distinct_sound. vm_compute. reflexivity. Qed.

(** The loader succeeds on the linked image. Only the symbols are
    computed, because computing the whole memory would unfold its byte
    functions. *)
Lemma hello_image_loads : option_map fst (initial_memory hello_image_module) <> None.
Proof. vm_compute. discriminate. Qed.

(** The loader's result can therefore be named. *)
Lemma hello_image_memory : exists g m, initial_memory hello_image_module = Some (g, m).
Proof.
  pose proof hello_image_loads as H. destruct (initial_memory hello_image_module) as [[g m]|].
  - exists g, m. reflexivity.
  - contradiction.
Qed.

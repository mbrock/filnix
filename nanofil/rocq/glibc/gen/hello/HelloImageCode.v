(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageChunks HelloImageEraseMem HelloImageTypedItems01 HelloImageTypedItems02 HelloImageTypedItems03 HelloImageTypedItems04 HelloImageTypedItems05 HelloImageTypedItems06 HelloImageTypedItems07 HelloImageTypedItems08 HelloImageTypedItems09 HelloImageTypedItems10 HelloImageTypedItems11 HelloImageTypedItems12 HelloImageTypedItems13 HelloImageTypedItems14 HelloImageTypedItems15 HelloImageTypedItems16 HelloImageTypedItems17 HelloImageTypedItems18 HelloImageTypedItems19 HelloImageTypedItems20 HelloImageTypedItems21 HelloImageTypedItems22 HelloImageTypedItems23 HelloImageTypedItems24 HelloImageTypedItems25 HelloImageTypedItems26 HelloImageTypedItems27.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).


(** ## Provenance

    The producer linked GNU Hello's 81 checked objects with 333 user glibc
    units by `rocq/scripts/link.pl --ctors main,__libc_start_main`. The objects come from the
    flake output `checks.x86_64-linux.nanofil-hello-fixture.captured`, and the units come from
    the capture `/nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44`.
    These SHA-256 digests identify the inputs and the result:

    - objects, by name and term digest: `5b7ba233e0adedaff060ffdce2b533211d3d360ee7af82a2201a816c261fe53b`
    - units, by name and term digest: `a6dedf5c33d6c177ae56c94ebc438b2ed0ea4ef314de4e22c4faf28d4a61c243`
    - the whole linked image: `d41e2c79f1408cfbb4b74c9b5c980cf5f934f08e940a152cebce3054f146b8b9`

    The extracted module decoder reads the linked term. Its OCaml printer
    writes the resulting constructors as Gallina, and the generator assembles
    the named definitions in link order. Rocq checks these definitions and
    their zero runs. The digests identify the input to the printer.
*)

Definition hello_image_decoded : module := hello_image_items_01 ++ hello_image_items_02 ++ hello_image_items_03 ++ hello_image_items_04 ++ hello_image_items_05 ++ hello_image_items_06 ++ hello_image_items_07 ++ hello_image_items_08 ++ hello_image_items_09 ++ hello_image_items_10 ++ hello_image_items_11 ++ hello_image_items_12 ++ hello_image_items_13 ++ hello_image_items_14 ++ hello_image_items_15 ++ hello_image_items_16 ++ hello_image_items_17 ++ hello_image_items_18 ++ hello_image_items_19 ++ hello_image_items_20 ++ hello_image_items_21 ++ hello_image_items_22 ++ hello_image_items_23 ++ hello_image_items_24 ++ hello_image_items_25 ++ hello_image_items_26 ++ hello_image_items_27.

Lemma hello_image_decoded_zero : zero_nonneg hello_image_decoded = true.
Proof.
  unfold hello_image_decoded. rewrite ?zero_nonneg_app, hello_image_items_01_zero, hello_image_items_02_zero, hello_image_items_03_zero, hello_image_items_04_zero, hello_image_items_05_zero, hello_image_items_06_zero, hello_image_items_07_zero, hello_image_items_08_zero, hello_image_items_09_zero, hello_image_items_10_zero, hello_image_items_11_zero, hello_image_items_12_zero, hello_image_items_13_zero, hello_image_items_14_zero, hello_image_items_15_zero, hello_image_items_16_zero, hello_image_items_17_zero, hello_image_items_18_zero, hello_image_items_19_zero, hello_image_items_20_zero, hello_image_items_21_zero, hello_image_items_22_zero, hello_image_items_23_zero, hello_image_items_24_zero, hello_image_items_25_zero, hello_image_items_26_zero, hello_image_items_27_zero. reflexivity.
Qed.

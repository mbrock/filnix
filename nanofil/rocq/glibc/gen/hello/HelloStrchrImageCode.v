(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_string_strchr_os Unit_string_strchrnul_os.
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

    The producer selected the items below from the full linked image.
    It checked that each selected name has one item and that its term
    agrees with the term in the `string/Strchr` fixture.

    - __GI_strchr: unique function, sha256 a1b2803e076535be3531828328fe37b4036c99d1cde50cf1d7674239304aefbc, equal to reference
    - __GI___strchrnul: unique function, sha256 80785420c1f5957aed016a7b884359814072b3d7cbcf5cbe65a73d67a437bf24, equal to reference
*)
Definition hellostrchrimage_module : module :=
  [IFunc Unit_string_strchr_os.fn___GI_strchr;
  IFunc Unit_string_strchrnul_os.fn___GI___strchrnul].

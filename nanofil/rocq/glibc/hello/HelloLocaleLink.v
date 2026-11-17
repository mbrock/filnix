(** The locale proofs run glibc's `c: setlocale` and the functions it
    calls, each decoded from its own unit by the fixtures in
    rocq/glibc/locale. Those proofs are about Hello only if Hello's image
    holds the same bodies under the names that the calls use. This file
    checks that by computation over the whole decoded image. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Heap.
From Glibc Require Import HelloImageModule SetlocaleCode FindlocaleCode PostloadCtypeCode.

(** Hello's call of `c: setlocale` finds the body of the setlocale
    fixture. *)
Lemma hello_image_setlocale g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "setlocale") = Some (Defined glibc_setlocale).
Proof. vm_compute. reflexivity. Qed.

(** The single-category route of `c: setlocale` calls its static helper
    `c: new_composite_name`, which the image keeps under its unit's
    prefix. *)
Lemma hello_image_new_composite_name g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "glibc_setlocale#new_composite_name") =
    Some (Defined glibc_new_composite_name).
Proof. vm_compute. reflexivity. Qed.

(** The search for each category's data calls `c: _nl_find_locale`. *)
Lemma hello_image_find_locale g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "_nl_find_locale") = Some (Defined glibc_nl_find_locale).
Proof. vm_compute. reflexivity. Qed.

(** Installing the character type data calls `c: _nl_postload_ctype`
    through glibc's table of postload functions. *)
Lemma hello_image_postload_ctype g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "_nl_postload_ctype") = Some (Defined glibc_nl_postload_ctype).
Proof. vm_compute. reflexivity. Qed.

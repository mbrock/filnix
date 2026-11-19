(** A check that accepts every piece would let a proof claim memory
    that the loader never wrote. HelloImageStart.v checks the objects of
    getopt_long's first call on an erased copy of Hello's image, so this
    file gives that check wrong pieces and shows that it refuses each.
    The capability that the loader really writes still passes. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith Bool.
From Nanofil Require Import Term Syntax Values Memory Run Pieces Heap.
From Glibc Require Import ImageData GetoptInitial ImagePieces HelloImageStart HelloImageLoad.
Import ListNotations.
Open Scope Z_scope.

(** ## Refusals

    A wrong value, a wrong object size and a missing capability are the
    mistakes a startup proof could make, and the check refuses each of
    them. It refuses opterr holding 0, the parser object with a longer
    region, and a table with no capability in its first name slot.

    The last mistake is to forget to keep the parser object. Its bytes
    in the copy are then zero, which happens to be right, but nothing
    ties them to the real memory, so the check refuses them. The real
    capability of the first name passes. *)

(** This keep set drops the parser's private object. *)
Local Definition keep_no_data (n : name) : bool :=
  hello_start_keep n && negb (name_eqb n (TAtom "glibc_getopt#getopt_data")).

Lemma hello_start_refused :
  match initial_memory hello_start_skel with
  | Some (g, m') =>
      negb (pieces_ok hello_start_keep hello_start_kept g m' (int_global_ps (img_a "opterr") (img_gd "opterr") 0)) &&
      negb (pieces_ok hello_start_keep hello_start_kept g m' (getopt_zero_ps (img_a "glibc_getopt#getopt_data") (gd (img_a "glibc_getopt#getopt_data") (img_a "glibc_getopt#getopt_data" + 64)))) &&
      negb (pieces_ok hello_start_keep hello_start_kept g m' [(PAux (img_a "hello#parse_options.longopts.64") 0, VAux CNone)]) &&
      negb (pieces_ok keep_no_data hello_start_kept g m' (getopt_zero_ps (img_a "glibc_getopt#getopt_data") (img_gd "glibc_getopt#getopt_data"))) &&
      pieces_ok hello_start_keep hello_start_kept g m' [(PAux (img_a "hello#parse_options.longopts.64") 0, VAux (Ro (img_a "hello#str.65")))]
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The application proof describes the checked module actually generated
    from hi.c. The shared program-fixture gate regenerates HiCode.v;
    this equality connects that artifact to the source-shaped body. *)

From Nanofil Require Import HiCode Hi Transport.

(** Decoding the pinned -O output gives exactly the module used by Hi.v,
    including its literal bytes, result and actual temporary argument. *)
Theorem hi_generated_module : decode_module hi_term = Some hi_module.
Proof. reflexivity. Qed.

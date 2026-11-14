(** The overflow wrapper chooses byte output before calling the
    stream's overflow function. This file instantiates its shared
    proof separately so the later composition stays within the
    per-file compilation budget. *)

From Nanofil Require Import Runtime.
From Glibc Require Import LibioOverflowGen HiAtexitBase.

(** The wrapper uses the same interpreter logic as stream output. *)

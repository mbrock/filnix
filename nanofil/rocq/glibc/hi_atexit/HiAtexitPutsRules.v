(** Puts takes stdout's lock, writes the string and a newline, and
    releases the lock. This file loads the shared proof of those
    steps separately so later files compile within their time limit. *)

From Nanofil Require Import Runtime.
From Glibc Require Import LibioPuts HiAtexitBase.

(** Puts uses the same interpreter logic as its proved callees. *)

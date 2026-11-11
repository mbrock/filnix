(** The string-output proof instantiates a large chain of libio
    modules. This file checks that instantiation separately so that
    composing the proved callees stays within the compilation budget. *)

From Nanofil Require Import Runtime.
From Glibc Require Import LibioXsputn HiAtexitBase.

(** String output uses the same interpreter logic as its callees. *)
Module HXS := LibioXsputnOn InterpRuntime HLG.

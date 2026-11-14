(** The proof of hi_atexit.c is for the interpreter's runtime, as the
    theorems of LenLogic.v and SayLogic.v are in the end. Every glibc
    triple is stated in a module over a runtime and a [LogicSig], and
    instantiating such a module elaborates all the modules it is built
    from. Fixing the runtime once, here, lets each composition file
    instantiate only the glibc modules it adds and name the rest by
    the path of the file that instantiated them, so no module is
    elaborated twice.

    [HLG] is the program logic over [InterpRuntime]; every
    composition file instantiates its glibc modules at it. *)

From Nanofil Require Import Runtime Logic.
From Glibc Require Import Fix.

(** The program logic over the interpreter's runtime. *)
Module HLG := LG0.

(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module PrintfNames.

Module fn___printf.
Notation "'‹format›'" := (TAtom "v0").
Notation "'‹&arg›'" := (TAtom "v2").
Notation "'‹chk(&arg)›'" := (TAtom "chk0").
Notation "'‹&stdout›'" := (TAtom "v4").
Notation "'‹chk(&stdout)›'" := (TAtom "chk1").
Notation "'‹stdout›'" := (TAtom "v5").
Notation "'‹done›'" := (TAtom "v7").
End fn___printf.

End PrintfNames.

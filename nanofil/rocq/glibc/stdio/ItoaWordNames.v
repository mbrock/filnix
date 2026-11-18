(** These notations name the temporaries of compiled functions after the C expression each one holds.
    A proof imports the module of its own function, and then writes and reads a temporary by that name.
    Every name is one token between single guillemets, so it cannot be read as a term about proof variables.
    A name with @ and a label belongs to a later temporary that holds the same expression.
    These names are notations for the temporaries' own names; they add no premise.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String.
From Nanofil Require Import Term.
Open Scope string_scope.

Module ItoaWordNames.

Module fn__itoa_word.
Notation "'‹value›'" := (TAtom "v0").
Notation "'‹buflim›'" := (TAtom "v2").
Notation "'‹base›'" := (TAtom "v4").
Notation "'‹upper_case›'" := (TAtom "v6").
Notation "'‹digits›'" := (TAtom "v15").
Notation "'‹buflim@L20›'" := (TAtom "pr.6").
Notation "'‹value@L20›'" := (TAtom "pr.1").
Notation "'‹buflim@L34›'" := (TAtom "pr.7").
Notation "'‹value@L34›'" := (TAtom "pr.2").
Notation "'‹buflim@L48›'" := (TAtom "pr.8").
Notation "'‹value@L48›'" := (TAtom "pr.3").
Notation "'‹buflim@L62›'" := (TAtom "pr.9").
Notation "'‹value@L62›'" := (TAtom "pr.4").
Notation "'‹buflim@L18›'" := (TAtom "pr.5").
Notation "'‹&_itoa_upper_digits›'" := (TAtom "v13").
Notation "'‹&_itoa_lower_digits›'" := (TAtom "v14").
Notation "'‹base==10›'" := (TAtom "v79").
Notation "'‹buflim@L20.2›'" := (TAtom "v24").
Notation "'‹chk(buflim)›'" := (TAtom "chk1").
Notation "'‹value@L20.2›'" := (TAtom "v31").
Notation "'‹value!=0›'" := (TAtom "v32").
Notation "'‹buflim@L34.2›'" := (TAtom "v38").
Notation "'‹chk(buflim)@L34›'" := (TAtom "chk3").
Notation "'‹value@L34.2›'" := (TAtom "v45").
Notation "'‹value!=0@L34›'" := (TAtom "v46").
Notation "'‹buflim@L48.2›'" := (TAtom "v52").
Notation "'‹chk(buflim)@L48›'" := (TAtom "chk5").
Notation "'‹value@L48.2›'" := (TAtom "v59").
Notation "'‹value!=0@L48›'" := (TAtom "v60").
Notation "'‹buflim@L62.2›'" := (TAtom "v66").
Notation "'‹chk(buflim)@L62›'" := (TAtom "chk7").
Notation "'‹value@L62.2›'" := (TAtom "v77").
Notation "'‹value!=0@L62›'" := (TAtom "v78").
Notation "'‹base==16›'" := (TAtom "v81").
Notation "'‹base==8›'" := (TAtom "v83").
End fn__itoa_word.

End ItoaWordNames.

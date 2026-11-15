(** GNU Hello initializes its state, parses options, and dispatches to an
    output or diagnostic path. These phases share one program logic;
    this module includes their proofs under the original public names. *)
From Nanofil Require Import Runtime HelloMainGetopt HelloMainDiagnostics.
Include HelloMainBase.MainDefinitions.
Module HelloMain (R : Runtime).
Include HelloMainGetopt R.
Include HelloMainDiagnostics.HelloMainDiagnostics R.
End HelloMain.

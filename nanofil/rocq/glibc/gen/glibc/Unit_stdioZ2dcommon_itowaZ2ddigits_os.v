(** This file defines checked IR from glibc’s `stdio-common/itowa-digits.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__itowa_lower_digits : item :=
  (IData (a "_itowa_lower_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 97; 0; 0; 0; 98; 0; 0; 0; 99; 0; 0; 0; 100; 0; 0; 0; 101; 0; 0; 0; 102; 0; 0; 0; 103; 0; 0; 0; 104; 0; 0; 0]) (app [105; 0; 0; 0; 106; 0; 0; 0; 107; 0; 0; 0; 108; 0; 0; 0; 109; 0; 0; 0; 110; 0; 0; 0; 111; 0; 0; 0; 112; 0; 0; 0; 113; 0; 0; 0] [114; 0; 0; 0; 115; 0; 0; 0; 116; 0; 0; 0; 117; 0; 0; 0; 118; 0; 0; 0; 119; 0; 0; 0; 120; 0; 0; 0; 121; 0; 0; 0; 122; 0; 0; 0])))]).

Definition item__itowa_upper_digits : item :=
  (IData (a "_itowa_upper_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 65; 0; 0; 0; 66; 0; 0; 0; 67; 0; 0; 0; 68; 0; 0; 0; 69; 0; 0; 0; 70; 0; 0; 0; 71; 0; 0; 0; 72; 0; 0; 0]) (app [73; 0; 0; 0; 74; 0; 0; 0; 75; 0; 0; 0; 76; 0; 0; 0; 77; 0; 0; 0; 78; 0; 0; 0; 79; 0; 0; 0; 80; 0; 0; 0; 81; 0; 0; 0] [82; 0; 0; 0; 83; 0; 0; 0; 84; 0; 0; 0; 85; 0; 0; 0; 86; 0; 0; 0; 87; 0; 0; 0; 88; 0; 0; 0; 89; 0; 0; 0; 90; 0; 0; 0])))]).

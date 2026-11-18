(** A field access adds an offset to a pointer while keeping its [[lower]].
    The short spelling repeats the base operand in both positions of the
    [[flight]] instruction. *)

From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax.
Import ListNotations.

Abbreviation a := TAtom.
Abbreviation k := Const.
Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).
Notation "'g' s" := (Global (TAtom s)) (at level 10, s at next level).
Notation "'to' s" := (To (TAtom s)) (at level 10, s at next level).
Notation "'padd' dst base offset" :=
  (Flight (TAtom dst) Add [FAddress (t base); FValue offset] (LowerOf (t base)))
  (at level 10, dst at next level, base at next level, offset at next level).

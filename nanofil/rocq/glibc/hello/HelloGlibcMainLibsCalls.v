(** This file groups the proved string and program-name bridges.
    The sealed group avoids repeating their proof substitutions when
    the final library record adds allocation, registration and exit. *)

From Nanofil Require Import Runtime Logic.
From Glibc Require Import HelloGlibcLibsT HelloGlibcLibsStr HelloGlibcLibsName.

(** The group exposes the two existing concrete call interfaces. *)
Module Type HelloLibsCallsSig (R : Runtime) (LG0 : LogicSig R) (D : HelloDebtsT R LG0).
(** The string calls use the same debt and resource definitions. *)
Declare Module ST : HelloLibsStrSig R LG0 D.
(** The program-name call uses the same debt and resource definitions. *)
Declare Module NM : HelloLibsNameSig R LG0 D.
End HelloLibsCallsSig.

(** Both interfaces are implemented by their concrete library proofs. *)
Module HelloGlibcMainLibsCallsOn (R : Runtime) (LG0 : LogicSig R) (D : HelloDebtsT R LG0)
  : HelloLibsCallsSig R LG0 D.
(** The string bridge proves the memory, comparison and errno calls. *)
Module ST := HelloGlibcLibsStrOn R LG0 D.
(** The name bridge proves the suffix searches and global stores. *)
Module NM := HelloGlibcLibsNameOn R LG0 D.
End HelloGlibcMainLibsCallsOn.

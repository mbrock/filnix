(** This file groups the proved string and program-name bridges.
    The sealed group avoids repeating their proof substitutions when
    the final library record adds allocation, registration and exit. *)

From Nanofil Require Import Runtime Logic.
From Glibc Require Import HelloGlibcLibsT HelloGlibcLibsStr HelloGlibcLibsName.
From Glibc Require Import Fix.

(** The group exposes the two existing concrete call interfaces. *)
Module Type HelloLibsCallsSig (D : HelloDebtsT).
(** The string calls use the same debt and resource definitions. *)
Declare Module ST : HelloLibsStrSig D.
(** The program-name call uses the same debt and resource definitions. *)
Declare Module NM : HelloLibsNameSig D.
End HelloLibsCallsSig.

(** Both interfaces are implemented by their concrete library proofs. *)
Module HelloGlibcMainLibsCallsOn (D : HelloDebtsT)
  : HelloLibsCallsSig D.
(** The string bridge proves the memory, comparison and errno calls. *)
Module ST := HelloGlibcLibsStrOn D.
(** The name bridge proves the suffix searches and global stores. *)
Module NM := HelloGlibcLibsNameOn D.
End HelloGlibcMainLibsCallsOn.

(** GNU Hello registers an exit handler, allocates and frees memory, and
    measures strings with the glibc it is linked with. Those calls are
    proved over glibc's own code. Every proof about Hello must agree on
    one description of glibc's list of exit handlers, or their pieces
    would not fit together. This file fixes that description once and
    builds the record of proved library calls from it. The safety theorem
    in HelloStartNeverPanics.v uses both. *)

From Glibc Require Import GlibcTactics.
From Glibc Require Import HelloGlibcDebts HelloGlibcLibsT HelloGlibcMainLibs.

(** The exit-handler state belongs to the compiled glibc implementation. *)
Module AX := HelloGlibcAtexitOn.
(** The completed library record contains no extra call assumptions. *)
Module Libs := HelloGlibcMainLibsOn HelloGlibcDebts AX.

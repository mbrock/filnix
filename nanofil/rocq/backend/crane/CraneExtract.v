(** # The backend's compiler, extracted to C++ by Crane

    As Extract.v for OCaml: the reader of IR text and the three
    compilers, with what main.cpp needs to print their lines. *)

From Crane Require Extraction.
From BackendCrane Require Import CraneMap.
From Nanofil Require Import Term Maps Transport.
From Backend Require Import Text Asm Layout EmitData EmitModule Compile IrText.

Set Crane Format Style "None".
Set Crane Extraction Output Directory ".".
Set Crane Loopify.
Set Crane NonAtomicRc.
Set Crane Loopify Diagnostics.
(* Their inner fixpoint is called under an operator, and the loop Crane
   writes for that names a function it never declares.  Both recurse
   only as deep as a term nests. *)
Crane NoLoopify term_eqb Order.term_compare.

Crane Extraction "nb" read_text compile compile_promoted compile_allocated
  rev_lines_parts first_todo.

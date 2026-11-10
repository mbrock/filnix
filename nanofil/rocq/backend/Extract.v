(** Extraction of the backend to OCaml: so far the decoder of an
    asm.pl line term ([dline]) and the printer of lines
    ([rev_lines_parts]), which the driver (extraction/main.ml) applies
    to what `nanofil asm-terms` prints. Integers become zarith's,
    strings OCaml's and [nat] OCaml's `int`, as in the model's
    extraction. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatInt.
From Backend Require Import Text Asm AsmTerm.

Set Extraction Output Directory "extraction".
Extraction "nanofil_backend.ml" dline rev_lines_parts.

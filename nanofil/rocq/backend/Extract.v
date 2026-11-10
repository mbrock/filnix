(** Extraction of the backend to OCaml, for the driver
    (extraction/main.ml), which holds each part to the Prolog
    compiler's output:

    - the decoder of an asm.pl line term ([dline]) and the printer of
      lines ([rev_lines_parts]), applied to what `nanofil asm-terms`
      prints;
    - the ABI plan of a function ([lower_function]) and of a module's
      weak thunks ([lower_thunks]), each written as its term
      ([plan_term], [thunks_term]) and compared ([term_eqb]) with
      what `nanofil abi-terms` prints, on the module that command
      prints first ([decode_module], [module_symbols]).

    Integers become zarith's, strings OCaml's and [nat] OCaml's
    `int`, as in the model's extraction. The order of two atoms'
    names becomes OCaml's comparison of strings, which is by byte;
    for UTF-8 that is the order of the character codes. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatInt.
From Nanofil Require Import Term Transport.
From Backend Require Import Text Asm AsmTerm Order Abi PlanTerm.

Extract Inlined Constant atom_compare =>
  "(fun a b -> let c = Stdlib.compare (a : string) b in if c < 0 then Lt else if c = 0 then Eq else Gt)".

Set Extraction Output Directory "extraction".
Extraction "nanofil_backend.ml" dline rev_lines_parts
  decode_module module_symbols lower_function lower_thunks plan_term thunks_term term_eqb.

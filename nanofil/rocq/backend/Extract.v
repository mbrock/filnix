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
    - the NFB writer and reader of a module (Nfb.v's [encode] and
      [decode]), held to the words `nanofil nfb-terms` writes, and
      [enc_module] to compare what the reader gives with the
      module that command prints.

    Integers become zarith's, strings OCaml's and [nat] OCaml's
    `int`, as in the model's extraction. The order of two atoms'
    names becomes OCaml's comparison of strings, which is by byte;
    for UTF-8 that is the order of the character codes. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatInt.
From Stdlib Require Import ZArith.
From Nanofil Require Import Term Maps Transport.
From Backend Require Import Text Asm AsmTerm Order Abi PlanTerm Nfb.

(** The hash that picks a name's bucket becomes OCaml's string hash,
    as in the model's extraction (theories/Extract.v): a lookup
    compares the names in the bucket, so the hash decides no answer,
    and the Gallina one took a fifth of the time of SQLite's plans. *)
Extract Constant Maps.string_hash =>
  "(fun s h -> Big_int_Z.big_int_of_int
     ((Hashtbl.hash s + 31 * Big_int_Z.int_of_big_int h) land 0xFFFFF))".

Extract Inlined Constant atom_compare =>
  "(fun a b -> let c = Stdlib.compare (a : string) b in if c < 0 then Lt else if c = 0 then Eq else Gt)".

(** A [nat] is OCaml's `int`, so the conversions between [nat] and
    [Z] are zarith's: the stdlib's count one by one. *)
Extract Constant Z.to_nat =>
  "(fun z -> if Big_int_Z.sign_big_int z <= 0 then 0 else Big_int_Z.int_of_big_int z)".
Extract Constant Z.of_nat => "Big_int_Z.big_int_of_int".

Set Extraction Output Directory "extraction".
Extraction "nanofil_backend.ml" dline rev_lines_parts
  decode_module module_symbols lower_function lower_thunks plan_term thunks_term term_eqb
  Nfb.encode Nfb.decode enc_module.

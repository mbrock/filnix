(** # How Crane writes the stdlib's numbers and strings in C++

    The C++ extraction of the backend (CraneExtract.v) and its
    self-test (CraneSelfTest.v) share these mappings, as Extract.v
    holds the OCaml ones. A [positive], an [N] and a [Z] are nfrt.h's
    `nf::Z`, a [nat] is a `uint64_t` (Crane's NatIntStd), an
    [ascii] is a `char` (Crane's AsciiChar) and a [string] is a
    `std::string`. The functions named in nfrt.h are the twins of the
    stdlib's; CraneSelfTest.v holds each to what [vm_compute] finds.

    A function that is not mapped here is extracted from its Gallina
    and is right, only slower: each mapping below is there because a
    profile of the compiler showed the function. *)

From Crane Require Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd Mapping.AsciiChar.
From Stdlib Require Import String ZArith NArith PArith List Ascii.
From Nanofil Require Import Term Maps.

(** ## Integers *)

Crane Extract Inductive positive =>
  "nf::Z"
  [ "nf::Z(2 * %a0 + 1)" "nf::Z(2 * %a0)" "nf::Z(1)" ]
  "if (%scrut == 1) { %br2 } else if (nf::z_odd(%scrut)) { nf::Z %b0a0 = %scrut >> 1; %br0 } else { nf::Z %b1a0 = %scrut >> 1; %br1 }"
  From "nfrt.h".

Crane Extract Inductive N =>
  "nf::Z"
  [ "nf::Z(0)" "%a0" ]
  "if (%scrut == 0) { %br0 } else { nf::Z %b1a0 = %scrut; %br1 }"
  From "nfrt.h".

Crane Extract Inductive Z =>
  "nf::Z"
  [ "nf::Z(0)" "%a0" "nf::Z(-%a0)" ]
  "if (%scrut == 0) { %br0 } else if (%scrut > 0) { nf::Z %b1a0 = %scrut; %br1 } else { nf::Z %b2a0 = -%scrut; %br2 }"
  From "nfrt.h".

Crane Extract Numeral N => "nf::Z(%n_nfz)".
Crane Extract Numeral Z => "nf::Z(%n_nfz)".

Crane Extract Inlined Constant Z.add => "nf::Z(%a0 + %a1)".
Crane Extract Inlined Constant Z.sub => "nf::Z(%a0 - %a1)".
Crane Extract Inlined Constant Z.mul => "nf::Z(%a0 * %a1)".
Crane Extract Inlined Constant Z.div => "nf::z_div(%a0, %a1)".
Crane Extract Inlined Constant Z.modulo => "nf::z_mod(%a0, %a1)".
Crane Extract Inlined Constant Z.quot => "nf::z_quot(%a0, %a1)".
Crane Extract Inlined Constant Z.opp => "nf::Z(-%a0)".
Crane Extract Inlined Constant Z.abs => "nf::Z(abs(%a0))".
Crane Extract Inlined Constant Z.succ => "nf::Z(%a0 + 1)".
Crane Extract Inlined Constant Z.pred => "nf::Z(%a0 - 1)".
Crane Extract Inlined Constant Z.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant Z.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant Z.leb => "(%a0 <= %a1)".
Crane Extract Inlined Constant Z.gtb => "(%a0 > %a1)".
Crane Extract Inlined Constant Z.geb => "(%a0 >= %a1)".
Crane Extract Inlined Constant Z.eq_dec => "(%a0 == %a1)".
Crane Extract Inlined Constant Z.compare => "nf::order<Comparison>(cmp(%a0, %a1))".
Crane Extract Inlined Constant Z.min => "nf::z_min(%a0, %a1)".
Crane Extract Inlined Constant Z.max => "nf::z_max(%a0, %a1)".
Crane Extract Inlined Constant Z.pow => "nf::z_pow(%a0, %a1)".
Crane Extract Inlined Constant Z.land => "nf::Z(%a0 & %a1)".
Crane Extract Inlined Constant Z.lor => "nf::Z(%a0 | %a1)".
Crane Extract Inlined Constant Z.shiftl => "nf::z_shiftl(%a0, %a1)".
Crane Extract Inlined Constant Z.shiftr => "nf::z_shiftl(%a0, nf::Z(-%a1))".
Crane Extract Inlined Constant Z.log2 => "nf::z_log2(%a0)".
Crane Extract Inlined Constant Z.div2 => "nf::Z(%a0 >> 1)".
Crane Extract Inlined Constant Z.of_N => "nf::Z(%a0)".
Crane Extract Inlined Constant Z.of_nat => "nf::z_of_nat(%a0)".
Crane Extract Inlined Constant Z.to_nat => "nf::z_to_nat(%a0)".

Crane Extract Inlined Constant N.add => "nf::Z(%a0 + %a1)".
Crane Extract Inlined Constant N.mul => "nf::Z(%a0 * %a1)".
Crane Extract Inlined Constant N.sub => "nf::z_max(nf::Z(%a0 - %a1), nf::Z(0))".
Crane Extract Inlined Constant N.compare => "nf::order<Comparison>(cmp(%a0, %a1))".
Crane Extract Inlined Constant N.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant N.leb => "(%a0 <= %a1)".
Crane Extract Inlined Constant N.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant N.land => "nf::Z(%a0 & %a1)".
Crane Extract Inlined Constant N.lor => "nf::Z(%a0 | %a1)".
Crane Extract Inlined Constant N.to_nat => "nf::z_to_nat(%a0)".
Crane Extract Inlined Constant N.of_nat => "nf::z_of_nat(%a0)".
Crane Extract Inlined Constant BinNatDef.N.add => "nf::Z(%a0 + %a1)".
Crane Extract Inlined Constant BinNatDef.N.mul => "nf::Z(%a0 * %a1)".
Crane Extract Inlined Constant BinNatDef.N.to_nat => "nf::z_to_nat(%a0)".
Crane Extract Inlined Constant BinNatDef.N.of_nat => "nf::z_of_nat(%a0)".

Crane Extract Inlined Constant Pos.add => "nf::Z(%a0 + %a1)".
Crane Extract Inlined Constant Pos.mul => "nf::Z(%a0 * %a1)".
Crane Extract Inlined Constant Pos.succ => "nf::Z(%a0 + 1)".
Crane Extract Inlined Constant Pos.compare => "nf::order<Comparison>(cmp(%a0, %a1))".
Crane Extract Inlined Constant Pos.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant Pos.eq_dec => "(%a0 == %a1)".
Crane Extract Inlined Constant Pos.to_nat => "nf::z_to_nat(%a0)".
Crane Extract Inlined Constant Pos.of_succ_nat => "nf::Z(nf::z_of_nat(%a0) + 1)".
Crane Extract Inlined Constant BinPosDef.Pos.add => "nf::Z(%a0 + %a1)".
Crane Extract Inlined Constant BinPosDef.Pos.mul => "nf::Z(%a0 * %a1)".
Crane Extract Inlined Constant BinPosDef.Pos.succ => "nf::Z(%a0 + 1)".

Crane Extract Inlined Constant Nat.compare =>
  "nf::order<Comparison>((%a0 > %a1) - (%a0 < %a1))".

(** ## Characters and strings *)

Crane Extract Inductive string =>
  "std::string"
  [ "std::string()" "(std::string(1, %a0) + %a1)" ]
  "if (%scrut.empty()) { %br0 } else { char %b1a0 = %scrut[0]; std::string %b1a1 = %scrut.substr(1); %br1 }"
  From "string".

Crane Extract Inlined Constant nat_of_ascii =>
  "static_cast<uint64_t>(static_cast<unsigned char>(%a0))".
Crane Extract Inlined Constant N_of_ascii =>
  "nf::Z(static_cast<unsigned long>(static_cast<unsigned char>(%a0)))".
Crane Extract Inlined Constant ascii_of_nat => "static_cast<char>((%a0) & 255)".

Crane Extract Inlined Constant String.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant String.compare =>
  "nf::order<Comparison>((%a0).compare(%a1))".
Crane Extract Inlined Constant String.append => "(%a0 + %a1)".
Crane Extract Inlined Constant String.length => "static_cast<uint64_t>((%a0).size())".
Crane Extract Inlined Constant String.prefix => "(%a1).starts_with(%a0)".
Crane Extract Inlined Constant string_of_list_ascii => "nf::string_of_list(%a0)".

(** ## The model's names *)

(** A name's hash is the Gallina one, by machine arithmetic. *)
Crane Extract Inlined Constant Maps.string_hash => "nf::string_hash(%a0, %a1)".

(** [name_eqb] is [term_eqb] under another name; written out as a
    function it takes its two terms by value, a copy of each for
    every key a lookup passes. *)
Crane Extraction Inline name_eqb.

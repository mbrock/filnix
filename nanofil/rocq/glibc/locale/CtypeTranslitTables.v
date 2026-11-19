(** The C locale stores transliteration indexes and strings as arrays of
    32-bit words. The conversion reads them from the compiled locale object.
    Hello's loader proof checks that the linked image holds the same bytes. *)

From Stdlib Require Import ZArith List.
From stdpp Require Import list.
From Nanofil Require Import Syntax MemLogic.
From Glibc Require Import Unit_locale_CZ2dctype_os.
Import ListNotations.
Open Scope Z_scope.

(** This function lists the little-endian bytes of 32-bit words. *)
Definition le_words (ws : list Z) : list Z := flat_map (fun c => MemLogic.le_bytes c 4) ws.

(** This function reads a byte string as 32-bit words and drops a
    short tail. *)
Fixpoint words_of (cs : list Z) : list Z :=
  match cs with a :: b :: c :: d :: r => (a + 256 * (b + 256 * (c + 256 * d))) :: words_of r | _ => [] end.

(** The compiler emits each word array as a byte string at the start of its initializer. *)
Definition object_words (it : item) : list Z :=
  match it with IData _ _ _ (Str cs :: _) => words_of cs | _ => [] end.

Definition wc_from_idx := Eval vm_compute in object_words Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_from_idx.
Definition wc_from_tbl := Eval vm_compute in object_words Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_from_tbl.
Definition wc_to_idx := Eval vm_compute in object_words Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_to_idx.
Definition wc_to_tbl := Eval vm_compute in object_words Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_to_tbl.

(** ## What the tables hold

    Transliteration searches the tables without checking their shape,
    so its proof needs the facts below about their words. Each table of
    strings is read here with its trailing zero word. *)

(** The function [nul_at] gives the distance from position p to the
    next zero word of a table, looking at most fuel words ahead. *)
Fixpoint nul_at (tbl : list Z) (p : nat) (fuel : nat) : option nat :=
  match fuel with
  | Datatypes.O => None
  | Datatypes.S f => match tbl !! p with Some Z0 => Some Datatypes.O | Some _ => option_map Datatypes.S (nul_at tbl (Datatypes.S p) f) | None => None end
  end.

(** An entry of the source index starts a nonempty string. *)
Definition from_okb (tbl : list Z) (fi : Z) : bool :=
  (0 <=? fi) && match nul_at tbl (Z.to_nat fi) 64 with Some (Datatypes.S _) => true | _ => false end.

(** An entry of the replacement index starts a list of strings that
    ends with an empty string. *)
Fixpoint list_okb (tbl : list Z) (p : nat) (fuel : nat) : bool :=
  match fuel with
  | Datatypes.O => false
  | Datatypes.S f => match nul_at tbl p 64 with
           | Some k => match tbl !! (p + k + 1)%nat with
                       | Some Z0 => true | Some _ => list_okb tbl (p + k + 1) f | None => false end
           | None => false
           end
  end.

Definition to_okb (tbl : list Z) (ti : Z) : bool := (0 <=? ti) && list_okb tbl (Z.to_nat ti) 64.

Definition word_okb (c : Z) : bool := (0 <=? c) && (c <? 2 ^ 32).

(** Both indexes have one entry for each of the 1659 sources. *)
Lemma wc_sizes : length wc_from_idx = 1659%nat /\ length wc_to_idx = 1659%nat.
Proof. split; vm_compute; reflexivity. Qed.

(** Every word of the tables is a 32-bit word. *)
Lemma wc_words_okb : forallb word_okb (wc_from_idx ++ wc_to_idx ++ wc_from_tbl ++ wc_to_tbl) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every source string is nonempty and ends in the source table. *)
Lemma wc_from_okb : forallb (from_okb (wc_from_tbl ++ [0])) wc_from_idx = true.
Proof. vm_compute. reflexivity. Qed.

(** Every list of replacements ends in the replacement table. *)
Lemma wc_to_okb : forallb (to_okb (wc_to_tbl ++ [0])) wc_to_idx = true.
Proof. vm_compute. reflexivity. Qed.

(** The narrow formatter reads two dispatch tables, a digit table and the
    text for a null string argument. These checks recover the bytes from
    their captures and describe the read permissions a caller supplies. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Pieces Heap Logic MemLogic.
From Glibc Require Import Fix GlibcProgram WordString FormatterCode.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** These declarations come from the existing complete formatter capture.
    Selecting them does not manufacture their bytes or change a function. *)
Definition formatter_string_tables : module := Eval vm_compute in
  filter (fun i => match i with IData n _ _ _ =>
    orb (term_eqb n (TAtom "glibc_vfprintf_internal#jump_table"))
      (term_eqb n (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277"))
    | _ => false end) formatter_module.

(** Loading the two tables alone provides a small check of their contents.
    Its addresses are not the addresses of a complete Hello image. *)
Definition formatter_tables_loaded :=
  match initial_memory formatter_string_tables with Some p => p | None => ([],empty_mem) end.

(** The loader succeeds, so the default empty memory cannot satisfy the
    following checks by accident. *)
Lemma formatter_tables_load :
  initial_memory formatter_string_tables = Some formatter_tables_loaded.
Proof.
  assert (H : option_map fst (initial_memory formatter_string_tables) =
    Some (fst formatter_tables_loaded)) by (vm_compute; reflexivity).
  unfold formatter_tables_loaded.
  destruct (initial_memory formatter_string_tables) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The selected declarations retain their captured read-only names. *)
Lemma formatter_tables_at :
  lookup (TAtom "glibc_vfprintf_internal#jump_table") (fst formatter_tables_loaded) =
    Some (mkPtr 65680 (Ro 65680)) /\
  lookup (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (fst formatter_tables_loaded) =
    Some (mkPtr 65536 (Ro 65536)).
Proof. vm_compute. split; reflexivity. Qed.

(** The genuine initializers contain precisely the bytes lent to the
    operational rule. This check supplies no ownership in a running program. *)
Lemma formatter_string_entries :
  load_bytes (snd formatter_tables_loaded) (65680 + 83) 1 = 21 /\
  load_bytes (snd formatter_tables_loaded) (65536 + 84) 4 = 21.
Proof. vm_compute. split; reflexivity. Qed.

(** The dispatch tables have these names in the linked program. *)

Definition jump_table : string := "glibc_vfprintf_internal#jump_table".
Definition step0_jumps : string := "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277".

(** The function [loaded_bytes] reads the bytes of a data object of
    the captured unit. It reads them from the memory that the loader
    builds for the formatter's two tables. *)
Definition loaded_bytes (n : string) : list Z :=
  match lookup (TAtom n) (fst formatter_tables_loaded),
        find (fun i => match i with IData m _ _ _ => term_eqb m (TAtom n) | _ => false end) formatter_string_tables with
  | Some p, Some (IData _ _ _ items) =>
      map (fun i => load_bytes (snd formatter_tables_loaded) (ptr_addr p + Z.of_nat i) 1)
        (seq 0 (Z.to_nat (items_size items)))
  | _, _ => []
  end.

Definition jump_table_bytes : list Z := Eval vm_compute in loaded_bytes jump_table.
Definition step0_jumps_bytes : list Z := Eval vm_compute in loaded_bytes step0_jumps.

(** The conversion `%d` turns a number into text with
    `c: _itoa_word`, which reads each digit's character from a table
    in another unit. The table holds the ten digits and then the 26
    lower-case letters, for bases up to 36. The linked program knows
    it under the name below. *)
Definition lower_digits : string := "__GI__itoa_lower_digits".
Definition lower_digits_bytes : list Z :=
  Eval vm_compute in map (fun i => 48 + Z.of_nat i) (seq 0 10) ++ map (fun i => 97 + Z.of_nat i) (seq 0 26).

(** The conversion `%s` prints this constant for a null argument. Its
    characters spell `(null)`. *)
Definition null_text : string := "glibc_vfprintf_internal#null".
Definition null_text_bytes : list Z := [40; 110; 117; 108; 108; 41].

(** The function [table_bytes] gives the bytes of one of the
    formatter's tables: its two dispatch tables and the table of
    digits. *)
Definition table_bytes (n : string) : list Z :=
  if String.eqb n jump_table then jump_table_bytes else
  if String.eqb n step0_jumps then step0_jumps_bytes else
  if String.eqb n lower_digits then lower_digits_bytes else [].

(** Each table has its bytes, so the definition above did not fall
    back to the empty list. *)
Lemma table_bytes_sizes :
  (length (table_bytes jump_table), length (table_bytes step0_jumps), length (table_bytes lower_digits)) =
  (91, 128, 36)%nat.
Proof. vm_compute. reflexivity. Qed.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The linked program has the table n, and anyone may read its bytes. *)
Definition ro_table (n : string) : iProp Σ :=
  ∃ b reg, ⌜lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Ro b)) /\ 0 < b /\
            b + Z.of_nat (length (table_bytes n)) <= r_end reg /\ r_end reg <= 2 ^ 63⌝ ∗
    liveq DfracDiscarded b reg ∗ bytesq DfracDiscarded b 0 (table_bytes n).

(** The global n holds a null pointer, and nobody can write it. *)
Definition null_global (n : string) : iProp Σ :=
  ∃ b reg, ⌜lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Obj b)) /\ 0 < b /\ b mod 8 = 0 /\
            b + 8 <= r_end reg /\ r_end reg <= 2 ^ 63⌝ ∗
    liveq DfracDiscarded b reg ∗ pcellq DfracDiscarded b 0 null.

(** The global n is a string constant with the characters s, and
    anyone may read it. *)
Definition ro_string (n : string) (s : list Z) : iProp Σ :=
  ∃ b, ⌜lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Ro b))⌝ ∗ word_string DfracDiscarded (mkPtr b (Ro b)) s.

(** The formatter reads its two dispatch tables, and the conversion
    `%d` reads the table of digits. The conversion `%s` prints the
    constant `(null)` when its argument is the null pointer. The
    formatter also reads three globals that are null while the program
    has registered no conversion of its own, and Hello registers
    none. *)
Definition printf_ro : iProp Σ :=
  ro_table jump_table ∗ ro_table step0_jumps ∗ ro_table lower_digits ∗
  ro_string null_text null_text_bytes ∗
  null_global "__printf_function_table" ∗ null_global "__printf_modifier_table" ∗
  null_global "__printf_va_arg_table".

(** A caller keeps the formatter's read-only data across a call,
    because anyone may read it at any time. *)
#[global] Instance printf_ro_persistent : Persistent printf_ro.
Proof using Type. rewrite /printf_ro /ro_table /ro_string /null_global. apply _. Qed.

End spec.

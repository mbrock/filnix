(** The formatter classifies an unmodified string directive through two
    read-only tables. This rule follows the actual loads for the byte s.
    The caller supplies their linked addresses and readable ownership;
    this rule does not obtain those resources from startup. *)
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic FormatterCode Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic.
Open Scope Z_scope.

(** The two loads set temporary registers without replacing the caller's
    other registers. This environment records their exact returned values. *)
Definition string_table_env e jb tb :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "v126", WPtr (mkPtr tb (Ro tb))); (TAtom "v127", WPtr (mkPtr jb (Ro jb)));
     (TAtom "v129", WInt 83); (TAtom "v130", WInt 83);
     (TAtom "v131", WPtr (mkPtr (jb + 83) (Ro jb)));
     (TAtom "chk12", WPtr (mkPtr (jb + 83) (Ro jb)));
     (TAtom "v132", WInt 21); (TAtom "v133", WInt 21); (TAtom "v134", WInt 84);
     (TAtom "v135", WPtr (mkPtr (tb + 84) (Ro tb)));
     (TAtom "chk13", WPtr (mkPtr (tb + 84) (Ro tb)));
     (TAtom "v136", WInt 21); (TAtom "v137", WInt 21)] e.

Section table.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Glibc reads both tables before it can choose how to print a string.
    Reading the byte s yields 21 from each table and leaves their contents
    unchanged. This rule stops before the jump to the string handler. *)
Lemma wp_formatter_string_table e ls from jb jr tb tr dqj dqt Φ :
  lookup (TAtom "v111") e = Some (WInt 115) ->
  lookup (TAtom "glibc_vfprintf_internal#jump_table") (ge_globals ge) = Some (mkPtr jb (Ro jb)) ->
  lookup (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (ge_globals ge) =
    Some (mkPtr tb (Ro tb)) ->
  0 < jb -> jb + 84 <= r_end jr -> r_end jr <= 2 ^ 63 ->
  0 < tb -> tb + 88 <= r_end tr -> r_end tr <= 2 ^ 63 ->
  liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗
  liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
  ▷ (liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗
    liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (string_table_env e jb tb) ls None
      (Enter (TAtom "L114") (Some (TAtom "L113")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L113") from)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv Hj Ht Hjb Hje Hjr Htb Hte Htr.
  iIntros "Hjl Hjb Htl Htb HK".
  iApply wp_enter; [reflexivity | destruct from; reflexivity |]. iNext.
  cbn [b_insts b_jump]. do 5 step. closed_ints.
  check_read_dq "Hjl" by ar. iNext. iIntros "Hjl".
  load_bytes_dq "Hjl Hjb" decode (reflexivity) by ar.
  iNext. iIntros "Hjl Hjb". do 3 step. closed_ints.
  check_read_dq "Htl" by ar. iNext. iIntros "Htl".
  load_bytes_dq "Htl Htb" decode (reflexivity) by ar.
  iNext. iIntros "Htl Htb". step. closed_ints. iApply wp_goto. iNext.
  norm.
  iApply ("HK" with "Hjl Hjb Htl Htb").
Qed.
End table.

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

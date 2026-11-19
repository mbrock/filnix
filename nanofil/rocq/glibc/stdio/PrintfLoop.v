(** The formatter of glibc prints a format string with the function
    `c: __printf_buffer`. The function copies the plain text of the
    format into a buffer. For each conversion, such as `%s`, it takes
    one argument and appends the text of that argument. This module
    proves that the compiled function is safe and that it gives back
    the memory that its caller lent. The contract
    [printf_buffer_spec] of [PrintfSpec](PrintfSpec.v) states this.
    The module proves the contract for a format of plain text and the
    conversions `%s`, `%c`, `%d` and `%%`.

    The function is a loop with one round for each conversion, and
    the proof stops at a few places of it. The module
    [PrintfLoopState](PrintfLoopState.v) says what is true at each of
    those places, and it names the modules that follow the code
    between them. This module joins their proofs into a proof about
    the whole function. *)

From Glibc Require FixVariadic.
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioDefaultXsputnBuf WordString StrchrnulLogic
  StrlenWord
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec FormatterNames PrintfLoopState PrintfLoopStart PrintfLoopHead
  PrintfLoopStr PrintfLoopChar PrintfLoopNext PrintfLoopInt.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic FixVariadic.VL0.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section table.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!Callees (loop_callees k R)}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation blocks := (loop_blocks k R).

(** Every block of the table meets its row. Each group of rows holds
    when the whole table holds one step later, and that is what a
    proof about a loop needs. *)
Lemma loop_table : ⊢ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH". iEval (rewrite /loop_blocks /blocks_hold !big_sepL_app).
  iSplit; [iApply (start_rows_hold with "IH")|]. iSplit; [iApply (head_rows_hold with "IH")|].
  iSplit; [iApply (str_rows_hold with "IH")|]. iSplit; [iApply (char_rows_hold with "IH")|].
  iSplit; [iApply (next_rows_hold with "IH")|]. iApply (int_rows_hold with "IH").
Qed.

(** ## The contract *)

(** A caller of `c: __printf_buffer` uses this lemma. It says that the
    compiled function meets [printf_buffer_spec] in every program that
    defines the function. *)
Lemma printf_buffer_has_spec `{!Defines ge "__printf_buffer" Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer") (printf_buffer_spec k R).
Proof using Type*.
  eapply (blocks_has_spec _ _ _ blocks); [exact defines | reflexivity | reflexivity | | exact loop_table].
  intros x. eexists _, x. split; [reflexivity|]. split.
  { destruct x as [bb [fa fc] dq bytes ds [ca cc] skip xs rest eb]. c_env_close. }
  cbn [bs_pre bs_post]. iIntros "$". iIntros (r) "$".
Qed.

End table.

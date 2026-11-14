From Glibc Require Import GlibcProgram.
(** Flushing a stream's buffer runs `c: _IO_new_do_write`, which hands
    the pending bytes to the write function and empties the buffer.
    It was proved one block at a time: LibioDoWrite.v proves the
    function from a triple of its call block, and each block's file
    assumes a triple of the block after it. This file joins the blocks
    from the last back to the first, with the write from
    LibioWriteDq.v at the whole share.

    | Assumption | Proved by |
    |---|---|
    | the write | [hi_file_write] |
    | the end of `c: L70` | LibioDoWriteEnd.v |
    | the pointer reset | LibioDoWriteSetp.v |
    | the tail | LibioDoWriteTail.v |
    | the return | LibioDoWriteRet.v |
    | the call | LibioDoWriteCall.v |

    The joined triple [hi_do_write_mode] assumes only facts about the
    genv: the write and `c: __write` are glibc's, and the system calls
    stay external. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioWriteDq LibioDoWriteEnd LibioDoWriteSetp LibioDoWriteTail LibioDoWriteRet
  LibioDoWriteCall LibioDoWrite HiAtexitBase.
From Glibc Require FileInv LibioDoWrite LibioDoWriteCall LibioDoWriteEnd LibioDoWriteRet LibioDoWriteSetp LibioDoWriteTail LibioLogic LibioWriteDq OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** The write of bytes at a share, the do-write's blocks and the
    do-write itself, at [HLG]. *)
(** `c: L70`'s end. *)
(** The pointer reset. *)
(** The tail. *)
(** The return. *)
(** The call. *)
(** The function. *)
Import LibioDoWrite SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context `{Hwrite : !Defines ge "__GI___write" glibc___libc_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_new_file_write(fp, data, n)` of bytes owned whole, as
    LibioDoWriteCall.v asks for it: LibioWriteDq.v's triple at the
    whole share, through the object's own capability. *)
Lemma hi_file_write fr fb freg fl f2 fd tw off b reg o xs eb Φ :
  call_frame glibc__IO_new_file_write
    [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) (Obj b)); WInt (Z.of_nat (length xs))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post (Z.of_nat (length xs)) fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hfal Hfend Hfreg Hf2 Hf2r Hfd Hfl He Hb Ho Hbend Hbreg Hxs.
  iIntros "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
  iApply (LibioWriteDq.wp_glibc__IO_new_file_write_dq Hreg Hext fr fb freg fl f2 fd tw off
            (DfracOwn 1) b reg (Obj b) o xs eb with "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK");
    try assumption; first [left; assumption | left; reflexivity].
Qed.

(** LibioDoWrite.v's [wp_glibc__IO_new_do_write_mode] with its call
    block proved: the blocks' premises discharged from the last back
    to the first, and the write by [hi_file_write]. *)
Definition hi_do_write_mode :=
  LibioDoWrite.wp_glibc__IO_new_do_write_mode (fun f2 => Z.land f2 2 = 0)
    (LibioDoWriteCall.wp_do_write_call Hfw (fun f2 => Z.land f2 2 = 0) hi_file_write
       (LibioDoWriteRet.wp_do_write_ret
          (LibioDoWriteTail.wp_do_write_tail
             (LibioDoWriteSetp.wp_do_write_setp (LibioDoWriteEnd.wp_do_write_end))))).

(** Overflow flushes from the buffer's base; the same proved blocks
    establish that case without a callee hypothesis. *)
Definition hi_do_write_base :=
  LibioDoWrite.wp_glibc__IO_new_do_write_base (fun f2 => Z.land f2 2 = 0)
    (LibioDoWriteCall.wp_do_write_call Hfw (fun f2 => Z.land f2 2 = 0) hi_file_write
       (LibioDoWriteRet.wp_do_write_ret
          (LibioDoWriteTail.wp_do_write_tail
             (LibioDoWriteSetp.wp_do_write_setp (LibioDoWriteEnd.wp_do_write_end))))).

(** A noncanceling write uses the captured wrapper rather than clearing flags2.
    Both branches return its exact value, the source bytes and errno ownership. *)
Lemma hi_file_write_nocancel fr fb freg fl f2 fd tw off b reg o xs eb Φ :
  call_frame glibc__IO_new_file_write
    [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) (Obj b)); WInt (Z.of_nat (length xs))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (Z.land f2 2 = 0 \/
    Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post (Z.of_nat (length xs)) fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hfal Hfend Hfreg Hf2 Hf2r Hfd Hfl He Hb Ho Hbend Hbreg Hxs.
  iIntros "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
  iApply (LibioWriteDq.wp_glibc__IO_new_file_write_dq Hreg Hext fr fb freg fl f2 fd tw off
            (DfracOwn 1) b reg (Obj b) o xs eb with "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK");
    try assumption; left; reflexivity.
Qed.

(** A stream can flush its pending bytes without allowing cancellation.
    This proof uses the captured write wrapper and retains the existing short-write and error cases. *)
Definition hi_do_write_mode_nocancel :=
  LibioDoWrite.wp_glibc__IO_new_do_write_mode
    (fun f2 => Z.land f2 2 = 0 \/
      Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel))
    (LibioDoWriteCall.wp_do_write_call Hfw _ hi_file_write_nocancel
       (LibioDoWriteRet.wp_do_write_ret
          (LibioDoWriteTail.wp_do_write_tail
             (LibioDoWriteSetp.wp_do_write_setp (LibioDoWriteEnd.wp_do_write_end))))).

(** Overflow can use the same noncanceling flush from the buffer's base.
    This rule does not acquire or release a stream lock. *)
Definition hi_do_write_base_nocancel :=
  LibioDoWrite.wp_glibc__IO_new_do_write_base
    (fun f2 => Z.land f2 2 = 0 \/
      Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel))
    (LibioDoWriteCall.wp_do_write_call Hfw _ hi_file_write_nocancel
       (LibioDoWriteRet.wp_do_write_ret
          (LibioDoWriteTail.wp_do_write_tail
             (LibioDoWriteSetp.wp_do_write_setp (LibioDoWriteEnd.wp_do_write_end))))).

End rules.

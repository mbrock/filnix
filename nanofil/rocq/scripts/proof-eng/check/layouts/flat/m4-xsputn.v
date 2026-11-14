From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  HiAtexitBase HiAtexitOverflowRules HiAtexitXsputnRules HiAtexitXsputnOverflow LibioXsputnBase
  HiAtexitXsputn PrintfBufferXsputnCall PrintfBufferXsputnReturn PrintfBufferXsputnPrelude.
From Glibc Require FileInv LibioDefaultXsputnBuf LibioLogic LibioOverflowBase LibioXsputnBase LibioXsputnSetp OsWorld PrintfBufferXsputnCall PrintfBufferXsputnPrelude PrintfBufferXsputnReturn SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import LibioOverflowBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Import LibioXsputnSetp.
Import LibioXsputnBase LibioDefaultXsputnBuf.
Module HLG := LG0.

Section regression.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write)).
Local Instance audit_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Lemma set_bit_write fr fb freg fl f2 fd tw off dq b reg o c xs eb Φ :
  call_frame glibc__IO_new_file_write
    [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) c); WInt (Z.of_nat (length xs))] = Some fr ->
  (c = Obj b \/ c = Ro b) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 2 ->
  find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel) ->
  0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
    icell fb off_total_written tw -∗ icell fb off_offset off -∗ liveq dq b reg -∗ bytesq dq b o xs -∗
    errno_any eb -∗
    ▷ (∀ r fl' tw' off', ⌜fw_post (Z.of_nat (length xs)) fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
       live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
       icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ liveq dq b reg -∗ bytesq dq b o xs -∗
       errno_any eb -∗ Φ (Ret (WInt r))) -∗
    WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hc Hfb Hal Hend Hregend Hbit Hfn Hf2r Hfd Hfl Heb Hb Ho Hbend Hbreg Hxs.
  iIntros "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
  iApply (hi_file_write_dq w0 registry ge Hreg Hext Hwrite
    fr fb freg fl f2 fd tw off dq b reg o c xs eb with
    "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK"); try assumption.
  right. tauto.
Qed.
End regression.
Print Assumptions hi_file_write_dq.
Print Assumptions hi_xsputn.
Print Assumptions hge_xsputn.
Print Assumptions PrintfBufferXsputnCall.wp_printf_xsputn_call.
Print Assumptions PrintfBufferXsputnReturn.wp_printf_xsputn_mismatch.
Print Assumptions PrintfBufferXsputnReturn.wp_printf_xsputn_complete.
Print Assumptions PrintfBufferXsputnPrelude.wp_printf_xsputn_prelude.
Print Assumptions set_bit_write.

(** After writing a string to an unbuffered stream, glibc resets the
    stream's read and write pointers to its short byte. Even a partial
    write leaves nothing buffered. Both paths return the number of bytes
    that the stream actually wrote. *)

From Glibc Require Import Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioPutsInv LibioOverflowBase LibioOverflowShortWrite.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section reset.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The stream offered the entire string to its write function. If the
    write succeeded there is no tail for the default string writer; if
    it stopped early, glibc returns without writing the tail. *)
Lemma wp_xs_short_reset fb freg fl mode rb n r e from Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  Z.land fl 514 <> 0 -> (mode = 0 \/ mode = 2^32-1) -> 0 <= r <= n -> n < 2^63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk15") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt n) ->
  lookup (TAtom "v175") e = Some (WInt n) -> lookup (TAtom "iw_2.v67") e = Some (WInt r) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗ short_ptrs fb rb (short_ptr fb) -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
     short_ptrs fb (short_ptr fb) (short_ptr fb) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_new_file_xsputn e [] None (Enter (TAtom "iw_2.L70") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfb Hal Hend Hrend Hub Hmd Hr Hn Hv0 Hc0 Hc15 Hv4 Hp5 Hv175 Hr67. unfold file_size in Hend.
  iIntros "Hl [%Hfl Hfl] [%Hm Hmode] (Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) HK".
  unfold short_ptr, off_shortbuf, off_buf_base in *. adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrb". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrp". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hre". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hwp". adv. store "Hl" "Hwb". adv.
  load_s32 "Hl" "Hmode". adv. brm Hmd. adv. load_s32 "Hl" "Hfl". adv.
  assert (0 <= Z.land fl 514 < 2^32) by (apply land_lt32; lia). branch_as false. adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hwe". adv.
  destruct (Z.eq_dec r n) as [Heq | Hlt]; [branch_as true; adv; branch_as true | branch_as false]; adv.
  all: iApply wp_ret; [reflexivity | vx |]; iNext;
    match goal with |- environments.envs_entails _ (?post (Ret (WInt ?v))) => replace v with r by (unwrap2; lia) end;
    iApply ("HK" with "Hl [$Hfl //] [$Hmode //] [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]").
Qed.
End reset.

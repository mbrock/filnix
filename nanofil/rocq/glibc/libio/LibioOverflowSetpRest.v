From Glibc Require Import GlibcProgram.
(** This file proves the second half of block `c: L113` of
    `c: _IO_new_file_overflow` (LibioOverflowSetp.v proves the first),
    split off so that each file compiles quickly. Once the write
    pointers are set, the read pointers all go to the read end,
    `c: _IO_CURRENTLY_PUTTING` is set, and the narrow stream goes on to
    block `c: L162` ([wp_ovf_L113_rest]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv LibioLogic
  SysWrappers LibioOverflowBase.
From Glibc Require FileInv LibioLogic LibioOverflowBase OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L113` of `c: _IO_new_file_overflow`. *)
Definition ovf_b113 : block := Eval vm_compute in
  match find_block (TAtom "L113") (fn_blocks glibc__IO_new_file_overflow) with
  | Some b => b | None => mkBlock (TAtom "L113") [] [] JRetVoid end.


Import LibioOverflowBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L162`, as LibioOverflowSetpEnd.v proves it ([wp_ovf_L162]). *)
Context (HL162 : forall fb freg ch f2 fd eb mode vb vreg bb breg sz xs fl tw off from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk30") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  lookup (TAtom "chk34") e = Some (WPtr (mkPtr (fb + off_write_end) (Obj fb))) ->
  lookup (TAtom "chk39") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz 0 (mkPtr (bb + sz) (Obj bb)) xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ (fl' = fl \/ fl' = Z.lor fl io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L162") (Some from))) : sexpr) {{ Φ }}).

(** The rest of block `c: L113` after its seventeenth instruction,
    the store of the write end: the read pointers, the flags, and the
    test of `c: _mode`. *)
Lemma wp_ovf_L113_rest fb freg ch f2 fd eb mode vb vreg bb breg sz xs fl tw off rest j e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  rest = skipn 17 (b_insts ovf_b113) -> j = b_jump ovf_b113 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk24") e = Some (WPtr (mkPtr (fb + off_read_ptr) (Obj fb))) ->
  lookup (TAtom "v133") e = Some (WPtr (mkPtr (fb + off_read_ptr) (Obj fb))) ->
  lookup (TAtom "chk30") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  lookup (TAtom "chk34") e = Some (WPtr (mkPtr (fb + off_write_end) (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz 0 (mkPtr (bb + sz) (Obj bb)) xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ (fl' = Z.lor fl 2048 \/ fl' = Z.lor (Z.lor fl 2048) io_err_seen)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Exec (TAtom "L113") rest j)) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hch Hf2 Hf2r Hfd Happ He Hmd -> -> Hv0 Hv2 Hc0 Hc24 Hv133 Hc30 Hc34.
  iIntros "#Hvt Hl Hfx Hst HK". unfold file_size in Hend.
  iDestruct "Hst" as "(%Hp & Hbl & Hxs & [%Hflr Hflb] & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
  destruct Hp as (Hbb & Hbe & Hbreg & Hsz & Hkr & Hxl & Hxr & Hwec & Hwea). rewrite Z.add_0_r.
  cbn [ovf_b113 b_insts b_jump skipn]. adv.
  load_pointer "Hl Hre Hbl" by ar.
  iNext. iIntros "Hl Hre Hbl". adv.
  store_pointer "Hl Hrp" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hrp". adv.
  store_pointer "Hl Hrb" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hrb". adv. load_s32_group "Hl Hflb". adv.
  store_word "Hl Hflb" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hflb".
  assert (Hlo : 0 <= Z.lor fl 2048 < 2 ^ 32) by (apply lor_lt32; lia).
  try change (2048 mod 2 ^ 32) with 2048. try (rewrite (Z.mod_small fl); [|lia]).
  try (rewrite (Z.mod_small (Z.lor fl 2048)); [|lia]).
  iDestruct "Hfx" as "(Hf2 & Hfd & Herr & Hcol & [%Hm Hmb] & Hvtp)".
  adv. load_s32_group "Hl Hmb". adv. brm Hmd.
  assert (Happ' : Z.land (Z.lor fl 2048) io_is_appending = 0) by (rewrite land_lor_const; [exact Happ | reflexivity]).
  iApply (HL162 with "Hvt Hl [$Hf2 $Hfd $Herr $Hcol $Hmb $Hvtp //] [Hbl Hxs Hflb Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend] HK");
    try first [libio_side | lk_prove |
      iApply (ovf_state_base with "Hbl Hxs [$Hflb //] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend");
        try first [assumption | reflexivity | cbn; lia]].
Qed.

End rules.

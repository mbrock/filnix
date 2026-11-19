(** Glibc switches an unbuffered stream into write mode before it sends
    the first character. It copies its read pointer to the write base
    and then sets the write end to that same address. This leaves no
    room for a caller to write straight into the short buffer. *)

From Glibc Require Import Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry FileInv LibioLogic
  LibioPutsInv LibioOverflowBase LibioOverflowShortWrite.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section put.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Both a newly installed short buffer and one left idle by a previous
    call have their read pointer and read end at the short byte. The
    switch uses those fields but overwrites all three old write cursors. *)
Lemma wp_short_put fb freg ch fl mode rb wb wp we from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  Z.land fl 256 = 0 -> Z.land fl 2 <> 0 -> (mode = 0 \/ mode = 2^32-1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk6") e = Some (WPtr (mkPtr (fb+off_write_base) (Obj fb))) ->
  let sb := short_ptr fb in
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_read_ptr sb -∗ pcell fb 16 sb -∗ pcell fb 24 rb -∗
  pcell fb off_write_base wb -∗ pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base sb -∗ pcell fb off_buf_end (mkPtr (fb+132) (Obj fb)) -∗
  ▷ (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr fb (Obj fb))) /\
            lookup (TAtom "v2") e' = Some (WInt ch) /\ lookup (TAtom "chk0") e' = Some (WPtr (mkPtr fb (Obj fb)))⌝ -∗
    live fb freg -∗ int_cell fb off_flags (Z.lor fl 2048) -∗ int_cell fb off_mode mode -∗ short_ptrs fb sb sb -∗
    WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_new_file_overflow e' [] None (Enter (TAtom "L18") (Some (TAtom "L155")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_new_file_overflow e [] None (Enter (TAtom "L35") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfb Hal Hend Hrend Hbk Hu Hmd Hv0 Hv2 Hc0 Hc6. cbn zeta.
  iIntros "Hl [%Hfl Hflags] [%Hm Hmode] Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HK".
  unfold file_size in Hend. unfold short_ptr, off_shortbuf. adv. load_s32 "Hl" "Hflags". adv. branch_as true.
  adv. load_self_using wp_raw_load_pointer_self "Hl Hrp". adv. load_self_using wp_raw_load_pointer_self "Hl Hbend".
  adv. branch_as true. adv. load_self_using wp_raw_load_pointer_self "Hl Hrp". adv. store "Hl" "Hwp".
  adv. load_self_using wp_raw_load_pointer_self "Hl Hwp". adv. store "Hl" "Hwb".
  adv. load_self_using wp_raw_load_pointer_self "Hl Hbend". adv. store "Hl" "Hwe".
  adv. load_self_using wp_raw_load_pointer_self "Hl Hre". adv. store "Hl" "Hrp". adv. store "Hl" "Hrb".
  adv. load_s32 "Hl" "Hflags". adv. store_int "Hl" "Hflags".
  assert (Hlo : 0 <= Z.lor fl 2048 < 2^32) by (apply lor_lt32; lia).
  try change (2048 mod 2^32) with 2048. try (rewrite (Z.mod_small fl); [|lia]).
  try (rewrite (Z.mod_small (Z.lor fl 2048)); [|lia]). adv. load_s32 "Hl" "Hmode". adv. brm Hmd.
  adv. load_s32 "Hl" "Hflags". adv.
  assert (Hu' : Z.land (Z.lor fl 2048) 514 <> 0).
  { rewrite land_lor_const; [|reflexivity]. intro Hz. apply Hu. change 2 with (Z.land 514 2). by rewrite Z.land_assoc Hz. }
  assert (0 <= Z.land (Z.lor fl 2048) 514 < 2^32) by (apply land_lt32; lia).
  branch_as false. adv. load_self_using wp_raw_load_pointer_self "Hl Hwp". adv. store "Hl" "Hwe". step.
  iApply ("HK" with "[%] Hl [$Hflags //] [$Hmode //] [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]").
  repeat split; lk_prove.
Qed.
End put.

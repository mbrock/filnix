From Glibc Require Import GlibcProgram.
(** Printf finds the stream operation through FILE's jump table before
    sending its staged bytes. It computes the byte count from its staging
    pointer and checks that the jump table belongs to glibc.

    Reading these pointers does not change the FILE or printf buffer.
    This proof establishes which function printf will call and how many bytes
    it will request. It does not prove the call itself. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioPutsInv LibioXsputnCode PrintfBufferFileCode PrintfBufferXsputnReturn.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hfn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).

(** An empty staging array requests zero bytes, and a full array requests 128.
    Every position between these endpoints gives its exact byte count. *)
Lemma wp_printf_xsputn_prelude e from bb breg fb freg dqf vb vreg n Φ :
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= n <= 128 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (bb + 8) (Obj bb))) ->
  vtables_ro ge vb vreg -∗ live bb breg -∗ liveq dqf fb freg -∗
  pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
  pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb))) /\
      lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (bb + 24) (Obj bb))) /\
      lookup (TAtom "v48") e' = Some (WPtr (sym_ptr ge "_IO_new_file_xsputn")) /\
      lookup (TAtom "v51") e' = Some (WPtr (mkPtr fb (Obj fb))) /\
      lookup (TAtom "v53") e' = Some (WPtr (mkPtr (bb + 48) (Obj bb))) /\
      lookup (TAtom "v37") e' = Some (WInt n)⌝ -∗
    live bb breg -∗ liveq dqf fb freg -∗
    pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗
    pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Exec (TAtom "iw_1.join") (skipn 7 (b_insts printf_xsputn_block))
        (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Enter (TAtom "L14") from)) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfr Hn Hv0 Hchk Hchk1.
  iIntros "#Hvt Hb Hf Hptr Hfp Hvtp HK".
  iPoseProof (vtables_slot ge vb vreg slot_xsputn "_IO_new_file_xsputn"
    with "Hvt") as "#Hsx"; [cbn; tauto |].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_xsputn")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfn). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  iApply wp_enter; [reflexivity | destruct from; reflexivity |].
  iNext. cbn [b_insts b_jump]. step.
  iApply (wp_raw_load_pointer_self with "Hb Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hb Hptr". step. step. step. step. step. check "Hb".
  load_pointer_dq "Hb Hfp Hf" by a2.
  iNext. iIntros "Hb Hfp Hf". step. check_shared "Hf".
  iApply (wp_raw_load_pointer_dq with "Hf Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file; lia |].
  iNext. iIntros "Hf Hvtp #Hvl'". step. step. step. step. step. branch_as true. step. step.
  check_read_dq "Hvl'" by a2.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsx Hfc");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hfn) |].
  iNext. iIntros "_ _ _". step. check "Hb".
  load_pointer_dq "Hb Hfp Hf" by a2.
  iNext. iIntros "Hb Hfp Hf". step.
  iApply ("HK" $! _ with "[%] Hb Hf Hptr Hfp Hvtp").
  split_and!; lookups; try reflexivity.
  - do 3 f_equal; cbn [ptr_addr ptr_cap]; unwrap2; lia.
  - do 2 f_equal; unwrap2; lia.
Qed.

End rules.

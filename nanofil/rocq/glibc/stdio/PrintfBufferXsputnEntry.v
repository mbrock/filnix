(** Flushing printf's staging array first adds its pending bytes to the
    accumulated count. The flush then recognizes the staging array by its end
    pointer and enters the xsputn path.

    This rule follows those instructions without calling the stream.
    It preserves the staging pointers and exposes the updated unsigned count,
    including wraparound, to the continuation at L14. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioPutsInv PrintfBufferFileCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance entry_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Each pointer into the staging array shares its containing allocation's lifetime. *)


(** The update counts every staged byte, including an empty or full array.
    The continuation receives the checked addresses needed by the L14 pointer reads. *)
Lemma wp_printf_xsputn_entry fr bb breg n written Φ :
  call_frame glibc___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 <= n <= 128 -> 0 <= written < 2 ^ 64 ->
  live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
  pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ icell bb 24 written -∗
  (∀ e, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) /\
    lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) /\
    lookup (TAtom "chk1") e = Some (WPtr (mkPtr (bb + 8) (Obj bb)))⌝ -∗
    live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
    pcell bb 8 (mkPtr (bb + 48 + n) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ icell bb 24 ((written + n) mod 2 ^ 64) -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
      (Enter (TAtom "L14") (Some (TAtom "start")))) : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hn Hw. injection Hfr as <-.
  iIntros "Hb Hbase Hptr Hend Hw HK".
  step. step. check "Hb".
  iApply (wp_raw_load_read_dq with "Hb Hw"); [reflexivity | vx | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hw".
  step. check "Hb". load_self_using (wp_raw_load_pointer_self w0 registry ge) "Hb Hptr".
  check "Hb". load_self_using (wp_raw_load_pointer_self w0 registry ge) "Hb Hbase".
  step. step. step. step. check "Hb". store_long "Hb" "Hw".
  step. load_self_using (wp_raw_load_pointer_self w0 registry ge) "Hb Hend". step. step. step. step. step. branch_as false.
  iApply ("HK" $! _ with "[%] Hb Hbase Hptr Hend [Hw]").
  - split_and!; lookups; try reflexivity;
      do 3 f_equal; cbn [ptr_addr ptr_cap]; unwrap2; lia.
  - norm. replace (bb + 48 + n - (bb + 48)) with n by lia.
    iEval (rewrite Z.mod_mod; [|lia]) in "Hw".
    iExact "Hw".
Qed.

End rules.

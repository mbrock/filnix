From Glibc Require Import GlibcProgram.
(** Block `c: L107` of `c: fputs(s, fp)` (LibioPutsCode.v,
    libio/iofputs.c), `c: _IO_release_lock(fp)`: the stream's lock,
    which LibioFputsLock.v's [wp_fputs_start] took, is released, the
    owner becoming null and the lock word 0 since the count is 0 and
    the process single-threaded, and the result is returned
    ([wp_fputs_unlock]). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  LibioPutsCode LibioPutsInv LibioFputsLock.
From Glibc Require FileInv LibioCloseSteps LibioFputsLock LibioLogic LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L107` of `c: fputs` after its phi, which releases the
    lock. *)
Definition fp_L107 : block := Eval vm_compute in
  match find_block (TAtom "L107") (fn_blocks glibc__IO_fputs) with
  | Some b => b | None => mkBlock (TAtom "L107") [] [] JRetVoid end.


Import LibioFputsLock LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L107` of `c: fputs`, its result r in `c: pr.1` and the
    stream fb in `c: v2` and `c: chk0`: the lock lb, held once by this
    thread, is released, the owner becoming null and the lock word 0,
    and r is returned. *)
Lemma wp_fputs_unlock e r fb freg fl lb lbreg sb sreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v2") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "pr.1") e = Some (WInt r) -> 0 <= r < 2 ^ 32 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 1 0 (ow_self w0) -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 0 0 null -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_fputs e [] None (Exec (TAtom "L107") (b_insts fp_L107) (b_jump fp_L107)))
        : sexpr) {{ Φ }}.
Proof.
  intros fp Hv2 Hc0 Hr Hrr Hfb Hfal Hfend Hfreg Hfl Hul. subst fp.
  unfold file_size in Hfend.
  assert (Hcu' : Z.land (fl mod 2 ^ 32) (32768 mod 2 ^ 32) mod 2 ^ 32 = 0).
  { rewrite (Z.mod_small fl); [|lia]. change (32768 mod 2 ^ 32) with 32768. rewrite Hul. reflexivity. }
  iIntros "#Hs Hl [_ Hfl] Hlp Hlb HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  cbn [fp_L107 b_insts b_jump].
  (* The user lock is clear, and the process single-threaded. *)
  check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  (* The count is 0: the owner becomes null, then the lock word 0. *)
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_s32 "Hbl" "Hb4". step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo".
  check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0". step.
  step. iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (Z.mod_small r); [|lia].
  iApply ("HK" with "Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo]").
  - iSplit; [done | iExact "Hfl"].
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.

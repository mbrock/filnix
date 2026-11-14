From Glibc Require Import GlibcProgram.
(** One write of `c: _IO_new_file_write`'s loop (LibioWrite.v
    describes the function), from block `c: L9` to the return of its
    call of `c: __write` ([wp_file_write_call]).

    The triple of `c: _IO_new_file_write` (LibioReadCode.v), the jump
    table's write: it hands the bytes from data to
    `c: __write(fp->_fileno, ...)` until all are written or a call
    fails, which sets `c: _IO_ERR_SEEN`, then counts what it wrote into
    `c: _total_written` and, when known, `c: _offset`.

    A write may take fewer bytes than asked, so the loop runs again on
    the rest, by Löb induction over the head of block `c: L8`
    ([wp_file_write_loop]), whose environment is the earlier one with
    the two phis `c: pr.1` (the next byte) and `c: pr.2` (the bytes
    left) put on top. The stream's `c: _flags2` has
    `c: _IO_FLAGS2_NOTCANCEL` clear, as a stream `c: fopen` did not
    open with "c" has, so the loop calls `c: __write`, the alias of
    `c: __libc_write`. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers LibioWriteExit.
From Glibc Require FileInv LibioLogic LibioWriteExit OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioWriteExit SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context `{Hwrite : !Defines ge "__GI___write" glibc___libc_write}.

Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L9` of `c: _IO_new_file_write`, t > 0 of the n bytes xs
    left: `c: _IO_FLAGS2_NOTCANCEL` is clear, so it calls
    `c: __write(fp->_fileno, p, t)` with p the next byte, and resumes
    at the end of block `c: L15` with its result k in `c: v36`. *)
Lemma wp_file_write_call fb freg f2 fd b reg o xs eb t e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 < t <= Z.of_nat (length xs) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "pr.2") e = Some (WInt t) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b + o + (Z.of_nat (length xs) - t)) (Obj b))) ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ live b reg -∗ bytes b o xs -∗
  errno_any eb -∗
  ▷ (∀ e' k, ⌜keeps (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) e e' /\
              lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (fb + off_flags2) (Obj fb))) /\
              lookup (TAtom "v36") e' = Some (WInt k) /\
              ((0 <= k <= t /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1)⌝ -∗
     live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ live b reg -∗ bytes b o xs -∗
     errno_any eb -∗
     WP (ERun (mkFrame glibc__IO_new_file_write e' [] None (Exec (TAtom "L15") [] (JGoto (To (TAtom "L16")))))
           : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_new_file_write e [] None (Enter (TAtom "L9") (Some (TAtom "L8")))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hf2 Hf2r Hfd He Hb Ho Hbend Hreg' Hy Ht Hv0 Ht' Hp. unfold file_size in Hend.
  iIntros "Hl Hfl2 Hfd Hbl Hxs Herr HK".
  assert (Hlen : 0 <= Z.of_nat (length xs) < 2 ^ 63) by lia.
  step. step. norm. check "Hl". iDestruct "Hfl2" as "[%Hf2' Hfl2]". load_s32_group "Hl Hfl2". step. step. step. step. step.
  rewrite (flags2_mask f2 2 1); [|reflexivity | lia | exact Hf2r]. rewrite Hf2. branch.
  step. step. norm. check "Hl". iDestruct "Hfd" as "[%Hfd' Hfdb]". load_s32_group "Hl Hfdb".
  iApply wp_call_bind; [vx | exact Hwrite | reflexivity |]. iNext.
  iPoseProof (live_bytes_pts with "Hbl Hxs") as "Hps".
  iApply (wp_glibc___libc_write Hreg Hext with "Hps Herr");
    [reflexivity | apply Z.mod_pos_bound; lia | unwrap; lia | exact He | rewrite Z.mod_small; [exact Hfd | lia] | |].
  { intros m Hm. apply all_agree_app in Hm as [[Hlv _] Hm]. cbn [agree_piece fst snd] in Hlv.
    unwrap. replace t with (Z.of_nat (length xs) - (Z.of_nat (length xs) - t)) at 2 by lia.
    apply (bytes_os_readable m b reg o xs); auto; lia. }
  iNext. iIntros (k Hk) "Hps Herr". iDestruct (pts_live_bytes with "Hps") as "[Hbl Hxs]". resume_ret.
  iApply ("HK" $! _ k with "[%] Hl [$Hfl2 //] [$Hfdb //] Hbl Hxs Herr").
  assert (Hk64 : 0 <= k < 2 ^ 64) by lia.
  split_and!; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; lookups; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; reflexivity | lookups; reflexivity | | ].
  - lookups. rewrite Z.mod_small; [reflexivity | exact Hk64].
  - rewrite Z.mod_small in Hk; [exact Hk | lia].
Qed.

End rules.

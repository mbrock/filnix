(** The triple of `c: _IO_new_file_write` (LibioReadCode.v), the jump
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

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers LibioWriteExit LibioWriteCall.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioWriteOn (R : Runtime) (LG0 : LogicSig R).
Module WC := LibioWriteCallOn R LG0.
Module WE := WC.WE.
Module SW := WE.SW.
Import WC WE SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write)).

Local Instance write_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The loop of `c: _IO_new_file_write(fp, data, n)` at its head, t of
    the n bytes xs at offset o of b left to write. *)
Lemma wp_file_write_loop fb freg fl f2 fd b reg o xs eb Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  ⊢ ∀ e t tw off, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
            lookup (TAtom "v4") e = Some (WInt (Z.of_nat (length xs))) /\
            lookup (TAtom "pr.2") e = Some (WInt t) /\
            lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b + o + (Z.of_nat (length xs) - t)) (Obj b))) /\
            0 <= t <= Z.of_nat (length xs)⌝ -∗
    live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
    icell fb off_total_written tw -∗ icell fb off_offset off -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
    ▷ (∀ r fl' tw' off', ⌜fw_post (Z.of_nat (length xs)) fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
       live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
       icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live b reg -∗ bytes b o xs -∗ errno_any eb -∗
       Φ (Ret (WInt r))) -∗
    WP (ERun (mkFrame glibc__IO_new_file_write e [] None (Exec (TAtom "L8") (b_insts fw_L8) (b_jump fw_L8)))
          : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hf2 Hf2r Hfd Hflr He Hb Ho Hbend Hreg' Hy. unfold file_size in Hend.
  iLöb as "IH". iIntros (e t tw off (Hv0 & Hv4 & Ht & Hp & Htr)) "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
  assert (Hlen : 0 <= Z.of_nat (length xs) < 2 ^ 63) by lia.
  cbn [fw_L8 b_insts b_jump]. st. destruct (Z.eq_dec t 0) as [-> | Ht0].
  { brv true. iApply (wp_file_write_exit w0 registry ge with "Hl Hoff"); try wside. iNext. iIntros (off') "Hl Hoff".
    rewrite Z.sub_0_r. iApply ("HK" with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr").
    split; [left; split; reflexivity | exact Hflr]. }
  brv false.
  iApply (wp_file_write_call w0 registry ge Hreg Hext Hwrite fb freg f2 fd b reg o xs eb t with "Hl Hfl2 Hfd Hbl Hxs Herr");
    try wside.
  iNext. iIntros (e' k (Hsame & Hc0 & Hk36 & Hk)) "Hl Hfl2 Hfd Hbl Hxs Herr".
  pose proof (Hsame (TAtom "v0") ltac:(auto)) as Hv0'. pose proof (Hsame (TAtom "v4") ltac:(auto)) as Hv4'.
  pose proof (Hsame (TAtom "pr.1") ltac:(auto)) as Hp''. pose proof (Hsame (TAtom "pr.2") ltac:(auto)) as Ht''.
  assert (Hv0n : lookup (TAtom "v0") e' = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hv0'; lookups; reflexivity).
  assert (Hv4n : lookup (TAtom "v4") e' = Some (WInt (Z.of_nat (length xs)))) by (rewrite Hv4'; lookups; reflexivity).
  assert (Hpn : lookup (TAtom "pr.1") e' = Some (WPtr (mkPtr (b + o + (Z.of_nat (length xs) - t)) (Obj b))))
    by (rewrite Hp''; lookups; reflexivity).
  assert (Htn : lookup (TAtom "pr.2") e' = Some (WInt t)) by (rewrite Ht''; lookups; reflexivity).
  clear Hsame Hv0' Hv4' Hp'' Ht'' Hv0 Hv4 Hp Ht.
  st. st. st. destruct Hk as [Hk | ->].
  2: { brv false.
       iApply (wp_file_write_err w0 registry ge with "Hl [$Hfl //] Hoff");
         try wside.
       iNext. iIntros (off') "Hl Hfl Hoff".
       iApply ("HK" $! _ (Z.lor fl io_err_seen) with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr").
       split; [right; split; [lia | reflexivity] | apply lor_lt32; unfold io_err_seen; lia]. }
  destruct Hk as [[Hk0 Hkn] Hk31]. try (rewrite Z.mod_small in Hkn; [|lia]). brv true.
  iApply (wp_file_write_next w0 registry ge fb freg tw t k (mkPtr (b + o + (Z.of_nat (length xs) - t)) (Obj b))
            with "Hl Htw");
    try wside.
  iNext. iIntros (e2 tw' (Hv02 & Hv42 & Ht2 & Hp2)) "Hl Htw".
  iApply ("IH" $! _ (t - k) _ off with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK").
  split_and!; [rewrite Hv02; lookups; reflexivity | rewrite Hv42; lookups; reflexivity | exact Ht2 | | lia | lia].
  rewrite Hp2. cbn [ptr_addr ptr_cap]. do 3 f_equal. lia.
Qed.

(** `c: _IO_new_file_write(fp, data, n)` of the n bytes xs at offset o
    of the object b, through `c: __write` on the stream's
    `c: _fileno`: r of them written, [fw_post]. *)
Lemma wp_glibc__IO_new_file_write fr fb freg fl f2 fd tw off b reg o xs eb Φ :
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
  intros Hfr. injection Hfr as <-. intros. iIntros "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
  enter. st. iApply wp_enter; [reflexivity | reflexivity | iNext].
  iApply (wp_file_write_loop with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK"); try eassumption.
  assert (Z.of_nat (length xs) < 2 ^ 63) by lia.
  split_and!; try reflexivity; cbn; try (unwrap; lia). do 3 f_equal. arith.
Qed.


End rules.
End LibioWriteOn.

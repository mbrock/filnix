From Glibc Require Import GlibcProgram.
(** `c: fputs` and `c: puts` hand `c: _IO_new_file_xsputn` the
    caller's string, which they may only read: it can be a string
    literal behind a read-only pointer, or a string the caller shares
    with others. This file proves one write of `c: _IO_new_file_write`'s
    loop for such a buffer, from block `c: L9` to the return of its
    call of `c: __write`. LibioWriteDq.v proves the whole function
    from it.

    The kernel only reads the buffer, and a share of its pieces tells
    the same facts about memory as the whole (Logic.v's [ptsq_facts]),
    so the rules of LibioWriteCall.v, OsWrite.v and SysWrappers.v hold
    at a share too:

    | Lemma | The rule at a share of |
    |---|---|
    | [wp_zsys_write_dq] | OsWrite.v's [wp_zsys_write] |
    | [wp_glibc___libc_write_dq] | SysWrappers.v's [wp_glibc___libc_write] |
    | [wp_file_write_call_dq] | LibioWriteCall.v's [wp_file_write_call] | *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsWrite OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers LibioWriteExit.
From Glibc Require FileInv LibioLogic LibioWriteExit OsWorld OsWrite SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The bytes xs from offset o of the live object b pass
    `c: filc_check_read` from any offset i among them through a
    pointer of either capability c of b: LibioWriteExit.v's
    [bytes_os_readable] for a read-only pointer too. *)
Lemma bytes_os_readable_cap m b reg o xs i c :
  c = Obj b \/ c = Ro b ->
  live_at m b reg -> all_agree m (byte_ps b o xs) -> Forall (fun x => 0 <= x < 256) xs ->
  0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> 0 <= i <= Z.of_nat (length xs) ->
  0 <= b -> b + o + Z.of_nat (length xs) < 2 ^ 64 ->
  os_readable m (mkPtr (b + o + i) c) (Z.of_nat (length xs) - i).
Proof.
  intros Hc Hl Hx Hy Ho Hend Hi Hb H64. split; [lia|]. right. split; [lia|].
  split; [exists b, reg; split; [exact Hc | exact Hl]|]. split.
  - apply (access_read _ b reg); [exact Hc | exact (proj1 Hl) | cbn; lia | cbn; lia | apply Z.mod_1_r].
  - intros k Hk. cbn [ptr_addr]. destruct (lookup_lt_is_Some_2 xs (Z.to_nat (i + k)) ltac:(lia)) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (Hv & _ & _).
    replace (b + o + i + k) with (b + (o + Z.of_nat (Z.to_nat (i + k)))) by lia. rewrite Hv.
    exact (Forall_lookup_1 _ _ _ _ Hy Hxi).
Qed.


Import LibioWriteExit SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
Lemma liveq_bytesq_ptsq dq b reg o xs :
  liveq dq b reg -∗ bytesq dq b o xs -∗ ptsq dq ([(PLive b, VLive reg)] ++ byte_ps b o xs).
Proof. iIntros "Hl Hb". rewrite ptsq_app. iFrame. Qed.
Lemma ptsq_liveq_bytesq dq b reg o xs :
  ptsq dq ([(PLive b, VLive reg)] ++ byte_ps b o xs) -∗ liveq dq b reg ∗ bytesq dq b o xs.
Proof. rewrite ptsq_app. auto. Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context `{Hwrite : !Defines ge "__GI___write" glibc___libc_write}.


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zsys_write(fd, p, n)` with `c: fd` among w0's descriptors, the
    pieces ps owned at the share dq making `c: p` pass
    `c: filc_check_read(p, n)` ([os_readable]) and errno owned: ps and
    errno come back, and d is bound to a count up to n and below 2^31
    or `c: -1`. OsWrite.v's [wp_zsys_write] at a share. *)
Lemma wp_zsys_write_dq f e ls lab d a0 a1 a2 rest j fd p n eb dq ps Φ :
  registry (TAtom "zsys_write") = Some os_write_contract ->
  find_fn ge (TAtom "zsys_write") = None -> lookup (TAtom "zsys_write") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1; Arg L a2] = Some [WInt fd; WPtr p; WInt n] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> os_readable m p n) ->
  ptsq dq ps -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ ptsq dq ps -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt (k mod 2 ^ 64)) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_write")) [Arg W a0; Arg P a1; Arg L a2]
                        :: rest) j)) : sexpr)
    {{ Φ }}.
Proof.
  intros Hrg Hfn Hdata Hx He Hin Hrd. iIntros "Hps Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [] (ptsq dq ps)
            (fun vs => exists k, vs = [WInt k] /\ ((0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1))
            with "Hps Herr [] [HK]"); [done | done | done | exact Hrg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (ptsq_facts with "Hσ Hps") as %(Ha & _).
    iDestruct (os_heap_ready with "Hσ") as %(-> & Hfd & Hc); [exact He | exact Hin|].
    iPureIntro. split; [exists fd, p, n, (mkPtr eb (Obj eb)); auto|]. split; [constructor|].
    exists []. split; [reflexivity | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro.
    destruct (OsWrite.os_write_returns _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & fd' & p' & n' & k & Hx' & -> & Hk).
    injection Hx' as <- <- <-. split; [reflexivity|]. eauto.
  - iApply blks_nil.
  - iNext. iIntros (vs (k & -> & Hk)) "Hps Herr _". iExists _. iSplit; [done|].
    iApply ("HK" with "[%] Hps Herr"). exact Hk.
Qed.

(** `c: __libc_write(fd, p, n)` over pieces owned at the share dq:
    SysWrappers.v's [wp_glibc___libc_write] at a share. *)
Lemma wp_glibc___libc_write_dq fr fd p n eb dq ps Φ :
  call_frame glibc___libc_write [WInt fd; WPtr p; WInt n] = Some fr ->
  0 <= fd < 2 ^ 32 -> 0 <= n < 2 ^ 64 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> os_readable m p n) ->
  ptsq dq ps -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ ptsq dq ps -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd Hn He Hin Hrd. injection Hfr as <-. iIntros "Hps Herr HK". step.
  iApply (wp_zsys_write_dq with "Hps Herr");
    [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
    | apply (ext_data ge Hext); cbn; tauto | cbn; repeat (rewrite Z.mod_small; [|lia]); reflexivity
    | exact He | exact Hin | exact Hrd |].
  iNext. iIntros (k Hk) "Hps Herr".
  assert (Hk' : 0 <= k < 2 ^ 64) by lia.
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite !(Z.mod_small k); [|lia|lia].
  iNext. iApply ("HK" with "[%] Hps Herr"). exact Hk.
Qed.

(** The noncanceling wrapper calls the same OS write contract directly.
    It preserves fractional source ownership and errno ownership without
    inspecting or changing the caller's cancellation state. *)
Lemma wp_glibc___write_nocancel_dq fr fd p n eb dq ps Φ :
  call_frame glibc___write_nocancel [WInt fd; WPtr p; WInt n] = Some fr ->
  0 <= fd < 2 ^ 32 -> 0 <= n < 2 ^ 64 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> os_readable m p n) ->
  ptsq dq ps -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ ptsq dq ps -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd Hn He Hin Hrd. injection Hfr as <-. iIntros "Hps Herr HK". step.
  iApply (wp_zsys_write_dq with "Hps Herr");
    [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
    | apply (ext_data ge Hext); cbn; tauto | cbn; repeat (rewrite Z.mod_small; [|lia]); reflexivity
    | exact He | exact Hin | exact Hrd |].
  iNext. iIntros (k Hk) "Hps Herr".
  assert (Hk' : 0 <= k < 2 ^ 64) by lia.
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite !(Z.mod_small k); [|lia|lia].
  iNext. iApply ("HK" with "[%] Hps Herr"). exact Hk.
Qed.

(** The life and bytes of a share, as one list of pieces. *)

(** The list back as the life and bytes. *)

(** Block `c: L9` of `c: _IO_new_file_write`, t > 0 of the n bytes xs
    owned at the share dq left, through a pointer of capability c of
    their object b: as LibioWriteCall.v's [wp_file_write_call], it
    calls `c: __write(fp->_fileno, p, t)` and resumes at the end of
    block `c: L15` with its result k in `c: v36`. *)
Lemma wp_file_write_call_dq fb freg f2 fd dq b reg c o xs eb t e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> c = Obj b \/ c = Ro b ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 < t <= Z.of_nat (length xs) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "pr.2") e = Some (WInt t) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b + o + (Z.of_nat (length xs) - t)) c)) ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ liveq dq b reg -∗
  bytesq dq b o xs -∗ errno_any eb -∗
  ▷ (∀ e' k, ⌜keeps (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) e e' /\
              lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (fb + off_flags2) (Obj fb))) /\
              lookup (TAtom "v36") e' = Some (WInt k) /\
              ((0 <= k <= t /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1)⌝ -∗
     live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ liveq dq b reg -∗
     bytesq dq b o xs -∗ errno_any eb -∗
     WP (ERun (mkFrame glibc__IO_new_file_write e' [] None (Exec (TAtom "L15") [] (JGoto (To (TAtom "L16")))))
           : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_new_file_write e [] None (Enter (TAtom "L9") (Some (TAtom "L8")))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hf2 Hf2r Hfd He Hc Hb Ho Hbend Hreg' Hy Ht Hv0 Ht' Hp. unfold file_size in Hend.
  iIntros "Hl Hfl2 Hfd Hbl Hxs Herr HK".
  assert (Hlen : 0 <= Z.of_nat (length xs) < 2 ^ 63) by lia.
  step. step. norm. check "Hl". iDestruct "Hfl2" as "[%Hf2' Hfl2]". load_s32_group "Hl Hfl2". step. step. step. step. step.
  rewrite (flags2_mask f2 2 1); [|reflexivity | lia | exact Hf2r]. rewrite Hf2. branch.
  step. step. norm. check "Hl". iDestruct "Hfd" as "[%Hfd' Hfdb]". load_s32_group "Hl Hfdb".
  iApply wp_call_bind; [vx | exact Hwrite | reflexivity |]. iNext.
  iPoseProof (liveq_bytesq_ptsq with "Hbl Hxs") as "Hps".
  iApply (wp_glibc___libc_write_dq with "Hps Herr");
    [reflexivity | apply Z.mod_pos_bound; lia | unwrap; lia | exact He | rewrite Z.mod_small; [exact Hfd | lia] | |].
  { intros m Hm. apply all_agree_app in Hm as [[Hlv _] Hm]. cbn [agree_piece fst snd] in Hlv.
    unwrap. replace t with (Z.of_nat (length xs) - (Z.of_nat (length xs) - t)) at 2 by lia.
    apply (bytes_os_readable_cap m b reg o xs); auto; lia. }
  iNext. iIntros (k Hk) "Hps Herr". iDestruct (ptsq_liveq_bytesq with "Hps") as "[Hbl Hxs]". resume_ret.
  iApply ("HK" $! _ k with "[%] Hl [$Hfl2 //] [$Hfdb //] Hbl Hxs Herr").
  assert (Hk64 : 0 <= k < 2 ^ 64) by lia.
  split_and!; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; lookups; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; reflexivity | lookups; reflexivity | | ].
  - lookups. rewrite Z.mod_small; [reflexivity | exact Hk64].
  - rewrite Z.mod_small in Hk; [exact Hk | lia].
Qed.

(** A stream can request writes that leave thread cancellation state
    alone. This rule follows that branch through the captured wrapper.
    It preserves the exact flags and fractional source ownership even
    when the OS write fails. *)
Lemma wp_file_write_call_nocancel_dq
    (Hnocancel : find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel))
    fb freg f2 fd dq b reg c o xs eb t e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 2 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> c = Obj b \/ c = Ro b ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 < t <= Z.of_nat (length xs) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "pr.2") e = Some (WInt t) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b + o + (Z.of_nat (length xs) - t)) c)) ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ liveq dq b reg -∗
  bytesq dq b o xs -∗ errno_any eb -∗
  ▷ (∀ e' k, ⌜keeps (atoms ["v0"; "v4"; "pr.1"; "pr.2"]) e e' /\
              lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (fb + off_flags2) (Obj fb))) /\
              lookup (TAtom "v30") e' = Some (WInt k) /\
              ((0 <= k <= t /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1)⌝ -∗
     live fb freg -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗ liveq dq b reg -∗
     bytesq dq b o xs -∗ errno_any eb -∗
     WP (ERun (mkFrame glibc__IO_new_file_write e' [] None (Exec (TAtom "L14") [] (JGoto (To (TAtom "L16")))))
           : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_new_file_write e [] None (Enter (TAtom "L9") (Some (TAtom "L8")))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hf2 Hf2r Hfd He Hc Hb Ho Hbend Hreg' Hy Ht Hv0 Ht' Hp. unfold file_size in Hend.
  iIntros "Hl Hfl2 Hfd Hbl Hxs Herr HK".
  assert (Hlen : 0 <= Z.of_nat (length xs) < 2 ^ 63) by lia.
  step. step. norm. check "Hl". iDestruct "Hfl2" as "[%Hf2' Hfl2]". load_s32_group "Hl Hfl2". step. step. step. step. step.
  rewrite (flags2_mask f2 2 1); [|reflexivity | lia | exact Hf2r]. rewrite Hf2. branch.
  step. step. norm. check "Hl". iDestruct "Hfd" as "[%Hfd' Hfdb]". load_s32_group "Hl Hfdb".
  iApply wp_call_bind; [vx | exact Hnocancel | reflexivity |]. iNext.
  iPoseProof (liveq_bytesq_ptsq with "Hbl Hxs") as "Hps".
  iApply (wp_glibc___write_nocancel_dq with "Hps Herr");
    [reflexivity | apply Z.mod_pos_bound; lia | unwrap; lia | exact He | rewrite Z.mod_small; [exact Hfd | lia] | |].
  { intros m Hm. apply all_agree_app in Hm as [[Hlv _] Hm]. cbn [agree_piece fst snd] in Hlv.
    unwrap. replace t with (Z.of_nat (length xs) - (Z.of_nat (length xs) - t)) at 2 by lia.
    apply (bytes_os_readable_cap m b reg o xs); auto; lia. }
  iNext. iIntros (k Hk) "Hps Herr". iDestruct (ptsq_liveq_bytesq with "Hps") as "[Hbl Hxs]". resume_ret.
  iApply ("HK" $! _ k with "[%] Hl [$Hfl2 //] [$Hfdb //] Hbl Hxs Herr").
  assert (Hk64 : 0 <= k < 2 ^ 64) by lia.
  split_and!; [rewrite keeps_forall; cbn [atoms List.map List.In]; intros x Hx; lookups; destruct Hx as [<- | [<- | [<- | [<- | []]]]]; reflexivity | lookups; reflexivity | | ].
  - lookups. rewrite Z.mod_small; [reflexivity | exact Hk64].
  - rewrite Z.mod_small in Hk; [exact Hk | lia].
Qed.

End rules.

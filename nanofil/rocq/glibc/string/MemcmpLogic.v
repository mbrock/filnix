(** This file proves that glibc's own memcmp compares fewer than 16
    bytes of two live objects correctly, whatever shares of them the
    caller holds. GNU Hello's `memeq` calls memcmp on seven bytes, so
    this case is the one Hello needs.

    Below 16 bytes, glibc's memcmp compares the bytes one at a time and
    returns the difference of the first pair that differs, or 0 when
    every pair is equal. That result is 0 modulo 2^32 just when the
    bytes are equal.

    | Name | What it states |
    | --- | --- |
    | [cmp_bytes] | the result memcmp computes from the two byte lists |
    | [cmp_bytes_zero] | that result is 0 just when the lists are equal |
    | [byte_loop] | the byte loop, by induction on the bytes left |
    | [wp_glibc_memcmp_small] | the triple for a frame of `__GI_memcmp` |
    | [glibc_memcmp_small] | HelloGlibcLeaf.v's [memcmp_spec] ([memcmp_small_spec]) |

    The proof stops at 16 bytes because glibc's memcmp traps from there
    on. For 16 bytes or more, it compares bytes until the second pointer
    is 8-aligned and then compares whole words. It reads each word
    through a pointer that it rebuilt from an integer address, and
    nanofil gives such a pointer no capability: the read is a [[flight]]
    that copies the integer with none (`flight(_, copy, [tmp(pr.5)],
    none)`), followed by a [[check]]. A check through no capability
    traps with `null_capability`, so two equal 8-aligned runs of 16
    bytes make glibc's memcmp trap. No triple for all lengths holds of
    this code. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Panics Language Logic StringLogic MemLogic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpBits StrcmpLoop MemcmpCode.
Open Scope Z_scope.
Open Scope list_scope.

(** The difference of the first bytes where xs and ys differ, or 0. *)
Fixpoint cmp_bytes (xs ys : list Z) : Z :=
  match xs, ys with
  | x :: xs', y :: ys' => if Z.eqb x y then cmp_bytes xs' ys' else x - y
  | _, _ => 0
  end.

(** On bytes of one length, [cmp_bytes] is 0 modulo 2^32 just when
    they are equal. *)
Lemma cmp_bytes_zero xs ys : List.length xs = List.length ys ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  cmp_bytes xs ys mod 2 ^ 32 = 0 <-> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hl Hx Hy; cbn in Hl |- *; try discriminate;
    [split; reflexivity|].
  apply Forall_cons_1 in Hx as [Hx Hxs]. apply Forall_cons_1 in Hy as [Hy Hys].
  destruct (Z.eqb_spec x y) as [->|Hne].
  - rewrite (IH ys ltac:(lia) Hxs Hys). split; [intros ->; reflexivity | intros E; injection E as E; exact E].
  - split; [intros E; exfalso; exact (byte_diff_nonzero x y Hx Hy Hne E) | intros E; injection E as -> _; lia].
Qed.

(** The bytes from i agree with the whole once those before i are
    equal. *)
Lemma cmp_bytes_drop xs ys i : take i xs = take i ys -> cmp_bytes xs ys = cmp_bytes (drop i xs) (drop i ys).
Proof.
  revert xs ys. induction i as [|i IH]; intros [|x xs] [|y ys] H; cbn in H |- *; try reflexivity; try discriminate.
  injection H as -> H. rewrite Z.eqb_refl. apply IH, H.
Qed.

(** The block of the byte loop, L89. *)
Definition memcmp_blk89 : block := Eval vm_compute in
  match find_block (TAtom "L89") (fn_blocks glibc_memcmp) with
  | Some b => b | None => mkBlock (TAtom "L89") [] [] JUnreachable end.

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module MemcmpLogicOn (R : Runtime) (LG0 : LogicSig R).
(** The step rules of the proof mode. *)
Module SL := StrcmpLoopOn R LG0.
(** The byte pieces. *)
Module ML := MemLogicOn R LG0.
(** Strings' windows. *)
Module WS := SL.WS.
(** The Logic instance. *)
Module LG := LG0.
(** The language of the Logic instance. *)
Module L := LG.L.
Import L LG WS SL ML.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A let, its value left whole. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** A flight. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Entering a block. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** A goto and the block it enters. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** A branch, its condition left whole. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** Read the temporaries of the frame's environment below its puts by
    the hypotheses about them there, then compute the rest. *)
Ltac vx :=
  cbn [map2_option map_option flight_arg_x flight_cap arg_x];
  repeat match goal with |- context [value_x ?g ?E ?k (Tmp ?n)] =>
    match goal with H : lookup n _ = Some ?x |- _ =>
      rewrite (value_x_tmp g E k n x); [|look H] end end;
  reflexivity.
(** A let that may read the environment below the puts. *)
Ltac sl' := eapply (s_let registry wi ge); [reflexivity | reflexivity | vx | intros ?; reflexivity |].
(** A flight that may read the environment below the puts. *)
Ltac sf' := eapply (s_flight registry wi ge); [vx | reflexivity | vx |].
(** Replace the integer the temporary name holds by v, proved by tac. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** Replace the integer the newest temporary holds by v, proved by tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Replace the address of the pointer the temporary name holds by v. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** Logic.v's [wp_read_with] that also hands the next step a pure fact
    P that every memory with F has: a step that changes no memory, to
    the frame fr'. *)
Lemma wp_read_fact (Q : iProp Σ) (F : mem -> Prop) (P : Prop) fr fr' Φ :
  (forall σ, heap_interp wi σ -∗ Q -∗ ⌜F (ls_mem σ)⌝) -> (forall m, F m -> P) ->
  (forall m fuel, F m -> Semantics.step ge (mkConfig fr [] m fuel) = Next (mkConfig fr' [] m fuel)) ->
  Q -∗ ▷ (⌜P⌝ -∗ Q -∗ WP (ERun fr' : gexpr) {{ Φ }}) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof.
  intros HF HP Hs. iIntros "HQ HK". iCombine "HQ HK" as "H".
  iApply (wp_lift_run registry wi ge with "H").
  - iIntros (σ) "Hσ [HQ _]". iDestruct (HF with "Hσ HQ") as %Hf. iPureIntro.
    left. unfold fails. rewrite (Hs _ _ Hf). auto.
  - iIntros ([m s fuel w]) "Hσ [HQ HK]". iDestruct (HF with "Hσ HQ") as %Hf. cbn [ls_mem] in Hf.
    iNext. iIntros (e2 σ2 Hm).
    destruct (moves_core registry ge _ _ _ _ Hm ltac:(intros ?; cbn [ls_mem ls_fuel]; rewrite (Hs _ _ Hf); discriminate))
      as [(c' & E' & -> & ->) | [(q & k & b & s' & E' & _) | (o & m' & E' & _)]];
      cbn [ls_mem ls_fuel ls_rt] in E'; rewrite (Hs _ _ Hf) in E'; try discriminate E'.
    injection E' as <-. cbn [conf_expr conf_state c_frame c_callers c_mem c_fuel].
    iModIntro. iFrame "Hσ". iApply ("HK" with "[] HQ"). iPureIntro. exact (HP _ Hf).
Qed.

(** A [[check]] of one byte for reading of the pointer pr holds, p, and
    a load of the unsigned byte there, where p addresses byte i of the
    bytes xs at offset o of the object b, at a share: the load gives
    the byte. *)
Lemma wp_bytes_byte f e ls l c d pr rest j p dq b reg o xs i x Φ :
  map2_option (value_x ge e) [P] [Tmp pr] = Some [WPtr p] -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  ptr_addr p = b + o + Z.of_nat i -> xs !! i = Some x -> 0 <= x < 256 -> 0 <= o ->
  b + o + Z.of_nat (List.length xs) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  liveq dq b reg -∗ bytesq dq b o xs -∗
  (liveq dq b reg -∗ bytesq dq b o xs -∗
   WP (ERun (mkFrame f (put d (WInt x) (put c (WPtr p) e)) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let c A (Check 0 1 Read 1) [Tmp pr] ::
                                         Let d W (RawLoad (LdNarrow Ub) 0) [Tmp c] :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Ha Hi Hx8 Ho Hend Hreg. iIntros "Hl Hb HK".
  pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
  iApply (wp_read_with registry wi ge (liveq dq b reg)%I
            (fun m => live_at m b reg /\ objects_fit (m_regions m)) _ _ [] with "Hl [HK Hb]").
  { iIntros (σ) "Hσ Hl". iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit). iPureIntro. auto. }
  { intros m fuel [Hlv Hfit]. destruct (Hfit b reg (proj1 Hlv)) as [Hb0 _].
    apply rule_let with (classes := [P]) (xs := [WPtr p]); [reflexivity | reflexivity | exact Hx |].
    apply op_check. apply (access_read _ b reg); [exact Hc | exact (proj1 Hlv) | arith | arith | apply Z.mod_1_r]. }
  iNext. iIntros "Hl".
  iApply (wp_read_with registry wi ge (liveq dq b reg ∗ bytesq dq b o xs)%I
            (fun m => live_at m b reg /\ all_agree m (byte_ps b o xs) /\ objects_fit (m_regions m)) _ _ []
            with "[$Hl $Hb] [HK]").
  - iIntros (σ) "Hσ [Hl Hb]". iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (ptsq_facts with "Hσ Hb") as %(Hag & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hag & Hfit). destruct (Hfit b reg (proj1 Hlv)) as [Hb0 _]. destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hag Hi) as (Hv & _ & _).
    apply rule_let with (classes := [A]) (xs := [WPtr p]); [reflexivity | reflexivity | |].
    { cbn [map2_option value_x]. rewrite lookup_after_put_same. reflexivity. }
    assert (Er : raw_address (ptr_addr p) 0 = b + (o + Z.of_nat i)) by arith.
    rewrite (op_raw_load_byte m W Ub p 0 eq_refl).
    + rewrite Er Hv. cbn. rewrite (Z.mod_small x 256); [|lia]. rewrite (Z.mod_small x (2 ^ 32)); [reflexivity | lia].
    + rewrite Er. apply (access_read _ b reg); [exact Hc | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hb]". iApply ("HK" with "Hl Hb").
Qed.

(** The byte loop at i: pr.6 and pr.12 are the addresses i bytes into
    the bytes xs at offset o of the object b and ys at o' of b', pr.3
    the count left, the bytes before i equal. memcmp returns
    [cmp_bytes] and hands both back. *)
Lemma byte_loop dq1 dq2 b reg o c xs b' reg' o' c' ys i e Φ :
  0 <= b -> 0 <= b' -> (c = Obj b \/ c = Ro b) -> (c' = Obj b' \/ c' = Ro b') -> List.length ys = List.length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (List.length xs) <= r_end reg ->
  b' + o' + Z.of_nat (List.length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  (i <= List.length xs)%nat -> take i xs = take i ys ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr (b + o) c)) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr (b' + o') c')) ->
  lookup (TAtom "v10") e = Some (WInt (b + o)) -> lookup (TAtom "v13") e = Some (WInt (b' + o')) ->
  liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
  (liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
   Φ (Ret (WInt (cmp_bytes xs ys mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_memcmp (put (TAtom "pr.3") (WInt (Z.of_nat (List.length xs - i)))
         (put (TAtom "pr.6") (WInt (b + o + Z.of_nat i)) (put (TAtom "pr.12") (WInt (b' + o' + Z.of_nat i)) e)))
       [] None (Exec (TAtom "L89") (b_insts memcmp_blk89) (b_jump memcmp_blk89))) : gexpr) {{ Φ }}.
Proof.
  intros Hb Hb' Hc Hc' Hly Ho Ho' Hend Hend' Hr Hr' Hx Hy.
  remember (List.length xs - i)%nat as k eqn:Hk.
  revert i e Hk. induction k as [|k IH]; intros i e Hk Hi Htake H0 H2 H10 H13;
    iIntros "Hl Hx Hl' Hy HK"; cbn [memcmp_blk89 b_insts b_jump]; sl; sb.
  - (* No bytes left: they are equal. *)
    close_if. en.
    assert (E : xs = ys).
    { rewrite <- (take_ge xs i), <- (take_ge ys i); [exact Htake | lia | lia]. }
    eapply (s_ret registry wi ge _ _ _ _ _ _ (cmp_bytes xs ys mod 2 ^ 32)); [reflexivity | reflexivity | |].
    { rewrite E. clear. induction ys as [|y ys IH]; [reflexivity|]. cbn. rewrite Z.eqb_refl. exact IH. }
    iApply ("HK" with "Hl Hx Hl' Hy").
  - rewrite (Z.mod_small (Z.of_nat (S k))); [|lia]. change (0 mod 2 ^ 64) with 0.
    rewrite (proj2 (Z.eqb_neq (Z.of_nat (S k)) 0)); [|lia].
    close_if. en.
    destruct (lookup_lt_is_Some_2 xs i ltac:(lia)) as [x Hxi].
    destruct (lookup_lt_is_Some_2 ys i ltac:(lia)) as [y Hyi].
    assert (Hx8 : 0 <= x < 256) by exact (proj1 (Forall_lookup _ _) Hx i x Hxi).
    assert (Hy8 : 0 <= y < 256) by exact (proj1 (Forall_lookup _ _) Hy i y Hyi).
    sl'. match goal with |- context [put (TAtom "lc.13") (WInt ?X) _] => replace X with (Z.of_nat i) end.
    2:{ arith. } sf'. normp "v95" (b + o + Z.of_nat i).
    iApply (wp_bytes_byte _ _ _ _ _ _ _ _ _ _ dq1 b reg o xs i x with "Hl Hx");
      [reflexivity | exact Hc | reflexivity | exact Hxi | exact Hx8 | exact Ho | exact Hend | exact Hr |].
    iIntros "Hl Hx".
    sl. normt x ltac:(arith).
    sl'. norm "lc.16" (Z.of_nat i) ltac:(arith). sf'. normp "v100" (b' + o' + Z.of_nat i).
    iApply (wp_bytes_byte _ _ _ _ _ _ _ _ _ _ dq2 b' reg' o' ys i y with "Hl' Hy");
      [reflexivity | exact Hc' | reflexivity | exact Hyi | exact Hy8 | exact Ho' | rewrite Hly; exact Hend' | exact Hr' |].
    iIntros "Hl' Hy".
    sl. normt y ltac:(arith).
    sl. normt (b + o + Z.of_nat (S i)) ltac:(arith). sl. normt (b' + o' + Z.of_nat (S i)) ltac:(arith).
    sl. normt ((x - y) mod 2 ^ 64) ltac:(arith). sl. sb. rewrite Zmod_mod. change (0 mod 2 ^ 64) with 0.
    destruct (Z.eq_dec x y) as [<-|Hne].
    + (* Equal bytes: the next. *)
      assert (Hk' : Z.of_nat k < 2 ^ 48) by lia.
      rewrite Z.sub_diag Zmod_0_l. close_if. en. sl. normt (Z.of_nat k) ltac:(arith). sg.
      norm "pr.3" (Z.of_nat k) ltac:(arith). norm "pr.6" (b + o + Z.of_nat (S i)) ltac:(arith).
      norm "pr.12" (b' + o' + Z.of_nat (S i)) ltac:(arith).
      iApply (IH (S i) with "Hl Hx Hl' Hy HK"); [lia | lia | | look H0 | look H2 | look H10 | look H13].
      rewrite !(take_S_r _ _ _ Hxi) (take_S_r _ _ _ Hyi) Htake. reflexivity.
    + (* Different bytes: their difference. *)
      rewrite (proj2 (Z.eqb_neq _ 0)); [|change (2 ^ 64) with 18446744073709551616; Z.div_mod_to_equations; lia]. close_if. en.
      eapply (s_ret registry wi ge _ _ _ _ _ _ (cmp_bytes xs ys mod 2 ^ 32)); [reflexivity | reflexivity | |].
      { rewrite (cmp_bytes_drop xs ys i Htake) (drop_S _ _ _ Hxi) (drop_S _ _ _ Hyi). cbn [cmp_bytes].
        rewrite (proj2 (Z.eqb_neq _ _) Hne). arith. }
      iApply ("HK" with "Hl Hx Hl' Hy").
Qed.

(** glibc's memcmp of fewer than 16 bytes xs at offset o of the object b
    and ys at o' of b', at any shares, as a call binds them: it
    returns [cmp_bytes] and hands both back. *)
Lemma wp_glibc_memcmp_small fr dq1 dq2 b reg o c xs b' reg' o' c' ys Φ :
  call_frame glibc_memcmp [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (List.length xs))] =
    Some fr -> (List.length xs < 16)%nat ->
  (c = Obj b \/ c = Ro b) -> (c' = Obj b' \/ c' = Ro b') -> List.length ys = List.length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (List.length xs) <= r_end reg ->
  b' + o' + Z.of_nat (List.length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
  (liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
   Φ (Ret (WInt (cmp_bytes xs ys mod 2 ^ 32)))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof.
  intros Hfr H16 Hc Hc' Hly Ho Ho' Hend Hend' Hr Hr' Hx Hy. iIntros "Hl Hx Hl' Hy HK".
  cbn in Hfr. injection Hfr as <-. en.
  iApply (wp_read_fact (liveq dq1 b reg ∗ liveq dq2 b' reg')%I
            (fun m => live_at m b reg /\ live_at m b' reg' /\ objects_fit (m_regions m)) (0 <= b /\ 0 <= b')
            with "[$Hl $Hl']").
  { iIntros (σ) "Hσ [Hl Hl']". iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _ & Hfit).
    iDestruct (ptsq_facts with "Hσ Hl'") as %([Hlv' _] & _). iPureIntro. auto. }
  { intros m (Hlv & Hlv' & Hfit). split; [apply (Hfit b reg (proj1 Hlv)) | apply (Hfit b' reg' (proj1 Hlv'))]. }
  { intros m fuel _. eapply rule_let; reflexivity. }
  iNext. iIntros ([Hb Hb']) "[Hl Hl']".
  normt (b + o) ltac:(arith). sl. normt (b' + o') ltac:(arith). sl. sb.
  rewrite (Z.mod_small (Z.of_nat (List.length xs))); [|arith].
  change (16 mod 2 ^ 64) with 16. rewrite (proj2 (Z.leb_gt 16 _)); [|lia]. close_if. en.
  norm "pr.3" (Z.of_nat (List.length xs - 0)) ltac:(arith). norm "pr.6" (b + o + Z.of_nat 0) ltac:(arith).
  norm "pr.12" (b' + o' + Z.of_nat 0) ltac:(arith).
  iApply (byte_loop _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Hl Hx Hl' Hy HK"); done || lia.
Qed.

(** HelloGlibcLeaf.v's [memcmp_spec] for fewer than 16 bytes: a call
    triple for the function at `memcmp` that, on as many bytes xs and
    ys of two live objects at any shares, n their count below 16,
    returns an int that is 0 just when they are equal, and hands them
    back. *)
Definition memcmp_small_spec : Prop :=
  exists F, find_fn ge (TAtom "memcmp") = Some (Defined F) /\
  (forall p q n, is_Some (call_frame F [WPtr p; WPtr q; WInt n])) /\
  forall fr dq1 dq2 b reg o c xs b' reg' o' c' ys Φ,
    call_frame F [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (List.length xs))] = Some fr ->
    (List.length xs < 16)%nat ->
    (c = Obj b \/ c = Ro b) -> (c' = Obj b' \/ c' = Ro b') -> List.length ys = List.length xs ->
    0 <= o -> 0 <= o' -> b + o + Z.of_nat (List.length xs) <= r_end reg ->
    b' + o' + Z.of_nat (List.length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
    Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
    ⊢ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
      (∀ k, ⌜k mod 2 ^ 32 = 0 <-> xs = ys⌝ -∗ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗
            liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗ Φ (Ret (WInt k))) -∗
      WP (ERun fr : gexpr) {{ Φ }}.

(** glibc's own memcmp at `memcmp` meets [memcmp_small_spec]. *)
Lemma glibc_memcmp_small : find_fn ge (TAtom "memcmp") = Some (Defined glibc_memcmp) -> memcmp_small_spec.
Proof.
  intros Hf. exists glibc_memcmp. split; [exact Hf|]. split; [intros; eexists; reflexivity|].
  intros fr dq1 dq2 b reg o c xs b' reg' o' c' ys Φ Hfr H16 Hc Hc' Hly Ho Ho' Hend Hend' Hr Hr' Hx Hy.
  iIntros "Hl Hx Hl' Hy HK".
  iApply (wp_glibc_memcmp_small with "Hl Hx Hl' Hy"); [exact Hfr | exact H16 | exact Hc | exact Hc' | exact Hly | exact Ho | exact Ho'
    | exact Hend | exact Hend' | exact Hr | exact Hr' | exact Hx | exact Hy |].
  iIntros "Hl Hx Hl' Hy". iApply ("HK" with "[] Hl Hx Hl' Hy"). iPureIntro.
  rewrite Zmod_mod. apply cmp_bytes_zero; [lia | exact Hx | exact Hy].
Qed.

End rules.
End MemcmpLogicOn.

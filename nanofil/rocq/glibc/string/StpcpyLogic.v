From Glibc Require Import Unit_string_stpcpy_os.
From Glibc Require Import GlibcProgram.
(** glibc's `c: stpcpy` copies a string and its terminator into a buffer
    and returns the address of the copied terminator. This module proves
    that the captured body does exactly that for any buffer the caller
    owns and any share of a readable string.

    The proof follows the three phases of the C code. It first copies
    single bytes until the destination is aligned to 8 bytes, stopping
    early if the string ends. It then copies whole words, by the aligned
    loop of StpcpyWords.v when the source is aligned too and by the
    shifting loop of StpcpyShift.v otherwise, and it finishes with the
    byte tail of StpcpyTail.v. The result [wp_glibc_stpcpy] says which
    bytes the buffer holds afterwards: the string and its terminator at
    the destination offset, and every other byte unchanged. The string
    itself is returned to the caller untouched.

    The rule needs no bound on the old bytes of the buffer, because the
    copy never reads them. The call rule [wp_call_glibc_stpcpy] applies
    the result at a call of any name bound to the captured body. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld FileInv LibioLogic StrlenBits GetoptBytes WordString StrcmpBits StrcmpLoop.
From Glibc Require Import LibioCloseSteps StpcpyBytes StpcpyTail StpcpyShift StpcpyWords.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** This definition names the loop head of the byte prologue. *)
Definition blk_9 : block := Eval vm_compute in sblk "L9".

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance stp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The byte prologue

    The prologue counts down the t bytes that separate the destination
    from the next multiple of 8. Each turn copies one byte of the string.
    When that byte is the terminator, the function returns at once.
    When the count reaches zero, the code tests the source alignment and
    enters one of the two word loops. *)

Lemma stp_head e bd rd xs o q b reg ws dq s i Φ :
  str_shape q b reg ws s ->
  lookup (TAtom "pr.3") e = Some (WInt ((- (bd + o)) mod 8 - i)) ->
  lookup (TAtom "pr.2") e = Some (WPtr (mkPtr (ptr_addr q + i) (ptr_cap q))) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (bd + o + i) (Obj bd))) ->
  0 <= i <= (- (bd + o)) mod 8 -> i <= Z.of_nat (length s) ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> 0 <= bd -> bd + Z.of_nat (length xs) <= r_end rd ->
  r_end rd <= 2 ^ 48 ->
  live bd rd -∗ bytes bd 0 (stp_dst xs o i (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
  (live bd rd -∗ bytes bd 0 (stp_dst xs o (Z.of_nat (length s) + 1) (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
     Φ (Ret (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))))) -∗
  WP (ERun (mkFrame Unit_string_stpcpy_os.fn___GI___stpcpy e [] None (Exec (TAtom "L9") (b_insts blk_9) (b_jump blk_9))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hs. destruct (shape_facts _ _ _ _ _ Hs) as (B & S1 & M & P & K & E & R & N & C).
  pose proof (ss_words _ _ _ _ _ Hs) as F. pose proof (ss_chars _ _ _ _ _ Hs) as Hch. pose proof (sbyte_agree _ _ _ _ _ Hs) as A.
  set (n := Z.of_nat (length s)) in *. set (S := (s ++ [0])%list) in *. set (t := (- (bd + o)) mod 8) in *.
  assert (Ht : 0 <= t < 8) by (apply Z.mod_pos_bound; lia).
  assert (HS : Z.of_nat (length S) = n + 1) by (unfold S, n; rewrite length_app; cbn; lia).
  assert (HSn : forall j, 0 <= j < n -> 0 < nth (Z.to_nat j) S 0 < 256).
  { intros j Hj. unfold S. rewrite app_nth1; [|lia]. apply (Forall_nth (fun c => 0 < c < 256)); [exact Hch | lia]. }
  assert (HS0 : nth (Z.to_nat n) S 0 = 0) by (unfold S, n; rewrite app_nth2; [|lia]; rewrite Nat2Z.id Nat.sub_diag; reflexivity).
  intros Hp3 Hp2 Hp1 Hi Hin Ho Hox Hbd Hend Hreg.
  remember (Z.to_nat (t - i)) as r eqn:Hr.
  revert i e Hp3 Hp2 Hp1 Hi Hin Hr. induction r as [r IH] using lt_wf_ind.
  intros i e Hp3 Hp2 Hp1 Hi Hin Hr. iIntros "Hl Hb Hw HK". cbn [blk_9 b_insts b_jump].
  step_symbolic. branch_symbolic. rewrite (Z.mod_small (t - i)); [|lia]. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eq_dec (t - i) 0) as [Hz|Hz].
  - rewrite Hz. close_edge. step. assert (Hit : i = t) by lia. subst i.
    step_symbolic. step_symbolic. normz "v35" ((ptr_addr q + t) mod 8) ltac:(rewrite land7; [reflexivity | cbn [ptr_addr]; lia]).
    step_symbolic. branch_symbolic. rewrite (Z.mod_small ((ptr_addr q + t) mod 8)); [|pose proof (Z.mod_pos_bound (ptr_addr q + t) 8); lia].
    change (0 mod 2 ^ 64) with 0.
    assert (Hm : (ptr_addr q + t) mod 8 = (ptr_addr q mod 8 + t) mod 8).
    { replace (ptr_addr q + t) with (wstart q + (ptr_addr q mod 8 + t)) by lia. rewrite Zplus_mod M Z.add_0_l Zmod_mod. reflexivity. }
    pose proof (Z.div_mod (ptr_addr q mod 8 + t) 8 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (ptr_addr q mod 8 + t) 8 ltac:(lia)) as Hmb.
    destruct (Z.eq_dec ((ptr_addr q + t) mod 8) 0) as [Ha|Ha].
    + rewrite Ha. close_edge. step.
      iApply (stp_align _ bd rd xs o q b reg ws dq s t ((ptr_addr q mod 8 + t) / 8) with "Hl Hb Hw HK"); try lk_prove; lia.
    + replace ((ptr_addr q + t) mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha). close_edge. step.
      iApply (stp_shift _ bd rd xs o q b reg ws dq s t ((ptr_addr q + t) mod 8) ((ptr_addr q mod 8 + t) / 8)
        with "Hl Hb Hw HK"); try lk_prove; lia.
  - replace (t - i =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_edge. step. step. cbn [ptr_addr ptr_cap].
    iApply (wp_win_byte registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ _ dq b reg (wstart q - b) ws (ptr_addr q mod 8 + i) with "Hw");
      [vx | exact C | cbn; lia | lia | lia | lia | lia | lia |]. iIntros "Hw".
    set (c := bt ws (ptr_addr q mod 8 + i)).
    assert (Hc : c = nth (Z.to_nat i) S 0) by (apply (A i); lia).
    assert (Hc8 : 0 <= c < 256) by apply byte_of_range.
    replace (extension Sb c mod 2 ^ 32) with (chr_w c) by reflexivity.
    pose proof (length_stp_dst xs o i S Ho ltac:(lia) ltac:(lia)) as Hlen.
    iDestruct (bytes_store1 bd _ (Z.to_nat (o + i)) with "Hb") as (x) "[Hx Hb]"; [lia|].
    rewrite Z2Nat.id; [|lia].
    check "Hl".
    iApply (wp_raw_store_byte with "Hl Hx"); [vx | vx | reflexivity | a2 | wi_store |].
    iNext. iIntros "Hl Hx". rewrite (Z.mod_small (chr_w c)); [|apply chr_w_range]. rewrite (chr_w_byte c Hc8). iDestruct ("Hb" with "Hx") as "Hb".
    iEval (rewrite Hc stp_dst_byte; [|lia|lia|lia]) in "Hb".
    step. branch_symbolic. rewrite (Z.mod_small (chr_w c)); [|apply chr_w_range]. change (0 mod 2 ^ 32) with 0.
    rewrite chr_w_eqb; [|exact Hc8|lia].
    destruct (Z.eqb_spec c 0) as [Hc0|Hc0].
    + assert (Hin' : i = n).
      { destruct (Z.eq_dec i n) as [|Hne]; [assumption|]. exfalso. pose proof (HSn i ltac:(lia)). lia. }
      rewrite Hc0. close_edge. step.
      iApply wp_ret; [reflexivity | vx |]. iNext. subst i. iApply ("HK" with "Hl Hb Hw").
    + assert (Hin' : i < n) by (destruct (Z.eq_dec i n) as [Ein|]; [exfalso; apply Hc0; rewrite Hc Ein HS0; reflexivity | lia]).
      replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc0). close_edge.
      step. step. step. step. step. cbn [ptr_addr ptr_cap].
      normp "pr.2" (ptr_addr q + (i + 1)). normp "pr.1" (bd + o + (i + 1)).
      normz "pr.3" (t - (i + 1)) ltac:(change (1 mod 2 ^ 64) with 1; rewrite (Z.mod_small (t - i)); [|lia];
        rewrite Zmod_mod; rewrite Z.mod_small; lia).
      iApply (IH (Z.to_nat (t - (i + 1))) ltac:(lia) (i + 1) _ with "Hl Hb Hw HK"); try lk_prove; lia.
Qed.

(** ## The whole function

    The entry block computes t and starts the prologue with nothing
    copied. A caller owns the buffer b, which holds xs, and lends a share
    of the string s at q. The copy goes to offset o of the buffer, which
    must leave room for s and its terminator. *)

Lemma wp_glibc_stpcpy e bd rd xs o dq q s Φ :
  lookup (TAtom "v0") e = Some (WPtr (mkPtr (bd + o) (Obj bd))) -> lookup (TAtom "v2") e = Some (WPtr q) ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> bd + Z.of_nat (length xs) <= r_end rd ->
  live bd rd -∗ bytes bd 0 xs -∗ word_string dq q s -∗
  (live bd rd -∗ bytes bd 0 (splice xs (Z.to_nat o) (s ++ [0])) -∗ word_string dq q s -∗
     Φ (Ret (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))))) -∗
  WP (ERun (mkFrame Unit_string_stpcpy_os.fn___GI___stpcpy e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv0 Hv2 Ho Hox Hend. iIntros "Hl Hb Hs HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hbd Hreg]) "Hl".
  iDestruct "Hs" as (b reg ws Hs) "Hw".
  pose proof (shape_facts _ _ _ _ _ Hs) as (B & S1 & M & P & K & E & R & N & C).
  rewrite -{1}(stp_dst_0 xs o (s ++ [0])); [|lia].
  step. step_symbolic. step_symbolic. step_symbolic.
  normz "v8" ((- (bd + o)) mod 8) ltac:(cbn [ptr_addr]; rewrite neg_land7; [reflexivity | lia]).
  step. step. cbn [edge_label].
  normz "pr.3" ((- (bd + o)) mod 8 - 0) ltac:(rewrite Z.sub_0_r (Z.mod_small ((- (bd + o)) mod 8) (2 ^ 64)); [reflexivity | pose proof (Z.mod_pos_bound (- (bd + o)) 8); lia]).
  iApply (stp_head _ bd rd xs o q b reg ws dq s 0 with "Hl Hb Hw [HK]"); try lk_prove; try lia.
  - rewrite Z.add_0_r. destruct q. lk_prove.
  - rewrite Z.add_0_r. lk_prove.
  - pose proof (Z.mod_pos_bound (- (bd + o)) 8). lia.
  - iIntros "Hl Hb Hw". replace (Z.of_nat (length s) + 1) with (Z.of_nat (length (s ++ [0]))) by (rewrite length_app; cbn; lia).
    rewrite stp_dst_all. iApply ("HK" with "Hl Hb"). iExists b, reg, ws. iFrame "Hw". done.
Qed.

(** ## The call rule *)

(** A caller needs the result at a call site rather than at the entry
    of the body. A call passes the destination and the source, and the
    caller resumes with the address of the copied terminator. *)
Lemma wp_call_glibc_stpcpy f e ls l d g args rest j bd rd xs o dq q s Φ :
  map_option (arg_x ge e) args = Some [WPtr (mkPtr (bd + o) (Obj bd)); WPtr q] ->
  find_fn ge g = Some (Defined Unit_string_stpcpy_os.fn___GI___stpcpy) ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> bd + Z.of_nat (length xs) <= r_end rd ->
  live bd rd -∗ bytes bd 0 xs -∗ word_string dq q s -∗
  ▷ (live bd rd -∗ bytes bd 0 (splice xs (Z.to_nat o) (s ++ [0])) -∗ word_string dq q s -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))) e) ls None (Exec l rest j)) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call (CResult d P) (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hg Ho Hox Hend. iIntros "Hl Hb Hs HK".
  iApply wp_call_bind; [exact Hargs | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_stpcpy with "Hl Hb Hs"); [reflexivity | reflexivity | exact Ho | exact Hox | exact Hend |].
  iIntros "Hl Hb Hs". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "Hl Hb Hs").
Qed.
End rules.

(** ## Controls

    These examples compute the buffer that the rule promises for small
    cases. A copy into the middle of a buffer leaves the bytes before and
    after it alone, an empty string copies only its terminator, and a copy
    that ends at the last byte still fits. A destination one byte too
    short would make the result longer than the buffer, which is why the
    rule asks for room for the terminator. *)

Example stp_interior : splice [9; 8; 7; 6; 5; 4] 2 ([65; 66] ++ [0]) = [9; 8; 65; 66; 0; 4].
Proof. reflexivity. Qed.
Example stp_empty : splice [9; 8; 7; 6; 5; 4] 3 ([] ++ [0]) = [9; 8; 7; 0; 5; 4].
Proof. reflexivity. Qed.
Example stp_capacity : splice [9; 8; 7; 6] 1 ([1; 2] ++ [0]) = [9; 1; 2; 0].
Proof. reflexivity. Qed.
Example stp_overflow : length (splice [9; 8; 7; 6] 2 ([1; 2] ++ [0])) = 5%nat.
Proof. reflexivity. Qed.

(** GNU Hello's leaf functions (HelloLeaf.v's [mbszero_fn],
    [strnlen1_fn], [streq_fn] and [memeq_fn], Hello's own IR from
    HelloCode.v) linked with glibc, over the [os_world] of
    [OsWorld](../zsys/OsWorld.v), with no premise about the world.

    - `mbszero` calls `memset`, glibc's own ([glibc_memset]):
      [mbszero_glibc] zeroes the 8 bytes it owns.
    - `strnlen1` calls `memchr`, glibc's own ([glibc_memchr]):
      [strnlen1_glibc] returns one past the NUL of a [word_string] when
      it is within n bytes, and n otherwise.
    - `streq` calls `strcmp` and `memeq` calls `memcmp`: their triples
      take any function at that name with a call triple ([strcmp_spec],
      [memcmp_spec]) whose result is 0 just when the strings, or the
      bytes, are equal, as glibc's own strcmp's will be; [streq_glibc]
      and [memeq_glibc] return 1 just when they are equal.

    The genv links Hello with glibc: its functions at `memset` and
    `memchr` are glibc's, and the registry holds OsRegistry.v's
    contract for libpizlo's `c: zmemset`, which glibc's memset calls. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic HelloLeaf.
From Glibc Require Import StrlenBits StrlenLogic WordString OsWorld OsRegistry MemFwdCode MemFwdLogic
  StrchrCode MemchrLast MemchrLogic StrnlenLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module HelloGlibcLeafOn (R : Runtime) (LG0 : LogicSig R).
Module MF := MemFwdLogicOn R LG0.
Module SN := StrnlenLogicOn R LG0.
Module OW := MF.OW.
Module WS := SN.WS.
Module LG := LG0.
Module L := LG.L.
Import L LG MF.ML WS SN.ML.

Section leaves.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The registry holds the contract for `c: zmemset`, which is no
    function or symbol of the genv. *)
Context (Hset : registry (TAtom "zmemset") = Some (void_only (memset_contract os_world)))
  (Hset_fn : find_fn ge (TAtom "zmemset") = None) (Hset_sym : lookup (TAtom "zmemset") (ge_globals ge) = None).
(** Hello's `memset` and `memchr` are glibc's. *)
Context (Hmemset : find_fn ge (TAtom "memset") = Some (Defined glibc_memset))
  (Hmemchr : find_fn ge (TAtom "memchr") = Some (Defined glibc_memchr)).

(** [os_wi] w0 survives safepoints. *)
Local Instance leaf_stable : SafepointStable (os_wi w0) := OW.os_wi_stable w0.
(** The Iris instance of the registry and [os_wi] w0. *)
Local Instance leaf_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A call triple for the function at `strcmp`: on two strings at any
    shares it returns an int that is 0 just when they are equal, and
    hands them back. *)
Definition strcmp_spec : Prop :=
  exists F, find_fn ge (TAtom "strcmp") = Some (Defined F) /\
  (forall p q, is_Some (call_frame F [WPtr p; WPtr q])) /\
  forall fr dq1 dq2 p q s t Φ, call_frame F [WPtr p; WPtr q] = Some fr ->
    ⊢ word_string dq1 p s -∗ word_string dq2 q t -∗
      (∀ k, ⌜k mod 2 ^ 32 = 0 <-> s = t⌝ -∗ word_string dq1 p s -∗ word_string dq2 q t -∗ Φ (Ret (WInt k))) -∗
      WP (ERun fr : gexpr) {{ Φ }}.

(** A call triple for the function at `memcmp`: on as many bytes xs and
    ys of two live objects at any shares, through read-write or
    read-only capabilities, n their count, it returns an int that is 0
    just when they are equal, and hands them back. *)
Definition memcmp_spec : Prop :=
  exists F, find_fn ge (TAtom "memcmp") = Some (Defined F) /\
  (forall p q n, is_Some (call_frame F [WPtr p; WPtr q; WInt n])) /\
  forall fr dq1 dq2 b reg o c xs b' reg' o' c' ys Φ,
    call_frame F [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))] = Some fr ->
    (c = Obj b \/ c = Ro b) -> (c' = Obj b' \/ c' = Ro b') -> length ys = length xs ->
    0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
    b' + o' + Z.of_nat (length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
    Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
    ⊢ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
      (∀ k, ⌜k mod 2 ^ 32 = 0 <-> xs = ys⌝ -∗ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗
            liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗ Φ (Ret (WInt k))) -∗
      WP (ERun fr : gexpr) {{ Φ }}.

(** One pure step whose premises compute. *)
Ltac pst := iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext].

(** `mbszero`'s triple, over glibc's memset: owning the 8 bytes xs and
    their slots cs at the 8-aligned offset o of the live object b, at a
    multiple of 8, it zeroes them and clears the slots. *)
Lemma mbszero_glibc b reg o xs cs Φ :
  length xs = 8%nat -> length cs = 8%nat -> b mod 8 = 0 -> o mod 8 = 0 -> 0 <= o -> b + o + 8 <= r_end reg ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗
  ▷ (live b reg -∗ bytes b o (replicate 8 0) -∗ auxes b o (MemLogic.clear_slots o cs) -∗ Φ RetVoid) -∗
  WP (ERun (invocation mbszero_fn [WPtr (mkPtr (b + o) (Obj b))]) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Hb8 Ho8 Ho Hend. iIntros "Hl Hx Hcs HΦ". rewrite mbszero_entry.
  iApply wp_enter; [exact find_z_start | reflexivity |]. iNext. cbn [b_insts b_jump z_start].
  iApply (MF.wp_call_glibc_memset w0 registry ge Hset Hset_fn Hset_sym _ _ _ _ _ _ _ _ _ b reg o xs cs 0
            with "Hl Hx Hcs"); [rewrite Hx; reflexivity | exact Hmemset | reflexivity | lia | rewrite Hx; lia
    | exact Hb8 | exact Ho8 | exact Ho | rewrite Hx; exact Hend | lia |].
  iNext. iIntros "Hl Hx Hcs". rewrite Hx.
  iApply wp_ret_void. iNext. iApply ("HΦ" with "Hl Hx Hcs").
Qed.

(** `strnlen1`'s triple, over glibc's memchr: on the string s at p at
    any share and a bound n, it returns one past the NUL when that lies
    within n bytes, and n otherwise. *)
Lemma strnlen1_glibc dq p s n Φ :
  0 <= n < 2 ^ 64 ->
  word_string dq p s -∗
  ▷ (word_string dq p s -∗ Φ (Ret (WInt (Z.min (Z.of_nat (length s) + 1) n)))) -∗
  WP (ERun (invocation strnlen1_fn [WPtr p; WInt n]) : gexpr) {{ Φ }}.
Proof.
  intros Hn. iIntros "Hs HΦ". rewrite strnlen1_entry.
  iDestruct "Hs" as "(%b & %reg & %ws & %Hs & Hw)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch].
  assert (Hend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end reg).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hs|].
  iApply wp_enter; [exact find_n_start | reflexivity |]. iNext. cbn [b_insts b_jump n_start].
  iApply (SN.wp_call_glibc_memchr_nul registry (os_wi w0) ge with "Hs");
    [cbn; rewrite (Z.mod_small n); [reflexivity | lia] | exact Hn | exact Hmemchr | reflexivity |].
  iNext. iIntros "Hs". destruct p as [a c0]. cbn [ptr_addr ptr_cap] in *. unfold nul_hit.
  destruct (Z.ltb_spec (Z.of_nat (length s)) n) as [Hls|Hls]; cbn [hit_ptr ptr_addr ptr_cap].
  - pst. pst. pst. iApply wp_branch; [reflexivity|]. iNext.
    rewrite !Zmod_0_l (Z.mod_small (a + Z.of_nat (length s))); [|lia].
    replace (negb (a + Z.of_nat (length s) =? 0)) with true
      by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
    cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_n_L8 | reflexivity |]. iNext. cbn [b_insts b_jump n_L8].
    pst. pst. pst. iApply wp_ret; [reflexivity | reflexivity |]. iNext. rewrite Z.min_l; [|lia].
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) =>
      replace X with (Z.of_nat (length s) + 1) end; [iApply ("HΦ" with "Hs")|].
    cbn [ptr_addr]. change (2 ^ 64) with 18446744073709551616.
    repeat match goal with |- context [?x mod 18446744073709551616] =>
      rewrite (Z.mod_small x 18446744073709551616); [|lia] end; lia.
  - pst. pst. pst. iApply wp_branch; [reflexivity|]. iNext. cbn [Z.eqb edge_label negb].
    iApply wp_enter; [exact find_n_L9 | reflexivity |]. iNext. cbn [b_insts b_jump n_L9].
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    rewrite Z.min_r; [|lia]. rewrite (Z.mod_small n); [|lia]. iApply ("HΦ" with "Hs").
Qed.

(** `streq`'s triple, from any [strcmp_spec] (glibc's own strcmp's, for
    one): on two strings at any shares it returns 1 just when they are
    equal, and 0 otherwise. *)
Lemma streq_glibc (Hcmp : strcmp_spec) dq1 dq2 p q s t Φ :
  word_string dq1 p s -∗ word_string dq2 q t -∗
  ▷ (word_string dq1 p s -∗ word_string dq2 q t -∗
     Φ (Ret (WInt (if decide (s = t) then 1 else 0)))) -∗
  WP (ERun (invocation streq_fn [WPtr p; WPtr q]) : gexpr) {{ Φ }}.
Proof.
  destruct Hcmp as (F & HF & Hfr & Hspec). iIntros "Hs Ht HΦ". rewrite streq_entry.
  destruct (Hfr p q) as [fr Hfr'].
  iApply wp_enter; [exact find_q_start | reflexivity |]. iNext. cbn [b_insts b_jump q_start].
  iApply (wp_call_bind with "[-]"); [reflexivity | exact HF | exact Hfr' |]. iNext.
  iApply (Hspec with "Hs Ht"); [exact Hfr'|]. iIntros (k Hk) "Hs Ht".
  iExists _. iSplit; [done|]. iNext.
  pst. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) =>
    replace X with (if decide (s = t) then 1 else 0) end; [iApply ("HΦ" with "Hs Ht")|].
  rewrite Zmod_0_l Zmod_mod. destruct (decide (s = t)) as [E|E].
  - rewrite (proj2 Hk E). reflexivity.
  - destruct (Z.eqb_spec (k mod 2 ^ 32) 0) as [E'|E']; [exfalso; exact (E (proj1 Hk E'))|reflexivity].
Qed.

(** `memeq`'s triple, from any [memcmp_spec]: on as many bytes xs and
    ys of two live objects at any shares, n their count, it returns 1
    just when they are equal, and 0 otherwise. *)
Lemma memeq_glibc (Hcmp : memcmp_spec) dq1 dq2 b reg o c xs b' reg' o' c' ys Φ : 0 < b ->
  (c = Obj b \/ c = Ro b) -> (c' = Obj b' \/ c' = Ro b') -> length ys = length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
  b' + o' + Z.of_nat (length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
  ▷ (liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
     Φ (Ret (WInt (if decide (xs = ys) then 1 else 0)))) -∗
  WP (ERun (invocation memeq_fn [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))])
        : gexpr) {{ Φ }}.
Proof.
  destruct Hcmp as (F & HF & Hfr & Hspec).
  intros Hb0 Hc Hc' Hly Ho Ho' Hend Hend' Hr Hr' Hx Hy. iIntros "Hl Hx Hl' Hy HΦ". rewrite memeq_entry.
  assert (Hn : Z.of_nat (length xs) < 2 ^ 64) by lia.
  destruct (Hfr (mkPtr (b + o) c) (mkPtr (b' + o') c') (Z.of_nat (length xs))) as [fr Hfr'].
  iApply wp_enter; [exact find_e_start | reflexivity |]. iNext. cbn [b_insts b_jump e_start].
  iApply (wp_call_bind with "[-]"); [cbn; rewrite (Z.mod_small (Z.of_nat (length xs))); [reflexivity | lia]
    | exact HF | exact Hfr' |]. iNext.
  iApply (Hspec with "Hl Hx Hl' Hy"); [exact Hfr' | exact Hc | exact Hc' | exact Hly | exact Ho | exact Ho'
    | exact Hend | exact Hend' | exact Hr | exact Hr' | exact Hx | exact Hy |].
  iIntros (k Hk) "Hl Hx Hl' Hy". iExists _. iSplit; [done|]. iNext.
  pst. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) =>
    replace X with (if decide (xs = ys) then 1 else 0) end; [iApply ("HΦ" with "Hl Hx Hl' Hy")|].
  rewrite Zmod_0_l Zmod_mod. destruct (decide (xs = ys)) as [E|E].
  - rewrite (proj2 Hk E). reflexivity.
  - destruct (Z.eqb_spec (k mod 2 ^ 32) 0) as [E'|E']; [exfalso; exact (E (proj1 Hk E'))|reflexivity].
Qed.

End leaves.
End HelloGlibcLeafOn.

(** When glibc rejects a byte in the C locale, gnulib checks the
    locale name before it accepts the byte as a wide character. Its
    query copies the name into a local buffer and compares it with
    "C". A match ends the search before the comparison with "POSIX". *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloLocale.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic WordString StrlenLogic StrlenWord
  MemFwdCode MemFwdLogic SetlocaleCode SetlocaleCtypeQuery StrcmpCode StrcmpLogic HelloImageModule HelloImageLoad.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section conversion.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation gexpr := (language.expr (nanofil_lang registry ge)).
Local Instance conv_stable : SafepointStable (os_wi w0) := os_wi_stable w0.

Context (gb : Z) (greg : region) (dql dqc : dfrac) (cb : Z).
Local Abbreviation cn := (mkPtr cb (Ro cb)).
Local Abbreviation names := (liveq dql gb greg ∗ pcellq dqc gb 128 cn)%I.
Context (Hgl : lookup (TAtom "_nl_global_locale") (ge_globals ge) = Some (mkPtr gb (Obj gb)))
  (Hgb : 0 < gb) (H8 : gb mod 8 = 0) (Hend : gb + 136 <= r_end greg) (Hmax : r_end greg <= 2 ^ 48)
  (Hset : find_fn ge (TAtom "setlocale") = Some (Defined glibc_setlocale)).

(** The unlocked query returns the same pointer that glibc reads from
    the character category. The string keeps that pointer's target alive. *)
Lemma wp_ctype_null_unlocked Φ :
  names -∗ word_string DfracDiscarded cn [67] -∗
  ▷ (names -∗ Φ (Ret (WPtr cn))) -∗ WP (ERun (invocation snu_fn [WInt 0]) : gexpr) {{ Φ }}.
Proof using Type*.
  iIntros "[Hl Hc] #Hs HK". iPoseProof "Hs" as "(%b & %reg & %ws & %Hsh & #Ht & _)".
  destruct Hsh as [[E|E] Hb Ha Hs Hend' Hsp Hlen _ _ _]; [discriminate|]. injection E as <-.
  rewrite snu_entry. step.
  iApply (wp_call_bind with "[-]"); [reflexivity | exact Hset | reflexivity |]. iNext.
  iApply (wp_setlocale_ctype_query with "Hl Hc Ht"); try eassumption; try reflexivity.
  { unfold wstart in Hend'. cbn [ptr_addr] in Hend' |- *. rewrite Ha in Hend'. lia. }
  iNext. iIntros "Hl Hc _". iExists _. iSplit; [done|]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "[$Hl $Hc]").
Qed.

Context (Hquery : find_fn ge (TAtom "setlocale_null_unlocked") = Some (Defined snu_fn))
  (Hstrlen : find_fn ge (TAtom "strlen") = Some (Defined glibc_strlen))
  (Hmemcpy : find_fn ge (TAtom "memcpy") = Some (Defined glibc_memcpy))
  (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).

(** The C locale name fits in the 257-byte buffer. The unlocked copy
    writes only the first two bytes and returns zero. *)
Lemma wp_ctype_copy b reg Φ :
  b mod 8 = 0 -> b + 2 <= r_end reg ->
  names -∗ word_string DfracDiscarded cn [67] -∗ live b reg -∗ bytes b 0 [0;0] -∗ auxes b 0 [CNone;CNone] -∗
  ▷ (names -∗ live b reg -∗ bytes b 0 [67;0] -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (invocation snru_fn [WInt 0; WPtr (mkPtr b (Obj b)); WInt 257]) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hb8 Hfit. iIntros "Hnames #Hs Hl Hb Ha HK".
  iDestruct (word_string_bytes with "Hs") as (b' reg' ws) "(%Hsh & #Hl' & #Hb' & _)".
  destruct Hsh as [[E|E] Hb' Hal Hst Hend' Hsp Hlen _ _ _]; [discriminate|]. injection E as <-.
  unfold wstart in Hend'. cbn [ptr_addr] in Hlen, Hend'. rewrite Hal in Hlen, Hend'.
  rewrite snru_entry. step.
  iApply (wp_call_bind with "[-]"); [reflexivity | exact Hquery | reflexivity |]. iNext.
  iApply (wp_ctype_null_unlocked with "Hnames Hs"). iNext. iIntros "Hnames".
  iExists _. iSplit; [done|]. iNext. do 3 step_symbolic. branch_symbolic.
  cbn [ptr_addr]. rewrite !Zmod_0_l (Z.mod_small cb); [|lia].
  rewrite (proj2 (Z.eqb_neq cb 0) ltac:(lia)). cbn [edge_label]. step.
  iApply (wp_call_glibc_strlen registry (os_wi w0) ge with "Hs"); [reflexivity | exact Hstrlen | reflexivity |].
  iNext. iIntros "_". step. branch. step. step.
  cbn [ptr_addr]. rewrite Z.sub_diag.
  iApply (wp_call_glibc_memcpy Hmove Hmove_fn Hmove_sym _ _ _ _ _ _ _ _ _ b reg 0 [0;0] [CNone;CNone]
    DfracDiscarded cb reg' 0 (Ro cb) [67;0] with "Hl Hb Ha Hl' Hb'");
    try (rewrite !Z.add_0_r; reflexivity); try reflexivity; try lia.
  - exact Hmemcpy.
  - by right.
  - change (b + 0 + 2 <= r_end reg). lia.
  - change (Z.of_nat (List.length ws) = 1) in Hlen. change (cb + 0 + 2 <= r_end reg'). lia.
  - repeat constructor; lia.
  - iNext. iIntros "Hl Hb _ _ _". iApply wp_ret; [reflexivity | reflexivity |].
    iNext. iApply ("HK" with "Hnames Hl Hb").
Qed.

Context (Hcopy : find_fn ge (TAtom "setlocale_null_r_unlocked") = Some (Defined snru_fn)).

(** The public wrapper calls the unlocked copy directly. It returns
    the same success code and the same two bytes. *)
Lemma wp_ctype_null_r b reg Φ :
  b mod 8 = 0 -> b + 2 <= r_end reg ->
  names -∗ word_string DfracDiscarded cn [67] -∗ live b reg -∗ bytes b 0 [0;0] -∗ auxes b 0 [CNone;CNone] -∗
  ▷ (names -∗ live b reg -∗ bytes b 0 [67;0] -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (invocation snr_fn [WInt 0; WPtr (mkPtr b (Obj b)); WInt 257]) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hb8 Hend'. iIntros "Hnames #Hs Hl Hb Ha HK". rewrite snr_entry. step.
  iApply (wp_call_bind with "[-]"); [reflexivity | exact Hcopy | reflexivity |]. iNext.
  iApply (wp_ctype_copy with "Hnames Hs Hl Hb Ha"); [exact Hb8 | exact Hend' |].
  iNext. iIntros "Hnames Hl Hb". iExists _. iSplit; [done|]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |].
  iNext. iApply ("HK" with "Hnames Hl Hb").
Qed.

Local Lemma c_buffer b reg :
  0 < b -> b mod 8 = 0 -> b + 8 <= r_end reg -> r_end reg <= 2 ^ 48 ->
  live b reg -∗ bytes b 0 [67;0] -∗ bytes b 2 (replicate 6 0) -∗ word_string (DfracOwn 1) (mkPtr b (Obj b)) [67].
Proof using Type.
  intros Hb Ha Hf Hsp. iIntros "Hl Hs Hpad". iExists b, reg, [67]. iSplit.
  - iPureIntro. constructor; cbn [ptr_cap ptr_addr wstart]; rewrite ?Ha; try lia;
      try (left; reflexivity); try reflexivity; try (repeat constructor; lia).
    unfold wstart. cbn [ptr_addr]. rewrite Ha. change (b - 0 + 8 <= r_end reg). lia.
  - rewrite /wwin /wstart. cbn [ptr_addr]. rewrite Ha. replace (b - 0 - b) with 0 by lia.
    iFrame "Hl". rewrite words_ps_bytes. iApply (bytes_app b 0 [67;0] (replicate 6 0) with "[$Hs $Hpad]").
Qed.

Context (Hsnr : find_fn ge (TAtom "setlocale_null_r") = Some (Defined snr_fn))
  (Heq : find_fn ge (TAtom "streq") = Some (Defined streq_fn))
  (Hstrcmp : find_fn ge (TAtom "strcmp") = Some (Defined glibc_strcmp)).

(** The first comparison finds the C name. Gnulib returns false and
    gives the caller back the two shares lent to the locale query. *)
Lemma wp_hard_locale_c q Φ :
  lookup (TAtom "hard-locale#str.31") (ge_globals ge) = Some q ->
  names -∗ word_string DfracDiscarded cn [67] -∗ word_string DfracDiscarded q [67] -∗
  ▷ (names -∗ Φ (Ret (WInt 0))) -∗ WP (ERun (invocation hard_locale_fn [WInt 0]) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hq. iIntros "Hnames #Hs #Hq HK". rewrite hard_locale_entry. step.
  iApply wp_alloc; [reflexivity | change (0 <= 257); lia | change (257 <= max_allocation_size); unfold max_allocation_size; lia |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b (Hb & Ha & Hsp)) "Ho". change (b mod 16 = 0) in Ha. change (b + 272 <= 2 ^ 48) in Hsp.
  pose proof (MemFwdLogic.mod16_mod8 b Ha) as Ha8.
  iDestruct (obj_zero_block with "Ho") as "(Hl & Hb & Ha)"; [change (0 <= 272); lia|].
  iDestruct (bytes_take_drop _ _ _ 2 with "Hb") as "[Hb Hrest]"; [vm_compute; lia|].
  iDestruct (auxes_take_drop _ _ _ 2 with "Ha") as "[Ha _]"; [vm_compute; lia|].
  iApply (wp_call_bind with "[-]"); [reflexivity | exact Hsnr | reflexivity |]. iNext.
  iApply (wp_ctype_null_r with "Hnames Hs Hl Hb Ha"); [exact Ha8 | change (b + 2 <= b + 272); lia |].
  iNext. iIntros "Hnames Hl Hb". iExists _. iSplit; [done|]. iNext. branch. step. step_global Hq.
  iDestruct (bytes_take_drop _ _ _ 6 with "Hrest") as "[Hpad _]"; [vm_compute; lia|].
  iDestruct (c_buffer with "Hl Hb Hpad") as "Hbuf"; [exact Hb | exact Ha8 | change (b + 8 <= b + 272); lia | exact Hsp |].
  iApply (wp_call_bind with "[-]"); [reflexivity | exact Heq | reflexivity |]. iNext.
  step. iApply (wp_call_glibc_strcmp registry (os_wi w0) ge with "Hbuf Hq"); [reflexivity | exact Hstrcmp | reflexivity |].
  iNext. iIntros "_ _". step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iExists _. iSplit; [done|]. iNext. step. branch. step. branch. step.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "Hnames").
Qed.

End conversion.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance image_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation gb := (img_a "_nl_global_locale").
Local Abbreviation greg := (img_gd "_nl_global_locale").
Local Abbreviation cb := (img_a "_nl_C_name").
Local Abbreviation qb := (img_a "hard-locale#str.31").

(** The linked image supplies each function on the path through the
    locale query, the copy and the comparison. The caller lends only
    the locale cell and the two strings. *)
Lemma hello_hard_locale_c dql dqc Φ :
  (liveq dql gb greg ∗ pcellq dqc gb 128 (mkPtr cb (Ro cb))) -∗
  word_string DfracDiscarded (mkPtr cb (Ro cb)) [67] -∗ word_string DfracDiscarded (mkPtr qb (Ro qb)) [67] -∗
  ▷ ((liveq dql gb greg ∗ pcellq dqc gb 128 (mkPtr cb (Ro cb))) -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (invocation hard_locale_fn [WInt 0]) : language.expr (nanofil_lang glibc_os_registry hge)) {{ Φ }}.
Proof using Type.
  apply (wp_hard_locale_c (glibc_program := image_program) gb greg dql dqc cb).
  10: reflexivity. all: vm_compute; first [reflexivity | congruence].
Qed.
End image.

(** Gnulib accepts every byte in the C locale. For an ASCII byte it
    keeps the character that glibc wrote. For a high byte it checks
    the name of the locale, reads the byte again as unsigned, and
    writes that value to the same four-byte output slot. *)

From Glibc Require Import AsciiConvert.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import IRFrames HelloBodies.
From Glibc Require Import HelloImageModule HelloImageLoad OsWorld OsRegistry FileInv LibioLogic WordString
  Mbrtowc HelloConvHardLocale Fix.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation heap b n := (mkRegion b (b + n) Heap Live).
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation gl := (img_a "_nl_global_locale").
Local Abbreviation eb := (img_a "errno").
Local Abbreviation cn := (rop (img_a "_nl_C_name")).
Local Abbreviation lit := (rop (img_a "hard-locale#str.31")).

(** The linker resolves the public alias and the converter's function
    pointer to the two bodies used above. The two data symbols name
    the objects that startup supplies. *)
Lemma mbrtowc_image_link fr : let ge := mkGenv hello_image_module img_globals fr in
  find_fn ge (TAtom "mbrtowc") = Some (Defined glibc_mbrtowc) /\
  find_fn ge (TAtom "__gconv_transform_ascii_internal") = Some (Defined glibc_ascii_internal) /\
  function_check_res ge (mkPtr (img_a "__gconv_transform_ascii_internal") (Fn (TAtom "__gconv_transform_ascii_internal"))) = Some ok /\ lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (objp (img_a "__libc_tsd_LOCALE")) /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (objp (img_a "errno")).
Proof. vm_compute. repeat split. Qed.

(** Reading the low byte as unsigned recovers the byte after a signed load. *)
Local Lemma ub_of_sb x : 0 <= x < 256 -> extension Ub (extension Sb x mod 2 ^ 32) mod 2 ^ 32 = x.
Proof.
  intros Hx. cbn [extension]. unfold sign_extension.
  assert (E : x mod 256 = x) by (apply Z.mod_small; lia). rewrite E.
  destruct (Z.leb_spec 128 x) as [Hh | Hh].
  - assert (E2 : (x - 256) mod 2 ^ 32 = x - 256 + 2 ^ 32) by (symmetry; apply Z.mod_unique with (-1); lia).
    rewrite E2.
    assert (E3 : (x - 256 + 2 ^ 32) mod 256 = x) by (symmetry; apply Z.mod_unique with (2 ^ 24 - 1); lia).
    rewrite E3. apply Z.mod_small. lia.
  - assert (E2 : x mod 2 ^ 32 = x) by (apply Z.mod_small; lia). rewrite E2. rewrite E. apply Z.mod_small. lia.
Qed.

Section conversion.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance byte_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** Each input byte produces its own wide character, including NUL.
    Only NUL returns zero instead of one. Errno records glibc's
    rejection even when gnulib recovers from it. *)
Lemma hello_rpl_mbrtowc dq dn sb sr sa sc ob oreg oa state n x xs es Φ :
  ow_errno w = Some (objp eb) ->
  sc = Obj sb \/ sc = Ro sb -> 0 < sb -> sb <= sa -> 1 <= n -> sa + n <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 < ob -> ob <= oa -> oa + 4 <= r_end oreg -> r_end oreg <= 2 ^ 48 ->
  0 < state -> state + 16 <= 2 ^ 48 -> 0 <= x < 256 -> length xs = 4%nat -> length es = 4%nat ->
  mbr_locale dq -∗ pcellq dn gl 128 cn -∗ mbr_tables -∗ word_string DfracDiscarded cn [67] -∗
  word_string DfracDiscarded lit [67] -∗ liveq DfracDiscarded sb sr -∗ bytesq DfracDiscarded sb (sa - sb) [x] -∗
  live state (heap state 16) -∗ bytes state 0 (le_bytes 0 4) -∗ live ob oreg -∗ bytes ob (oa - ob) xs -∗ bytes eb 0 es -∗
  ▷ (mbr_locale dq -∗ pcellq dn gl 128 cn -∗ live state (heap state 16) -∗ bytes state 0 (le_bytes 0 4) -∗ live ob oreg -∗
     bytes ob (oa - ob) (le_bytes x 4) -∗ bytes eb 0 (if x <? 128 then es else le_bytes 84 4) -∗
     Φ (Ret (WInt (if x =? 0 then 0 else 1)))) -∗
  WP (ERun (invocation rpl_fn [WPtr (mkPtr oa (Obj ob)); WPtr (mkPtr sa sc); WInt n; WPtr (objp state)]) : sexpr) {{ Φ }}.
Proof using Type.
  intros Herr Hsc Hsb Hsa Hn Hse Hsr Hob Hoa Hoe Hor Hstate Hste Hx Hxs Hes.
  destruct (mbrtowc_image_link fr) as (Hm & Ha & Hf & Hts & He).
  iIntros "Hloc Hname Htab #Hcn #Hlit #Hsl #Hbyte Hpsl Hps Hol Hbytes He HK".
  rewrite rpl_entry. step. iApply wp_alloc; [reflexivity | change (0 <= 4); lia | vm_compute; congruence |
    intros ? ? ? ? Hfresh Hw; exact (os_wi_alloc w _ _ _ _ _ Hfresh Hw) |]; iNext. iIntros (? _) "_".
  do 2 step. branch_as true. do 3 step.
  iApply wp_call_bind; [vx | exact Hm | reflexivity |]. iNext.
  rewrite (Z.mod_small n (2^64)); [|lia].
  iApply (wp_mbrtowc_c (glibc_program := byte_program) eb Herr He Hts Hf Ha dq sb sr sa sc ob oreg oa state n x xs es
    with "Hloc Htab Hsl Hbyte Hpsl Hps Hol Hbytes He"); try assumption.
  iNext. iIntros "Hloc Hpsl Hps Hol Hbytes He". destruct (Z.ltb_spec x 128) as [Hlo|Hhi].
  - destruct (Z.eqb_spec x 0); iExists _; iSplit; [done| |done|]; iNext;
      repeat first [step | branch]; iApply wp_ret; [reflexivity | vx | |reflexivity | vx |]; iNext;
      iApply ("HK" with "Hloc Hname Hpsl Hps Hol Hbytes He").
  - iExists _; iSplit; [done|]; iNext. step. branch. do 4 step. branch_as false. step.
    iDestruct "Hloc" as "(Hts & Hp & Hgl & Hc)".
    assert (Hhard : find_fn hge (TAtom "hard_locale") = Some (Defined hard_locale_fn)) by (vm_compute; reflexivity).
    iApply wp_call_bind; [vx | exact Hhard | reflexivity |]. iNext.
    iApply (hello_hard_locale_c w fr (DfracOwn 1) dn with "[$Hgl $Hname] Hcn Hlit").
    iNext. iIntros "[Hgl Hname]". iExists _. iSplit; [done|]. iNext. repeat first [step | branch].
    check_read_dq "Hsl" by a2. iNext. iIntros "_".
    assert (Ex : extended Sb W (of_bytes [x]) = Some (WInt (extension Sb x mod 2^32))).
    { change (Some (WInt (extension Sb (x + 0) mod 2^32)) = Some (WInt (extension Sb x mod 2^32))).
      rewrite Z.add_0_r. reflexivity. }
    load_bytes_dq "Hsl Hbyte" decode (exact Ex) by a2. iNext. iIntros "_ _".
    step_symbolic. check "Hol". iApply (wp_raw_store_w with "Hol Hbytes"); [vx | vx | reflexivity | a2 | exact Hxs | wi_store |].
    iNext. iIntros "Hol Hbytes". iApply wp_ret; [reflexivity | vx |]. iNext.
    iEval (rewrite ?Zmod_mod (ub_of_sb x Hx)) in "Hbytes".
    rewrite (proj2 (Z.eqb_neq x 0) ltac:(lia)). iApply ("HK" with "[$Hts $Hp $Hgl $Hc] Hname Hpsl Hps Hol Hbytes He").
Qed.
End conversion.

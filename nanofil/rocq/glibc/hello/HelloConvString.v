(** Gnulib converts the greeting from left to right. Each iteration
    consumes one byte, writes one four-byte character, and leaves room
    for the terminating NUL. When it reaches NUL, it clears the
    caller's source pointer and returns the number of characters. *)

From Glibc Require Import Unit_string_memchr_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import IRFrames HelloBodies.
From Glibc Require Import HelloImageModule HelloImageLoad OsWorld OsRegistry FileInv LibioLogic WordString
  ByteRead Mbrtowc HelloConvByte HelloConvWindow HelloGlibcDebts Fix.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation heap b n := (mkRegion b (b+n) Heap Live).
Local Abbreviation gl := (img_a "_nl_global_locale").
Local Abbreviation eb := (img_a "errno").
Local Abbreviation cn := (rop (img_a "_nl_C_name")).
Local Abbreviation lit := (rop (img_a "hard-locale#str.31")).

(** The loop changes errno on a high byte but always leaves four
    bytes there. The two locale cells return unchanged. *)
Definition conv_cells `{!gen_heapGS piece pval Σ} dq dn : iProp Σ :=
  mbr_locale dq ∗ pcellq dn gl 128 cn ∗ ∃ es, ⌜length es = 4%nat⌝ ∗ bytes eb 0 es.

(** Every wide character has the value of its original byte, so only
    its least significant byte is nonzero. *)
Lemma conv_le_byte x : 0 <= x < 256 -> le_bytes x 4 = [x;0;0;0].
Proof.
  intros H. change ((x / 1) mod 256 :: (x / 256) mod 256 ::
    (x / 65536) mod 256 :: (x / 16777216) mod 256 :: nil = [x;0;0;0]).
  rewrite Z.div_1_r (Z.mod_small x 256) // !Z.div_small; lia || reflexivity.
Qed.

Section convert.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance string_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Local Instance string_stable : SafepointStable (os_wi w) := os_wi_stable w.
Context (Herr : ow_errno w = Some (objp eb)).
Local Abbreviation wide s := ((flat_map (fun x : Z => [x;0;0;0]) s ++ [0;0;0;0])%list).
Local Abbreviation off i := (4 * Z.of_nat i).

(** Starting at character i, the loop writes the rest of the
    greeting and its terminator. Splitting off the first four bytes
    of the destination leaves just enough space for the next call. *)
Lemma conv_loop dq dn bd rd b4 b6 g Φ :
  0 < bd -> r_end rd <= 2^48 -> 0 < b4 -> b4 mod 8 = 0 -> b4 + 16 <= 2^48 ->
  0 < b6 -> b6 + 16 <= 2^48 ->
  mbr_tables -∗ word_string DfracDiscarded cn [67] -∗ word_string DfracDiscarded lit [67] -∗
  ∀ e q s (i : nat) xs,
    ⌜conv_regs e q (WPtr (mkPtr (bd + off i) (Obj bd))) (WInt (Z.of_nat (length s) + 1))
      (WPtr (objp b6)) (WPtr (objp b4)) (WPtr (objp b4)) (WInt bd) /\
      length xs = (4 * S (length s))%nat /\ bd + off i + Z.of_nat (length xs) <= r_end rd⌝ -∗
    word_string DfracDiscarded q s -∗ conv_cells dq dn -∗ live b6 (heap b6 16) -∗ bytes b6 0 (le_bytes 0 4) -∗
    live b4 (heap b4 16) -∗ pcell b4 0 g -∗ live bd rd -∗ bytes bd (off i) xs -∗
    (conv_cells dq dn -∗ live bd rd -∗ bytes bd (off i) (wide s) -∗ Φ (Ret (WInt (Z.of_nat i + Z.of_nat (length s))))) -∗
    WP (ERun (mkFrame mbs_fn e [] None (Exec (TAtom "L28") (b_insts (mbs_block "L28"))
         (b_jump (mbs_block "L28")))) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hbd Hdr Hb4 H4a H4e Hb6 H6e. iIntros "#Htab #Hcn #Hlit".
  assert (Hmem : Defines hge "memchr" Unit_string_memchr_os.fn___memchr) by (vm_compute; reflexivity).
  assert (Hstr : find_fn hge (TAtom "strnlen1") = Some (Defined strnlen1_fn)) by (vm_compute; reflexivity).
  assert (Hrpl : find_fn hge (TAtom "rpl_mbrtowc") = Some (Defined rpl_fn)) by (vm_compute; reflexivity).
  iLöb as "IH". iIntros (e q s i xs (Hregs & Lxs & Hroom)) "#Hs Hcells H6 Hzero H4 Hcell Hd Hxs HK".
  pose proof Hregs as (Hq & Hout & Hcount & Hst & Hsp & Hck & Hbase).
  iDestruct (ws_shape with "Hs") as %(Hchars & Hq0 & Hqe).
  Local Ltac expose l := let B := eval vm_compute in (mbs_block l) in change (mbs_block l) with B; cbn [b_insts b_jump].
  expose "L28"%string. step. branch_as false. step.
  iApply (conv_window (glibc_program := string_program) Hstr _ q _ _ _ _ _ _ s with "Hs"); [repeat split; lk_prove|].
  iNext. iIntros (e' ((Hq' & Hout' & Hcount' & Hst' & Hsp' & Hck' & Hbase') & Hwin)).
  iDestruct (ws_byte q s 0 with "Hs") as (sb sr (Hsc & Hsb & Hsa & Hse & Hsr)) "[#Hsl #Hbyte]"; [lia|].
  iEval (rewrite Z.add_0_r) in "Hbyte". iDestruct "Hcells" as "(Hloc & Hname & %es & %Les & He)".
  iDestruct (bytes_take_drop _ _ _ 4 with "Hxs") as "[Hfirst Hrest]"; [lia|].
  assert (Lfirst : length (take 4 xs) = 4%nat) by (apply length_take_le; lia).
  set (n := Z.min (Z.of_nat (length s) + 1) 16) in *.
  assert (Hn : 1 <= n <= Z.of_nat (length s) + 1) by (unfold n; lia).
  pose proof (sbyte_range s 0 Hchars) as Hx. expose "L37"%string.
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ rpl_fn (invocation rpl_fn [WPtr (mkPtr (bd + off i) (Obj bd));
    WPtr q; WInt n; WPtr (objp b6)])); [vx | exact Hrpl | rewrite (Z.mod_small n); [reflexivity|lia] |]. iNext.
  destruct q as [sa sc]. cbn [ptr_addr ptr_cap] in *.
  iEval (replace (off i) with (bd + off i - bd) by lia) in "Hfirst".
  iApply (hello_rpl_mbrtowc w fr dq dn sb sr sa sc bd rd (bd + off i) b6 n (sbyte s 0) (take 4 xs) es
    with "Hloc Hname Htab Hcn Hlit Hsl Hbyte H6 Hzero Hd Hfirst He"); try assumption; try lia.
  iNext. iIntros "Hloc Hname H6 Hzero Hd Hfirst He". iEval (rewrite conv_le_byte //) in "Hfirst".
  iEval (replace (bd + off i - bd) with (off i) by lia) in "Hfirst".
  iAssert (conv_cells dq dn) with "[Hloc Hname He]" as "Hcells".
  { iFrame "Hloc Hname". iExists _. iFrame "He". iPureIntro. destruct (sbyte s 0 <? 128); [exact Les | reflexivity]. }
  destruct s as [|c s].
  - change (sbyte [] 0) with 0. iExists _. iSplit; [done|]; iNext. repeat first [step | branch].
    iApply (wp_renew with "H4"); [reflexivity | vx | reflexivity | reflexivity | a2 | a2 | a2 |].
    iNext. iIntros "H4". store "H4" "Hcell". do 3 step_symbolic. iApply wp_ret; [reflexivity | vx |]. iNext.
    cbn [length flat_map app]. unwrap2. replace (bd + off i - bd) with (Z.of_nat i * 4) by lia.
    change (sign_extension (2^64) (2^63) 4) with 4. change (4 =? 0) with false. unfold sign_extension.
    rewrite (Z.mod_small (Z.of_nat i * 4) (2^64)); [|lia]. rewrite (proj2 (Z.leb_gt (2^63) (Z.of_nat i * 4)) ltac:(lia)).
    rewrite Z.quot_mul; [|lia]. unwrap2. rewrite Z.add_0_r. iApply ("HK" with "Hcells Hd Hfirst").
  - change (sbyte (c :: s) 0) with c. pose proof (Forall_inv Hchars) as Hc. cbv beta in Hc.
    rewrite (proj2 (Z.eqb_neq c 0) ltac:(lia)). iExists _. iSplit; [done|]; iNext.
    step. branch. step. step. branch. step. step. branch. step.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sa + 1)); [vx | cbn; f_equal; f_equal; addr_premise | vx |]. iNext.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bd + off (S i))); [vx | cbn; f_equal; f_equal; addr_premise | vx |]. iNext.
    step_symbolic. iApply wp_goto. iNext. step.
    iPoseProof (ws_suffix (mkPtr sa sc) (c::s) 1 with "Hs") as "Hs1"; [cbn; lia|].
    assert (Ei : off i + 4 = off (S i)) by lia. iEval (rewrite Ei) in "Hrest".
    iApply ("IH" $! _ (mkPtr (sa+1) sc) s (S i) (drop 4 xs) with "[%] Hs1 Hcells H6 Hzero H4 Hcell Hd Hrest").
    + split; [unfold conv_regs; repeat split; try lk_prove | rewrite length_drop; cbn [length] in Lxs; lia].
      lazymatch goal with |- lookup ?k ?E = _ => assert (Hleft : lookup k E = _) by lk_prove; rewrite Hleft end.
      cbn [length ptr_addr] in *. unwrap2. f_equal; f_equal; lia.
    + iIntros "Hcells Hd Htail". replace (Z.of_nat (S i) + Z.of_nat (length s)) with
        (Z.of_nat i + Z.of_nat (length (c::s))) by (cbn [length]; lia). iApply ("HK" with "Hcells Hd [Hfirst Htail]").
      rewrite (bytes_app bd (off i) [c;0;0;0] (wide s)). iFrame "Hfirst". rewrite Ei. iExact "Htail".
Qed.

(** Hello gives gnulib one output slot per byte plus a slot for NUL.
    The returned count is the original string length. The output
    consists of those characters followed by NUL and untouched padding. *)
Lemma hello_conv_string dq dn bd b4 b6 g s Φ :
  let n := 4 * (Z.of_nat (length s) + 1) in
  (0 < b4 /\ b4 mod 16 = 0 /\ b4 + 16 <= 2^48) -> (0 < b6 /\ b6 mod 16 = 0 /\ b6 + 16 <= 2^48) ->
  (0 < bd /\ bd mod 16 = 0 /\ bd + req_extent (wreq n) <= 2^48) ->
  mbr_tables -∗ word_string DfracDiscarded cn [67] -∗ word_string DfracDiscarded lit [67] -∗ conv_cells dq dn -∗
  wbuf bd n (replicate (Z.to_nat (req_extent (wreq n))) 0) -∗ gcell b4 g -∗ word_string DfracDiscarded g s -∗ obj b6 (heap_req 4 8) -∗
  ▷ (∀ ws, ⌜wide_text ws /\ Z.of_nat (length s) < 2^48⌝ -∗ conv_cells dq dn -∗ wbuf bd n ws -∗ Φ (Ret (WInt (Z.of_nat (length s))))) -∗
  WP (ERun (invocation mbs_fn [WPtr (objp bd); WPtr (objp b4); WInt (Z.of_nat (length s) + 1); WPtr (objp b6)]) : sexpr) {{ Φ }}.
Proof using Type*.
  intros n (Hb4 & H4a & H4e) (Hb6 & H6a & H6e) (Hbd & Hda & Hde).
  iIntros "#Htab #Hcn #Hlit Hcells (%cs & [%Lxs %Lcs] & Hd & Hxs & Ha) (H4 & Hp & _ & _) #Hs H6 HK".
  iDestruct (ws_shape with "Hs") as %(Hchars & Hg & Hfit).
  iDestruct (ws_byte g s 0 with "Hs") as (sb sr (Hsc & Hsb & Hsa & Hse & Hsr)) "[#Hsl _]"; [lia|].
  iAssert (live_capq DfracDiscarded (ptr_cap g) sr) as "Hsk"; [destruct Hsc as [->| ->]; iExact "Hsl"|].
  iDestruct (obj_zero_block with "H6") as "(H6 & Hz & _)"; [vm_compute; congruence|].
  iDestruct (bytes_take_drop _ _ _ 4 with "Hz") as "[Hz _]"; [vm_compute; lia|].
  set (xs := replicate (Z.to_nat (req_extent (wreq n))) 0) in *.
  pose proof (heap_req_extent 16 n) as Hcover. change (n <= req_extent (wreq n)) in Hcover.
  set (k := (4 * S (length s))%nat). assert (Lk : Z.of_nat k = n) by (unfold k,n; lia).
  iDestruct (bytes_take_drop _ _ _ k with "Hxs") as "[Hxs Htail]"; [lia|].
  assert (Ltake : length (take k xs) = k) by (apply length_take_le; lia).
  change (invocation mbs_fn _) with (mkFrame mbs_fn [(TAtom "v6", WPtr (objp b6));
    (TAtom "v4", WInt (Z.of_nat (length s) + 1)); (TAtom "v2", WPtr (objp b4)); (TAtom "v0", WPtr (objp bd))]
    [] None (Enter (TAtom "start") None)).
  step. iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w _ _ _ _ _ Hf Hw) |]; iNext. iIntros (? _) "_".
  do 3 step. branch_as true. step. check "H4". load_pointer_dq "H4 Hp Hsk" by a2. iNext. iIntros "H4 Hp _".
  do 2 step. branch_as false. step.
  iPoseProof (conv_loop dq dn bd (heap bd (req_extent (wreq n))) b4 b6 g Φ with "Htab Hcn Hlit") as "Hloop"; try assumption; try (Z.div_mod_to_equations; lia).
  iApply ("Hloop" $! _ g s 0%nat (take k xs) with "[%] Hs Hcells H6 Hz H4 Hp Hd Hxs").
  { split; [unfold conv_regs; repeat split; try reflexivity; cbn [ptr_addr]; unwrap2; rewrite ?Z.add_0_r; reflexivity |
      split; [exact Ltake | rewrite Ltake Lk; cbn [r_end]; lia]]. }
  iIntros "Hcells Hd Hwide".
  assert (Lflat : length (flat_map (fun x : Z => [x;0;0;0]) s) = (4 * length s)%nat).
  { clear. induction s; cbn [flat_map length app]; lia. }
  assert (Lwide : length (wide s) = k) by (rewrite length_app Lflat; unfold k; cbn [length]; lia).
  iApply ("HK" $! (wide s ++ drop k xs)%list with "[%] Hcells").
  { split; [|lia]. exists s. split; [exact Hchars|]. split; [rewrite length_app Lwide; unfold k; lia|].
    replace (4 * length s + 4)%nat with (length (wide s)) by (rewrite Lwide; unfold k; lia). apply take_app_length. }
  iExists cs. iSplit. { iPureIntro. rewrite length_app Lwide length_drop. lia. }
  iFrame "Hd Ha". rewrite (bytes_app bd 0 (wide s) (drop k xs)) Lwide. iFrame "Hwide Htail".
Qed.
End convert.

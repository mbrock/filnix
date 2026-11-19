(** Gnulib chooses how much input to offer the converter before it
    reads the next character. It checks the first four bytes one at a
    time. If none is NUL, it asks strnlen1 to count at most twelve
    more. The resulting window always includes the first byte and
    never extends past the string's terminator. *)

From Glibc Require Import Unit_string_memchr_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import IRFrames HelloBodies.
From Glibc Require Import FileInv LibioLogic WordString ByteRead MemchrLast HelloGlibcLeaf Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** When the scan passes the first four bytes, it counts up to twelve more. *)
Local Lemma window_min l : (4 <= l)%nat -> Z.min (Z.of_nat (l - 4) + 1) 12 + 4 = Z.min (Z.of_nat l + 1) 16.
Proof. intros Hl. lia. Qed.

(** The window scan preserves both cursors, the remaining capacity,
    the shift state and the two values needed to finish the call. *)
Definition conv_regs (e : env) (q : ptr) (out count state src check base : word) :=
  lookup (TAtom "pr.5") e = Some (WPtr q) /\ lookup (TAtom "pr.7") e = Some out /\
  lookup (TAtom "pr.1") e = Some count /\ lookup (TAtom "pr.2") e = Some state /\
  lookup (TAtom "v2") e = Some src /\ lookup (TAtom "chk0") e = Some check /\ lookup (TAtom "v23") e = Some base.

Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{HM : !Defines ge "memchr" Unit_string_memchr_os.fn___memchr}.
Context (Hstrn : find_fn ge (TAtom "strnlen1") = Some (Defined strnlen1_fn)).
Local Instance scan_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The scan passes the smaller of sixteen and the remaining length
    including NUL. It keeps a read-only share of the entire source, so
    the converter can read the first byte again. *)
Lemma conv_window e q out count state src chk base s Φ :
  conv_regs e q out count state src chk base ->
  word_string DfracDiscarded q s -∗
  ▷ (∀ e', ⌜conv_regs e' q out count state src chk base /\
             lookup (TAtom "pr.8") e' = Some (WInt (Z.min (Z.of_nat (length s) + 1) 16))⌝ -∗
       WP (ERun (mkFrame mbs_fn e' [] None (Exec (TAtom "L37") (b_insts (mbs_block "L37"))
            (b_jump (mbs_block "L37")))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame mbs_fn e [] None (Exec (TAtom "L29") (b_insts (mbs_block "L29"))
       (b_jump (mbs_block "L29")))) : sexpr) {{ Φ }}.
Proof using Type*.
  intros (Hq & Hout & Hcount & Hstate & Hsrc & Hchk & Hbase). iIntros "#Hs HK".
  iDestruct (ws_shape with "Hs") as %(Hchars & Hq0 & Hqend).
  cbn [mbs_block hblk b_insts b_jump].
  Local Ltac scan_addr := cbn [ptr_addr]; unfold raw_address; rewrite ?Z.add_0_r; unwrap2; lia.
  Local Ltac scan_byte q s k :=
    let b := fresh "b" in let r := fresh "r" in let Hcap := fresh "Hcap" in
    iDestruct (ws_byte q s k with "Hs") as (b r (Hcap & ? & ? & ? & ?)) "[#Hl #Hx]"; [lia|];
    first [check_read_dq "Hl" by a2 | iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
      [reflexivity | vx | reflexivity | exact Hcap | scan_addr | scan_addr | lia | lia | apply Z.mod_1_r |]];
    iNext; iIntros "_";
    load_bytes_dq "Hl Hx" decode (apply extended_chr) by a2; iNext; iIntros "_ _";
    iClear "Hl Hx"; step_symbolic.
  Local Ltac scan_branch s Hchars k :=
    let Hx := fresh "Hx" in pose proof (sbyte_range s k Hchars) as Hx;
    let H := fresh "Hbyte" in assert (H : (chr_w (sbyte s k) mod 2^32 =? 0) = (sbyte s k =? 0))
      by (rewrite Z.mod_small; [apply chr_w_eqb; lia | apply chr_w_range]);
    branch_symbolic; change (0 mod 2^32) with 0; rewrite H;
    destruct (Z.eqb_spec (sbyte s k) 0) as [Hz|Hz]; cbn [edge_label];
    [apply (proj1 (sbyte_zero s k Hchars ltac:(lia))) in Hz; step; iApply ("HK" with "[%]");
       split; [repeat split; lk_prove| rewrite <- Hz; lk_prove] |
     assert (k < length s)%nat by (pose proof (sbyte_zero s k Hchars ltac:(lia)); lia); clear Hz].
  scan_byte q s 0%nat. scan_branch s Hchars 0%nat.
  Local Ltac scan_next q k := step;
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr q + Z.of_nat k));
    [vx | cbn; f_equal; f_equal; addr_premise | vx |]; iNext.
  scan_next q 1%nat. scan_byte q s 1%nat. scan_branch s Hchars 1%nat.
  scan_next q 2%nat. scan_byte q s 2%nat. scan_branch s Hchars 2%nat.
  scan_next q 3%nat. scan_byte q s 3%nat. scan_branch s Hchars 3%nat.
  scan_next q 4%nat.
  iDestruct (ws_suffix q s 4 with "Hs") as "Hs4"; [lia|].
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ strnlen1_fn (invocation strnlen1_fn [WPtr (ptr_add q 4); WInt 12]));
    [vx | exact Hstrn | reflexivity |]. iNext.
  iApply (strnlen1_glibc with "Hs4"); [lia|]. iNext. iIntros "_". iExists _. iSplit; [done|]. iNext.
  step_symbolic. step. step. iApply ("HK" with "[%]"). split; [repeat split; lk_prove|].
  lazymatch goal with |- lookup ?k ?E = _ => assert (Hlen : lookup k E = _) by lk_prove; rewrite Hlen end.
  rewrite length_drop. unwrap2. rewrite window_min; [reflexivity | lia].
Qed.
End scan.

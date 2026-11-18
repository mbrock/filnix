(** Wide overflow increments the cursor before it stores the character.
    The old cursor must therefore have room for one word in the
    physical buffer. The stream's write end need not leave any room:
    glibc uses that end to force a flush on line-buffered streams. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWOverflowDispatch LibioWXsputnWindow LibioWXsputnRoom LibioWXsputnFill LibioWOverflowFlush CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Section store.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e at_ := (ERun (mkFrame wfile_overflow_fn e [] None at_) : sexpr).

Local Lemma lend_word fb fr wd wr fl w i j : 0 < wd -> wd+232 <= r_end wr -> r_end wr <= 2^63 ->
  0 <= i < window_size w -> write_window fb fr wd wr fl w (i+1) j -∗ ∃ b br o old,
    ⌜wpos wd w i = mkPtr (b+o) (Obj b) /\ 0 < b /\ 0 <= o /\ b+o+4 <= r_end br /\ r_end br <= 2^63 /\ length old = 4%nat⌝ ∗
    live b br ∗ bytes b o old ∗ (∀ ys, ⌜length ys = 4%nat /\ Forall (fun x => 0 <= x < 256) ys⌝ -∗
      live b br -∗ bytes b o ys -∗ write_window fb fr wd wr fl w (i+1) j).
Proof using Type.
  intros Hwd Hwe Hwr Hi. iIntros "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
  destruct w as [| |b sz]; cbn [window_size] in Hi; [lia| |].
  - assert (i=0) as -> by lia. iDestruct "Hshort" as (xs [L V]) "Hx". iExists wd, wr, woff_shortbuf, xs.
    iSplit; [iPureIntro; unfold woff_shortbuf, wpos, window_base; cbn [ptr_addr ptr_cap]; split_and!; try done; try lia; f_equal; lia|].
    iFrame "Hl Hx". iIntros (ys H) "Hl Hy". rewrite /write_window. iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hb". iExists ys. by iFrame.
  - iDestruct "Hb" as (br xs caps (Hk & He & Hr & Hb & Ha & Hsz & M & L & V & Lc)) "(Hb & Hx & Haux)".
    set (k := Z.to_nat (4*i)). assert (K : Z.of_nat k = 4*i) by (unfold k; lia). pose proof (Z.div_mod sz 4 ltac:(lia)).
    iDestruct (lend_bytes b 0 xs k 4 with "Hx") as (old Lo) "[Hword Hback]"; [lia|done|].
    iEval (rewrite Z.add_0_l K) in "Hword Hback". iExists b, br, (4*i), old. iSplit; [iPureIntro; split_and!; (done || lia)|].
    iFrame "Hb Hword". iIntros (ys Vys) "Hb Hy". iDestruct ("Hback" $! ys with "[%] Hy") as (xs' [L' V']) "Hx"; [done|].
    rewrite /write_window. iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hshort". iExists br, xs', caps. iFrame. iPureIntro. split_and!; (assumption || lia).
Qed.

(** Once the character is in the buffer, glibc reads the flags to
    decide whether to write it out immediately. *)
Definition wo_test_flags := Eval vm_compute in
  match body_at wfile_overflow_fn "L262" with Exec l code j => Exec l (skipn 11 code) j | x => x end.

Lemma wp_wo_store vb self e fb ch wd w i Φ : 0 <= ch < 2^32 -> i < window_size w -> wo_regs BeforeStore e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗
  (∀ ee, ⌜wo_regs AfterStore ee fb ch⌝ -∗ file_pending ge vb self (obj fb) 1 wd w (i+1) -∗ WP (run ee wo_test_flags) {{ Φ }}) -∗
  WP (run e (body_at wfile_overflow_fn "L262")) {{ Φ }}.
Proof using Type.
  intros Ch Room (Hfp & Hch & Hck & H85). iIntros "HP HK".
  iDestruct (pending_write_window with "HP") as (fb' fr wr fl j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]".
  injection Eq as <-. iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
  body_start wfile_overflow_fn "L262"%string. step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl".
  load_wpos "Hl" "Hcur" "Hb". step. check "Hl". store "Hl" "Hcur".
  pose proof (wpos_bounds _ _ (i+1) Hwd ltac:(lia) B ltac:(lia)) as (_ & R & _). cbn [ptr_addr wpos] in R.
  iAssert (write_window fb fr wd wr fl w (i+1) j) with "[-Hclose HK]" as "Hwin".
  { rewrite /write_window. iFrame "Hf Hfl Hwd Hl Hbase Hend Hstop Hshort Hb". unfold wpos; cbn [ptr_addr ptr_cap].
    pose proof (wpos_bounds _ _ i Hwd ltac:(lia) B Hi) as (_ & Ri & _). cbn [wpos ptr_addr] in Ri.
    replace (((ptr_addr (window_base wd w)+4*i) mod 2^64+4 mod 2^64) mod 2^64) with (ptr_addr (window_base wd w)+4*(i+1))
      by (rewrite !(Z.mod_small _ (2^64)); lia). done. }
  iDestruct (lend_word with "Hwin") as (b br o old (P & Hb & Ho & He & Hr & Lo)) "(Hl & Hx & Hback)"; [lia..|].
  rewrite P. check "Hl". iApply (wp_raw_store_w with "Hl Hx"); [vx|vx|reflexivity|a2|done|wi_store|].
  iNext. iIntros "Hl Hx". iDestruct ("Hback" with "[%] Hl Hx") as "Hwin"; [split; [apply length_le_bytes|apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (n & <- & _); apply Z.mod_pos_bound; lia]|].
  iDestruct ("Hclose" with "[%] Hwin") as "HP"; [lia|]. iApply ("HK" with "[%] HP"). unfold wo_regs. split_and!; lookups; done.
Qed.
End store.

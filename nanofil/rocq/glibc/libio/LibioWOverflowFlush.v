(** Wide overflow flushes in three places. A caller can request a flush
    instead of supplying a character. A full buffer must drain before
    the next store, and a line-buffered or unbuffered stream may drain
    again after the store. All three sites pass the same base and count
    to the wide writer. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWOverflowDispatch LibioWXsputnWindow LibioWXsputnRoom LibioWOverflowWrite CBlocks.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Inductive wo_flush_site := FlushRequest | BeforeStore | AfterStore.
Definition wo_flush_start site := match site with FlushRequest => "L211" | BeforeStore => "L260" | AfterStore => "L332" end%string.
Definition wo_flush_end site := match site with FlushRequest => "L218" | BeforeStore => "L281" | AfterStore => "L356" end%string.
Definition wo_flush_result site := match site with FlushRequest => "v258" | BeforeStore => "v321" | AfterStore => "v396" end%string.
Definition wo_regs site e fb ch := reg e "v0" (WPtr (obj fb)) /\ reg e "v2" (WInt ch) /\ reg e "chk0" (WPtr (obj fb)) /\
  match site with FlushRequest => True | _ => reg e "chk85" (WPtr (mkPtr (fb+160) (Obj fb))) end.

Section sites.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn} (Hwrite : wdo_pending_spec vb self 1 E).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e l := (ERun (mkFrame wfile_overflow_fn e [] None (body_at wfile_overflow_fn l)) : sexpr).

Local Lemma pending_mode fb wd w i : file_pending ge vb self (obj fb) 1 wd w i -∗ ∃ fr,
  ⌜0 < fb /\ fb mod 8 = 0 /\ fb+224 <= r_end fr /\ r_end fr <= 2^63⌝ ∗ live fb fr ∗ int_cell fb off_mode 1 ∗
  (live fb fr -∗ int_cell fb off_mode 1 -∗ file_pending ge vb self (obj fb) 1 wd w i).
Proof using Type.
  iIntros "(%fb' & %fr & %st & %nb & %tw & %tm & %wr & %j & %B & %P & Hl & Hfields & Hlock & Hnb & Hd)".
  pose proof P as (Eq & Hal & Hfb & He & Hr & _ & _ & Hm & _). injection Eq as <-.
  iDestruct "Hfields" as "(%L & Hfl & Hp & Hfd & Hf2 & Ho & %C & Hc & Hlk & Hof & Hcv & Hwd & Hfr & Hbuf & Hm & Htot & Hvt)".
  rewrite Hm. iExists fr. iSplit; [iPureIntro; unfold file_size in *; tauto|]. iFrame "Hl Hm".
  iIntros "Hl Hm". iExists fb, fr, st, nb, tw, tm, wr, j. iSplit; [done|]. rewrite /file_wide_at. iFrame "Hl Hlock Hnb Hd".
  iSplit; [done|]. rewrite /file_fields Hm. by iFrame.
Qed.

Local Ltac read_cursor field := load "Hf" "Hwd" "Hl"; step; check "Hl"; load_wpos "Hl" field "Hb".

(** Only the full-buffer case needs the precise buffer identity after
    a successful call. The same postcondition covers the other sites,
    which can forget the cursor and return the stream. *)
Lemma wp_wo_flush site e fb ch wd w i Φ : wo_regs site e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗
  (∀ ee (ok : bool), ⌜wo_regs site ee fb ch /\ reg ee (wo_flush_result site) (WInt (if ok then 0 else 2^32-1))⌝ -∗
    (if ok then file_pending ge vb self (obj fb) 1 wd w 0 else file_wide ge vb self (obj fb) 1) -∗ E -∗
    WP (run ee (wo_flush_end site)) {{ Φ }}) -∗ WP (run e (wo_flush_start site)) {{ Φ }}.
Proof using Type*.
  intros (Hfp & Hch & Hck & H85). iIntros "HP HE HK".
  iDestruct (pending_mode with "HP") as (rr (Fb & Fa & Fe & Fr)) "(Hf & [%M Hm] & Hback)".
  destruct site; cbn [wo_flush_start wo_flush_end wo_flush_result] in *;
    [body_start wfile_overflow_fn "L211"%string|body_start wfile_overflow_fn "L260"%string|body_start wfile_overflow_fn "L332"%string];
    step; check "Hf"; load_s32 "Hf" "Hm"; step; branch; step;
    iDestruct ("Hback" with "Hf [$Hm //]") as "HP"; clear rr Fb Fa Fe Fr M.
  all: iDestruct (pending_write_window with "HP") as (fb' fr wr fl j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]";
    injection Eq as <-; iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)";
    iEval (rewrite <-(wpos_zero wd w)) in "Hbase"; step; try check "Hf";
    read_cursor "Hbase"; read_cursor "Hcur"; read_cursor "Hbase"; do 3 step; step_named.
  all: pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hi) as (Ba & Ai & C); cbn [wpos ptr_addr] in Ai.
  all: rewrite Z.add_0_r wflush_count in E0.
  all: try lia.
  all: subst x; iEval (rewrite wpos_zero) in "Hbase"; iDestruct ("Hclose" $! i with "[%] [-HE HK]") as "HP"; [done|rewrite /write_window; by iFrame|];
    iApply wp_call_bind; [vx|apply defines|reflexivity|]; iNext; norm; rewrite wpos_zero; unwrap2;
    iApply (Hwrite _ (obj fb) wd w i with "HP HE"); [reflexivity|]; iNext; iIntros (ok) "HP HE";
    resume; step; step; iApply ("HK" $! _ ok with "[%] HP HE"); unfold wo_regs; split_and!; lookups; try done; destruct ok; reflexivity.
Qed.
End sites.

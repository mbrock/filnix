(** The default wide writer fills whatever room the stream has, then
    passes one more character to overflow if any input remains. A
    successful overflow starts another round on the unread suffix.
    Failure returns the number of characters accepted so far. *)

From Glibc Require Import Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWOverflowDispatch LibioWXsputnWords LibioWXsputnRoom LibioWXsputnWindow LibioWXsputnAppend
  LibioWXsputnTail LibioWXsputnCopy WPrintfDispatch CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation p b o := (mkPtr (b+o) (Obj b)).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Section writer.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_block e l := (ERun (mkFrame wdefault_xsputn_fn e [] None (body_at wdefault_xsputn_fn l)) : sexpr).

Lemma wchar_sub dq s so cs a k : (a+k <= length cs)%nat ->
  bytesq dq s so (stage_bytes cs) -∗ bytesq dq s (so+4*Z.of_nat a) (stage_bytes (take k (drop a cs))) ∗
    (bytesq dq s (so+4*Z.of_nat a) (stage_bytes (take k (drop a cs))) -∗ bytesq dq s so (stage_bytes cs)).
Proof using Type.
  intros H. set (part := take k (drop a cs)).
  assert (D : cs = (take a cs ++ part ++ drop k (drop a cs))%list) by (unfold part; rewrite !take_drop //).
  rewrite {1 2}D /stage_bytes !flat_map_app /bytesq !byte_ps_app !ptsq_app. fold (stage_bytes (take a cs)).
  rewrite stage_bytes_length length_take_le; [|lia]. replace (Z.of_nat (4*a)) with (4*Z.of_nat a) by lia.
  iIntros "(Hp & Hx & Hs)". iFrame "Hx". iIntros "Hx". iFrame.
Qed.

Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hfn : find_fn ge (TAtom "zmemmove") = None) (Hsym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Context `{!Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
  !Defines ge "__wmempcpy" wmempcpy_fn}.

Local Definition after_fill fb fr wd wr fl w j dq s sr so cs Φ : iProp Σ := ∀ e' k left,
  ⌜0 <= k <= window_size w /\ wsource_regs e' (obj fb) s so (size cs) left "pr.8" "pr.3"⌝ -∗
  write_window fb fr wd wr fl w k j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗ WP (at_block e' "L37") {{ Φ }}.

Local Lemma default_copy e fb fr wd wr fl w i j dq s sr so cs t k Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i -> i+k <= window_size w -> 0 <= k <= t -> size cs <= 128 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  wsource_regs e (obj fb) s so (size cs) t "pr.7" "pr.2" -> reg e "chk0" (WPtr (p fb 160)) -> reg e "pr.9" (WInt k) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  after_fill fb fr wd wr fl w j dq s sr so cs Φ -∗ WP (at_block e "L42") {{ Φ }}.
Proof using Type*.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hfit Hk N V Hs Hsa Hso Hse Hsr (Hfp & Hcnt & Ht & Hp & R) Hck H9.
  iIntros "Hwin Hs Hcs HK". body_start wdefault_xsputn_fn "L42"%string. step.
  destruct (Z.eq_dec k 0) as [->|Hnz].
  - branch_as true. step. step. branch_as false. do 4 step. iApply ("HK" $! _ i t with "[%] Hwin Hs Hcs").
    unfold wsource_regs. split_and!; try lia; lookups; unwrap2; repeat f_equal; lia.
  - set (a := Z.to_nat (size cs-t)). set (ys := take (Z.to_nat k) (drop a cs)).
    assert (Ly : size ys = k) by (unfold ys; rewrite length_take_le; [lia|rewrite length_drop; lia]).
    assert (Vy : Forall (fun c => 0 <= c < 2^32) ys) by (apply Forall_take, Forall_drop; done).
    iDestruct (wchar_sub dq s so cs a (Z.to_nat k) with "Hcs") as "[Hy Hback]"; [lia|].
    iAssert (append_next false fb fr wd wr fl w i j (size cs) t dq s sr (so+4*Z.of_nat a) ys Φ) with "[Hback HK]" as "Hnext".
    { iIntros (ee ((Hfp' & Hcnt' & H9' & Hck' & Ht') & Hp' & H10)) "Hwin Hs Hy".
      specialize (H10 eq_refl). cbn in Ht', Hp'. iDestruct ("Hback" with "Hy") as "Hcs".
      body_start wdefault_xsputn_fn "L49"%string. do 3 step. iApply ("HK" $! _ (i+size ys) (t-k) with "[%] Hwin Hs Hcs").
      unfold wsource_regs. split_and!; try lia; lookups; rewrite ?Ly; unwrap2; try reflexivity; do 3 f_equal; unfold a; lia. }
    destruct (Z_lt_le_dec 20 k) as [Hlarge|Hsmall].
    + branch_as false. step.
      iApply (wp_wxsputn_append_bulk Hmove Hfn Hsym false _ fb fr wd wr fl w i j (size cs) t dq s sr (so+4*Z.of_nat a) ys
        with "Hwin Hs Hy Hnext"); try assumption; try lia.
      * unfold append_regs. split_and!; lookups; rewrite ?Ly; reflexivity.
      * lookups. do 3 f_equal; unfold a; lia.
    + branch_as true. step. step. branch_as true. step.
      iApply (wp_wxsputn_append_small false _ fb fr wd wr fl w i j (size cs) t dq s sr (so+4*Z.of_nat a) ys
        with "Hwin Hs Hy Hnext"); try assumption; try lia.
      * unfold append_regs. split_and!; lookups; rewrite ?Ly; reflexivity.
      * lookups. do 3 f_equal; unfold a; lia.
Qed.

Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI___woverflow" woverflow_fn} (Hov : woverflow_spec vb self E woverflow_fn).

(** Each round chooses the smaller of the space available and the
    input remaining. After the copy the overflow path gets back the
    whole stream, even when the copy reached the end of the buffer. *)
Local Lemma default_loop fp dq s sr so cs Φ : size cs <= 128 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  ⊢ wdefault_round vb self E fp dq s sr so cs Φ.
Proof using Type*.
  intros N V Hs Hsa Hso Hse Hsr. iLöb as "IH". iIntros (e t Reg) "HF HE Hs Hcs HK".
  iDestruct (wide_write_window with "HF") as (fb fr wd wr fl w i j
    (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & Hfl & B & Hi & Hj)) "[Hwin Hclose]". subst fp.
  iAssert (after_fill fb fr wd wr fl w j dq s sr so cs Φ) with "[Hclose HE HK]" as "Hdone".
  { iIntros (ee k left [R G]) "Hwin Hs Hcs". iDestruct ("Hclose" $! k with "[%] Hwin") as "HF"; [done|].
    iApply (wp_wdefault_tail vb self E Hov _ dq s sr so cs Φ ee left with "HF HE Hs Hcs IH HK"); assumption. }
  iApply (wp_wdefault_room e fb fr wd wr fl w i j s so (size cs) t with "Hwin [-]"); try assumption; try lia.
  iSplit.
  - iIntros (ee G) "Hwin". iApply ("Hdone" $! ee i t with "[%] Hwin Hs Hcs"). auto.
  - iIntros (ee (G & Hck & Hroom & Hpos)) "Hwin". destruct G as (Hfp & Hcnt & Ht & Hp & R).
    pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hi) as (_ & _ & C).
    body_start wdefault_xsputn_fn "L35"%string. step. destruct (Z_lt_le_dec t (j-i)) as [Hless|Huse].
    + branch_as false. step. iApply (default_copy _ fb fr wd wr fl w i j dq s sr so cs t t with "Hwin Hs Hcs Hdone");
        try assumption; try lia; try unfold wsource_regs; repeat split; try lia; lookups; unwrap2; reflexivity.
    + branch_as true. do 3 step. iApply (default_copy _ fb fr wd wr fl w i j dq s sr so cs t (j-i) with "Hwin Hs Hcs Hdone");
        try assumption; try lia; try unfold wsource_regs; repeat split; try lia; lookups; unwrap2; reflexivity.
Qed.

(** The file writer calls the default writer with the unread suffix
    after its first copy. The suffix can start partway into the staged
    source. On return the caller still owns all the characters it lent. *)
Lemma wp_wdefault_xsputn frame fp dq s sr so cs Φ :
  call_frame wdefault_xsputn_fn [WPtr fp; WPtr (p s so); WInt (size cs)] = Some frame ->
  size cs <= 128 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  file_wide ge vb self fp 1 -∗ E -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  ▷ wcount_post vb self E fp dq s sr so cs Φ -∗ WP (ERun frame : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hcall N V Hs Hsa Hso Hse Hsr. injection Hcall as <-. iIntros "HF HE Hs Hcs HK".
  step. step. destruct (Z.eq_dec (size cs) 0) as [Hz|Hnz].
  - branch_as false. step. iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! 0 with "[%] HF HE Hs Hcs"). lia.
  - branch_as true. step. iApply (default_loop fp dq s sr so cs Φ N V Hs Hsa Hso Hse Hsr with "[%] HF HE Hs Hcs HK").
    unfold wsource_regs. split_and!; try lia; lookups; unwrap2; try reflexivity; do 3 f_equal; lia.
Qed.
End writer.

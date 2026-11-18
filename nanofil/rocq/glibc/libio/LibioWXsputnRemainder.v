(** The file writer first copies the part that fits, then gives the
    default writer the remaining characters. Both copies borrow their
    input from the same stage. Even on a short write the caller gets
    the whole stage back. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps LibioWIdle LibioWOverflowDispatch
  LibioWXsputnWords LibioWXsputnRoom LibioWXsputnWindow LibioWXsputnAppend LibioWXsputnSelect
  LibioWXsputnDefault LibioWXsputnTail LibioWXsputnCopy WPrintfDispatch WPrintfFileFlush MemFwdCode CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation p b o := (mkPtr (b+o) (Obj b)).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Definition wf_finish_regs e fb n flush := reg e "v0" (WPtr (obj fb)) /\ reg e "v4" (WInt n) /\
  reg e "chk0" (WPtr (obj fb)) /\ reg e "pr.6" (WInt flush).
Section remainder.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_block e l := (ERun (mkFrame wprintf_xsputn_fn e [] None (body_at wprintf_xsputn_fn l)) : sexpr).
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hfn : find_fn ge (TAtom "zmemmove") = None) (Hsym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Context `{!Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI_mempcpy" glibc_mempcpy,
  !Defines ge "__wmempcpy" wmempcpy_fn}.

Local Definition wf_remainder fb fr wd wr fl w j flush dq s sr so cs Φ : iProp Σ := ∀ ee i k,
  ⌜0 <= i <= window_size w /\ 0 <= k <= size cs /\ wf_finish_regs ee fb (size cs) flush /\
    reg ee "pr.4" (WInt (size cs-k)) /\ reg ee "pr.1" (WPtr (p s (so+4*k)))⌝ -∗
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗ WP (at_block ee "L112") {{ Φ }}.

Local Lemma wf_copy e fb fr wd wr fl w i j flush dq s sr so cs k Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i -> i+k <= window_size w -> 0 < k <= size cs -> size cs <= 128 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  wf_checked e fb s so (size cs) -> reg e "pr.9" (WInt k) -> reg e "pr.6" (WInt flush) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wf_remainder fb fr wd wr fl w j flush dq s sr so cs Φ -∗ WP (at_block e "L117") {{ Φ }}.
Proof using Type*.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hfit Hk N V Hs Hsa Hso Hse Hsr ((Hfp & Hp & Hn) & Hck) H9 H6.
  iIntros "Hwin Hs Hcs HK". body_start wprintf_xsputn_fn "L117"%string. step.
  set (ys := take (Z.to_nat k) cs). assert (Ly : size ys = k) by (unfold ys; rewrite length_take_le; lia).
  assert (Vy : Forall (fun c => 0 <= c < 2^32) ys) by (apply Forall_take; done).
  iDestruct (wchar_sub dq s so cs O (Z.to_nat k) with "Hcs") as "[Hy Hback]"; [lia|].
  change (4*Z.of_nat O) with 0. iEval (rewrite Z.add_0_r /=) in "Hy Hback".
  iAssert (append_next true fb fr wd wr fl w i j (size cs) flush dq s sr so ys Φ) with "[Hback HK]" as "Hnext".
  { iIntros (ee ((Hfp' & Hn' & H9' & Hck' & H6') & Hp' & _)) "Hwin Hs Hy". iDestruct ("Hback" with "Hy") as "Hcs".
    body_start wprintf_xsputn_fn "L124"%string. do 3 step. iApply ("HK" $! _ (i+size ys) k with "[%] Hwin Hs Hcs").
    unfold wf_finish_regs. split_and!; try lia; lookups; rewrite ?Ly; unwrap2; reflexivity. }
  destruct (Z_lt_le_dec 20 k).
  - branch_as false. step. iApply (wp_wxsputn_append_bulk Hmove Hfn Hsym true _ fb fr wd wr fl w i j (size cs) flush dq s sr so ys
      with "Hwin Hs Hy Hnext"); try assumption; try lia; try unfold append_regs; repeat split; lookups; rewrite ?Ly; reflexivity.
  - branch_as true. step. iApply (wp_wxsputn_append_small true _ fb fr wd wr fl w i j (size cs) flush dq s sr so ys
      with "Hwin Hs Hy Hnext"); try assumption; try lia; try unfold append_regs; repeat split; lookups; rewrite ?Ly; reflexivity.
Qed.

Local Lemma wf_count e fb fr wd wr fl w i j flush dq s sr so cs room Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i <= window_size w -> 0 <= room <= window_size w-i -> 0 < size cs <= 128 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  wf_checked e fb s so (size cs) -> reg e "pr.10" (WInt room) -> reg e "pr.6" (WInt flush) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wf_remainder fb fr wd wr fl w j flush dq s sr so cs Φ -∗ WP (at_block e "L20") {{ Φ }}.
Proof using Type*.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hroom N V Hs Hsa Hso Hse Hsr ((Hfp & Hp & Hn) & Hck) H10 H6.
  iIntros "Hwin Hs Hcs HK". pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hi) as (_ & _ & C).
  body_start wprintf_xsputn_fn "L20"%string. step. destruct (Z.eq_dec room 0) as [->|Hnz].
  - branch_as true. step. iApply ("HK" $! _ i 0 with "[%] Hwin Hs Hcs").
    unfold wf_finish_regs. split_and!; try lia; lookups; unwrap2; try reflexivity; do 3 f_equal; lia.
  - branch_as false. step. step. destruct (Z_lt_le_dec (size cs) room).
    + branch_as false. step. iApply (wf_copy _ fb fr wd wr fl w i j flush dq s sr so cs (size cs) with "Hwin Hs Hcs HK");
        try assumption; try lia; try unfold wf_checked, wf_input; repeat split; lookups; unwrap2; reflexivity.
    + branch_as true. do 3 step. iApply (wf_copy _ fb fr wd wr fl w i j flush dq s sr so cs room with "Hwin Hs Hcs HK");
        try assumption; try lia; try unfold wf_checked, wf_input; repeat split; lookups; unwrap2; reflexivity.
Qed.

Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI___woverflow" woverflow_fn, !Defines ge "__GI__IO_wdefault_xsputn" wdefault_xsputn_fn}
  (Hov : woverflow_spec vb self E woverflow_fn).

Definition wf_after_copy fb dq s sr so cs Φ : iProp Σ := ∀ e left flush,
  ⌜wf_finish_regs e fb (size cs) flush /\ reg e "pr.5" (WInt left) /\ 0 <= left <= size cs /\ (flush = 0 \/ flush = 1)⌝ -∗
  file_wide ge vb self (obj fb) 1 -∗ E -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗ WP (at_block e "L172") {{ Φ }}.

Local Lemma wf_suffix e fb dq s sr so cs k flush Φ :
  size cs <= 128 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  0 <= k <= size cs -> wf_finish_regs e fb (size cs) flush -> reg e "pr.4" (WInt (size cs-k)) ->
  reg e "pr.1" (WPtr (p s (so+4*k))) -> (flush = 0 \/ flush = 1) ->
  file_wide ge vb self (obj fb) 1 -∗ E -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wf_after_copy fb dq s sr so cs Φ -∗ WP (at_block e "L112") {{ Φ }}.
Proof using Type*.
  intros N V Hs Hsa Hso Hse Hsr R (Hfp & Hn & Hck & H6) H4 H1 Hflush.
  iIntros "HF HE Hs Hcs HK". body_start wprintf_xsputn_fn "L112"%string. step.
  destruct (Z.eq_dec (size cs-k) 0) as [Hz|Hnz].
  - branch_symbolic. unwrap2. rewrite Hz. cbn. step. iApply ("HK" $! _ (size cs-k) flush with "[%] HF HE Hs Hcs").
    unfold wf_finish_regs. split_and!; try assumption; try lia; lookups; unwrap2; reflexivity.
  - branch_symbolic. unwrap2. rewrite (proj2 (Z.ltb_lt 0 (size cs-k)) ltac:(lia)). cbn [edge_label]. step.
    set (a := Z.to_nat k). set (ys := drop a cs).
    assert (L : size ys = size cs-k) by (unfold ys; rewrite length_drop; unfold a; lia).
    assert (Vy : Forall (fun c => 0 <= c < 2^32) ys) by (apply Forall_drop; done).
    iDestruct (wchar_sub dq s so cs a (length ys) with "Hcs") as "[Hy Hback]"; [unfold a; lia|].
    fold ys. rewrite take_ge; [|lia]. replace (Z.of_nat a) with k by (unfold a; lia).
    iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext. norm. rewrite <- L.
    iApply (wp_wdefault_xsputn Hmove Hfn Hsym vb self E Hov _ (obj fb) dq s sr (so+4*k) ys with "HF HE Hs Hy"); try assumption; try lia; [reflexivity|].
    iNext. iIntros (r Hr) "HF HE Hs Hy". iDestruct ("Hback" with "Hy") as "Hcs". resume. do 3 step.
    iApply ("HK" $! _ (size cs-k-r) flush with "[%] HF HE Hs Hcs").
    unfold wf_finish_regs. split_and!; try assumption; try lia; lookups; unwrap2; reflexivity.
Qed.

(** After choosing the room and copying the prefix, the file writer
    lends the default writer just the suffix. It recovers the entire
    input before it tests whether to flush the stream. *)
Lemma wp_wfile_copy_input e fb dq s sr so cs Φ :
  0 < size cs <= 128 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  wf_input e fb s so (size cs) ->
  file_wide ge vb self (obj fb) 1 -∗ E -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wf_after_copy fb dq s sr so cs Φ -∗ WP (at_block e "L14") {{ Φ }}.
Proof using Type*.
  intros N V Hs Hsa Hso Hse Hsr G. iIntros "HF HE Hs Hcs HK".
  iDestruct (wide_write_window with "HF") as (fb' fr wd wr fl w i j
    (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & Hfl & B & Hi & Hj)) "[Hwin Hclose]".
  injection Eq as <-. iApply (wp_wfile_select with "Hwin Hs Hcs [-]"); try assumption.
  iIntros (ee count flush (G' & Hcount & H6 & R & Hflush)) "Hwin Hs Hcs".
  iApply (wf_count _ fb fr wd wr fl w i j flush dq s sr so cs count with "Hwin Hs Hcs [-]"); try assumption.
  iIntros (ee' i' k (Ri & Rk & G'' & H4 & H1)) "Hwin Hs Hcs".
  iDestruct ("Hclose" with "[%] Hwin") as "HF"; [exact Ri|].
  iApply (wf_suffix _ fb dq s sr so cs k flush with "HF HE Hs Hcs HK"); try assumption; lia.
Qed.
End remainder.

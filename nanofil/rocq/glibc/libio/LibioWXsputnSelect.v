(** The file writer uses all the room up to the physical buffer end
    when a line-buffered stream is putting. If the whole input fits,
    it scans for the last newline and may stop there for a flush. On
    other streams it copies only up to the current write end. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioWIdle
  LibioDefaultXsputnBuf LibioWXsputnRoom LibioWXsputnWindow LibioWXsputnScan WideWriteSpec WideBytes CBlocks.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation p b o := (mkPtr (b+o) (Obj b)).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Definition wf_input e fb s so n := reg e "v0" (WPtr (obj fb)) /\ reg e "v2" (WPtr (p s so)) /\ reg e "v4" (WInt n).
Definition wf_checked e fb s so n := wf_input e fb s so n /\ reg e "chk0" (WPtr (obj fb)).

Section choose.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_block e l := (ERun (mkFrame wprintf_xsputn_fn e [] None (body_at wprintf_xsputn_fn l)) : sexpr).

Definition wf_selected fb fr wd wr fl w i j dq s sr so cs Φ : iProp Σ := ∀ ee count flush,
  ⌜wf_checked ee fb s so (size cs) /\ reg ee "pr.10" (WInt count) /\ reg ee "pr.6" (WInt flush) /\
    0 <= count <= window_size w-i /\ (flush = 0 \/ flush = 1)⌝ -∗
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗ WP (at_block ee "L20") {{ Φ }}.

Local Ltac open_window := iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
Local Ltac close_window := rewrite /write_window; iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hshort Hb".
Local Ltac read_pair field := load "Hf" "Hwd" "Hl"; step; check "Hl"; load_wpos "Hl" field "Hb";
  load "Hf" "Hwd" "Hl"; step; check "Hl"; load_wpos "Hl" "Hcur" "Hb"; do 2 step.

(** Both room counts come from a byte difference divided by four. The
    subtraction is nonnegative on the branches that use it. *)
Local Lemma positive_room b i j : 0 <= b -> 0 <= i <= j -> b+4*j <= 2^63 -> 4*j < 2^63 ->
  (if sign_extension (2^64) (2^63) (4 mod 2^64) =? 0 then 0 else
    (sign_extension (2^64) (2^63) ((((b+4*j) mod 2^64 - (b+4*i) mod 2^64) mod 2^64) mod 2^64)
     ÷ sign_extension (2^64) (2^63) (4 mod 2^64)) mod 2^64) = j-i.
Proof using Type.
  intros. change (sign_extension (2^64) (2^63) (4 mod 2^64)) with 4. change (4 =? 0) with false. cbn iota.
  rewrite (Z.mod_small (b+4*j) (2^64)); [|lia]. rewrite (Z.mod_small (b+4*i) (2^64)); [|lia].
  rewrite Z.mod_mod; [|lia]. replace (b+4*j-(b+4*i)) with ((j-i)*4) by lia.
  rewrite wpos_signed; [|lia]. rewrite Z.quot_mul; [|lia]. apply Z.mod_small. lia.
Qed.

Local Lemma wf_line_room e fb fr wd wr fl w i j dq s sr so cs Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i <= window_size w -> 0 < s -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  Forall (fun c => 0 <= c < 2^32) cs -> wf_checked e fb s so (size cs) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wf_selected fb fr wd wr fl w i j dq s sr so cs Φ -∗ WP (at_block e "L18") {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hs Hso Hse Hsr V ((Hfp & Hp & Hn) & Hck).
  iIntros "Hwin Hs Hcs HK". open_window. body_start wprintf_xsputn_fn "L18"%string. step. check "Hf".
  read_pair "Hstop". step. step_named.
  pose proof (wpos_bounds wd w (window_size w) Hwd ltac:(lia) B ltac:(lia)) as (Hb & Hmax & C). cbn [wpos ptr_addr] in Hmax.
  rewrite positive_room in E; [|lia..]. subst x. step. destruct (Z_le_gt_dec (size cs) (window_size w-i)) as [Fits|Miss].
  - branch_as false. do 5 step.
    iApply (wp_wfile_xsputn_scan dq s sr so cs (window_size w-i) Hs Hso Hse Hsr V ltac:(lia) $! _ (size cs) Φ with "[%] Hs Hcs").
    + split_and!; try lia; lookups; cbn [ptr_addr ptr_cap]; unwrap2; try reflexivity; change (2^(2 mod 64)) with 4; unwrap2; do 3 f_equal; lia.
    + iIntros (ee count flush (Same & Hcount & Hflush & Res)) "Hs Hcs". iApply ("HK" $! ee count flush with "[%] [-Hs Hcs] Hs Hcs"); [|close_window].
      unfold wf_checked, wf_input. split_and!; try assumption; try lia; (rewrite Same; [lookups; reflexivity|done]).
  - branch_symbolic. assert (Lcs : size cs < 2^63) by lia. unwrap2.
    rewrite (proj2 (Z.leb_gt (size cs) (window_size w-i)) ltac:(lia)). cbn [edge_label]. step.
    iApply ("HK" $! _ (window_size w-i) 0 with "[%] [-Hs Hcs] Hs Hcs"); [|close_window].
    unfold wf_checked, wf_input. split_and!; try lia; lookups; unwrap2; reflexivity.
Qed.

Local Lemma wf_other_room e fb fr wd wr fl w i j dq s sr so cs Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i <= window_size w -> 0 <= j <= window_size w -> wf_checked e fb s so (size cs) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wf_selected fb fr wd wr fl w i j dq s sr so cs Φ -∗ WP (at_block e "L19") {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hj ((Hfp & Hp & Hn) & Hck).
  iIntros "Hwin Hs Hcs HK". open_window. body_start wprintf_xsputn_fn "L19"%string. step. check "Hf". read_pair "Hend". step.
  pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hi) as (Hb & Ai & C).
  pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hj) as (_ & Aj & _). cbn [wpos ptr_addr] in Ai, Aj.
  destruct (Z_lt_le_dec i j) as [Hlt|Hle].
  - branch_as false. step. step. read_pair "Hend". step. step_named. rewrite positive_room in E; [|lia..]. subst x.
    step. step. iApply ("HK" $! _ (j-i) 0 with "[%] [-Hs Hcs] Hs Hcs"); [|close_window].
    unfold wf_checked, wf_input. split_and!; try lia; lookups; unwrap2; reflexivity.
  - branch_as true. step. iApply ("HK" $! _ 0 0 with "[%] [-Hs Hcs] Hs Hcs"); [|close_window].
    unfold wf_checked, wf_input. split_and!; try lia; lookups; reflexivity.
Qed.

(** The flag tests choose between the physical room and the logical
    write end. Both branches return a count that fits in the physical
    buffer before the writer takes the smaller of that count and the
    input length. *)
Lemma wp_wfile_select e fb fr wd wr fl w i j dq s sr so cs Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i <= window_size w -> 0 <= j <= window_size w ->
  0 < s -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 -> Forall (fun c => 0 <= c < 2^32) cs ->
  wf_input e fb s so (size cs) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wf_selected fb fr wd wr fl w i j dq s sr so cs Φ -∗ WP (at_block e "L14") {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hj Hs Hso Hse Hsr V (Hfp & Hp & Hn).
  iIntros "Hwin Hs Hcs HK".
  iAssert (∀ ee d, ⌜wf_checked ee fb s so (size cs) /\ reg ee "v30" (WInt d)⌝ -∗
    write_window fb fr wd wr fl w i j -∗ WP (at_block ee "L25") {{ Φ }})%I with "[Hs Hcs HK]" as "Hjoin".
  { iIntros (ee d [G Hd]) "Hwin". body_start wprintf_xsputn_fn "L25"%string. branch_cases; step.
    - iApply (wf_other_room with "Hwin Hs Hcs HK"); assumption.
    - iApply (wf_line_room with "Hwin Hs Hcs HK"); assumption. }
  open_window. iDestruct "Hfl" as "[%F Hfl]". body_start wprintf_xsputn_fn "L14"%string. check "Hf". load_s32 "Hf" "Hfl". step.
  branch_cases; step; [|load_s32 "Hf" "Hfl"; do 4 step]; (iApply ("Hjoin" with "[%] [-]");
    [unfold wf_checked, wf_input; split_and!; lookups; unwrap2; reflexivity|rewrite /write_window /int_cell; iFrame; done]).
Qed.
End choose.

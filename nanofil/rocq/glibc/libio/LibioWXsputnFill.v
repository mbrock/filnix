(** A counted copy changes the bytes under the wide write pointer but
    not the surrounding storage. A short copy can target the stream's
    one-character buffer or a heap allocation. A copy of more than
    twenty characters always targets a heap allocation. *)

From Glibc Require Import Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import Fix OsWorld OsRegistry FileInv LibioLogic LibioWIdle
  LibioDefaultXsputnBuf BufferCopy CBlocks WideBytes WideWriteSpec
  LibioWXsputnWindow LibioWXsputnWords LibioWXsputnCopy.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Abbreviation okbyte := (fun x : Z => 0 <= x < 256).

Section fill.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The word loop replaces only the borrowed interval. Replacing that
    interval with the same number of valid bytes leaves the allocation
    at its original length. *)
Lemma lend_bytes b o xs k n : (k+n <= length xs)%nat -> Forall okbyte xs ->
  bytes b o xs -∗ ∃ old, ⌜length old = n⌝ ∗ bytes b (o+Z.of_nat k) old ∗
  (∀ ys, ⌜length ys = n /\ Forall okbyte ys⌝ -∗ bytes b (o+Z.of_nat k) ys -∗
     ∃ xs', ⌜length xs' = length xs /\ Forall okbyte xs'⌝ ∗ bytes b o xs').
Proof using Type.
  intros H V. iIntros "H". iDestruct (bytes_take_drop _ _ _ k with "H") as "[Hp H]"; [lia|].
  iDestruct (bytes_take_drop _ _ _ n with "H") as "[Hx Hs]"; [rewrite length_drop; lia|].
  iExists (take n (drop k xs)). iSplit; [iPureIntro; rewrite length_take_le; [done|rewrite length_drop; lia]|].
  iFrame "Hx". iIntros (ys [Ly Vy]) "Hy". iExists (take k xs ++ ys ++ drop n (drop k xs))%list.
  iSplit; [iPureIntro; split; [rewrite !length_app length_take_le ?length_drop; lia|
    rewrite !Forall_app; repeat split; auto using Forall_take, Forall_drop]|].
  rewrite !bytes_app length_take_le; [|lia]. rewrite Ly. iFrame.
Qed.

(** Both writers copy a short string one character at a time. They move
    the stream's write pointer only after copying the last character. *)
Lemma wp_wxsputn_fill_words (file : bool) fb fr wd wr fl w i j e dq s sr so cs Φ :
  let fn := if file then wprintf_xsputn_fn else wdefault_xsputn_fn in
  let head := if file then "L151" else "L81" in let exit := if file then "L153" else "L84" in
  let nr := TAtom (if file then "pr.16" else "pr.13") in let dst := TAtom (if file then "pr.15" else "pr.12") in
  let src := TAtom (if file then "pr.3" else "pr.6") in
  0 < wd -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> 0 <= i -> i+size cs <= window_size w ->
  0 < s -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  0 < size cs <= 20 -> Forall (fun c => 0 <= c < 2^32) cs ->
  lookup nr e = Some (WInt (size cs)) -> lookup dst e = Some (WPtr (wpos wd w i)) ->
  lookup src e = Some (WPtr (mkPtr (s+so) (Obj s))) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  (∀ e', ⌜same_out (wcopy_names file) e e' /\ lookup dst e' = Some (WPtr (wpos wd w (i+size cs))) /\
    lookup src e' = Some (WPtr (mkPtr (s+(so+4*size cs)) (Obj s)))⌝ -∗
    write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
    WP (ERun (mkFrame fn e' [] None (Enter (TAtom exit) (Some (TAtom head)))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame fn e [] None (body_at fn head)) : sexpr) {{ Φ }}.
Proof using Type.
  cbv zeta. intros Hwd Hwe Hwr Hi Hfit Hs Hso Hse Hsr Hn V Hcnt Hd Hp.
  iIntros "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hbuf) Hs Hcs HK".
  destruct w as [| |b sz]; cbn [window_size] in Hfit; [lia| |].
  - assert (i = 0) as -> by lia. assert (size cs = 1) as L by lia.
    iDestruct "Hshort" as (sb [Lsb Vsb]) "Hsb".
    iApply (wp_wxsputn_words file wd wr dq s sr cs Φ Hwd Hwr Hs Hsr woff_shortbuf so sb e with "Hl Hsb Hs Hcs");
      try assumption; try (unfold woff_shortbuf; lia).
    { rewrite Hd. unfold wpos, window_base, woff_shortbuf. cbn [ptr_addr ptr_cap]. do 3 f_equal; lia. }
    iIntros (ee (Hs1 & Hd1 & Hp1)) "Hl Hsb Hs Hcs". iApply ("HK" $! ee with "[%] [-Hs Hcs] Hs Hcs").
    + split; [done|]. rewrite Hp1 Hd1. split; [|done]. unfold wpos, window_base, woff_shortbuf.
      cbn [ptr_addr ptr_cap]. do 3 f_equal; lia.
    + rewrite /write_window. iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hbuf". iExists (stage_bytes cs).
      iFrame "Hsb". iPureIntro. split; [rewrite stage_bytes_length; lia|apply stage_bytes_valid].
  - iDestruct "Hbuf" as (br xs caps (Hkind & He & Hr & Hb & Hba & Hsz & Hmod & L & Vx & Lc)) "(Hb & Hxs & Ha)".
    set (k := Z.to_nat (4*i)). assert (K : Z.of_nat k = 4*i) by (unfold k; lia).
    pose proof (Z.div_mod sz 4 ltac:(lia)).
    iDestruct (lend_bytes b 0 xs k (4*length cs) with "Hxs") as (old Lo) "[Hx Hback]"; [lia|done|].
    iEval (rewrite Z.add_0_l K) in "Hx".
    iApply (wp_wxsputn_words file b br dq s sr cs Φ Hb Hr Hs Hsr (4*i) so old e with "Hb Hx Hs Hcs"); try assumption; try lia.
    iIntros (ee (Hs1 & Hd1 & Hp1)) "Hb Hx Hs Hcs".
    iDestruct ("Hback" $! (stage_bytes cs) with "[%] [Hx]") as (xs' [L' V']) "Hxs".
    + split; [apply stage_bytes_length|apply stage_bytes_valid].
    + by rewrite Z.add_0_l K.
    + iApply ("HK" $! ee with "[%] [-Hs Hcs] Hs Hcs").
      * split; [done|]. rewrite Hp1 Hd1. split; [|done]. unfold wpos, window_base. cbn [ptr_addr ptr_cap]. do 3 f_equal; lia.
      * rewrite /write_window. iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hshort".
        iExists br, xs', caps. iFrame. iPureIntro. split_and!; (assumption || lia).
Qed.

Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hfn : find_fn ge (TAtom "zmemmove") = None) (Hsym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Context `{!Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy}.

(** A bulk copy also leaves the old cursor cell intact. Its return
    value points just past the copied characters, including when the
    copy fills the last slot of the allocation. *)
Lemma wp_wxsputn_fill_bulk frame fb fr wd wr fl w i j dq s sr so cs Φ :
  call_frame wmempcpy_fn [WPtr (wpos wd w i); WPtr (mkPtr (s+so) (Obj s)); WInt (size cs)] = Some frame ->
  0 <= i -> i+size cs <= window_size w -> 20 < size cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  ▷ (write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
     Φ (Ret (WPtr (wpos wd w (i+size cs))))) -∗ WP (ERun frame : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hcall Hi Hfit Hn Hs Hsa Hso Hse Hsr. destruct w as [| |b sz]; cbn [window_size] in Hfit; try lia.
  iIntros "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hbuf) Hs Hcs HK".
  iDestruct "Hbuf" as (br xs caps (Hkind & He & Hr & Hb & Hba & Hsz & Hmod & L & Vx & Lc)) "(Hb & Hxs & Ha)".
  pose proof (Z.div_mod sz 4 ltac:(lia)).
  iApply (wp_wmempcpy Hmove Hfn Hsym _ b br (4*i) xs caps dq s sr so cs with "Hb Hxs Ha Hs Hcs"); try assumption; try lia.
  iNext. iIntros "Hb (%xs' & %caps' & (%L' & %Lc' & %V') & Hxs & Ha) Hs Hcs".
  replace (b+4*i+4*size cs) with (b+4*(i+size cs)) by lia. iApply ("HK" with "[-Hs Hcs] Hs Hcs").
  rewrite /write_window. iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hshort".
  iExists br, xs', caps'. iFrame. iPureIntro. split_and!; (assumption || lia).
Qed.
End fill.

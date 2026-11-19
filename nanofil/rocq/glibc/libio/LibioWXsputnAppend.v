(** Both wide writers advance the stream and the source by the number
    of characters copied. The scalar loop leaves the two new pointers
    in registers. The bulk path takes the new destination from
    `c: __wmempcpy` and computes the new source from the count. *)

From Glibc Require Import Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioDefaultXsputnBuf LibioWXsputnWords LibioWXsputnRoom LibioWXsputnWindow LibioWXsputnFill
  WPrintfFileFlush WPrintfDispatch LibioWXsputnCopy CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation p b o := (mkPtr (b+o) (Obj b)).
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Abbreviation fn file := (if (file : bool) then wprintf_xsputn_fn else wdefault_xsputn_fn).

Definition append_regs (file : bool) e fb n k saved :=
  reg e "v0" (WPtr (obj fb)) /\ reg e "v4" (WInt n) /\ reg e "pr.9" (WInt k) /\
  reg e "chk0" (WPtr (if file then obj fb else p fb 160)) /\ reg e (if file then "pr.6" else "pr.7") (WInt saved).

Section append.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

Definition append_next (file : bool) fb fr wd wr fl w i j n saved dq s sr so cs Φ : iProp Σ :=
  ∀ e, ⌜append_regs file e fb n (size cs) saved /\
    reg e (if file then "pr.2" else "pr.4") (WPtr (p s (so+4*size cs))) /\
    (file = false -> reg e "pr.10" (WInt (size cs)))⌝ -∗
  write_window fb fr wd wr fl w (i+size cs) j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  WP (ERun (mkFrame (fn file) e [] None (body_at (fn file) (if file then "L124" else "L49"))) : sexpr) {{ Φ }}.

Local Ltac open_window := iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
Local Ltac close_window := rewrite /write_window; iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hshort Hb".

Lemma wp_wxsputn_append_small (file : bool) e fb fr wd wr fl w i j n saved dq s sr so cs Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i -> i+size cs <= window_size w -> 0 < size cs <= 20 -> Forall (fun c => 0 <= c < 2^32) cs ->
  0 < s -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  append_regs file e fb n (size cs) saved -> reg e (if file then "v2" else "pr.2") (WPtr (p s so)) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  append_next file fb fr wd wr fl w i j n saved dq s sr so cs Φ -∗
  WP (ERun (mkFrame (fn file) e [] None (body_at (fn file) (if file then "L123" else "L69"))) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hfit Hn V Hs Hso Hse Hsr (Hfp & Hcnt & Hk & Hck & Hsav) Hp.
  iIntros "Hwin Hs Hcs HK". open_window. destruct file; cbn in Hck, Hsav, Hp.
  - body_start wprintf_xsputn_fn "L123"%string. step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl".
    load_wpos "Hl" "Hcur" "Hb". step. step.
    iApply (wp_wxsputn_fill_words true fb fr wd wr fl w i j _ dq s sr so cs with "[-Hs Hcs HK] Hs Hcs");
      try assumption; try lia; try solve [lookups; unwrap2; reflexivity]; [close_window|].
    iIntros (ee (Hs1 & Hd & Hsrc)) "Hwin Hs Hcs". cbn in Hd, Hsrc. open_window.
    assert (Hfp' : reg ee "v0" (WPtr (obj fb))) by (rewrite Hs1; [by lookups|done]).
    assert (Hc' : reg ee "chk19" (WPtr (p fb 160))) by (rewrite Hs1; [lookups; unwrap2; done|done]).
    step. step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". store "Hl" "Hcur". step. step.
    iApply ("HK" with "[%] [-Hs Hcs] Hs Hcs"); [|close_window].
    unfold append_regs. split_and!; try discriminate; lookups; try reflexivity; (rewrite Hs1; [by lookups|done]).
  - body_start wdefault_xsputn_fn "L69"%string. step. load "Hf" "Hwd" "Hl". step. check "Hl".
    load_wpos "Hl" "Hcur" "Hb". step. step.
    iApply (wp_wxsputn_fill_words false fb fr wd wr fl w i j _ dq s sr so cs with "[-Hs Hcs HK] Hs Hcs");
      try assumption; try lia; try solve [lookups; unwrap2; reflexivity]; [close_window|].
    iIntros (ee (Hs1 & Hd & Hsrc)) "Hwin Hs Hcs". cbn in Hd, Hsrc. open_window.
    assert (Hfp' : reg ee "v0" (WPtr (obj fb))) by (rewrite Hs1; [by lookups|done]).
    assert (Hc' : reg ee "chk0" (WPtr (p fb 160))) by (rewrite Hs1; [by lookups|done]).
    assert (Hk' : reg ee "pr.9" (WInt (size cs))) by (rewrite Hs1; [by lookups|done]).
    step. step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". store "Hl" "Hcur". step. step.
    iApply ("HK" with "[%] [-Hs Hcs] Hs Hcs"); [|close_window].
    unfold append_regs. split_and!; intros; lookups; unwrap2; try reflexivity; (rewrite Hs1; [by lookups|done]).
Qed.

Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hfn : find_fn ge (TAtom "zmemmove") = None) (Hsym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Context `{!Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
  !Defines ge "__wmempcpy" wmempcpy_fn}.

Lemma wp_wxsputn_append_bulk (file : bool) e fb fr wd wr fl w i j n saved dq s sr so cs Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i -> i+size cs <= window_size w -> 20 < size cs ->
  0 < s -> s mod 8 = 0 -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 ->
  append_regs file e fb n (size cs) saved -> reg e (if file then "v2" else "pr.2") (WPtr (p s so)) ->
  write_window fb fr wd wr fl w i j -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  append_next file fb fr wd wr fl w i j n saved dq s sr so cs Φ -∗
  WP (ERun (mkFrame (fn file) e [] None (body_at (fn file) (if file then "L122" else "L47"))) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hfit Hn Hs Hsa Hso Hse Hsr (Hfp & Hcnt & Hk & Hck & Hsav) Hp.
  iIntros "Hwin Hs Hcs HK". open_window. destruct file; cbn in Hck, Hsav, Hp;
    [body_start wprintf_xsputn_fn "L122"%string; step; check "Hf"|body_start wdefault_xsputn_fn "L47"%string; step];
    load "Hf" "Hwd" "Hl"; step; load "Hf" "Hwd" "Hl"; step; check "Hl"; load_wpos "Hl" "Hcur" "Hb";
    (iApply wp_call_bind; [vx|apply defines|reflexivity|]); iNext; norm; unwrap2.
  all: iApply (wp_wxsputn_fill_bulk Hmove Hfn Hsym _ fb fr wd wr fl w i j dq s sr so cs with "[-Hs Hcs HK] Hs Hcs");
    try assumption; try reflexivity; try lia; [close_window|].
  all: iNext; iIntros "Hwin Hs Hcs"; resume; open_window; check "Hl"; store "Hl" "Hcur"; do 4 step;
    iApply ("HK" with "[%] [-Hs Hcs] Hs Hcs"); [|close_window].
  all: unfold append_regs; split_and!; intros; try discriminate; lookups; cbn [ptr_addr ptr_cap]; unwrap2; try reflexivity;
    change (2^(2 mod 64)) with 4; unwrap2; do 3 f_equal; lia.
Qed.
End append.

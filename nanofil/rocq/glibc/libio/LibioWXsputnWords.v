(** Both wide stream writers copy up to twenty characters with a loop
    instead of calling wmempcpy. The file writer counts down in a 32-bit
    register and the default writer uses a 64-bit register. In both loops
    a zero count exits before the next load or store. *)

From Glibc Require Import HelloImageTypedIO.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld FileInv LibioLogic LibioCloseSteps
  LibioDefaultXsputnBuf CBlocks WPrintfFileFlush WPrintfDispatch.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Abbreviation at_off b o := (mkPtr (b+o) (Obj b)).

Definition wdefault_xsputn_fn := hello_image_fn___GI__IO_wdefault_xsputn.

Definition wcopy_names (file : bool) := map TAtom (if file then
  ["pr.16"; "pr.15"; "pr.3"; "v155"; "v156"; "v158"; "v160"; "chk21"; "v161"; "chk22"] else
  ["pr.13"; "pr.12"; "pr.6"; "v86"; "v87"; "v89"; "v91"; "chk10"; "v92"; "chk11"]).

Section words.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The loop needs only the destination bytes it will replace. That
    range can be inside the stream's wide data object for a short
    buffer or inside a separate heap allocation. Both cursors advance
    by the same byte count, and the source loan comes back unchanged. *)
Lemma wp_wxsputn_words (file : bool) b br dq s sr cs Φ :
  let fn := if file then wprintf_xsputn_fn else wdefault_xsputn_fn in
  let head := if file then "L151" else "L81" in let exit := if file then "L153" else "L84" in
  let nr := TAtom (if file then "pr.16" else "pr.13") in let dst := TAtom (if file then "pr.15" else "pr.12") in
  let src := TAtom (if file then "pr.3" else "pr.6") in
  0 < b -> r_end br <= 2^63 -> 0 < s -> r_end sr <= 2^63 ->
  forall o so bs e, 0 <= o -> b+o+4*size cs <= r_end br -> 0 <= so -> s+so+4*size cs <= r_end sr ->
  size cs <= 20 -> Forall (fun c => 0 <= c < 2^32) cs -> length bs = (4*length cs)%nat ->
  lookup nr e = Some (WInt (size cs)) -> lookup dst e = Some (WPtr (at_off b o)) -> lookup src e = Some (WPtr (at_off s so)) ->
  live b br -∗ bytes b o bs -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  (∀ e', ⌜same_out (wcopy_names file) e e' /\ lookup dst e' = Some (WPtr (at_off b (o+4*size cs))) /\
      lookup src e' = Some (WPtr (at_off s (so+4*size cs)))⌝ -∗
    live b br -∗ bytes b o (stage_bytes cs) -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
    WP (ERun (mkFrame fn e' [] None (Enter (TAtom exit) (Some (TAtom head)))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame fn e [] None (body_at fn head)) : sexpr) {{ Φ }}.
Proof using Type.
  cbv zeta. intros Hb Hr Hs Hsr. induction cs as [|c cs IH]; intros o so bs e Ho He Hso Hse Hn V L Hcnt Hdst Hsrc;
    iIntros "Hl Hbs Hs Hcs HK".
  - destruct bs; [|discriminate]. change (size (@nil Z)) with 0 in *. rewrite !Z.mul_0_r !Z.add_0_r.
    destruct file; cbn in Hcnt, Hdst, Hsrc; [body_start wprintf_xsputn_fn "L151"%string|body_start wdefault_xsputn_fn "L81"%string];
      do 2 step; branch_as true; iApply ("HK" with "[%] Hl Hbs Hs Hcs"); (split; [same_tac|split; by lookups]).
  - inversion V as [|? ? Vc Vcs]; subst. cbn beta in Vc.
    assert (Hcount : size (c::cs) = 1 + size cs) by (cbn [length]; lia). rewrite Hcount in Hcnt, He, Hse, Hn |- *.
    assert (L4 : length (take 4 bs) = 4%nat) by (rewrite length_take; simpl in L; lia).
    iDestruct (bytes_take_drop _ _ _ 4 with "Hbs") as "[Hc Hbtl]"; [simpl in L; lia|].
    change (stage_bytes (c::cs)) with (le_bytes c 4 ++ stage_bytes cs)%list.
    iEval (rewrite /bytesq StringLogic.byte_ps_app ptsq_app length_le_bytes) in "Hcs". iDestruct "Hcs" as "[Hx Hstl]".
    destruct file; cbn in Hcnt, Hdst, Hsrc; [body_start wprintf_xsputn_fn "L151"%string|body_start wdefault_xsputn_fn "L81"%string];
      do 2 step; branch_as false; do 3 step; check_read_dq "Hs" by a2; iNext; iIntros "Hs";
      load_bytes_dq "Hs Hx" decode (apply load_sw_int; assumption) by a2; iNext; iIntros "Hs Hx"; check "Hl".
    all: iApply (wp_raw_store_w with "Hl Hc"); [vx|vx|reflexivity|a2|exact L4|wi_store|].
    all: iNext; iIntros "Hl Hc"; iEval (rewrite (Z.mod_small c (2^32) Vc)) in "Hc"; do 2 step;
      iApply (IH (o+4) (so+4) (drop 4 bs) _ with "Hl Hbtl Hs Hstl [Hc Hx HK]"); try assumption; try lia;
      try (rewrite length_drop; simpl in L; lia); try solve [lookups; cbn [ptr_addr ptr_cap]; unwrap2; rewrite ?Z.add_assoc; repeat f_equal; lia].
    all: iIntros (ee (Hsame & Hd & Hs1)) "Hl Hd Hs Htl"; iApply ("HK" $! ee with "[%] Hl [Hc Hd] Hs [Hx Htl]");
      [|rewrite bytes_app length_le_bytes; iFrame|rewrite /bytesq StringLogic.byte_ps_app ptsq_app length_le_bytes; iFrame].
    all: split; [eapply same_out_trans; [|exact Hsame]; same_tac|rewrite Hd Hs1; split; do 3 f_equal; lia].
Qed.
End words.

(** The default wide writer subtracts its write pointer from its write
    end and tests the signed result. A line-buffered stream may have
    passed that end without reaching the end of its allocation. The
    writer treats a negative difference as no room and calls overflow. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioPutsInv LibioCloseSteps LibioWIdle
  LibioWXsputnWindow LibioWXsputnWords LibioWXsputnTail CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).

Lemma wpos_bounds wd w i : 0 < wd -> wd+232 <= 2^63 -> window_bound w -> 0 <= i <= window_size w ->
  0 <= ptr_addr (window_base wd w) /\ 0 <= ptr_addr (wpos wd w i) <= 2^63 /\ 4*window_size w < 2^63.
Proof.
  intros Hwd He B R. destruct w; cbn [window_size window_bound] in *;
    cbn [window_base wpos ptr_addr null]; try lia. destruct B as (Hb & Hsz & Hmod & Hend).
  pose proof (Z.div_mod wsz 4 ltac:(lia)). cbn [window_size]. lia.
Qed.

Lemma wpos_signed x : -2^63 <= x < 2^63 -> sign_extension (2^64) (2^63) (x mod 2^64) = x.
Proof. intros R. unfold sign_extension. rewrite Z.mod_mod; [|lia]. destruct (Z_lt_le_dec x 0).
  - replace (x mod 2^64) with (x+2^64) by (apply Z.mod_unique with (-1); lia).
    destruct (Z.leb_spec (2^63) (x+2^64)); lia.
  - rewrite Z.mod_small; [|lia]. destruct (Z.leb_spec (2^63) x); lia.
Qed.

Section room.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** Loading a wide cursor needs the life of its target. A short buffer
    shares the wide data object's life, and a heap buffer has its own.
    A null cursor needs no target life. *)
Lemma wp_load_wpos f e ls l d off args rest j classes p wd wr o w i Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj wd -> raw_address (ptr_addr p) off = wd+o -> (wd+o) mod 8 = 0 ->
  0 < wd -> wd+232 <= 2^63 -> window_bound w -> 0 <= i <= window_size w ->
  live wd wr -∗ pcell wd o (wpos wd w i) -∗ wbuf_idle w -∗
  ▷ (live wd wr -∗ pcell wd o (wpos wd w i) -∗ wbuf_idle w -∗
    WP (ERun (mkFrame f (put d (WPtr (wpos wd w i)) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros C A T O Al Hwd He B R. pose proof (wpos_bounds _ _ _ Hwd He B R) as (_ & Range & _).
  iIntros "Hl Hc Hb HK". destruct w as [| |b sz].
  - assert (i=0) as -> by (cbn [window_size] in R; lia).
    iApply (wp_raw_load_null with "Hl Hc"); [exact C|exact A|done|done|done|]. iNext. iIntros "Hl Hc". by iApply ("HK" with "Hl Hc Hb").
  - iApply (wp_raw_load_pointer_self with "Hl Hc"); [exact C|exact A|done|done|done|lia|done|].
    iNext. iIntros "Hl Hc". by iApply ("HK" with "Hl Hc Hb").
  - iDestruct "Hb" as (br xs cs H) "(Hb & Hx & Ha)". iApply (wp_raw_load_pointer with "Hl Hc Hb"); [exact C|exact A|done|done|done|lia|].
    iNext. iIntros "Hl Hc Hb". iApply ("HK" with "Hl Hc [-]"). iExists br, xs, cs. by iFrame.
Qed.
End room.

Ltac load_wpos Hl Hc Hb :=
  rule3 Hl Hc Hb ltac:(eapply wp_load_wpos; inst; [reflexivity|vx|reflexivity|a2|a2|assumption|lia|assumption|lia]).

Section test.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The writer needs no storage bytes to test the two cursors. Its next
    block either skips the copy or receives the number of characters
    between the write pointer and the write end. *)
Lemma wp_wdefault_room e fb fr wd wr fl w i j s so n t Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w ->
  0 <= i <= window_size w -> 0 <= j <= window_size w -> n < 2^63 ->
  wsource_regs e (mkPtr fb (Obj fb)) s so n t "pr.7" "pr.2" ->
  write_window fb fr wd wr fl w i j -∗
  ((∀ e', ⌜wsource_regs e' (mkPtr fb (Obj fb)) s so n t "pr.8" "pr.3"⌝ -∗ write_window fb fr wd wr fl w i j -∗
      WP (ERun (mkFrame wdefault_xsputn_fn e' [] None (body_at wdefault_xsputn_fn "L37")) : sexpr) {{ Φ }}) ∧
  (∀ e', ⌜wsource_regs e' (mkPtr fb (Obj fb)) s so n t "pr.7" "pr.2" /\
      reg e' "chk0" (WPtr (mkPtr (fb+160) (Obj fb))) /\ reg e' "v34" (WInt (j-i)) /\ 0 < j-i⌝ -∗
    write_window fb fr wd wr fl w i j -∗
      WP (ERun (mkFrame wdefault_xsputn_fn e' [] None (body_at wdefault_xsputn_fn "L35")) : sexpr) {{ Φ }})) -∗
    WP (ERun (mkFrame wdefault_xsputn_fn e [] None (body_at wdefault_xsputn_fn "L16")) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hi Hj Hn (Hfp & Hcnt & Ht & Hsrc & R).
  iIntros "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb) HKs".
  body_start wdefault_xsputn_fn "L16"%string. step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl".
  load_wpos "Hl" "Hend" "Hb". load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hcur" "Hb".
  do 3 step. step_named. step_named.
  pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hi) as (Ba & Ai & Cap).
  pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hj) as (_ & Aj & _). cbn [wpos ptr_addr] in Ai, Aj.
  change (sign_extension (2^64) (2^63) (4 mod 2^64)) with 4 in E. change (4 =? 0) with false in E.
  rewrite (Z.mod_small (ptr_addr (window_base wd w)+4*j) (2^64)) in E; [|lia].
  rewrite (Z.mod_small (ptr_addr (window_base wd w)+4*i) (2^64)) in E; [|lia]. rewrite Z.mod_mod in E; [|lia].
  replace (ptr_addr (window_base wd w)+4*j-(ptr_addr (window_base wd w)+4*i)) with ((j-i)*4) in E by lia.
  rewrite wpos_signed in E; [|lia]. rewrite Z.quot_mul in E; [|lia].
  change (sign_extension (2^64) (2^63) (0 mod 2^64)) with 0 in E0. rewrite E Z.mod_mod in E0; [|lia].
  rewrite wpos_signed in E0; [|lia]. destruct (Z.ltb_spec 0 (j-i)); subst x0; branch; step.
  - iDestruct "HKs" as "[_ HK]". iApply ("HK" with "[%] [-]").
    + subst x. unfold wsource_regs. split_and!; try (lookups; cbn [ptr_addr ptr_cap]; unwrap2; reflexivity); lia.
    + rewrite /write_window. by iFrame.
  - iDestruct "HKs" as "[HK0 _]". iApply ("HK0" with "[%] [-]").
    + unfold wsource_regs. split_and!; try (lookups; unwrap2; reflexivity); lia.
    + rewrite /write_window. by iFrame.
Qed.
End test.

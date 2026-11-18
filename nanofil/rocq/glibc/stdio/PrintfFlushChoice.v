(** When printf chooses its next window, the stream may have room for
    more bytes. In that case it lends printf its character buffer. If
    not, the stream takes back all its fields and printf uses its own
    staging array. Both initialization and flushing make this choice. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Machine ExternalCalls ExternalMachine
  Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileTidy LibioFputsSpec AllocRo CStruct LiveApart
  PrintfLayout PrintfOut PrintfSpec PrintfFileOut.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv.
Open Scope Z_scope.

Section choice.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** If the stream has a buffer, its end cannot lie inside the printf
    wrapper. The wrapper owns its whole lifetime, so even a reader's
    share of the other buffer must belong to a different object. *)
Local Lemma wp_choice_apart fr i Φ :
  pbuf_file_live (fi_buf i) (fi_breg i) -∗ fwin_stream i -∗
  (⌜forall c, fi_chars i = Some c -> fc_data c <> fi_buf i /\
     (r_end (fc_reg c) <= fi_buf i \/ r_end (fi_breg i) <= fc_data c)⌝ -∗
   pbuf_file_live (fi_buf i) (fi_breg i) -∗ fwin_stream i -∗ WP (ERun fr : gexpr) {{ Φ }}) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  iIntros "Hbb Hs HK". destruct (fi_chars i) as [c|] eqn:E; last first.
  { iApply ("HK" with "[%] Hbb Hs"). discriminate. }
  struct_live_open "Hbb" as "[%Hbb Hl]". unfold fwin_stream. rewrite E.
  iDestruct "Hs" as "(Hfile & Hwc & %Hc & Hd)".
  iAssert (⌜fc_data c <> fi_buf i⌝)%I as %Hne.
  { iDestruct "Hl" as "[H1 _]". iDestruct "Hd" as "[H2 _]". iDestruct (pointsto_ne with "H1 H2") as %H. iPureIntro. cbn [fst] in H. congruence. }
  iApply (wp_live_apart registry (os_wi w0) ge with "Hl Hd"). iIntros (Ha) "Hl Hd".
  iApply ("HK" with "[%] [Hl] [$Hfile $Hwc $Hd //]"); last by struct_live_close "Hl".
  intros c' H. injection H as <-. specialize (Ha ltac:(congruence)). tauto.
Qed.

(** The window owns the bytes it can fill. The stream owns the rest,
    including any unused part of the staging array. *)
Definition choice_own a bb br w : iProp Σ :=
  ⌜pwin_ok w⌝ ∗ win_live bb br w ∗ win_own (pw_obj w) (pw_lo w) (pw_end w) ∗
  (pbuf_file bb [("fp", VPtr (fo_fp a))] -∗ errno_any (fo_eb a) -∗ fputs_ro (fo_vb a) -∗ malloc_ro -∗
   file_R a bb br (pw_place w)).

(** The caller lends the stream's write fields to the compiled switch.
    Once the switch returns those fields, the caller owns the window it
    selected and can resume formatting. *)
Lemma wp_file_choice fr a bb br Φ :
  pbuf_file_live bb br -∗ win_own bb (bb + stage_off) (bb + stage_end) -∗
  file_tidy (fo_vb a) (fo_self a) (fo_fp a) (fo_fd a) (fo_flags2 a) (fo_held a) -∗
  (∀ freg dq cs, let i := FWinIn bb br (fo_fb a) freg dq cs in
    pbuf_file_live bb br -∗ fwin_stream i -∗ (fwin_stream i -∗ choice_own a bb br (fwin_choice i)) -∗
    WP (ERun fr : gexpr) {{ Φ }}) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  iIntros "Hbb Hstage HF HK". iDestruct (file_tidy_fwin a bb br with "HF") as (freg dq cs) "[Hs Hback]".
  set (i := FWinIn bb br (fo_fb a) freg dq cs). iApply (wp_choice_apart _ i with "Hbb Hs"). iIntros (Ha) "Hbb Hs".
  iAssert (⌜0 < bb /\ bb mod 8 = 0 /\ bb+176 <= r_end br <= 2^63⌝)%I as %Hb. { struct_live_open "Hbb" as "[$ _]". }
  iApply ("HK" $! freg dq cs with "Hbb Hs"). iIntros "Hs". unfold i, fwin_choice. cbn [fi_chars fi_buf fi_breg].
  destruct cs as [c|]; [destruct (Z.ltb_spec (fc_bo c) (fc_eo c)) as [Hroom|Hfull]|].
  { iDestruct "Hback" as "[_ Hd]". iDestruct ("Hd" $! c with "[%] Hs") as "(Hd & Hwin & Hloan)"; [done|].
    specialize (Ha c eq_refl) as [Hne Ha]. unfold i in Hne, Ha. cbn [fi_buf fi_breg] in Hne, Ha.
    iAssert (⌜pwin_ok (data_win (fc_data c) (fc_reg c) (fc_bo c) (fc_eo c))⌝)%I as %Hw.
    { iDestruct "Hloan" as (f st sz H) "_". unfold lent_ok, pwin_ok, data_win, pw_lo in *. cbn [pw_obj pw_reg pw_base pw_ptr pw_end] in *.
      iPureIntro. intuition lia. }
    unfold choice_own. iFrame "Hwin". iSplit; [done|]. unfold win_live. cbn [data_win pw_obj pw_reg].
    destruct (numbers.Z.eq_dec (fc_data c) bb); [contradiction|]. iFrame "Hd". iIntros "Hfp Herr #Hro #Hm".
    unfold file_R, pw_place. cbn [data_win pw_obj pw_reg pw_base pw_ptr pw_end]. destruct (Z.eq_dec (fc_data c) bb); [contradiction|].
    iFrame "Hfp Herr Hro Hm Hstage Hloan". unfold pwin_ok in Hw. cbn [data_win pw_obj pw_reg pw_base pw_ptr pw_end] in Hw.
    repeat iSplit; iPureIntro; unfold stage_end; intuition lia. }
  all: iDestruct "Hback" as "[HF _]"; iDestruct ("HF" with "Hs") as "HF"; unfold choice_own, win_live, pw_lo, stage_win;
    cbn [pw_obj pw_reg pw_base pw_ptr pw_end]; destruct (numbers.Z.eq_dec bb bb); [|contradiction];
    replace (bb+stage_off-(bb+stage_off) mod 8) with (bb+stage_off) by (unfold stage_off; Z.div_mod_to_equations; lia);
    iFrame "Hstage"; iSplit; [iPureIntro; unfold pwin_ok, stage_off, stage_end; cbn [pw_obj pw_reg pw_base pw_ptr pw_end]; intuition lia|];
    iSplit; [done|]; iIntros "Hfp Herr #Hro #Hm"; unfold file_R, pw_place; cbn [pw_obj pw_reg pw_base pw_end]; destruct (Z.eq_dec bb bb); [|contradiction];
    iFrame "Hfp Herr Hro Hm HF"; iSplit; [iPureIntro; unfold stage_end; lia|]; iSplit; [by iPureIntro; intuition|];
    iExists [], []; iSplit; [iPureIntro; cbn; split_and!; auto; lia|by rewrite /bytes /auxes /pts /= left_id].
Qed.
End choice.

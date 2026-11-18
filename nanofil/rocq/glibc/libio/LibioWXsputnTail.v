(** After filling the available room, the default wide writer tests how
    many characters remain. If it still has input, it borrows one more
    character for overflow. A successful call consumes that character;
    a WEOF return leaves it out of the reported count. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWOverflowDispatch LibioWXsputnWords LibioOverflowBase CBlocks WPrintfDispatch WPrintfLength.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).

(** At the start and end of each round the same two arguments still
    hold the stream and the original count. Only the registers for the
    remaining count and its source pointer change between blocks. *)
Definition wsource_regs e fp s so n left (count src : string) :=
  lookup (TAtom "v0") e = Some (WPtr fp) /\ lookup (TAtom "v4") e = Some (WInt n) /\
  lookup (TAtom count) e = Some (WInt left) /\
  lookup (TAtom src) e = Some (WPtr (mkPtr (s+so+4*(n-left)) (Obj s))) /\ 0 <= left <= n.

Section tail.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

Definition wcount_post fp dq s sr so cs (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ r, ⌜0 <= r <= size cs⌝ -∗ file_wide ge vb self fp 1 -∗ E -∗
    liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗ Φ (Ret (WInt r)).

Definition wdefault_round fp dq s sr so cs Φ : iProp Σ := ∀ e t,
  ⌜wsource_regs e fp s so (size cs) t "pr.7" "pr.2"⌝ -∗ file_wide ge vb self fp 1 -∗ E -∗
  liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗ wcount_post fp dq s sr so cs Φ -∗
  WP (ERun (mkFrame wdefault_xsputn_fn e [] None (body_at wdefault_xsputn_fn "L16")) : sexpr) {{ Φ }}.

Context `{!Defines ge "__GI___woverflow" woverflow_fn} (Hov : woverflow_spec vb self E woverflow_fn).

Lemma wp_wdefault_tail fp dq s sr so cs Φ e t :
  0 < s -> 0 <= so -> s+so+4*size cs <= r_end sr -> r_end sr <= 2^63 -> Forall (fun c => 0 <= c < 2^32) cs ->
  wsource_regs e fp s so (size cs) t "pr.8" "pr.3" ->
  file_wide ge vb self fp 1 -∗ E -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  ▷ wdefault_round fp dq s sr so cs Φ -∗ wcount_post fp dq s sr so cs Φ -∗
  WP (ERun (mkFrame wdefault_xsputn_fn e [] None (body_at wdefault_xsputn_fn "L37")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hs Ho He Hr V (Hfp & Hn & Ht & Hp & R). iIntros "HF HE Hl Hcs IH HK".
  body_start wdefault_xsputn_fn "L37"%string. step. destruct (Z.eq_dec t 0) as [->|Hnz].
  - branch_as false. step. branch. step. step. iApply wp_ret; [reflexivity|vx|]. iNext. norm. unwrap2.
    rewrite Z.sub_0_r. iApply ("HK" with "[%] HF HE Hl Hcs"). lia.
  - branch_as true. step. step. set (k := Z.to_nat (size cs-t)).
    destruct (lookup_lt_is_Some_2 cs k ltac:(lia)) as [c Hc]. pose proof (Forall_lookup_1 _ _ _ _ V Hc) as Vc. cbn beta in Vc.
    iDestruct (wchar_at _ _ _ _ _ _ Hc with "Hcs") as "[Hx Hback]".
    check_read_dq "Hl" by a2. iNext. iIntros "Hl". load_bytes_dq "Hl Hx" decode (apply load_sw_int; exact Vc) by a2.
    iNext. iIntros "Hl Hx". iDestruct ("Hback" with "Hx") as "Hcs".
    iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext. norm.
    iApply (Hov _ fp c with "HF HE"); [done|reflexivity|]. iNext. iIntros (r Hret) "HF HE". resume. do 3 step.
    destruct (Z.eq_dec r (2^32-1)) as [->|Hok].
    + branch_as false. step. step. iApply wp_ret; [reflexivity|vx|]. iNext. norm. unwrap2.
      iApply ("HK" with "[%] HF HE Hl Hcs"). lia.
    + assert (Rr : 0 <= r < 2^32) by (unfold ovf_ret in Hret; destruct Hret as [Hfail|Hok1]; [lia|rewrite Hok1; destruct (c =? _); lia]).
      branch_as true. do 4 step. iApply ("IH" $! _ (t-1) with "[%] HF HE Hl Hcs HK").
      split_and!; try (lookups; reflexivity); try lia; lookups; cbn [ptr_addr ptr_cap]; unwrap2; do 3 f_equal; lia.
Qed.
End tail.

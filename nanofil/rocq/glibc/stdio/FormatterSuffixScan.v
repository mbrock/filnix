(** After printing a conversion, glibc scans the following format text.
    This proof advances the saved format pointer past the conversion
    letter, calls the captured scanning helper and stores its result.
    The result points to the next percent sign or terminating NUL.

    The caller must own the saved pointer cell and enough padded memory
    to read the suffix. The scan does not write output. This rule does
    not cover the later suffix write or the formatter's return. *)
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps
  Fix WordString FormatterScan StrchrnulLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
(** This block resumes formatting after the string write. *)
Definition suffix_block := Eval vm_compute in
  match find_block (TAtom "L1150") (fn_blocks Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer) with
  | Some b => b | None => mkBlock (TAtom "absent") [] [] JRetVoid end.
(** The selector finds the captured block rather than its fallback. *)
Lemma suffix_block_found :
  find_block (TAtom "L1150") (fn_blocks Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer) = Some suffix_block.
Proof. vm_compute. reflexivity. Qed.
(** Scanning advances the conversion counter with machine-word wrapping
    and records both the suffix pointer and the scan result. *)
Definition suffix_scan_env e cb p n count k :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "pr.12", WInt (n mod 2^32)); (TAtom "v2113", WInt ((count mod 2^32 + 1) mod 2^32));
     (TAtom "chk191", WPtr (mkPtr cb (Obj cb)));
     (TAtom "v2114", WPtr (mkPtr (ptr_addr p - 1) (ptr_cap p)));
     (TAtom "v2115", WPtr p); (TAtom "chk192", WPtr (mkPtr cb (Obj cb)));
     (TAtom "v2116", WPtr (ptr_add p k)); (TAtom "chk193", WPtr (mkPtr cb (Obj cb)))] e.
Section suffix.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** The formatter must remember where the next conversion begins.
    The scan replaces its saved pointer to the preceding conversion
    letter with the next percent sign or NUL. It leaves the suffix
    readable with the caller's original ownership share. *)
Lemma wp_formatter_suffix_scan e ls cb cr p dq s n count Φ :
  lookup (TAtom "pr.16") e = Some (WInt n) ->
  lookup (TAtom "pr.11") e = Some (WInt count) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  0 < ptr_addr p < 2^63 ->
  live cb cr -∗ pcell cb 0 (mkPtr (ptr_addr p - 1) (ptr_cap p)) -∗ word_string dq p s -∗
  ▷ (live cb cr -∗ pcell cb 0 (ptr_add p (Z.of_nat (chr_idx 37 s))) -∗ word_string dq p s -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
      (suffix_scan_env e cb p n count (Z.of_nat (chr_idx 37 s))) ls None
      (Exec (TAtom "L1150") (skipn 9 (b_insts suffix_block)) (b_jump suffix_block))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L1150") (Some (TAtom "L1887")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hn Hcount Hv Hchk Hchr Hscan Hb Ha He Hr Hp.
  iIntros "Hl Hcell Hs HK".
  iDestruct "Hs" as (b reg ws) "[%Hshape [Hsl Hwords]]".
  pose proof Hshape as [Hcap Hsb Hsa Hst Hfit Hspace Hlen Hws Hbytes Hchars].
  iAssert (live_capq dq (ptr_cap p) reg) with "[Hsl]" as "Hsl".
  { destruct Hcap as [-> | ->]; iExact "Hsl". }
  iApply wp_enter; [reflexivity | vx |]. iNext.
  cbn [b_insts b_jump]. step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcell Hsl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hl Hcell Hsl". step.
  replace (ptr_addr p - 1 + 1) with (ptr_addr p) by lia.
  destruct p as [pa pc]. cbn [ptr_addr ptr_cap] in *.
  assert (Hinc : ((pa - 1) mod 2^64 + 1 mod 2^64) mod 2^64 = pa).
  { rewrite (Z.mod_small (pa - 1) (2^64)); [|lia].
    rewrite (Z.mod_small 1 (2^64)); [|lia].
    replace (pa - 1 + 1) with pa by lia. apply Z.mod_small. lia. }
  rewrite Hinc.
  check "Hl". store "Hl" "Hcell".
  iAssert (liveq dq b reg) with "[Hsl]" as "Hsl".
  { destruct Hcap as [Hcap | Hcap]; subst pc; iExact "Hsl". }
  iAssert (word_string dq (mkPtr pa pc) s) with "[Hsl Hwords]" as "Hs".
  { iExists b, reg, ws. iSplit; [done|iFrame]. }
  iApply wp_call_bind; [vx | exact Hscan | reflexivity |]. iNext.
  iApply (wp_wand with "[Hs]").
  { iApply (wp_find_specmb dq (mkPtr pa pc) s
      (fun v => ⌜v = Ret (WPtr (ptr_add (mkPtr pa pc) (Z.of_nat (chr_idx 37 s))))⌝ ∗
        word_string dq (mkPtr pa pc) s)%I with "Hs"); [exact Hchr|].
    iIntros "Hs". iFrame. done. }
  iIntros (v) "[-> Hs]". resume.
  check "Hl". store "Hl" "Hcell".
  norm. closed_ints.
  iApply ("HK" with "Hl Hcell Hs").
Qed.
End suffix.

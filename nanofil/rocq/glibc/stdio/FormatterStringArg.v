(** The ordinary string conversion reads one pointer from the caller's
    variadic snapshot. This rule follows the actual argument block, not
    the parser that selects it. It advances the caller cursor by eight
    bytes and preserves the snapshot and target ownership. FILE fields,
    staging, errno and registration globals remain in the caller's frame.
    This rule does not establish parser readiness or a complete conversion. *)
From Glibc Require FixVariadic.
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld FileInv Fix.
Module StringVL := FixVariadic.VL0.
Import StringVL ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section argument.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Reading an argument must recover its pointer authority, not just its
    address. The caller therefore lends the argument cell and ownership
    of the object it points to. The next block receives that same ownership
    and the advanced cursor. The function keeps its local allocations. *)
Lemma wp_formatter_string_arg e ls from cb cr sb sr off x ps Φ :
  lookup (TAtom "v4") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr ->
  r_end sr <= 2 ^ 48 -> (sb + off) mod 8 = 0 -> 0 <= ptr_addr x < 2 ^ 64 ->
  (ptr_cap x = CNone \/ exists xb xr,
    (ptr_cap x = Obj xb \/ ptr_cap x = Ro xb) /\ (PLive xb, VLive xr) ∈ ps) ->
  pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off x -∗ pts ps -∗
  ▷ (pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off x -∗ pts ps -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (put (TAtom "v1828") (WPtr x) e) ls None
      (Enter (TAtom "L1695") (Some (TAtom "L1825")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L1825") from)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv Hcb Hsb Ho He Hr Ha Hx Htarget.
  assert (Hwi : forall m w h,
    (forall k v, (k, v) ∈ va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb)) -> h !! k = Some v) ->
    os_wi w0 m w h -> os_wi w0 (store_bytes m cb 8 (sb + off + 8)) w
      (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) h)).
  { intros m w h Hown Hw. eapply os_wi_store; [reflexivity | | exact Hw].
    intros k v Hin. destruct k; try done.
    apply Hown. unfold va_cursor_ps, cell in *.
    simpl in *. set_solver. }
  iIntros "Hc Hl Hx Hps HK".
  iApply wp_enter; [reflexivity | destruct from; reflexivity |]. iNext.
  iApply (wp_va_arg_pointer with "Hc Hl Hx Hps");
    [vx | exact Hcb | exact Hsb | exact Ho | exact He | exact Hr |
     exact Ha | exact Hx | exact Htarget | exact Hwi |].
  iNext. iIntros "Hc Hl Hx Hps". iApply wp_goto. iNext.
  iApply ("HK" with "Hc Hl Hx Hps").
Qed.
End argument.

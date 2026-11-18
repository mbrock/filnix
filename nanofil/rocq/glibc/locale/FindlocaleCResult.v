(** Both names for the C locale lead to the same built-in data. After
    choosing a nonempty name, glibc compares it with "C" and then, if
    necessary, with "POSIX". It writes the canonical name back to the
    caller and returns the data for the requested category. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls ExternalMachine
  Pieces Heap Language Logic MemLogic StepRules Symbolic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptBytes StrcmpCode StrcmpLogic FindlocaleCode LocaleEnv Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** The search keeps the category and two slots in registers. Each
    slot has a checked pointer that later blocks renew before access. *)
Definition findlocale_regs (e : env) (cat d : Z) (slot : ptr) : Prop :=
  lookup (TAtom "v4") e = Some (WInt cat) /\ lookup (TAtom "v6") e = Some (WPtr slot) /\
  lookup (TAtom "chk0") e = Some (WPtr slot) /\ lookup (TAtom "v9") e = Some (WPtr (mkPtr d (Obj d))) /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr d (Obj d))).

Section result.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance fl_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation heap d := (mkRegion d (d+16) Heap Live).
Context (cb pb lb : Z) (Hcn : lookup (TAtom "_nl_C_name") (ge_globals ge) = Some (rop cb))
  (Hpn : lookup (TAtom "_nl_POSIX_name") (ge_globals ge) = Some (rop pb))
  (Hlo : lookup (TAtom "_nl_C_locobj") (ge_globals ge) = Some (rop lb))
  (Hcmp : find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp)).

(** The name in the local slot is either "C" or "POSIX". The caller's
    slot still has its old value until both comparisons are finished.
    Only that slot changes; the table entry and its target stay live. *)
Lemma findlocale_c_result e pred cat b o reg d p q s dq dc dt lr target tr Φ :
  findlocale_regs e cat d (mkPtr (b+o) (Obj b)) -> s = lit "C" \/ s = lit "POSIX" ->
  0 <= cat < 13 -> 0 < b -> 0 <= o -> (b+o) mod 8 = 0 -> b+o+8 <= r_end reg -> r_end reg <= 2^48 ->
  0 < d -> d mod 8 = 0 -> d+16 <= 2^48 -> 0 < lb -> lb mod 8 = 0 -> lb+8*cat+8 <= r_end lr -> r_end lr <= 2^48 ->
  0 <= ptr_addr target < 2^64 ->
  word_string DfracDiscarded (rop cb) (lit "C") -∗ word_string DfracDiscarded (rop pb) (lit "POSIX") -∗
  word_string DfracDiscarded q s -∗ live d (heap d) -∗ pcell d 0 q -∗ live b reg -∗ pcell b o p -∗
  liveq dq lb lr -∗ pcellq dc lb (8*cat) target -∗ live_capq dt (ptr_cap target) tr -∗
  (live b reg -∗ pcell b o (rop cb) -∗ liveq dq lb lr -∗ pcellq dc lb (8*cat) target -∗ live_capq dt (ptr_cap target) tr -∗
   Φ (Ret (WPtr target))) -∗
  WP (ERun (mkFrame glibc_nl_find_locale e [] None (Enter (TAtom "L20") (Some pred))) : sexpr) {{ Φ }}.
Proof using Type*.
  intros (Hcat & Hslot & Hchk & Hdreg & Hdchk) Hs Hcatb Hb Ho Ha He Hr Hd Hda Hde Hlb Hla Hle Hlr Ht.
  iIntros "#HC #HP #Hs Hd Hq Hl Hcell Hlo Hval Hlife HK".
  iDestruct (ws_byte q s 0 with "Hs") as (sb sr (Hsc & Hsb & Hsa & Hse & Hsr)) "[#Hsl _]"; [lia|].
  iAssert (live_capq DfracDiscarded (ptr_cap q) sr) as "Hsk"; [destruct Hsc as [->| ->]; iExact "Hsl"|].
  step. check "Hd". load_pointer_dq "Hd Hq Hsk" by a2. iNext. iIntros "Hd Hq _". step_global Hcn.
  Local Ltac cmp H := iApply (wp_call_glibc_strcmp registry (os_wi w0) ge with H);
    [vx | exact Hcmp | reflexivity |]; iNext; iIntros "_ _"; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  cmp "Hs HC". destruct Hs as [->| ->]; do 2 step; branch; step.
  2: (check "Hd"; load_pointer_dq "Hd Hq Hsk" by a2; iNext; iIntros "Hd Hq _"; step_global Hpn;
      cmp "Hs HP"; do 4 step).
  all: branch; step; step_global Hcn; check "Hl"; store "Hl" "Hcell"; step_global Hlo; do 2 step_symbolic.
  all: iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lb+8*cat));
    [vx | cbn; f_equal; f_equal; change (2 ^ ((3 mod 2 ^ 32) mod 64)) with 8;
          unfold sign_extension; unwrap2; destruct (Z.leb_spec (2^31) cat); [lia|]; a2 | vx |]; iNext.
  all: check_read_dq "Hlo" by a2; iNext; iIntros "Hlo"; load_pointer_dq "Hlo Hval Hlife" by a2;
    iNext; iIntros "Hlo Hval Hlife"; iApply wp_ret; [reflexivity | vx |]; iNext; iApply ("HK" with "Hl Hcell Hlo Hval Hlife").
Qed.
End result.

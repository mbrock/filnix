(** Glibc tests whether an environment value names a locale. A null
    pointer skips the byte load. A pointer to the empty string takes
    the same fallback, but only after glibc reads its terminator. The
    compiler inlines this test at each of the three lookups. *)

From Glibc Require Import Unit_locale_findlocale_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls ExternalMachine
  Pieces Heap Language Logic MemLogic StepRules Symbolic.
From Glibc Require Import IRFrames.
From Glibc Require Import OsWorld OsMemLogic WordString ByteRead FindlocaleCResult FindlocaleEnv LocaleEnv Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsMemLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** The three copies inspect LC_ALL, the current category and LANG, in that order. *)
Inductive findlocale_test := AfterAll | AfterCategory | AfterLang.

(** To tell whether getenv found a variable, glibc compares the
    address it returned with zero. It computes that zero once and
    keeps it for all three comparisons. *)
Definition findlocale_search_regs e cat d slot :=
  findlocale_regs e cat d slot /\ lookup (TAtom "iw_1.v4") e = Some (WInt 0).

(** This frame starts at the reload of the local name pointer. The
    first block calls getenv and stores its result before the reload. *)
Definition findlocale_test_frame t e :=
  let l := match t with AfterAll => "L18" | AfterCategory => "L29" | AfterLang => "L38" end%string in
  let b := hblk Unit_locale_findlocale_os.fn__nl_find_locale l in
  mkFrame Unit_locale_findlocale_os.fn__nl_find_locale e [] None (Exec (TAtom l)
    (skipn (match t with AfterAll => 4 | _ => 0 end) (b_insts b)) (b_jump b)).

(** Each copy has its own join block and its own fallback. A missing
    LANG falls back to the literal "C" rather than another lookup. *)
Definition findlocale_test_next t (present : bool) e :=
  let join := match t with AfterAll => "iw_1.L7" | AfterCategory => "iw_3.L7" | AfterLang => "iw_4.L7" end%string in
  let l := match t, present with
    | AfterAll, true => "L29" | AfterAll, false => "iw_2.start"
    | AfterCategory, true => "L38" | AfterCategory, false => "L36"
    | AfterLang, true => "L20" | AfterLang, false => "L44" end%string in
  mkFrame Unit_locale_findlocale_os.fn__nl_find_locale e [] None (Enter (TAtom l) (Some (TAtom join))).

Section present.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation heap d := (mkRegion d (d+16) Heap Live).

(** On the taken branch the pointer holds one of the two built-in
    names. On the fallback branch the caller can overwrite the local
    pointer without knowing whether it was null or pointed to NUL. *)
Lemma findlocale_name_present t e cat d slot q Φ :
  findlocale_regs e cat d slot -> (t = AfterAll \/ lookup (TAtom "iw_1.v4") e = Some (WInt 0)) ->
  0 < d -> d mod 8 = 0 -> d+16 <= 2^48 ->
  findlocale_value (fun v => In v c_locale_values) q -∗ live d (heap d) -∗ pcell d 0 q -∗
  (∀ (hit : bool) e', ⌜findlocale_search_regs e' cat d slot⌝ -∗ live d (heap d) -∗ pcell d 0 q -∗
     (if hit then ∃ s, ⌜s = lit "C" \/ s = lit "POSIX"⌝ ∗ word_string DfracDiscarded q s else True) -∗
     WP (ERun (findlocale_test_next t hit e') : sexpr) {{ Φ }}) -∗
  WP (ERun (findlocale_test_frame t e) : sexpr) {{ Φ }}.
Proof using Type*.
  intros (Hcat & Hslot & Hchk & Hdr & Hdc) Hz Hd Hda Hde. iIntros "Hvalue Hd Hq HK".
  Local Ltac setup_test t Hz := destruct t; unfold findlocale_test_frame;
    lazymatch goal with |- context [hblk Unit_locale_findlocale_os.fn__nl_find_locale ?l] =>
      let B := eval vm_compute in (hblk Unit_locale_findlocale_os.fn__nl_find_locale l) in change (hblk Unit_locale_findlocale_os.fn__nl_find_locale l) with B end;
    cbn [skipn b_jump b_insts];
    try (destruct Hz as [Hbad|Hz]; [discriminate|]); check "Hd".
  Local Ltac finish_test hit := iApply ("HK" $! hit _ with "[%] Hd Hq");
    [repeat split; lk_prove|].
  iDestruct "Hvalue" as "[%Hnull|Hs]".
  - subst q. setup_test t Hz; load_null "Hd" "Hq"; repeat step; branch; step; branch; finish_test false; done.
  - iDestruct "Hs" as (s Hin) "#Hs".
    iDestruct (ws_byte q s 0 with "Hs") as (b r (Hcap & Hb & Ha & He & Hr)) "[#Hl #Hb]"; [lia|].
    iAssert (live_capq DfracDiscarded (ptr_cap q) r) as "Ht"; [destruct Hcap as [->| ->]; iExact "Hl"|].
    setup_test t Hz; load_pointer_dq "Hd Hq Ht" by a2; iNext; iIntros "Hd Hq _"; repeat step; branch_as false;
      step; check_read_dq "Hl" by a2; iNext; iIntros "_"; load_bytes_dq "Hl Hb" decode (apply extended_chr) by a2;
      iNext; iIntros "_ _"; step_symbolic; step; step.
    all: destruct Hin as [<-|[<-|[<-|[]]]]; branch.
    all: first [finish_test false; done | finish_test true; iExists _; iSplitL ""; [|iExact "Hs"]; iPureIntro; auto].
Qed.
End present.

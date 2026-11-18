(** When setlocale asks for the empty name, glibc looks up LC_ALL,
    the variable for the requested category, and LANG, in that order.
    If none names a locale, it chooses "C". This proof follows the
    compiled lookups and returns the category's built-in locale data. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls ExternalMachine
  Pieces Heap Language Logic MemLogic StepRules Symbolic VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic GetoptBytes WordString GetenvCode GetenvEntry GetenvScan GetenvStatic
  GetenvCall StartGetenv StrlenLogic StrncmpCode StrcmpBits StrcmpCode LocaleEnv FindlocaleCode FindlocaleEnv
  FindlocaleCResult FindlocalePresent Fix.
Module FL := VariadicLogicOn R LG0.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic FL.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation heap d := (mkRegion d (d+16) Heap Live).

Section search.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{!Defines ge "__GI_getenv" glibc_getenv, !Defines ge "__GI_strlen" glibc_strlen,
          !Defines ge "__GI_strncmp" glibc_strncmp}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (dq dqa dqt : dfrac) (bc : Z) (rc : region) (be : Z) (re : region) (counter : Z) (ep : ptr) (es : list getenv_entry)
  (Himage : getenv_image_ok ge bc rc be re) (Henv : c_locale_env (map entry_text es)).
Local Notation globals := (getenv_globals dq bc rc be re counter ep).
Local Notation storage := (getenv_storage dqa dqt ep es).
Local Notation value := (findlocale_value (fun v => In v c_locale_values)).

(** The first matching entry has an allowed value even when the
    environment contains several entries with that name. *)
Local Lemma locale_getenv e l d args rest j p s Φ :
  map_option (arg_x ge e) args = Some [WPtr p] -> In s locale_vars ->
  word_string DfracDiscarded p s -∗ globals -∗ storage -∗
  (∀ q, value q -∗ globals -∗ storage -∗
    WP (ERun (mkFrame glibc_nl_find_locale (put d (WPtr q) e) [] None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_nl_find_locale e [] None (Exec l
       (Call (CResult d P) (Global (TAtom "__GI_getenv")) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hx Hin. destruct Himage as (? & ? & ? & ? & ? & ? & ? & ? & ?). iIntros "#Hkey HG HS HK".
  iApply (wp_call_getenv_static with "Hkey HG HS []"); try eassumption; [iEmpIntro|].
  iNext. iIntros "HG HS _ _". iDestruct (findlocale_getenv_value _ _ _ _ _ _ (fun v => In v c_locale_values)
    with "Hkey HS") as "[HS Hv]"; [intros v Hv; exact (proj1 Henv s v Hv Hin)|]. iApply ("HK" with "Hv HG HS").
Qed.

Context (ap lp : ptr) (cb ib nb idx cat : Z) (ir : region) (di dv : dfrac) (key : list Z)
  (Hall : lookup (TAtom "glibc_findlocale#str.243") (ge_globals ge) = Some ap)
  (Hlang : lookup (TAtom "glibc_findlocale#str.244") (ge_globals ge) = Some lp)
  (Hcn : lookup (TAtom "_nl_C_name") (ge_globals ge) = Some (rop cb))
  (Hidx : lookup (TAtom "_nl_category_name_idxs") (ge_globals ge) = Some (rop ib))
  (Hnames : lookup (TAtom "_nl_category_names") (ge_globals ge) = Some (rop nb))
  (Hcat : 0 <= cat < 13) (Hib : 0 < ib) (Hie : ib+cat+1 <= r_end ir) (Hir : r_end ir <= 2^48)
  (Hix : 0 <= idx < 256) (Hkey : In key locale_vars).
Local Notation keyptr := (mkPtr (nb+idx) (Ro nb)).
Local Notation loans := (globals ∗ storage ∗ liveq di ib ir ∗ bytesq dv ib cat [idx])%I.
Local Abbreviation enter e l pred := (ERun (mkFrame glibc_nl_find_locale e [] None (Enter (TAtom l) (Some pred))) : sexpr).

(** Each fallback joins the callers that already have a candidate and
    those that have just read one from the next variable. Both enter
    the join with the same environment and local pointer cell. *)
Local Definition ready l cat d slot Φ : iProp Σ :=
  ∀ e pred q, ⌜findlocale_search_regs e cat d slot⌝ -∗ value q -∗ live d (heap d) -∗ pcell d 0 q -∗ loans -∗
    WP (enter e l pred) {{ Φ }}.

Local Ltac regs H := destruct H as ((? & ? & ? & ? & ?) & ?).
Local Ltac prove_regs := repeat split; lk_prove.
Local Ltac save_name := check "Hd"; store "Hd" "Hq".

(** The search starts after the caller's empty string has been read.
    It ends at the two comparisons with a nonempty built-in name in
    the local cell. Nothing in the search changes the environment. *)
Local Lemma choose_name e d slot pred p Φ :
  findlocale_regs e cat d slot -> 0 < d -> d mod 8 = 0 -> d+16 <= 2^48 ->
  word_string DfracDiscarded (rop cb) (lit "C") -∗ word_string DfracDiscarded ap (lit "LC_ALL") -∗
  word_string DfracDiscarded keyptr key -∗ word_string DfracDiscarded lp (lit "LANG") -∗
  live d (heap d) -∗ pcell d 0 p -∗ loans -∗
  (∀ e' pred' q s, ⌜findlocale_regs e' cat d slot⌝ -∗ ⌜s = lit "C" \/ s = lit "POSIX"⌝ -∗
    word_string DfracDiscarded q s -∗ live d (heap d) -∗ pcell d 0 q -∗ loans -∗ WP (enter e' "L20" pred') {{ Φ }}) -∗
  WP (enter e "L18" pred) {{ Φ }}.
Proof using Type*.
  intros Hr Hd Hda Hde. iIntros "#HC #Hall #Hkey #Hlang Hdl Hptr Hloans HK".
  iAssert (ready "L38" cat d slot Φ) with "[HK]" as "K38".
  { iIntros (e' from q Hregs) "Hv Hd Hq HR". step.
    iApply (findlocale_name_present AfterLang _ cat d slot with "Hv Hd Hq"); try apply Hregs; try lia; [right; apply Hregs|].
    iIntros ([] e2 Hnext) "Hd Hq Hname"; unfold findlocale_test_next.
    - iDestruct "Hname" as (s Hs) "#Hname". iApply ("HK" with "[%] [%] Hname Hd Hq HR"); [apply Hnext|exact Hs].
    - regs Hnext. step. step_global Hcn. save_name. step. iApply ("HK" with "[%] [%] HC Hd Hq HR"); [prove_regs|auto]. }
  iAssert (ready "L29" cat d slot Φ) with "[K38]" as "K29".
  { iIntros (e' from q Hregs) "Hv Hd Hq HR". iDestruct "Hv" as "#Hv". step.
    iApply (findlocale_name_present AfterCategory _ cat d slot with "Hv Hd Hq"); try apply Hregs; try lia; [right; apply Hregs|].
    iIntros ([] e2 Hnext) "Hd Hq _"; unfold findlocale_test_next.
    - iApply ("K38" with "[%] Hv Hd Hq HR"); exact Hnext.
    - regs Hnext. step. step_global Hlang. iDestruct "HR" as "(HG & HS & Hi & Hb)".
      iApply (locale_getenv with "Hlang HG HS"); [vx|vm_compute; tauto|]. iIntros (q') "Hv' HG HS".
      save_name. step. iApply ("K38" with "[%] Hv' Hd Hq [$HG $HS $Hi $Hb]"); prove_regs. }
  destruct Hr as (? & ? & ? & ? & ?). step. step_global Hall. iDestruct "Hloans" as "(HG & HS & Hi & Hb)".
  iApply (locale_getenv with "Hall HG HS"); [vx|vm_compute; tauto|]. iIntros (q) "#Hv HG HS".
  iRename "Hdl" into "Hd". iRename "Hptr" into "Hq". save_name.
  iApply (findlocale_name_present AfterAll _ cat d slot with "Hv Hd Hq"); [prove_regs|left; reflexivity|lia|lia|lia|].
  iIntros ([] e2 Hnext) "Hd Hq _"; unfold findlocale_test_next.
  - iApply ("K29" with "[%] Hv Hd Hq [$HG $HS $Hi $Hb]"); exact Hnext.
  - regs Hnext. step. step_global Hnames. step_global Hidx. step_symbolic.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ib+cat)); [vx|cbn; f_equal; f_equal; rewrite sext_small; [a2|lia]|vx|]. iNext.
    check_read_dq "Hi" by a2. iNext. iIntros "Hi".
    assert (Ebyte : extended Ub W (of_bytes [idx]) = Some (WInt idx)).
    { change (Some (WInt (((idx+0) mod 256) mod 2^32)) = Some (WInt idx)).
      rewrite Z.add_0_r (Z.mod_small idx 256); [rewrite Z.mod_small; [reflexivity|lia]|lia]. }
    load_bytes_dq "Hi Hb" decode (exact Ebyte) by a2. iNext. iIntros "Hi Hb". step_symbolic.
    iDestruct (ws_byte keyptr key 0 with "Hkey") as (bb rr ([E|E] & Hbb & Hstart & Hke & Hkr)) "_"; [lia|discriminate|].
    injection E as <-. cbn [ptr_addr] in Hke.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nb+idx)); [vx|cbn; f_equal; f_equal; a2|vx|]. iNext.
    iApply (locale_getenv with "Hkey HG HS"); [vx|exact Hkey|]. iIntros (q') "Hv' HG HS".
    save_name. step. iApply ("K29" with "[%] Hv' Hd Hq [$HG $HS $Hi $Hb]"); prove_regs.
Qed.

(** Setlocale lends its writable name slot and asks for one category.
    On return that slot points to the canonical "C" string, and the
    result is the exact pointer read from the built-in locale table.
    The call only reads the environment, names and table, so their
    [[separation-logic|shares]] remain available for the next category. *)
Lemma wp_findlocale_c fr b o reg p pb lb dqlo dqcell dqlife lr target tr Φ :
  call_frame glibc_nl_find_locale [WPtr null; WInt 0; WInt cat; WPtr (mkPtr (b+o) (Obj b))] = Some fr ->
  lookup (TAtom "_nl_POSIX_name") (ge_globals ge) = Some (rop pb) ->
  lookup (TAtom "_nl_C_locobj") (ge_globals ge) = Some (rop lb) ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  0 < b -> 0 <= o -> (b+o) mod 8 = 0 -> b+o+8 <= r_end reg -> r_end reg <= 2^48 ->
  0 < lb -> lb mod 8 = 0 -> lb+8*cat+8 <= r_end lr -> r_end lr <= 2^48 -> 0 <= ptr_addr target < 2^64 ->
  word_string DfracDiscarded p [] -∗ word_string DfracDiscarded (rop cb) (lit "C") -∗
  word_string DfracDiscarded (rop pb) (lit "POSIX") -∗ word_string DfracDiscarded ap (lit "LC_ALL") -∗
  word_string DfracDiscarded keyptr key -∗ word_string DfracDiscarded lp (lit "LANG") -∗
  live b reg -∗ pcell b o p -∗ loans -∗ liveq dqlo lb lr -∗ pcellq dqcell lb (8*cat) target -∗ live_capq dqlife (ptr_cap target) tr -∗
  ▷ (live b reg -∗ pcell b o (rop cb) -∗ loans -∗ liveq dqlo lb lr -∗ pcellq dqcell lb (8*cat) target -∗
     live_capq dqlife (ptr_cap target) tr -∗ Φ (Ret (WPtr target))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hpn Hlo Hcmp Hb Ho Ha He Hr Hlb Hla Hle Hlr Ht. injection Hfr as <-.
  iIntros "#Hp #HC #HP #Hall #Hkey #Hlang Hl Hcell HR Hlo Hentry Htarget HK".
  step. Local Ltac fl_alloc := iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext.
  fl_alloc. iIntros (d Hfresh) "Hd". change (0 < d /\ d mod 16 = 0 /\ d+16 <= 2^48) in Hfresh.
  destruct Hfresh as (Hd & H16 & Hde). assert (Hda : d mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hd") as "(Hd & Hb & Ha)"; [vm_compute; congruence|].
  iAssert (live d (heap d)) with "Hd" as "Hd". iDestruct (zero_cell_prefix d 0 8 with "Hb Ha") as "(Hq & _ & _)".
  do 5 (fl_alloc; iIntros (? _) "_").
  iDestruct (ws_byte p [] 0 with "Hp") as (sb sr (Hsc & Hsb & Hsa & Hse & Hsr)) "[#Hsl #Hbyte]"; [lia|].
  iAssert (live_capq DfracDiscarded (ptr_cap p) sr) as "Hsk"; [destruct Hsc as [->| ->]; iExact "Hsl"|].
  check "Hl". load_pointer_dq "Hl Hcell Hsk" by a2. iNext. iIntros "Hl Hcell _". save_name.
  check "Hd". load_pointer_dq "Hd Hq Hsk" by a2. iNext. iIntros "Hd Hq _".
  check_read_dq "Hsl" by a2. iNext. iIntros "_". load_bytes_dq "Hsl Hbyte" decode reflexivity by a2.
  iNext. iIntros "_ _". step. branch.
  iApply (choose_name _ d (mkPtr (b+o) (Obj b)) with "HC Hall Hkey Hlang Hd Hq HR"); [prove_regs|lia|lia|lia|].
  iIntros (e pred q s Hregs Hs) "#Hs Hd Hq HR".
  iApply (findlocale_c_result cb pb lb Hcn Hpn Hlo Hcmp with "HC HP Hs Hd Hq Hl Hcell Hlo Hentry Htarget"); try eassumption.
  iIntros "Hl Hcell Hlo Hentry Htarget". iApply ("HK" with "Hl Hcell HR Hlo Hentry Htarget").
Qed.
End search.

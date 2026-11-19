From Glibc Require Import Unit_intl_dcigettext_os.
From Glibc Require Import GlibcProgram.
(** When a program runs in the C locale, glibc's message lookup returns
    the message it was given. This module proves the last block of that
    route in `c: __dcigettext`, the block that the source labels
    `c: return_untranslated`. The block frees the three strings that the
    lookup allocated, releases the two locale locks, puts back the errno
    value saved at entry, and returns the original message id.

    Releasing a lock is the one step of the block that this module does
    not prove, because glibc's rwlock code is not captured here. A caller
    therefore states how each release behaves, naming the resources that
    the lock takes and gives back. The rest of the C route lives in
    DcigettextC.v. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsMemLogic OsExternals DcigettextFree.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Import Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld OsMemLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## Restoring errno

    The lookup saves errno at entry and stores the saved value back at
    exit, because the calls in between may change it. The OS invariant
    keeps the four errno bytes in a live global object, so these rules
    need only the caller's ownership of those bytes. *)

(** The errno object's bounds hold in every machine state. *)
Definition dci_errno_mem eb m :=
  ∃ reg, live_at m eb reg ∧ 0 <= eb ∧ eb + 4 <= r_end reg ∧ r_end reg <= 2 ^ 48.

(** The state interpretation supplies those bounds at every step. *)
Lemma dci_errno_mem_facts σ : heap_interp (os_wi w0) σ -∗ ⌜dci_errno_mem eb (ls_mem σ)⌝.
Proof using Type*.
  iIntros "Hσ". iDestruct (os_heap_errno w0 σ eb Herr with "Hσ") as %[_ (reg & Hl & _ & _ & Hend)].
  iDestruct "Hσ" as (h) "[_ %Hs]". destruct Hs as (_ & _ & Hr & _).
  destruct (R.address_space _ _ Hr eb reg (proj1 Hl)) as [Hb He].
  iPureIntro. exists reg. split; [exact Hl|]. cbn in Hend. repeat split; lia.
Qed.

(** A four-byte write check on errno's address succeeds without using
    any ownership. *)
Lemma wp_dci_errno_check f e ls l d mode v rest j Φ :
  value_x ge e P v = Some (WPtr (mkPtr eb (Obj eb))) ->
  ▷ WP (ERun (mkFrame f (put d (WPtr (mkPtr eb (Obj eb))) e) ls None (Exec l rest j)) : gexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check 0 4 mode 1) [v] :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hv. iIntros "HK".
  iApply (wp_read_with registry (os_wi w0) ge True%I (dci_errno_mem eb) _ _ [] with "[] [HK]").
  - iIntros (σ) "Hσ _". iApply (dci_errno_mem_facts with "Hσ").
  - intros m fuel (reg & Hl & Hb & Hend & He).
    apply rule_let with (classes := [P]) (xs := [WPtr (mkPtr eb (Obj eb))]);
      [reflexivity | reflexivity | cbn; rewrite Hv; reflexivity |].
    apply op_check. cbn [ptr_addr ptr_cap]. unfold raw_address.
    rewrite Z.add_0_r Z.mod_small; [|lia].
    apply (access_obj _ _ reg); [exact (proj1 Hl)|lia|lia|apply Z.mod_1_r].
  - done.
  - iNext. iIntros "_". iExact "HK".
Qed.

(** Storing a saved 32-bit value writes exactly its four bytes into
    errno and changes nothing else that the caller owns. *)
Lemma wp_dci_errno_store f e ls l a x s rest j bs Φ :
  value_x ge e A a = Some (WPtr (mkPtr eb (Obj eb))) -> value_x ge e W x = Some (WInt s) ->
  length bs = 4%nat ->
  bytes eb 0 bs -∗
  ▷ (bytes eb 0 (le_bytes s 4) -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Ww 0 x a :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Ha Hx Hlen. iIntros "Hb HK".
  iApply (wp_write_with registry (os_wi w0) ge True%I (dci_errno_mem eb)
    (byte_ps eb 0 bs) (byte_ps eb 0 (le_bytes s 4)) _ _ [] (fun m => store_bytes m eb 4 s) with "Hb [] [HK]").
  - rewrite !byte_ps_keys length_le_bytes Hlen. reflexivity.
  - iIntros (σ) "Hσ _". iApply (dci_errno_mem_facts with "Hσ").
  - intros m fuel (Hbs & Hd & _) (reg & Hl & Hb & Hend & He).
    destruct (store_after m eb reg 0 bs s Hd Hl Hbs) as [Hnew Hframe].
    rewrite Hlen Z.add_0_r in Hnew, Hframe. cbn in Hnew, Hframe.
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store with (vk := W) (x := WInt s) (p := mkPtr eb (Obj eb));
        [reflexivity|exact Hx|exact Ha|].
      cbn - [access_res raw_address store_bytes]. unfold raw_address. rewrite Z.add_0_r Z.mod_small; [|lia].
      rewrite (access_obj _ _ reg); [reflexivity|exact (proj1 Hl)|lia|lia|apply Z.mod_1_r].
    + apply store_bytes_kept. intros y Hy. exists eb, reg. split; [exact (proj1 Hl)|lia].
    + exact Hnew.
    + rewrite byte_ps_keys Hlen in Hframe.
      rewrite byte_ps_keys length_le_bytes. exact Hframe.
  - intros m w h Hps Hw. apply (os_wi_store w0 m); [reflexivity| |exact Hw].
    intros key v Hin. apply byte_ps_elem in Hin as (i & y & Hi & -> & ->). done.
  - done.
  - iNext. iIntros "Hb _". iApply ("HK" with "Hb").
Qed.

(** ## The untranslated return *)

(** The lookup releases a read lock with __GI___pthread_rwlock_unlock.
    This module does not prove that function, so a caller supplies a rule
    for each lock lk. The rule takes U and gives back U' with some
    integer result, which the lookup ignores. *)
Definition dci_unlock_rule (lk : ptr) (U U' : iProp Σ) : Prop :=
  forall f e ls l d args rest j Φ, map_option (arg_x ge e) args = Some [WPtr lk] ->
    ⊢ U -∗ ▷ (∀ x, U' -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_unlock")) args :: rest) j)) : gexpr) {{ Φ }}.

(** The block runs after the C-locale test sends the lookup to
    `c: return_untranslated`. The slot of the directory string holds
    null, so the first free does nothing. The other two frees release the
    domain-file string and the locale-name string. The block then
    releases the state lock and the setlocale lock in that order, stores
    the saved errno value s back, and returns the message id. *)
Lemma wp_dci_exit_fr e xs xsreg xd xreg sl sreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  dci_free_rule -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) -> lookup (TAtom "v254") e = Some (WPtr (mkPtr sl (Obj sl))) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 ->
  r_kind xreg = Heap -> 0 < xd < 2 ^ 64 -> r_kind sreg = Heap -> 0 < sl < 2 ^ 64 ->
  live xs xsreg -∗ pcell xs 0 null -∗ live xd xreg -∗ live sl sreg -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L205") (Some (TAtom "L356")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros [Hfn Hfl] Hge Hlk1 Hlk2 Hu1 Hu2 Hv17 Hc0 Hv232 Hv254 Hv69 Hs Hv6 Hv2
    Hxs0 Hxs8 Hxsend Hxsr Hxk Hxd Hsk Hsl.
  iIntros "Hxl Hxc Hdl Hsl HU1 HU2 Herr HK".
  step. check "Hxl". load_null "Hxl" "Hxc".
  iApply Hfn; [vx |]. iNext.
  iApply (Hfl with "Hdl"); [vx | exact Hxk | lia |]. iNext.
  iApply (Hfl with "Hsl"); [vx | exact Hsk | lia |]. iNext. step_global Hlk1.
  iApply (Hu1 with "HU1"); [vx |]. iNext. iIntros (x1) "HU1".
  step_global Hlk2.
  iApply (Hu2 with "HU2"); [vx |]. iNext. iIntros (x2) "HU2".
  step_global Hge.
  iApply wp_dci_errno_check; [vx |]. iNext.
  iDestruct "Herr" as (cs [Hbs Hcs]) "Hp". rewrite pts_app. iDestruct "Hp" as "[Hb Haux]".
  iApply (wp_dci_errno_store with "Hb"); [vx | vx | exact Hbs |]. iNext. iIntros "Hb".
  step. branch. step.
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" with "Hxl Hxc HU1 HU2 [Hb Haux]").
  iExists cs. rewrite pts_app. iSplitR; [iPureIntro; rewrite length_le_bytes; auto|].
  iFrame "Haux". rewrite (Z.mod_small s); [iExact "Hb" | lia].
Qed.

(** The older statement takes the model's free, which meets the rule. *)
Lemma wp_dci_exit e xs xsreg xd xreg sl sreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  heap_fns ge -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) -> lookup (TAtom "v254") e = Some (WPtr (mkPtr sl (Obj sl))) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 ->
  r_kind xreg = Heap -> 0 < xd < 2 ^ 64 -> r_kind sreg = Heap -> 0 < sl < 2 ^ 64 ->
  live xs xsreg -∗ pcell xs 0 null -∗ live xd xreg -∗ live sl sreg -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L205") (Some (TAtom "L356")))) : gexpr) {{ Φ }}.
Proof using Type*. intros Hh. apply wp_dci_exit_fr, dci_free_rule_heap, Hh. Qed.
End rules.

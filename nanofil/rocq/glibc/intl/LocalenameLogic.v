From Glibc Require Import GlibcProgram.
(** glibc's `c: __current_locale_name` returns the name of one category
    of the calling thread's locale. The gettext lookup calls it to learn
    which catalog to open. This module proves the captured body.

    To read the name, the function follows two pointers, and each read
    must stay inside a live object. It first reads the thread's locale
    pointer from a cell that nanofil keeps as the global
    __libc_tsd_LOCALE. It then reads entry category of the table of
    names that starts 128 bytes into the locale. The caller lends a share
    of both cells, of both objects' lifetimes, and of the lifetime of the
    name that the second read checks, and the proof gives each share back
    unchanged.

    The caller decides which locale the thread uses and what its names
    say. This module proves only that the function returns the name that
    the lent entry holds. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic LocalenameCode.
From Glibc Require WordString.
From Glibc Require Import StrlenBits.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance loc_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup of category cat reads the thread's locale cell, entry cat of
    the locale's table of names, and the lifetimes of the locale object
    and of the name. This resource holds a share of each. The locale cell
    lies at offset go of object gb and holds lp, which points into object
    lb, and the entry holds cv. *)
Definition locale_name_res (dqg : dfrac) (gb go : Z) (greg : region) (lp : ptr) (dql : dfrac) (lb : Z)
    (lreg : region) (dqn : dfrac) (cat : Z) (cv : ptr) (dqt : dfrac) (treg : region) : iProp Σ :=
  liveq dqg gb greg ∗ pcellq dqg gb go lp ∗ liveq dql lb lreg ∗
  pcellq dqn lb (ptr_addr lp - lb + 128 + 8 * cat) cv ∗ live_capq dqt (ptr_cap cv) treg.

(** ## The lookup

    The locale cell must be the global the code names, and both cells
    must be aligned and lie inside their regions. The category must be
    one of the 13 entries of the table. *)

(** The body returns the name that entry cat holds. *)
Lemma wp_glibc_current_locale_name e cat gb go greg dqg lp lb lreg dql dqn cv treg dqt Φ :
  lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (mkPtr (gb + go) (Obj gb)) ->
  lookup (TAtom "v0") e = Some (WInt cat) -> 0 <= cat < 13 ->
  0 < gb -> 0 <= go -> (gb + go) mod 8 = 0 -> gb + go + 8 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  (ptr_cap lp = Obj lb \/ ptr_cap lp = Ro lb) -> 0 < lb <= ptr_addr lp -> ptr_addr lp mod 8 = 0 ->
  ptr_addr lp + 128 + 8 * cat + 8 <= r_end lreg -> r_end lreg <= 2 ^ 48 ->
  0 <= ptr_addr cv < 2 ^ 64 ->
  liveq dqg gb greg -∗ pcellq dqg gb go lp -∗ liveq dql lb lreg -∗
  pcellq dqn lb (ptr_addr lp - lb + 128 + 8 * cat) cv -∗ live_capq dqt (ptr_cap cv) treg -∗
  (liveq dqg gb greg -∗ pcellq dqg gb go lp -∗ liveq dql lb lreg -∗
   pcellq dqn lb (ptr_addr lp - lb + 128 + 8 * cat) cv -∗ live_capq dqt (ptr_cap cv) treg -∗ Φ (Ret (WPtr cv))) -∗
  WP (ERun (mkFrame glibc_current_locale_name e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hg Hv0 Hcat Hgb Hgo Hgal Hgend Hgreg Hlc Hlb Hlal Hlend Hlreg Hcv.
  iIntros "Hgl Hgc Hll Hnc Hct HK".
  step. step_global Hg.
  iApply (wp_check_read_dq with "Hgl"); [reflexivity | vx | left; reflexivity | ar | ar | ar |]. iNext. iIntros "Hgl".
  iAssert (live_capq dql (ptr_cap lp) lreg) with "[Hll]" as "Hll".
  { destruct Hlc as [-> | ->]; iExact "Hll". }
  iApply (wp_raw_load_pointer_dq with "Hgl Hgc Hll"); [reflexivity | vx | left; reflexivity | ar | exact Hgal | lia |].
  iNext. iIntros "Hgl Hgc Hll".
  destruct lp as [la lc]. cbn [ptr_addr ptr_cap] in *.
  step. step. step. step. cbn [ptr_addr ptr_cap].
  assert (Ea : (((la mod 2 ^ 64 + 128 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 +
     (((sign_extension (2 ^ 32) (2 ^ 31) (cat mod 2 ^ 32) mod 2 ^ 64) mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64))
      mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 = la + 128 + 8 * cat).
  { rewrite (Z.mod_small cat (2 ^ 32)); [|lia].
    replace (sign_extension (2 ^ 32) (2 ^ 31) cat) with cat
      by (unfold sign_extension; rewrite Z.mod_small; [|lia]; replace (2 ^ 31 <=? cat) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
    change ((3 mod 2 ^ 32) mod 64) with 3. change (2 ^ 3) with 8. change (128 mod 2 ^ 64) with 128.
    rewrite !(Z.mod_small cat); try lia. rewrite (Z.mod_small la); [|lia]. rewrite !Z.mod_small; lia. }
  rewrite Ea.
  iAssert (liveq dql lb lreg) with "[Hll]" as "Hll". { destruct Hlc as [-> | ->]; iExact "Hll". }
  iApply (wp_check_read_dq with "Hll"); [reflexivity | vx | exact Hlc | | | |];
    try (unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r (Z.mod_small (la + 128 + 8 * cat) (2 ^ 64)); [|lia];
         first [lia | Z.div_mod_to_equations; lia]).
  iNext. iIntros "Hll".
  iApply (wp_raw_load_pointer_dq with "Hll Hnc Hct"); [reflexivity | vx | exact Hlc | unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia |
    Z.div_mod_to_equations; lia | exact Hcv |].
  iNext. iIntros "Hll Hnc Hct".
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" with "Hgl Hgc Hll Hnc Hct").
Qed.

(** A call of a name bound to the captured body passes the category and
    resumes the caller with the name and the same resource. *)
Lemma wp_call_glibc_current_locale_name f e ls l d g args rest j cat gb go greg dqg lp lb lreg dql dqn cv treg dqt Φ :
  map_option (arg_x ge e) args = Some [WInt cat] -> find_fn ge g = Some (Defined glibc_current_locale_name) ->
  lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (mkPtr (gb + go) (Obj gb)) -> 0 <= cat < 13 ->
  0 < gb -> 0 <= go -> (gb + go) mod 8 = 0 -> gb + go + 8 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  (ptr_cap lp = Obj lb \/ ptr_cap lp = Ro lb) -> 0 < lb <= ptr_addr lp -> ptr_addr lp mod 8 = 0 ->
  ptr_addr lp + 128 + 8 * cat + 8 <= r_end lreg -> r_end lreg <= 2 ^ 48 -> 0 <= ptr_addr cv < 2 ^ 64 ->
  locale_name_res dqg gb go greg lp dql lb lreg dqn cat cv dqt treg -∗
  ▷ (locale_name_res dqg gb go greg lp dql lb lreg dqn cat cv dqt treg -∗
     WP (ERun (mkFrame f (put d (WPtr cv) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call (CResult d P) (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hg Hgl Hcat Hgb Hgo Hgal Hgend Hgreg Hlc Hlb Hlal Hlend Hlreg Hcv.
  iIntros "(Hgl & Hgc & Hll & Hnc & Hct) HK".
  iApply wp_call_bind; [exact Hargs | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_current_locale_name with "Hgl Hgc Hll Hnc Hct"); first [exact Hgl | reflexivity | eassumption | idtac].
  iIntros "Hgl Hgc Hll Hnc Hct". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "[$Hgl $Hgc $Hll $Hnc $Hct]").
Qed.

(** A caller cannot claim one name while the table holds another. When
    two shares describe the same entry, they agree on the pointer it
    holds. *)
Lemma locale_name_entry_agree dq1 dq2 lb o cv cv' : 0 <= ptr_addr cv < 2 ^ 64 -> 0 <= ptr_addr cv' < 2 ^ 64 ->
  pcellq dq1 lb o cv -∗ pcellq dq2 lb o cv' -∗ ⌜cv = cv'⌝.
Proof using Type.
  intros H1 H2. iIntros "A B". iDestruct (WordString.ptsq_agree with "A B") as %E; [reflexivity|].
  iPureIntro. destruct cv as [a c], cv' as [a' c']. cbn in H1, H2, E.
  injection E as Ec E0 E1 E2 E3 E4 E5 E6 E7. subst c'. f_equal.
  rewrite <- (of_bytes_byte_of a H1), <- (of_bytes_byte_of a' H2). cbn [map idx8].
  rewrite E0 E1 E2 E3 E4 E5 E6 E7. reflexivity.
Qed.
End rules.

(** ## Controls

    These examples check that the proof follows the code the compiler
    produced. The captured body has one block, which names one global,
    calls no function and loads two pointers. The message category is
    entry 5, which lies 168 bytes into the locale object because 13 data
    pointers and three table pointers come before the names table. *)
Definition loc_insts : list inst :=
  match fn_blocks glibc_current_locale_name with b :: _ => b_insts b | [] => [] end.
Definition inst_globals (i : inst) : list name :=
  match i with
  | Let _ _ _ args => flat_map (fun v => match v with Global s => [s] | _ => [] end) args
  | Call _ (Global s) _ | RawCall _ (Global s) _ => [s]
  | _ => []
  end.
Example localename_shape :
  length (fn_blocks glibc_current_locale_name) = 1%nat /\
  flat_map inst_globals loc_insts = [TAtom "__libc_tsd_LOCALE"] /\
  length (filter (fun i => match i with Let _ _ (RawLoadPointer _ _) _ => true | _ => false end) loc_insts) = 2%nat /\
  existsb (fun i => match i with Call _ _ _ | RawCall _ _ _ => true | _ => false end) loc_insts = false.
Proof. vm_compute. repeat split. Qed.
(** The two constants of the address computation are the table offset
    128 and the shift 3, which scales the category to 8-byte entries, and
    the block returns the second loaded pointer v9. *)
Definition inst_consts (i : inst) : list Z :=
  match i with
  | Let _ _ _ args => flat_map (fun v => match v with Const n => [n] | _ => [] end) args
  | Flight _ _ args _ => flat_map (fun a => match a with FValue (Const n) => [n] | _ => [] end) args
  | _ => []
  end.
Example localename_consts :
  flat_map inst_consts loc_insts = [128; 3] /\
  match fn_blocks glibc_current_locale_name with b :: _ => Validate.jump_uses (b_jump b) | [] => [] end = [TAtom "v9"].
Proof. vm_compute. split; reflexivity. Qed.
Example localename_offset : 8 * 13 + 3 * 8 = 128 /\ 128 + 8 * 5 = 168.
Proof. split; reflexivity. Qed.

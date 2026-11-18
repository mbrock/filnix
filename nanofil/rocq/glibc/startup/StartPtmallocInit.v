(** This module proves the contract of `c: __ptmalloc_init`, stated in
    [StartPtmallocInitSpec](StartPtmallocInitSpec.v), over the
    function's compiled body. The allocator must be ready before any
    constructor or `c: main` asks for memory, and its set-up reads
    randomness, the clock and ten tunables, so this is the longest body
    in early initialization.

    ## How the proof follows the body

    The body has two loops and a long straight run of tunable reads. The
    proof gives each loop its own lemma, gives the run of reads and the
    final threshold checks a third, and joins them in the order the body
    runs them. Each piece takes the contracts of its callees as
    assumptions, so the proof never imports how a callee was proved. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import HiAtexitTypedPT.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import HiAtexitModule OsBlocks OsWorld OsGetrandom OsClockGettime FileInv LibioLogic LibioCloseSteps StartCode StartLogic
  StartTunableGetValSpec StartTunableIsInitializedSpec StartClockGettimeSpec StartPtmallocInitSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: __ptmalloc_init`. *)
Definition start_ptmalloc_init_fn : func := hi_fn___ptmalloc_init.

(** The image defines `c: __ptmalloc_init` with that body. *)
Lemma start_ptmalloc_init_defined :
  find_direct (TAtom "__ptmalloc_init") hi_module = Some (Defined start_ptmalloc_init_fn).
Proof. vm_compute. reflexivity. Qed.

(** ## What the loops leave alone

    The function allocates its ten locals before its two loops and reads
    them after both. Each loop overwrites only its own temporaries, so
    the relation [keeps] below says that the locals' entries in the
    environment are unchanged. *)

(** This list names the locals that the loops must keep. *)
Definition pm_names : list name :=
  map TAtom ["v10"; "v12"; "v17"; "v22"; "v27"; "v32"; "v37"; "v42"; "v47"; "v52"; "v57"].

(** The environment e' gives every name in ns the entry that e gives it. *)
Definition keeps (ns : list name) (e e' : list (name * word)) : Prop :=
  Forall (fun n => lookup n e' = lookup n e) ns.

(** Every environment keeps its own entries. *)
Lemma keeps_refl ns e : keeps ns e e.
Proof. apply Forall_forall. reflexivity. Qed.

(** Keeping entries is transitive. *)
Lemma keeps_trans ns e1 e2 e3 : keeps ns e1 e2 -> keeps ns e2 e3 -> keeps ns e1 e3.
Proof.
  unfold keeps. rewrite !Forall_forall. intros H1 H2 n Hn. rewrite (H2 n Hn). exact (H1 n Hn).
Qed.

(** Writing a name outside ns keeps the entries of ns. *)
Lemma keeps_put ns e e' n v :
  forallb (fun k => negb (name_eqb k n)) ns = true -> keeps ns e e' -> keeps ns e (put n v e').
Proof.
  unfold keeps. rewrite forallb_forall !Forall_forall. intros Hn H k Hk.
  rewrite Symbolic.lookup_after_put_other; [exact (H k Hk)|].
  specialize (Hn k Hk). destruct (name_eqb k n); [discriminate | reflexivity].
Qed.

(** This tactic proves that a run of writes keeps the entries. *)
Ltac keeps_tac := repeat (apply keeps_put; [reflexivity|]); apply keeps_refl.

(** The body passes one of these callbacks with each of its ten tunable
    reads. *)
Definition pm_callbacks : list string :=
  map (fun s => "glibc_malloc#_dl_tunable_set_" ++ s)%string
    ["top_pad"; "perturb_byte"; "mmap_threshold"; "trim_threshold"; "mmaps_max"; "arena_max"; "arena_test";
     "tcache_max"; "tcache_count"; "hugetlb"].

(** The body keeps ten small locals on the heap, one for each tunable it
    reads. This predicate says which temporary holds each local's address. *)
Definition pm_env (e : list (name * word)) (b12 b17 b22 b27 b32 b37 b42 b47 b52 b57 : Z) : Prop :=
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b12 (Obj b12))) /\ lookup (TAtom "v17") e = Some (WPtr (mkPtr b17 (Obj b17))) /\
  lookup (TAtom "v22") e = Some (WPtr (mkPtr b22 (Obj b22))) /\ lookup (TAtom "v27") e = Some (WPtr (mkPtr b27 (Obj b27))) /\
  lookup (TAtom "v32") e = Some (WPtr (mkPtr b32 (Obj b32))) /\ lookup (TAtom "v37") e = Some (WPtr (mkPtr b37 (Obj b37))) /\
  lookup (TAtom "v42") e = Some (WPtr (mkPtr b42 (Obj b42))) /\ lookup (TAtom "v47") e = Some (WPtr (mkPtr b47 (Obj b47))) /\
  lookup (TAtom "v52") e = Some (WPtr (mkPtr b52 (Obj b52))) /\ lookup (TAtom "v57") e = Some (WPtr (mkPtr b57 (Obj b57))) /\
  Forall (fun b => 0 < b /\ b mod 16 = 0 /\ b + 16 <= 2 ^ 48) [b12; b17; b22; b27; b32; b37; b42; b47; b52; b57].

(** Kept entries keep the locals. *)
Lemma pm_env_keeps e e' b12 b17 b22 b27 b32 b37 b42 b47 b52 b57 :
  keeps pm_names e e' -> pm_env e b12 b17 b22 b27 b32 b37 b42 b47 b52 b57 ->
  pm_env e' b12 b17 b22 b27 b32 b37 b42 b47 b52 b57.
Proof.
  unfold keeps. rewrite Forall_forall. intros Hk H. unfold pm_env in *.
  rewrite !Hk; [exact H | cbn; tauto ..].
Qed.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hsize : !HasSpec registry (os_wi w0) ge (TAtom "__tunable_get_val") tunable_size_spec}.
Context `{Hint : !HasSpec registry (os_wi w0) ge (TAtom "__tunable_get_val") tunable_int_spec}.
Context `{Hinit : !HasSpec registry (os_wi w0) ge (TAtom "__tunable_is_initialized") tunable_is_initialized_spec}.
Context `{Hclock : !HasSpec registry (os_wi w0) ge (TAtom "__GI___clock_gettime") clock_gettime_spec}.
Context (Hrand : registry (TAtom "zsys_getrandom") = Some os_getrandom_contract).
Context (Hrand_ext : os_ext ge "zsys_getrandom").
Context (Hcbs : Forall (fun n => exists p, lookup (TAtom n) (ge_globals ge) = Some p) pm_callbacks).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Ltac pm_alloc b H Ho :=
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (b H) Ho.

(** This tactic runs one inlined call of `c: clock_gettime` on a fresh
    buffer and the two loads of the buffer that follow it. *)
Ltac pm_clock Herr eb :=
  let b0 := fresh "b" in let Hb0 := fresh "Hb" in
  pm_alloc b0 Hb0 "Ho0";
  iDestruct (obj_blk_any with "Ho0") as "[Lb0 Hb0]"; [vm_compute; congruence|];
  change (req_extent (heap_req 8 (16 mod 2 ^ 64))) with 16 in *;
  change (req_kind (heap_req 8 (16 mod 2 ^ 64))) with Heap in *;
  call_spec with (1, b0, mkRegion b0 (b0 + 16) Heap Live, eb);
  [unfold timespec_size; split_and!; [lia | lia | exact Herr | cbn; lia] |];
  let k := fresh "k" in let Hk := fresh "Hk" in
  iDestruct "Hpost" as (k [-> Hk]) "(Lb0 & Hb0 & Herr)"; iExists _; iSplit; [done|]; iNext;
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at];
  let breg := fresh "breg" in let Ebreg := fresh "Ebreg" in let Hbr := fresh "Hbr" in
  remember (mkRegion b0 (b0 + 16) Heap Live) as breg eqn:Ebreg;
  assert (Hbr : r_end breg = b0 + 16) by (rewrite Ebreg; reflexivity);
  let B0 := fresh "B0" in let B48 := fresh "B48" in
  iApply (wp_live_fit1 with "Lb0"); iIntros ([B0 B48]) "Lb0";
  let zs := fresh "zs" in let zc := fresh "zc" in let Hzl := fresh "Hzl" in let Hzc := fresh "Hzc" in
  iDestruct "Hb0" as (zs zc [Hzl Hzc]) "Hb0"; rewrite pts_app; iDestruct "Hb0" as "[Hb0 _]";
  iAssert (bytes b0 0 (take 8 zs ++ drop 8 zs)) with "[Hb0]" as "Hb0"; [rewrite take_drop; iExact "Hb0"|];
  rewrite bytes_app; iDestruct "Hb0" as "[Hlo Hhi]";
  rewrite length_take; replace (Z.of_nat (8 `min` length zs)) with 8 by (rewrite Hzl; reflexivity);
  step; check "Lb0";
  iApply (wp_raw_load_long_bytes with "Lb0 Hhi"); [reflexivity | vx | rewrite length_drop Hzl; reflexivity
    | left; reflexivity | a2 |]; iNext; iIntros "Lb0 Hhi";
  check "Lb0";
  iApply (wp_raw_load_long_bytes with "Lb0 Hlo"); [reflexivity | vx | rewrite length_take Hzl; reflexivity
    | left; reflexivity | a2 |]; iNext; iIntros "Lb0 Hlo";
  iClear "Lb0 Hlo Hhi".

(** This tactic moves into the next block when the values it starts from
    are already known. *)
Ltac enter := iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]].

(** This tactic hands the loop back to its retry block. *)
Ltac pm_retry := iApply ("Hretry" with "[%] Ltk [Htkb Htka] Herr HK");
  [keeps_tac | iExists _, _; iSplitR; last first; [rewrite pts_app; iFrame "Htkb Htka" | iPureIntro; split; assumption]].

(** This tactic runs one population count of the key and its test. *)
Ltac pm_popcount G Hxl := enter; step_global G; check "Ltk";
  iApply (wp_raw_load_long_bytes with "Ltk Htkb"); [reflexivity | vx | exact Hxl | left; reflexivity | a2 |];
  iNext; iIntros "Ltk Htkb"; do 13 step; enter; step; step.

(** ## The random key

    The per-thread cache tags freed chunks with a random key, so that a
    double free is caught. The body asks `c: getrandom` for eight bytes
    and then, until the key looks random enough, mixes two clock
    readings into it. Nothing bounds the number of retries, so the
    lemma below holds for any number of them. *)

(** The key loop always finishes. When it does, the eight bytes of the key
    are still owned and the locals are unchanged. *)
Lemma pm_key_loop tk tkreg eb Φ :
  lookup (TAtom "glibc_malloc#tcache_key") (ge_globals ge) = Some (mkPtr tk (Obj tk)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> tk + 8 <= r_end tkreg ->
  ⊢ ∀ e from, live tk tkreg -∗ blk_any tk 0 8 -∗ errno_any eb -∗
    (∀ e', ⌜keeps pm_names e e'⌝ -∗ live tk tkreg -∗ blk_any tk 0 8 -∗ errno_any eb -∗
       WP (ERun (mkFrame start_ptmalloc_init_fn e' [] None (Enter (TAtom "iw_1.join") (Some (TAtom "iw_1.L38")))) : sexpr)
         {{ Φ }}) -∗
    WP (ERun (mkFrame start_ptmalloc_init_fn e [] None (Enter (TAtom "iw_1.L12") from)) : sexpr) {{ Φ }}.
Proof using Hclock.
  intros Gtk Herr Btk. iLöb as "IH". iIntros (e from) "Ltk Htk Herr HK".
  iApply (wp_live_fit1 with "Ltk"). iIntros ([T0 T48]) "Ltk".
  iAssert (□ ∀ e1, ⌜keeps pm_names e e1⌝ -∗ live tk tkreg -∗ blk_any tk 0 8 -∗ errno_any eb -∗
    (∀ e', ⌜keeps pm_names e e'⌝ -∗ live tk tkreg -∗ blk_any tk 0 8 -∗ errno_any eb -∗
       WP (ERun (mkFrame start_ptmalloc_init_fn e' [] None (Enter (TAtom "iw_1.join") (Some (TAtom "iw_1.L38")))) : sexpr)
         {{ Φ }}) -∗
    WP (ERun (mkFrame start_ptmalloc_init_fn e1 [] None (Enter (TAtom "iw_1.L13") (Some (TAtom "iw_1.L38")))) : sexpr)
      {{ Φ }})%I as "#Hretry".
  { iIntros "!>" (e1 He1) "Ltk Htk Herr HK".
    iApply wp_enter; [reflexivity | reflexivity | iNext].
    step_global Gtk. pm_clock Herr eb.
    do 9 step.
    iDestruct "Htk" as (ts tc [Htl Htc]) "Htk". rewrite pts_app. iDestruct "Htk" as "[Htkb Htka]".
    iApply (wp_live_fit1 with "Ltk"). iIntros ([T0' T48']) "Ltk".
    check "Ltk".
    iApply (wp_raw_store_long_bytes with "Ltk Htkb"); [vx | vx | reflexivity | a2 | exact Htl | wi_store |].
    iNext. iIntros "Ltk Htkb".
    step_global Gtk. step_global Gtk. check "Ltk".
    iApply (wp_raw_load_long_bytes with "Ltk Htkb"); [reflexivity | vx | apply length_le_bytes | left; reflexivity | a2 |].
    iNext. iIntros "Ltk Htkb". step.
    pm_clock Herr eb.
    do 10 step.
    check "Ltk".
    iApply (wp_raw_store_long_bytes with "Ltk Htkb"); [vx | vx | reflexivity | a2 | apply length_le_bytes | wi_store |].
    iNext. iIntros "Ltk Htkb".
    iApply wp_goto. iNext. cbn [edge_label].
    iApply ("IH" with "Ltk [Htkb Htka] Herr").
    { iExists _, tc. iSplitR; last first; [rewrite pts_app; iFrame "Htkb Htka" | iPureIntro; rewrite length_le_bytes; done]. }
    iIntros (e') "%He' Ltk Htk Herr". iApply ("HK" with "[%] Ltk Htk Herr").
    eapply keeps_trans; [exact He1 | eapply keeps_trans; [| exact He']]. keeps_tac.
  }
  iApply wp_enter; [reflexivity | destruct from; reflexivity | iNext].
  iDestruct "Htk" as (xs cs [Hxl Hcl]) "Htk". rewrite pts_app. iDestruct "Htk" as "[Htkb Htka]".
  step_global Gtk. check "Ltk".
  iApply (wp_raw_load_long_bytes with "Ltk Htkb"); [reflexivity | vx | exact Hxl | left; reflexivity | a2 |].
  iNext. iIntros "Ltk Htkb". step.
  branch_cases.
  - (* The key is above the small range. *)
    enter. step_global Gtk. check "Ltk".
    iApply (wp_raw_load_long_bytes with "Ltk Htkb"); [reflexivity | vx | exact Hxl | left; reflexivity | a2 |].
    iNext. iIntros "Ltk Htkb". step. step. enter. branch_cases.
    + pm_popcount Gtk Hxl. enter. branch_cases.
      * pm_popcount Gtk Hxl. enter. branch_cases.
        -- (* All three tests passed: the loop ends. *)
           iApply ("HK" with "[%] Ltk [Htkb Htka] Herr");
             [keeps_tac | iExists _, _; iSplitR; last first; [rewrite pts_app; iFrame "Htkb Htka" | iPureIntro; split; assumption]].
        -- pm_retry.
      * enter. branch. pm_retry.
    + enter. branch. enter. branch. pm_retry.
  - enter. branch. enter. branch. enter. branch. pm_retry.
Qed.

(** A value below the sign bit reads as itself. *)
Lemma sign_extension_low m h u : 0 <= u < h -> h <= m -> sign_extension m h u = u.
Proof using Type.
  intros Hu Hm. unfold sign_extension. rewrite Z.mod_small; [|lia].
  destruct (Z.leb_spec h u); lia.
Qed.

(** ## The main arena's bins

    Each of the main arena's 127 bins is a doubly linked list whose head
    starts out pointing at itself. The loop writes both links of every
    bin and touches nothing else. *)

(** The loop over the bins starts each round at this block of the body. *)
Definition pm_L4 : block := Eval vm_compute in
  match find_block (TAtom "iw_2.L4") (fn_blocks start_ptmalloc_init_fn) with
  | Some b => b | None => mkBlock (TAtom "iw_2.L4") [] [] JRetVoid end.

(** From bin i on, the loop links every remaining bin to itself and
    leaves at its exit with the locals kept. *)
Lemma pm_bins_loop ma mareg Φ :
  ma mod 8 = 0 -> ma + 2056 <= r_end mareg ->
  ⊢ ∀ i e, ⌜1 <= i <= 128 /\ lookup (TAtom "iw_2.pr.1") e = Some (WInt i) /\
            lookup (TAtom "v10") e = Some (WPtr (mkPtr ma (Obj ma)))⌝ -∗
    live ma mareg -∗ pm_bins ma -∗
    (∀ e', ⌜keeps pm_names e e'⌝ -∗ live ma mareg -∗ pm_bins ma -∗
       WP (ERun (mkFrame start_ptmalloc_init_fn e' [] None (Enter (TAtom "iw_2.L7") (Some (TAtom "iw_2.L4"))))
             : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame start_ptmalloc_init_fn e [] None (Exec (TAtom "iw_2.L4") (b_insts pm_L4) (b_jump pm_L4)))
          : sexpr) {{ Φ }}.
Proof using Type.
  intros Ama Bma. iLöb as "IH". iIntros (i e (Hi & Hpr & Hv10)) "Lma Hbins HK".
  iApply (wp_live_fit1 with "Lma"). iIntros ([M0 M48]) "Lma".
  cbn [pm_L4 b_insts b_jump]. step.
  destruct (Z.lt_ge_cases i 128) as [Hlt|Hge].
  - branch_as false. step. do 9 step. norm.
    change (2 ^ (1 mod 32)) with 2. norm.
    rewrite sign_extension_low; [| lia | lia]. change (2 ^ (3 mod 64)) with 8. norm.
    iDestruct (big_sepL_lookup_acc (fun _ k => ∃ x, pcell ma (24 + 8 * k) x)%I (seqZ 0 254) (Z.to_nat (2 * i - 1)) (2 * i - 1) with "Hbins")
      as "[[%x1 Hc1] Hcl1]"; [rewrite lookup_seqZ_lt; [f_equal; lia | lia] |].
    check "Lma".
    iApply (wp_raw_store_pointer with "Lma Hc1"); [vx | vx | reflexivity | a2 | a2 | wi_store |].
    iNext. iIntros "Lma Hc1". iDestruct ("Hcl1" with "[Hc1]") as "Hbins"; [iExists _; iExact "Hc1"|].
    iDestruct (big_sepL_lookup_acc (fun _ k => ∃ x, pcell ma (24 + 8 * k) x)%I (seqZ 0 254) (Z.to_nat (2 * i - 2)) (2 * i - 2) with "Hbins")
      as "[[%x0 Hc0] Hcl0]"; [rewrite lookup_seqZ_lt; [f_equal; lia | lia] |].
    check "Lma".
    iApply (wp_raw_store_pointer with "Lma Hc0"); [vx | vx | reflexivity | a2 | a2 | wi_store |].
    iNext. iIntros "Lma Hc0". iDestruct ("Hcl0" with "[Hc0]") as "Hbins"; [iExists _; iExact "Hc0"|].
    step. step. step. cbn [edge_label].
    iApply ("IH" $! (i + 1) with "[%] Lma Hbins").
    { split_and!; [lia | lia | | lk_prove]. cbn -[put]. rewrite Symbolic.lookup_after_put_same. norm. reflexivity. }
    iIntros (e') "%He' Lma Hbins". iApply ("HK" with "[%] Lma Hbins").
    eapply keeps_trans; [| exact He']. keeps_tac.
  - branch_as true. iApply ("HK" with "[%] Lma Hbins"). keeps_tac.
Qed.

(** This assertion owns an eight-byte local whose contents are unknown. *)
Definition pm_loc8 (b : Z) : iProp Σ := live b (mkRegion b (b + 16) Heap Live) ∗ ∃ w, icell b 0 w.

(** This assertion owns a four-byte local whose contents are unknown. *)
Definition pm_loc4 (b : Z) : iProp Σ :=
  live b (mkRegion b (b + 16) Heap Live) ∗ ∃ xs, ⌜length xs = 4%nat⌝ ∗ bytes b 0 xs.

(** ## The tunables and the thresholds

    A user can tune the allocator through environment settings, so the
    body reads ten of them into its locals. It then checks whether huge
    pages are configured. If they are, it uses the huge page size as the
    mmap threshold unless the user chose one, and it turns off growth
    through morecore. The tactics below make
    one tunable read a single step of the proof. *)

(** This tactic reads temporaries like [vx] and then drops the wraps
    on small constants. *)
Ltac vxu := first [vx | cbn -[put];
  repeat match goal with |- context [lookup ?k ?E] =>
    let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H end;
  unwrap2; reflexivity].

(** This tactic copies the address cb of one of the callbacks. *)
Ltac pm_cb cb := lazymatch goal with
  | |- context [Exec _ (Let _ _ Copy [Global (TAtom ?n)] :: _) _] =>
      let H := fresh "Hcb" in
      destruct (proj1 (Forall_forall _ _) Hcbs n ltac:(cbn; tauto)) as [cb H]; step_global H
  end.

(** This tactic proves a bounds check on the local or global H by
    applying the rule directly, which also works after a contract call. *)
Ltac pm_chk H := iApply (wp_check with H);
  [reflexivity | vx | reflexivity | cbn [r_end]; a2 | cbn [r_end]; a2 | cbn [r_end]; a2 | iNext; iIntros H].

(** This tactic calls the function under the contract H, for logical
    input x. It is [call_spec] with the contract named, because
    `c: __tunable_get_val` has two contracts. *)
Ltac pm_call H x :=
  lazymatch type of H with HasSpec ?registry ?wi ?ge ?n ?s =>
  lazymatch goal with |- context [mkFrame ?f ?e ?ls None (Exec ?lab (Call ?r (Global ?n) ?args :: ?rest) ?j)] =>
    let rule := open_constr:(fun y => wp_call_spec registry wi ge n s (HasSpec0 := H) y f e ls lab r args rest j _) in
    call_spec_apply rule x end end.

(** Reading one size tunable is a single step with this tactic. It
    copies tunable id into the eight-byte local b and loads the local
    back. *)
Ltac pm_read_size Hs Htun tl tlreg tv id b Hl Hb Ht :=
  let cb := fresh "cb" in let w := fresh "w" in
  iRename Hl into "Lx"; iRename Hb into "Hx"; iRename Ht into "Tx";
  pm_cb cb; iDestruct "Hx" as (w) "Hx";
  pm_call Hs (id, cb, tl, tlreg, tv id, b, mkRegion b (b + 16) Heap Live, w);
  [vxu | split_and!; [exact (proj1 (Forall_forall _ _) Htun id ltac:(cbn; tauto))
                     | Z.div_mod_to_equations; lia | cbn; lia] |];
  iDestruct "Hpost" as "(-> & Ltl & Tx & Lx & Hx)"; iExists _; iSplit; [done|]; iNext;
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at];
  iApply (wp_live_fit1 with "Lx"); iIntros ([? ?]) "Lx"; pm_chk "Lx";
  iApply (wp_raw_load with "Lx Hx"); [reflexivity | vx | reflexivity | cbn [r_end]; a2 |]; iNext; iIntros "Lx Hx";
  iRename "Lx" into Hl; iRename "Tx" into Ht; iClear "Hx".

(** This tactic reads int tunable id into the four-byte local b in the
    same way. *)
Ltac pm_read_int Hs Htun tl tlreg tv id b Hl Hb Ht :=
  let cb := fresh "cb" in let xs := fresh "xs" in let Hxs := fresh "Hxs" in
  iRename Hl into "Lx"; iRename Hb into "Hx"; iRename Ht into "Tx";
  pm_cb cb; iDestruct "Hx" as (xs Hxs) "Hx";
  pm_call Hs (id, cb, tl, tlreg, tv id, b, mkRegion b (b + 16) Heap Live, xs);
  [vxu | split_and!; [exact (proj1 (Forall_forall _ _) Htun id ltac:(cbn; tauto)) | cbn; lia | exact Hxs] |];
  iDestruct "Hpost" as "(-> & Ltl & Tx & Lx & Hx)"; iExists _; iSplit; [done|]; iNext;
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at];
  iApply (wp_live_fit1 with "Lx"); iIntros ([? ?]) "Lx"; pm_chk "Lx";
  iApply (wp_raw_load_sub_bytes_dq with "Lx Hx"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | cbn [r_end]; a2 |];
  iNext; iIntros "Lx Hx"; iRename "Lx" into Hl; iRename "Tx" into Ht; iClear "Hx".

(** This tactic returns from the body and hands every resource back. *)
Ltac pm_fin := iApply wp_ret_void; iNext;
  iApply ("HK" with "[$Ltk $Leb $Lli $Laf $Lta $Lma $Lmp $Ltl] [T24 T19 T25 T14 T15 T23 T22 T17 T21 T18] Hli Hta
    [Htk Herr Haf Hma8 Hbins Hmp16 Hmp80 Hmp56]");
  [rewrite /pm_tunables; cbn [pm_size_ids pm_int_ids big_opL pm_tl]; iFrame
  |rewrite /pm_fields; cbn [pm_tk pm_eb pm_af pm_ma pm_mp]; iFrame "Htk Herr Haf Hma8 Hbins Hmp16 Hmp80"; iExists _; iExact "Hmp56"].

(** The body returns from the block after the morecore check, having
    pointed `c: thread_arena` at the main arena. *)
Lemma pm_tail o tv x t e from b12 b17 b22 b27 b32 b37 b42 b47 b52 b57 Φ :
  pm_ok o -> pm_env e b12 b17 b22 b27 b32 b37 b42 b47 b52 b57 ->
  pm_lives o -∗ pm_tunables o tv -∗ ibyte (pm_li o) 0 x -∗ pcell (pm_ta o) 0 t -∗ pm_fields o -∗
  pm_loc8 b12 -∗ pm_loc4 b17 -∗ pm_loc8 b22 -∗ pm_loc8 b27 -∗ pm_loc4 b32 -∗
  pm_loc8 b37 -∗ pm_loc8 b42 -∗ pm_loc8 b47 -∗ pm_loc8 b52 -∗ pm_loc8 b57 -∗
  (pm_lives o -∗ pm_tunables o tv -∗ ibyte (pm_li o) 0 x -∗ pcell (pm_ta o) 0 (mkPtr (pm_ma o) (Obj (pm_ma o))) -∗
     pm_fields o -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame start_ptmalloc_init_fn e [] None (Enter (TAtom "L2") from)) : sexpr) {{ Φ }}.
Proof using Hsize Hint Hinit Hcbs.
  intros Hok Henv.
  destruct o as [tk tkreg eb ereg li lireg af afreg ta tareg ma mareg mp mpreg tl tlreg].
  destruct Hok as (Gtk & Geb & Gli & Gaf & Gta & Gma & Gmp & Herr & Btk & Beb & Bli & Baf & Ata & Bta & Ama & Bma
    & Amp & Bmp & Htun). cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
    pm_mp pm_mpreg pm_tl pm_tlreg] in *.
  iIntros "(Ltk & Leb & Lli & Laf & Lta & Lma & Lmp & Ltl) Htun Hli Hta (Htk & Herr & Haf & Hma8 & Hbins & Hmp16 & Hmp56 & Hmp80)".
  iIntros "H12 H17 H22 H27 H32 H37 H42 H47 H52 H57 HK".
  cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
    pm_mp pm_mpreg pm_tl pm_tlreg].
  iApply wp_enter; [reflexivity | destruct from; reflexivity | iNext; cbn [b_insts b_jump]].
  iApply (wp_live_fit1 with "Lta"). iIntros ([A0 A48]) "Lta".
  iApply (wp_live_fit1 with "Lma"). iIntros ([M0 M48]) "Lma".
  step_global Gta. step_global Gma. check "Lta".
  iApply (wp_raw_store_pointer with "Lta Hta"); [vx | vx | reflexivity | a2 | a2 | wi_store |].
  iNext. iIntros "Lta Hta". step_global Gma. step.
  iApply wp_enter; [reflexivity | reflexivity | iNext].
  iApply (pm_bins_loop _ _ _ Ama Bma $! 1 with "[%] Lma Hbins"); [split_and!; [lia | lia | vx | lk_prove] |].
  iIntros (e1 He1) "Lma Hbins".
  destruct Henv as (E12 & E17 & E22 & E27 & E32 & E37 & E42 & E47 & E52 & E57 & Hbs).
  assert (Hk : forall n r, In n pm_names -> lookup n (put (TAtom "iw_2.pr.1") (WInt 1) (put (TAtom "v10")
    (WPtr (mkPtr ma (Obj ma))) (put (TAtom "chk16") (WPtr (mkPtr ta (Obj ta))) (put (TAtom "v9")
    (WPtr (mkPtr ma (Obj ma))) (put (TAtom "v8") (WPtr (mkPtr ta (Obj ta))) e))))) = r -> lookup n e1 = r).
  { intros n r Hn <-. exact (proj1 (Forall_forall _ _) He1 n Hn). }
  assert (V10 : lookup (TAtom "v10") e1 = Some (WPtr (mkPtr ma (Obj ma)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V12 : lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b12 (Obj b12)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V17 : lookup (TAtom "v17") e1 = Some (WPtr (mkPtr b17 (Obj b17)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V22 : lookup (TAtom "v22") e1 = Some (WPtr (mkPtr b22 (Obj b22)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V27 : lookup (TAtom "v27") e1 = Some (WPtr (mkPtr b27 (Obj b27)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V32 : lookup (TAtom "v32") e1 = Some (WPtr (mkPtr b32 (Obj b32)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V37 : lookup (TAtom "v37") e1 = Some (WPtr (mkPtr b37 (Obj b37)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V42 : lookup (TAtom "v42") e1 = Some (WPtr (mkPtr b42 (Obj b42)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V47 : lookup (TAtom "v47") e1 = Some (WPtr (mkPtr b47 (Obj b47)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V52 : lookup (TAtom "v52") e1 = Some (WPtr (mkPtr b52 (Obj b52)))) by (apply Hk; [cbn; tauto | lk_prove]).
  assert (V57 : lookup (TAtom "v57") e1 = Some (WPtr (mkPtr b57 (Obj b57)))) by (apply Hk; [cbn; tauto | lk_prove]).
  clear Hk He1 E12 E17 E22 E27 E32 E37 E42 E47 E52 E57.
  repeat match type of Hbs with Forall _ (_ :: _) => apply Forall_cons_iff in Hbs as [[? [? ?]] Hbs] end.
  step. step_global Gma. step. step. step. branch_as true.
  step. step. step. step. iDestruct "Hma8" as (x8) "Hma8". check "Lma".
  iApply (wp_raw_store_pointer with "Lma Hma8"); [vx | vx | reflexivity | a2 | a2 | wi_store |].
  iNext. iIntros "Lma Hma8".
  iDestruct "Htun" as "[Hsz Hint]". cbn [pm_size_ids pm_int_ids big_opL].
  iDestruct "Hsz" as "(T24 & T19 & T25 & T14 & T15 & T23 & T22 & T17 & _)". iDestruct "Hint" as "(T21 & T18 & _)".
  iDestruct "H12" as "[L12 H12]". iDestruct "H17" as "[L17 H17]". iDestruct "H22" as "[L22 H22]".
  iDestruct "H27" as "[L27 H27]". iDestruct "H32" as "[L32 H32]". iDestruct "H37" as "[L37 H37]".
  iDestruct "H42" as "[L42 H42]". iDestruct "H47" as "[L47 H47]". iDestruct "H52" as "[L52 H52]".
  iDestruct "H57" as "[L57 H57]".
  pm_read_size Hsize Htun tl tlreg tv 24 b12 "L12" "H12" "T24".
  pm_read_int Hint Htun tl tlreg tv 21 b17 "L17" "H17" "T21".
  pm_read_size Hsize Htun tl tlreg tv 19 b22 "L22" "H22" "T19".
  pm_read_size Hsize Htun tl tlreg tv 25 b27 "L27" "H27" "T25".
  pm_read_int Hint Htun tl tlreg tv 18 b32 "L32" "H32" "T18".
  pm_read_size Hsize Htun tl tlreg tv 14 b37 "L37" "H37" "T14".
  pm_read_size Hsize Htun tl tlreg tv 15 b42 "L42" "H42" "T15".
  pm_read_size Hsize Htun tl tlreg tv 23 b47 "L47" "H47" "T23".
  pm_read_size Hsize Htun tl tlreg tv 22 b52 "L52" "H52" "T22".
  pm_read_size Hsize Htun tl tlreg tv 17 b57 "L57" "H57" "T17".
  iDestruct "Hmp56" as (v56) "Hmp56".
  iApply (wp_live_fit1 with "Lmp"). iIntros ([P0 P48]) "Lmp".
  step_global Gmp. step. pm_chk "Lmp".
  iApply (wp_raw_load with "Lmp Hmp56"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Lmp Hmp56".
  step.
  (* The threshold read from mp_ is zero: nothing more is set. *)
  branch_cases.
  1: { enter. branch. enter. pm_fin. }
  (* The threshold is set: when it is small and the tunable was not set
     by the user, it becomes the trim threshold too. *)
  enter. step_global Gmp. step. pm_chk "Lmp".
  iApply (wp_raw_load with "Lmp Hmp56"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Lmp Hmp56".
  step. step. enter.
  cbn [edge_label]. branch_cases.
  1: { enter. pm_fin. }
  enter.
  pm_call Hinit (19, tl, tlreg, 2, tv 19); [first [vxu | exact (proj1 (Forall_forall _ _) Htun 19 ltac:(cbn; tauto))] .. | idtac].
  iDestruct "Hpost" as "(-> & Ltl & T19)". iExists _. iSplit; [done|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. step. branch. enter.
  step_global Gmp. step. pm_chk "Lmp".
  iApply (wp_raw_load with "Lmp Hmp56"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Lmp Hmp56".
  step_global Gmp. step. pm_chk "Lmp". iDestruct "Hmp16" as (v16) "Hmp16".
  iApply (wp_raw_store with "Lmp Hmp16"); [vx | vx | reflexivity | a2 | wi_store |]. iNext. iIntros "Lmp Hmp16".
  step_global Gmp. step. pm_chk "Lmp". iDestruct "Hmp80" as (xs80 Hxs80) "Hmp80".
  iApply (wp_raw_store_w with "Lmp Hmp80"); [vx | vx | reflexivity | a2 | exact Hxs80 | wi_store |]. iNext. iIntros "Lmp Hmp80".
  step. enter. iDestruct "Haf" as (yaf) "Haf".
  iApply (wp_live_fit1 with "Laf"). iIntros ([F0 F48]) "Laf".
  step_global Gaf. pm_chk "Laf".
  iApply (wp_raw_store_byte with "Laf Haf"); [vx | vx | reflexivity | a2 | wi_store |]. iNext. iIntros "Laf Haf".
  step. enter.
  iAssert (∃ v, icell mp 16 v)%I with "[Hmp16]" as "Hmp16"; [iExists _; iExact "Hmp16"|].
  iAssert (∃ xs, ⌜length xs = 4%nat⌝ ∗ bytes mp 80 xs)%I with "[Hmp80]" as "Hmp80";
    [iExists _; iFrame "Hmp80"; rewrite length_le_bytes; done|].
  iAssert (∃ y, ibyte af 0 y)%I with "[Haf]" as "Haf"; [iExists _; iExact "Haf"|].
  pm_fin.
Qed.

(** A fresh eight-byte local is a [pm_loc8]. *)
Lemma pm_loc8_fresh b : obj b (heap_req 8 (8 mod 2 ^ 64)) ⊢ pm_loc8 b.
Proof using Type.
  rewrite (obj_layout b _ [FLong; FPad 8]); [|vm_compute; congruence | reflexivity].
  iIntros "[Hl [H _]]". iSplitL "Hl"; [iExact "Hl"|]. iExists 0. iExact "H".
Qed.

(** A fresh four-byte local is a [pm_loc4]. *)
Lemma pm_loc4_fresh b : obj b (heap_req 4 (4 mod 2 ^ 64)) ⊢ pm_loc4 b.
Proof using Type.
  rewrite (obj_layout b _ [FInt; FPad 12]); [|vm_compute; congruence | reflexivity].
  iIntros "[Hl [H _]]". iSplitL "Hl"; [iExact "Hl"|]. iExists [0; 0; 0; 0]. iSplitR; [iPureIntro; reflexivity | iExact "H"].
Qed.

(** After the key loop the body reads `c: __libc_initial`. In the first
    libc of a process the flag is set, and the body then leaves the
    morecore hook in place; otherwise it disables it. Both ways continue
    with [pm_tail]. *)
Lemma pm_join o tv x t e from b12 b17 b22 b27 b32 b37 b42 b47 b52 b57 Φ :
  pm_ok o -> pm_env e b12 b17 b22 b27 b32 b37 b42 b47 b52 b57 ->
  pm_lives o -∗ pm_tunables o tv -∗ ibyte (pm_li o) 0 x -∗ pcell (pm_ta o) 0 t -∗ pm_fields o -∗
  pm_loc8 b12 -∗ pm_loc4 b17 -∗ pm_loc8 b22 -∗ pm_loc8 b27 -∗ pm_loc4 b32 -∗
  pm_loc8 b37 -∗ pm_loc8 b42 -∗ pm_loc8 b47 -∗ pm_loc8 b52 -∗ pm_loc8 b57 -∗
  (pm_lives o -∗ pm_tunables o tv -∗ ibyte (pm_li o) 0 x -∗ pcell (pm_ta o) 0 (mkPtr (pm_ma o) (Obj (pm_ma o))) -∗
     pm_fields o -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame start_ptmalloc_init_fn e [] None (Enter (TAtom "iw_1.join") from)) : sexpr) {{ Φ }}.
Proof using Hsize Hint Hinit Hcbs.
  intros Hok Henv. pose proof Hok as Hok'.
  destruct o as [tk tkreg eb ereg li lireg af afreg ta tareg ma mareg mp mpreg tl tlreg].
  destruct Hok' as (Gtk & Geb & Gli & Gaf & Gta & Gma & Gmp & Herr & Btk & Beb & Bli & Baf & Ata & Bta & Ama & Bma
    & Amp & Bmp & Htun). cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
    pm_mp pm_mpreg pm_tl pm_tlreg] in *.
  iIntros "Hlv Htun Hli Hta Hf H12 H17 H22 H27 H32 H37 H42 H47 H52 H57 HK".
  iDestruct "Hlv" as "(Ltk & Leb & Lli & Laf & Lta & Lma & Lmp & Ltl)".
  cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
    pm_mp pm_mpreg pm_tl pm_tlreg].
  iApply wp_enter; [reflexivity | destruct from; reflexivity | iNext; cbn [b_insts b_jump]].
  iApply (wp_live_fit1 with "Lli"). iIntros ([I0 I48]) "Lli".
  step_global Gli. pm_chk "Lli".
  iApply (wp_raw_load_byte with "Lli Hli"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Lli Hli". step.
  Local Ltac go Hok Henv := iApply (pm_tail with "[Ltk Leb Lli Laf Lta Lma Lmp Ltl] Htun Hli Hta Hf H12 H17 H22 H27 H32 H37 H42 H47 H52 H57 HK");
    [exact Hok | unfold pm_env in *; cbn -[put]; intuition (try lk_prove) | rewrite /pm_lives; cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
    pm_mp pm_mpreg pm_tl pm_tlreg]; iFrame].
  branch_cases.
  - go Hok Henv.
  - enter. iDestruct "Hf" as "(Htk & Herr & Haf & Hf)". iDestruct "Haf" as (y) "Haf".
    iApply (wp_live_fit1 with "Laf"). iIntros ([F0 F48]) "Laf".
    step_global Gaf. pm_chk "Laf".
    iApply (wp_raw_store_byte with "Laf Haf"); [vx | vx | reflexivity | a2 | wi_store |]. iNext. iIntros "Laf Haf".
    step. iAssert (pm_fields _) with "[Htk Herr Haf Hf]" as "Hf"; [iFrame; iExists _; iExact "Haf"|].
    go Hok Henv.
Qed.

(** The body enters the key loop from two places, and this tactic proves
    that both reach the same end. *)
Ltac pm_loop Hok0 Gtk Herr Btk :=
    iApply (pm_key_loop with "Ltk Htk Herr"); [exact Gtk | exact Herr | exact Btk |];
    iIntros (e') "%He' Ltk Htk Herr";
    iApply (pm_join with "[Ltk Leb Lli Laf Lta Lma Lmp Ltl] Htun Hli Hta [Htk Herr Haf Hma8 Hbins Hmp16 Hmp56 Hmp80]
              H12 H17 H22 H27 H32 H37 H42 H47 H52 H57 HK");
    [exact Hok0 | eapply pm_env_keeps; [eassumption | unfold pm_env; cbn -[put]; repeat split; try lk_prove; repeat (first [apply Forall_nil | apply Forall_cons]); lia]
    | rewrite /pm_lives; cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
        pm_mp pm_mpreg pm_tl pm_tlreg]; iFrame
    | rewrite /pm_fields; cbn [pm_tk pm_eb pm_af pm_ma pm_mp]; iFrame].

(** ## The whole body

    A failed `c: getrandom` must not change errno for the program, so
    the body saves errno before the call and restores it afterwards.
    Before that it makes room for its ten locals. The pieces proved
    above then run in turn. *)

(** The body satisfies the contract's pre- and postcondition. *)
Lemma wp_ptmalloc_init fr o tv x t Φ :
  call_frame start_ptmalloc_init_fn [] = Some fr ->
  pm_ok o ->
  pm_lives o -∗ pm_tunables o tv -∗ ibyte (pm_li o) 0 x -∗ pcell (pm_ta o) 0 t -∗ pm_fields o -∗
  (pm_lives o -∗ pm_tunables o tv -∗ ibyte (pm_li o) 0 x -∗ pcell (pm_ta o) 0 (mkPtr (pm_ma o) (Obj (pm_ma o))) -∗
     pm_fields o -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hsize Hint Hinit Hclock Hcbs Hrand Hrand_ext.
  intros Hfr Hok. injection Hfr as <-. pose proof Hok as Hok0.
  destruct o as [tk tkreg eb ereg li lireg af afreg ta tareg ma mareg mp mpreg tl tlreg].
  destruct Hok as (Gtk & Geb & Gli & Gaf & Gta & Gma & Gmp & Herr & Btk & Beb & Bli & Baf & Ata & Bta & Ama & Bma
    & Amp & Bmp & Htun). cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
    pm_mp pm_mpreg pm_tl pm_tlreg] in *.
  iIntros "(Ltk & Leb & Lli & Laf & Lta & Lma & Lmp & Ltl) Htun Hli Hta (Htk & Herr & Haf & Hma8 & Hbins & Hmp16 & Hmp56 & Hmp80) HK".
  cbn [pm_tk pm_tkreg pm_eb pm_ereg pm_li pm_lireg pm_af pm_afreg pm_ta pm_tareg pm_ma pm_mareg
    pm_mp pm_mpreg pm_tl pm_tlreg].
  step.
  pm_alloc b12 Hb12 "Ho12". pm_alloc b17 Hb17 "Ho17". pm_alloc b22 Hb22 "Ho22". pm_alloc b27 Hb27 "Ho27".
  pm_alloc b32 Hb32 "Ho32". pm_alloc b37 Hb37 "Ho37". pm_alloc b42 Hb42 "Ho42". pm_alloc b47 Hb47 "Ho47".
  pm_alloc b52 Hb52 "Ho52". pm_alloc b57 Hb57 "Ho57".
  iDestruct (pm_loc8_fresh with "Ho12") as "H12". iDestruct (pm_loc4_fresh with "Ho17") as "H17".
  iDestruct (pm_loc8_fresh with "Ho22") as "H22". iDestruct (pm_loc8_fresh with "Ho27") as "H27".
  iDestruct (pm_loc4_fresh with "Ho32") as "H32". iDestruct (pm_loc8_fresh with "Ho37") as "H37".
  iDestruct (pm_loc8_fresh with "Ho42") as "H42". iDestruct (pm_loc8_fresh with "Ho47") as "H47".
  iDestruct (pm_loc8_fresh with "Ho52") as "H52". iDestruct (pm_loc8_fresh with "Ho57") as "H57".
  change (req_align (heap_req 8 (8 mod 2 ^ 64))) with 16 in *. change (req_extent (heap_req 8 (8 mod 2 ^ 64))) with 16 in *.
  change (req_align (heap_req 4 (4 mod 2 ^ 64))) with 16 in *. change (req_extent (heap_req 4 (4 mod 2 ^ 64))) with 16 in *.
  step_global Gtk. step_global Geb.
  iDestruct "Herr" as (bs cs [Hbsl Hcsl]) "Herr". rewrite pts_app. iDestruct "Herr" as "[Herrb Herra]".
  iApply (wp_live_fit1 with "Leb"). iIntros ([E0 E48]) "Leb".
  check "Leb".
  iApply (wp_raw_load_sub_bytes_dq with "Leb Herrb"); [reflexivity | vx | exact Hbsl | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Leb Herrb".
  iApply (wp_live_fit1 with "Ltk"). iIntros ([T0 T48]) "Ltk".
  iApply (wp_zsys_getrandom _ _ _ _ _ _ _ _ _ _ tk tkreg 0 8 1 eb with "Ltk Htk [Herrb Herra]");
    [exact Hrand | exact (proj1 Hrand_ext) | exact (proj2 Hrand_ext) | rewrite Z.add_0_r; vx | exact Herr | lia | lia | lia
    | iExists bs, cs; iSplit; [done | rewrite pts_app; iFrame] |].
  iNext. iIntros (k Hk) "Ltk Htk Herr".
  step_global Geb.
  iDestruct "Herr" as (bs2 cs2 [Hbsl2 Hcsl2]) "Herr". rewrite pts_app. iDestruct "Herr" as "[Herrb Herra]".
  check "Leb".
  iApply (wp_raw_store_w with "Leb Herrb"); [vx | vx | reflexivity | a2 | exact Hbsl2 | wi_store |].
  iNext. iIntros "Leb Herrb".
  iAssert (errno_any eb) with "[Herrb Herra]" as "Herr".
  { iExists _, cs2. iSplitR; last first; [rewrite pts_app; iFrame "Herrb Herra" | iPureIntro; split; [apply length_le_bytes | exact Hcsl2]]. }
  step.
  branch_cases.
  - pm_loop Hok0 Gtk Herr Btk.
  - enter. step_global Gtk. pm_chk "Ltk".
    iDestruct "Htk" as (ts tc [Htl Htc]) "Htk". rewrite pts_app. iDestruct "Htk" as "[Htkb Htka]".
    iApply (wp_raw_store_long_bytes with "Ltk Htkb"); [vx | vx | reflexivity | a2 | exact Htl | wi_store |].
    iNext. iIntros "Ltk Htkb".
    iAssert (blk_any tk 0 8) with "[Htkb Htka]" as "Htk".
    { iExists _, tc. iSplitR; last first; [rewrite pts_app; iFrame "Htkb Htka" | iPureIntro; rewrite length_le_bytes; done]. }
    step. pm_loop Hok0 Gtk Herr Btk.
Qed.
(** Any program whose image defines `c: __ptmalloc_init` with this body,
    and in which its callees meet their contracts, meets the contract. *)
Lemma ptmalloc_init_has_spec `{!Defines ge "__ptmalloc_init" start_ptmalloc_init_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__ptmalloc_init") ptmalloc_init_spec.
Proof using Hsize Hint Hinit Hclock Hcbs Hrand Hrand_ext.
  intros [[[o tv] x] t]. exists start_ptmalloc_init_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args ptmalloc_init_spec].
  iIntros "(%Hok & Hl & Ht & Hx & Hta & Hf) HK".
  iApply (wp_ptmalloc_init with "Hl Ht Hx Hta Hf"); [exact Hfr | exact Hok |].
  iIntros "Hl Ht Hx Hta Hf". iApply "HK". iFrame. done.
Qed.

End rules.

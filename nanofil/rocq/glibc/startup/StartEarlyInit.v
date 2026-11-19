(** This module proves the contract of `c: __libc_early_init`, stated
    in [StartEarlyInitSpec](StartEarlyInitSpec.v), over its compiled
    body. The body calls four functions whose contracts it imports,
    stores its argument in two flags, and computes the default stack
    size from the stack limit and the page size.

    ## Where the body lives

    The body is defined here, next to its only proof, rather than in a
    shared module. So adding it rebuilds only this file and the final
    startup assembly. *)

From Glibc Require Import Unit_elf_libc_early_init_os Unit_stdlib_getrandom_os.
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import HiAtexitModule OsBlocks OsWorld FileInv LibioLogic LibioCloseSteps StartCode StartLogic.
From Glibc Require Import StartTunableGetValSpec StartGetrlimitSpec StartCtypeInitSpec StartPthreadTunablesSpec.
From Glibc Require Import StartPtmallocInitSpec StartEarlyInitSpec OsGetrlimit.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: __libc_early_init`. *)
Definition start_early_init_fn : func := Unit_elf_libc_early_init_os.fn___libc_early_init.

(** This constant is the empty body of `c: __getrandom_early_init`. *)
Definition start_getrandom_early_init_fn : func := Unit_stdlib_getrandom_os.fn___getrandom_early_init.

(** The image defines both functions with those bodies. *)
Lemma start_early_init_defined :
  find_direct (TAtom "__libc_early_init") hi_module = Some (Defined start_early_init_fn) /\
  find_direct (TAtom "__getrandom_early_init") hi_module = Some (Defined start_getrandom_early_init_fn).
Proof. split; vm_compute; reflexivity. Qed.

(** ## The empty callee

    The body of `c: __getrandom_early_init` only returns, so its
    contract is proved here rather than in a file of its own. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The empty body meets its contract in any program that defines it. *)
Lemma getrandom_early_init_has_spec
    `{!Defines ge "__getrandom_early_init" start_getrandom_early_init_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__getrandom_early_init") getrandom_early_init_spec.
Proof using Type.
  intros a. exists start_getrandom_early_init_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args getrandom_early_init_spec].
  iIntros "_ HK". step. iApply wp_ret_void. iNext. iApply "HK". done.
Qed.

End rules.

(** ## The proof

    The body picks a default stack size along one of four paths, which
    all end in the same rounding and the same three calls. The proof
    shows that shared end once and uses it on each path. It does not
    work out the stack size, which the contract leaves unknown. *)

Section proof.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hctype : !HasSpec registry (os_wi w0) ge (TAtom "__GI___ctype_init") ctype_init_spec}.
Context `{Hrlim : !HasSpec registry (os_wi w0) ge (TAtom "__GI___getrlimit") getrlimit_spec}.
Context `{Hpth : !HasSpec registry (os_wi w0) ge (TAtom "__pthread_tunables_init") pthread_tunables_init_spec}.
Context `{Hgre : !HasSpec registry (os_wi w0) ge (TAtom "__getrandom_early_init") getrandom_early_init_spec}.
Context `{Hpm : !HasSpec registry (os_wi w0) ge (TAtom "__ptmalloc_init") ptmalloc_init_spec}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The shared end runs in an environment that each path builds
    differently. This tactic reads a temporary from such an
    environment. *)
Ltac vxu := first [vx | cbn -[put];
  repeat match goal with |- context [lookup ?k ?E] =>
    let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H end;
  unwrap2; reflexivity].

(** This tactic checks an access to the local at temporary H's base. *)
Ltac ei_chk H := rule1 H ltac:(eapply wp_check; inst;
  [reflexivity | vxu | reflexivity | cbn [r_end]; a2 | cbn [r_end]; a2 | cbn [r_end]; a2]).

(** This tactic renews the check of an access to the local at
    temporary H's base. *)
Ltac ei_renew H := rule1 H ltac:(eapply wp_renew; inst;
  [reflexivity | vxu | reflexivity | reflexivity | cbn [r_end]; a2 | cbn [r_end]; a2 | cbn [r_end]; a2]).

(** Any program whose image defines `c: __libc_early_init` with this
    body, and whose callees meet their contracts, meets the contract. *)
Lemma early_init_has_spec `{!Defines ge "__libc_early_init" start_early_init_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__libc_early_init") early_init_spec.
Proof using Hctype Hrlim Hpth Hgre Hpm.
  intros [[[[[e o] c] tv] a] ps]. exists start_early_init_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args early_init_spec].
  iIntros "(%H & Hei & Hst & Hpg & Hd16 & Hd32 & #Hro & Hloc & Hclv & Hcc & Hpml & Htun & H27 & Hli & Hta & Hf) HK".
  destruct H as (Ha & Hps & Hei & Hpmok & Hct & H27s).
  destruct Hei as (Gst & Gsti & Gpg & Gda & Hste & Hpga & Hpge & Hdaa & Hdae).
  pose proof Hpmok as (Gtk & Geb & Gli & Gaf & Gta & Gma & Gmp & Gerr & Hpmrest).
  assert (E1 : ((((a mod 2 ^ 32) mod 256) mod 2 ^ 32) mod 2 ^ 32) mod 256 = a mod 256).
  { pose proof (Z.mod_pos_bound a 256). rewrite (Z.mod_small a (2 ^ 32)) ?(Z.mod_small (a mod 256) (2 ^ 32)) ?Zmod_mod; lia. }
  assert (E2 : ((sign_extension 256 128 ((((a mod 2 ^ 32) mod 256) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32)
                 mod 256 = a mod 256).
  { pose proof (Z.mod_pos_bound a 256). rewrite (Z.mod_small a (2 ^ 32)) ?(Z.mod_small (a mod 256) (2 ^ 32)); try lia.
    unfold sign_extension. rewrite !Zmod_mod. remember (a mod 256) as v.
    destruct (Z.leb_spec 128 v); Z.div_mod_to_equations; lia. }
  iDestruct "Hei" as "(Lst & Lpg & Lda)". iDestruct "Hcc" as "([%x Hcb] & [%y Hcu] & [%z Hcl])".
  (* The character tables. *)
  step. call_spec with (c, x, y, z). exact Hct.
  cbn [fs_post ctype_init_spec] in *. iDestruct "Hpost" as "(-> & Hloc & Hclv & Hcb & Hcu & Hcl)".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  (* The two flags. *)
  step_global Gst. step. step. iApply (wp_live_fit1 with "Lst"). iIntros ([Hst0 Hst48]) "Lst". check "Lst".
  iDestruct "Hst" as (y0) "Hst".
  iApply (wp_raw_store_byte with "Lst Hst"); [vx | vx | reflexivity | a2 | wi_store |]. iNext. iIntros "Lst Hst".
  step_global Gsti. step_global Gli. iDestruct "Hpml" as "(Ltk & Leb & Lli & Hpml)". iDestruct "Hli" as (y1) "Hli".
  iApply (wp_live_fit1 with "Lli"). iIntros ([Hli0 Hli48]) "Lli". check "Lli".
  iApply (wp_raw_store_byte with "Lli Hli"); [vx | vx | reflexivity | a2 | wi_store |]. iNext. iIntros "Lli Hli".
  check "Lst". iApply (wp_raw_store_byte with "Lst Hst"); [vx | vx | reflexivity | a2 | wi_store |]. iNext. iIntros "Lst Hst".
  (* The stack limit. *)
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]. iNext. iIntros (rb Hrb) "Hrb".
  iDestruct (obj_blk_any with "Hrb") as "[Lrb Hrb]"; [vm_compute; congruence|].
  change (req_extent (heap_req 8 (16 mod 2 ^ 64))) with 16 in *. change (req_kind (heap_req 8 (16 mod 2 ^ 64))) with Heap in *.
  iDestruct "Hf" as "(Htk & Herr & Haf & Hma8 & Hbins & Hmp16 & Hmp56 & Hmp80)".
  call_spec with (3, rb, mkRegion rb (rb + 16) Heap Live, pm_eb o).
  { unfold rlimit_size; split_and!; first [exact Gerr | cbn; lia]. }
  iDestruct "Hpost" as (k [-> Hk]) "(Lrb & Hrb & Herr)". iExists _. iSplit; [done|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step.
  iDestruct "Hrb" as (xs cs [Hxl Hcl]) "Hrb". iEval (rewrite pts_app) in "Hrb". iDestruct "Hrb" as "[Hrb _]".
  iAssert (bytes rb 0 xs) with "[Hrb]" as "Hrb"; [iExact "Hrb"|]. cbn in Hxl.
  iAssert (bytes rb 0 (take 8 xs) ∗ bytes rb (0 + Z.of_nat (length (take 8 xs))) (drop 8 xs))%I
    with "[Hrb]" as "[Hrb _]". { rewrite -bytes_app take_drop. iExact "Hrb". }
  assert (Hx8 : length (take 8 xs) = 8%nat) by (rewrite length_take; unfold rlimit_size in Hxl; lia).
  (* The stack size computation that every path ends with. *)
  iAssert (∀ e1 from bs, ⌜lookup (TAtom "iw_1.v0") e1 = Some (WPtr (mkPtr rb (Obj rb))) /\
      lookup (TAtom "v3") e1 = Some (WInt (((a mod 2 ^ 32) mod 256) mod 2 ^ 32)) /\ length bs = 8%nat⌝ -∗
    live rb (mkRegion rb (rb + 16) Heap Live) -∗ bytes rb 0 bs -∗
    WP (ERun (mkFrame start_early_init_fn e1 [] None (Enter (TAtom "iw_1.L3") from)) : sexpr) {{ Φ }})%I
    with "[-Lrb Hrb]" as "Htail".
  { iIntros (e1 from bs (He1 & He3 & Hbs)) "Lrb Hrb".
    iApply wp_enter; [reflexivity | destruct from; reflexivity | iNext; cbn [b_insts b_jump]].
    step_global Gpg. iApply (wp_live_fit1 with "Lpg"). iIntros ([Hpg0 Hpg48]) "Lpg". check "Lpg".
    iApply (wp_raw_load with "Lpg Hpg"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Lpg Hpg". step.
    iApply (wp_live_fit1 with "Lrb"). iIntros ([Hrb0 Hrb48]) "Lrb". ei_chk "Lrb".
    iApply (wp_raw_load_long_bytes with "Lrb Hrb"); [reflexivity | vxu | exact Hbs | left; reflexivity | a2 |].
    iNext. iIntros "Lrb Hrb". step.
    (* The rounding, the two attributes and the last three calls. *)
    iAssert (∀ e2 from bs, ⌜lookup (TAtom "iw_1.v0") e2 = Some (WPtr (mkPtr rb (Obj rb))) /\
        lookup (TAtom "chk8") e2 = Some (WPtr (mkPtr rb (Obj rb))) /\
        lookup (TAtom "v3") e2 = Some (WInt (((a mod 2 ^ 32) mod 256) mod 2 ^ 32)) /\
        lookup (TAtom "iw_1.v24") e2 = Some (WInt (ps mod 2 ^ 64)) /\ length bs = 8%nat⌝ -∗
      live rb (mkRegion rb (rb + 16) Heap Live) -∗ bytes rb 0 bs -∗
      WP (ERun (mkFrame start_early_init_fn e2 [] None (Enter (TAtom "iw_1.L32") from)) : sexpr) {{ Φ }})%I
      with "[-Lrb Hrb]" as "Htail2".
    { iIntros (e2 from2 bs2 (He21 & He2c & He23 & He24 & Hbs2)) "Lrb Hrb".
      iApply wp_enter; [reflexivity | destruct from2; reflexivity | iNext; cbn [b_insts b_jump]].
      iApply (wp_raw_load_long_bytes with "Lrb Hrb"); [reflexivity | vxu | exact Hbs2 | left; reflexivity | a2 |].
      iNext. iIntros "Lrb Hrb". do 4 step.
      ei_renew "Lrb".
      iApply (wp_raw_store_long_bytes with "Lrb Hrb"); [vxu | vxu | reflexivity | a2 | exact Hbs2 | wi_store |].
      iNext. iIntros "Lrb Hrb".
      step_global Gda. step. ei_renew "Lrb".
      iApply (wp_raw_load_long_bytes with "Lrb Hrb"); [reflexivity | vxu | apply length_le_bytes | left; reflexivity | a2 |].
      iNext. iIntros "Lrb Hrb".
      iApply (wp_live_fit1 with "Lda"). iIntros ([Hda0 Hda48]) "Lda". check "Lda".
      iDestruct "Hd32" as (d32) "Hd32". store_long "Lda" "Hd32".
      step_global Gda. step. step_global Gpg. check "Lpg".
      iApply (wp_raw_load with "Lpg Hpg"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Lpg Hpg".
      check "Lda". iDestruct "Hd16" as (d16) "Hd16". store_long "Lda" "Hd16".
      iDestruct "Hpml" as "(Laf & Lta & Lma & Lmp & Ltl)".
      call_spec with (pm_tl o, pm_tlreg o, tv 27). exact H27s.
      iDestruct "Hpost" as "(-> & Ltl & H27)". iExists _. iSplit; [done|]. iNext.
      cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
      call_spec with (((a mod 2 ^ 32) mod 256) mod 2 ^ 32).
      { repeat match goal with |- context [lookup ?k ?E] =>
          let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H end.
        cbn. rewrite Zmod_mod. reflexivity. }
      { apply Z.mod_pos_bound; lia. }
      iDestruct "Hpost" as "->". iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
      iDestruct "Hta" as (t) "Hta". iEval (rewrite E1) in "Hli". iEval (rewrite E2) in "Hst".
      call_spec with (o, tv, a mod 256, t). exact Hpmok.
      iDestruct "Hpost" as "(-> & Hpml & Htun & Hli & Hta & Hf)". iExists _. iSplit; [done|]. iNext.
      cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
      iApply wp_ret_void. iNext. iApply "HK". rewrite !(Z.mod_small ps (2 ^ 64)); [|lia..].
      rewrite /ei_lives /ct_cells_set. iFrame. done. }
    branch_cases.
    - iApply ("Htail2" with "[%] Lrb Hrb"). split_and!; [lk_prove | lk_prove | lk_prove | lk_prove | exact Hbs].
    - iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]. ei_renew "Lrb".
      iApply (wp_raw_store_long_bytes with "Lrb Hrb"); [vxu | vxu | reflexivity | a2 | exact Hbs | wi_store |].
      iNext. iIntros "Lrb Hrb". iApply wp_goto. iNext.
      iApply ("Htail2" with "[%] Lrb Hrb"). split_and!; [lk_prove | lk_prove | lk_prove | lk_prove | apply length_le_bytes]. }
  (* A failed call, or an unlimited stack, uses the default of 2 MiB; a
     small limit is raised to 16 KiB. *)
  destruct Hk as [-> | ->].
  - branch. iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]].
    iApply (wp_live_fit1 with "Lrb"). iIntros ([Hrb0 Hrb48]) "Lrb". ei_chk "Lrb".
    iApply (wp_raw_load_long_bytes with "Lrb Hrb"); [reflexivity | vx | exact Hx8 | left; reflexivity | a2 |].
    iNext. iIntros "Lrb Hrb". step.
    iApply wp_goto. iNext. iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]].
    destruct (of_bytes (take 8 xs) mod 2 ^ 64 =? 18446744073709551615 mod 2 ^ 64) eqn:Einf.
    + branch. iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]. ei_chk "Lrb".
      iApply (wp_raw_store_long_bytes with "Lrb Hrb"); [vx | vx | reflexivity | a2 | exact Hx8 | wi_store |].
      iNext. iIntros "Lrb Hrb". iApply wp_goto. iNext.
      iApply ("Htail" with "[%] Lrb Hrb"). split_and!; [lk_prove | lk_prove | apply length_le_bytes].
    + branch. iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]. ei_chk "Lrb".
      iApply (wp_raw_load_long_bytes with "Lrb Hrb"); [reflexivity | vx | exact Hx8 | left; reflexivity | a2 |].
      iNext. iIntros "Lrb Hrb". step.
      destruct (Z.ltb_spec (of_bytes (take 8 xs) mod 2 ^ 64) (16384 mod 2 ^ 64)) as [Hlt|Hge].
      * branch. iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]. ei_renew "Lrb".
        iApply (wp_raw_store_long_bytes with "Lrb Hrb"); [vx | vx | reflexivity | a2 | exact Hx8 | wi_store |].
        iNext. iIntros "Lrb Hrb". iApply wp_goto. iNext.
        iApply ("Htail" with "[%] Lrb Hrb"). split_and!; [lk_prove | lk_prove | apply length_le_bytes].
      * branch. iApply ("Htail" with "[%] Lrb Hrb"). split_and!; [lk_prove | lk_prove | exact Hx8].
  - branch. iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]. branch.
    iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]. ei_chk "Lrb".
    iApply (wp_raw_store_long_bytes with "Lrb Hrb"); [vx | vx | reflexivity | a2 | exact Hx8 | wi_store |].
    iNext. iIntros "Lrb Hrb". iApply wp_goto. iNext.
    iApply ("Htail" with "[%] Lrb Hrb"). split_and!; [lk_prove | lk_prove | apply length_le_bytes].
Qed.

End proof.

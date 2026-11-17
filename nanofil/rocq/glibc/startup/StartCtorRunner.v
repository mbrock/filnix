(** This module proves the contract of the constructor runner,
    `c: zrun_deferred_global_ctors`, stated in
    [StartCtorRunnerSpec](StartCtorRunnerSpec.v). Its calls through the
    table's pointers use the rule of [StartRawCall](StartRawCall.v). *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps StartCtors StartCtorRunnerSpec StartRawCall.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.


(** This constant is the runner for three constructors. *)
Definition start_ctor_runner_fn : func := Eval vm_compute in ctor_runner 3.

(** ## The runner's body

    Startup must run each constructor exactly once, with the program's
    arguments. So the runner checks its flag and sets it, reads the three
    saved arguments and every constructor pointer, and then calls the
    constructors in table order. The proof gives each call only the
    resources of its own constructor. *)

Section runner.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Any program that defines the runner symbol with this body meets the
    runner's contract. *)
Lemma ctor_runner_has_spec `{!Defines ge "zrun_deferred_global_ctors" start_ctor_runner_fn} :
  HasSpec registry (os_wi w0) ge ctor_runner_name ctor_runner_spec.
Proof using Type.
  intros [c K]. exists start_ctor_runner_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args ctor_runner_spec].
  iIntros "([%Hok %Hcalls] & Lfl & Hfl & Htab & HP) HK".
  destruct c as [fl flreg tb treg dq argc argv avreg env enreg adq order ptrs].
  destruct Hok as (Gfl & Gtb & Hfle & Htba & Htbe & Hlen & Hargc & Hav & Hen & Hptrs).
  cbn [cr_fl cr_flreg cr_tb cr_treg cr_dq cr_argc cr_argv cr_avreg cr_env cr_enreg cr_adq
       cr_order cr_ptrs] in *.
  destruct order as [|g0 [|g1 [|g2 [|? ?]]]]; try discriminate Hlen.
  inversion Hptrs as [|? p0 ? ? Hp0 Hptrs1]; subst. inversion Hptrs1 as [|? p1 ? ? Hp1 Hptrs2]; subst.
  inversion Hptrs2 as [|? p2 ? ? Hp2 Hptrs3]; subst. inversion Hptrs3; subst.
  pose proof (Hcalls 0%nat g0 eq_refl) as Hc0. pose proof (Hcalls 1%nat g1 eq_refl) as Hc1.
  pose proof (Hcalls 2%nat g2 eq_refl) as Hc2. cbn [firstn] in Hc0, Hc1, Hc2.
  destruct Hp0 as (Hf0 & Hk0 & Hr0), Hp1 as (Hf1 & Hk1 & Hr1), Hp2 as (Hf2 & Hk2 & Hr2).
  unfold ctor_table_size in Htbe. rewrite /cr_table /=.
  iDestruct "Htab" as "(Ltb & Hargc & Hargv & Henv & (Hq0 & Hq1 & Hq2 & _) & Cav & Cen)".
  (* The flag is clear, so the runner sets it and goes on. *)
  step. step_global Gfl. iApply (wp_live_fit1 with "Lfl"). iIntros ([Hfl0 Hfl48]) "Lfl". check "Lfl".
  iApply (wp_raw_load_byte with "Lfl Hfl"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Lfl Hfl".
  branch. iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]].
  iApply (wp_raw_store_byte with "Lfl Hfl"); [vx | vx | reflexivity | a2 | wi_store |]. iNext. iIntros "Lfl Hfl".
  (* The runner reads argc, the two arrays and the three constructor pointers. *)
  step_global Gtb. iApply (wp_live_fit with "Ltb"). iIntros ([Htb0 Htb48]) "Ltb".
  check_read_dq "Ltb" by a2. iNext. iIntros "Ltb".
  iApply (wp_raw_load_sub_bytes_dq with "Ltb Hargc");
    [reflexivity | vx | reflexivity | apply load_sw_int; lia | right; reflexivity | a2 |].
  iNext. iIntros "Ltb Hargc".
  load_pointer_dq "Ltb Hargv Cav" by a2. iNext. iIntros "Ltb Hargv Cav".
  load_pointer_dq "Ltb Henv Cen" by a2. iNext. iIntros "Ltb Henv Cen".
  iAssert (live_capq dq (ptr_cap p0) treg) as "C0"; [by rewrite Hf0|].
  iAssert (live_capq dq (ptr_cap p1) treg) as "C1"; [by rewrite Hf1|].
  iAssert (live_capq dq (ptr_cap p2) treg) as "C2"; [by rewrite Hf2|].
  load_pointer_dq "Ltb Hq0 C0" by a2. iNext. iIntros "Ltb Hq0 _".
  load_pointer_dq "Ltb Hq1 C1" by a2. iNext. iIntros "Ltb Hq1 _".
  load_pointer_dq "Ltb Hq2 C2" by a2. iNext. iIntros "Ltb Hq2 _".
  (* Each constructor is checked and then called through its contract. *)
  iApply wp_check_function; [vx | exact Hk0 |]. iNext.
  iApply (Hc0 with "HP"); [vx | exact Hf0 | exact Hk0 | rewrite /cr_args /= Z.mod_small; [reflexivity | lia] |].
  iNext. iIntros "HP".
  iApply wp_check_function; [vx | exact Hk1 |]. iNext.
  iApply (Hc1 with "HP"); [vx | exact Hf1 | exact Hk1 | rewrite /cr_args /= Z.mod_small; [reflexivity | lia] |].
  iNext. iIntros "HP".
  iApply wp_check_function; [vx | exact Hk2 |]. iNext.
  iApply (Hc2 with "HP"); [vx | exact Hf2 | exact Hk2 | rewrite /cr_args /= Z.mod_small; [reflexivity | lia] |].
  iNext. iIntros "HP".
  iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|]. iFrame.
Qed.

(** ## Constructors with contracts

    The runner's contract asks each constructor for a promise about its
    call. A constructor with its own contract keeps that promise when the
    runner's three arguments convert to the contract's arguments, the
    call needs no conversion of its result, and the contract's
    postcondition says the call returned nothing. *)

(** A constructor g with contract s keeps the promise that the runner
    needs, with the contract's precondition and the rest of its
    postcondition. *)
Lemma ctor_call_ok_spec g s `{Hs : !HasSpec registry (os_wi w0) ge g s} x xs gf ys Q :
  find_fn ge g = Some (Defined gf) ->
  indirect_call_conv gf CVoid ctor_args xs = Some (Converted ys None) ->
  (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else []))%list = fs_args s x ->
  (forall v, fs_post s x v ⊢ ⌜v = RetVoid⌝ ∗ Q) ->
  ctor_call_ok g xs (fs_pre s x) Q.
Proof using Type.
  intros Hf Hcv Hys HQ f e ls lab callee rest j p Ψ args Hv Hp Hc Hx. iIntros "HP HK".
  iApply (wp_raw_call_spec g s x with "HP"); [exact Hv | exact Hp | exact Hc | exact Hx | exact Hf | exact Hcv | exact Hys |].
  iIntros (v) "Hpost". iDestruct (HQ v with "Hpost") as "[-> HQ]".
  iExists _. iSplit; [done|]. iNext. iApply ("HK" with "HQ").
Qed.

End runner.

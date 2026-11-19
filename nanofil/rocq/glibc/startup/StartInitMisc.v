(** This module proves the contract of `c: __init_misc`, stated in
    [StartInitMiscSpec](StartInitMiscSpec.v), over the compiled body
    of the function. The body tests that the argument array and its
    first slot are not null. It then searches the program name for
    its last slash with `c: strrchr` and stores the short name and
    the full name.

    ## Where the body lives

    The body is defined here, next to its only proof, rather than in a
    shared module. So adding it rebuilds only this file and the final
    startup assembly. *)

From Glibc Require Import Unit_misc_initZ2dmisc_os.
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics OsTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv LibioLogic LibioCloseSteps
  MemchrLast MemrchrBits StrrchrLogic StartInitMiscSpec.
From Glibc Require WordString.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps WordString.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: __init_misc`. *)
Definition start_init_misc_fn : func := Unit_misc_initZ2dmisc_os.fn___init_misc.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hstrrchr : !HasSpec registry (os_wi w0) ge (TAtom "__GI_strrchr") strrchr_spec}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Local Ltac enter := iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]].

(** A pointer that is loaded from memory must point into a live
    object. For the program name, the string owns a share of that
    lifetime. This lemma lends the share out and takes it back, and it
    also gives the bounds of the string's address. *)
Lemma string_life dq a s :
  word_string dq a s -∗
  ∃ reg, ⌜0 < ptr_addr a /\ ptr_addr a + Z.of_nat (length s) < 2 ^ 48⌝ ∗ live_capq dq (ptr_cap a) reg ∗
         (live_capq dq (ptr_cap a) reg -∗ word_string dq a s).
Proof using Type.
  iIntros "(%b & %reg & %ws & %Hsh & Ls & Hw)". iExists reg.
  pose proof Hsh as [Hcap Hb Hal Hstart Hfit Hspace Hlen Hwords Hbytes Hchars]. iSplit.
  { iPureIntro. unfold wstart in Hfit. pose proof (Z.mod_pos_bound (ptr_addr a) 8 ltac:(lia)).
    pose proof (Z.mul_succ_div_gt (ptr_addr a mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iSplitL "Ls"; [destruct Hcap as [Hc | Hc]; rewrite Hc; iExact "Ls"|].
  iIntros "Ls". iExists b, reg, ws. iSplit; [done|]. iFrame "Hw". destruct Hcap as [Hc | Hc]; rewrite Hc; iExact "Ls".
Qed.

(** Any program whose image defines the function with this body meets
    the contract, provided that `c: strrchr` meets its own. *)
Lemma init_misc_has_spec `{!Defines ge "__init_misc" start_init_misc_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__init_misc") init_misc_spec.
Proof using Hstrrchr.
  intros [[[[[[[o dq] argc] envp] a] s] x] y]. exists start_init_misc_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args init_misc_spec].
  iIntros "(%H & Hn & Ha) HK".
  destruct H as (Hpn & Hpf & Hpna & Hpne & Hpfa & Hpfe & Hav0 & Hava & Have).
  iDestruct "Hn" as "(Lpn & Hpn & Lpf & Hpf)". iDestruct "Ha" as "(Lav & Hav & Hs)".
  iApply (wp_live_fit with "Lav"). iIntros ([_ Hav48]) "Lav".
  iApply (wp_live_fit1 with "Lpn"). iIntros ([Hpn0 Hpn48]) "Lpn".
  iApply (wp_live_fit1 with "Lpf"). iIntros ([Hpf0 Hpf48]) "Lpf".
  iDestruct (string_life with "Hs") as (reg) "(%Ha & Ls & Hclose)".
  (* The two tests. *)
  step. step. step. branch_as false. enter. check_read_dq "Lav" by a2. iNext. iIntros "Lav".
  load_pointer_dq "Lav Hav Ls" by a2. iNext. iIntros "Lav Hav Ls". step. step.
  iApply wp_goto. iNext. enter. branch_as false.
  (* The search for the last slash. *)
  enter. check_read_dq "Lav" by a2. iNext. iIntros "Lav".
  load_pointer_dq "Lav Hav Ls" by a2. iNext. iIntros "Lav Hav Ls".
  iDestruct ("Hclose" with "Ls") as "Hs". call_spec with (dq, a, s, 47); [lia|].
  cbn [fs_post strrchr_spec] in *. iDestruct "Hpost" as "(-> & Hs)".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iDestruct (string_life with "Hs") as (reg') "(_ & Ls & Hclose)".
  step. step. step. change (47 mod 256) with 47. unfold short_name.
  pose proof (last_byte_hit 47 (s ++ [0])) as Hh.
  destruct (last_byte 47 (s ++ [0])) as [t|] eqn:Et; cbn [hit_ptr ptr_addr ptr_cap].
  - (* A slash was found, and the short name starts after it. *)
    destruct Hh as [Hh _]. apply lookup_lt_Some in Hh. rewrite length_app in Hh. cbn [length] in Hh.
    branch_as true. enter. step_global Hpn. step. check "Lpn". store "Lpn" "Hpn".
    iApply wp_goto. iNext. enter. step_global Hpf.
    iApply (wp_renew_read_dq with "Lav"); [reflexivity | vx | reflexivity | left; reflexivity | a2 | a2 | a2 |].
    iNext. iIntros "Lav". load_pointer_dq "Lav Hav Ls" by a2. iNext. iIntros "Lav Hav Ls".
    check "Lpf". store "Lpf" "Hpf". iApply wp_goto. iNext. enter.
    iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|].
    iDestruct ("Hclose" with "Ls") as "Hs". cbn [ptr_addr ptr_cap].
    rewrite (Z.mod_small (ptr_addr a + Z.of_nat t)); [|lia]. rewrite (Z.mod_small 1); [|lia].
    rewrite (Z.mod_small (ptr_addr a + Z.of_nat t + 1)); [|lia].
    rewrite /ptr_add Z.add_assoc /im_names /im_args. iFrame.
  - (* No slash was found, and the short name is the whole name. *)
    branch_as false. enter. step_global Hpn.
    iApply (wp_renew_read_dq with "Lav"); [reflexivity | vx | reflexivity | left; reflexivity | a2 | a2 | a2 |].
    iNext. iIntros "Lav". load_pointer_dq "Lav Hav Ls" by a2. iNext. iIntros "Lav Hav Ls".
    check "Lpn". store "Lpn" "Hpn". iApply wp_goto. iNext. enter. step_global Hpf.
    iApply (wp_renew_read_dq with "Lav"); [reflexivity | vx | reflexivity | left; reflexivity | a2 | a2 | a2 |].
    iNext. iIntros "Lav". load_pointer_dq "Lav Hav Ls" by a2. iNext. iIntros "Lav Hav Ls".
    check "Lpf". store "Lpf" "Hpf". iApply wp_goto. iNext. enter.
    iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|].
    iDestruct ("Hclose" with "Ls") as "Hs". rewrite /im_names /im_args. iFrame.
Qed.

End rules.

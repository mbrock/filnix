(** This module proves the contract of `c: __libc_start_call_main`,
    stated in [StartCallMainSpec](StartCallMainSpec.v), over the
    compiled body of the function.

    ## Where the body lives

    The body is defined here, next to its only proof, rather than in a
    shared module. So adding it rebuilds only this file and the final
    startup assembly. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import HiAtexitTypedLI.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import HiAtexitModule OsBlocks OsWorld OsThread FileInv LibioLogic LibioCloseSteps StartCode StartLogic
  StartRawCall StartCallMainSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** This constant is the body of `c: __libc_start_call_main`. The
    function is private to its source file, so the linker gave it a
    longer name. *)
Definition start_call_main_fn : func := hi_fn_glibc_libc_start'23__libc_start_call_main.

(** The image defines `c: __libc_start_call_main` with that body. *)
Lemma start_call_main_defined :
  find_direct (TAtom "glibc_libc_start#__libc_start_call_main") hi_module = Some (Defined start_call_main_fn).
Proof. vm_compute. reflexivity. Qed.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic enters the block that a jump has reached. *)
Local Ltac enter := iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]].

(** ## The first return of setjmp

    The function calls `c: _setjmp` on a buffer in its own frame. In
    the model a call of `c: _setjmp` returns once, with the value 0.
    Before it returns, it writes the buffer's own address into the
    first eight bytes of the buffer. *)

(** A call of `c: _setjmp` on the base of a writable object returns 0.
    The caller gives the first pointer cell of the object, and gets it
    back holding the object's address with no capability. *)
Lemma wp_setjmp f e ls l d sk args rest j p w b reg x Φ :
  map2_option (value_x ge e) [P; W] args = Some [WPtr p; w] ->
  ptr_cap p = Obj b -> ptr_addr p = b -> b mod 8 = 0 ->
  live b reg -∗ pcell b 0 x -∗
  ▷ (live b reg -∗ pcell b 0 (mkPtr b CNone) -∗
     WP (ERun (mkFrame f (put d (WInt 0) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d W (Setjmp sk) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hx Hp Ha Hal. iIntros "Hl Hc HK".
  iApply (wp_write registry (os_wi w0) ge
            ([(PLive b, VLive reg)] ++ (PAux b 0, VAux (ptr_cap x)) :: cell b 0 (ptr_addr x))
            ([(PLive b, VLive reg)] ++ (PAux b 0, VAux CNone) :: cell b 0 b)
            _ _ [] (fun m => store_bytes (store_aux m (b + 0) CNone) (b + 0) 8 b)
            with "[Hl Hc] [HK]");
    [reflexivity | | wi_store | rewrite pts_app; iFrame |].
  - intros m fuel (Hf & Hd & _). apply all_agree_app in Hf as [[Hlv _] [_ Hcl]].
    cbn [agree_piece fst snd] in Hlv. destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    destruct (pcell_store_ok m b reg 0 (b + 0) CNone b Hd Hlv Ho He eq_refl) as [Hcs Hfr].
    assert (Hin := in_object_live _ _ _ (b + 0) Hlv ltac:(lia) ltac:(lia)).
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_let with (classes := [P; W]) (xs := [WPtr p; w]); [reflexivity | reflexivity | exact Hx |].
      unfold op_res. cbn [fmt_of op_res_int]. unfold store_res. cbn [width_bytes ptr_addr ptr_cap].
      rewrite Ha Hp (access_obj m b reg b 8 Write 8 (proj1 Hlv) ltac:(lia) ltac:(lia) Hal). cbn.
      rewrite Z.add_0_r. reflexivity.
    + exact (pointer_store_effects_kept _ _ _ _ _ Hin (pointer_store_plain m (b + 0) (mkPtr b CNone))).
    + apply all_agree_app. split; [|exact Hcs]. cbn [all_agree agree_piece fst snd].
      split; [apply (live_at_regions m); [reflexivity|exact Hlv] | exact I].
    + eapply frame_ok_mono; [|exact Hfr]. intros k Hin'. rewrite fmap_app. apply elem_of_app. by right.
  - iNext. iIntros "H". rewrite pts_app. iDestruct "H" as "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

(** ## The functions that it calls

    Most of what happens during a call happens inside three other
    functions, and their code is not in this file. So the proof is
    given what each of them does. The program's `c: main` does what
    its contract says. The function `c: exit` ends the process, so it
    does not return. The runtime call `c: zthread_self_cookie` returns
    the calling thread's own thread object. *)
Context (mn : name) (main_spec : fspec Σ) (E : Z -> iProp Σ).
Context `{Hmain : !HasSpec registry (os_wi w0) ge mn main_spec}.
Context `{Hexit : !HasSpec registry (os_wi w0) ge (TAtom "__GI_exit") (exit_never_spec E)}.
Context (Hself : registry (TAtom "zthread_self_cookie") = Some os_self_contract).
Context (Hself_ext : os_ext ge "zthread_self_cookie").

(** This tactic allocates one stack slot. It names the slot's address
    b, the facts about that address H and the slot's memory Ho. *)
Local Ltac alloc b H Ho :=
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (b H); iIntros Ho.

(** This tactic computes the rounded size and the alignment of each
    slot, so that later steps see plain numbers. *)
Local Ltac sizes :=
  repeat match goal with
  | |- context [(?s mod 2 ^ 64 + 15) / 16 * 16] =>
      let n := eval vm_compute in ((s mod 2 ^ 64 + 15) / 16 * 16) in change ((s mod 2 ^ 64 + 15) / 16 * 16) with n
  | H : context [(?s mod 2 ^ 64 + 15) / 16 * 16] |- _ =>
      let n := eval vm_compute in ((s mod 2 ^ 64 + 15) / 16 * 16) in change ((s mod 2 ^ 64 + 15) / 16 * 16) with n in H
  | H : context [Z.max ?a 16] |- _ => let n := eval vm_compute in (Z.max a 16) in change (Z.max a 16) with n in H
  end.

(** This tactic allocates one stack slot and splits its zeroed memory
    into the fields fs. *)
Local Ltac slot b H Ho fs :=
  alloc b H Ho; rewrite (obj_layout b _ fs); [|vm_compute; congruence | reflexivity];
  cbn [layout_own field_own field_len req_extent req_kind req_align heap_req] in H |- *; sizes.

(** The compiled body of `c: __libc_start_call_main` meets its
    contract. The body calls `c: _setjmp` and takes the branch for the
    first return. It saves the thread's old unwind buffer and cleanup
    handler in its own buffer, and makes its own buffer the thread's
    unwind buffer. It then calls `c: main` through the pointer that it
    was given, and it calls `c: exit` with the result. *)
Lemma start_call_main_has_spec `{!Defines ge "glibc_libc_start#__libc_start_call_main" start_call_main_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_libc_start#__libc_start_call_main")
    (start_call_main_spec mn main_spec E).
Proof using Hmain Hexit Hself Hself_ext.
  intros [[[[[[x o] dq] mainp] argc] argv] envp]. exists start_call_main_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args start_call_main_spec].
  iIntros "(%H & Htcb & Hr & Hpre & Hpost) _".
  destruct H as (Hmp & Hmc & Hmr & Hargc & Gen & Hena & Hene & Hav & Hev & Htakes).
  iDestruct "Htcb" as (tb treg (Hself0 & Htb0 & Htba & Htbe & Htb63)) "(Ltb & H776 & H784 & H792)".
  iDestruct "Hr" as "(Len & Hen & Lav & Lev)".
  iApply (wp_live_fit with "Len"). iIntros ([Hen0 Hen48]) "Len".
  (* The stack slots. *)
  step. slot b1 B1 "O1" [FPtr; FPad 8]. iDestruct "O1" as "(L1 & H1 & _)".
  slot b3 B3 "O3" [FInt; FPad 12]. iDestruct "O3" as "(L3 & H3 & _)".
  slot b5 B5 "O5" [FPtr; FPad 8]. iDestruct "O5" as "(L5 & H5 & _)".
  slot b6 B6 "O6" [FInt; FPad 12]. iDestruct "O6" as "(L6 & H6 & _)".
  slot b7 B7 "O7" [FPtr; FPad 64; FPtr; FPtr; FPad 24]. iDestruct "O7" as "(L7 & H70 & _ & H772 & H780 & _)".
  slot b8 B8 "O8" [FInt; FPad 12]. iDestruct "O8" as "(L8 & H8 & _)".
  slot b17 B17 "O17" [FPtr; FPad 8]. iDestruct "O17" as "(L17 & H17 & _)".
  alloc b36 B36 "_". alloc b37 B37 "_". alloc b62 B62 "_". alloc b63 B63 "_". alloc b64 B64 "_".
  clear B36 B37 B62 B63 B64.
  check "L1". store "L1" "H1". check "L3". store_int "L3" "H3". check "L5". store "L5" "H5".
  (* The first return of setjmp. *)
  iApply (wp_setjmp with "L7 H70"); [reflexivity | reflexivity | reflexivity | destruct B7 as (_ & ? & _); Z.div_mod_to_equations; lia |].
  iNext. iIntros "L7 H70". check "L8". store_int "L8" "H8".
  change (0 mod 2 ^ 32) with 0. assert (Hz : 0 <= 0 < 2 ^ 32) by lia. load_s32 "L8" "H8".
  step. step. step. branch_as false. enter.
  (* The thread's unwind buffer. *)
  destruct Hself_ext as [Hsf Hsg].
  iApply OsThread.wp_zthread_self_cookie; [exact Hself | exact Hsf | exact Hsg | rewrite Hself0; cbn; lia |].
  iNext. rewrite Hself0. unfold off_cancelhandling in Htbe. unfold off_cleanup_jmp, off_cleanup.
  assert (Htbr : 0 <= tb < 2 ^ 64) by lia.
  check "L17". store "L17" "H17". step. check "L17". load "L17" "H17" "Ltb". step. norm. check "Ltb".
  load_null "Ltb" "H784". norm. check "L7". store "L7" "H772". step. step. norm.
  check "L17". load "L17" "H17" "Ltb". step. norm. check "Ltb". load_null "Ltb" "H776". check "L7". store "L7" "H780".
  check "L17". load "L17" "H17" "Ltb". step. norm. check "Ltb". store "Ltb" "H784".
  (* The arguments of main. *)
  check "L1". iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 mainp treg _ _ dq with "L1 H1 []");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hmr | rewrite Hmp; done |].
  iNext. iIntros "L1 H1 _". check "L3". load_s32 "L3" "H3". check "L5".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 argv (cm_avreg o) _ _ dq with "L5 H5 Lav");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hav |].
  iNext. iIntros "L5 H5 Lav". step_global Gen. check_read_dq "Len" by a2. iNext. iIntros "Len".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 envp (cm_evreg o) _ _ dq with "Len Hen Lev");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hev |].
  iNext. iIntros "Len Hen Lev". iApply wp_check_function; [vx | exact Hmc |]. iNext.
  (* The call of main. *)
  destruct (Hmain x) as (gf & Hgf & _ & _). destruct (Htakes gf Hgf) as [Hnv Hconv].
  iMod ("Hpre" with "[Ltb H776 H784 H792] [$Len $Hen $Lav $Lev]") as "Hpre".
  { iExists tb, treg, _. iFrame "Ltb H776 H784". iSplit; [iPureIntro; unfold off_cancelhandling; repeat split; (reflexivity || lia)|].
    iSplit; [iPureIntro; lia|]. iExact "H792". }
  iApply (wp_raw_call_spec mn main_spec x _ _ _ _ _ _ _ _ _ mainp gf _ (fs_args main_spec x) None with "Hpre");
    [vx | exact Hmp | exact Hmc | vx | exact Hgf | rewrite (Z.mod_small argc); [apply Hconv | exact Hargc]
    | rewrite Hnv app_nil_r; reflexivity |].
  iIntros (v) "Hv". iDestruct ("Hpost" with "Hv") as (st [-> Hst]) "HE".
  iExists _. iSplit; [iPureIntro; cbn; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  rewrite (Z.mod_small st); [|exact Hst]. check "L6". store_int "L6" "H6". rewrite (Z.mod_small st); [|exact Hst].
  (* The call of exit. *)
  iApply wp_goto. iNext. enter. check "L6". load_s32 "L6" "H6".
  call_spec using Hexit with st; [cbn; rewrite Z.mod_small; [reflexivity | lia] |].
  cbn [fs_post exit_never_spec]. iDestruct "Hpost" as "[]".
Qed.

End rules.

(** Before `c: main` runs, glibc gives the thread a thread object and
    makes it the runtime's cookie, which the proofs of `c: main` read as
    [ow_self]. This module proves the two startup functions that do it,
    over their compiled bodies. `c: __libc_setup_tls` allocates the
    2496-byte object, points its two self fields at it and sets the
    cookie. `c: __tls_init_tp` then fills in the fields that name the
    kernel thread, the runtime thread and the object itself.

    ## What the proofs give `c: main`

    The program can only exit safely if glibc's cleanup code finds the
    thread object in the state it expects. That code reads three fields:
    the cleanup pointer, the saved jump buffer and the cancellation
    state. Neither startup function writes them, so they stay zero from
    the allocation, and the setup rule hands them back with the
    object. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsStartCalls FileInv LibioLogic LibioCloseSteps OsStart StartCode StartLogic.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.


(** ## The thread object

    The thread object has many fields, but a proof needs only those that
    startup writes or that `c: main` reads. The layout below picks them
    out of the zeroed object. The two assertions after it describe those
    fields before and after `c: __tls_init_tp` runs. *)

(** This layout splits the 2496-byte thread object into zero fields. It
    names the two self pointers at 0 and 16, the fields that
    `c: __tls_init_tp` writes, the cleanup pointers at 776 and 784, and
    `c: cancelhandling` at 792. *)
Definition tcb_layout : list field :=
  [FPtr; FPad 8; FPtr; FPad 696; FInt; FPad 4; FPtr; FInt; FPad 4; FPtr; FPtr; FLong; FPad 8; FPtr; FPtr;
   FInt; FPad 516; FPtr; FPad 249; FByte; FPad 2; FInt; FPad 16; FInt; FPad 124; FLong; FPad 768].

Section fields.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** This assertion owns the fields that `c: __tls_init_tp` writes, while
    they are all zero. *)
Definition tp_zero (tb : Z) : iProp Σ :=
  bytes tb 720 [0; 0; 0; 0] ∗ pcell tb 728 null ∗ bytes tb 736 [0; 0; 0; 0] ∗
  pcell tb 744 null ∗ pcell tb 752 null ∗ icell tb 760 0 ∗ pcell tb 1312 null ∗
  ibyte tb 1569 0 ∗ bytes tb 1572 [0; 0; 0; 0] ∗ bytes tb 1592 [0; 0; 0; 0] ∗ icell tb 1720 0.

(** This assertion owns the same fields after `c: __tls_init_tp` has
    written them. Four values vary from run to run: the kernel thread id
    t, the runtime thread address a, the report-events byte x and the
    saved stack end sp. *)
Definition tp_fields (tb t a x : Z) (sp : ptr) : iProp Σ :=
  bytes tb 720 (le_bytes t 4) ∗ pcell tb 728 (mkPtr a CNone) ∗ bytes tb 736 (le_bytes 0 4) ∗
  pcell tb 744 (mkPtr (tb + 752) (Obj tb)) ∗ pcell tb 752 (mkPtr (tb + 752) (Obj tb)) ∗
  icell tb 760 18446744073709551584 ∗ pcell tb 1312 (mkPtr (tb + 800) (Obj tb)) ∗
  ibyte tb 1569 x ∗ bytes tb 1572 (le_bytes 2 4) ∗ bytes tb 1592 (le_bytes 2 4) ∗ icell tb 1720 (ptr_addr sp).

(** A fresh 2496-byte thread object gives its life and its zero fields.
    The prepared state of the older hi_atexit proof used a 2560-byte
    object instead, but 2496 bytes still cover every field read later. *)
Lemma tcb_fresh tb :
  obj tb (heap_req 16 2496) ⊢
  live tb (mkRegion tb (tb + 2496) Heap Live) ∗ pcell tb 0 null ∗ pcell tb 16 null ∗ tp_zero tb ∗
  pcell tb 776 null ∗ pcell tb 784 null ∗ bytes tb 792 [0; 0; 0; 0].
Proof.
  rewrite obj_zero_block; [|vm_compute; congruence].
  change (req_extent (heap_req 16 2496)) with 2496. change (req_kind (heap_req 16 2496)) with Heap.
  change (Z.to_nat 2496) with (layout_len tcb_layout).
  iIntros "[$ H]". iDestruct (zero_layout with "H") as "H". cbn [layout_own field_own field_len tcb_layout].
  iEval (simpl) in "H".
  iDestruct "H" as "(H0 & _ & H16 & _ & H720 & _ & H728 & H736 & _ & H744 & H752 & H760 & _ & H776 & H784 &
    H792 & _ & H1312 & _ & H1569 & _ & H1572 & _ & H1592 & _ & H1720 & _)".
  iSplitL "H0"; [iExact "H0"|]. iSplitL "H16"; [iExact "H16"|].
  iSplitR "H776 H784 H792"; [|iSplitL "H776"; [iExact "H776"|]; iSplitL "H784"; [iExact "H784" | iExact "H792"]].
  rewrite /tp_zero. iSplitL "H720"; [iExact "H720"|]. iSplitL "H728"; [iExact "H728"|].
  iSplitL "H736"; [iExact "H736"|]. iSplitL "H744"; [iExact "H744"|]. iSplitL "H752"; [iExact "H752"|].
  iSplitL "H760"; [iExact "H760"|]. iSplitL "H1312"; [iExact "H1312"|]. iSplitL "H1569"; [iExact "H1569"|].
  iSplitL "H1572"; [iExact "H1572"|]. iSplitL "H1592"; [iExact "H1592" | iExact "H1720"].
Qed.

End fields.

(** ## Filling in the thread object

    `c: __tls_init_tp` runs after the cookie names the thread object.
    It records the kernel thread id and the runtime's thread handle,
    points the robust-mutex list and the rseq area at the object itself,
    copies the report-events flag and records the stack end. It needs no
    errno handler, because none of its three runtime calls can fail. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** When the cookie already names the thread object tb, a call of
    `c: __tls_init_tp()` fills in the object's fields for some nonzero
    thread id and thread handle. It only reads the report-events byte and
    the saved stack end, and it gives both back. *)
Lemma wp_tls_init_tp fr tb treg re rereg x se sereg sp spreg Φ :
  call_frame start_tls_init_tp_fn [] = Some fr ->
  registry (TAtom "zthread_self_cookie") = Some os_self_contract ->
  registry (TAtom "zthread_self_id") = Some os_self_id_contract ->
  registry (TAtom "zthread_self") = Some os_thread_self_contract ->
  os_ext ge "zthread_self_cookie" -> os_ext ge "zthread_self_id" -> os_ext ge "zthread_self" ->
  lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr re (Obj re)) ->
  lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  re + 1 <= r_end rereg -> se mod 8 = 0 -> se + 8 <= r_end sereg -> 0 <= x < 256 -> 0 <= ptr_addr sp < 2 ^ 64 ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb mod 16 = 0 -> tb + 2496 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  live tb treg -∗ tp_zero tb -∗
  live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
  ▷ (∀ t a, ⌜0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ -∗ live tb treg -∗ tp_fields tb t a x sp -∗
       live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
       Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hr1 Hr2 Hr3 [Hf1 Hg1] [Hf2 Hg2] [Hf3 Hg3] Hre Hse Hreend Hseal Hseend Hx Hsp Hself Htb Hal Hend Hreg.
  injection Hfr as <-. assert (Hal8 : tb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iIntros "Hl (H720 & H728 & H736 & H744 & H752 & H760 & H1312 & H1569 & H1572 & H1592 & H1720)
    Hlre Hre Hlse Hse Hcap HK".
  step.
  iApply wp_zthread_self_cookie; [exact Hr1 | exact Hf1 | exact Hg1 | rewrite Hself; cbn; lia |]. iNext.
  rewrite Hself. step.
  iApply wp_zthread_self_id; [exact Hr2 | exact Hf2 | exact Hg2 |]. iNext. iIntros (t Ht).
  norm. check "Hl". store_int "Hl" "H720". step. norm.
  iApply wp_zthread_self; [exact Hr3 | exact Hf3 | exact Hg3 |]. iNext. iIntros (a Ha).
  check "Hl". store "Hl" "H728".
  step. norm. check "Hl". store_int "Hl" "H736".
  step. step. norm. check "Hl". store "Hl" "H1312".
  step. norm. check "Hl". store_int "Hl" "H1572".
  step. norm. check "Hl". store_int "Hl" "H1592".
  step. step_global Hre. norm.
  iApply (wp_live_fit1 with "Hlre"). iIntros ([Hre0 Hre48]) "Hlre". check "Hlre".
  iApply (wp_raw_load_byte with "Hlre Hre"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hlre Hre". check "Hl".
  iApply (wp_raw_store_byte with "Hl H1569"); [vx | vx | reflexivity | a2 | wi_store |]. iNext.
  iIntros "Hl H1569".
  step. step. norm. check "Hl". store "Hl" "H744".
  check "Hl". store "Hl" "H752".
  step. norm. check "Hl". store_long "Hl" "H760".
  step. step_global Hse. iApply (wp_live_fit1 with "Hlse"). iIntros ([Hse0 Hse48]) "Hlse".
  check "Hlse". load "Hlse" "Hse" "Hcap". step. norm. check "Hl". store_long "Hl" "H1720".
  iApply wp_ret_void. iNext.
  replace (((extension Ub x mod 2 ^ 32) mod 2 ^ 32) mod 256) with x
    by (cbn [extension]; rewrite !(Z.mod_small x); lia).
  rewrite (Z.mod_small (ptr_addr sp)); [|lia].
  iApply ("HK" $! t a with "[%] Hl [H720 H728 H736 H744 H752 H760 H1312 H1569 H1572 H1592 H1720] Hlre Hre Hlse Hse Hcap");
    [lia | rewrite /tp_fields; iFrame "H720 H728 H736 H744 H752 H760 H1312 H1569 H1572 H1592 H1720"].
Qed.

End rules.

(** ## Making the thread object the cookie

    Setting the cookie changes the OS world in the middle of the
    function, so no single fixed world describes the whole call. The
    proof therefore tracks the current world through a ghost key k over
    a base world w0. The function allocates the thread object, points
    its two self fields at it and makes it the cookie. Then it calls
    `c: __tls_init_tp`, whose rule above runs in the fixed world that has
    this cookie. *)

Section setup.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract os_world)) (ge : genv) (w0 : os_world) (k : Z).

(** In this section the program reads the OS world through the key k,
    over the base world w0. *)
Local Instance setup_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi_start w0 k) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Garbage collection keeps the startup interpretation. *)
Local Instance setup_stable : LG0.SafepointStable (os_wi_start w0 k) := os_wi_start_stable w0 k.

(** A call of `c: __libc_setup_tls()` starts with no handler registered
    and any cookie c. It ends with a fresh 2496-byte thread object tb as
    the cookie. The object's self fields name it, `c: __tls_init_tp` has
    filled in its fields, and its cleanup fields and `c: cancelhandling`
    are still zero. *)
Lemma wp_setup_tls fr c re rereg x se sereg sp spreg Φ :
  call_frame start_setup_tls_fn [] = Some fr ->
  registry (TAtom "zthread_set_self_cookie") = Some os_set_cookie_contract ->
  registry (TAtom "zthread_self_cookie") = Some os_self_contract ->
  registry (TAtom "zthread_self_id") = Some os_self_id_contract ->
  registry (TAtom "zthread_self") = Some os_thread_self_contract ->
  os_ext ge "zthread_set_self_cookie" -> os_ext ge "zthread_self_cookie" -> os_ext ge "zthread_self_id" ->
  os_ext ge "zthread_self" ->
  find_fn ge (TAtom "__tls_init_tp") = Some (Defined start_tls_init_tp_fn) ->
  lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr re (Obj re)) ->
  lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  re + 1 <= r_end rereg -> se mod 8 = 0 -> se + 8 <= r_end sereg -> 0 <= x < 256 -> 0 <= ptr_addr sp < 2 ^ 64 ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c false false) -∗
  live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
  ▷ (∀ tb t a, ⌜0 < tb /\ tb mod 16 = 0 /\ tb + 2496 <= 2 ^ 48 /\ 0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ -∗
       pointsto (PName k) (DfracOwn 1) (start_ghost (mkPtr tb (Obj tb)) false false) -∗
       live tb (mkRegion tb (tb + 2496) Heap Live) -∗
       pcell tb 0 (mkPtr tb (Obj tb)) -∗ pcell tb 16 (mkPtr tb (Obj tb)) -∗ tp_fields tb t a x sp -∗
       pcell tb 776 null -∗ pcell tb 784 null -∗ bytes tb 792 [0; 0; 0; 0] -∗
       live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
       Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hrs Hr1 Hr2 Hr3 [Hfs Hgs] He1 He2 He3 Htp Hre Hse Hreend Hseal Hseend Hx Hsp. injection Hfr as <-.
  iIntros "Hkey Hlre Hre Hlse Hse Hcap HK". step.
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_start_alloc _ _ _ _ _ _ _ Hf Hw) |].
  change (2496 mod 2 ^ 64) with 2496.
  iNext. iIntros (tb (Htb & Hal & Hend)) "Ho".
  change (req_extent (heap_req 16 2496)) with 2496 in Hend. change (req_align (heap_req 16 2496)) with 16 in Hal.
  assert (Hal8 : tb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (tcb_fresh with "Ho") as "(Hl & H0 & H16 & Htp & H776 & H784 & H792)".
  remember (mkRegion tb (tb + 2496) Heap Live) as treg eqn:Etreg.
  assert (Htr : r_end treg = tb + 2496) by (rewrite Etreg; reflexivity).
  check "Hl". iApply (wp_raw_store_pointer with "Hl H0"); [vx | vx | reflexivity | a2 | a2 | wi_store_start |].
  iNext. iIntros "Hl H0". step. norm. check "Hl".
  iApply (wp_raw_store_pointer with "Hl H16"); [vx | vx | reflexivity | a2 | a2 | wi_store_start |].
  iNext. iIntros "Hl H16".
  iApply (wp_zthread_set_self_cookie_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (live tb _) with "Hkey Hl");
    [exact Hrs | exact Hfs | exact Hgs | reflexivity | |].
  { iIntros (h m) "Hh Hl". rewrite /live pts_ptsq. iApply (self_registered_liveq with "Hh Hl"). }
  iNext. iIntros "Hkey Hl".
  eapply step_wand; [eapply wp_call_bind; inst; [reflexivity | exact Htp | reflexivity] |].
  set (Ψ := (fun o : outcome => ⌜o = RetVoid⌝ ∗ ∃ t a, ⌜0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ ∗
    live tb treg ∗ tp_fields tb t a x sp ∗ live re rereg ∗ ibyte re 0 x ∗ live se sereg ∗ pcell se 0 sp ∗
    live_cap (ptr_cap sp) spreg)%I).
  iApply (wp_wand with "[Hkey Hl Htp Hlre Hre Hlse Hse Hcap]").
  { iApply (wp_start_of_os registry ge w0 k (mkPtr tb (Obj tb)) false false (DfracOwn 1) _ Ψ with "Hkey").
    iApply (program_call (wp_tls_init_tp (glibc_program := program_of (start_world w0 (mkPtr tb (Obj tb)) false false) registry ge))
         with "Hl Htp Hlre Hre Hlse Hse Hcap");
      [reflexivity | exact Hr1 | exact Hr2 | exact Hr3 | exact He1 | exact He2 | exact He3 | exact Hre | exact Hse
      | exact Hreend | exact Hseal | exact Hseend | exact Hx | exact Hsp | reflexivity | exact Htb | exact Hal | lia | lia |].
    iNext. iIntros (t a Hta) "Hl Hf Hlre Hre Hlse Hse Hcap". iSplit; [done|]. iExists t, a. iFrame. done. }
  iIntros (o) "[Hkey (-> & %t & %a & %Hta & Hl & Hf & Hlre & Hre & Hlse & Hse & Hcap)]".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret_void. iNext. subst treg.
  iApply ("HK" with "[%] Hkey Hl H0 H16 Hf H776 H784 H792 Hlre Hre Hlse Hse Hcap"). lia.
Qed.

End setup.

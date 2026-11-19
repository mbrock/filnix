(** `c: __libc_start_main` runs while the OS world changes: it sets the
    thread cookie and registers the errno and dlerror handlers. So its
    proof runs under [os_wi_start], which reads the world through a
    ghost key. Most of its callees were proved in one fixed world. This
    module first gives the rules that call such a function, or a quiet
    runtime function, from the startup world, and then proves the body.

    ## Calls from the startup world

    Most callees were proved in one fixed world, and startup must still
    be able to call them. Between two world-changing calls the world does
    not change, so such a callee runs unchanged while the key holds the
    current cookie and flags. The caller lends the key for the call and
    gets it back with the result. *)

From Glibc Require Import Unit_csu_libcZ2dstart_os.
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic Symbolic.
From Glibc Require Import HiAtexitModule OsBlocks OsWorld OsThread OsStartCalls FileInv LibioLogic LibioCloseSteps OsStart StartCode StartLogic
  StartTlsInitTpSpec StartSetupTlsSpec StartCtors.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section calls.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract os_world)) (ge : genv) (w0 : os_world) (k : Z).

(** In this section the program reads the OS world through the key k,
    over the base world w0. *)
Local Instance start_main_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi_start w0 k) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Garbage collection keeps the startup interpretation. *)
Local Instance start_main_stable : LG0.SafepointStable (os_wi_start w0 k) := os_wi_start_stable w0 k.

(** A function proved for the world with cookie c and flags e0 and d can
    be called from the startup world while the key holds those values.
    The caller lends the key for the call and gets it back unchanged. *)
Lemma wp_call_spec_start c e0 d n s `{Hs : !HasSpec registry (os_wi (start_world w0 c e0 d)) ge n s}
    x f e ls lab r args rest j Ψ :
  map_option (arg_x ge e) args = Some (fs_args s x) ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c e0 d) -∗ fs_pre s x -∗
  (∀ v, pointsto (PName k) (DfracOwn 1) (start_ghost c e0 d) -∗ fs_post s x v -∗ ∃ cf',
     ⌜resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) v = Some cf'⌝ ∗
     ▷ WP (ERun cf' : sexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global n) args :: rest) j)) : sexpr) {{ Ψ }}.
Proof using Type.
  intros Hx. destruct (Hs x) as (gf & Hg & [fr Hfr] & Ht). iIntros "Hk HP HK".
  iApply (wp_call_bind with "[-]"); [exact Hx | exact Hg | exact Hfr |]. iNext.
  iApply (wp_wand with "[Hk HP]").
  { iApply (wp_start_of_os registry ge w0 k c e0 d (DfracOwn 1) with "Hk").
    iApply (Ht fr _ Hfr with "HP"). iIntros (o) "H". iExact "H". }
  iIntros (o) "[Hk HQ]". iApply ("HK" with "Hk HQ").
Qed.

(** Setting the setjmp signal-mask flag changes neither memory nor the
    world, so the key keeps its value. *)
Lemma wp_zmake_setjmp_save_sigmask_start f e ls lab a rest j b c e0 d Φ :
  registry (TAtom "zmake_setjmp_save_sigmask") = Some os_setjmp_sigmask_contract ->
  find_fn ge (TAtom "zmake_setjmp_save_sigmask") = None ->
  lookup (TAtom "zmake_setjmp_save_sigmask") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a] = Some [WInt b] ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c e0 d) -∗
  ▷ (pointsto (PName k) (DfracOwn 1) (start_ghost c e0 d) -∗
       WP (ERun (mkFrame f e ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zmake_setjmp_save_sigmask")) [Arg W a] :: rest) j)) : sexpr)
    {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata Hx. iIntros "Hk HK".
  iApply (wp_start_change registry ge w0 k _ _ _ _ _ _ _ _ _ _ _ c e0 d c e0 d True%I with "Hk [//] [HK]");
    [done | done | done | exact Hreg | exact Hx | | | | | ].
  - split; [reflexivity | eexists; reflexivity].
  - iIntros (σ) "_ _". iPureIntro. eexists; reflexivity.
  - intros s m trace values s' m' w' Hi.
    destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (_ & born & _ & _ & _ & -> & -> & vs & He & Hok).
    injection He as ->. auto.
  - iIntros (h m) "_ _". iPureIntro. auto.
  - iNext. iIntros "Hk _". iExists e. iSplit; [done|]. iApply ("HK" with "Hk").
Qed.

End calls.

(** ## The body

    The body saves environ and the auxiliary vector, scans the vector for
    `c: AT_SECURE`, and then calls the startup functions in order. *)

(** This constant is the body of `c: __libc_start_main`. *)
Definition start_libc_start_main_fn : func := Unit_csu_libcZ2dstart_os.fn___libc_start_main.

(** The image defines `c: __libc_start_main` with that body. *)
Lemma start_libc_start_main_defined :
  find_direct (TAtom "__libc_start_main") HiAtexitModule.hi_module = Some (Defined start_libc_start_main_fn).
Proof. vm_compute. reflexivity. Qed.

(** This constant is the head of the loop over the auxiliary vector. *)
Definition lsm_blk17 : block := Eval vm_compute in
  match find_block (TAtom "L17") (fn_blocks start_libc_start_main_fn) with
  | Some b => b | None => mkBlock (TAtom "L17") [] [] JUnreachable end.

(** The cells of an auxiliary vector hold its key and value pairs, from
    offset o on, one pair every sixteen bytes. *)
Definition auxv_cells `{!gen_heapGS piece pval Σ} (av o : Z) (qs : list (Z * Z)) : iProp Σ :=
  [∗ list] i ↦ kv ∈ qs, icell av (o + 16 * Z.of_nat i) kv.1 ∗ icell av (o + 16 * Z.of_nat i + 8) kv.2.

(** The first pair of a vector comes apart from the pairs after it. *)
Lemma auxv_cells_cons `{!gen_heapGS piece pval Σ} av o kv qs :
  auxv_cells av o (kv :: qs) ⊣⊢ (icell av o kv.1 ∗ icell av (o + 8) kv.2) ∗ auxv_cells av (o + 16) qs.
Proof.
  rewrite /auxv_cells big_sepL_cons. cbn [Z.of_nat]. rewrite Z.mul_0_r Z.add_0_r.
  f_equiv. apply big_sepL_proper. intros i x _. rewrite Nat2Z.inj_succ.
  replace (o + 16 * Z.succ (Z.of_nat i)) with (o + 16 + 16 * Z.of_nat i) by lia. reflexivity.
Qed.

(** This tactic shows that a temporary the scan never writes keeps its value. *)
Ltac keep := repeat (rewrite lookup_after_put_other; [|reflexivity]); assumption.

Section body.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract os_world)) (ge : genv) (w0 : os_world) (k : Z).

Local Instance body_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi_start w0 k) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Instance body_stable : LG0.SafepointStable (os_wi_start w0 k) := os_wi_start_stable w0 k.

(** Every live object lies below 2^48, and a share of its life shows it. *)
Lemma wp_liveq_fit_start dq b reg fr Φ :
  liveq dq b reg -∗
  (⌜0 <= b /\ r_end reg <= 2 ^ 48⌝ -∗ liveq dq b reg -∗ WP (ERun fr : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  iIntros "Hl HK". rewrite !wp_unfold /wp_pre /=. iIntros (σ ns κs nt) "Hσ".
  iDestruct (ptsq_facts with "Hσ Hl") as %(Hag & _ & Hfit).
  cbn [all_agree agree_piece fst snd] in Hag. destruct Hag as [[Hreg _] _].
  destruct (Hfit b reg Hreg) as [H0 H48].
  iSpecialize ("HK" with "[%] Hl"); [lia|]. iApply ("HK" $! σ ns κs nt with "Hσ").
Qed.

(** The same holds for a whole life token. *)
Lemma wp_live_fit_start b reg fr Φ :
  live b reg -∗
  (⌜0 <= b /\ r_end reg <= 2 ^ 48⌝ -∗ live b reg -∗ WP (ERun fr : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  iIntros "Hl HK". rewrite /live pts_ptsq. iApply (wp_liveq_fit_start with "Hl").
  iIntros (H) "Hl". rewrite -pts_ptsq. iApply ("HK" with "[//] Hl").
Qed.

(** The scan reads pairs until it meets the zero key or `c: AT_SECURE`,
    whose value it copies into `c: __libc_enable_secure`. It changes no
    temporary that the rest of the body reads. *)
Lemma wp_auxv_loop av avreg es esreg ls e0 Φ qs :
  0 < av -> r_end avreg <= 2 ^ 48 ->
  lookup (TAtom "__libc_enable_secure") (ge_globals ge) = Some (mkPtr es (Obj es)) -> es + 4 <= r_end esreg ->
  Forall (fun kv => 0 < kv.1 < 2 ^ 64 /\ 0 <= kv.2 < 2 ^ 64) qs ->
  forall o e from,
  0 <= o -> av + o + 16 * Z.of_nat (length qs) + 8 <= r_end avreg ->
  phis_env ge (b_phis lsm_blk17) from e = Some (put (TAtom "pr.1") (WPtr (mkPtr (av + o) (Obj av))) e) ->
  lookup (TAtom "v0") e = lookup (TAtom "v0") e0 -> lookup (TAtom "v2") e = lookup (TAtom "v2") e0 ->
  lookup (TAtom "v4") e = lookup (TAtom "v4") e0 ->
  live av avreg -∗ auxv_cells av o qs -∗ icell av (o + 16 * Z.of_nat (length qs)) 0 -∗
  live es esreg -∗ (∃ y, bytes es 0 (le_bytes y 4)) -∗
  (∀ e' from', ⌜lookup (TAtom "v0") e' = lookup (TAtom "v0") e0 /\ lookup (TAtom "v2") e' = lookup (TAtom "v2") e0 /\
                 lookup (TAtom "v4") e' = lookup (TAtom "v4") e0⌝ -∗
     live av avreg -∗ auxv_cells av o qs -∗ icell av (o + 16 * Z.of_nat (length qs)) 0 -∗
     live es esreg -∗ (∃ y, bytes es 0 (le_bytes y 4)) -∗
     WP (ERun (mkFrame start_libc_start_main_fn e' ls None (Enter (TAtom "L20") from')) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame start_libc_start_main_fn e ls None (Enter (TAtom "L17") from)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hav Hreg Gs Hse Hqs. induction qs as [|[kk vv] qs IH]; intros o e from Ho Hend Hphi H0 H2 H4.
  - iIntros "La Hc Ht Ls Hs HK".
    iApply wp_enter; [reflexivity | exact Hphi |]. iNext. cbn [b_insts b_jump lsm_blk17].
    cbn [length Z.of_nat] in *. rewrite ?Z.mul_0_r ?Z.add_0_r.
    check "La".
    iApply (wp_raw_load_read_dq with "La Ht"); [reflexivity | vx | left; reflexivity | a2 |]. iNext. iIntros "La Ht".
    step. branch.
    iApply ("HK" with "[%] La Hc [Ht] Ls Hs"); [split; [|split]; keep |].
    cbn [length Z.of_nat]. rewrite ?Z.mul_0_r ?Z.add_0_r. iExact "Ht".
  - iIntros "La Hc Ht Ls Hs HK".
    destruct (Forall_cons_1 _ _ _ Hqs) as [[Hk1 Hk2] Hq2]. cbn [fst snd] in Hk1, Hk2.
    iDestruct (auxv_cells_cons with "Hc") as "[[Hck Hcv] Hc]". cbn [fst snd].
    cbn [length] in Hend |- *. rewrite Nat2Z.inj_succ in Hend |- *.
    iApply wp_enter; [reflexivity | exact Hphi |]. iNext. cbn [b_insts b_jump lsm_blk17].
    check "La".
    iApply (wp_raw_load_read_dq with "La Hck"); [reflexivity | vx | left; reflexivity | a2 |]. iNext. iIntros "La Hck".
    step. rewrite !(Z.mod_small kk (2 ^ 64)); [|lia..].
    assert (E0 : (kk =? 0 mod 2 ^ 64) = false) by (apply Z.eqb_neq; rewrite Zmod_0_l; lia).
    branch_rewrite E0. iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
    iApply (wp_raw_load_read_dq with "La Hck"); [reflexivity | vx | left; reflexivity | a2 |]. iNext. iIntros "La Hck".
    rewrite !(Z.mod_small kk (2 ^ 64)); [|lia..]. step.
    destruct (Z.eq_dec kk 23) as [->|Hn23].
    + branch. iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
      step_global Gs. step. cbn [ptr_addr ptr_cap].
      assert (Ea : ((av + o) mod 2 ^ 64 + 8 mod 2 ^ 64) mod 2 ^ 64 = av + o + 8).
      { rewrite (Z.mod_small (av + o)); [|lia]. rewrite (Z.mod_small 8); [|lia]. apply Z.mod_small. lia. }
      rewrite Ea.
      iApply (wp_half_check with "La"); [reflexivity | vx | reflexivity | reflexivity | a2 | a2 | lia | lia | a2 |].
      iNext. iIntros "La".
      iApply (wp_raw_load_read_dq with "La Hcv"); [reflexivity | vx | left; reflexivity | a2 |]. iNext. iIntros "La Hcv".
      iApply (wp_live_fit_start with "Ls"). iIntros ([Hs0 Hs48]) "Ls". check "Ls". iDestruct "Hs" as (y) "Hs".
      iApply (wp_raw_store_w with "Ls Hs"); [vx | vx | reflexivity | a2 | reflexivity | wi_store_start |].
      iNext. iIntros "Ls Hs".
      step.
      iApply ("HK" with "[%] La [Hck Hcv Hc] Ht Ls [Hs]"); [split; [|split]; keep | | by iExists _].
      iApply auxv_cells_cons. cbn [fst snd]. iFrame.
    + branch_symbolic. rewrite (Z.mod_small kk (2 ^ 64)); [|lia]. change (23 mod 2 ^ 64) with 23.
      rewrite (proj2 (Z.eqb_neq kk 23) Hn23). change ((0 mod 2 ^ 32 =? 0)) with true. cbn [edge_label].
      iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump]. step.
      change (ptr_cap (mkPtr (av + o) (Obj av))) with (Obj av).
      change (ptr_addr (mkPtr (av + o) (Obj av))) with (av + o).
      assert (Eb : ((av + o) mod 2 ^ 64 + 16 mod 2 ^ 64) mod 2 ^ 64 = av + (o + 16)).
      { rewrite (Z.mod_small (av + o)); [|lia]. rewrite (Z.mod_small 16); [|lia]. rewrite Z.mod_small; lia. }
      rewrite Eb. iApply wp_goto. iNext. cbn [edge_label].
      iApply (IH Hq2 (o + 16) _ (Some (TAtom "L19")) with "La Hc [Ht] Ls Hs [HK Hck Hcv]");
        [lia | lia | reflexivity | keep | keep | keep | |].
      { replace (o + 16 + 16 * Z.of_nat (length qs)) with (o + 16 * Z.succ (Z.of_nat (length qs))) by lia.
        iExact "Ht". }
      iIntros (e1 from1 Hlk) "La Hc Ht Ls Hs".
      iApply ("HK" with "[%] La [Hck Hcv Hc] [Ht] Ls Hs"); [exact Hlk | iApply auxv_cells_cons; iFrame |].
      replace (o + 16 * Z.succ (Z.of_nat (length qs))) with (o + 16 + 16 * Z.of_nat (length qs)) by lia.
      iExact "Ht".
Qed.

(** When startup is done, the thread object tb identifies the thread and
    both handlers are registered. The program's main function runs in
    this world from then on. *)
Definition final_world (tb : Z) : os_world := start_world w0 (mkPtr tb (Obj tb)) true true.

(** Startup must reach `c: main` without a panic, and this lemma shows
    that the body of `c: __libc_start_main` does. The body sets the
    setjmp flag, saves environ and the auxiliary vector, scans the
    vector, and calls `c: init_cpu_features` and `c: __libc_setup_tls`.
    Then it registers both handlers. In the final world it calls early
    init with 1, then the constructor runner, then
    `c: __libc_start_call_main`.

    Hello and hi_atexit run different code after the handlers are
    registered, and one proof should serve both programs. So the lemma
    leaves open what each of the last four functions needs and gives
    back. The caller says how to get from what the earlier calls gave
    back to what the next call needs. The last function never returns,
    so the body never returns either. *)
Lemma wp_libc_start_main fr xs mainp argc argv envp av avreg ps
    en enreg dx dxreg es esreg dm dmreg dqm eb ereg dqe hp dp dn
    cfp icf_s x1 re rereg x se sereg sp spreg ei_s cr_s cm_s Φ
    `{Hicf : !HasSpec registry (os_wi (start_world w0 null false false)) ge
                (TAtom "glibc_libc_start#init_cpu_features") icf_s}
    `{Htls : !HasSpec registry (os_wi_start w0 k) ge (TAtom "__libc_setup_tls") (setup_tls_spec ge k)}
    (Hei : forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 ->
       HasSpec registry (os_wi (final_world tb)) ge (TAtom "__libc_early_init") (ei_s tb))
    (Hcr : forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 ->
       HasSpec registry (os_wi (final_world tb)) ge ctor_runner_name (cr_s tb))
    (Hcm : forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 ->
       HasSpec registry (os_wi (final_world tb)) ge
         (TAtom "glibc_libc_start#__libc_start_call_main") (cm_s tb)) :
  call_frame start_libc_start_main_fn xs = Some fr ->
  xs = [WPtr mainp; WInt argc; WPtr argv; WPtr envp; WPtr (mkPtr av (Obj av))] ->
  0 <= argc < 2 ^ 32 ->
  registry (TAtom "zmake_setjmp_save_sigmask") = Some os_setjmp_sigmask_contract ->
  registry (TAtom "zregister_sys_errno_handler") = Some os_errno_register_contract ->
  registry (TAtom "zregister_sys_dlerror_handler") = Some os_dlerror_register_contract ->
  os_ext ge "zmake_setjmp_save_sigmask" -> os_ext ge "zregister_sys_errno_handler" ->
  os_ext ge "zregister_sys_dlerror_handler" ->
  lookup (TAtom "__pthread_initialize_minimal") (ge_globals ge) = None ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr en (Obj en)) -> en mod 8 = 0 -> en + 8 <= r_end enreg ->
  lookup (TAtom "_dl_auxv") (ge_globals ge) = Some (mkPtr dx (Obj dx)) -> dx mod 8 = 0 -> dx + 8 <= r_end dxreg ->
  0 < av -> av + 16 * Z.of_nat (length ps) + 8 <= r_end avreg ->
  Forall (fun kv => 0 < kv.1 < 2 ^ 64 /\ 0 <= kv.2 < 2 ^ 64) ps ->
  lookup (TAtom "__libc_enable_secure") (ge_globals ge) = Some (mkPtr es (Obj es)) -> es + 4 <= r_end esreg ->
  lookup (TAtom "_dl_debug_mask") (ge_globals ge) = Some (mkPtr dm (Obj dm)) -> dm mod 4 = 0 -> dm + 4 <= r_end dmreg ->
  lookup (TAtom "_dl_x86_cpu_features") (ge_globals ge) = Some cfp -> fs_args icf_s x1 = [WPtr cfp] ->
  (forall v, fs_post icf_s x1 v ⊢ ⌜v = RetVoid⌝ ∗ fs_post icf_s x1 RetVoid) ->
  lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr re (Obj re)) ->
  lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  re + 1 <= r_end rereg -> se mod 8 = 0 -> se + 8 <= r_end sereg -> 0 <= x < 256 -> 0 <= ptr_addr sp < 2 ^ 64 ->
  lookup errno_handler_name (ge_globals ge) = Some hp -> ptr_cap hp = Fn errno_handler_name ->
  ow_errno_cell w0 = mkPtr eb (Obj eb) -> eb <> 0 -> eb mod 4 = 0 -> r_kind ereg = GlobalData -> eb + 4 <= r_end ereg ->
  lookup (TAtom "glibc_libc_start#dlerror_handler") (ge_globals ge) = Some dp -> ptr_cap dp = Fn dn ->
  pointsto (PName k) (DfracOwn 1) (start_ghost null false false) -∗
  live en enreg -∗ (∃ p, pcell en 0 p) -∗ live dx dxreg -∗ (∃ p, pcell dx 0 p) -∗
  live av avreg -∗ auxv_cells av 0 ps -∗ icell av (16 * Z.of_nat (length ps)) 0 -∗
  live es esreg -∗ (∃ y, bytes es 0 (le_bytes y 4)) -∗
  liveq dqm dm dmreg -∗ bytesq dqm dm 0 [0; 0; 0; 0] -∗ liveq dqe eb ereg -∗
  fs_pre icf_s x1 -∗
  live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
  (∀ tb t a, ⌜0 < tb /\ tb mod 16 = 0 /\ tb + 2496 <= 2 ^ 48 /\ 0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ -∗
     fs_post icf_s x1 RetVoid -∗
     live tb (mkRegion tb (tb + 2496) Heap Live) -∗
     pcell tb 0 (mkPtr tb (Obj tb)) -∗ pcell tb 16 (mkPtr tb (Obj tb)) -∗ tp_fields tb t a x sp -∗
     pcell tb 776 null -∗ pcell tb 784 null -∗ bytes tb 792 [0; 0; 0; 0] -∗
     live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
     live en enreg -∗ pcell en 0 envp -∗ live dx dxreg -∗ pcell dx 0 (mkPtr av (Obj av)) -∗
     live av avreg -∗ auxv_cells av 0 ps -∗ icell av (16 * Z.of_nat (length ps)) 0 -∗
     live es esreg -∗ (∃ y, bytes es 0 (le_bytes y 4)) -∗ liveq dqe eb ereg -∗
     ∃ x3, ⌜fs_args (ei_s tb) x3 = [WInt 1]⌝ ∗ fs_pre (ei_s tb) x3 ∗
     ∀ v3, fs_post (ei_s tb) x3 v3 -∗ ⌜v3 = RetVoid⌝ ∗
     ∃ x4, ⌜fs_args (cr_s tb) x4 = []⌝ ∗ fs_pre (cr_s tb) x4 ∗
     ∀ v4, fs_post (cr_s tb) x4 v4 -∗ ⌜v4 = RetVoid⌝ ∗
     ∃ x5, ⌜fs_args (cm_s tb) x5 = [WPtr mainp; WInt argc; WPtr argv]⌝ ∗ fs_pre (cm_s tb) x5 ∗
     ∀ v5, fs_post (cm_s tb) x5 v5 -∗ False) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr -> Hargc Rsm Rer Rdl [Fsm Gsm] [Fer Ger] [Fdl Gdl] Gpm Gen Hena Hene Gdx Hdxa Hdxe
    Hav Have Hps Gs Hse Gdm Hdma Hdme Gcf Hcfa Hicf_ret Gre Gse Hree Hsea Hsee Hx Hsp Ghp Hhp Hcell Heb0 Heb4 Herk Hebe
    Gdp Hdp.
  injection Hfr as <-.
  iIntros "Hk Len Hen Ldx Hdx La Hc Ht Ls Hs Ldm Hdm Leb H1 Lre Hre Lse Hse Hcap HK".
  step.
  iApply (wp_zmake_setjmp_save_sigmask_start with "Hk"); [exact Rsm | exact Fsm | exact Gsm | reflexivity |].
  iNext. iIntros "Hk".
  (* The body saves environ and the auxiliary vector. *)
  iDestruct "Hen" as (p0) "Hen". iDestruct "Hdx" as (p1) "Hdx".
  step_global Gen. iApply (wp_live_fit_start with "Len"). iIntros ([Hen0 Hen48]) "Len". check "Len".
  iApply (wp_raw_store_pointer with "Len Hen"); [vx | vx | reflexivity | a2 | a2 | wi_store_start |].
  iNext. iIntros "Len Hen".
  step_global Gdx. iApply (wp_live_fit_start with "Ldx"). iIntros ([Hdx0 Hdx48]) "Ldx". check "Ldx".
  iApply (wp_raw_store_pointer with "Ldx Hdx"); [vx | vx | reflexivity | a2 | a2 | wi_store_start |].
  iNext. iIntros "Ldx Hdx".
  (* It scans the vector. *)
  iApply wp_goto. iNext. cbn [edge_label].
  iApply (wp_live_fit_start with "La"). iIntros ([Hav0 Hav48]) "La".
  iApply (wp_auxv_loop av avreg es esreg _ _ _ ps Hav Hav48 Gs Hse Hps 0 _ (Some (TAtom "start"))
            with "La [Hc] [Ht] Ls Hs");
    [lia | lia | rewrite Z.add_0_r; reflexivity | reflexivity | reflexivity | reflexivity | iExact "Hc"
    | rewrite Z.add_0_l; iExact "Ht" |].
  iIntros (e1 from1 (L0 & L2 & L4)) "La Hc Ht Ls Hs". cbn in L0, L2, L4.
  iApply wp_enter; [reflexivity | destruct from1; reflexivity |]. iNext. cbn [b_insts b_jump].
  (* The weak __pthread_initialize_minimal is not linked, so the body skips it. *)
  step. step. step. step. branch. iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  (* init_cpu_features runs in the world before any registration. *)
  step_global Gcf.
  iApply (wp_call_spec_start registry ge w0 k null false false _ icf_s x1 with "Hk H1"); [rewrite Hcfa; vx |].
  iIntros (v1) "Hk H1". iDestruct (Hicf_ret with "H1") as "[-> H1]".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  (* __libc_setup_tls makes the new thread object the cookie. *)
  iApply (wp_call_spec registry (os_wi_start w0 k) ge (TAtom "__libc_setup_tls") (setup_tls_spec ge k)
            (null, re, rereg, x, se, sereg, sp, spreg) with "[Hk Lre Hre Lse Hse Hcap]"); [reflexivity | |].
  { cbn [fs_pre setup_tls_spec]. iFrame. iPureIntro. split_and!; first [assumption | lia]. }
  iIntros (v2). cbn [fs_post setup_tls_spec].
  iIntros "(-> & %tb & %t & %a & %Htb & Hk & Ltb & H0 & H16 & Htp & H776 & H784 & H792 & Lre & Hre & Lse & Hse & Hcap)".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  (* The body registers the two handlers. *)
  step_global Ghp.
  iApply (wp_zregister_sys_errno_handler_start registry ge w0 k with "Hk Leb");
    [exact Rer | exact Fer | exact Ger | vx | exact Hhp | exact Hcell | exact Heb0 | exact Heb4 | exact Herk
    | exact Hebe |].
  iNext. iIntros "Hk Leb".
  step_global Gdp.
  iApply (wp_zregister_sys_dlerror_handler_start registry ge w0 k with "Hk");
    [exact Rdl | exact Fdl | exact Gdl | vx | exact Hdp |].
  iNext. iIntros "Hk".
  (* The continuation gives early init's precondition, and the body passes it 1. *)
  pose proof Htb as (Htb0 & _ & Htb1 & _).
  iDestruct ("HK" $! tb t a Htb with "H1 Ltb H0 H16 Htp H776 H784 H792 Lre Hre Lse Hse Hcap Len Hen Ldx Hdx
              La Hc Ht Ls Hs Leb") as (x3 Hx3) "[H3 HK]".
  iApply (wp_call_spec_start registry ge w0 k (mkPtr tb (Obj tb)) true true _ (ei_s tb) (Hs := Hei tb Htb0 Htb1) x3 with "Hk H3");
    [rewrite Hx3; vx |].
  iIntros (v3) "Hk H3". iDestruct ("HK" with "H3") as (->) "HK".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  (* Bit 1 of _dl_debug_mask is clear, so the body prints nothing. *)
  step_global Gdm. iApply (wp_liveq_fit_start with "Ldm"). iIntros ([Hdm0 Hdm48]) "Ldm".
  check_read_dq "Ldm" by a2. iNext. iIntros "Ldm".
  iApply (wp_raw_load_sub_bytes_dq with "Ldm Hdm");
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Ldm Hdm". step. step. step. branch.
  (* The constructor runner runs in the final world. *)
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iDestruct "HK" as (x4 Hx4) "[H4 HK]".
  iApply (wp_call_spec_start registry ge w0 k (mkPtr tb (Obj tb)) true true _ (cr_s tb) (Hs := Hcr tb Htb0 Htb1) x4 with "Hk H4");
    [rewrite Hx4; vx |].
  iIntros (v4) "Hk H4". iDestruct ("HK" with "H4") as (->) "HK".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step_global Gdm. check_read_dq "Ldm" by a2. iNext. iIntros "Ldm".
  iApply (wp_raw_load_sub_bytes_dq with "Ldm Hdm");
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Ldm Hdm". step. step. step. branch.
  (* __libc_start_call_main gets main, argc and argv, and never returns. *)
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iDestruct "HK" as (x5 Hx5) "[H5 HK]".
  iApply (wp_call_spec_start registry ge w0 k (mkPtr tb (Obj tb)) true true _ (cm_s tb) (Hs := Hcm tb Htb0 Htb1) x5 with "Hk H5").
  { rewrite Hx5. cbn -[put]. rewrite !lookup_after_put_other; try reflexivity. rewrite L0 L2 L4. cbn.
    rewrite (Z.mod_small argc); [reflexivity | lia]. }
  iIntros (v5) "_ H5". iDestruct ("HK" with "H5") as "[]".
Qed.

End body.

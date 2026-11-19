(** We want to show that GNU Hello never panics from the moment the
    runtime calls `c: __libc_start_main`. The proof of the startup body
    for Hello is in [HelloStartRun](HelloStartRun.v). It asks its caller
    for the memory that the body reads, and for each of the three late
    calls it asks for what that call needs. This module supplies both,
    as [StartWpHiAtexit](../hi_atexit/StartWpHiAtexit.v) does for
    hi_atexit. The theorem itself is in
    [HelloStartNeverPanics](HelloStartNeverPanics.v).

    ## What differs from hi_atexit

    Hello's main reads its arguments and its environment, so the run
    keeps every share of the argument array, the environment array and
    `c: __environ` that it lends to a late call, and it joins the shares
    again when main starts. Startup builds main's private state from
    the objects that `c: getenv` reads and the image's private list. *)

From Glibc Require Import HelloObjects.
From Glibc Require Fix.
From Glibc Require Import ImageObjectPieces GlibcTactics GlibcProgram GlibcSpec PrintfSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import LocaleEnv.
From Glibc Require Import FileInv OsWorld OsRegistry OsStart OsCpuid StartCtors StartState StartOwn
  StartJoin StartGetenv StartLibcStartMain StartLsmImage StartLsmHello StartEarlyInitSpec StartCtorRunnerSpec
  StartCallMainSpec StartPtmallocInitSpec StartInitFirstSpec StartInitMiscSpec StartCtorChain StartImageEarly StartTunablesEarly CpuInitSpec
  WordString GetenvScan GetenvEntry GetenvStatic HelloGlibcDebts HelloImageModule
  HelloImageLoad HelloImageLayout HelloImageEarly HelloImageCpu HelloImageEnviron HelloImageCtors
  HelloStartAssembly HelloStartCtors HelloStartMain HelloStartBridge HelloStartRun HelloStartPost
  HelloStartEntry HelloStartFacts OsMemLogic HelloGetoptDiagImage HelloGetoptStart HelloStartHdGetopt HelloStartQuery HelloSetlocaleState HelloStartSetlocale
  HelloStartHdRules HelloStartHdBuild HelloLocaleState HelloConvState HelloStartGetoptRules LibioFputsSpec HelloVersionEtcCall HelloVfprintfImage
  HelloCloseStdoutCall.
From Glibc Require AtexitLogic ExitRun HelloGlibcMainLibs HelloCloseStdoutWideCall HelloWDoWriteImage HelloWPrintfCall HelloWPrintfWrite.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** ## Joining shares *)

Section join.
Context `{!gen_heapGS piece pval Σ}.

(** A half and two quarters of some pieces are the whole pieces. *)
Lemma ptsq_join3 ps : ptsq (DfracOwn (1/2)) ps -∗ ptsq (DfracOwn (1/2/2)) ps -∗ ptsq (DfracOwn (1/2/2)) ps -∗ pts ps.
Proof using Type.
  iIntros "A B C".
  iAssert (ptsq (DfracOwn (1/2/2 + 1/2/2)) ps) with "[B C]" as "B"; [iApply ptsq_split; iFrame|].
  rewrite Qp.div_2.
  iAssert (ptsq (DfracOwn (1/2 + 1/2)) ps) with "[A B]" as "A"; [iApply ptsq_split; iFrame|].
  rewrite Qp.half_half -pts_ptsq. iExact "A".
Qed.

(** Two halves of some pieces are the whole pieces. *)
Lemma ptsq_join2 ps : ptsq (DfracOwn (1/2)) ps -∗ ptsq (DfracOwn (1/2)) ps -∗ pts ps.
Proof using Type.
  iIntros "A B". iAssert (ptsq (DfracOwn (1/2 + 1/2)) ps) with "[A B]" as "A"; [iApply ptsq_split; iFrame|].
  rewrite Qp.half_half -pts_ptsq. iExact "A".
Qed.

(** Eight zero bytes are an eight-byte cell that holds zero. *)
Lemma bytes_zero_icell b : bytes b 0 (repeat 0 8) ⊢ icell b 0 0.
Proof using Type.
  assert (E : StringLogic.byte_ps b 0 (repeat 0 8) = cell b 0 0) by (vm_compute; reflexivity).
  by rewrite /icell /bytes E.
Qed.

End join.

(** A heap object of the start state lies above zero, is aligned to
    eight bytes, and fits in its region below 2^48. *)
Lemma heap_object_bounds m b n : 0 <= n -> heap_object m b n ->
  0 < b /\ b mod 8 = 0 /\ b + n <= r_end (reg_of m b) /\ r_end (reg_of m b) <= 2 ^ 48.
Proof.
  intros Hn (reg & [Er _] & _ & H0 & H16 & He & Hs).
  assert (R : reg_of m b = reg) by (unfold reg_of; rewrite Er; reflexivity). rewrite R.
  Z.div_mod_to_equations. lia.
Qed.

(** An address aligned to sixteen bytes is aligned to eight. *)
Lemma mod16_mod8 b : b mod 16 = 0 -> b mod 8 = 0.
Proof. intros H. Z.div_mod_to_equations. lia. Qed.

(** ## The startup run *)

Section run.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (k : Z).
Context (m0 m : mem).
Context (Hi : initial_memory hello_image_module = Some (img_globals, m0)).

Local Notation fr := R.free.
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
Local Abbreviation o := hello_image_objs.
Local Abbreviation P tb := (program_of (final_world w0 tb) glibc_os_registry hge).
Local Abbreviation P0 := (program_of (start_world w0 null false false) glibc_os_registry hge).

Local Instance run_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi_start w0 k) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** The library calls borrow the environment, getopt's warning state
    and the private cells that startup supplies. The two halves of the
    environment let a call read it while the rest of main keeps its
    share. This definition specifies those resources, not the behavior
    of any call. *)
Local Definition hello_main_priv (env : Z * list (Z * list Z)) (tb : Z) : iProp Σ :=
  let envp := mkPtr env.1 (Obj env.1) in
  let half := (getenv_globals (glibc_program := P tb) (DfracOwn (1/2)) (img_a "__environ_counter")
      (img_gd "__environ_counter") (img_a "__environ") (img_gd "__environ") 0 envp ∗
    getenv_storage (DfracOwn (1/2)) DfracDiscarded envp (env_entries m env))%I in
  (half ∗ hello_hd_getopt (final_world w0 tb) fr tb ∗ (half ∗ hello_priv_rest (final_world w0 tb) fr))%I.

(** The run's memory, split into the parts the image proofs name, lets
    the startup body reach main and lets main run without a panic. *)
Lemma hello_start_wp fr0 argv env av aps order argc :
  ow_leaf4_ends w0 = true -> In 2 (ow_fds w0) -> In 1 (ow_fds w0) ->
  lookup (TAtom "__libc_errno") img_globals = Some (ow_errno_cell w0) ->
  call_frame start_libc_start_main_fn
    [WPtr (mkPtr (img_a "main") (Fn (TAtom "main"))); WInt argc; WPtr (mkPtr argv.1 (Obj argv.1));
     WPtr (mkPtr env.1 (Obj env.1)); WPtr (mkPtr av (Obj av))] = Some fr0 ->
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> c_locale_env (map snd env.2) -> auxv_array m av aps ->
  argc = Z.of_nat (length argv.2) -> 1 <= argc < 2 ^ 31 ->
  Permutation order (ctor_names hello_image_module) ->
  pts hello_start_all_ps -∗
  (bytes hello_runner_objs.2.1 0 (le_bytes argc 4) ∗ pcell hello_runner_objs.2.1 8 (mkPtr argv.1 (Obj argv.1)) ∗
   pcell hello_runner_objs.2.1 16 (mkPtr env.1 (Obj env.1)) ∗
   [∗ list] i ↦ p ∈ ctor_ptrs img_globals order, pcell hello_runner_objs.2.1 (24 + 8 * Z.of_nat i) p) -∗
  pts (array_ps m argv) -∗ pts (array_ps m env) -∗
  (live av (reg_of m av) ∗ auxv_cells av 0 aps ∗ icell av (16 * Z.of_nat (length aps)) 0) -∗
  pointsto (PName k) (DfracOwn 1) (start_ghost null false false) -∗
  WP (ERun fr0 : sexpr) {{ _, ⌜False⌝ }}.
Proof using Hi.
  intros Hleaf Hfd2 Hfd1 He Hfr Ha He2 Hloc Hv Hargc Hargc2 Hord.
  pose proof R.free_succeeds as Hfree.
  pose proof (hello_image_layout img_globals m0 fr Hi) as Hy.
  assert (Lb : forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 ->
    HelloLibs (final_world w0 tb) hge o (hello_main_priv env tb) hello_exit0
      (AtexitLogic.exit_funcs_inv (ho_x o) [(ho_cp o, null, null)] ((0 + 1) mod 2 ^ 64) ∗
       ExitRun.exit_lock_free (ho_el o) (ho_elr o))%I).
  { intros tb H0 H1. destruct (hello_final_world_facts w0 tb He ltac:(lia)) as (Herr & _ & Hfds).
    assert (Hpv : hello_main_priv env tb ⊣⊢ hello_main_priv env tb) by reflexivity.
    unfold hello_main_priv at 2 in Hpv.
    assert (F1 : In 1 (ow_fds (final_world w0 tb))) by (rewrite Hfds; exact Hfd1).
    assert (F2 : In 2 (ow_fds (final_world w0 tb))) by (rewrite Hfds; exact Hfd2).
    assert (Hfputs := hello_fputs_image (final_world w0 tb) fr (hello_link_all fr Hfree)
      ltac:(destruct (hello_final_world_facts w0 tb He ltac:(lia)) as (_ & -> & _); cbn; lia)
      ltac:(rewrite Herr; vm_compute; reflexivity)).
    pose proof (hello_vfprintf_image (final_world w0 tb) fr (hello_link_all fr Hfree)) as Hvf.
    assert (Hgi : getenv_image_ok hge (img_a "__environ_counter") (img_gd "__environ_counter")
      (img_a "__environ") (img_gd "__environ")) by (split_and!; vm_compute; first [reflexivity | congruence]).
    assert (Hle : c_locale_env (map entry_text (env_entries m env))) by (rewrite env_entries_text; exact Hloc).
    exact (HelloGlibcMainLibs.hello_libs (final_world w0 tb) hge o (hello_link_all fr Hfree)
      (hello_os_layout_final w0 tb He ltac:(lia)) (hello_main_priv env tb) 0
      (hello_setlocale_all (final_world w0 tb) fr tb ltac:(rewrite Hfds; exact Hfd2) _ _ _ _ _ _ _ _ _ _ _ _
         (hello_setlocale_lend (final_world w0 tb) fr) Hgi Hle Hfree Hpv)
      (hello_setlocale_query (final_world w0 tb) fr tb ltac:(rewrite Hfds; exact Hfd2) _ _ _ Hpv)
      (hello_close_stdout_narrow (final_world w0 tb) tb Herr F1 F2 (Hvf := Hvf) _ _ _ Hpv)
      (HelloCloseStdoutWideCall.hello_close_stdout_wide
        (final_world w0 tb) tb Herr F1 F2 (Hvf := Hvf) (HelloWDoWriteImage.hello_close_write _ F1 Herr) _ _ _ Hpv)
      (hello_mbsrtowcs (final_world w0 tb) fr tb ltac:(rewrite Hfds; exact Hfd2) Herr _ _ Hpv)
      (HelloWPrintfCall.hello_wprintf_greet
        (final_world w0 tb) R.free tb (hello_link_all R.free R.free_succeeds) Herr F1 F2 _ _ Hpv
        (HelloWPrintfWrite.hello_wprintf_pending _ tb _ _ Hpv F1 F2 Herr))
      (hello_prints_image (final_world w0 tb) fr _ Hy (hello_link_all fr Hfree) Herr
         ltac:(rewrite Hfds; exact Hfd1) ltac:(rewrite Hfds; exact Hfd2) (hello_os_layout_final w0 tb He ltac:(lia))
         Hvf Hfputs)). }
  iIntros "Hall (Tc & Tv & Te & Tp) Harg Henv (La & Hc & Ht) Hk".
  iDestruct (hello_start_own with "Hall") as "(Hcpu & Hearly & Hrun & Hctor & Hkept & Hlsm & Hso & Hcnt & Hpriv)".
  iDestruct (pts_app with "Hctor") as "[Hil Hctor]". iDestruct (pts_app with "Hctor") as "[Hif Hvt]".
  iDestruct (hello_init_first_split with "Hif") as "(Hifc & Len & Hen)".
  iDestruct (hello_cpu_globals_own (start_world w0 null false false) img_globals fr with "Hcpu") as "Hicf".
  iDestruct "Hicf" as "(Lcf & Fcf & Ltl & Ttl & Lkn & Kkn & Sm)".
  iMod (early_own (glibc_program := P0) hello_ei_objs hello_pm_objs hello_ct_objs with "Ltl Hearly")
    as "(Ei & St & Pg & D16 & D32 & #Ro & Loc & Cl & Ccells & Pml & Li & Ta & Pf)".
  iDestruct "Pml" as "(Ltk & Leb & Lli & Laf & Lta & Lma & Lmp & Ltl)".
  iDestruct (hello_lsm_split with "Hlsm") as "(Ldx & Bdx & Adx & Les & Bes & Ldm & Bdm & Lre & Bre & Lse & Bse & Ase)".
  iDestruct (zero_bytes_pcell with "Bdx Adx") as "Hdx". iDestruct (zero_bytes_pcell with "Bse Ase") as "Hse".
  pose proof (heap_object_bounds m av (8 * (2 * Z.of_nat (length aps) + 1)) ltac:(lia) (proj1 Hv)) as (Hav0 & _ & Have & _).
  destruct Hv as (_ & _ & Hpos & Hslots & _).
  iApply (hello_libc_start_main_wp w0 k m0 fr Hi o (hello_main_priv env) hello_exit0 _ Lb Hy fr0 _ (mkPtr (img_a "main") (Fn (TAtom "main")))
    argc (mkPtr argv.1 (Obj argv.1)) (mkPtr env.1 (Obj env.1)) av (reg_of m av) aps (DfracOwn 1) (DfracOwn 1) 0 null
    (mkRegion 0 0 Heap Live) (fun _ => ⌜False⌝)%I
    with "Hk Len [Hen] Ldx [Hdx] La Hc Ht Les [Bes] Ldm Bdm Leb [Lcf Fcf Ltl Ttl Lkn Kkn Sm] Lre Bre Lse Hse [] [-]").
  1: exact Hleaf. 1: exact He. 1: exact Hfr. 1: reflexivity. 1: lia. 1: exact Hav0.
  1: lia.
  1: { apply List.Forall_forall. intros [kk vv] Hin. destruct (In_nth_error _ _ Hin) as [i Hi'].
       destruct (Hslots i kk vv Hi') as [[Hk0 _] [Hv0 _]].
       pose proof (proj1 (List.Forall_forall _ _) Hpos _ Hin) as Hp. cbn in Hp |- *. lia. }
  1: lia. 1: (cbn; lia).
  1: (iExists null; iExact "Hen").
  1: (iExists null; iExact "Hdx").
  1: (iExists 1; iExact "Bes").
  1: (rewrite /icf_owns; iFrame "Lcf Fcf Lkn Kkn Sm Ltl Ttl").
  1: done.
  iIntros (tb t a (Htb0 & Htb16 & Htbe & Ht0 & Hta))
    "[_ Hicf] Ltb H0 H16 Htp H776 H784 H792 Lre Hre Lse Hse Hcap Len Hen Ldx Hdx La Hc Ht Les Hes Leb".
  destruct (hello_final_world_facts w0 tb He ltac:(lia)) as (Herr & Hself & Hfds).
  iDestruct "Hicf" as "(Lcf & Fcf & Ltl & Ttl & Lkn & Kkn & Sm)".
  iDestruct (icf_tunables_early (glibc_program := P tb) hello_pm_objs with "[Ttl]") as "[(%tv & Pt & T27) _]";
    [iExact "Ttl"|].
  iExists (hello_ei_objs, hello_pm_objs, hello_ct_objs, tv, 1, 4096). iSplit; [done|].
  iSplitL "Ei St Pg D16 D32 Loc Cl Ccells Ltk Leb Lli Laf Lta Lma Lmp Ltl Pt T27 Li Ta Pf".
  { cbn [fs_pre early_init_spec].
    destruct (hello_early_ok (final_world w0 tb) img_globals m0 fr Hi Herr) as (E1 & E2 & E3 & E4).
    iSplitR; [iPureIntro; split_and!; first [lia | assumption]|].
    rewrite /pm_lives.
    iSplitL "Ei"; [iFrame "Ei"|]. iSplitL "St"; [iFrame "St"|]. iSplitL "Pg"; [iFrame "Pg"|]. iSplitL "D16"; [iFrame "D16"|]. iSplitL "D32"; [iFrame "D32"|]. iSplitR; [iExact "Ro"|].
    iSplitL "Loc"; [iFrame "Loc"|]. iSplitL "Cl"; [iFrame "Cl"|]. iSplitL "Ccells"; [iFrame "Ccells"|].
    iSplitL "Ltk Leb Lli Laf Lta Lma Lmp Ltl"; [iFrame "Ltk Leb Lli Laf Lta Lma Lmp Ltl"|].
    iSplitL "Pt"; [iFrame "Pt"|]. iSplitL "T27"; [iFrame "T27"|]. iSplitL "Li"; [iFrame "Li"|]. iSplitL "Ta"; [iFrame "Ta"|]. iFrame "Pf". }
  iIntros (v3) "Hpost". cbn [fs_post early_init_spec].
  iDestruct "Hpost" as "(-> & Ei & St & Pg & D16 & D32 & Loc & Cl & Ccells & Pml & Pt & T27 & Li & Ta & Pf)".
  iSplit; [done|].
  (* The runner and the constructors. *)
  destruct argv as [avb [|[q0b q0s] qs]]; cbn [length fst snd] in Hargc; [lia|].
  cbn [fst snd] in Ha. pose proof Ha as (Hah & Hsa & Han). destruct (Hsa 0%nat q0b q0s eq_refl) as [_ Hc0].
  pose proof (heap_object_bounds m avb (8 * (Z.of_nat (length ((q0b, q0s) :: qs)) + 1)) ltac:(lia) Hah) as (Havb0 & Havb8 & Havbe & Havbs).
  pose proof (heap_object_bounds m env.1 (8 * (Z.of_nat (length env.2) + 1)) ltac:(lia) (proj1 He2)) as (Hevb0 & Hevb8 & Hevbe & Hevbs).
  iEval (rewrite /hello_runner_ps) in "Hrun".
  iDestruct (runner_own (glibc_program := P0) hello_runner_objs with "Hrun") as "(Lfl & Bfl & Ltt)".
  iDestruct (array_own with "Harg") as "(Lav & Pav & Nav & Sav)". cbn [fst snd].
  iDestruct (array_own with "Henv") as "(Lev & Pev & Nev & Sev)".
  rewrite big_sepL_cons. iDestruct "Pav" as "[P0 Pav]". rewrite big_sepL_cons. iDestruct "Sav" as "[[Lq0 Bq0] Sav]".
  iDestruct (str_word_string m (q0b, q0s) Hc0 with "Lq0 Bq0") as "Ws". cbn [fst snd].
  iEval (rewrite -(Qp.div_2 1) word_string_split) in "Ws". iDestruct "Ws" as "[Ws Ws2]".
  iDestruct (pcell_halves with "P0") as "[P0 P02]".
  iDestruct (live_halves with "Lav") as "[Lav1 Lav]".
  iDestruct (liveq_half (1/2) with "Lav") as "[Lav2 Lav3]".
  iDestruct (live_halves with "Lev") as "[Lev1 Lev]".
  iDestruct (liveq_half (1/2) with "Lev") as "[Lev2 Lev3]".
  set (envp := mkPtr env.1 (Obj env.1)).
  set (c := {| cr_fl := hello_runner_objs.1.1; cr_flreg := hello_runner_objs.1.2; cr_tb := hello_runner_objs.2.1;
    cr_treg := hello_runner_objs.2.2; cr_dq := DfracOwn 1; cr_argc := argc; cr_argv := mkPtr avb (Obj avb);
    cr_avreg := reg_of m avb; cr_env := envp; cr_enreg := reg_of m env.1;
    cr_adq := DfracOwn (1/2/2); cr_order := order; cr_ptrs := ctor_ptrs img_globals order |}).
  iExists (c, hello_ctor_mem (final_world w0 tb) fr avb (reg_of m avb) (DfracOwn (1/2)) argc envp
    (mkPtr q0b (Obj q0b)) q0s). iSplit; [done|].
  iSplitL "Lfl Bfl Ltt Tc Tv Te Tp Lav2 Lev2 Hil Hso Hifc Len Hen Lav1 P0 Ws Hvt".
  { cbn [fs_pre ctor_runner_spec]. iSplitR.
    { iPureIntro. split.
      - destruct (hello_runner_ok img_globals m0 Hi) as (R1 & R2 & R3 & R4 & R5).
        refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj _ (conj _ (conj _ (conj _ _))))))))).
        + unfold c; cbn [cr_order]. rewrite (Permutation_length Hord) hello_ctor_count_eq. reflexivity.
        + unfold c; cbn [cr_argc]. lia.
        + unfold c; cbn [cr_argv ptr_addr]. lia.
        + unfold c, envp; cbn [cr_env ptr_addr]. lia.
        + unfold c; cbn [cr_order cr_ptrs]. exact (hello_ctor_ptrs_ok fr order Hord).
      - unfold c; cbn [cr_order cr_args cr_argc cr_argv cr_env].
        exact (hello_ctor_chain (final_world w0 tb) m0 fr Hi avb (reg_of m avb) (DfracOwn (1/2)) argc _ _ q0s order Hord). }
    iFrame "Lfl Bfl". iSplitL "Ltt Tc Tv Te Tp Lav2 Lev2".
    { rewrite /cr_table /liveq /bytesq /pcellq. unfold c.
      cbn [cr_dq cr_tb cr_treg cr_argc cr_argv cr_env cr_ptrs cr_adq cr_avreg cr_enreg ptr_cap].
      rewrite -!pts_ptsq. iFrame "Tc Tv Te Tp Lav2 Lev2". iExact "Ltt". }
    iApply (hello_ctor_start (final_world w0 tb) m0 fr Hi with "Hil Hifc Hvt [Hso] Len Hen [Lav1 P0 Ws]").
    - lia.
    - exact Havb0.
    - exact Havb8.
    - cbn [length] in Havbe. lia.
    - rewrite /hello_stdout_life_ps. iExact "Hso".
    - rewrite /im_args. iFrame "Lav1 Ws". iExact "P0". }
  iIntros (v4) "Hpost". cbn [fs_post ctor_runner_spec]. iDestruct "Hpost" as "(-> & _ & _ & Tab & K)". iSplit; [done|].
  iEval (rewrite (hello_ctor_end (final_world w0 tb) fr _ _ _ _ _ _ _ (cr_order c) Hord)) in "K".
  iDestruct "K" as "((Io & Sl) & Ifd & Vc)".
  cbn [init_first_done hello_xf]. rewrite /if_lives /vtables_cells. cbn [hello_init_first_objs if_en if_enreg].
  iDestruct "Ifd" as "((_ & _ & Len) & _ & _ & Ien & Nms & Ims)". iDestruct "Vc" as "(Ci & Co & Ce & Lv)".
  iDestruct "Tab" as "(_ & _ & _ & _ & _ & TLav & TLev)".
  iDestruct (live_halves with "Len") as "[Len1 Len]". iDestruct (liveq_half with "Len") as "[Len2 Len3]".
  iDestruct (pcell_halves with "Ien") as "[Ien1 Ien]". iDestruct (pcellq_half with "Ien") as "[Ien2 Ien3]".
  (* The call of main. *)
  set (p0 := mkPtr q0b (Obj q0b)). set (ps := (fun q : Z * list Z => mkPtr q.1 (Obj q.1)) <$> qs).
  assert (Ea : Z.of_nat (length (p0 :: ps)) = argc) by (rewrite /ps /= length_fmap; lia).
  set (sz := ptr_addr null).
  iExists (hello_main_x (final_world w0 tb) fr avb (reg_of m avb) p0 ps p0 (short_name p0 q0s) sz,
    {| cm_en := if_en hello_init_first_objs; cm_enreg := if_enreg hello_init_first_objs; cm_avreg := reg_of m avb;
       cm_evreg := reg_of m env.1 |}, DfracOwn (1/2/2), mkPtr (img_a "main") (Fn (TAtom "main")), argc,
    mkPtr avb (Obj avb), envp).
  iSplit; [done|].
  iSplitL; [|iIntros (v5) "[]"].
  rewrite /hello_cm_spec. cbn [fs_pre fs_args start_call_main_spec hello_main_spec hello_main_x].
  iSplitR; [iPureIntro; rewrite Ea; apply hello_cm_ok; lia|].
  assert (Oc : off_cleanup = 776) by reflexivity. assert (Oj : off_cleanup_jmp = 784) by reflexivity.
  assert (Oh : off_cancelhandling = 792) by reflexivity.
  iSplitL "Ltb H776 H784 H792".
  { iExists tb, _. rewrite Oc Oj Oh. iFrame "Ltb H776 H784 H792". iPureIntro. cbn [r_end].
    split_and!; [exact Hself|lia|exact (mod16_mod8 tb Htb16)|lia|lia]. }
  iSplitL "Len3 Ien3 Lav3 Lev3".
  { rewrite /cm_reads. cbn [cm_en cm_enreg cm_avreg cm_evreg ptr_cap live_capq]. iFrame. }
  iSplitR "".
  2: { iIntros (r) "[]". }
  iIntros "Tci (Len3 & Ien3 & Lav3 & Lev3)".
  (* Join the shares that the late calls gave back. *)
  rewrite /im_args. iDestruct "Ims" as "(Lav1 & P0 & Ws)".
  iDestruct (ptsq_join3 with "Lav1 TLav Lav3") as "Lav".
  iDestruct (ptsq_join3 with "Lev1 TLev Lev3") as "Lev".
  iDestruct (ptsq_join3 with "Len1 Len2 Len3") as "Len".
  iDestruct (ptsq_join3 with "Ien1 Ien2 Ien3") as "Ien".
  iDestruct (ptsq_join2 with "P0 P02") as "P0".
  iMod (word_string_persist with "Ws") as "#W0".
  iAssert (|==> [∗ list] q ∈ qs, str_ro (mkPtr q.1 (Obj q.1)))%I with "[Sav]" as ">#Hss".
  { iApply big_sepL_bupd. iApply (big_sepL_impl with "Sav"). iIntros "!>" (i q Hq) "[L B]".
    destruct q as [sb s]. destruct (Hsa (S i) sb s (lookup_nth_error_eq _ _ _ Hq)) as [_ Hcs].
    iMod (word_string_persist with "[L B]") as "#W"; [iApply (str_word_string m (sb, s) Hcs with "L B")|].
    iModIntro. iExists s. iExact "W". }
  iAssert ([∗ list] q ∈ p0 :: ps, str_ro q)%I as "#Hargs".
  { rewrite big_sepL_cons. iSplit; [iExists q0s; iExact "W0"|].
    iEval (rewrite /ps (big_sepL_fmap (PROP:=iProp Σ))). iExact "Hss". }
  iAssert (argv_own avb (reg_of m avb) (p0 :: ps)) with "[Lav P0 Pav Nav]" as "Hav".
  { assert (Lps : length ps = length qs) by (rewrite /ps length_fmap; reflexivity).
    rewrite /argv_own. iSplit.
    { iPureIntro. cbn [length] in *. rewrite Lps. split_and!; lia. }
    iSplitL "Lav"; [iExact "Lav"|].
    rewrite big_sepL_app big_sepL_singleton (big_sepL_cons _ p0 ps).
    iSplitL "P0 Pav"; [iSplitL "P0"|].
    { rewrite Z.mul_0_r. iExact "P0". }
    { iEval (rewrite /ps (big_sepL_fmap (PROP:=iProp Σ))). iExact "Pav". }
    cbn [length] in *. rewrite Lps Nat.add_0_r. iExact "Nav". }
  rewrite /ei_lives /pm_lives /pm_fields /im_names. cbn [im_pn im_pnreg im_pf im_pfreg hello_init_misc_objs].
  iDestruct "Ei" as "(Lst & _)". iDestruct "Pf" as "(_ & Eb & _)".
  iDestruct "Pml" as "(_ & Leb & _ & _ & _ & _ & Lmp & _)". iDestruct "Nms" as "(Lpn & Hpn & Lpf & Hpf)".
  iEval (rewrite /hello_priv_ps) in "Hpriv". iDestruct (pts_app with "Hpriv") as "[Hpriv Hco]".
  iDestruct (pts_app with "Hco") as "[Hco Hlo]". iDestruct (pts_app with "Hlo") as "[Hlo Hmb]". iDestruct (pts_app with "Hmb") as "[Hmb Hcx]".
  iDestruct (pts_app with "Hcx") as "[Hcx Her]". iDestruct (pts_app with "Her") as "[Hel Her]".
  (* The globals of error go to the read-only promise and to the streams. *)
  iMod (hello_error_objs_own hge eq_refl with "Her") as "[#Hepn Hec]".
  iMod (hello_start_post_main img_globals m0 fr Hi (final_world w0 tb) avb (reg_of m avb) p0 ps p0 (short_name p0 q0s)
    with "[Hkept Io Sl Ci Co Ce Lv Lst St Leb Eb Lmp Lpn Hpn Lpf Hpf Hav] Tci Hepn Hec") as "Hres".
  { rewrite /hello_start_post.
    iSplitL "Hkept"; [iExact "Hkept"|]. iSplitL "Io"; [iExact "Io"|]. iSplitL "Sl"; [iExact "Sl"|]. iSplitL "Ci"; [iExact "Ci"|]. iSplitL "Co"; [iExact "Co"|]. iSplitL "Ce"; [iExact "Ce"|]. iSplitL "Lv"; [iExact "Lv"|]. iSplitL "Lst"; [iExact "Lst"|].
    iSplitL "St"; [iExact "St"|]. iSplitL "Leb"; [iExact "Leb"|]. iSplitL "Eb"; [iExact "Eb"|]. iSplitL "Lmp"; [iExact "Lmp"|]. iSplitL "Lpf"; [iExact "Lpf"|]. iSplitL "Hpf"; [iExact "Hpf"|]. iSplitL "Lpn"; [iExact "Lpn"|]. iSplitL "Hpn"; [iExact "Hpn"|].
    iSplitR; [iExact "Hargs"|iExact "Hav"]. }
  (* What getopt and Hello's private state read. *)
  (* The counter is the eight zero bytes at 176352, and `c: __environ` is at 176320. *)
  rewrite /hello_environ_counter_ps. iDestruct (ImageObjectPieces.obj_ps_own with "Hcnt") as "(Lc & Bc & _)".
  cbn [fst snd]. iDestruct (bytes_zero_icell with "Bc") as "Bc".
  iMod (getenv_own (glibc_program := P tb) m env 176352 _ 176320 _ He2
    with "Lc Bc Len Ien Lev Pev Nev Sev") as "[Gg Gs]".
  rewrite /StartTlsInitTpSpec.tp_fields. iDestruct "Htp" as "(Htid & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsz)".
  assert (Hfd2' : In 2 (ow_fds (final_world w0 tb))) by (rewrite Hfds; exact Hfd2).
  iDestruct (getenv_half with "[$Gg $Gs]") as "[Gh1 Gh2]".
  iEval (rewrite /hello_start_main_res) in "Hres". iDestruct "Hres" as "(#Hrr & #Hk145 & #H80 & Hres)".
  iDestruct "Hes" as (sv) "Hes".
  assert (Esec : hello_sec = (lo_es hello_lsm_objs, lo_esreg hello_lsm_objs)) by (vm_compute; reflexivity).
  iMod (hello_hd_build (final_world w0 tb) fr tb Hself Hfd2' sv t Ht0 with "Hpriv Hco Hlo Cl Ccells Hmb Hcx Hel Ro [Les] [Hes] Htid Hrr Loc")
    as "[Hgo Hrest]"; [rewrite Esec; iExact "Les" | rewrite Esec; iExact "Hes" |].
  iDestruct "Hrest" as "(Hgl & #Hgro & Hcr)".
  iAssert (hello_printf_ro hge) as "#Hpr".
  { iDestruct "Hgro" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & Hp)". iExact "Hp". }
  assert (E80 : sym_ptr (mkGenv hello_image_module img_globals fr) "hello#str.80" =
    mkPtr (img_a "hello#str.80") (Ro (img_a "hello#str.80"))) by (vm_compute; reflexivity).
  iEval (rewrite E80) in "H80".
  iMod (hello_priv_build (final_world w0 tb) fr with "H80 [Hgl Hcr]") as "HX".
  { rewrite /hello_hd_rest. iSplitL "Hgl"; [iExact "Hgl"|]. iSplitR; [iExact "Hgro" | iExact "Hcr"]. }
  pose (gg := getenv_globals (glibc_program := P tb) (DfracOwn (1/2)) (img_a "__environ_counter")
      (img_gd "__environ_counter") (img_a "__environ") (img_gd "__environ") 0 envp).
  pose (gs := getenv_storage (DfracOwn (1/2)) DfracDiscarded envp (env_entries m env)).
  iAssert (hello_main_priv env tb) with "[Gh1 Gh2 Hgo HX]" as "Hpv".
  { rewrite /hello_main_priv. iFrame "Gh1 Gh2 Hgo HX". }
  destruct (hello_hd_rules (final_world w0 tb) fr Hfree Herr (Hvf := hello_vfprintf_image (final_world w0 tb) fr (hello_link_all fr Hfree)) tb gs)
    as (Rd & Rl & Rn).
  apply (getopt_diag_rule_sep_l _ _ _ gg) in Rd. apply (getopt_ldiag_rule_sep_l _ _ _ gg) in Rl.
  assert (Hln : gg ∗ (gs ∗ hello_getopt_E (final_world w0 tb) fr tb) ⊢
    tcb_cleanup_inv (ow_self (final_world w0 tb)) ∗
    (tcb_cleanup_inv (ow_self (final_world w0 tb)) -∗ gg ∗ (gs ∗ hello_getopt_E (final_world w0 tb) fr tb))).
  { iIntros "[A B]". iDestruct (Rn with "B") as "[$ W]". iIntros "C". iFrame "A". iApply ("W" with "C"). }
  assert (Hg : hello_stdio (final_world w0 tb) hge o ∗ hello_main_priv env tb ⊢
    (gg ∗ (gs ∗ hello_getopt_E (final_world w0 tb) fr tb)) ∗
    (gg ∗ (gs ∗ hello_getopt_E (final_world w0 tb) fr tb) -∗ hello_stdio (final_world w0 tb) hge o ∗
      hello_main_priv env tb)).
  { rewrite /hello_main_priv. iIntros "H".
    iDestruct (hello_hd_lend (final_world w0 tb) fr tb Hfd2' (gg ∗ gs) _ with "H") as "[[[A B] C] W]".
    iFrame "A B C". iIntros "(A & B & C)". iApply ("W" with "[$A $B $C]"). }
  iMod (hello_main_entry (final_world w0 tb) m0 fr Hi (hello_link_all fr Hfree) (hello_main_priv env tb)
    (hello_getopt_E (final_world w0 tb) fr tb)
    (fun mid q => gg ∗ (gs ∗ hello_getopt_T (final_world w0 tb) fr tb mid q))%I
    hello_dom envp (env_entries m env) sz tb avb (reg_of m avb) p0 ps p0 (short_name p0 q0s) Hself Rd Rl Hln Hg
    with "[Hres] Hsz Hpv Hpr") as "Hpre"; [rewrite /hello_start_main_res; iSplitR; [iExact "Hrr"|]; iSplitR; [iExact "Hk145"|]; iSplitR; [iExact "H80" | iExact "Hres"]|].
  iModIntro. iExact "Hpre".
Qed.

End run.

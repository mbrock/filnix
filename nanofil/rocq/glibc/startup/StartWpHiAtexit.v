(** We want to show that hi_atexit never panics from the moment the
    runtime calls `c: __libc_start_main`. The proof of the startup body
    for hi_atexit is in [StartRunHiAtexit](StartRunHiAtexit.v). It asks
    its caller for two things. The caller owns the memory that the body
    reads, and it gives each of the three late calls what that call
    needs. This module supplies both. The theorem itself is in
    [StartSafeHiAtexit](StartSafeHiAtexit.v).

    ## The late calls

    After the body has made the thread, it calls early init, then the
    constructor runner, then the function that calls main. Each call
    leaves memory as the next one expects it. The constructors may run
    in any order, because the image does not record the order that the
    loader chose. *)

From Glibc Require Import Unit_string_memrchr_os Unit_string_strrchr_os.
From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv OsWorld OsRegistry OsStart OsCpuid StartCode StartCtors StartCtorRunnerSpec StartCtorRunner
  StartStdfilesInitSpec StartStdfilesInit StartCtorVtablesSpec StartCtorVtables StartInitMiscSpec StartInitMisc
  StartInitFirstSpec StartInitFirst StartCtorCalls StartCtorChain StrlenLogic StrrchrLogic
  MemrchrLogic HiAtexitGe HiAtexitModule HiAtexitInitial HiAtexitInitialStdout StartInitFirstImage
  StartVtablesImage StartStdfilesImage StartLogic StartLibcStartMain StartLsmImage StartEarlyInitSpec
  StartPtmallocInitSpec StartCtypeInitSpec StartTunableGetValSpec StartTlsInitTpSpec StartCallMainSpec
  CpuInitSpec CpuHiAtexit StartImageCpu StartImageEarly StartTunablesEarly StartState StartOwn StartJoin
  StartOwnHiAtexit HiAtexitStartBridge StartMainHiAtexit StartRunHiAtexit HiAtexitInitialList HiAtexitInitialAlloc HiAtexitMain WordString.
From Glibc Require LibioStdfiles.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** hi_atexit's image has exactly the three constructors that the chain
    knows. *)
Lemma hi_ctor_names : Permutation (ctor_names hi_module) [ctor_stdfiles; ctor_vtables; ctor_init_first].
Proof.
  assert (E : ctor_names hi_module = [ctor_stdfiles; ctor_vtables; ctor_init_first]) by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

(** ## The constructors

    The runner calls hi_atexit's three constructors in the table's order.
    [StartCtorChain](StartCtorChain.v) gives, for any image, the memory
    that each call keeps. This section fills in hi_atexit's addresses
    and proves the three contracts for its image. *)

Section ctors.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).

(** This is the linked hi_atexit program, run in world w. *)
Local Abbreviation P := (program_of w glibc_os_registry hge).

(** The loader may run the three constructors in any world that
    startup reaches. Each one keeps its contract there, because the
    image links the same code that its contract was proved for. *)
Lemma hi_ctor_specs :
  HasSpec glibc_os_registry (os_wi w) hge ctor_stdfiles (stdfiles_init_spec (glibc_program := P)) /\
  HasSpec glibc_os_registry (os_wi w) hge ctor_vtables (check_vtables_spec (glibc_program := P)) /\
  HasSpec glibc_os_registry (os_wi w) hge ctor_init_first (init_first_spec (glibc_program := P)).
Proof using Type.
  assert (D1 : Defines hge "glibc_stdfiles#_IO_stdfiles_init" LibioStdfiles.glibc_stdfiles_init)
    by (vm_compute; reflexivity).
  assert (D2 : Defines hge "glibc_vtables#check_stdfiles_vtables" start_check_vtables_fn) by (vm_compute; reflexivity).
  assert (D3 : Defines hge "glibc_init_first#_init_first" start_init_first_fn) by (vm_compute; reflexivity).
  assert (D4 : Defines hge "__init_misc" start_init_misc_fn) by (vm_compute; reflexivity).
  assert (D5 : Defines hge "__GI_strrchr" Unit_string_strrchr_os.fn___GI_strrchr) by (vm_compute; reflexivity).
  assert (D6 : Defines hge "__GI_strlen" glibc_strlen) by (vm_compute; reflexivity).
  assert (D7 : Defines hge "__GI___memrchr" Unit_string_memrchr_os.fn___GI___memrchr) by (vm_compute; reflexivity).
  pose proof (OsWorld.os_wi_stable w) as Hst.
  pose proof (strrchr_has_spec glibc_os_registry (os_wi w) hge "__GI_strrchr"
    (glibc_memrchr_spec glibc_os_registry (os_wi w) hge D7)) as Hs.
  pose proof (init_misc_has_spec (glibc_program := P)) as Hm.
  split; [exact (stdfiles_init_has_spec (glibc_program := P))|].
  split; [exact (check_vtables_has_spec (glibc_program := P))|].
  exact (init_first_has_spec (glibc_program := P)).
Qed.

(** The constructor `c: _init_first` reads argc, the argument array
    and the environment. This tuple gives those inputs: the array at av
    in region avreg, the share dq of it that the call reads, and the
    first string s at a. The startup body has already stored envp in
    `c: __environ`, so the global holds envp when the call begins. *)
Definition hi_xf (av : Z) (avreg : region) (dq : dfrac) (argc : Z) (envp a : ptr) (s : list Z) :=
  (hi_init_first_objs, hi_init_misc_objs av avreg, dq, argc, envp, a, s, hi_empty_name, hi_empty_name, null, envp).

(** This assertion describes hi_atexit's memory after the constructors
    in the list have run. *)
Definition hi_ctor_mem av avreg dq argc envp a s : list name -> iProp Σ :=
  ctor_mem (glibc_program := P) 71760 72240 72000 72480 (mkRegion 72480 72488 GlobalData Live)
    71648 (mkRegion 71648 71664 GlobalData Live) 71680 (mkRegion 71680 71688 GlobalData Live)
    73504 hi_vtables_reg (hi_xf av avreg dq argc envp a s).

(** In every order of the table, each constructor call keeps the memory
    that the next call expects. *)
Lemma hi_ctor_chain av avreg dq argc envp a s order :
  Permutation order (ctor_names hi_module) ->
  ctor_chain_ok (glibc_program := P) (chain_args (hi_xf av avreg dq argc envp a s))
    (hi_ctor_mem av avreg dq argc envp a s) order.
Proof using Type.
  intros Hp. destruct hi_ctor_specs as (H1 & H2 & H3).
  assert (D1 : Defines hge "glibc_stdfiles#_IO_stdfiles_init" LibioStdfiles.glibc_stdfiles_init)
    by (vm_compute; reflexivity).
  assert (D2 : Defines hge "glibc_vtables#check_stdfiles_vtables" start_check_vtables_fn) by (vm_compute; reflexivity).
  assert (D3 : Defines hge "glibc_init_first#_init_first" start_init_first_fn) by (vm_compute; reflexivity).
  apply (ctor_mem_chain (glibc_program := P)); [exact (proj1 (hi_vtables_ok w)) |].
  rewrite Hp. exact hi_ctor_names.
Qed.

(** After the last call, the memory is the three constructors'
    results. *)
Lemma hi_ctor_end av avreg dq argc envp a s order :
  Permutation order (ctor_names hi_module) ->
  hi_ctor_mem av avreg dq argc envp a s order ⊣⊢
  stdfiles_done (glibc_program := P) 71760 72240 72000 ∗
  init_first_done (glibc_program := P) (hi_xf av avreg dq argc envp a s) ∗
  vtables_cells (glibc_program := P) 71760 72240 72000 73504 hi_vtables_reg.
Proof using Type.
  intros Hp. apply ctor_mem_end. rewrite Hp. exact hi_ctor_names.
Qed.

End ctors.

(** ## Shares and pointers

    Several late calls read the same arrays, so each takes a share of
    their lives. The runner also checks each constructor's pointer
    before calling it. These lemmas give both. *)

(** Every pointer in the constructor table names its constructor and
    passes the function check. *)
Lemma hi_ctor_ptrs_ok order : Permutation order (ctor_names hi_module) ->
  Forall2 (fun g p => ptr_cap p = Fn g /\ function_check_res hge p = Some ok /\ 0 <= ptr_addr p < 2 ^ 64)
    order (ctor_ptrs hi_globals order).
Proof.
  intros Hp. assert (Hin : forall g, In g order -> In g [ctor_stdfiles; ctor_vtables; ctor_init_first]).
  { intros g H. apply (Permutation_in _ (perm_trans Hp hi_ctor_names) H). }
  clear Hp. unfold ctor_ptrs. induction order as [|g0 rest IH]; cbn [List.map]; constructor.
  - destruct (Hin g0 (or_introl eq_refl)) as [<-|[<-|[<-|[]]]];
      split_and!; vm_compute; first [reflexivity | intros H; discriminate H].
  - apply IH. intros g H. apply Hin. right. exact H.
Qed.

Section shares.
Context `{!gen_heapGS piece pval Σ}.

(** A share of an object's life splits into two halves. *)
Lemma liveq_half q b reg : liveq (DfracOwn q) b reg ⊣⊢ liveq (DfracOwn (q / 2)) b reg ∗ liveq (DfracOwn (q / 2)) b reg.
Proof using Type. rewrite /liveq -ptsq_split Qp.div_2. done. Qed.

(** A share of a stored pointer splits into two halves. *)
Lemma pcellq_half q b o p : pcellq (DfracOwn q) b o p ⊣⊢ pcellq (DfracOwn (q / 2)) b o p ∗ pcellq (DfracOwn (q / 2)) b o p.
Proof using Type. rewrite /pcellq -ptsq_split Qp.div_2. done. Qed.

(** A whole life splits into two halves. *)
Lemma live_halves b reg : live b reg ⊢ liveq (DfracOwn (1 / 2)) b reg ∗ liveq (DfracOwn (1 / 2)) b reg.
Proof using Type. iIntros "H". iApply liveq_half. rewrite /liveq -pts_ptsq. iExact "H". Qed.

(** A whole stored pointer splits into two halves. *)
Lemma pcell_halves b o p : pcell b o p ⊢ pcellq (DfracOwn (1 / 2)) b o p ∗ pcellq (DfracOwn (1 / 2)) b o p.
Proof using Type. iIntros "H". iApply pcellq_half. rewrite /pcellq -pts_ptsq. iExact "H". Qed.

(** The run takes the image's nine lists apart, one list at a time,
    because rewriting the whole sum at once is slow. *)
Lemma hi_start_all_split :
  pts hi_start_all_ps ⊢
  pts hi_cpu_globals_ps ∗ pts hi_early_ps ∗ pts hi_runner_ps ∗ pts hi_initial_list_ps ∗
  pts hi_init_first_ps ∗ pts hi_vtables_ps ∗ pts hi_start_kept_ps ∗ pts hi_lsm_ps ∗ pts hi_stdout_life_ps.
Proof using Type.
  rewrite /hi_start_all_ps. iIntros "H".
  do 8 (iDestruct (pts_app with "H") as "[$ H]"). iExact "H".
Qed.

(** The startup body writes five globals of its own. Each splits into
    its life and its bytes, and the two that hold pointers also give
    the slots for their capabilities. *)
Lemma hi_lsm_split :
  pts hi_lsm_ps ⊢
  live (lo_dx hi_lsm_objs) (lo_dxreg hi_lsm_objs) ∗ bytes (lo_dx hi_lsm_objs) 0 (repeat 0 8%nat) ∗
  auxes (lo_dx hi_lsm_objs) 0 (repeat CNone 8%nat) ∗
  live (lo_es hi_lsm_objs) (lo_esreg hi_lsm_objs) ∗ bytes (lo_es hi_lsm_objs) 0 [1; 0; 0; 0] ∗
  live (lo_dm hi_lsm_objs) (lo_dmreg hi_lsm_objs) ∗ bytes (lo_dm hi_lsm_objs) 0 (repeat 0 4%nat) ∗
  live (lo_re hi_lsm_objs) (lo_rereg hi_lsm_objs) ∗ bytes (lo_re hi_lsm_objs) 0 [0] ∗
  live (lo_se hi_lsm_objs) (lo_sereg hi_lsm_objs) ∗ bytes (lo_se hi_lsm_objs) 0 (repeat 0 8%nat) ∗
  auxes (lo_se hi_lsm_objs) 0 (repeat CNone 8%nat).
Proof using Type.
  rewrite /hi_lsm_ps (pts_app (obj_ps _ _)) (pts_app (obj_ps _ _)) (pts_app (obj_ps _ _)) (pts_app (obj_ps _ _))
    !obj_ps_own.
  iIntros "((? & ? & ?) & (? & ? & _) & (? & ? & _) & (? & ? & _) & (? & ? & ?))". iFrame.
Qed.

End shares.

(** ## The startup run

    The run owns the image's lists, the constructor table, argv,
    environ, the auxiliary vector and the startup key. The startup
    body borrows the globals it writes, and the three late calls then
    take what their contracts ask for. *)

Section run.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (k : Z).

Local Abbreviation P tb := (program_of (final_world w0 tb) glibc_os_registry hge).
Local Abbreviation P0 := (program_of (start_world w0 null false false) glibc_os_registry hge).

Local Instance safe_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi_start w0 k) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** Eight zero bytes with no capabilities are a stored null pointer. *)
Lemma zero_pcell b : bytes b 0 (repeat 0 8%nat) -∗ auxes b 0 (repeat CNone 8%nat) -∗ pcell b 0 null.
Proof using Type.
  assert (E1 : byte_ps b 0 (repeat 0 8%nat) = cell b 0 (ptr_addr null)) by reflexivity.
  assert (E2 : aux_ps b 0 (repeat CNone 8%nat) = (PAux b 0, VAux (ptr_cap null)) :: aux_ps b 1 (repeat CNone 7%nat))
    by reflexivity.
  rewrite /bytes /auxes /pcell E1 E2 (pts_app [_] (aux_ps _ _ _)). iIntros "H [A _]".
  rewrite (pts_app [_] (cell _ _ _)). iFrame.
Qed.

(** Startup may call main with any argument count and any two arrays.
    The call is checked before it happens, and it succeeds because the
    pointer names main, the environment pointer is one aligned global,
    and hi_atexit's main takes no arguments. *)
Lemma hi_cm_ok tb argc avb envb avreg evreg :
  0 <= argc < 2 ^ 32 -> 0 <= avb < 2 ^ 64 -> 0 <= envb < 2 ^ 64 ->
  cm_ok (glibc_program := P tb) (TAtom "main") []
    {| cm_en := 78768; cm_enreg := if_enreg hi_init_first_objs; cm_avreg := avreg; cm_evreg := evreg |}
    (mkPtr 65552 (Fn (TAtom "main"))) argc (mkPtr avb (Obj avb)) (mkPtr envb (Obj envb)).
Proof using Type.
  intros Ha Hv He. unfold cm_ok. cbn [ptr_cap ptr_addr cm_en cm_enreg].
  split_and!; try lia.
  - reflexivity.
  - change (function_check_res hge (mkPtr 65552 (Fn (TAtom "main"))) = Some ok). vm_compute. reflexivity.
  - change (lookup (TAtom "__environ") (ge_globals hge) = Some (mkPtr 78768 (Obj 78768))). vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. congruence.
  - intros gf Hf. change (find_fn hge (TAtom "main") = Some (Defined gf)) in Hf.
    rewrite hi_find_main in Hf. injection Hf as <-. split; [vm_compute; reflexivity|].
    intros d a b c. vm_compute. reflexivity.
Qed.

(** The run's memory, split into the parts the image proofs name, lets
    the startup body reach main and lets main run without a panic. *)
Lemma hi_start_wp fr m argv env av aps order argc :
  In 1 (ow_fds w0) -> ow_leaf4_ends w0 = true ->
  lookup (TAtom "__libc_errno") hi_globals = Some (ow_errno_cell w0) ->
  call_frame start_libc_start_main_fn
    [WPtr (mkPtr 65552 (Fn (TAtom "main"))); WInt argc; WPtr (mkPtr argv.1 (Obj argv.1));
     WPtr (mkPtr env.1 (Obj env.1)); WPtr (mkPtr av (Obj av))] = Some fr ->
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> auxv_array m av aps ->
  argc = Z.of_nat (length argv.2) -> 1 <= argc < 2 ^ 31 ->
  Permutation order (ctor_names hi_module) ->
  pts hi_start_all_ps -∗
  (bytes hi_runner_objs.2.1 0 (le_bytes argc 4) ∗ pcell hi_runner_objs.2.1 8 (mkPtr argv.1 (Obj argv.1)) ∗
   pcell hi_runner_objs.2.1 16 (mkPtr env.1 (Obj env.1)) ∗
   [∗ list] i ↦ p ∈ ctor_ptrs hi_globals order, pcell hi_runner_objs.2.1 (24 + 8 * Z.of_nat i) p) -∗
  pts (array_ps m argv) -∗ pts (array_ps m env) -∗
  (live av (reg_of m av) ∗ auxv_cells av 0 aps ∗ icell av (16 * Z.of_nat (length aps)) 0) -∗
  pointsto (PName k) (DfracOwn 1) (start_ghost null false false) -∗
  WP (ERun fr : sexpr) {{ _, ⌜False⌝ }}.
Proof using Type.
  intros Hfd Hleaf He Hfr Ha He2 Hv Hargc Hargc2 Hord.
  iIntros "Hall (Tc & Tv & Te & Tp) Harg Henv (La & Hc & Ht) Hk".
  iDestruct (hi_start_all_split with "Hall") as "(Hcpu & Hearly & Hrun & Hil & Hif & Hvt & Hkept & Hlsm & Hso)".
  iDestruct (hi_cpu_globals_own (start_world w0 null false false) with "Hcpu") as "(Lcf & Fcf & Ltl & Ttl & Lkn & Kkn & Sm)".
  iMod (early_own (glibc_program := P0) hi_ei_objs hi_pm_objs hi_ct_objs with "Ltl Hearly") as "(Ei & St & Pg & D16 & D32 & #Ro & Loc & Cl & Ccells & Pml & Li & Ta & Pf)".
  iDestruct "Pml" as "(Ltk & Leb & Lli & Laf & Lta & Lma & Lmp & Ltl)".
  iDestruct (hi_lsm_split with "Hlsm") as "(Ldx & Bdx & Adx & Les & Bes & Ldm & Bdm & Lre & Bre & Lse & Bse & Ase)".
  iDestruct (zero_pcell with "Bdx Adx") as "Hdx". iDestruct (zero_pcell with "Bse Ase") as "Hse".
  rewrite /hi_init_first_ps hi_pts_concat. cbn [big_opL].
  iDestruct "Hif" as "(Lac & Hac & Llv & Hlv & Len & Hen & Lpn & Hpn & Lpf & Hpf & _)".
  
  destruct Hv as ((avreg & [Eav Lav] & Hkav & Hav0 & Hava & Have & Has) & _ & Hpos & Hslots & _).
  assert (Rav : reg_of m av = avreg) by (unfold reg_of; rewrite Eav; reflexivity).
  pose proof (hi_lsm_image_ok) as Hok.
  iApply (hi_libc_start_main_wp w0 k fr _ (mkPtr 65552 (Fn (TAtom "main"))) argc (mkPtr argv.1 (Obj argv.1))
    (mkPtr env.1 (Obj env.1)) av (reg_of m av) aps (DfracOwn 1) (DfracOwn 1) 0 null (mkRegion 0 0 Heap Live)
    with "Hk Len [Hen] Ldx [Hdx] La Hc Ht Les [Bes] Ldm Bdm Leb [Lcf Fcf Ltl Ttl Lkn Kkn Sm] Lre Bre Lse Hse [] [-]").
  
  1: exact Hleaf. 1: exact He. 1: exact Hfr. 1: reflexivity. 1: lia. 1: exact Hav0.
  1: { rewrite Rav. assert (16 * Z.of_nat (length aps) + 8 <= (8 * (2 * Z.of_nat (length aps) + 1) + 15) / 16 * 16)
         by (Z.div_mod_to_equations; lia). lia. }
  1: { apply List.Forall_forall. intros [kk vv] Hin. destruct (In_nth_error _ _ Hin) as [i Hi].
       destruct (Hslots i kk vv Hi) as [[Hk0 _] [Hv0 _]].
       pose proof (proj1 (List.Forall_forall _ _) Hpos _ Hin) as Hp. cbn in Hp |- *. lia. }
  1: lia. 1: (cbn; lia).
  1: (iExists null; iExact "Hen").
  1: (iExists null; iExact "Hdx").
  1: (iExists 1; iExact "Bes").
  1: (rewrite /icf_owns; iFrame "Lcf Fcf Lkn Kkn Sm Ltl Ttl").
  1: done.
  iIntros (tb t a (Htb0 & Htb16 & Htbe & Ht0 & Hta)) "[_ Hicf] Ltb H0 H16 Htp H776 H784 H792 Lre Hre Lse Hse Hcap Len Hen Ldx Hdx La Hc Ht Les Hes Leb".
  destruct (hi_final_world_facts w0 tb He ltac:(lia)) as (Herr & Hself & Hfds).
  iDestruct "Hicf" as "(Lcf & Fcf & Ltl & Ttl & Lkn & Kkn & Sm)".
  iDestruct (icf_tunables_early (glibc_program := P tb) hi_pm_objs with "[Ttl]") as "[(%tv & Pt & T27) _]"; [iExact "Ttl"|].
  iExists (hi_ei_objs, hi_pm_objs, hi_ct_objs, tv, 1, 4096). iSplit; [done|].
  iSplitL "Ei St Pg D16 D32 Loc Cl Ccells Ltk Leb Lli Laf Lta Lma Lmp Ltl Pt T27 Li Ta Pf".
  { cbn [fs_pre early_init_spec]. destruct (hi_early_ok (final_world w0 tb) Herr) as (E1 & E2 & E3 & E4).
    iSplitR; [iPureIntro; split_and!; first [lia | assumption]|].
    rewrite /pm_lives. iFrame "Ei St Pg D16 D32 Ro Loc Cl Ccells Ltk Lli Laf Lta Lma Lmp Ltl Pt T27 Li Ta Pf". iExact "Leb". }
  iIntros (v3) "Hpost". cbn [fs_post early_init_spec].
  iDestruct "Hpost" as "(-> & Ei & St & Pg & D16 & D32 & Loc & Cl & Ccells & Pml & Pt & T27 & Li & Ta & Pf)".
  iSplit; [done|].
  
  destruct argv as [avb [|[q0b q0s] qs]]; cbn [length fst snd] in Hargc; [lia|].
  cbn [fst snd] in Ha. pose proof Ha as (Hah & Hsa & Han). destruct (Hsa 0%nat q0b q0s eq_refl) as [_ Hc0].
  pose proof Hah as (avr & [Eavr Lavr] & _ & Havb0 & Havb16 & Havbe & Havbs).
  pose proof He2 as ((evr & [Eevr Levr] & _ & Hevb0 & _ & Hevbe & Hevbs) & _).
  assert (Ravr : reg_of m avb = avr) by (unfold reg_of; rewrite Eavr; reflexivity).
  assert (Revr : reg_of m env.1 = evr) by (unfold reg_of; rewrite Eevr; reflexivity).
  iEval (rewrite /hi_runner_ps) in "Hrun". iDestruct (runner_own (glibc_program := P0) hi_runner_objs with "Hrun") as "(Lfl & Bfl & Ltt)".
  iDestruct (array_own with "Harg") as "(Lav & Pav & _ & Sav)". cbn [fst snd].
  iDestruct (array_own with "Henv") as "(Lev & _ & _ & _)".
  rewrite big_sepL_cons. iDestruct "Pav" as "[P0 _]". rewrite big_sepL_cons. iDestruct "Sav" as "[[Lq0 Bq0] _]".
  iDestruct (str_word_string m (q0b, q0s) Hc0 with "Lq0 Bq0") as "Ws". cbn [fst snd].
  iEval (rewrite -(Qp.div_2 1) word_string_split) in "Ws". iDestruct "Ws" as "[Ws _]".
  iDestruct (pcell_halves with "P0") as "[P0 _]".
  iDestruct (live_halves with "Lav") as "[Lav1 Lav]".
  iDestruct (liveq_half (1/2) with "Lav") as "[Lav2 Lav3]".
  iDestruct (live_halves with "Lev") as "[Lev _]".
  iDestruct (liveq_half (1/2) with "Lev") as "[Lev2 Lev3]".
  set (c := {| cr_fl := hi_runner_objs.1.1; cr_flreg := hi_runner_objs.1.2; cr_tb := hi_runner_objs.2.1;
    cr_treg := hi_runner_objs.2.2; cr_dq := DfracOwn 1; cr_argc := argc; cr_argv := mkPtr avb (Obj avb);
    cr_avreg := reg_of m avb; cr_env := mkPtr env.1 (Obj env.1); cr_enreg := reg_of m env.1;
    cr_adq := DfracOwn (1/2/2); cr_order := order; cr_ptrs := ctor_ptrs hi_globals order |}).
  iExists (c, hi_ctor_mem (final_world w0 tb) avb (reg_of m avb) (DfracOwn (1/2)) argc (mkPtr env.1 (Obj env.1))
    (mkPtr q0b (Obj q0b)) q0s). iSplit; [done|].
  
  iSplitL "Lfl Bfl Ltt Tc Tv Te Tp Lav2 Lev2 Hil Hso Lac Hac Llv Hlv Len Hen Lpn Hpn Lpf Hpf Lav1 P0 Ws Hvt".
  { cbn [fs_pre ctor_runner_spec]. iSplitR.
    { iPureIntro. split.
      - destruct hi_runner_ok as (R1 & R2 & R3 & R4 & R5).
        refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj _ (conj _ (conj _ (conj _ _))))))))).
        + unfold c; cbn [cr_order]. rewrite (Permutation_length Hord). vm_compute. reflexivity.
        + unfold c; cbn [cr_argc]. lia.
        + unfold c; cbn [cr_argv ptr_addr]. Z.div_mod_to_equations; lia.
        + unfold c; cbn [cr_env ptr_addr]. Z.div_mod_to_equations; lia.
        + unfold c; cbn [cr_order cr_ptrs]. exact (hi_ctor_ptrs_ok order Hord).
      - unfold c; cbn [cr_order cr_args cr_argc cr_argv cr_env]. exact (hi_ctor_chain (final_world w0 tb) avb (reg_of m avb) (DfracOwn (1/2)) argc _ _ q0s order Hord). }
    iFrame "Lfl Bfl". iSplitL "Ltt Tc Tv Te Tp Lav2 Lev2".
    { rewrite /cr_table /liveq /bytesq /pcellq. unfold c. cbn [cr_dq cr_tb cr_treg cr_argc cr_argv cr_env cr_ptrs cr_adq cr_avreg cr_enreg ptr_cap].
      rewrite -!pts_ptsq. iFrame "Tc Tv Te Tp Lav2 Lev2". iExact "Ltt". }
  
    rewrite /hi_ctor_mem ctor_mem_start.
    iSplitL "Hil Hso".
    { iApply (hi_stdfiles_init_pre (final_world w0 tb) with "Hil [Hso]"). rewrite /hi_stdout_life_ps. iExact "Hso". }
    iSplitL "Lac Hac Llv Hlv Len Hen Lpn Hpn Lpf Hpf Lav1 P0 Ws".
    { cbn [fs_pre init_first_spec hi_xf]. iSplit.
      { iPureIntro. split; [vm_compute; intuition congruence|]. split; [lia|].
        unfold im_ok. cbn [im_pn im_pnreg im_pf im_pfreg im_av im_avreg hi_init_misc_objs].
        split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
        split; [reflexivity|]. split; [vm_compute; congruence|]. split; [reflexivity|]. split; [vm_compute; congruence|].
        split; [exact Havb0|]. split; [Z.div_mod_to_equations; lia|]. rewrite Ravr. Z.div_mod_to_equations; lia. }
      iSplitL "Lac Llv Len"; [rewrite /if_lives; iFrame "Lac Llv"; iExact "Len"|].
      iSplitL "Hac"; [iExists (int_bytes 0); iSplit; [done|iExact "Hac"]|].
      iSplitL "Hlv"; [iExact "Hlv"|]. iSplitL "Hen"; [iExact "Hen"|].
      iSplitR "Lav1 P0 Ws"; [rewrite /im_names; iFrame "Lpn Hpn Lpf Hpf"|].
      rewrite /im_args. iFrame "Lav1 Ws". iExact "P0". }
    iDestruct (hi_vtables_cells with "Hvt") as "(Ci & Co & Ce & Lv)". rewrite /vtables_cells. iFrame. }
  
  iIntros (v4) "Hpost". cbn [fs_post ctor_runner_spec]. iDestruct "Hpost" as "(-> & _ & _ & _ & K)". iSplit; [done|].
  iEval (rewrite (hi_ctor_end _ _ _ _ _ _ _ _ (cr_order c) Hord)) in "K". iDestruct "K" as "((Io & Sl) & Ifd & Vc)".
  cbn [init_first_done hi_xf]. rewrite /if_lives /vtables_cells. cbn [hi_init_first_objs if_en if_enreg].
  iDestruct "Ifd" as "((_ & _ & Len) & _ & _ & Ien & _ & _)". iDestruct "Vc" as "(_ & Co & _ & Lv)".
  iDestruct (live_halves with "Len") as "[Len _]". iDestruct (liveq_half with "Len") as "[Len _]".
  iDestruct (pcell_halves with "Ien") as "[Ien _]". iDestruct (pcellq_half with "Ien") as "[Ien _]".
  iExists (tt, {| cm_en := 78768; cm_enreg := if_enreg hi_init_first_objs; cm_avreg := reg_of m avb;
    cm_evreg := reg_of m env.1 |}, DfracOwn (1/2/2), mkPtr 65552 (Fn (TAtom "main")), argc, mkPtr avb (Obj avb),
    mkPtr env.1 (Obj env.1)).
  iSplit; [done|].
  iSplitL; [|iIntros (v5) "[]"].
  rewrite /hi_cm_spec. cbn [fs_pre fs_args start_call_main_spec hi_main_spec].
  iSplitR; [iPureIntro; apply hi_cm_ok; Z.div_mod_to_equations; lia|].
  assert (Oc : off_cleanup = 776) by reflexivity. assert (Oj : off_cleanup_jmp = 784) by reflexivity.
  assert (Oh : off_cancelhandling = 792) by reflexivity.
  iSplitL "Ltb H776 H784 H792".
  { iExists tb, _. rewrite Oc Oj Oh. iFrame "Ltb H776 H784 H792". iPureIntro. cbn [r_end].
    split_and!; [reflexivity|lia|Z.div_mod_to_equations; lia|lia|lia]. }
  iSplitL "Len Ien Lav3 Lev3".
  { rewrite /cm_reads. cbn [cm_en cm_enreg cm_avreg cm_evreg ptr_cap live_capq]. iFrame. }
  iSplitR "".
  2: { iIntros (r) "[]". }
  iIntros "Tci _". iApply (hi_start_post_main (final_world w0 tb) with "[-Tci] Tci").
  { rewrite Hfds. exact Hfd. }
  rewrite /hi_start_post. rewrite /ei_lives /pm_lives /pm_fields.
  iDestruct "Ei" as "(Lst & _)". iDestruct "Pf" as "(_ & Eb & _)". iDestruct "Pml" as "(_ & _ & _ & _ & _ & _ & Lmp & _)".
  iSplitL "Hkept"; [iExact "Hkept"|]. iSplitL "Io"; [iExact "Io"|]. iSplitL "Sl"; [iExact "Sl"|].
  iSplitL "Lst"; [iExact "Lst"|]. iSplitL "St"; [iExact "St"|]. iSplitL "Eb"; [iExact "Eb"|].
  iSplitL "Lmp"; [iExact "Lmp"|]. iSplitL "Lv"; [iExact "Lv"|]. iExact "Co".
Qed.

End run.

(** We want to show that hi_atexit never panics from the moment the
    runtime calls `c: __libc_start_main`. One proof of that function's
    body, in [StartLibcStartMain](StartLibcStartMain.v), serves every
    program, so it asks its caller many questions about the program.
    This module answers all of them for hi_atexit, except two: which
    memory the body reads, and how each late call hands over to the
    next.

    ## Why nothing here is new

    Every fact that the startup proof asks about hi_atexit was already
    proved, either about its image or about the code of one of its
    calls. So this module adds no reasoning of its own. It checks that
    the image matches what the startup proof expects and passes the
    contracts along. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry OsStart OsStartCalls OsCpuid StartCtors StartLogic HiAtexitGe
  HiAtexitModule HiAtexitInitial StartCode StartTlsInitTp StartSetupTlsSpec StartSetupTls CpuInitSpec CpuHiAtexit
  StartTlsInitTpSpec StartLibcStartMain StartLsmImage StartEarlyInitSpec StartCtorRunnerSpec StartMainHiAtexit.
From Glibc Require FileInv.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** The image keeps `c: __libc_errno` in this region. *)
Definition hi_errno_reg : region :=
  Eval vm_compute in match object_region 70608 (m_regions hi_m0) with Some r => r | None => mkRegion 0 0 GlobalData Live end.

Section run.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (k : Z).

(** After startup creates its thread tb, the three late calls all run
    in one fixed world, and this abbreviation names that setting. *)
Local Abbreviation P tb := (program_of (final_world w0 tb) glibc_os_registry hge).

(** The CPU code runs hi_atexit in the start world, before any
    cookie or handler exists. *)
Local Abbreviation P0 := (program_of (start_world w0 null false false) glibc_os_registry hge).

Local Instance run_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi_start w0 k) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** We want the startup body of hi_atexit to reach main without a
    panic. This lemma needs only two things from its caller: the memory
    that the body reads, and a way to turn each late call's result into
    the next call's needs. Everything else is already known about
    hi_atexit. *)
Lemma hi_libc_start_main_wp fr xs mainp argc argv envp av avreg ps dqm dqe x sp spreg Φ :
  ow_leaf4_ends w0 = true ->
  lookup (TAtom "__libc_errno") hi_globals = Some (ow_errno_cell w0) ->
  call_frame start_libc_start_main_fn xs = Some fr ->
  xs = [WPtr mainp; WInt argc; WPtr argv; WPtr envp; WPtr (mkPtr av (Obj av))] ->
  0 <= argc < 2 ^ 32 ->
  0 < av -> av + 16 * Z.of_nat (length ps) + 8 <= r_end avreg ->
  Forall (fun kv => 0 < kv.1 < 2 ^ 64 /\ 0 <= kv.2 < 2 ^ 64) ps ->
  0 <= x < 256 -> 0 <= ptr_addr sp < 2 ^ 64 ->
  let o := hi_lsm_objs in
  pointsto (PName k) (DfracOwn 1) (start_ghost null false false) -∗
  live (lo_en o) (lo_enreg o) -∗ (∃ p, pcell (lo_en o) 0 p) -∗
  live (lo_dx o) (lo_dxreg o) -∗ (∃ p, pcell (lo_dx o) 0 p) -∗
  live av avreg -∗ auxv_cells av 0 ps -∗ icell av (16 * Z.of_nat (length ps)) 0 -∗
  live (lo_es o) (lo_esreg o) -∗ (∃ y, bytes (lo_es o) 0 (le_bytes y 4)) -∗
  liveq dqm (lo_dm o) (lo_dmreg o) -∗ bytesq dqm (lo_dm o) 0 [0; 0; 0; 0] -∗
  liveq dqe 70608 hi_errno_reg -∗
  icf_owns (glibc_program := P0) hi_icf_objs -∗
  live (lo_re o) (lo_rereg o) -∗ ibyte (lo_re o) 0 x -∗
  live (lo_se o) (lo_sereg o) -∗ pcell (lo_se o) 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
  (∀ tb t a, ⌜0 < tb /\ tb mod 16 = 0 /\ tb + 2496 <= 2 ^ 48 /\ 0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ -∗
     (⌜RetVoid = RetVoid⌝ ∗ icf_owns (glibc_program := P0) hi_icf_objs) -∗
     live tb (mkRegion tb (tb + 2496) Heap Live) -∗
     pcell tb 0 (mkPtr tb (Obj tb)) -∗ pcell tb 16 (mkPtr tb (Obj tb)) -∗ tp_fields tb t a x sp -∗
     pcell tb 776 null -∗ pcell tb 784 null -∗ bytes tb 792 [0; 0; 0; 0] -∗
     live (lo_re o) (lo_rereg o) -∗ ibyte (lo_re o) 0 x -∗
     live (lo_se o) (lo_sereg o) -∗ pcell (lo_se o) 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
     live (lo_en o) (lo_enreg o) -∗ pcell (lo_en o) 0 envp -∗
     live (lo_dx o) (lo_dxreg o) -∗ pcell (lo_dx o) 0 (mkPtr av (Obj av)) -∗
     live av avreg -∗ auxv_cells av 0 ps -∗ icell av (16 * Z.of_nat (length ps)) 0 -∗
     live (lo_es o) (lo_esreg o) -∗ (∃ y, bytes (lo_es o) 0 (le_bytes y 4)) -∗ liveq dqe 70608 hi_errno_reg -∗
     ∃ x3, ⌜fs_args (early_init_spec (glibc_program := P tb)) x3 = [WInt 1]⌝ ∗
       fs_pre (early_init_spec (glibc_program := P tb)) x3 ∗
     ∀ v3, fs_post (early_init_spec (glibc_program := P tb)) x3 v3 -∗ ⌜v3 = RetVoid⌝ ∗
     ∃ x4, ⌜fs_args (ctor_runner_spec (glibc_program := P tb)) x4 = []⌝ ∗
       fs_pre (ctor_runner_spec (glibc_program := P tb)) x4 ∗
     ∀ v4, fs_post (ctor_runner_spec (glibc_program := P tb)) x4 v4 -∗ ⌜v4 = RetVoid⌝ ∗
     ∃ x5, ⌜fs_args (hi_cm_spec w0 tb) x5 = [WPtr mainp; WInt argc; WPtr argv]⌝ ∗ fs_pre (hi_cm_spec w0 tb) x5 ∗
     ∀ v5, fs_post (hi_cm_spec w0 tb) x5 v5 -∗ False) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hleaf He Hfr Hxs Hargc Hav Have Hps Hx Hsp o.
  pose proof hi_lsm_image_ok as Hok.
  destruct Hok as (Fsm & Fer & Fdl & Gpm & Gen & Hena & Hene & Gdx & Hdxa & Hdxe & Ges & Hese & Gdm & Hdma & Hdme &
    Gcf & Gre & Gse & Hree & Hsea & Hsee & Ghp & Hhp & Gdp & Hdp).
  assert (Ee : ow_errno_cell w0 = mkPtr 70608 (Obj 70608)).
  { assert (L : lookup (TAtom "__libc_errno") hi_globals = Some (mkPtr 70608 (Obj 70608))) by (vm_compute; reflexivity).
    rewrite L in He. injection He as <-. reflexivity. }
  assert (Hicf : HasSpec glibc_os_registry (os_wi (start_world w0 null false false)) hge
                   (TAtom "glibc_libc_start#init_cpu_features") (init_cpu_features_spec (glibc_program := P0)))
    by (apply hi_init_cpu_features_has_spec; exact Hleaf).
  assert (Htls : HasSpec glibc_os_registry (os_wi_start w0 k) hge (TAtom "__libc_setup_tls") (setup_tls_spec hge k)).
  { assert (Dtp : Defines hge "__tls_init_tp" start_tls_init_tp_fn).
    { unfold Defines, find_fn. change (ge_module hge) with hi_module.
      rewrite start_tls_init_tp_defined. reflexivity. }
    apply setup_tls_has_spec; [| | reflexivity | split; vm_compute; reflexivity].
    - intros tb. apply (tls_init_tp_has_spec (glibc_program :=
        program_of (start_world w0 (mkPtr tb (Obj tb)) false false) glibc_os_registry hge) tb);
        try reflexivity; try (split; vm_compute; reflexivity).
    - unfold find_fn. change (ge_module hge) with hi_module. rewrite start_setup_tls_defined. reflexivity. }
  pose proof (fun tb (H0 : 0 < tb) (H1 : tb + 2496 <= 2 ^ 48) => hi_early_init_has_spec w0 tb) as Hei.
  pose proof (fun tb (H0 : 0 < tb) (H1 : tb + 2496 <= 2 ^ 48) => hi_ctor_runner_has_spec w0 tb) as Hcr.
  pose proof (fun tb (H0 : 0 < tb) (H1 : tb + 2496 <= 2 ^ 48) => hi_call_main_has_spec w0 tb He ltac:(lia)) as Hcm.
  iIntros "Hk Len Hen Ldx Hdx La Hc Ht Les Hes Ldm Hdm Leb Hicf Lre Hre Lse Hse Hcap HK".
  iApply (wp_libc_start_main glibc_os_registry hge w0 k fr xs mainp argc argv envp av avreg ps
    (lo_en o) (lo_enreg o) (lo_dx o) (lo_dxreg o) (lo_es o) (lo_esreg o) (lo_dm o) (lo_dmreg o) dqm
    70608 hi_errno_reg dqe (lo_hp o) (lo_dp o) (lo_dn o) (lo_cfp o)
    (init_cpu_features_spec (glibc_program := P0)) hi_icf_objs (lo_re o) (lo_rereg o) x (lo_se o) (lo_sereg o)
    sp spreg (fun tb => early_init_spec (glibc_program := P tb)) (fun tb => ctor_runner_spec (glibc_program := P tb))
    (fun tb => hi_cm_spec w0 tb) Φ (Hicf := Hicf) (Htls := Htls) Hei Hcr Hcm
    with "Hk Len Hen Ldx Hdx La Hc Ht Les Hes Ldm Hdm Leb [Hicf] Lre Hre Lse Hse Hcap HK");
    try assumption; [reflexivity | reflexivity | reflexivity | ..].
  - vm_compute. reflexivity.
  - intros v. cbn [fs_post init_cpu_features_spec]. iIntros "[-> H]". iSplit; [done|]. iSplit; [done|]. iExact "H".
  - discriminate.
  - reflexivity.
  - cbn [fs_pre init_cpu_features_spec]. iSplit; [iPureIntro; apply hi_icf_ok|]. iExact "Hicf".
Qed.

End run.

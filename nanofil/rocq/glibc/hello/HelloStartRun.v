(** We want to show that GNU Hello never panics from the moment the
    runtime calls `c: __libc_start_main`. One proof of that function's
    body, in [StartLibcStartMain](../startup/StartLibcStartMain.v),
    serves every program, so it asks its caller many questions about
    the program. This module answers all of them for Hello, except two:
    which memory the body reads, and how each late call hands over to
    the next. [StartRunHiAtexit](../startup/StartRunHiAtexit.v) does the
    same for hi_atexit, and this module follows it line by line.

    ## Why nothing here is new

    Every fact that the startup proof asks about Hello was already
    proved, either about its image or about the code of one of its
    calls. So this module adds no reasoning of its own. It checks that
    the image matches what the startup proof expects and passes the
    contracts along. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry OsStart OsStartCalls OsCpuid StartCtors StartLogic
  HelloImageModule HelloImageLoad HelloImageEarly HelloGlibcDebts HelloGlibcLibsT HelloStartBridge
  StartCode StartTlsInitTp StartSetupTlsSpec StartSetupTls CpuInitSpec CpuHello StartImageEarly
  StartTlsInitTpSpec StartLibcStartMain StartLsmImage StartLsmHello StartEarlyInitSpec StartCtorRunnerSpec StartPtmallocInitSpec
  HelloStartMain.
From Glibc Require FileInv.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section run.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (k : Z).
Context (m : mem) (fr : word -> mem -> option (res unit * mem)).
Context (Hi : initial_memory hello_image_module = Some (img_globals, m)).

(** Main takes the private state of the thread that startup creates.
    The library proofs use that same state. *)
Context (o : hello_objs) (priv : Z -> iProp Σ)
  (X0 X : iProp Σ)
  (Lb : forall tb, 0 < tb -> tb + 2496 <= 2 ^ 48 ->
     HelloLibs (final_world w0 tb) (mkGenv hello_image_module img_globals fr) o
       (priv tb) X0 X)
  (Hy : hello_layout (mkGenv hello_image_module img_globals fr) o).

(** This is the linked Hello program. *)
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).

(** After startup creates its thread tb, the three late calls all run
    in one fixed world, and this abbreviation names that setting. *)
Local Abbreviation P tb := (program_of (final_world w0 tb) glibc_os_registry hge).

(** The CPU code runs Hello in the start world, before any cookie or
    handler exists. *)
Local Abbreviation P0 := (program_of (start_world w0 null false false) glibc_os_registry hge).

(** The image keeps `c: __libc_errno` at this address and region. *)
Local Abbreviation eb := (pm_eb hello_pm_objs).
Local Abbreviation ereg := (pm_ereg hello_pm_objs).

Local Instance run_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi_start w0 k) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** We want the startup body of Hello to reach main without a panic.
    This lemma needs only two things from its caller: the memory that
    the body reads, and a way to turn each late call's result into the
    next call's needs. Everything else is already known about Hello. *)
Lemma hello_libc_start_main_wp fr0 xs mainp argc argv envp av avreg ps dqm dqe x sp spreg Φ :
  ow_leaf4_ends w0 = true ->
  lookup (TAtom "__libc_errno") img_globals = Some (ow_errno_cell w0) ->
  call_frame start_libc_start_main_fn xs = Some fr0 ->
  xs = [WPtr mainp; WInt argc; WPtr argv; WPtr envp; WPtr (mkPtr av (Obj av))] ->
  0 <= argc < 2 ^ 32 ->
  0 < av -> av + 16 * Z.of_nat (length ps) + 8 <= r_end avreg ->
  Forall (fun kv => 0 < kv.1 < 2 ^ 64 /\ 0 <= kv.2 < 2 ^ 64) ps ->
  0 <= x < 256 -> 0 <= ptr_addr sp < 2 ^ 64 ->
  let lo := hello_lsm_objs in
  pointsto (PName k) (DfracOwn 1) (start_ghost null false false) -∗
  live (lo_en lo) (lo_enreg lo) -∗ (∃ p, pcell (lo_en lo) 0 p) -∗
  live (lo_dx lo) (lo_dxreg lo) -∗ (∃ p, pcell (lo_dx lo) 0 p) -∗
  live av avreg -∗ auxv_cells av 0 ps -∗ icell av (16 * Z.of_nat (length ps)) 0 -∗
  live (lo_es lo) (lo_esreg lo) -∗ (∃ y, bytes (lo_es lo) 0 (le_bytes y 4)) -∗
  liveq dqm (lo_dm lo) (lo_dmreg lo) -∗ bytesq dqm (lo_dm lo) 0 [0; 0; 0; 0] -∗
  liveq dqe eb ereg -∗
  icf_owns (glibc_program := P0) hello_icf_objs -∗
  live (lo_re lo) (lo_rereg lo) -∗ ibyte (lo_re lo) 0 x -∗
  live (lo_se lo) (lo_sereg lo) -∗ pcell (lo_se lo) 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
  (∀ tb t a, ⌜0 < tb /\ tb mod 16 = 0 /\ tb + 2496 <= 2 ^ 48 /\ 0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ -∗
     (⌜RetVoid = RetVoid⌝ ∗ icf_owns (glibc_program := P0) hello_icf_objs) -∗
     live tb (mkRegion tb (tb + 2496) Heap Live) -∗
     pcell tb 0 (mkPtr tb (Obj tb)) -∗ pcell tb 16 (mkPtr tb (Obj tb)) -∗ tp_fields tb t a x sp -∗
     pcell tb 776 null -∗ pcell tb 784 null -∗ bytes tb 792 [0; 0; 0; 0] -∗
     live (lo_re lo) (lo_rereg lo) -∗ ibyte (lo_re lo) 0 x -∗
     live (lo_se lo) (lo_sereg lo) -∗ pcell (lo_se lo) 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
     live (lo_en lo) (lo_enreg lo) -∗ pcell (lo_en lo) 0 envp -∗
     live (lo_dx lo) (lo_dxreg lo) -∗ pcell (lo_dx lo) 0 (mkPtr av (Obj av)) -∗
     live av avreg -∗ auxv_cells av 0 ps -∗ icell av (16 * Z.of_nat (length ps)) 0 -∗
     live (lo_es lo) (lo_esreg lo) -∗ (∃ y, bytes (lo_es lo) 0 (le_bytes y 4)) -∗ liveq dqe eb ereg -∗
     ∃ x3, ⌜fs_args (early_init_spec (glibc_program := P tb)) x3 = [WInt 1]⌝ ∗
       fs_pre (early_init_spec (glibc_program := P tb)) x3 ∗
     ∀ v3, fs_post (early_init_spec (glibc_program := P tb)) x3 v3 -∗ ⌜v3 = RetVoid⌝ ∗
     ∃ x4, ⌜fs_args (ctor_runner_spec (glibc_program := P tb)) x4 = []⌝ ∗
       fs_pre (ctor_runner_spec (glibc_program := P tb)) x4 ∗
     ∀ v4, fs_post (ctor_runner_spec (glibc_program := P tb)) x4 v4 -∗ ⌜v4 = RetVoid⌝ ∗
     ∃ x5, ⌜fs_args (hello_cm_spec w0 img_globals fr o priv X0 tb) x5 = [WPtr mainp; WInt argc; WPtr argv]⌝ ∗
       fs_pre (hello_cm_spec w0 img_globals fr o priv X0 tb) x5 ∗
     ∀ v5, fs_post (hello_cm_spec w0 img_globals fr o priv X0 tb) x5 v5 -∗ False) -∗
  WP (ERun fr0 : sexpr) {{ Φ }}.
Proof using Hi Lb Hy.
  intros Hleaf He Hfr Hxs Hargc Hav Have Hps Hx Hsp lo.
  pose proof (hello_lsm_image_ok img_globals m fr Hi) as Hok.
  destruct Hok as (Fsm & Fer & Fdl & Gpm & Gen & Hena & Hene & Gdx & Hdxa & Hdxe & Ges & Hese & Gdm & Hdma & Hdme &
    Gcf & Gre & Gse & Hree & Hsea & Hsee & Ghp & Hhp & Gdp & Hdp).
  assert (Ee : ow_errno_cell w0 = mkPtr eb (Obj eb)).
  { assert (L : lookup (TAtom "__libc_errno") img_globals = Some (mkPtr eb (Obj eb))) by (vm_compute; reflexivity).
    rewrite L in He. injection He as <-. reflexivity. }
  assert (Hicf : HasSpec glibc_os_registry (os_wi (start_world w0 null false false)) hge
                   (TAtom "glibc_libc_start#init_cpu_features") (init_cpu_features_spec (glibc_program := P0)))
    by (apply (hello_init_cpu_features_has_spec _ img_globals m fr Hi); exact Hleaf).
  pose proof (hello_setup_tls_has_spec w0 img_globals m fr Hi k) as Htls.
  pose proof (fun tb (H0 : 0 < tb) (H1 : tb + 2496 <= 2 ^ 48) => hello_early_init_has_spec w0 img_globals m fr Hi tb)
    as Hei.
  pose proof (fun tb (H0 : 0 < tb) (H1 : tb + 2496 <= 2 ^ 48) => hello_ctor_runner_has_spec w0 img_globals fr tb)
    as Hcr.
  pose proof (hello_call_main_has_spec w0 img_globals m fr Hi o priv X0 X Lb Hy) as Hcm.
  iIntros "Hk Len Hen Ldx Hdx La Hc Ht Les Hes Ldm Hdm Leb Hicf Lre Hre Lse Hse Hcap HK".
  iApply (wp_libc_start_main glibc_os_registry hge w0 k fr0 xs mainp argc argv envp av avreg ps
    (lo_en lo) (lo_enreg lo) (lo_dx lo) (lo_dxreg lo) (lo_es lo) (lo_esreg lo) (lo_dm lo) (lo_dmreg lo) dqm
    eb ereg dqe (lo_hp lo) (lo_dp lo) (lo_dn lo) (lo_cfp lo)
    (init_cpu_features_spec (glibc_program := P0)) hello_icf_objs (lo_re lo) (lo_rereg lo) x (lo_se lo) (lo_sereg lo)
    sp spreg (fun tb => early_init_spec (glibc_program := P tb)) (fun tb => ctor_runner_spec (glibc_program := P tb))
    (fun tb => hello_cm_spec w0 img_globals fr o priv X0 tb) Φ (Hicf := Hicf) (Htls := Htls) Hei Hcr Hcm
    with "Hk Len Hen Ldx Hdx La Hc Ht Les Hes Ldm Hdm Leb [Hicf] Lre Hre Lse Hse Hcap HK");
    try assumption; [reflexivity | reflexivity | reflexivity | ..].
  - vm_compute. reflexivity.
  - intros v. cbn [fs_post init_cpu_features_spec]. iIntros "[-> H]". iSplit; [done|]. iSplit; [done|]. iExact "H".
  - discriminate.
  - reflexivity.
  - cbn [fs_pre init_cpu_features_spec]. iSplit; [iPureIntro; exact (hello_icf_ok _ img_globals m fr Hi)|].
    iExact "Hicf".
Qed.

End run.

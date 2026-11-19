(** After startup has initialized libc, its constructor runner calls
    Hello's three constructors in the order of the table. The runner's
    contract asks for one assertion that each call keeps, whatever ran
    before it. [StartCtorChain](../startup/StartCtorChain.v) gives that
    assertion for any image with these three constructors, given the
    addresses of the streams and the inputs of `c: _init_first`. This
    module fills in Hello's addresses, proves the three contracts for
    Hello's image, and shows that the image's start lists give the
    assertion before the first call. *)

From Glibc Require Fix.
From Glibc Require Import Unit_string_memrchr_os Unit_string_strrchr_os.
From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import FileInv OsWorld OsRegistry StartCode StartCtors StartCtorRunnerSpec
  StartStdfilesInitSpec StartStdfilesInit StartCtorVtablesSpec StartCtorVtables StartInitMiscSpec StartInitMisc
  StartInitFirstSpec StartInitFirst StartCtorChain StrlenLogic StrrchrLogic
  MemrchrLogic
  HelloImageModule HelloImageLoad HelloImageCtors.
From Glibc Require LibioStdfiles.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** Hello's image has exactly the three constructors that the chain
    knows. *)
Lemma hello_ctor_names : Permutation (ctor_names hello_image_module) [ctor_stdfiles; ctor_vtables; ctor_init_first].
Proof.
  assert (E : ctor_names hello_image_module = [ctor_stdfiles; ctor_vtables; ctor_init_first])
    by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

Section ctors.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world) (m : mem).
Context (fr : word -> mem -> option (res unit * mem)).
Context (Hi : initial_memory hello_image_module = Some (img_globals, m)).

(** This is the linked Hello program, run in world w. *)
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
Local Abbreviation P := (program_of w glibc_os_registry hge).

(** ## The three contracts *)

(** Each constructor of Hello's image keeps its contract in world w,
    because the image defines it with the body that the contract was
    proved for. *)
Lemma hello_ctor_specs :
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

(** ## The memory between calls *)

(** This tuple holds the inputs of `c: _init_first`. The argument array
    lies at av in region avreg, and the call reads a share dq of it. The
    array's first string is s, which lies at a. The body of
    `c: __libc_start_main` has already stored envp in `c: __environ`. *)
Definition hello_xf (av : Z) (avreg : region) (dq : dfrac) (argc : Z) (envp a : ptr) (s : list Z) :=
  (hello_init_first_objs, hello_init_misc_objs av avreg, dq, argc, envp, a, s,
   hello_empty_name, hello_empty_name, null, envp).

(** This assertion describes Hello's memory after the constructors in
    the list have run. *)
Definition hello_ctor_mem av avreg dq argc envp a s : list name -> iProp Σ :=
  ctor_mem (glibc_program := P) (img_a "_IO_2_1_stderr_") (img_a "_IO_2_1_stdout_") (img_a "_IO_2_1_stdin_")
    (img_a "__GI__IO_list_all") (img_gd "__GI__IO_list_all")
    (img_a "glibc_genops#list_all_lock") (img_gd "glibc_genops#list_all_lock")
    (img_a "glibc_genops#run_fp") (img_gd "glibc_genops#run_fp")
    (img_a "__io_vtables") (img_gd "__io_vtables") (hello_xf av avreg dq argc envp a s).

(** In every order of the table, each constructor call keeps the
    memory that the next call expects. *)
Lemma hello_ctor_chain av avreg dq argc envp a s order :
  Permutation order (ctor_names hello_image_module) ->
  ctor_chain_ok (glibc_program := P) (chain_args (hello_xf av avreg dq argc envp a s))
    (hello_ctor_mem av avreg dq argc envp a s) order.
Proof using Hi.
  intros Hp. destruct hello_ctor_specs as (H1 & H2 & H3).
  assert (D1 : Defines hge "glibc_stdfiles#_IO_stdfiles_init" LibioStdfiles.glibc_stdfiles_init)
    by (vm_compute; reflexivity).
  assert (D2 : Defines hge "glibc_vtables#check_stdfiles_vtables" start_check_vtables_fn) by (vm_compute; reflexivity).
  assert (D3 : Defines hge "glibc_init_first#_init_first" start_init_first_fn) by (vm_compute; reflexivity).
  apply (ctor_mem_chain (glibc_program := P)); [exact (proj1 (hello_vtables_ok w img_globals m fr Hi)) |].
  rewrite Hp. exact hello_ctor_names.
Qed.

(** Before the first call, the chain's memory comes from four sources.
    They are the constructors' lists, stdout's life, `c: __environ` as
    the startup body leaves it, and a share of the arguments. *)
Lemma hello_ctor_start av avreg dq argc envp a s :
  0 <= argc < 2 ^ 32 -> 0 < av -> av mod 8 = 0 -> av + 8 <= r_end avreg ->
  pts hello_initial_list_ps -∗ pts hello_init_first_core_ps -∗ pts hello_vtables_ps -∗
  live (img_a "_IO_2_1_stdout_") hello_stdout_reg -∗
  live (img_a "__environ") (img_gd "__environ") -∗ pcell (img_a "__environ") 0 envp -∗
  im_args (glibc_program := P) (hello_init_misc_objs av avreg) dq a s -∗
  hello_ctor_mem av avreg dq argc envp a s [].
Proof using Hi.
  intros Hargc Hav0 Hava Have. rewrite /hello_ctor_mem ctor_mem_start.
  iIntros "Hl Hf Hv Ho Le He Ha".
  iSplitL "Hl Ho"; [iApply (hello_stdfiles_init_pre w img_globals m fr Hi with "Hl Ho")|].
  iSplitL "Hf Le He Ha"; [iApply (hello_init_first_pre w img_globals m fr Hi with "Hf Le He Ha"); assumption|].
  rewrite /hello_vtables_ps /vtables_cells !pts_app. iDestruct "Hv" as "(Ci & Co & Ce & Lv)".
  iFrame "Ci Co Ce". iExact "Lv".
Qed.

(** After the last call, the memory is the three constructors'
    results. *)
Lemma hello_ctor_end av avreg dq argc envp a s order :
  Permutation order (ctor_names hello_image_module) ->
  hello_ctor_mem av avreg dq argc envp a s order ⊣⊢
  stdfiles_done (glibc_program := P) (img_a "_IO_2_1_stderr_") (img_a "_IO_2_1_stdout_") (img_a "_IO_2_1_stdin_") ∗
  init_first_done (glibc_program := P) (hello_xf av avreg dq argc envp a s) ∗
  vtables_cells (glibc_program := P) (img_a "_IO_2_1_stderr_") (img_a "_IO_2_1_stdout_") (img_a "_IO_2_1_stdin_")
    (img_a "__io_vtables") (img_gd "__io_vtables").
Proof using Type.
  intros Hp. apply ctor_mem_end. rewrite Hp. exact hello_ctor_names.
Qed.

End ctors.

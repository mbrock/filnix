(** A passed check of [CpuSetup](CpuSetup.v) is a fact about the
    checker. This module turns it into a fact about the program. The
    theorem of [AbsSound](../../theories/exec/AbsSound.v) does the
    work, and it asks for three things about the linked hi_atexit
    image. The hook for the CPU calls must be sound, which
    [CpuHook](CpuHook.v) proves. The one function called through a
    pointer must have the signature the checker was told. Every
    specification that a caller uses must hold of its callee, so the
    functions are proved bottom up and collected in tables.

    The hook assumes that the CPUID leaf 4 list ends, so everything
    here is stated for a world with that property. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  Pieces Heap Language Logic StringLogic MemLogic ExternalCalls Dominance AbsRun AbsInfer AbsDen AbsMem AbsStep
  AbsCall AbsOwn AbsSound.
From Glibc Require Import Fix GlibcProgram OsWorld OsCpuid OsRegistry HiAtexitModule HiAtexitGe
  CpuRules CpuHook CpuSetup.
Import ListNotations.
Open Scope Z_scope.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Hypothesis Hends : ow_leaf4_ends w0 = true.

(** The proofs below show that a function of the image runs without
    a panic and returns what its specification promises. The
    predicate [holds] states that for one function and one
    specification, in the program logic of the other startup proofs. *)
Definition holds (g : name) (sp : fspec) : Prop :=
  AS.spec_holds glibc_os_registry (os_wi w0) hge (ow_osxsave w0 = true) gobjs g sp.

(** The image leaves the three CPU calls to the runtime. *)
Lemma hi_cpu_calls : cpu_calls (glibc_program := program_of w0 glibc_os_registry hge).
Proof using Type.
  split; [|split]; (split; [reflexivity|]); vm_compute; split; reflexivity.
Qed.

(** The checks were run with a hook that assumes that the leaf 4 list
    ends. That hook is sound in every world whose list ends. *)
Lemma hi_hook_holds :
  AS.builtin_holds glibc_os_registry (os_wi w0) hge (ow_osxsave w0 = true) hook gobjs.
Proof using Hends.
  pose proof (cpu_builtin_holds (glibc_program := program_of w0 glibc_os_registry hge) gobjs hi_cpu_calls) as H.
  cbn [program_world program_of] in H. rewrite Hends in H. exact H.
Qed.

(** The comparison function has the signature the checker was told. *)
Lemma hi_fnames_ok : fnames_ok hge fnames.
Proof using Type.
  intros g ks rt H. cbn [fnames lookup] in H.
  destruct (name_eqb g (TAtom "glibc_libc_start#intel_02_known_compare")) eqn:E; [|discriminate].
  apply name_eqb_true in E. subst g. injection H as <- <-. split.
  - eexists. split; vm_compute; reflexivity.
  - intros gf Hgf. vm_compute in Hgf. injection Hgf as <-. vm_compute. auto.
Qed.

(** Every specification of a table holds of the function it is filed
    under. *)
Definition table_holds (t : table) : Prop := forall g sp, In sp (specs_of t g) -> holds g sp.

Lemma table_nil : table_holds [].
Proof using Type. intros g sp []. Qed.

Lemma table_cons g sps t :
  (forall sp, In sp sps -> holds (TAtom g) sp) -> table_holds t -> table_holds ((g, sps) :: t).
Proof using Type.
  intros Hs Ht g' sp. unfold specs_of. cbn [find fst snd].
  destruct (name_eqb (TAtom g) g') eqn:E; [|apply Ht].
  apply name_eqb_true in E. subst g'. apply Hs.
Qed.

Lemma table_app t1 t2 : table_holds t1 -> table_holds t2 -> table_holds (t1 ++ t2).
Proof using Type.
  intros H1 H2 g sp.
  assert (E : specs_of (t1 ++ t2) g = specs_of t1 g \/
              (specs_of t1 g = [] /\ specs_of (t1 ++ t2) g = specs_of t2 g)).
  { clear. unfold specs_of. induction t1 as [|p t1 IH]; cbn [app find]; [by right|].
    destruct (name_eqb (TAtom (fst p)) g); [by left | exact IH]. }
  destruct E as [->|[_ ->]]; [apply H1 | apply H2].
Qed.

(** A function whose inferred specifications pass the check satisfies
    each of them, once the specifications of its callees hold. *)
Lemma verified_holds t g f nocut plans :
  find_fn hge (TAtom g) = Some (Defined f) -> table_holds t ->
  forallb (verified t f nocut) plans = true ->
  forall sp, In sp (map fst plans) -> holds (TAtom g) sp.
Proof using Hends.
  intros Hf Ht Hv sp Hin. apply in_map_iff in Hin as ([sp0 inv] & <- & Hin).
  rewrite forallb_forall in Hv. specialize (Hv _ Hin).
  exact (AS.verify_sound glibc_os_registry (os_wi w0) hge (ow_osxsave w0 = true) hook gobjs fnames (specs_of t)
           (TAtom g) f sp0 inv _ 3000%nat Hf Hv hi_fnames_ok hi_hook_holds Ht).
Qed.

End sound.

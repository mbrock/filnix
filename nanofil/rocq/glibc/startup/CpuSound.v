(** A passed check of [CpuSetup](CpuSetup.v) is a fact about the
    checker. This module turns it into a fact about a program. The
    theorem of [AbsSound](../../theories/exec/AbsSound.v) does the
    work, and it asks for three things about the linked program. The
    hook for the CPU calls must be sound, which [CpuHook](CpuHook.v)
    proves. The one function called through a pointer must have the
    signature the checker was told. Every specification that a caller
    uses must hold of its callee, so the functions are proved bottom
    up and collected in tables.

    The checker never looks at a linked program. It reads the bodies
    of the functions as data. So the proofs hold for every program
    that defines those functions with those bodies, and the class
    [CpuImage] says what such a program must satisfy. The hi_atexit
    image and the Hello image can both be instances.

    The hook assumes that the CPUID leaf 4 list ends, so everything
    here is stated for a world with that property. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  Pieces Heap Language Logic StringLogic MemLogic ExternalCalls Dominance AbsRun AbsInfer AbsDen AbsMem AbsStep
  AbsCall AbsOwn AbsSound.
From Glibc Require Import Fix GlibcProgram OsWorld OsCpuid OsRegistry CpuRules CpuHook CpuSetup.
Import ListNotations.
Open Scope Z_scope.

(** * The linked program

    The proofs of these modules are about a program that some linker
    produced. They need to know three things about it. The program
    has each function named in [cpu_fns], and the body is the one
    that the checker was run on. The program does not define
    `c: zcpuid`, `c: zcpuid_count` or `c: zxgetbv`, so that a call of
    one of them goes to the Fil-C runtime. The program has an address
    for `c: intel_02_known_compare`, because the binary search of the
    descriptor table receives that function as a pointer. *)
Class CpuImage (ge : genv) : Prop := {
  cpu_image_fns : Forall (fun n => find_fn ge (TAtom n) = Some (Defined (fn n))) cpu_fns;
  cpu_image_calls :
    Forall (fun n => find_fn ge (TAtom n) = None /\ lookup (TAtom n) (ge_globals ge) = None)
      ["zcpuid"; "zcpuid_count"; "zxgetbv"]%string;
  cpu_image_compare :
    exists p, lookup (TAtom "glibc_libc_start#intel_02_known_compare") (ge_globals ge) = Some p /\
              ptr_cap p = Fn (TAtom "glibc_libc_start#intel_02_known_compare")
}.

(** Such a program finds each function of the call tree under its
    name. *)
Lemma cpu_find ge `{!CpuImage ge} n f : cpu_fn n f -> find_fn ge (TAtom n) = Some (Defined f).
Proof.
  intros [Hin <-]. apply existsb_exists in Hin as (m & Hm & E). apply String.eqb_eq in E. subst m.
  pose proof (cpu_image_fns (ge := ge)) as H. rewrite Forall_forall in H. exact (H n Hm).
Qed.

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.
Hypothesis Hends : ow_leaf4_ends w0 = true.

(** The proofs below show that a function of the program runs without
    a panic and returns what its specification promises. The
    predicate [holds] states that for one function and one
    specification, in the program logic of the other startup proofs. *)
Definition holds (g : name) (sp : fspec) : Prop :=
  AS.spec_holds glibc_os_registry (os_wi w0) ge (ow_osxsave w0 = true) gobjs g sp.

(** The program leaves the three CPU calls to the runtime, and the
    registry of the glibc proofs gives each its contract. *)
Lemma image_cpu_calls : cpu_calls (glibc_program := program_of w0 glibc_os_registry ge).
Proof using Hge.
  pose proof (cpu_image_calls (ge := ge)) as H.
  apply Forall_cons_iff in H as [[F1 G1] H]. apply Forall_cons_iff in H as [[F2 G2] H].
  apply Forall_cons_iff in H as [[F3 G3] _].
  split; [|split]; (split; [reflexivity|]); split; assumption.
Qed.

(** The checks were run with a hook that assumes that the leaf 4 list
    ends. That hook is sound in every world whose list ends. *)
Lemma image_hook_holds :
  AS.builtin_holds glibc_os_registry (os_wi w0) ge (ow_osxsave w0 = true) hook gobjs.
Proof using Hends Hge.
  pose proof (cpu_builtin_holds (glibc_program := program_of w0 glibc_os_registry ge) gobjs image_cpu_calls) as H.
  cbn [program_world program_of] in H. rewrite Hends in H. exact H.
Qed.

(** The comparison function has the signature the checker was told. *)
Lemma image_fnames_ok : fnames_ok ge fnames.
Proof using Hge.
  intros g ks rt H. cbn [fnames lookup] in H.
  destruct (name_eqb g (TAtom "glibc_libc_start#intel_02_known_compare")) eqn:E; [|discriminate].
  apply name_eqb_true in E. subst g. injection H as <- <-. split.
  - exact cpu_image_compare.
  - intros gf Hgf.
    rewrite (cpu_find ge "glibc_libc_start#intel_02_known_compare" _ (conj eq_refl eq_refl)) in Hgf.
    injection Hgf as <-. vm_compute. auto.
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
  cpu_fn g f -> table_holds t ->
  forallb (verified t f nocut) plans = true ->
  forall sp, In sp (map fst plans) -> holds (TAtom g) sp.
Proof using Hends Hge.
  intros Hf Ht Hv sp Hin. apply (cpu_find ge) in Hf. apply in_map_iff in Hin as ([sp0 inv] & <- & Hin).
  rewrite forallb_forall in Hv. specialize (Hv _ Hin).
  exact (AS.verify_sound glibc_os_registry (os_wi w0) ge (ow_osxsave w0 = true) hook gobjs fnames (specs_of t)
           (TAtom g) f sp0 inv _ 3000%nat Hf Hv image_fnames_ok image_hook_holds Ht).
Qed.

End sound.

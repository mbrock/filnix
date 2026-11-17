(** This file states Hello's safety theorem from the point where the
    runtime calls into glibc, rather than from main. GNU Hello, linked
    with userland glibc, never panics, gets stuck or breaks a contract
    in any state that [StartState](../zsys/StartState.v) allows for its
    image. In those states the caller no longer describes main's memory,
    because the loader's image and the startup code supply it.

    The premises say what remains open. Standard output and
    standard error are open descriptors, the process environment
    selects the C locale, the allocator's cursor is ready, and the
    environment's free releases heap objects. The calls
    that print, convert or read the locale are still contracts, the
    fields of [HelloCore], and so are the two printers of getopt's
    warnings. A script in nanofil/tests lists and counts these premises,
    and CI prints the count.

    This is a draft. The proof of the startup body for Hello is being
    assembled in [HelloStartAssembly](HelloStartAssembly.v), and until it
    is done the theorem takes its conclusion as a section hypothesis.
    The older theorem that starts at main stays in
    [HelloNeverPanics](HelloNeverPanics.v) until then. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Language Logic HelloLeaf.
From Glibc Require Import LocaleEnv GlibcProgram OsWorld OsRegistry FileInv GetoptDiag GetoptLongDiag HelloGlibcDebts
  StartCode StartState StartLibcStartMain HelloImageModule HelloImageLoad HelloImageLayout.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** This is the linked Hello program, whose environment frees memory
    with frt. *)
Definition hello_start_ge (frt : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv hello_image_module img_globals frt.

(** The theorem still assumes these contracts. For each ghost state,
    the library calls of [HelloCore] keep their contracts in every world
    that startup can end in, and so do the two printers of getopt's
    warnings. *)
Definition hello_start_contracts Σ (w0 : os_world) frt (dom : ptr) : Prop :=
  forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : forall tb, HelloCore (final_world w0 tb) (hello_start_ge frt) hello_image_objs),
    forall tb, exists (G : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getopt_diag_rule (final_world w0 tb) glibc_os_registry (hello_start_ge frt) G T (ho_err hello_image_objs) dom /\
    getopt_ldiag_rule (final_world w0 tb) glibc_os_registry (hello_start_ge frt) G T (ho_err hello_image_objs) dom.

Section draft.

(** ## The assembly, for now a hypothesis

    The assembly will show that every start state gives a heap that
    agrees with its memory and its world, and from which the startup
    body runs safely. This hypothesis states exactly that. *)
Context (Hasm : forall Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ} w0 m w xs frt dom,
  start_state hello_image_module w0 m w xs -> In 1 (ow_fds w0) -> In 2 (ow_fds w0) -> start_c_locale m xs -> frees_heap frt ->
  hello_start_contracts Σ w0 frt dom ->
  exists h0, live_disjoint m /\ agrees m h0 /\ os_wi w0 m w h0 /\
  forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    ([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
      let _ : irisGS_gen HasNoLc (nanofil_lang glibc_os_registry (hello_start_ge frt)) Σ :=
        nanofil_irisGS glibc_os_registry (os_wi w0) (hello_start_ge frt) in
      WP (ERun (invocation start_libc_start_main_fn xs) :
            language.expr (nanofil_lang glibc_os_registry (hello_start_ge frt))) {{ o, ⌜True⌝ }}).

(** ## The theorem *)

(** Every run of Hello from a state in which the runtime can start it
    avoids panics, stuck steps and contract failures. *)
Theorem hello_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 m s w xs frt dom fuel :
  start_state hello_image_module w0 m w xs ->
  In 1 (ow_fds w0) -> In 2 (ow_fds w0) -> start_c_locale m xs ->
  R.ready s m ->
  frees_heap frt ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : forall tb, HelloCore (final_world w0 tb) (hello_start_ge frt) hello_image_objs),
    forall tb, exists (G : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getopt_diag_rule (final_world w0 tb) glibc_os_registry (hello_start_ge frt) G T (ho_err hello_image_objs) dom /\
    getopt_ldiag_rule (final_world w0 tb) glibc_os_registry (hello_start_ge frt) G T (ho_err hello_image_objs) dom) ->
  labelled_safe glibc_os_registry (hello_start_ge frt) (invocation start_libc_start_main_fn xs)
    m s w fuel (fun _ => True).
Proof using Hasm.
  intros Hst H1 H2 Hl Hr Hf Hc.
  destruct (Hasm Σ HinvP HheapP w0 m w xs frt dom Hst H1 H2 Hl Hf Hc) as (h0 & Hd & Ha & Hw & Hwp).
  exact (heap_labelled_safe Σ glibc_os_registry (os_wi w0) (hello_start_ge frt)
    (invocation start_libc_start_main_fn xs) m s w h0 (fun _ => True) Hr Hd Ha Hw Hwp fuel).
Qed.

End draft.

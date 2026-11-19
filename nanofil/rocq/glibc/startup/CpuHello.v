(** GNU Hello is linked against the same glibc as hi_atexit, so its
    startup code calls the same `c: init_cpu_features`. The function
    was checked once, on the code of hi_atexit, and that took long
    computations. This module does not run them again. It compares
    the Hello image with the code that was checked, and concludes
    that the function keeps its contract in Hello too.

    Three things must be true of a program for the contract to hold
    in it. The program has the sixteen functions with the checked
    code. It leaves the three CPU calls to the Fil-C runtime. It has
    an address for the comparison function that the cache code passes
    to a binary search. [CpuSound](CpuSound.v) states these three
    facts, and this module proves them for Hello. *)

From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap.
From Glibc Require Import Fix GlibcProgram GlibcSpec OsWorld OsCpuid OsRegistry HelloImageModule HelloImageLoad
  HelloImageEraseMem CpuSetup CpuSound CpuInit CpuInitSpec CpuSpec CpuPlace.
Import ListNotations.
Open Scope string_scope.

(** The Hello image has an address for the comparison function, and
    the address carries the right to call that function. The address
    itself is read from the loaded image and is not written here. *)
Lemma hello_cpu_compare g m : initial_memory hello_image_module = Some (g, m) ->
  exists p, lookup (TAtom "glibc_libc_start#intel_02_known_compare") g = Some p /\
            ptr_cap p = Fn (TAtom "glibc_libc_start#intel_02_known_compare").
Proof.
  intros Hi.
  assert (C : option_map (fun gm => option_map ptr_cap (lookup (TAtom "glibc_libc_start#intel_02_known_compare") (fst gm)))
                (initial_memory hello_image_module) =
              Some (Some (Fn (TAtom "glibc_libc_start#intel_02_known_compare"))))
    by (rewrite hello_loaded_eq; vm_compute; reflexivity).
  rewrite Hi in C. cbn [option_map fst] in C.
  destruct (lookup (TAtom "glibc_libc_start#intel_02_known_compare") g) as [p|]; [|discriminate C].
  exists p. split; [reflexivity|]. cbn [option_map] in C. injection C as C. exact C.
Qed.

(** The Hello image contains the sixteen functions that
    `c: init_cpu_features` runs, and each has the same code as in
    hi_atexit. It does not define the three CPU calls. These facts
    hold for whatever memory the loader builds for the image. *)
Lemma hello_cpu_image g m fr : initial_memory hello_image_module = Some (g, m) ->
  CpuImage (mkGenv hello_image_module g fr).
Proof.
  intros Hi. split.
  - unfold cpu_fns. repeat (constructor; [vm_compute; reflexivity|]). constructor.
  - assert (C : forallb (absent_ok hello_image_module) ["zcpuid"; "zcpuid_count"; "zxgetbv"] = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in C. apply List.Forall_forall. intros s Hs.
    exact (absent_ok_sound _ _ _ fr _ Hi (C s Hs)).
  - exact (hello_cpu_compare g m Hi).
Qed.

(** The contract asks for the global objects of the function in a
    certain state before the call. The Hello image starts them in
    that state, as the hi_atexit image does. *)
Lemma hello_icf_start : icf_start_ok hello_image_module = true.
Proof. vm_compute. reflexivity. Qed.

(** The contract names eighteen global objects, and its caller must
    say where they lie. This record gives the address and the region
    of each one in Hello. It is computed from the memory that the
    loader builds for the image. *)
Definition hello_icf_objs : icf_objs := Eval vm_compute in
  match icf_objs_in img_globals img_regions with Some o => o | None => icf_no_objs end.

(** The search succeeds on Hello, whatever memory the loader builds.
    Each of the eighteen globals therefore has the right kind of
    pointer, is aligned, and fits in its region. *)
Lemma hello_icf_found g m : initial_memory hello_image_module = Some (g, m) ->
  icf_objs_in g (m_regions m) = Some hello_icf_objs.
Proof.
  intros Hi.
  assert (C : option_map (fun gm => icf_objs_in (fst gm) (m_regions (snd gm))) (initial_memory hello_image_module) =
              Some (Some hello_icf_objs)) by (rewrite hello_loaded_eq; vm_compute; reflexivity).
  rewrite Hi in C. cbn [option_map fst snd] in C. injection C as C. exact C.
Qed.

(** The loader gives every global a region when Hello starts. The
    regions in the record are exactly those, so a proof that owns
    the globals at the start owns them in the form that the contract
    asks for. *)
Lemma hello_icf_regions g m : initial_memory hello_image_module = Some (g, m) ->
  Forall (fun q => object_region (fst q) (m_regions m) = Some (snd q)) (icf_regions hello_icf_objs).
Proof. intros Hi. exact (icf_objs_in_regions _ _ _ (hello_icf_found g m Hi)). Qed.

Section hello.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Context (g : list (name * ptr)) (m : mem) (fr : word -> mem -> option (res unit * mem)).

(** The function `c: init_cpu_features` of the Hello image satisfies
    its contract in every world whose list of caches ends. *)
Theorem hello_init_cpu_features_has_spec :
  initial_memory hello_image_module = Some (g, m) ->
  ow_leaf4_ends w0 = true ->
  HasSpec glibc_os_registry (os_wi w0) (mkGenv hello_image_module g fr) (TAtom "glibc_libc_start#init_cpu_features")
    (init_cpu_features_spec (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module g fr))).
Proof using Type.
  intros Hi. pose proof (hello_cpu_image g m fr Hi) as Himg.
  exact (init_cpu_features_has_spec w0 (mkGenv hello_image_module g fr)).
Qed.

(** The contract first asks that each global lies where the record
    says, is aligned, and fits in its region. The record of Hello
    passes all of that. A caller in Hello is left with one duty,
    which is to own the eighteen objects. *)
Lemma hello_icf_ok : initial_memory hello_image_module = Some (g, m) ->
  icf_ok (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module g fr)) hello_icf_objs.
Proof using Type.
  intros Hi.
  exact (icf_objs_in_ok (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module g fr)) _ _
           (hello_icf_found g m Hi)).
Qed.

End hello.

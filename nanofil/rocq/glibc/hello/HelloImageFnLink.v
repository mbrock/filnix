(** Hello's safety proof runs main_fn, the body of main in Hello's own
    module, and its library bridges assume the record hello_link. That
    record says which body each call finds and which names are left to
    the OS. A proof about the whole linked program needs those facts for
    the whole decoded image, because the linker could have placed a
    different main or a different malloc there.

    This file checks main and every function field of hello_link against
    the whole decoded image. Most of them hold, with the bodies that the
    record names. Four do not. The image's malloc, __new_exitfn and
    __internal_atexit bodies refer to their module's private objects
    under the names glibc_malloc#... and glibc_cxa_atexit#..., while the
    record's bodies use malloc#... and cxa_atexit#.... For the same
    reason the image has no function malloc#__libc_malloc2, so the record
    as written cannot hold for this image.

    The file checks names and bodies only. It does not say that Hello
    starts from this image, and it proves no object or layout field. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Heap HelloLeaf HelloName.
From Nanofil Require HelloClose HelloMain.
From Glibc Require Import SysWrappers StrlenLogic StrncmpCode MemrchrCode MemcmpCode MemFwdCode StrchrCode
  AllocLogic LeavesLogic AtexitLogic ExitRunCode LibioGenCode SysCode LibioFlushCode LibioCleanupCode
  HelloGlibcLibsT.
From Glibc Require Import HelloImageEraseMem HelloImageCode HelloImageGettextLink.
Import ListNotations.

(** ## Hello's entry *)

(** A safety proof of Hello is only about the linked program if the
    program's main is the body that the proof runs. In the whole image,
    the name main finds exactly the body main_fn. *)
Lemma hello_image_main g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "main") = Some (Defined HelloMain.main_fn).
Proof. vm_compute. reflexivity. Qed.

(** If the check accepted any main, it would prove nothing. So we build
    a copy of the image whose main lacks its last block, and the check
    refuses that copy. *)
Local Definition changed_main : func :=
  mkFunc (fn_name HelloMain.main_fn) (fn_linkage HelloMain.main_fn) (fn_ret HelloMain.main_fn)
    (fn_params HelloMain.main_fn) (removelast (fn_blocks HelloMain.main_fn)).

Local Definition changed_image : module :=
  map (fun it => match it with
    | IFunc f => if name_eqb (fn_name f) (TAtom "main") then IFunc changed_main else it
    | _ => it end) hello_image_module.

Example hello_image_changed_main g fr :
  find_fn (mkGenv changed_image g fr) (TAtom "main") <> Some (Defined HelloMain.main_fn).
Proof. vm_compute. discriminate. Qed.

(** ## The function fields that hold *)

(** These are the calls of hello_link whose bodies the image matches,
    paired with the bodies that the record names. *)
Definition hello_image_fns : list (string * func) :=
  [("mbszero", mbszero_fn); ("memset", glibc_memset); ("set_program_name", set_program_name_fn);
   ("strrchr", glibc_strrchr); ("__GI_strlen", glibc_strlen); ("__GI___memrchr", glibc_memrchr);
   ("memcmp", glibc_memcmp); ("memeq", memeq_fn); ("strncmp", glibc_strncmp); ("strlen", glibc_strlen);
   ("__errno_location", errno_location_fn); ("xmalloc", xmalloc_fn); ("free", free_fn);
   ("atexit", atexit_fn); ("__cxa_atexit", cxa_atexit_fn); ("exit", glibc_exit);
   ("__run_exit_handlers", glibc___run_exit_handlers); ("__GI___call_tls_dtors", glibc___call_tls_dtors);
   ("__GI___libc_cleanup_push_defer", glibc___libc_cleanup_push_defer);
   ("__GI___libc_cleanup_pop_restore", glibc___libc_cleanup_pop_restore);
   ("__GI__IO_flush_all", glibc__IO_flush_all); ("_IO_cleanup", glibc__IO_cleanup);
   ("close_stdout", HelloClose.close_stdout_fn)]%string.

(** These names must stay outside the program, so that calls to them
    reach the OS contracts or the runtime's free. *)
Definition hello_image_absent : list string := ("zmemset" :: "zgc_free" :: sys_externals)%string.

(** The list holds exactly what hello_link asks: any environment with
    the record finds these bodies and leaves these names out. *)
Lemma hello_link_fns ge o : hello_link ge o ->
  Forall (fun nf => find_fn ge (TAtom (fst nf)) = Some (Defined (snd nf))) hello_image_fns /\
  Forall (fun s => find_fn ge (TAtom s) = None /\ lookup (TAtom s) (ge_globals ge) = None) hello_image_absent.
Proof.
  intros H. destruct (hk_exit_fns _ _ H) as (_ & _ & Hc). destruct (hk_frees _ _ H) as (_ & Hz).
  split.
  - unfold hello_image_fns.
    apply Forall_cons; [exact (hk_mbszero _ _ H)|]. apply Forall_cons; [exact (hk_memset _ _ H)|].
    apply Forall_cons; [exact (hk_name _ _ H)|]. apply Forall_cons; [exact (hk_strrchr _ _ H)|].
    apply Forall_cons; [exact (hk_gi_strlen _ _ H)|]. apply Forall_cons; [exact (hk_memrchr _ _ H)|].
    apply Forall_cons; [exact (hk_memcmp _ _ H)|]. apply Forall_cons; [exact (hk_memeq _ _ H)|].
    apply Forall_cons; [exact (hk_strncmp _ _ H)|]. apply Forall_cons; [exact (hk_strlen _ _ H)|].
    apply Forall_cons; [exact (hk_errno _ _ H)|]. apply Forall_cons; [exact (hk_xmalloc _ _ H)|].
    apply Forall_cons; [exact (hk_free _ _ H)|]. apply Forall_cons; [exact (hk_atexit _ _ H)|].
    apply Forall_cons; [exact Hc|]. apply Forall_cons; [exact (hk_exit _ _ H)|].
    apply Forall_cons; [exact (hk_run_exit _ _ H)|]. apply Forall_cons; [exact (hk_dtors _ _ H)|].
    apply Forall_cons; [exact (hk_push _ _ H)|]. apply Forall_cons; [exact (hk_pop _ _ H)|].
    apply Forall_cons; [exact (hk_flush _ _ H)|]. apply Forall_cons; [exact (hk_cleanup _ _ H)|].
    apply Forall_cons; [exact (hk_close_stdout _ _ H)|]. apply Forall_nil.
  - apply Forall_cons; [exact (hk_zmemset _ _ H)|]. apply Forall_cons; [exact Hz|]. exact (hk_sys _ _ H).
Qed.

(** A name that no item of a module carries finds no function and has
    no symbol, so a check of the decoded items settles both. *)
Definition absent_ok (md : module) (s : string) : bool :=
  match find_direct (TAtom s) md, find_alias (TAtom s) md with
  | None, None => negb (existsb (name_eqb (TAtom s)) (map item_key md))
  | _, _ => false
  end.

Lemma absent_ok_sound md g m fr s : initial_memory md = Some (g, m) -> absent_ok md s = true ->
  find_fn (mkGenv md g fr) (TAtom s) = None /\ lookup (TAtom s) g = None.
Proof.
  intros Hi. unfold absent_ok. destruct (find_direct (TAtom s) md) eqn:Hd; [discriminate|].
  destruct (find_alias (TAtom s) md) eqn:Ha; [discriminate|]. intros Hk. split.
  - unfold find_fn. cbn [ge_module]. rewrite Hd, Ha. reflexivity.
  - apply (loaded_absent _ _ m _ Hi). intros Hin.
    assert (E : existsb (name_eqb (TAtom s)) (map item_key md) = true).
    { apply existsb_exists. exists (TAtom s). split; [exact Hin | apply term_eqb_refl]. }
    rewrite E in Hk. discriminate.
Qed.

(** In the whole image, main and each listed call find the expected
    body, and no item carries a name that must stay outside. *)
Theorem hello_image_fn_link g m fr : initial_memory hello_image_module = Some (g, m) ->
  find_fn (mkGenv hello_image_module g fr) (TAtom "main") = Some (Defined HelloMain.main_fn) /\
  Forall (fun nf => find_fn (mkGenv hello_image_module g fr) (TAtom (fst nf)) = Some (Defined (snd nf))) hello_image_fns /\
  Forall (fun s => find_fn (mkGenv hello_image_module g fr) (TAtom s) = None /\ lookup (TAtom s) g = None)
    hello_image_absent.
Proof.
  intros Hi. split; [apply hello_image_main|]. split.
  - unfold hello_image_fns. repeat (apply Forall_cons; [cbn [fst snd]; vm_compute; reflexivity|]). apply Forall_nil.
  - assert (C : forallb (absent_ok hello_image_module) hello_image_absent = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in C. apply List.Forall_forall. intros s Hs. exact (absent_ok_sound _ _ _ fr _ Hi (C s Hs)).
Qed.

(** ## The fields that fail

    The image compiles malloc and the atexit functions in modules named
    glibc_malloc and glibc_cxa_atexit, so their private objects carry
    those prefixes. The record's bodies were extracted from a link that
    named the modules malloc and cxa_atexit. The lemmas below record the
    exact disagreement; nothing here renames either side. *)

(** The record's helper malloc#__libc_malloc2 is not in the image. *)
Lemma hello_image_no_malloc2 g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "malloc#__libc_malloc2") = None.
Proof. vm_compute. reflexivity. Qed.

(** The record's object malloc#mp_ has no symbol in the image. *)
Lemma hello_image_no_mp g m : initial_memory hello_image_module = Some (g, m) -> lookup (TAtom "malloc#mp_") g = None.
Proof.
  intros Hi. assert (C : absent_ok hello_image_module "malloc#mp_" = true) by (vm_compute; reflexivity).
  exact (proj2 (absent_ok_sound _ _ _ (fun _ _ => None) _ Hi C)).
Qed.

(** The three bodies differ from the record's, here in the names of
    their private objects and helper. *)
Lemma hello_image_bodies_differ g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "malloc") <> Some (Defined malloc_fn) /\
  find_fn (mkGenv hello_image_module g fr) (TAtom "__new_exitfn") <> Some (Defined new_exitfn_fn) /\
  find_fn (mkGenv hello_image_module g fr) (TAtom "__internal_atexit") <> Some (Defined internal_atexit_fn).
Proof. split; [|split]; vm_compute; discriminate. Qed.

(** So no environment over the image satisfies hello_link as written,
    whatever its symbols, free function and objects. *)
Theorem hello_image_not_link g fr o : ~ hello_link (mkGenv hello_image_module g fr) o.
Proof. intros H. pose proof (hk_malloc2 _ _ H) as E. rewrite hello_image_no_malloc2 in E. discriminate E. Qed.

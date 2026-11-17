(** The startup code of glibc calls `c: init_cpu_features`, and the
    contract of that call in [CpuInitSpec](CpuInitSpec.v) asks for
    eighteen global objects. A proof of startup can make the call only
    if the program starts with those objects in a state that the
    contract accepts. This module shows that the hi_atexit program
    does.

    The memory of a program at its start is fixed when the program is
    linked. In hi_atexit the feature structure is all zeros. The
    tunable table holds the names, the type codes and the defaults of
    the tunables. The descriptor table holds its fixed rows. Some of
    the fifteen small globals hold default cache sizes, and the others
    are zero.

    The module does three things. It writes down those contents as
    one list. It checks that the memory of the loaded program holds
    what the list says. It shows that the contents are ones that the
    function accepts at its start. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list_numbers.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv HiAtexitModule HiAtexitGe HiAtexitInitial
  HelloImageErase HelloImageEraseMem HelloImagePieces CpuInitSpec CpuPlace CpuHiAtexit StartImageUnique.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv.
Open Scope Z_scope.

(** ## The contents of the eighteen objects *)

(** These are the names of the eighteen objects, in the order of the
    record [icf_objs]. *)
Definition icf_names : list string :=
  "_dl_x86_cpu_features"%string :: "glibc_dl_tunables#tunable_list"%string ::
  "glibc_libc_start#intel_02_known"%string :: map fst icf_small_globals.

(** Reading one byte of the full initial memory is slow, because that
    memory is built from every initializer of the program. The checks
    below read a smaller memory instead. It keeps the eighteen objects
    and holds zeros everywhere else. This function says which objects
    it keeps. *)
Definition icf_keep (n : name) : bool := existsb (name_eqb n) (map TAtom icf_names).

(** This function reads n bytes of a memory, starting at the address
    b. *)
Definition bytes_at (m : mem) (b n : Z) : list Z := map (fun i => m_bytes m (b + i)) (seqZ 0 n).

(** These are the 4896 bytes of the tunable table in hi_atexit. *)
Definition hi_tunable_bytes : list Z := Eval vm_compute in
  bytes_at (hi_erased icf_keep) (icf_tl hi_icf_objs) 4896.

(** These are the bytes of the fifteen small globals in hi_atexit, in
    the order of [icf_small_globals]. *)
Definition hi_small_bytes : list (list Z) := Eval vm_compute in
  zip_with (fun q g => bytes_at (hi_erased icf_keep) (fst q) (snd g)) (icf_small hi_icf_objs) icf_small_globals.

(** This list holds one whole object. The object lies at the address
    and in the region that the pair q gives. It holds the bytes xs,
    and it holds no pointer. *)
Definition obj_ps (q : Z * region) (xs : list Z) : list (piece * pval) :=
  (PLive (fst q), VLive (snd q)) :: byte_ps (fst q) 0 xs ++ aux_ps (fst q) 0 (repeat CNone (length xs)).

(** This list says what the eighteen objects hold when hi_atexit
    starts. The feature structure holds 528 zero bytes. The tunable
    table and the small globals hold the bytes that were read above.
    The descriptor table holds the rows that the function searches. *)
Definition hi_cpu_globals_ps : list (piece * pval) :=
  obj_ps (icf_cf hi_icf_objs, icf_cfreg hi_icf_objs) (repeat 0 528%nat) ++
  obj_ps (icf_tl hi_icf_objs, icf_tlreg hi_icf_objs) hi_tunable_bytes ++
  obj_ps (icf_kn hi_icf_objs, icf_knreg hi_icf_objs) icf_known_bytes ++
  concat (zip_with obj_ps (icf_small hi_icf_objs) hi_small_bytes).

(** ## The list against the loaded program *)

(** The linked program really starts with these contents. The check
    runs on the smaller memory, and the theorem [image_pieces] carries
    its result over to the full initial memory. *)
Lemma hi_cpu_globals_agree : all_agree hi_m0 hi_cpu_globals_ps.
Proof.
  destruct (image_pieces icf_keep hi_module hi_module hi_globals hi_m0 hi_cpu_globals_ps (incl_refl _)
    hi_initial hi_module_names hi_module_zeros) as (m' & E & _ & H).
  apply H. assert (Hm : m' = hi_erased icf_keep) by (unfold hi_erased; rewrite E; reflexivity).
  rewrite Hm. vm_cast_no_check (eq_refl true).
Qed.

(** No object and no byte occurs twice in the list, so a proof can
    own all of it at once. *)
Lemma hi_cpu_globals_nodup : NoDup hi_cpu_globals_ps.*1.
Proof. apply pieces_unique_sound. vm_cast_no_check (eq_refl true). Qed.

(** ## Three checks on plain lists *)

(** This function tests that a number is a byte. *)
Definition is_u8 (x : Z) : bool := (0 <=? x) && (x <? 256).

(** A list that passes the test holds only bytes. *)
Lemma bytes_ok xs : forallb is_u8 xs = true -> Forall (fun x => 0 <= x < 256) xs.
Proof.
  induction xs as [|x xs IH]; cbn [forallb]; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [Ha Hb].
  apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. constructor; [lia | exact (IH H2)].
Qed.

(** This function tests that the list xs holds each byte of l at its
    offset. *)
Definition fixed_in (xs : list Z) (l : list (Z * Z)) : bool :=
  forallb (fun ox => match nth_error xs (Z.to_nat (fst ox)) with Some y => y =? snd ox | None => false end) l.

(** A list that passes the test has the fixed bytes in place. *)
Lemma fixed_in_ok xs l : fixed_in xs l = true -> Forall (fun '(o, x) => nth_error xs (Z.to_nat o) = Some x) l.
Proof.
  unfold fixed_in. induction l as [|[o x] l IH]; cbn [forallb]; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|exact (IH H2)]. cbn [fst snd] in H1.
  destruct (nth_error xs (Z.to_nat o)) as [y|]; [|discriminate]. apply Z.eqb_eq in H1. subst y. reflexivity.
Qed.

(** This function tests the contents of the small globals. Each one
    must be as long as its global and must hold only bytes. *)
Fixpoint smalls_ok (gs : list (string * Z)) (xss : list (list Z)) : bool :=
  match gs, xss with
  | [], [] => true
  | g :: gs', xs :: xss' => (length xs =? Z.to_nat (snd g))%nat && forallb is_u8 xs && smalls_ok gs' xss'
  | _, _ => false
  end.

(** The tunable table of hi_atexit has contents that the contract
    allows. It has its full size, it holds only bytes, and the type
    codes and cleared flags are where the function reads them. *)
Lemma hi_tunable_ok : icf_tunables_ok hi_tunable_bytes.
Proof.
  split; [vm_compute; reflexivity|]. split; [apply bytes_ok; vm_compute; reflexivity|].
  apply fixed_in_ok. vm_compute. reflexivity.
Qed.

(** ## From the list to the precondition *)

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Local Notation hi_program := (program_of w0 glibc_os_registry hge).

(** Owning the list of one object is owning its lifetime, its bytes
    and its empty pointer slots. *)
Lemma obj_ps_own q xs :
  pts (obj_ps q xs) ⊣⊢ live (fst q) (snd q) ∗ bytes (fst q) 0 xs ∗ auxes (fst q) 0 (repeat CNone (length xs)).
Proof using Type.
  change (obj_ps q xs) with
    ([(PLive (fst q), VLive (snd q))] ++ (byte_ps (fst q) 0 xs ++ aux_ps (fst q) 0 (repeat CNone (length xs))))%list.
  rewrite !pts_app. done.
Qed.

(** Owning the lists of the small globals gives each one in the form
    that the contract asks for. The contract does not care what a
    small global holds, so the known bytes are given up. *)
Lemma smalls_own ge gs : forall qs xss, smalls_ok gs xss = true -> length qs = length gs ->
  pts (concat (zip_with obj_ps qs xss)) ⊢
  [∗ list] g; q ∈ gs; qs, live (fst q) (snd q) ∗
    blk_u8 (glibc_program := program_of w0 glibc_os_registry ge) (fst q) (snd g).
Proof using Type.
  induction gs as [|g gs IH]; intros [|q qs] [|xs xss] Hok Hlen; cbn in Hok, Hlen; try discriminate.
  - iIntros "_". done.
  - cbn [zip_with concat]. rewrite pts_app obj_ps_own.
    apply andb_prop in Hok as [Hok Hr]. apply andb_prop in Hok as [Hl Hb]. apply Nat.eqb_eq in Hl.
    iIntros "((L & Hx & Ha) & Hr)". rewrite big_sepL2_cons. iFrame "L". iSplitL "Hx Ha".
    + iApply (blk_u8_intro (glibc_program := program_of w0 glibc_os_registry ge) (fst q) (snd g) xs
                (repeat CNone (length xs)) with "Hx Ha");
        [exact Hl | rewrite repeat_length; exact Hl | exact (bytes_ok _ Hb)].
    + iApply (IH with "Hr"); [exact Hr | lia].
Qed.

(** The function `c: init_cpu_features` reads the saved XSAVE bit of
    the feature structure and the type codes of the tunable table, and
    it searches the rows of the descriptor table. In hi_atexit the bit
    starts clear, the codes start in place and the rows are there. So
    the function may be called on the eighteen objects as the program
    starts with them. *)
Lemma hi_cpu_globals_own :
  pts hi_cpu_globals_ps ⊢ icf_owns (glibc_program := hi_program) hi_icf_objs.
Proof using Type.
  assert (Hk : length icf_known_bytes = 544%nat) by (vm_compute; reflexivity).
  pose proof (smalls_own hge icf_small_globals (icf_small hi_icf_objs) hi_small_bytes
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hsm.
  rewrite /hi_cpu_globals_ps. revert Hsm.
  generalize (concat (zip_with obj_ps (icf_small hi_icf_objs) hi_small_bytes)). intros sm Hsm.
  rewrite !pts_app !obj_ps_own (repeat_length 0 528) Hk. cbn [fst snd].
  iIntros "((Lcf & Hcf & Acf) & (Ltl & Htl & Atl) & (Lkn & Hkn & Akn) & Hs)".
  rewrite /icf_owns. iFrame "Lcf Ltl Lkn". iSplitL "Hcf Acf".
  { iExists (repeat 0 528%nat), (repeat CNone 528%nat). rewrite pts_app. iFrame "Hcf Acf". iPureIntro.
    split; [apply repeat_length|]. split; [apply repeat_length|].
    split; [apply bytes_ok; vm_compute; reflexivity|]. vm_compute. discriminate. }
  iSplitL "Htl Atl".
  { iExists hi_tunable_bytes, (repeat CNone (length hi_tunable_bytes)). rewrite pts_app. iFrame "Htl Atl".
    iPureIntro. split; [exact hi_tunable_ok|]. rewrite repeat_length. vm_compute. reflexivity. }
  iSplitL "Hkn Akn"; [rewrite /icf_known; iFrame "Hkn Akn"|].
  iApply (Hsm with "Hs").
Qed.

End image.

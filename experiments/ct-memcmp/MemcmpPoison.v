(** The two kernels of memcmp.ir under the poison spike
    (nanofil/rocq/spikes/Poison.v): the checked module nanofil -O makes
    of them, run by [prun] on two buffers whose every byte is secret, as
    run.sh runs the native builds under zegarmistrz. poison.sh writes
    MemcmpCode.v and compiles this file. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics Run Transport Machine.
From Spike Require Import Poison.
From CtMemcmp Require Import MemcmpCode.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** The checked module, decoded from [memcmp_term]. *)
Definition mc_module : module :=
  match decode_module memcmp_term with Some md => md | None => [] end.

(** The fixture decodes to [mc_module]. *)
Lemma mc_decodes : decode_module memcmp_term = Some mc_module.
Proof. vm_compute. reflexivity. Qed.

(** The module's globals, its two functions. *)
Definition mc_globals : list (name * ptr) :=
  match initial_memory mc_module with Some (g, _) => g | None => [] end.

(** The genv of the module, with the model's free. *)
Definition mc_ge : genv := mkGenv mc_module mc_globals free_res.

(** The function named n in the module. *)
Definition mc_fn (n : string) : func :=
  match find_fn mc_ge (TAtom n) with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** Both kernels are functions of the core subset in the module. *)
Lemma mc_finds :
  find_fn mc_ge (TAtom "ct_memcmp") = Some (Defined (mc_fn "ct_memcmp")) /\
  find_fn mc_ge (TAtom "leaky_memcmp") = Some (Defined (mc_fn "leaky_memcmp")).
Proof. split; vm_compute; reflexivity. Qed.

(** ## The call *)

(** Where the two buffers are. *)
Definition buf_a : Z := 4096.
Definition buf_b : Z := 8192.

(** A memory of two live heap objects of size bytes, with the contents
    bytes and no stored capability. *)
Definition two_buffers (size : Z) (bytes : Z -> Z) : mem :=
  mkMem bytes
    [mkRegion buf_a (buf_a + size) Heap Live; mkRegion buf_b (buf_b + size) Heap Live]
    (fun _ => CNone).

(** The frame of the kernel k called with the two buffers and the
    length len. *)
Definition call_fr (k : string) (len : Z) : frame :=
  let f := mc_fn k in
  match call_frame f [WPtr (mkPtr buf_a (Obj buf_a)); WPtr (mkPtr buf_b (Obj buf_b)); WInt len] with
  | Some fr => fr
  | None => mkFrame f [] [] None (Enter (TAtom "start") None)
  end.

(** That call in a memory of two size-byte buffers with the contents
    bytes. *)
Definition call (k : string) (size len : Z) (bytes : Z -> Z) : config :=
  mkConfig (call_fr k len) [] (two_buffers size bytes) 100000.

(** The poison state of that call: the pointers and the length are
    public, and every byte of both buffers carries all three taints, as
    harness.c poisons them with cannot-branch, cannot-index and
    cannot-var-time-op. *)
Definition secret_buffers (k : string) (size : Z) : pstate :=
  mkPState
    match call_tenv (mc_fn k) [WTPtr taint_bot taint_bot; WTPtr taint_bot taint_bot; WTInt taint_bot] with
    | Some te => te
    | None => []
    end
    []
    (poison_range (poison_range (fun _ => pb_clean) buf_a size (pb_secret taint_all))
       buf_b size (pb_secret taint_all))
    (fun _ => taint_bot).

(** harness.c's buffers: byte i of each is 37 i + 11, and byte differ of
    the second has its top bit changed. *)
Definition pattern (differ : Z) (a : Z) : Z :=
  let i := if a <? buf_b then a - buf_a else a - buf_b in
  let x := (i * 37 + 11) mod 256 in
  if a =? buf_b + differ then Z.lxor x 128 else x.

(** The run of the kernel k under the strictest policy, which has the
    bounds checks branch as the native code does. *)
Definition poisoned_run (k : string) (size len : Z) (bytes : Z -> Z) : pstep_result :=
  prun pol_strict mc_ge 2000 (call k size len bytes) (secret_buffers k size).

(** The leak trace of that run: its branches, the addresses and widths
    of its accesses and the pointers its checks read. *)
Definition poisoned_trace (k : string) (size len : Z) (bytes : Z -> Z)
  : option (list leak_event) :=
  prun_trace pol_strict mc_ge 2000 (call k size len bytes) (secret_buffers k size).

(** ## ct_memcmp is clean *)

(** The 16-byte path: the result is 1, and it is as secret as the
    buffers. *)
Example ct_16_differ :
  poisoned_run "ct_memcmp" 16 16 (pattern 9) = PDone (Ret (WInt 1)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** The byte loop on buffers that differ. *)
Example ct_32_differ :
  poisoned_run "ct_memcmp" 32 32 (pattern 20) = PDone (Ret (WInt 1)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** The byte loop on equal buffers. *)
Example ct_32_equal :
  poisoned_run "ct_memcmp" 32 32 (pattern (-1)) = PDone (Ret (WInt 0)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** ## leaky_memcmp is caught *)

(** The early exit branches on a comparison of secret bytes, whether or
    not the buffers differ. *)
Example leaky_32_differ :
  poisoned_run "leaky_memcmp" 32 32 (pattern 20) = PTrap CannotBranch.
Proof. vm_compute. reflexivity. Qed.

Example leaky_32_equal :
  poisoned_run "leaky_memcmp" 32 32 (pattern (-1)) = PTrap CannotBranch.
Proof. vm_compute. reflexivity. Qed.

(** ## One clean run of ct_memcmp speaks for every secret *)

(** A run that stops has a leak trace. *)
Lemma prun_done_trace : forall pol ge steps c ps o ots,
  prun pol ge steps c ps = PDone o ots ->
  exists tr, prun_trace pol ge steps c ps = Some tr.
Proof.
  intros pol ge steps. induction steps as [|n IH]; intros c ps o ots H; cbn in *; [discriminate H|].
  destruct (pstep pol ge c ps) as [c' ps' | | | | ]; try discriminate H.
  - destruct (IH _ _ _ _ H) as [tr Htr]. rewrite Htr. eexists. reflexivity.
  - eexists. reflexivity.
Qed.

(** A binding of an environment is one of its pairs. *)
Lemma lookup_in : forall (A : Type) x (e : list (name * A)) v,
  lookup x e = Some v -> In (x, v) e.
Proof.
  intros A x e v. induction e as [|[k w] e IH]; cbn; [discriminate|].
  destruct (name_eqb x k) eqn:E.
  - intros H. injection H as <-. apply term_eqb_eq in E. subst k. left. reflexivity.
  - intros H. right. exact (IH H).
Qed.

(** Whether the taint environment te has a taint of the right form for
    the pair xw of an environment. *)
Definition shaped (te : tenv) (xw : name * word) : bool :=
  match lookup (fst xw) te, snd xw with
  | Some (WTInt _), WInt _ | Some (WTPtr _ _), WPtr _ | Some (WTLimit _ _), WLimit _ _ => true
  | _, _ => false
  end.

(** An environment is related to itself under any taint environment
    that has a taint of the right form for each of its temporaries. *)
Lemma env_rel_same : forall te e, forallb (shaped te) e = true -> env_rel te e e.
Proof.
  intros te e H x. destruct (lookup x e) as [w|] eqn:E; [right | left; split; reflexivity].
  apply lookup_in in E. rewrite forallb_forall in H. specialize (H _ E).
  unfold shaped in H. cbn [fst snd] in H.
  destruct (lookup x te) as [wt|]; [|discriminate H].
  exists w, w, wt. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  destruct wt, w; try discriminate H; cbn; try split; intros Hne; exfalso; apply Hne; reflexivity.
Qed.

(** The contents b differ from b0 only inside the two buffers. *)
Definition buffers_only (size : Z) (b0 b : Z -> Z) : Prop :=
  forall a, b0 a <> b a -> buf_a <= a < buf_a + size \/ buf_b <= a < buf_b + size.

(** If ct_memcmp returns on the contents b0 without a poison fault,
    then on any other contents of the two buffers its leak trace is the
    same one. This is the spike's [prun_ct_sound] at this call: the two
    runs are related at the start because they differ only in bytes that
    carry every taint. *)
Theorem ct_memcmp_trace_is_public : forall size len b0 b w ots,
  buffers_only size b0 b ->
  poisoned_run "ct_memcmp" size len b0 = PDone (Ret w) ots ->
  poisoned_trace "ct_memcmp" size len b = poisoned_trace "ct_memcmp" size len b0.
Proof.
  intros size len b0 b w ots Hb Hrun. unfold poisoned_run in Hrun. unfold poisoned_trace.
  destruct (prun_done_trace _ _ _ _ _ _ _ Hrun) as [tr Htr]. rewrite Htr.
  apply (prun_ct_sound pol_strict mc_ge 2000 (call "ct_memcmp" size len b0) _ _ (Ret w) ots tr);
    [reflexivity | reflexivity | | right; right; exists w; reflexivity | exact Hrun | exact Htr].
  unfold ct_rel, call. cbn [c_frame c_mem c_fuel c_callers two_buffers m_regions m_bytes m_aux].
  repeat split.
  - apply env_rel_same. vm_compute. reflexivity.
  - intros a Hne. destruct (Hb a Hne) as [Ha | Ha]; unfold buf_a, buf_b in Ha;
      unfold secret_buffers, poison_range, buf_a, buf_b; cbn [ps_mem].
    + destruct ((8192 <=? a) && (a <? 8192 + size)) eqn:E.
      * cbn [pb_taint]. apply taint_join_all_r.
      * replace ((4096 <=? a) && (a <? 4096 + size)) with true
          by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        cbn [pb_taint]. apply taint_join_all_r.
    + replace ((8192 <=? a) && (a <? 8192 + size)) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [pb_taint]. apply taint_join_all_r.
  - intros a Hne. exfalso. apply Hne. reflexivity.
Qed.

(** So for a length of 16, and for the byte loop at a length of 32,
    ct_memcmp's leak trace does not depend on what the buffers hold. *)
Corollary ct_16_any_secret : forall b,
  buffers_only 16 (pattern 9) b ->
  poisoned_trace "ct_memcmp" 16 16 b = poisoned_trace "ct_memcmp" 16 16 (pattern 9).
Proof. intros b Hb. exact (ct_memcmp_trace_is_public _ _ _ _ _ _ Hb ct_16_differ). Qed.

Corollary ct_32_any_secret : forall b,
  buffers_only 32 (pattern 20) b ->
  poisoned_trace "ct_memcmp" 32 32 b = poisoned_trace "ct_memcmp" 32 32 (pattern 20).
Proof. intros b Hb. exact (ct_memcmp_trace_is_public _ _ _ _ _ _ Hb ct_32_differ). Qed.

(** The theorems rest on no axiom. *)
Print Assumptions ct_32_any_secret.
Print Assumptions leaky_32_equal.

(** The three kernels lifted from bn_add.s under the poison spike
    (nanofil/rocq/spikes/Poison.v): the checked module nanofil -O makes
    of them, run by [prun] on operands whose every byte is secret, as
    run.sh runs the native builds under zegarmistrz. poison.sh writes
    BnAddCode.v and compiles this file. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics Run Transport Machine.
From Spike Require Import Poison.
From CtBnAdd Require Import BnAddCode.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** The checked module, decoded from [bn_add_term]. *)
Definition bn_module : module :=
  match decode_module bn_add_term with Some md => md | None => [] end.

(** The fixture decodes to [bn_module]. *)
Lemma bn_decodes : decode_module bn_add_term = Some bn_module.
Proof. vm_compute. reflexivity. Qed.

(** The module's globals, its three functions. *)
Definition bn_globals : list (name * ptr) :=
  match initial_memory bn_module with Some (g, _) => g | None => [] end.

(** The genv of the module, with the model's free. *)
Definition bn_ge : genv := mkGenv bn_module bn_globals free_res.

(** The function named n in the module. *)
Definition bn_fn (n : string) : func :=
  match find_fn bn_ge (TAtom n) with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass L) [] []
  end.

(** The three kernels are functions of the core subset in the module. *)
Lemma bn_finds :
  find_fn bn_ge (TAtom "bn_add_words") = Some (Defined (bn_fn "bn_add_words")) /\
  find_fn bn_ge (TAtom "bn_sub_words") = Some (Defined (bn_fn "bn_sub_words")) /\
  find_fn bn_ge (TAtom "leaky_add_words") = Some (Defined (bn_fn "leaky_add_words")).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ## The call *)

(** Where the result and the two operands are. *)
Definition buf_r : Z := 4096.
Definition buf_a : Z := 8192.
Definition buf_b : Z := 12288.

(** A memory of three live heap objects of size bytes, with the contents
    bytes and no stored capability. *)
Definition three_buffers (size : Z) (bytes : Z -> Z) : mem :=
  mkMem bytes
    [mkRegion buf_r (buf_r + size) Heap Live; mkRegion buf_a (buf_a + size) Heap Live;
     mkRegion buf_b (buf_b + size) Heap Live]
    (fun _ => CNone).

(** The frame of the kernel k called with the three buffers and the
    count n. *)
Definition call_fr (k : string) (n : Z) : frame :=
  let f := bn_fn k in
  match call_frame f [WPtr (mkPtr buf_r (Obj buf_r)); WPtr (mkPtr buf_a (Obj buf_a));
                      WPtr (mkPtr buf_b (Obj buf_b)); WInt n] with
  | Some fr => fr
  | None => mkFrame f [] [] None (Enter (TAtom "start") None)
  end.

(** That call in a memory of three size-byte buffers with the contents
    bytes. *)
Definition call (k : string) (size n : Z) (bytes : Z -> Z) : config :=
  mkConfig (call_fr k n) [] (three_buffers size bytes) 100000.

(** The poison state of that call: the pointers, the count and the
    result buffer are public, and every byte of both operands carries
    all three taints, as harness.c poisons them with cannot-branch,
    cannot-index and cannot-var-time-op. *)
Definition secret_operands (k : string) (size : Z) : pstate :=
  mkPState
    match call_tenv (bn_fn k) [WTPtr taint_bot taint_bot; WTPtr taint_bot taint_bot;
                               WTPtr taint_bot taint_bot; WTInt taint_bot] with
    | Some te => te
    | None => []
    end
    []
    (poison_range (poison_range (fun _ => pb_clean) buf_a size (pb_secret taint_all))
       buf_b size (pb_secret taint_all))
    (fun _ => taint_bot).

(** harness.c's operands: word i of a is a0 + i astep and word i of b is
    b0 + i bstep, little-endian, and r is zero. *)
Definition operands (a0 astep b0 bstep : Z) (x : Z) : Z :=
  let byte base first step :=
    (((first + ((x - base) / 8) * step) mod 2 ^ 64) / 2 ^ (8 * ((x - base) mod 8))) mod 256 in
  if x <? buf_a then 0 else if x <? buf_b then byte buf_a a0 astep else byte buf_b b0 bstep.

(** The run of the kernel k under the strictest policy, which has the
    bounds checks branch as the native code does. *)
Definition poisoned_run (k : string) (size n : Z) (bytes : Z -> Z) : pstep_result :=
  prun pol_strict bn_ge 2000 (call k size n bytes) (secret_operands k size).

(** The leak trace of that run: its branches, the addresses and widths
    of its accesses and the pointers its checks read. *)
Definition poisoned_trace (k : string) (size n : Z) (bytes : Z -> Z)
  : option (list leak_event) :=
  prun_trace pol_strict bn_ge 2000 (call k size n bytes) (secret_operands k size).

(** ## bn_add_words and bn_sub_words are clean *)

(** Four words with no carry: the result is 0, and it is as secret as
    the operands. *)
Example add_no_carry :
  poisoned_run "bn_add_words" 32 4 (operands 3 5 7 11) = PDone (Ret (WInt 0)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** A carry out of the first word that ripples through the other
    three. *)
Example add_ripple :
  poisoned_run "bn_add_words" 32 4 (operands (-1) 0 1 0) = PDone (Ret (WInt 1)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** Eight words, of which the first three carry. *)
Example add_mixed :
  poisoned_run "bn_add_words" 64 8 (operands (-3) 1 1 1) = PDone (Ret (WInt 0)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** A borrow out of every word. *)
Example sub_ripple :
  poisoned_run "bn_sub_words" 32 4 (operands 0 0 1 0) = PDone (Ret (WInt 1)) [WTInt taint_all].
Proof. vm_compute. reflexivity. Qed.

(** ## leaky_add_words is caught *)

(** The control branches on the carry of a sum of secret words, whether
    or not there is one. *)
Example leaky_no_carry :
  poisoned_run "leaky_add_words" 32 4 (operands 3 5 7 11) = PTrap CannotBranch.
Proof. vm_compute. reflexivity. Qed.

Example leaky_ripple :
  poisoned_run "leaky_add_words" 32 4 (operands (-1) 0 1 0) = PTrap CannotBranch.
Proof. vm_compute. reflexivity. Qed.

(** ## One clean run speaks for every operand *)

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

(** The contents b differ from b0 only inside the two operands. *)
Definition operands_only (size : Z) (b0 b : Z -> Z) : Prop :=
  forall a, b0 a <> b a -> buf_a <= a < buf_a + size \/ buf_b <= a < buf_b + size.

(** The proof that a kernel's leak trace is the one of its run Hrun on
    any other contents of the two operands (Hb). This is the spike's
    [prun_ct_sound] at the call: the two runs are related at the start
    because they differ only in bytes that carry every taint. *)
Ltac public_trace Hb Hrun :=
  unfold poisoned_run in Hrun; unfold poisoned_trace;
  let tr := fresh "tr" in
  let Htr := fresh "Htr" in
  destruct (prun_done_trace _ _ _ _ _ _ _ Hrun) as [tr Htr]; rewrite Htr;
  match type of Hrun with
  | prun _ _ _ ?c _ = PDone ?o ?ots =>
    apply (prun_ct_sound pol_strict bn_ge 2000 c _ _ o ots tr);
      [reflexivity | reflexivity | | right; right; eexists; reflexivity | exact Hrun | exact Htr]
  end;
  unfold ct_rel, call; cbn [c_frame c_mem c_fuel c_callers three_buffers m_regions m_bytes m_aux];
  repeat split;
  [ apply env_rel_same; vm_compute; reflexivity
  | let a := fresh "a" in
    let Hne := fresh "Hne" in
    let Ha := fresh "Ha" in
    let E := fresh "E" in
    intros a Hne; destruct (Hb a Hne) as [Ha | Ha]; unfold buf_a, buf_b in Ha;
    unfold secret_operands, poison_range, buf_a, buf_b; cbn [ps_mem];
    [ destruct ((12288 <=? a) && (a <? 12288 + _)) eqn:E;
      [ cbn [pb_taint]; apply taint_join_all_r
      | match goal with
        | |- context [(8192 <=? a) && (a <? 8192 + ?size)] =>
          replace ((8192 <=? a) && (a <? 8192 + size)) with true
            by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia)
        end;
        cbn [pb_taint]; apply taint_join_all_r ]
    | match goal with
      | |- context [(12288 <=? a) && (a <? 12288 + ?size)] =>
        replace ((12288 <=? a) && (a <? 12288 + size)) with true
          by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia)
      end;
      cbn [pb_taint]; apply taint_join_all_r ]
  | let a := fresh "a" in
    let Hne := fresh "Hne" in
    intros a Hne; exfalso; apply Hne; reflexivity ].

(** If bn_add_words returns on the contents b0 without a poison fault,
    then on any other contents of the two operands its leak trace is the
    same one. *)
Theorem bn_add_words_trace_is_public : forall size n b0 b w ots,
  operands_only size b0 b ->
  poisoned_run "bn_add_words" size n b0 = PDone (Ret w) ots ->
  poisoned_trace "bn_add_words" size n b = poisoned_trace "bn_add_words" size n b0.
Proof. intros size n b0 b w ots Hb Hrun. public_trace Hb Hrun. Qed.

(** The same of bn_sub_words. *)
Theorem bn_sub_words_trace_is_public : forall size n b0 b w ots,
  operands_only size b0 b ->
  poisoned_run "bn_sub_words" size n b0 = PDone (Ret w) ots ->
  poisoned_trace "bn_sub_words" size n b = poisoned_trace "bn_sub_words" size n b0.
Proof. intros size n b0 b w ots Hb Hrun. public_trace Hb Hrun. Qed.

(** So for four words whose carry ripples, bn_add_words's leak trace
    does not depend on what the operands hold, and neither does
    bn_sub_words's for four words that all borrow. *)
Corollary add_any_operands : forall b,
  operands_only 32 (operands (-1) 0 1 0) b ->
  poisoned_trace "bn_add_words" 32 4 b = poisoned_trace "bn_add_words" 32 4 (operands (-1) 0 1 0).
Proof. intros b Hb. exact (bn_add_words_trace_is_public _ _ _ _ _ _ Hb add_ripple). Qed.

Corollary sub_any_operands : forall b,
  operands_only 32 (operands 0 0 1 0) b ->
  poisoned_trace "bn_sub_words" 32 4 b = poisoned_trace "bn_sub_words" 32 4 (operands 0 0 1 0).
Proof. intros b Hb. exact (bn_sub_words_trace_is_public _ _ _ _ _ _ Hb sub_ripple). Qed.

(** The theorems rest on no axiom. *)
Print Assumptions add_any_operands.
Print Assumptions sub_any_operands.
Print Assumptions leaky_ripple.

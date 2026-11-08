(** The first program with an input proved never to panic:
    rocq/programs/prefix.c, the sum of the first n longs of a read-only
    global array, for every integer n (PrefixCode.v, checked current by
    rocq/programs.sh). The loop's index is compared with both n and the
    array's length, and only the second guards the access.

    The statement is Panics.v's [never_panics] over every [[runtime]],
    every input word and every [[fuel]]. As in Sum.v the proof checks a
    computed run step by step against abstract memory, but here the
    input changes the path: each iteration compares the index with n.
    The proof does not ask which way that comparison goes. It allows
    both answers at every iteration, so the states it covers are the
    six runs of [prefix_runs] (n from 0 to 5), with n itself left
    abstract in the environment ([with_input]). Run 5 takes the true
    answer every time; run k leaves it at the k-th comparison
    ([exit_at]), and its states before that are run 5's. Since the
    access is guarded by the comparison with 4 alone, every one of
    those states steps safely, whatever n is.

    ## Decisions

    | Decision | Why |
    |---|---|
    | the comparison with n is over-approximated, both answers allowed | then nothing about n's value is needed: no reasoning about signed 32-bit comparison, and n stays a variable throughout |
    | a state is a run k and an index, with run 5 standing for every run before it leaves ([canonical]) | the six runs share their beginnings; listing each shared state once keeps the proof to 109 cases |
    | the input is any list whose first word is a 32-bit integer word, 0 to 2^32 - 1 | the ABI passes an `int` as such a word; a pointer there is outside the C type, and extra words are ignored by [call_frame]. It also keeps the input's remainder modulo 2^32 from unfolding, which no reduction finishes on a variable | *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics PrefixCode Sum.
Import ListNotations.
Open Scope Z_scope.

(** ## The program *)

(** The checked module, decoded from the fixture [prefix_term]
    ([prefix_decodes]). *)
Definition prefix_module : module :=
  match decode_module prefix_term with Some md => md | None => [] end.

(** The fixture decodes to [prefix_module]. *)
Lemma prefix_decodes : decode_module prefix_term = Some prefix_module.
Proof. vm_compute. reflexivity. Qed.

(** The function `prefix`, the module's first item. *)
Definition prefix_fn : func :=
  match prefix_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "prefix") (TAtom "export") (RClass L) [] []
  end.

(** The module's globals: the array `xs`, laid out as in Sum.v, and the
    function `prefix`. *)
Definition prefix_globals : list (name * ptr) :=
  [(TAtom "xs", mkPtr 65552 (Ro 65552)); (TAtom "prefix", mkPtr 65536 (Fn (TAtom "prefix")))].

(** The module's initial memory. *)
Definition prefix_mem : mem :=
  match initial_memory prefix_module with Some (_, m) => m | None => empty_mem end.

(** Laying out the module succeeds, with [prefix_globals] and
    [prefix_mem]. *)
Lemma prefix_initial : initial_memory prefix_module = Some (prefix_globals, prefix_mem).
Proof.
  assert (H : option_map fst (initial_memory prefix_module) = Some prefix_globals)
    by (vm_compute; reflexivity).
  unfold prefix_mem. destruct (initial_memory prefix_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The genv of the module with any free; the program calls none. *)
Definition prefix_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv prefix_module prefix_globals free.

(** `prefix` is a function of the [[core subset]] in the module. *)
Lemma prefix_find : forall free,
  find_fn (prefix_ge free) (TAtom "prefix") = Some (Defined prefix_fn).
Proof. intros free. vm_compute. reflexivity. Qed.

(** The name of `prefix`'s parameter. *)
Definition input_name : name := TAtom "v0".

(** Any arguments whose first word is the integer n start `prefix` at
    its entry block with n as its parameter. *)
Lemma prefix_call_frame : forall n rest,
  call_frame prefix_fn (WInt n :: rest) =
  Some (mkFrame prefix_fn [(input_name, WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** ## The runs *)

(** The environment e with the parameter's word replaced by the integer
    n: a state of a computed run, for the input n. *)
Definition with_input (n : Z) (e : env) : env :=
  map (fun p => if name_eqb (fst p) input_name then (fst p, WInt n) else p) e.

(** The run of `prefix` on the input k, computed by the model on the
    initial memory. *)
Definition prefix_run (k : Z) : list (point * env) :=
  trace (prefix_ge (fun _ _ => None)) 300
    (mkConfig (mkFrame prefix_fn [(input_name, WInt k)] [] None (Enter (TAtom "start") None))
              [] prefix_mem 1000).

(** The runs on the inputs 0 to 5: every way the comparisons with n can
    go, since the loop stops at the first false one or after four. *)
Definition prefix_runs : list (list (point * env)) := map prefix_run [0; 1; 2; 3; 4; 5].

(** Where the run r leaves the loop because the index is not below the
    input: the first point at the loop's branch with the comparison
    false; the run's length if there is none. *)
Fixpoint exit_at (r : list (point * env)) : nat :=
  match r with
  | [] => O
  | (Exec l [] _, e) :: r' =>
      if name_eqb l (TAtom "L4") && match lookup (TAtom "v10") e with
                                    | Some (WInt 0) => true | _ => false end
      then O else S (exit_at r')
  | _ :: r' => S (exit_at r')
  end.

(** Index i of run k stands for a state: run 5 stands for every run up
    to where it leaves, so a run k below 5 is used only from there. *)
Definition canonical (k i : nat) : Prop :=
  k = 5%nat \/ (exit_at (nth k prefix_runs []) <= i)%nat.

(** ## Each step *)

(** The four longs of the array in the initial memory, 1 to 4. *)
Lemma pxs0 : load_bytes prefix_mem 65552 8 = 1. Proof. vm_compute. reflexivity. Qed.
Lemma pxs1 : load_bytes prefix_mem 65560 8 = 2. Proof. vm_compute. reflexivity. Qed.
Lemma pxs2 : load_bytes prefix_mem 65568 8 = 3. Proof. vm_compute. reflexivity. Qed.
Lemma pxs3 : load_bytes prefix_mem 65576 8 = 4. Proof. vm_compute. reflexivity. Qed.

(** A signed comparison of two 32-bit words is 0 or 1. *)
Lemma slt_bit : forall x y, cond_bit Slt W x y = Some 0 \/ cond_bit Slt W x y = Some 1.
Proof.
  intros x y. unfold cond_bit. simpl.
  match goal with |- context[if ?b then _ else _] => destruct b end; auto.
Qed.

(** The comparison with the input in the step computed in E: reduced
    with remainders and comparisons folded, since [cbv] does not finish
    on the remainder of a variable, it stops at the comparison; the
    input's remainder is rewritten (Hmod), and the comparison is split
    into its two answers ([slt_bit]). *)
Ltac input_compare E Hmod :=
  cbv beta iota zeta delta -[object_region m_regions load_bytes prefix_mem prefix_module
                             cond_bit Z.modulo Z.eqb] in E;
  rewrite ?Hmod in E;
  match type of E with context[cond_bit Slt W ?x ?y] =>
    destruct (slt_bit x y) as [Ecb|Ecb]; rewrite Ecb in E; clear Ecb
  end.

(** Compute the [step] in the goal for a memory known only by Hb and Hr,
    an input known only by Hmod and the fuel, as Sum.v's [step_eq]; the
    one instruction that reads the input, its comparison at the loop's
    head, goes through [input_compare] first. *)
Ltac input_step_eq Hb Hr Hmod fuel :=
  match goal with |- context[step ?g ?c] =>
    remember (step g c) as r eqn:Estep;
    try (match type of Estep with context[Enter _ _] => case_eq (fuel =? 0); intro end);
    try (match type of Estep with
         | context[Exec _ (Let _ W (Cmp Slt W) [_; Tmp (TAtom "v0")] :: _) _] => input_compare Estep Hmod
         end);
    cbv beta iota zeta delta -[object_region m_regions load_bytes prefix_mem prefix_module Z.eqb] in Estep;
    try (match goal with Hf : (fuel =? 0) = _ |- _ => rewrite Hf in Estep end);
    repeat progress (cbv beta iota zeta delta -[object_region m_regions load_bytes prefix_mem prefix_module] in Estep;
                     rewrite ?Hr, ?(load_bytes_same _ _ Hb), ?pxs0, ?pxs1, ?pxs2, ?pxs3 in Estep);
    subst r
  end.

(** The next state is index S i of run k. *)
Ltac next_in k :=
  exists k; do 3 eexists; split; [lia|]; split;
  [first [left; reflexivity | right; cbv; lia] |];
  split; reflexivity.

(** One state of run k: take its point and environment from Hn,
    compute its step, and find it among the outcomes [prefix_progress]
    allows, trying run k first for the next state, then each run. *)
Ltac run_step k Hn Hb Hr Hmod fuel :=
  cbv in Hn; injection Hn as <- <-;
  input_step_eq Hb Hr Hmod fuel;
  first [ right; left; reflexivity
        | right; right; eexists; reflexivity
        | left; first [next_in k | next_in 5%nat | next_in 0%nat | next_in 1%nat
                      | next_in 2%nat | next_in 3%nat | next_in 4%nat] ].

(** The states of run k below 5, which start where it leaves run 5
    ([canonical]): five of them, to its return. *)
Ltac run_tail k Hc Hn Hb Hr Hmod fuel :=
  destruct Hc as [Hc|Hc]; [discriminate Hc|];
  cbv in Hc; destruct (Nat.le_exists_sub _ _ Hc) as (j & Hj & _);
  rewrite Nat.add_comm in Hj; subst;
  do 5 (destruct j as [|j]; [run_step k Hn Hb Hr Hmod fuel|]);
  destruct j; cbv in Hn; discriminate Hn.

(** From index i of run k, for the 32-bit input n, in any memory that is
    [mem_ok] and with any fuel, `prefix` steps to index S i of some run
    with the same memory, ends for lack of fuel, or returns. *)
Lemma prefix_progress : forall free n k i pt e m fuel,
  0 <= n < 2 ^ 32 -> (k <= 5)%nat -> canonical k i ->
  nth_error (nth k prefix_runs []) i = Some (pt, e) -> mem_ok prefix_mem m ->
  (exists k' pt' e' fuel', (k' <= 5)%nat /\ canonical k' (S i) /\
     nth_error (nth k' prefix_runs []) (S i) = Some (pt', e') /\
     step (prefix_ge free) (mkConfig (mkFrame prefix_fn (with_input n e) [] None pt) [] m fuel) =
     Next (mkConfig (mkFrame prefix_fn (with_input n e') [] None pt') [] m fuel')) \/
  step (prefix_ge free) (mkConfig (mkFrame prefix_fn (with_input n e) [] None pt) [] m fuel)
    = Done OutOfFuel \/
  exists s, step (prefix_ge free) (mkConfig (mkFrame prefix_fn (with_input n e) [] None pt) [] m fuel)
    = Done (Ret (WInt s)).
Proof.
  intros free n k i pt e m fuel Hin Hk Hc Hn [Hb Hr].
  assert (Hmod : n mod 4294967296 = n) by (apply Z.mod_small; exact Hin).
  unfold canonical in *.
  set (runs := prefix_runs) in Hn, Hc |- *. vm_compute in runs.
  set (f := prefix_fn). vm_compute in f.
  destruct k as [|[|[|[|[|[|k]]]]]].
  - run_tail 0%nat Hc Hn Hb Hr Hmod fuel.
  - run_tail 1%nat Hc Hn Hb Hr Hmod fuel.
  - run_tail 2%nat Hc Hn Hb Hr Hmod fuel.
  - run_tail 3%nat Hc Hn Hb Hr Hmod fuel.
  - run_tail 4%nat Hc Hn Hb Hr Hmod fuel.
  - do 84 (destruct i as [|i]; [run_step 5%nat Hn Hb Hr Hmod fuel|]).
    destruct i; cbv in Hn; discriminate Hn.
  - lia.
Qed.

(** ## Over any runtime *)

(** `prefix` never panics under the [[runtime]] R. *)
Module PrefixSafe (R : Runtime).
Module P := Panics R.
Module S := SumSafe R.

(** A machine state that one of the runs stands for: `prefix` at a
    [canonical] index of a run, with the input n, no caller, in a
    [mem_ok] memory. *)
Definition prefix_inv (n : Z) (st : P.RM.mstate) : Prop :=
  0 <= n < 2 ^ 32 /\ exists k i pt e, (k <= 5)%nat /\ canonical k i /\
    nth_error (nth k prefix_runs []) i = Some (pt, e) /\
    fst st = mkConfig (mkFrame prefix_fn (with_input n e) [] None pt) [] (c_mem (fst st)) (c_fuel (fst st)) /\
    mem_ok prefix_mem (c_mem (fst st)).

(** Every machine step from such a state leads to one: a step is to the
    next index of some run ([prefix_progress]), never an allocation,
    and a safepoint keeps the state and [mem_ok] (Sum.v's
    [mem_ok_safepoint]). *)
Lemma prefix_mstep : forall n st st',
  P.RM.mstep (P.program_genv prefix_module prefix_globals) st st' ->
  prefix_inv n st -> prefix_inv n st'.
Proof.
  intros n st st' Hs (Hin & k & i & pt & e & Hk & Hc & Hn & Hst & Hm). split; [exact Hin|].
  destruct Hs as [c c' s E | c q k0 s base s' E _ _ | c s s' m' _ Hsp]; cbn [fst snd] in Hst, Hm |- *;
    change (P.program_genv prefix_module prefix_globals) with (prefix_ge R.free) in *.
  - rewrite Hst in E.
    destruct (prefix_progress R.free n k i pt e (c_mem c) (c_fuel c) Hin Hk Hc Hn Hm)
      as [(k' & pt' & e' & fuel' & Hk' & Hc' & Hn' & E') | [E' | (v & E')]];
      rewrite E' in E; try discriminate.
    injection E as <-. exists k', (S i), pt', e'. cbn [c_mem c_fuel]. auto.
  - rewrite Hst in E.
    destruct (prefix_progress R.free n k i pt e (c_mem c) (c_fuel c) Hin Hk Hc Hn Hm)
      as [(k' & pt' & e' & fuel' & Hk' & Hc' & Hn' & E') | [E' | (v & E')]];
      rewrite E' in E; discriminate.
  - exists k, i, pt, e. rewrite Hst. unfold P.RM.with_mem; cbn [c_mem c_fuel c_frame c_callers].
    split; [exact Hk|]. split; [exact Hc|]. split; [exact Hn|]. split; [reflexivity|].
    eapply S.mem_ok_safepoint; eauto.
Qed.

(** Every state a run reaches from such a state is one. *)
Lemma prefix_reachable : forall n st st',
  P.RM.mreachable (P.program_genv prefix_module prefix_globals) st st' ->
  prefix_inv n st -> prefix_inv n st'.
Proof.
  intros n st st' H. induction H as [st st' Hs | st | st1 st2 st3 _ IH1 _ IH2]; auto.
  apply prefix_mstep; assumption.
Qed.

(** No such state [fails]: its step is to a next state, the end of
    fuel, or a return. *)
Lemma prefix_not_fails : forall n st, prefix_inv n st ->
  ~ fails (P.program_genv prefix_module prefix_globals) (fst st).
Proof.
  intros n st (Hin & k & i & pt & e & Hk & Hc & Hn & Hst & Hm). rewrite Hst. unfold fails.
  destruct (prefix_progress R.free n k i pt e (c_mem (fst st)) (c_fuel (fst st)) Hin Hk Hc Hn Hm)
    as [(k' & pt' & e' & fuel' & _ & _ & _ & E) | [E | (v & E)]];
    change (P.program_genv prefix_module prefix_globals) with (prefix_ge R.free);
    rewrite E; simpl; tauto.
Qed.

(** `prefix` never panics: for every 32-bit input, under the runtime
    R, with any fuel, no state of its run [fails]. *)
Theorem prefix_never_panics :
  P.never_panics prefix_module (TAtom "prefix")
    (fun xs => exists n rest, xs = WInt n :: rest /\ 0 <= n < 2 ^ 32).
Proof.
  exists prefix_globals, prefix_mem, prefix_fn.
  split; [exact prefix_initial|]. split; [apply prefix_find|].
  intros xs (n & rest & -> & Hin). eexists. split; [apply prefix_call_frame|].
  intros _ fuel st Hreach. apply (prefix_not_fails n). eapply prefix_reachable; [exact Hreach|].
  split; [exact Hin|]. exists 5%nat, O, (Enter (TAtom "start") None), [(input_name, WInt 5)].
  split; [lia|]. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [reflexivity|]. split; [reflexivity | vm_compute; reflexivity].
Qed.

End PrefixSafe.

(** The theorem for the [[interpreter]]'s runtime. *)
Module InterpPrefix := PrefixSafe InterpRuntime.

(** What one [[step]] gives, rule by rule: for each instruction form of
    the [[core subset]] and each jump, the configuration [step] reaches
    from a frame at it, under premises small enough to compute on their
    own. They are the forward reading of Steps.v, whose lemmas say what
    a step that happened must have been.

    A program proof that reduces [step] itself carries the whole
    function and memory through every reduction; Cycle.v and Buffer.v
    spend most of their time there ([[proof]], docs/logic.md). With
    these rules, a proof names the instruction, checks the premises (a
    temporary's value, an operation on words, an access check against
    an object's region) and gets the next configuration as a term. They
    are the instruction rules of the program logic (docs/logic.md): its
    weakest-precondition rules are these, lifted.

    Every rule is for a frame that is not [[doomed]]. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics.
Import ListNotations.
Open Scope Z_scope.

(** ## Operations *)

(** The op o is one [inst_step] runs through [op_res]: not a check of a
    named local, a function check or a read of the argument snapshot,
    which have their own cases. *)
Definition general_op (o : op) : bool :=
  match o with CheckLocal _ _ _ _ _ | CheckFunction | VaArgs => false | _ => true end.

(** An instruction's result that continues keeps a frame that is not
    doomed undoomed. *)
Lemma doomed_result_continue : forall ge fr m i e ls m',
  fr_doomed fr = None -> doomed_result ge fr m i (IContinue e ls m') = Some (IContinue e ls m', None).
Proof.
  intros ge fr m i e ls m' Hd. unfold doomed_result. rewrite Hd.
  destruct i as [d k o args| | | | | | | |]; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|a [|a' args]]; reflexivity.
Qed.

(** An instruction's result that allocates keeps a frame that is not
    doomed undoomed. *)
Lemma doomed_result_fresh_none : forall ge fr m i q k,
  fr_doomed fr = None -> doomed_result ge fr m i (IFresh q k) = Some (IFresh q k, None).
Proof.
  intros ge fr m i q kk Hd. unfold doomed_result. rewrite Hd.
  destruct i as [d k o args| | | | | | | |]; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|a [|a' args]]; reflexivity.
Qed.

(** An instruction's result that calls keeps a frame that is not doomed
    undoomed. *)
Lemma doomed_result_call : forall ge fr m i g xs pd,
  fr_doomed fr = None -> doomed_result ge fr m i (ICall g xs pd) = Some (ICall g xs pd, None).
Proof.
  intros ge fr m i g xs pd Hd. unfold doomed_result. rewrite Hd.
  destruct i as [d k o args| | | | | | | |]; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|a [|a' args]]; reflexivity.
Qed.

(** A step at an instruction of a frame that is not doomed: what
    [inst_step] makes of it, through [inst_next]. *)
Lemma rule_inst : forall ge f e ls l i rest j cs m fuel out,
  inst_step ge (mkFrame f e ls None (Exec l (i :: rest) j)) m i = Some out ->
  doomed_result ge (mkFrame f e ls None (Exec l (i :: rest) j)) m i out = Some (out, None) ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs m fuel) =
  inst_next (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs m fuel) l rest j out None.
Proof.
  intros ge f e ls l i rest j cs m fuel out Hi Hd.
  unfold step; cbn [fr_at c_frame c_mem fr_doomed]. rewrite Hi.
  rewrite Hd. reflexivity.
Qed.

(** A let of a general op whose arguments read as the words xs and whose
    [op_res] is the word w, in the memory m': the frame binds w to d and
    goes on, in m'. *)
Lemma rule_let : forall ge f e ls l d k o args rest j cs m fuel classes xs w m',
  general_op o = true ->
  op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  op_res o k xs m = Some (OpRes (RVal w) m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d w e) ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l d k o args rest j cs m fuel classes xs w m' Hg Hc Hx Ho.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) m
                 (Let d k o args) = Some (IContinue (put d w e) ls m')).
  { transitivity (let* classes := op_arg_classes o k in
                  let* xs := map2_option (value_x ge e) classes args in
                  let* out := op_res o k xs m in
                  match out with
                  | OpRes r m' => Some (bind_res d r e ls m')
                  | OpUB why => Some (IStop (UB why))
                  | OpAlloc q kont =>
                      Some (IFresh q (fun base => let (x, m') := kont base in (put d x e, ls, m')))
                  end).
    - destruct o; try discriminate Hg; destruct k; reflexivity.
    - rewrite Hc. cbn - [op_res map2_option]. rewrite Hx. cbn - [op_res]. rewrite Ho. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** A heap allocation of size bytes, size read as the only argument and
    within Fil-C's limit: the step asks for [heap_req] of it, and for
    any base the frame binds d to the new object's own pointer, in the
    memory with the object [allocated]. *)
Lemma rule_alloc : forall ge f e ls l d k al args rest j cs m fuel size,
  map2_option (value_x ge e) [L] args = Some [WInt size] ->
  size <= max_allocation_size ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) cs m fuel) =
  Fresh (heap_req al size)
        (fun base => mkConfig (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec l rest j))
                              cs (allocated m (heap_req al size) base) fuel).
Proof.
  intros ge f e ls l d k al args rest j cs m fuel size Hx Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) m
                 (Let d k (Alloc al) args) =
               Some (IFresh (heap_req al size)
                       (fun base => (put d (WPtr (mkPtr base (Obj base))) e, ls,
                                     allocated m (heap_req al size) base)))).
  { destruct k; cbn - [map2_option heap_req allocated max_allocation_size]; rewrite Hx;
      cbn - [heap_req allocated max_allocation_size];
      replace (max_allocation_size <? size) with false by (symmetry; apply Z.ltb_ge; exact Hs);
      reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_fresh_none; reflexivity).
  reflexivity.
Qed.

(** ## Flights and stores *)

(** A [[flight]] whose arguments read as xs, whose address [alu]
    computes as n, and whose capability source gives c: the frame binds
    d to the pointer of n and c. *)
Lemma rule_flight : forall ge f e ls l d o args lw rest j cs m fuel xs n c,
  map_option (flight_arg_x ge e) args = Some xs ->
  alu o L xs = Some (WInt n) ->
  flight_cap ge e lw = Some c ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) cs m fuel).
Proof.
  intros ge f e ls l d o args lw rest j cs m fuel xs n c Hx Ha Hc.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) m
                 (Flight d o args lw) = Some (IContinue (put d (WPtr (mkPtr n c)) e) ls m)).
  { cbn - [map_option alu flight_cap]. rewrite Hx, Ha, Hc. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** A raw store of width w of the value v, which reads as x, through the
    proven pointer a, which reads as p, at offset off, where the store
    passes and leaves the memory m': the frame goes on in m'. *)
Lemma rule_raw_store : forall ge f e ls l w off v a rest j cs m fuel vk x p m',
  width_value_class w = Some vk ->
  value_x ge e vk v = Some x ->
  value_x ge e A a = Some (WPtr p) ->
  store_res w m (raw_address (ptr_addr p) off) (ptr_cap p) x = Some (ok, m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (RawStore w off v a :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l w off v a rest j cs m fuel vk x p m' Hw Hv Ha Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (RawStore w off v a :: rest) j)) m
                 (RawStore w off v a) = Some (IContinue e ls m')).
  { cbn - [width_value_class value_x store_res raw_address]. rewrite Hw, Hv, Ha, Hs. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** A raw store of the pointer v, which reads as xp, through the proven
    pointer a, which reads as p, at offset off: where the 8-byte write
    access there passes and the protocol es leaves the memory m', the
    frame goes on in m'. *)
Lemma rule_raw_store_pointer : forall ge f e ls l off v a es rest j cs m fuel xp p m',
  value_x ge e P v = Some (WPtr xp) ->
  value_x ge e A a = Some (WPtr p) ->
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Write 8 = Some ok ->
  pointer_store_effects (raw_address (ptr_addr p) off) xp m es = Some m' ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (RawStorePointer off v a es :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l off v a es rest j cs m fuel xp p m' Hv Ha Hc Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (RawStorePointer off v a es :: rest) j)) m
                 (RawStorePointer off v a es) = Some (IContinue e ls m')).
  { cbn - [value_x access_res pointer_store_effects raw_address]. rewrite Hv, Ha, Hc. cbn - [pointer_store_effects raw_address].
    rewrite Hs. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** ## Calls *)

(** A direct call of the function g, defined in the module, with
    arguments that read as xs and make its frame callee: the callee runs
    on top, and the caller waits at the rest of its block for the result
    r. *)
Lemma rule_call : forall ge f e ls l r g args rest j cs m fuel xs gf callee,
  map_option (arg_x ge e) args = Some xs ->
  find_fn ge g = Some (Defined gf) ->
  call_frame gf xs = Some callee ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) cs m fuel) =
  Next (mkConfig callee ((mkFrame f e ls None (Exec l rest j), mkPending r None) :: cs) m fuel).
Proof.
  intros ge f e ls l r g args rest j cs m fuel xs gf callee Hx Hf Hc.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) m
                 (Call r (Global g) args) = Some (ICall gf xs (mkPending r None))).
  { cbn - [map_option find_fn]. rewrite Hx, Hf. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_call; reflexivity).
  cbn [inst_next c_frame fr_fn fr_env fr_locals c_callers c_mem c_fuel]. rewrite Hc. reflexivity.
Qed.

(** A call of libc's `void free(p)`, a name the module neither defines
    nor holds as data, whose argument v reads as x, where the genv's
    free frees x without a trap and leaves the memory m': the frame
    goes on in m' ([external_call]). *)
Lemma rule_free : forall ge f e ls l v rest j cs m fuel x m',
  find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some x -> ge_free ge x m = Some (ok, m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j))
             cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l v rest j cs m fuel x m' Hf Hd Hx Hfree.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j))
                 m (Call CVoid (Global free_name) [Arg P v]) = Some (IContinue e ls m')).
  { cbn - [arg_x find_fn lookup ge_free]. rewrite Hx, Hf. unfold external_call. rewrite Hd.
    cbn - [ge_free]. rewrite Hfree. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_continue; reflexivity).
  reflexivity.
Qed.

(** ## Blocks and jumps *)

(** Entering the block l of f, found as b, from the edge from, with fuel
    left: its phis bind the environment e', and the frame goes on at
    its instructions with one [[fuel]] less. *)
Lemma rule_enter : forall ge f e ls l from cs m fuel b e',
  fuel <> 0 ->
  find_block l (fn_blocks f) = Some b ->
  phis_env ge (b_phis b) from e = Some e' ->
  step ge (mkConfig (mkFrame f e ls None (Enter l from)) cs m fuel) =
  Next (mkConfig (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) cs m (fuel - 1)).
Proof.
  intros ge f e ls l from cs m fuel b e' Hf Hb Hp. unfold step; cbn [fr_at c_frame c_fuel fr_fn fr_env].
  replace (fuel =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf).
  rewrite Hb. cbn [b_phis]. rewrite Hp. reflexivity.
Qed.

(** Entering a block with no fuel left ends the run, out of fuel. *)
Lemma rule_out_of_fuel : forall ge f e ls l from cs m,
  step ge (mkConfig (mkFrame f e ls None (Enter l from)) cs m 0) = Done OutOfFuel.
Proof. reflexivity. Qed.

(** A goto to the target t, polling or not, enters its block from l. *)
Lemma rule_goto : forall ge f e ls l t cs m fuel,
  step ge (mkConfig (mkFrame f e ls None (Exec l [] (JGoto t))) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Enter (edge_label t) (Some l))) cs m fuel).
Proof. intros. destruct t; reflexivity. Qed.

(** A branch on v, which reads as the integer n, enters t2's block from
    l if n is 0, else t1's. *)
Lemma rule_branch : forall ge f e ls l v t1 t2 cs m fuel n,
  value_x ge e W v = Some (WInt n) ->
  step ge (mkConfig (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) cs m fuel) =
  Next (mkConfig (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) cs m fuel).
Proof.
  intros ge f e ls l v t1 t2 cs m fuel n Hv. unfold step; cbn [fr_at c_frame fr_doomed jump_step fr_env].
  rewrite Hv. cbn [or_stuck]. destruct (n =? 0), t1, t2; reflexivity.
Qed.

(** A return of v, which reads as x at f's return class k: the
    invocation ends with [Ret x] ([return_step]). *)
Lemma rule_ret : forall ge f e ls l v cs m fuel k x,
  fn_ret f = RClass k ->
  value_x ge e k v = Some x ->
  step ge (mkConfig (mkFrame f e ls None (Exec l [] (JRet v))) cs m fuel) =
  return_step (mkConfig (mkFrame f e ls None (Exec l [] (JRet v))) cs m fuel) (Ret x).
Proof.
  intros ge f e ls l v cs m fuel k x Hk Hv. unfold step; cbn [fr_at c_frame fr_doomed jump_step fr_env fr_fn].
  rewrite Hk, Hv. reflexivity.
Qed.

(** A return from a `void` function: the invocation ends with
    [RetVoid] ([return_step]). *)
Lemma rule_ret_void : forall ge f e ls l cs m fuel,
  step ge (mkConfig (mkFrame f e ls None (Exec l [] JRetVoid)) cs m fuel) =
  return_step (mkConfig (mkFrame f e ls None (Exec l [] JRetVoid)) cs m fuel) RetVoid.
Proof. intros. reflexivity. Qed.

(** An invocation whose named locals end, leaving the memory m', and
    that has no caller: the run's outcome is o. *)
Lemma rule_return_top : forall fr m fuel o m',
  invalidate_locals (fr_locals fr) m = Some m' ->
  return_step (mkConfig fr [] m fuel) o = Done o.
Proof. intros fr m fuel o m' H. unfold return_step; cbn [c_frame c_mem c_callers]. rewrite H. reflexivity. Qed.

(** An invocation whose named locals end, leaving the memory m', and
    whose caller cf reads the result as pd says, binding its
    environment e': the caller goes on, in m'. *)
Lemma rule_return : forall fr cf pd cs m fuel o m' e',
  invalidate_locals (fr_locals fr) m = Some m' ->
  pd_conv pd = None ->
  returned_env (pd_res pd) o (fr_env cf) = Some e' ->
  return_step (mkConfig fr ((cf, pd) :: cs) m fuel) o =
  Next (mkConfig (mkFrame (fr_fn cf) e' (fr_locals cf) (fr_doomed cf) (fr_at cf)) cs m' fuel).
Proof.
  intros fr cf pd cs m fuel o m' e' H Hc He. unfold return_step; cbn [c_frame c_mem c_callers c_fuel].
  rewrite H, Hc, He. reflexivity.
Qed.

(** An invocation with no named locals ends without changing memory. *)
Lemma invalidate_none : forall m, invalidate_locals [] m = Some m.
Proof. reflexivity. Qed.

(** ## Access checks *)

(** An access of size bytes at the address a through the capability of
    the object b, live or not, with the region reg: it passes where the
    bytes lie in its bounds and a is aligned. *)
Lemma access_obj : forall m b reg a size r al,
  object_region b (m_regions m) = Some reg ->
  b <= a -> a + size <= r_end reg -> a mod al = 0 ->
  access_res m a (Obj b) size r al = Some ok.
Proof.
  intros m b reg a size r al Hr H1 H2 H3. unfold access_res, cap_access_res. rewrite Hr.
  replace ((b <=? a) && (a + size <=? r_end reg)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  unfold aligned_res. rewrite H3. reflexivity.
Qed.

(** A read through a read-write or read-only capability for the object
    b with the region reg, of size bytes at a within its bounds and
    aligned, passes. *)
Lemma access_read : forall m b reg c a size al,
  c = Obj b \/ c = Ro b ->
  object_region b (m_regions m) = Some reg ->
  b <= a -> a + size <= r_end reg -> a mod al = 0 ->
  access_res m a c size Read al = Some ok.
Proof.
  intros m b reg c a size al [->| ->] Hr H1 H2 H3; [exact (access_obj _ _ _ _ _ _ _ Hr H1 H2 H3)|].
  unfold access_res, cap_access_res. rewrite Hr.
  replace ((b <=? a) && (a + size <=? r_end reg)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  cbn [readonly_access_res]. unfold aligned_res. rewrite H3. reflexivity.
Qed.

(** A [[check]] of the pointer p whose access passes: p, proven. *)
Lemma op_check : forall m p lo hi r al,
  access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al = Some ok ->
  op_res (Check lo hi r al) A [WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof. intros m p lo hi r al H. cbn - [access_res raw_address]. rewrite H. reflexivity. Qed.

(** A [[half_check]] of the pointer p, against the proof p1 of the same
    capability, at a live object b whose bounds hold the bytes, which
    are aligned, and which ends at or below 2^63: p, proven. Both the full
    check and the half check's native test pass. *)
Lemma op_half_check : forall m p1 p bd lo hi r al b reg,
  ptr_cap p1 = Obj b -> ptr_cap p = Obj b ->
  object_region b (m_regions m) = Some reg -> r_life reg = Live ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  op_res (HalfCheck bd lo hi r al) A [WPtr p1; WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof.
  intros m p1 p bd lo hi r al b reg H1 H2 Hr Hl Hlo Hhi Hlh Hend Hal.
  assert (Hacc : access_res m (raw_address (ptr_addr p) lo) (Obj b) (hi - lo) r al = Some ok)
    by (eapply access_obj; eauto).
  cbn - [access_res raw_address half_passes]. rewrite H1, H2.
  cbn [cap_eqb]. rewrite Z.eqb_refl, Hacc.
  unfold half_passes. rewrite Hr. cbn [option_map].
  replace (half_bound bd (raw_address (ptr_addr p) lo) (hi - lo) b (r_end reg) (r_life reg)) with true.
  - rewrite Hal, Z.eqb_refl. destruct r; reflexivity.
  - symmetry. unfold half_bound. rewrite Hl. destruct bd; [apply Z.leb_le; lia|].
    assert (Hn : 0 <= raw_address (ptr_addr p) lo < 2 ^ 63).
    { pose proof (Z.mod_pos_bound (ptr_addr p + lo) (2 ^ 64) ltac:(lia)) as Hm.
      fold (raw_address (ptr_addr p) lo) in Hm. lia. }
    replace (2 ^ 63 <=? raw_address (ptr_addr p) lo) with false by (symmetry; apply Z.leb_gt; lia).
    apply Z.leb_le; lia.
Qed.

(** A read [[half_check]] of the pointer p, against the proof p1 of the
    same capability, an object's or a read-only object's, at a live
    object b whose bounds hold the bytes, which are aligned, and which
    ends at or below 2^63: p, proven. A read-only capability passes a
    read's native test as an object's does. *)
Lemma op_half_check_read : forall m p1 p bd lo hi al b reg,
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  object_region b (m_regions m) = Some reg -> r_life reg = Live ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  op_res (HalfCheck bd lo hi Read al) A [WPtr p1; WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof.
  intros m p1 p bd lo hi al b reg E Hc Hr Hl Hlo Hhi Hlh Hend Hal.
  destruct Hc as [Hc | Hc]; [rewrite Hc in E; exact (op_half_check _ _ _ _ _ _ Read _ _ _ E Hc Hr Hl Hlo Hhi Hlh Hend Hal)|].
  assert (Hacc : access_res m (raw_address (ptr_addr p) lo) (Ro b) (hi - lo) Read al = Some ok)
    by (eapply access_read; eauto).
  cbn - [access_res raw_address half_passes]. rewrite E, Hc.
  cbn [cap_eqb]. rewrite Z.eqb_refl, Hacc.
  unfold half_passes. rewrite Hr. cbn [option_map].
  replace (half_bound bd (raw_address (ptr_addr p) lo) (hi - lo) b (r_end reg) (r_life reg)) with true.
  - rewrite Hal, Z.eqb_refl. reflexivity.
  - symmetry. unfold half_bound. rewrite Hl. destruct bd; [apply Z.leb_le; lia|].
    assert (Hn : 0 <= raw_address (ptr_addr p) lo < 2 ^ 63).
    { pose proof (Z.mod_pos_bound (ptr_addr p + lo) (2 ^ 64) ltac:(lia)) as Hm.
      fold (raw_address (ptr_addr p) lo) in Hm. lia. }
    replace (2 ^ 63 <=? raw_address (ptr_addr p) lo) with false by (symmetry; apply Z.leb_gt; lia).
    apply Z.leb_le; lia.
Qed.

(** A [[renew]] of the pointer p, against the proof p1 of the same
    capability, whose own access check passes: p, proven, as the check
    it replaced would have proven it. *)
Lemma op_renew : forall m p1 p lo hi r al,
  ptr_cap p1 = ptr_cap p ->
  access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al = Some ok ->
  op_res (Renew lo hi r al) A [WPtr p1; WPtr p] m = Some (OpRes (RVal (WPtr p)) m).
Proof.
  intros m p1 p lo hi r al E H. cbn - [access_res raw_address cap_eqb]. rewrite E.
  replace (cap_eqb (ptr_cap p) (ptr_cap p)) with true
    by (symmetry; destruct (ptr_cap p); cbn; try apply Z.eqb_refl; try apply term_eqb_refl; reflexivity).
  rewrite H. reflexivity.
Qed.

(** A raw load of 8 bytes at offset off from the proven pointer p, whose
    read access passes: the little-endian integer there. *)
Lemma op_raw_load : forall m k p off,
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Read 1 = Some ok ->
  op_res (RawLoad LdL off) k [WPtr p] m =
  Some (OpRes (RVal (WInt (load_bytes m (raw_address (ptr_addr p) off) 8))) m).
Proof.
  intros m k p off H.
  assert (E : op_res (RawLoad LdL off) k [WPtr p] m = op_res_int (RawLoad LdL off) k [WPtr p] m)
    by (destruct k; reflexivity).
  rewrite E. cbn - [access_res raw_address load_bytes]. unfold int_load_res. cbn - [access_res raw_address load_bytes]. rewrite H. reflexivity.
Qed.

(** A raw load of the one-byte narrow type n at offset off from the
    proven pointer p, whose read access passes: the byte there, extended
    to the class k. *)
Lemma op_raw_load_byte : forall m k n p off,
  fst (narrow_type n) = 1 ->
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 1 Read 1 = Some ok ->
  op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
  option_map (fun y => OpRes (RVal y) m) (extended n k (m_bytes m (raw_address (ptr_addr p) off))).
Proof.
  intros m k n p off Hn H.
  assert (E : op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
              op_res_int (RawLoad (LdNarrow n) off) k [WPtr p] m) by (destruct k; reflexivity).
  assert (Hl : load_bytes m (raw_address (ptr_addr p) off) 1 = m_bytes m (raw_address (ptr_addr p) off)).
  { unfold load_bytes. change (Z.to_nat 1) with 1%nat. cbn - [raw_address]. now rewrite Z.add_0_r. }
  rewrite E. cbn - [access_res raw_address load_bytes narrow_type extended]. unfold int_load_res.
  rewrite Hn, H, Hl. destruct (extended n k _); reflexivity.
Qed.

(** A raw pointer load at offset off from the proven pointer p, whose
    8-byte read access passes and whose protocol es loads x: x. *)
Lemma op_raw_load_pointer : forall m p off es x,
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 8 Read 8 = Some ok ->
  pointer_load_effects m (raw_address (ptr_addr p) off) es = Some x ->
  op_res (RawLoadPointer off es) P [WPtr p] m = Some (OpRes (RVal (WPtr x)) m).
Proof.
  intros m p off es x H He. cbn - [access_res raw_address pointer_load_effects]. rewrite H.
  cbn - [raw_address pointer_load_effects]. rewrite He. reflexivity.
Qed.

(** The load protocol nanofil emits for a plain pointer load reads the
    [[aux]] capability, takes it as the [[lower]], then reads the
    address: the pointer of the 8 bytes at a and the capability stored
    there. *)
Lemma pointer_load_plain : forall m a,
  pointer_load_effects m a [AuxRead; LowerResolve; AddressRead] =
  Some (mkPtr (load_bytes m a 8) (aux_at m a)).
Proof. reflexivity. Qed.

(** The store protocol nanofil emits for a plain pointer store writes
    the capability to the aux, then the address to the bytes. *)
Lemma pointer_store_plain : forall m a x,
  pointer_store_effects a x m [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] =
  Some (store_bytes (store_aux m a (ptr_cap x)) a 8 (ptr_addr x)).
Proof. reflexivity. Qed.

(** A read of size bytes at the address a through the read-only
    capability of the object b, with the region reg: it passes where
    the bytes lie in its bounds and a is aligned, as [access_obj] for a
    read. *)
Lemma access_ro_read : forall m b reg a size al,
  object_region b (m_regions m) = Some reg ->
  b <= a -> a + size <= r_end reg -> a mod al = 0 ->
  access_res m a (Ro b) size Read al = Some ok.
Proof.
  intros m b reg a size al Hr H1 H2 H3. unfold access_res, cap_access_res. rewrite Hr.
  replace ((b <=? a) && (a + size <=? r_end reg)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  unfold readonly_access_res, aligned_res. rewrite H3. reflexivity.
Qed.

(** A store of the integer v as a long at the address a through the
    capability c, whose 8-byte write access passes: its bytes. *)
Lemma store_res_long : forall m a c v,
  access_res m a c 8 Write 1 = Some ok ->
  store_res Wl m a c (WInt v) = Some (ok, store_bytes m a 8 v).
Proof. intros m a c v H. cbn - [access_res store_bytes]. rewrite H. reflexivity. Qed.

(** A raw load of the narrow type n, of s bytes, at offset off from the
    proven pointer p, whose read access passes: the s bytes there,
    extended to the class k. [op_raw_load_byte] for every width. *)
Lemma op_raw_load_narrow : forall m k n p off,
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) (fst (narrow_type n)) Read 1 = Some ok ->
  op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
  option_map (fun y => OpRes (RVal y) m)
    (extended n k (load_bytes m (raw_address (ptr_addr p) off) (fst (narrow_type n)))).
Proof.
  intros m k n p off H.
  assert (E : op_res (RawLoad (LdNarrow n) off) k [WPtr p] m =
              op_res_int (RawLoad (LdNarrow n) off) k [WPtr p] m) by (destruct k; reflexivity).
  rewrite E. cbn - [access_res raw_address load_bytes narrow_type extended]. unfold int_load_res.
  rewrite H. destruct (extended n k _); reflexivity.
Qed.

(** ## Allocations Fil-C refuses *)

(** A heap allocation of size bytes, size read as the only argument and
    over Fil-C's limit: the run stops with the [TooBig] trap, a refusal
    (Panics.v), not a failure. *)
Lemma rule_alloc_too_big : forall ge f e ls l d k al args rest j cs m fuel size,
  map2_option (value_x ge e) [L] args = Some [WInt size] ->
  max_allocation_size < size ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) cs m fuel) =
  Done (Trap TooBig).
Proof.
  intros ge f e ls l d k al args rest j cs m fuel size Hx Hs.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (Let d k (Alloc al) args :: rest) j)) m
                 (Let d k (Alloc al) args) = Some (IStop (Trap TooBig))).
  { destruct k; cbn - [map2_option max_allocation_size]; rewrite Hx; cbn - [max_allocation_size];
      replace (max_allocation_size <? size) with true by (symmetry; apply Z.ltb_lt; exact Hs);
      reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (destruct k; reflexivity).
  reflexivity.
Qed.

(** ## Calls through function pointers *)

(** A [[check]] of the function pointer v, which reads as p, the exact
    address of a function ([function_check_res]): d is bound to p. *)
Lemma rule_check_function : forall ge f e ls l d v rest j cs m fuel p,
  value_x ge e P v = Some (WPtr p) -> function_check_res ge p = Some ok ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d F CheckFunction [v] :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) cs m fuel).
Proof.
  intros ge f e ls l d v rest j cs m fuel p Hv Hc.
  apply (rule_inst ge f e ls l _ rest j cs m fuel (IContinue (put d (WPtr p) e) ls m)).
  - cbn [inst_step fr_env fr_locals]. rewrite Hv. cbn - [function_check_res]. rewrite Hc. reflexivity.
  - apply doomed_result_continue. reflexivity.
Qed.

(** A call through the proven function pointer callee, which reads as
    p, the exact address of the module's function g, defined as gf,
    with arguments that read as xs: they are converted to gf's
    parameters through the [[fast-generic-convention|generic entry]]
    ([indirect_call_conv]), a variadic gf also gets the rest of xs as
    they are, and the frame callee of those words runs on top while the
    caller waits at the rest of its block, reading the result as r and
    converting its words as words says. *)
Lemma rule_raw_call : forall ge f e ls l r callee args rest j cs m fuel p g xs gf ys words fr',
  value_x ge e F callee = Some (WPtr p) -> ptr_cap p = Fn g -> function_check_res ge p = Some ok ->
  map_option (arg_x ge e) args = Some xs -> find_fn ge g = Some (Defined gf) ->
  indirect_call_conv gf r args xs = Some (Converted ys words) ->
  call_frame gf (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else [])) = Some fr' ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (RawCall r callee args :: rest) j)) cs m fuel) =
  Next (mkConfig fr' ((mkFrame f e ls None (Exec l rest j), mkPending r words) :: cs) m fuel).
Proof.
  intros ge f e ls l r callee args rest j cs m fuel p g xs gf ys words fr' Hv Hp Hc Hx Hf Hcv Hfr.
  assert (Hi : inst_step ge (mkFrame f e ls None (Exec l (RawCall r callee args :: rest) j)) m
                 (RawCall r callee args) =
               Some (ICall gf (ys ++ (if variadic_func gf then skipn (length (fn_params gf)) xs else []))
                       (mkPending r words))).
  { cbn - [value_x map_option function_check_res find_fn indirect_call_conv].
    rewrite Hv, Hx. cbn - [function_check_res find_fn indirect_call_conv].
    rewrite Hc. cbn - [find_fn indirect_call_conv]. rewrite Hp, Hf, Hcv. reflexivity. }
  rewrite (rule_inst _ _ _ _ _ _ _ _ _ _ _ _ Hi) by (apply doomed_result_call; reflexivity).
  cbn [inst_next c_frame fr_fn fr_env fr_locals c_callers c_mem c_fuel]. rewrite Hfr. reflexivity.
Qed.

(** ## Variadic arguments *)

(** Reading the hidden variadic snapshot p at the offset off: d is
    bound to p moved by off, with p's capability. The pointer is frame
    state, not a heap resource. *)
Lemma rule_va_args : forall ge f e ls l d off rest j cs m fuel p,
  lookup va_snapshot e = Some (WPtr p) ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d P VaArgs [Const off] :: rest) j)) cs m fuel) =
  Next (mkConfig
    (mkFrame f (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
      ls None (Exec l rest j)) cs m fuel).
Proof.
  intros ge f e ls l d off rest j cs m fuel p Hp.
  apply (rule_inst ge f e ls l (Let d P VaArgs [Const off]) rest j cs m fuel
    (IContinue (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e) ls m)).
  - cbn [inst_step fr_env fr_locals]. rewrite Hp. reflexivity.
  - apply doomed_result_continue. reflexivity.
Qed.

(** A variadic read of class k through the va_list p, whose
    [va_arg_res] is x in the memory m': d is bound to x, in m'. The
    cursor at p is memory, not frame state. *)
Lemma rule_va_arg : forall ge f e ls l d k args rest j cs m fuel p x m',
  map2_option (value_x ge e) [P] args = Some [WPtr p] ->
  va_arg_res k p m = Some (RVal x, m') ->
  step ge (mkConfig (mkFrame f e ls None (Exec l (Let d k VaArg args :: rest) j)) cs m fuel) =
  Next (mkConfig (mkFrame f (put d x e) ls None (Exec l rest j)) cs m' fuel).
Proof.
  intros ge f e ls l d k args rest j cs m fuel p x m' Hargs Hread.
  apply rule_let with (classes := [P]) (xs := [WPtr p]); [reflexivity | reflexivity | exact Hargs |].
  cbn [op_res]. rewrite Hread. reflexivity.
Qed.

(** Rounding an 8-aligned address up to 8 leaves it. *)
Lemma round8_aligned : forall a, a mod 8 = 0 -> (a + 8 - 1) / 8 * 8 = a.
Proof.
  intros a Hal. pose proof (Z.div_mod a 8 ltac:(lia)) as Hdiv. rewrite Hal in Hdiv.
  replace (a + 8 - 1) with (7 + (a / 8) * 8) by lia.
  rewrite Z.div_add by lia. replace (7 / 8) with 0 by reflexivity. lia.
Qed.

(** A pointer va_arg through the va_list p whose cursor, the address a
    and capability c stored at p, is 8-aligned: both reads pass, the
    cursor's [Wl] store makes m', and the result is the pointer x whose
    address and capability m' holds at a, even where the store
    overlaps a's cell. *)
Lemma va_arg_pointer : forall m p a c m' x,
  access_res m (ptr_addr p) (ptr_cap p) 8 Read 8 = Some ok ->
  load_bytes m (ptr_addr p) 8 = a -> aux_at m (ptr_addr p) = c ->
  a mod 8 = 0 -> access_res m a c 8 Read 8 = Some ok ->
  store_res Wl m (ptr_addr p) (ptr_cap p) (WInt (a + 8)) = Some (ok, m') ->
  load_bytes m' a 8 = ptr_addr x -> aux_at m' a = ptr_cap x ->
  va_arg_res P p m = Some (RVal (WPtr x), m').
Proof.
  intros m p a c m' x Hp Ha Hc Hal Hcell Hstore Haddr Hcap.
  unfold va_arg_res. rewrite Hp, Ha, Hc. cbn [va_cell class_width width_bytes ptr_addr ptr_cap].
  rewrite (round8_aligned a Hal), Hcell, Hstore, Haddr, Hcap. destruct x. reflexivity.
Qed.

(** An integer va_arg of class k, whose cell is n bytes at an 8-aligned
    address ([va_cell]), through the va_list p whose cursor cur rounds
    up to a: both reads pass, the cursor's [Wl] store of a + n makes
    m', and the result is the n bytes m' holds at a. *)
Lemma va_arg_int : forall m k w n p cur c a m',
  k <> P -> class_width k = Some w -> va_cell k = Some (n, 8) ->
  access_res m (ptr_addr p) (ptr_cap p) 8 Read 8 = Some ok ->
  load_bytes m (ptr_addr p) 8 = cur -> aux_at m (ptr_addr p) = c ->
  (cur + 8 - 1) / 8 * 8 = a -> access_res m a c n Read 8 = Some ok ->
  store_res Wl m (ptr_addr p) (ptr_cap p) (WInt (a + n)) = Some (ok, m') ->
  va_arg_res k p m = Some (RVal (WInt (load_bytes m' a (width_bytes w))), m').
Proof.
  intros m k w n p cur c a m' Hk Hw Hcl Hp Hcur Hc Ha Hcell Hstore.
  unfold va_arg_res. rewrite Hp, Hcur, Hc, Hcl, Hw. cbn [ptr_addr ptr_cap].
  rewrite Ha, Hcell, Hstore. destruct k; try reflexivity. contradiction.
Qed.

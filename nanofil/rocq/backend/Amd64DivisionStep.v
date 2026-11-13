(** Amd64Division.v proves that the register part of an emitted
    division computes the IR's result from two registers. This module
    extends that theorem to the whole instruction. The emitted code
    for the IR instruction that binds a temporary to a quotient or a
    remainder loads the two operands from the stack frame, divides in
    registers, and stores the result into the frame.

    The theorem [division_instruction_correct] relates one step of the
    IR's semantics to that code. Suppose that the IR executes the
    instruction in an environment and that a machine state represents
    the environment, in the sense of Amd64Frame.v. Then the IR
    continues with the destination bound to an integer, the emitted
    lines are inside the model, and every execution of them ends
    without a fault in a state that represents the new environment.

    The code has four parts, which run in order: a load of each
    operand, the division in registers, and the store of the result.
    Earlier modules prove what each part does on its own. This module
    shows that the parts fit together. Each part leaves the machine in
    a state that the next part accepts, and the division in registers
    does not change the frame.

    The examples at the end of the module execute the emitted lines on
    a small frame. They test the model apart from the proofs. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Maps.
From Nanofil Require Values Memory Ops Semantics.
From Backend Require Import Asm Plan PlanTerm Layout EmitOps EmitInst.
From Backend Require Import Amd64Word Amd64Memory Amd64Machine Amd64Step Amd64Asm
  Amd64Total Amd64DivisionCode Amd64Division Amd64Frame.
Import ListNotations.
Local Open Scope Z_scope.

(** ## The step of the IR

    The IR's semantics executes an instruction with the function
    `inst_step`, which handles every operation of the language. This
    section states what that function does for an integer division, so
    the rest of the module does not unfold it. *)

(** When the IR executes a division at an integer class, both
    operands evaluate to integers, the operation returns an integer,
    and execution continues with the destination bound to that
    integer. The locals and the IR's memory do not change. The IR has
    no step when an operand is unassigned or is not an integer, and
    the hypothesis excludes those cases. *)
Lemma division_step_inversion (ge : Semantics.genv) (fr : Semantics.frame)
    (m : Memory.mem) (sg : signedness) (remainder : bool) (k : class) (z : size)
    (d : name) (x y : value) (out : Semantics.inst_out) :
  class_size k = Some z ->
  Semantics.inst_step ge fr m (Let d k (division_op sg remainder) [x; y]) = Some out ->
  exists a b w,
    Semantics.value_x ge (Semantics.fr_env fr) k x = Some (Values.WInt a)
    /\ Semantics.value_x ge (Semantics.fr_env fr) k y = Some (Values.WInt b)
    /\ Ops.alu (division_op sg remainder) k [Values.WInt a; Values.WInt b]
       = Some (Values.WInt w)
    /\ out = Semantics.IContinue (put d (Values.WInt w) (Semantics.fr_env fr))
               (Semantics.fr_locals fr) m.
Proof.
  intro Hk. destruct k; try discriminate; destruct sg, remainder;
    cbn [division_op Semantics.inst_step op_arg_classes Semantics.map2_option];
    destruct (Semantics.value_x ge (Semantics.fr_env fr) _ x) as [vx|] eqn:Ex;
    cbn; try discriminate;
    destruct (Semantics.value_x ge (Semantics.fr_env fr) _ y) as [vy|] eqn:Ey;
    cbn; try discriminate;
    destruct vx, vy;
    cbn [Ops.op_res Ops.op_res_int Ops.alu]; try discriminate;
    intro H;
    repeat match type of H with
    | context [match ?v with Some _ => _ | None => _ end] =>
        destruct v eqn:?; try discriminate
    end;
    inversion H; subst;
    do 3 eexists; repeat split; eauto;
    cbn [division_op Ops.alu]; repeat match goal with
    | E : ?v = Some _ |- context [?v] => rewrite E
    end; reflexivity.
Qed.

(** ## The emitted lines

    The emitter writes the lines of a `Let` instruction with the
    function `let_lines`. This section shows that its lines for a
    division are four fragments in sequence, and that the third
    fragment writes no memory. *)

(** The lines that the emitter writes for a division at an integer
    class are the load of each operand, the register part
    `division_lines`, and the store of `%rax` into the slot of the
    destination. *)
Lemma let_lines_division (cx : ctx) (b : name) (index : string) (sg : signedness)
    (remainder : bool) (k : class) (z : size) (d : name) (x y : value) :
  class_size k = Some z ->
  let_lines cx b index d k (division_op sg remainder) [x; y]
  = load cx x k "a" ++ load cx y k "c"
    ++ division_lines sg remainder k ++ slot_store cx "rax" (KTmp d).
Proof.
  intro Hk. destruct k; try discriminate; destruct sg, remainder;
    cbn [division_op let_lines x87_op]; unfold integer_inst;
    cbn [compute_op float_compute sse_class];
    rewrite division_split with (z := z) by exact Hk;
    repeat rewrite app_assoc; reflexivity.
Qed.

(** No instruction of the register part of a division is a store. *)
Lemma division_code_stores_nothing (sg : signedness) (remainder : bool) (z : size)
    (i : instr) :
  In i (division_code sg remainder z) -> stores i = false.
Proof.
  destruct sg, remainder; unfold division_code, zero_divisor_code,
    minus_one_divisor_code, divide_code, result_code;
    cbn [app In]; intros H; repeat destruct H as [H | H];
    try contradiction; subst i; reflexivity.
Qed.

(** The register part of a division computes the IR's result in
    `%rax`, and it leaves the memory and the set of mapped addresses
    as it found them. This lemma is the division theorem of
    Amd64Division.v with the facts about memory added. *)
Lemma division_code_keeps_memory (sg : signedness) (remainder : bool) (k : class)
    (z : size) :
  class_size k = Some z ->
  establishes (fun _ => True) (division_code sg remainder z)
    (fun s s' =>
       division_result_in_rax sg remainder k z s s'
       /\ bytes s' = bytes s /\ mapped s' = mapped s).
Proof.
  intro Hk. apply establishes_memory.
  - apply division_code_correct; exact Hk.
  - intros i Hi. eapply division_code_stores_nothing; exact Hi.
Qed.

(** ## The fragments on a frame

    The four fragments run in sequence, and each one starts in a state
    where the frame is placed and represents the environment. This
    section proves that the first three fragments keep that
    condition. *)

(** A state with the same `%rbp`, the same memory and the same mapped
    addresses as another state has the frame in the same place, and it
    represents the same environments. *)
Lemma frame_kept (cx : ctx) (live : name -> Prop) (e : Semantics.env)
    (s s' : machine) :
  slots_laid_out cx ->
  regs s' RBP = regs s RBP -> bytes s' = bytes s -> mapped s' = mapped s ->
  frame_placed cx s /\ represents cx live e s ->
  frame_placed cx s' /\ represents cx live e s'.
Proof.
  intros Hlayout Hbp Hbytes Hmapped [Hplaced Hrep]. split.
  - eapply frame_placed_preserved; eassumption.
  - eapply represents_same_frame; try eassumption.
    intros a _. rewrite Hbytes. reflexivity.
Qed.

(** The two loads of a division are inside the model and never fault.
    They leave the first operand in `%rax` and the second in `%rcx`,
    each as the integer to which the IR evaluates it. They change no
    other register and no memory. *)
Lemma operands_loaded_spec (cx : ctx) (ge : Semantics.genv) (live : name -> Prop)
    (e : Semantics.env) (k : class) (z : size) (x y : value) (a b : Z) :
  class_size k = Some z ->
  slots_laid_out cx ->
  frame_encodable cx ->
  operand_placed cx x -> operand_placed cx y ->
  operand_live live x -> operand_live live y ->
  Semantics.value_x ge e k x = Some (Values.WInt a) ->
  Semantics.value_x ge e k y = Some (Values.WInt b) ->
  exists code,
    decode_lines (load cx x k "a" ++ load cx y k "c") = Some code
    /\ establishes (fun s => frame_placed cx s /\ represents cx live e s) code
         (fun s s' =>
            regs s' RAX = a /\ regs s' RCX = b
            /\ (forall r, r <> RAX -> r <> RCX -> regs s' r = regs s r)
            /\ bytes s' = bytes s /\ mapped s' = mapped s).
Proof.
  intros Hk Hlayout Henc Hpx Hpy Hlx Hly Hx Hy.
  destruct (load_operand_spec cx ge live e k z x a "a" RAX
    Hk Hlayout Henc names_rax Hpx Hlx Hx) as [ca [Da Sa]].
  destruct (load_operand_spec cx ge live e k z y b "c" RCX
    Hk Hlayout Henc names_rcx Hpy Hly Hy) as [cc [Dc Sc]].
  exists (ca ++ cc). split.
  - apply decode_lines_app; assumption.
  - eapply establishes_weaken.
    + eapply establishes_app; [exact Sa | exact Sc |].
      intros s t HP [_ [Hr [Hb Hm]]].
      eapply frame_kept; try eassumption. apply Hr; discriminate.
    + intros s HP; exact HP.
    + intros s u _ [t [[Ha [Ra [Ba Ma]]] [Hc [Rc [Bc Mc]]]]].
      repeat split.
      * rewrite Rc by discriminate. exact Ha.
      * exact Hc.
      * intros r Hra Hrc. rewrite Rc by exact Hrc. apply Ra; exact Hra.
      * rewrite Bc, Ba. reflexivity.
      * rewrite Mc, Ma. reflexivity.
Qed.

(** ## The whole instruction

    The theorem of this section joins the four fragments. Its
    postcondition has three parts: the frame is still placed, the
    final state represents the environment after the IR's step, and
    the code has changed nothing that the rest of the function relies
    on. *)

(** The relation [instruction_keeps] holds of two states when the
    second differs from the first in at most the scratch registers
    `%rax`, `%rcx` and `%rdx`, the flags, and the eight bytes of the
    slot at the offset off. Every other register, every byte outside
    that slot and the set of mapped addresses are the same. *)
Definition instruction_keeps (off : Z) (s s' : machine) : Prop :=
  scratch_only s s'
  /\ mapped s' = mapped s
  /\ (forall a, a < slot_address off s \/ slot_address off s + 8 <= a ->
        bytes s' a = bytes s a).

(** The emitted code for a division instruction implements the IR's
    step. The hypotheses are about the frame and the operands: the
    slots are laid out and encodable, each operand that is a temporary
    is live and has a slot, and the destination d has the slot at the
    offset off. If the IR has a step for the instruction, then that
    step continues with d bound to an integer w. The emitted lines
    have a typed reading, and from every state where the frame is
    placed and represents the environment, they run without a fault to
    a state that represents the environment with d bound to w. The
    live set afterwards is [live_after], which drops a temporary that
    shared the slot of d. *)
Theorem division_instruction_correct (cx : ctx) (ge : Semantics.genv)
    (fr : Semantics.frame) (m : Memory.mem) (live : name -> Prop) (b : name)
    (index : string) (sg : signedness) (remainder : bool) (k : class) (z : size)
    (d : name) (off : Z) (x y : value) (out : Semantics.inst_out) :
  class_size k = Some z ->
  slots_laid_out cx ->
  frame_encodable cx ->
  operand_placed cx x -> operand_placed cx y ->
  operand_live live x -> operand_live live y ->
  slot cx (KTmp d) = Some off ->
  Semantics.inst_step ge fr m (Let d k (division_op sg remainder) [x; y]) = Some out ->
  exists w code,
    out = Semantics.IContinue (put d (Values.WInt w) (Semantics.fr_env fr))
            (Semantics.fr_locals fr) m
    /\ decode_lines (let_lines cx b index d k (division_op sg remainder) [x; y])
       = Some code
    /\ establishes
         (fun s => frame_placed cx s /\ represents cx live (Semantics.fr_env fr) s)
         code
         (fun s s' =>
            frame_placed cx s'
            /\ represents cx (live_after cx live d)
                 (put d (Values.WInt w) (Semantics.fr_env fr)) s'
            /\ instruction_keeps off s s').
Proof.
  intros Hk Hlayout Henc Hpx Hpy Hlx Hly Hd Hstep.
  destruct (division_step_inversion ge fr m sg remainder k z d x y out Hk Hstep)
    as [a [c [w [Hx [Hy [Halu Hout]]]]]].
  destruct (operands_loaded_spec cx ge live (Semantics.fr_env fr) k z x y a c
    Hk Hlayout Henc Hpx Hpy Hlx Hly Hx Hy) as [cl [Dl Sl]].
  destruct (store_slot_spec cx live (Semantics.fr_env fr) d off "rax" RAX
    Hlayout Henc eq_refl Hd) as [cs [Ds Ss]].
  assert (Sp : establishes
    (fun s => frame_placed cx s /\ represents cx live (Semantics.fr_env fr) s)
    (cl ++ division_code sg remainder z)
    (fun s u =>
      (frame_placed cx u /\ represents cx live (Semantics.fr_env fr) u)
      /\ regs u RAX = w /\ scratch_only s u
      /\ bytes u = bytes s /\ mapped u = mapped s)).
  { eapply establishes_weaken.
    - eapply establishes_app.
      + exact Sl.
      + apply division_code_keeps_memory; exact Hk.
      + intros; exact I.
    - intros s HP; exact HP.
    - intros s u HP [t [[Ha [Hc [Hr [Hb Hm]]]] [[Hresult Hscratch] [Hb' Hm']]]].
      assert (Ht : frame_placed cx t /\ represents cx live (Semantics.fr_env fr) t).
      { eapply frame_kept; try eassumption. apply Hr; discriminate. }
      split.
      + eapply frame_kept; try eassumption.
        apply Hscratch; discriminate.
      + split.
        * unfold get_reg in Hresult. rewrite Ha, Hc in Hresult.
          rewrite (wrap_small z a (value_x_range ge (Semantics.fr_env fr) k z x a Hk Hx)),
            (wrap_small z c (value_x_range ge (Semantics.fr_env fr) k z y c Hk Hy))
            in Hresult.
          rewrite Halu in Hresult. injection Hresult; auto.
        * split.
          -- intros r Hra Hrc Hrd. rewrite Hscratch by assumption.
             apply Hr; assumption.
          -- split; [rewrite Hb', Hb | rewrite Hm', Hm]; reflexivity. }
  exists w, ((cl ++ division_code sg remainder z) ++ cs).
  split; [exact Hout |]. split.
  - rewrite let_lines_division with (z := z) by exact Hk.
    repeat rewrite app_assoc. apply decode_lines_app; [|exact Ds].
    apply decode_lines_app; [exact Dl | apply division_lines_decode; exact Hk].
  - eapply establishes_weaken.
    + eapply establishes_app; [exact Sp | exact Ss |].
      intros s u _ [HP _]. exact HP.
    + intros s HP; exact HP.
    + intros s v _ [u [[[Hu Hrep] [Hrax [Hr [Hb Hm]]]] [Hnew [Rv [Mv Bv]]]]].
      split.
      * eapply frame_placed_preserved; [exact Hu | apply Rv | exact Mv].
      * split; [rewrite Hrax in Hnew; exact Hnew |].
        unfold instruction_keeps. split.
        -- intros r Hra Hrc Hrd. rewrite Rv. apply Hr; assumption.
        -- split; [rewrite Mv, Hm; reflexivity |].
           assert (Haddr : slot_address off u = slot_address off s).
           { unfold slot_address. rewrite Hr by discriminate. reflexivity. }
           intros addr Houtside. rewrite Bv; [rewrite Hb; reflexivity |].
           rewrite Haddr. exact Houtside.
Qed.

(** This corollary states the same result without the relation
    [establishes]. Every execution of the emitted lines from a state
    that represents the IR's environment ends in a state and not in a
    fault, and that state represents the environment in which the IR
    continues. *)
Corollary division_instruction_never_faults (cx : ctx) (ge : Semantics.genv)
    (fr : Semantics.frame) (m : Memory.mem) (live : name -> Prop) (b : name)
    (index : string) (sg : signedness) (remainder : bool) (k : class) (z : size)
    (d : name) (off : Z) (x y : value) (out : Semantics.inst_out)
    (code : list instr) (s : machine) (o : outcome) :
  class_size k = Some z ->
  slots_laid_out cx ->
  frame_encodable cx ->
  operand_placed cx x -> operand_placed cx y ->
  operand_live live x -> operand_live live y ->
  slot cx (KTmp d) = Some off ->
  Semantics.inst_step ge fr m (Let d k (division_op sg remainder) [x; y]) = Some out ->
  decode_lines (let_lines cx b index d k (division_op sg remainder) [x; y]) = Some code ->
  frame_placed cx s ->
  represents cx live (Semantics.fr_env fr) s ->
  runs code s o ->
  exists e' s',
    out = Semantics.IContinue e' (Semantics.fr_locals fr) m
    /\ o = Next s'
    /\ frame_placed cx s'
    /\ represents cx (live_after cx live d) e' s'
    /\ instruction_keeps off s s'.
Proof.
  intros Hk Hlayout Henc Hpx Hpy Hlx Hly Hd Hstep Hdecode Hplaced Hrep Hrun.
  destruct (division_instruction_correct cx ge fr m live b index sg remainder k z
    d off x y out Hk Hlayout Henc Hpx Hpy Hlx Hly Hd Hstep)
    as [w [code' [Hout [Hdecode' Hcorrect]]]].
  rewrite Hdecode in Hdecode'. injection Hdecode' as E; subst code'.
  destruct (Hcorrect s o (conj Hplaced Hrep) Hrun) as [s' [Ho [Hp [Hr Hkeep]]]].
  exists (put d (Values.WInt w) (Semantics.fr_env fr)), s'.
  exact (conj Hout (conj Ho (conj Hp (conj Hr Hkeep)))).
Qed.

(** ## Executions on a concrete frame

    These examples execute the emitted lines of one division on a
    frame of 32 bytes with three slots. They compare the content of
    the destination's slot with the result that the IR defines. They
    are evaluations of the model, which test it apart from the
    proofs. *)

(** The temporaries of the examples are the two operands and the
    destination. *)
Definition sample_x : name := TAtom "x".
Definition sample_y : name := TAtom "y".
Definition sample_d : name := TAtom "d".

(** The context [sample_ctx] has a frame of 32 bytes. The slots of the
    operands are 8 and 16 bytes below `%rbp`, and the slot of the
    destination is 24 bytes below it. *)
Definition sample_ctx : ctx :=
  mkCtx "f"
    (nm_of_list [(key_term (KTmp sample_x), 8); (key_term (KTmp sample_y), 16);
                 (key_term (KTmp sample_d), 24)])
    nm_empty 32 32 nm_empty.

(** The state [sample_state] is the machine state on which the
    examples run. The register `%rbp` holds the address 4096, and the
    slots of the two operands hold the integers a and c. The argument
    placed says whether the 32 bytes of the frame are mapped. Every
    other register and every other byte has all bits set, so that code
    which wrongly reads stale state does not read zero. *)
Definition sample_state (placed : bool) (a c : Z) : machine :=
  mkMachine
    (fun r => match r with RBP => 4096 | _ => 18446744073709551615 end)
    (fun _ => true)
    (write_at S64 (write_at S64 (fun _ => 255) 4088 a) 4080 c)
    (fun addr => placed && (4064 <=? addr) && (addr <? 4096)).

(** The function [slot_after] executes the emitted lines of an
    instruction on a state, with every undefined flag set. It returns
    the 64-bit content of the destination's slot after a completed
    execution, and `None` when a line has no typed reading or the
    execution faults. *)
Definition slot_after (ls : list line) (s : machine) : option Z :=
  match decode_lines ls with
  | Some code =>
      match run (fun _ => true) code s with
      | Next s' => Some (read_at S64 (bytes s') 4072)
      | Fault _ => None
      end
  | None => None
  end.

(** The function [sample_lines] returns the emitted lines for the
    instruction that binds the destination to the operation o, at the
    class k, of the first operand and the value y. *)
Definition sample_lines (o : op) (k : class) (y : value) : list line :=
  let_lines sample_ctx (TAtom "start") "0" sample_d k o [Tmp sample_x; y].

(** The 32-bit division of -7 by 2 stores -3, zero-extended to 64
    bits, in the destination's slot. *)
Example frame_signed_division :
  slot_after (sample_lines Div W (Tmp sample_y)) (sample_state true 4294967289 2)
  = Some 4294967293.
Proof. vm_compute. reflexivity. Qed.

(** A division by zero stores 0 and does not fault. *)
Example frame_division_by_zero :
  slot_after (sample_lines Div W (Tmp sample_y)) (sample_state true 7 0) = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** A 32-bit load reads only the low four bytes of a slot, so the high
    bytes of the operand's slot do not reach the result. *)
Example frame_reads_low_half :
  slot_after (sample_lines Udiv W (Tmp sample_y))
    (sample_state true (4294967296 * 5 + 100) 7)
  = Some 14.
Proof. vm_compute. reflexivity. Qed.

(** A constant operand needs no slot. The 64-bit remainder of the
    least integer by the constant -1 is 0. *)
Example frame_constant_divisor :
  slot_after (sample_lines Rem L (Const (-1))) (sample_state true 9223372036854775808 0)
  = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** The same code faults on a state where the frame is not mapped,
    which is why the theorem assumes that the frame is placed. *)
Example frame_unmapped_faults :
  slot_after (sample_lines Div W (Tmp sample_y)) (sample_state false 7 2) = None.
Proof. vm_compute. reflexivity. Qed.

(** The IR's step for the first example binds the destination to the
    same integer that the emitted code stores. *)
Example frame_step_agrees :
  Ops.alu Div W [Values.WInt 4294967289; Values.WInt 2] = Some (Values.WInt 4294967293).
Proof. vm_compute. reflexivity. Qed.

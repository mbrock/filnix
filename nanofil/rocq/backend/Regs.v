(** # Whole-function register allocation and selection

    A simple, loop-weighted interval register allocator and direct
    register emitter for the Gallina backend (M7 of
    docs/gallina-backend.md). It takes the [func] and [plan] that
    Validate.v and Abi.v produce, numbers the temporaries into [nat]
    identifiers so inner loops avoid term and string comparisons,
    assigns integer (`w`, `l`) temporaries and pointer (`p`) address
    words to the seven allocatable general registers (`%r10`, `%r11`,
    `%rbx`, `%r12`–`%r15`), checks the assignment with an executable
    validator ([valid_alloc]; CFG trace simulation in RegsProof.v), resolves
    [[phi]] edges by parallel moves without shadow slots, and selects
    scalar and address operations straight into their assigned
    registers.

    Pointer lowers stay in their `lowers[]` frame roots so the
    collector scans every live [[capability]] at every safepoint, and
    temporaries live across any returning call take only callee-saved
    registers (`%rbx`, `%r12`–`%r15`), saved after the stack check and
    restored before every `leave`. *)

From Stdlib Require Import String ZArith List Bool Arith.
From Nanofil Require Import Term Syntax Validate Maps Cfg.
From Backend Require Import Text Asm Order Plan Fuse FrameSlots Abi PlanTerm Layout
  EmitOps EmitInst EmitObject Emit EmitData EmitThunk EmitModule.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Allocatable registers *)

(** The seven general registers available for register homes: two
    caller-saved (`%r10`, `%r11`) and five callee-saved (`%rbx`,
    `%r12`–`%r15`), all disjoint from the emitter's scratch registers
    (`%rax`, `%rcx`, `%rdx`, `%rsi`, `%rdi`, `%r8`, `%r9`). *)
Inductive hreg : Type :=
| HR10
| HR11
| HRbx
| HR12
| HR13
| HR14
| HR15.

(** Equality of [hreg]s. *)
Definition hreg_eqb (a b : hreg) : bool :=
  match a, b with
  | HR10, HR10 | HR11, HR11 | HRbx, HRbx
  | HR12, HR12 | HR13, HR13 | HR14, HR14 | HR15, HR15 => true
  | _, _ => false
  end.

(** Whether [r] is preserved across SysV / Fil-C calls. *)
Definition hreg_callee_saved (r : hreg) : bool :=
  match r with
  | HR10 | HR11 => false
  | HRbx | HR12 | HR13 | HR14 | HR15 => true
  end.

(** The five callee-saved registers, in prologue save order. *)
Definition callee_saved_hregs : list hreg := [HRbx; HR12; HR13; HR14; HR15].

(** The caller-saved registers, tried first for non-call-crossing
    temporaries so callee-saved registers remain free across calls. *)
Definition caller_saved_hregs : list hreg := [HR10; HR11].

(** All seven allocatable registers. *)
Definition all_hregs : list hreg := [HR10; HR11; HRbx; HR12; HR13; HR14; HR15].

(** 64-bit AT&T name of [r]. *)
Definition hreg64 (r : hreg) : string :=
  match r with
  | HR10 => "r10" | HR11 => "r11" | HRbx => "rbx"
  | HR12 => "r12" | HR13 => "r13" | HR14 => "r14" | HR15 => "r15"
  end.

(** 32-bit AT&T name of [r]. *)
Definition hreg32 (r : hreg) : string :=
  match r with
  | HR10 => "r10d" | HR11 => "r11d" | HRbx => "ebx"
  | HR12 => "r12d" | HR13 => "r13d" | HR14 => "r14d" | HR15 => "r15d"
  end.

(** 16-bit AT&T name of [r]. *)
Definition hreg16 (r : hreg) : string :=
  match r with
  | HR10 => "r10w" | HR11 => "r11w" | HRbx => "bx"
  | HR12 => "r12w" | HR13 => "r13w" | HR14 => "r14w" | HR15 => "r15w"
  end.

(** 8-bit AT&T name of [r]. *)
Definition hreg8 (r : hreg) : string :=
  match r with
  | HR10 => "r10b" | HR11 => "r11b" | HRbx => "bl"
  | HR12 => "r12b" | HR13 => "r13b" | HR14 => "r14b" | HR15 => "r15b"
  end.

(** Name of [r] at 32 bits ([half = true]) or 64 bits ([half = false]). *)
Definition hreg_at (r : hreg) (half : bool) : string :=
  if half then hreg32 r else hreg64 r.

(** Name of [r] at store width [w]. *)
Definition hreg_width (r : hreg) (w : width) : option string :=
  match w with
  | Wb => Some (hreg8 r)
  | Wh => Some (hreg16 r)
  | Ww | Ws => Some (hreg32 r)
  | Wl | Wd => Some (hreg64 r)
  | Wp | Wx => None
  end.

(** ## Tail-recursive nat sets and intervals *)

(** Fast [nat] comparisons through [Nat.compare], avoiding Peano
    subtraction in extracted code. *)
Definition nat_eqb (a b : nat) : bool :=
  match Nat.compare a b with Datatypes.Eq => true | _ => false end.

Definition nat_ltb (a b : nat) : bool :=
  match Nat.compare a b with Datatypes.Lt => true | _ => false end.

Definition nat_leb (a b : nat) : bool :=
  match Nat.compare a b with Datatypes.Gt => false | _ => true end.

Definition nat_max (a b : nat) : nat :=
  if nat_ltb a b then b else a.

Definition nat_min (a b : nat) : nat :=
  if nat_ltb a b then a else b.

(** Membership in a sorted [list nat]. *)
Fixpoint nset_mem (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: xs' =>
      match Nat.compare x y with
      | Datatypes.Lt => false
      | Datatypes.Eq => true
      | Datatypes.Gt => nset_mem x xs'
      end
  end.

(** Equality of two sorted [list nat] ordsets. *)
Fixpoint nset_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => if nat_eqb x y then nset_eqb xs' ys' else false
  | _, _ => false
  end.

(** Tail-recursive union accumulator for sorted [list nat]s. *)
Fixpoint nset_union_acc (fuel : nat) (xs ys acc : list nat) : list nat :=
  match xs, ys with
  | [], _ => rev_append acc ys
  | _, [] => rev_append acc xs
  | x :: xs', y :: ys' =>
      match fuel with
      | O => rev_append acc (xs ++ ys)
      | S fuel' =>
          match Nat.compare x y with
          | Datatypes.Lt => nset_union_acc fuel' xs' ys (x :: acc)
          | Datatypes.Eq => nset_union_acc fuel' xs' ys' (x :: acc)
          | Datatypes.Gt => nset_union_acc fuel' xs ys' (y :: acc)
          end
      end
  end.

Definition nset_union (xs ys : list nat) : list nat :=
  nset_union_acc (length xs + length ys) xs ys [].

(** Tail-recursive difference accumulator for sorted [list nat]s. *)
Fixpoint nset_sub_acc (fuel : nat) (xs ys acc : list nat) : list nat :=
  match xs, ys with
  | [], _ => rev' acc
  | _, [] => rev_append acc xs
  | x :: xs', y :: ys' =>
      match fuel with
      | O => rev_append acc xs
      | S fuel' =>
          match Nat.compare x y with
          | Datatypes.Lt => nset_sub_acc fuel' xs' ys (x :: acc)
          | Datatypes.Eq => nset_sub_acc fuel' xs' ys' acc
          | Datatypes.Gt => nset_sub_acc fuel' xs ys' acc
          end
      end
  end.

Definition nset_sub (xs ys : list nat) : list nat :=
  nset_sub_acc (length xs + length ys) xs ys [].

(** Sort and deduplicate a [list nat]. *)
Definition nset_of_list (xs : list nat) : list nat :=
  sort Nat.compare xs.

(** Insert one [nat] into a sorted [list nat]. *)
Definition nset_add (x : nat) (xs : list nat) : list nat :=
  nset_union [x] xs.

(** A closed live interval `[lo, hi]` with `lo <= hi`. *)
Definition ival : Type := (nat * nat)%type.

(** Whether two sorted lists of disjoint closed intervals have no point
    in common. *)
Fixpoint ivals_disjoint_fuel (fuel : nat) (xs ys : list ival) : bool :=
  match xs, ys with
  | [], _ => true
  | _, [] => true
  | (a1, b1) :: xs', (a2, b2) :: ys' =>
      match fuel with
      | O => false
      | S fuel' =>
          if nat_ltb b1 a2 then ivals_disjoint_fuel fuel' xs' ys
          else if nat_ltb b2 a1 then ivals_disjoint_fuel fuel' xs ys'
          else false
      end
  end.

Definition ivals_disjoint (xs ys : list ival) : bool :=
  ivals_disjoint_fuel (length xs + length ys) xs ys.

(** Push interval `iv` onto reversed coalesced accumulator `acc`, where
    `iv` starts no earlier than the head of `acc`. *)
Definition ival_push_acc (iv : ival) (acc : list ival) : list ival :=
  match acc with
  | [] => [iv]
  | (a0, b0) :: acc' =>
      if nat_leb (fst iv) (S b0)
      then (a0, nat_max b0 (snd iv)) :: acc'
      else iv :: acc
  end.

(** Tail-recursive merge and coalescing of two sorted interval lists. *)
Fixpoint ivals_union_acc (fuel : nat) (xs ys acc : list ival) : list ival :=
  match xs, ys with
  | [], [] => rev' acc
  | _, _ =>
      match fuel with
      | O => rev' acc
      | S fuel' =>
          match xs, ys with
          | [], [] => rev' acc
          | [], y :: ys' => ivals_union_acc fuel' [] ys' (ival_push_acc y acc)
          | x :: xs', [] => ivals_union_acc fuel' xs' [] (ival_push_acc x acc)
          | (a1, _) as x :: xs', (a2, _) as y :: ys' =>
              if nat_leb a1 a2
              then ivals_union_acc fuel' xs' ys (ival_push_acc x acc)
              else ivals_union_acc fuel' xs ys' (ival_push_acc y acc)
          end
      end
  end.

Definition ivals_union (xs ys : list ival) : list ival :=
  ivals_union_acc (length xs + length ys) xs ys [].

(** Whether any point in sorted [pts] lies inside sorted intervals [ivs]. *)
Fixpoint ivals_hit_points_fuel (fuel : nat) (ivs : list ival) (pts : list nat) : bool :=
  match ivs, pts with
  | [], _ => false
  | _, [] => false
  | (a, b) :: ivs', p :: pts' =>
      match fuel with
      | O => true
      | S fuel' =>
          if nat_ltb b p then ivals_hit_points_fuel fuel' ivs' pts
          else if nat_ltb p a then ivals_hit_points_fuel fuel' ivs pts'
          else true
      end
  end.

Definition ivals_hit_points (ivs : list ival) (pts : list nat) : bool :=
  ivals_hit_points_fuel (length ivs + length pts) ivs pts.

(** [ZMap] keyed by [nat] via [Z.of_nat]. *)
Definition zmap_find_nat {A : Type} (k : nat) (m : ZMap.t A) : option A :=
  ZMap.find (Z.of_nat k) m.

Definition zmap_add_nat {A : Type} (k : nat) (v : A) (m : ZMap.t A) : ZMap.t A :=
  ZMap.add (Z.of_nat k) v m.

(** ## Plan uses, defs, calls and adjacent elisions *)

Definition is_atomic_read (e : effect) : bool :=
  match e with AtomicRead => true | _ => false end.

(** How an instruction invokes helper or target calls. *)
Inductive rcall : Type :=
| RCallNone
| RCallAfterReads
| RCallDuringReads.

Definition rcall_join (a b : rcall) : rcall :=
  match a, b with
  | RCallDuringReads, _ | _, RCallDuringReads => RCallDuringReads
  | RCallAfterReads, _ | _, RCallAfterReads => RCallAfterReads
  | RCallNone, RCallNone => RCallNone
  end.

(** Temporary reads in a fast-call [word]. *)
Definition word_uses (w : word) : list name :=
  match w with
  | Wf _ (SrcAddr v) | Wf _ (SrcLower v) | Wf _ (SrcVal _ v) => value_temps [v]
  | Wf _ _ => []
  end.

Fixpoint words_uses_acc (ws : list word) (acc : list name) : list name :=
  match ws with
  | [] => rev' acc
  | w :: ws' => words_uses_acc ws' (rev_append (word_uses w) acc)
  end.

(** Temporary reads in a generic [cell]. *)
Definition cell_uses (c : cell) : list name :=
  match c with
  | Cell _ _ s lw =>
      let u1 := match s with CellValue v => value_temps [v] | CellSaved _ => [] end in
      let u2 := match lw with Some (CellValue p) => value_temps [p] | _ => [] end in
      u1 ++ u2
  end.

Fixpoint cells_uses_acc (cs : list cell) (acc : list name) : list name :=
  match cs with
  | [] => rev' acc
  | c :: cs' => cells_uses_acc cs' (rev_append (cell_uses c) acc)
  end.

(** Temporary definitions in call result [channels]. *)
Definition key_def_names (k : key) : list name :=
  match k with
  | KTmp d => [d]
  | _ => []
  end.

Fixpoint keys_defs_acc (ks : list key) (acc : list name) : list name :=
  match ks with
  | [] => rev' acc
  | k :: ks' => keys_defs_acc ks' (rev_append (key_def_names k) acc)
  end.

Fixpoint typed_keys_defs_acc (ks : list (class * key)) (acc : list name) : list name :=
  match ks with
  | [] => rev' acc
  | (_, k) :: ks' => typed_keys_defs_acc ks' (rev_append (key_def_names k) acc)
  end.

Definition channels_defs (c : channels) : list name :=
  match c with
  | ChSlots ks => keys_defs_acc ks []
  | ChFloat _ d => [d]
  | ChTyped ks => typed_keys_defs_acc ks []
  end.

(** Uses, definitions and call kind of one [action]. *)
Definition action_uses (a : action) : list name :=
  match a with
  | AInvoke _ _ ws => words_uses_acc ws []
  | ADispatch p _ _ ws _ _ cells _ _ =>
      value_temps [p] ++ words_uses_acc ws [] ++ cells_uses_acc cells []
  | ASnapshotCursor _ _ => [va_snapshot]
  | AConsumeVa _ p _ _ => value_temps [p]
  | _ => []
  end.

Definition action_defs (a : action) : list name :=
  match a with
  | AResult _ c => channels_defs c
  | ADispatch _ _ _ _ c _ _ _ _ => channels_defs c
  | AGetter _ d | ASnapshotCursor _ d | AConsumeVa _ _ _ d => [d]
  | _ => []
  end.

Definition action_call (a : action) : rcall :=
  match a with
  | ADispatch _ _ _ _ _ _ _ _ _ => RCallDuringReads
  | AInvoke _ _ _ | AGetter _ _ | AConsumeVa _ _ _ _ => RCallAfterReads
  | _ => RCallNone
  end.

Fixpoint actions_uses_acc (acts : list action) (acc : list name) : list name :=
  match acts with
  | [] => rev' acc
  | a :: acts' => actions_uses_acc acts' (rev_append (action_uses a) acc)
  end.

Fixpoint actions_defs_acc (acts : list action) (acc : list name) : list name :=
  match acts with
  | [] => rev' acc
  | a :: acts' => actions_defs_acc acts' (rev_append (action_defs a) acc)
  end.

Fixpoint actions_call (acts : list action) (acc : rcall) : rcall :=
  match acts with
  | [] => acc
  | a :: acts' => actions_call acts' (rcall_join acc (action_call a))
  end.

Definition access_call (a : access) : rcall :=
  match a with
  | AStorePointer _ _ _ _ => RCallDuringReads
  | ALoadPointer _ _ es _ =>
      if existsb is_atomic_read es then RCallAfterReads else RCallNone
  | _ => RCallNone
  end.

Definition pinst_uses (pi : pinst) : list name :=
  match pi with
  | PInst fi => finst_uses fi
  | PAbi acts => actions_uses_acc acts []
  end.

Definition pinst_defs (pi : pinst) : list name :=
  match pi with
  | PInst fi => map fst (finst_defs fi)
  | PAbi acts => actions_defs_acc acts []
  end.

Definition pinst_call (pi : pinst) : rcall :=
  match pi with
  | PInst (FPlain (Let _ _ (Alloc _) _)) => RCallAfterReads
  | PInst (FFused _ a) | PInst (FReused a) => access_call a
  | PInst (FCall _ _ _) => RCallDuringReads
  | PInst _ => RCallNone
  | PAbi acts => actions_call acts RCallNone
  end.

Definition pjump_uses (j : pjump) : list name :=
  match j with
  | PJump jj => jump_uses jj
  | PReturnValue _ v _ => value_temps [v]
  | PReturnBuffer ws => words_uses_acc ws []
  | PReturnTyped _ vs | PReturnRegisters vs => value_temps vs
  | PReturnVoid _ => []
  end.

Definition pjump_targets (j : pjump) : list target :=
  match j with
  | PJump jj => jump_targets jj
  | _ => []
  end.

(** Count every read of a temporary across all blocks of a plan. *)
Definition bump_name_count (m : nmap Z) (n : name) : nmap Z :=
  nm_add n (match nm_find n m with Some c => c + 1 | None => 1 end) m.

Fixpoint bump_names_count (ns : list name) (m : nmap Z) : nmap Z :=
  match ns with
  | [] => m
  | n :: ns' => bump_names_count ns' (bump_name_count m n)
  end.

Fixpoint count_phi_pairs (ps : list (name * value)) (m : nmap Z) : nmap Z :=
  match ps with
  | [] => m
  | (_, Tmp n) :: ps' => count_phi_pairs ps' (bump_name_count m n)
  | (_, _) :: ps' => count_phi_pairs ps' m
  end.

Fixpoint count_phis_reads (phis : list phi) (m : nmap Z) : nmap Z :=
  match phis with
  | [] => m
  | Phi _ _ ps :: phis' => count_phis_reads phis' (count_phi_pairs ps m)
  end.

Fixpoint count_pinsts_reads (pis : list pinst) (m : nmap Z) : nmap Z :=
  match pis with
  | [] => m
  | pi :: pis' => count_pinsts_reads pis' (bump_names_count (pinst_uses pi) m)
  end.

Fixpoint plan_read_counts_acc (bs : list pblock) (m : nmap Z) : nmap Z :=
  match bs with
  | [] => m
  | b :: bs' =>
      let m1 := count_phis_reads (pb_phis b) m in
      let m2 := count_pinsts_reads (pb_insts b) m1 in
      let m3 := bump_names_count (pjump_uses (pb_jump b)) m2 in
      plan_read_counts_acc bs' m3
  end.

Definition name_reads (n : name) (reads : nmap Z) : Z :=
  match nm_find n reads with Some c => c | None => 0 end.

(** Expanded block instructions and jumps after recognizing adjacent
    single-use `Flight -> FFused`, `Cmp -> JBranch`, and integer
    `Let -> Cmp -> JBranch` pairs. *)
Inductive einst : Type :=
| EPlain (idx : Z) (pi : pinst)
| EFlightFused (idx1 idx2 : Z) (d : name) (o : op) (args : list flight_arg)
               (lw : flight_lower) (ck : check_kind) (a : access).

Inductive ejump : Type :=
| EJumpPlain (j : pjump)
| EJumpCmp (c : cond) (ck : class) (x y : value) (t f : target)
| EJumpLetCmp (d1 : name) (k1 : class) (o1 : op) (args1 : list value)
              (c : cond) (ck : class) (y : value) (t f : target).

Record eblock : Type := mkEBlock {
  eb_label : name;
  eb_phis : list phi;
  eb_insts : list einst;
  eb_jump : ejump
}.

(** Non-place uses of an [access] (its stored value, if any). *)
Definition access_value_uses (a : access) : list name :=
  match a with
  | AStore _ _ v _ | AStorePointer _ v _ _ => value_temps [v]
  | _ => []
  end.

Definition flight_uses (args : list flight_arg) (lw : flight_lower) : list name :=
  value_temps (map flight_arg_value args
               ++ match lw with LowerOf p => [p] | LowerNone => [] end).

Definition einst_uses (ei : einst) : list name :=
  match ei with
  | EPlain _ pi => pinst_uses pi
  | EFlightFused _ _ _ _ args lw _ a => flight_uses args lw ++ access_value_uses a
  end.

Definition einst_defs (ei : einst) : list name :=
  match ei with
  | EPlain _ pi => pinst_defs pi
  | EFlightFused _ _ _ _ _ _ _ a => map fst (access_defs a)
  end.

Definition einst_call (ei : einst) : rcall :=
  match ei with
  | EPlain _ pi => pinst_call pi
  | EFlightFused _ _ _ _ _ _ _ a => access_call a
  end.

Definition ejump_uses (ej : ejump) : list name :=
  match ej with
  | EJumpPlain j => pjump_uses j
  | EJumpCmp _ _ x y _ _ => value_temps [x; y]
  | EJumpLetCmp _ _ _ args1 _ _ y _ _ => value_temps args1 ++ value_temps [y]
  end.

Definition ejump_targets (ej : ejump) : list target :=
  match ej with
  | EJumpPlain j => pjump_targets j
  | EJumpCmp _ _ _ _ t f | EJumpLetCmp _ _ _ _ _ _ _ t f => [t; f]
  end.

(** Whether [o] at integer class [k] computes directly into `%rax`
    without calls or float state. *)
Definition simple_int_op (o : op) (k : class) : bool :=
  match k with
  | W | L =>
      if x87_op o k || float_compute o k then false
      else match o with
           | Add | Sub | Mul | And | Or | Xor | Shl | Shr | Sar
           | Neg | Copy | Ptoi | Ext _ => true
           | _ => false
           end
  | _ => false
  end.

Definition let_cmp_class_ok (k1 ck : class) : bool :=
  match k1, ck with
  | W, W | L, L | L, W => true
  | _, _ => false
  end.

(** Try to fuse a single-use `Flight` with an immediately following
    non-calling heap `FFused` access at that pointer. *)
Definition try_fuse_flight (reads : nmap Z) (i1 : Z) (pi1 : pinst)
                           (i2 : Z) (pi2 : pinst) : option einst :=
  match pi1, pi2 with
  | PInst (FPlain (Flight d o args lw)),
    PInst (FFused (Check 0 size r al) a) =>
      let same_ptr :=
        match access_place a with
        | AtValue (Tmp d') => name_eqb d d'
        | _ => false
        end in
      let no_call :=
        match access_call a with RCallNone => true | _ => false end in
      if same_ptr && no_call && (name_reads d reads =? 1)
         && negb (name_eqb d va_snapshot)
      then Some (EFlightFused i1 i2 d o args lw (mkKind size (rights_write r) al) a)
      else None
  | _, _ => None
  end.

Fixpoint build_einsts_rev (reads : nmap Z) (idx : Z) (pis : list pinst)
                          (acc : list einst) : list einst :=
  match pis with
  | [] => acc
  | pi1 :: rest =>
      match rest with
      | pi2 :: rest' =>
          match try_fuse_flight reads idx pi1 (idx + 1) pi2 with
          | Some ef => build_einsts_rev reads (idx + 2) rest' (ef :: acc)
          | None => build_einsts_rev reads (idx + 1) rest (EPlain idx pi1 :: acc)
          end
      | [] => EPlain idx pi1 :: acc
      end
  end.

Definition build_eblock (reads : nmap Z) (b : pblock) : eblock :=
  let rev_is := build_einsts_rev reads 0 (pb_insts b) [] in
  match pb_jump b, rev_is with
  | PJump (JBranch (Tmp dc) t f),
    EPlain _ (PInst (FPlain (Let dc' W (Cmp c ck) [x; y]))) :: rev_rest =>
      let ok_cmp :=
        name_eqb dc dc'
        && match ck with W | L => true | _ => false end
        && (name_reads dc reads =? 1)
        && negb (name_eqb dc va_snapshot) in
      if ok_cmp then
        match x, rev_rest with
        | Tmp d1, EPlain _ (PInst (FPlain (Let d1' k1 o1 args1))) :: rev_rest2 =>
            if name_eqb d1 d1'
               && let_cmp_class_ok k1 ck
               && simple_int_op o1 k1
               && (name_reads d1 reads =? 1)
               && negb (name_eqb d1 va_snapshot)
            then mkEBlock (pb_label b) (pb_phis b) (rev' rev_rest2)
                          (EJumpLetCmp d1 k1 o1 args1 c ck y t f)
            else mkEBlock (pb_label b) (pb_phis b) (rev' rev_rest)
                          (EJumpCmp c ck x y t f)
        | _, _ =>
            mkEBlock (pb_label b) (pb_phis b) (rev' rev_rest)
                     (EJumpCmp c ck x y t f)
        end
      else mkEBlock (pb_label b) (pb_phis b) (rev' rev_is) (EJumpPlain (pb_jump b))
  | _, _ =>
      mkEBlock (pb_label b) (pb_phis b) (rev' rev_is) (EJumpPlain (pb_jump b))
  end.

Fixpoint build_eblocks_acc (reads : nmap Z) (bs : list pblock) (acc : list eblock)
  : list eblock :=
  match bs with
  | [] => rev' acc
  | b :: bs' => build_eblocks_acc reads bs' (build_eblock reads b :: acc)
  end.

(** ## Numbered CFG representation *)

Record rinst : Type := mkRInst {
  ri_uses : list nat;
  ri_defs : list nat;
  ri_call : rcall
}.

Record rblock : Type := mkRBlock {
  rb_idx : nat;
  rb_succs : list (nat * bool);
  rb_phis : list (nat * list (nat * option nat));
  rb_insts : list rinst;
  rb_jump_uses : list nat
}.

(** Class table and numbering of temporaries defined in [f]. *)
Definition record_temp_def (st : nmap nat * ZMap.t class * list name * nat)
                           (d : name) (k : class)
  : nmap nat * ZMap.t class * list name * nat :=
  let '(tmap, cmap, rev_names, next) := st in
  if nm_mem d tmap then st
  else (nm_add d next tmap, zmap_add_nat next k cmap, d :: rev_names, S next).

Fixpoint number_params (ps : list (class * name))
                       (st : nmap nat * ZMap.t class * list name * nat)
  : nmap nat * ZMap.t class * list name * nat :=
  match ps with
  | [] => st
  | (k, d) :: ps' => number_params ps' (record_temp_def st d k)
  end.

Fixpoint number_phis (phis : list phi)
                     (st : nmap nat * ZMap.t class * list name * nat)
  : nmap nat * ZMap.t class * list name * nat :=
  match phis with
  | [] => st
  | Phi d k _ :: phis' => number_phis phis' (record_temp_def st d k)
  end.

Fixpoint number_inst_defs (ds : list (name * class))
                          (st : nmap nat * ZMap.t class * list name * nat)
  : nmap nat * ZMap.t class * list name * nat :=
  match ds with
  | [] => st
  | (d, k) :: ds' => number_inst_defs ds' (record_temp_def st d k)
  end.

Fixpoint number_block_insts (is : list inst)
                            (st : nmap nat * ZMap.t class * list name * nat)
  : nmap nat * ZMap.t class * list name * nat :=
  match is with
  | [] => st
  | i :: is' => number_block_insts is' (number_inst_defs (inst_temp_defs i) st)
  end.

Fixpoint number_func_blocks (bs : list block)
                            (st : nmap nat * ZMap.t class * list name * nat)
  : nmap nat * ZMap.t class * list name * nat :=
  match bs with
  | [] => st
  | b :: bs' =>
      let st1 := number_phis (b_phis b) st in
      let st2 := number_block_insts (b_insts b) st1 in
      number_func_blocks bs' st2
  end.

Fixpoint number_eblocks_labels (ebs : list eblock) (idx : nat) (m : nmap nat) : nmap nat :=
  match ebs with
  | [] => m
  | eb :: ebs' =>
      let m' := if nm_mem (eb_label eb) m then m else nm_add (eb_label eb) idx m in
      number_eblocks_labels ebs' (S idx) m'
  end.

Fixpoint names_to_tids_acc (tmap : nmap nat) (ns : list name) (acc : list nat) : list nat :=
  match ns with
  | [] => rev' acc
  | n :: ns' =>
      match nm_find n tmap with
      | Some id => names_to_tids_acc tmap ns' (id :: acc)
      | None => names_to_tids_acc tmap ns' acc
      end
  end.

Definition names_to_tids (tmap : nmap nat) (ns : list name) : list nat :=
  names_to_tids_acc tmap ns [].

Fixpoint targets_to_succs_acc (bmap : nmap nat) (ts : list target)
                              (acc : list (nat * bool)) : list (nat * bool) :=
  match ts with
  | [] => rev' acc
  | t :: ts' =>
      let poll := match t with Poll _ => true | To _ => false end in
      match nm_find (edge_label t) bmap with
      | Some bi => targets_to_succs_acc bmap ts' ((bi, poll) :: acc)
      | None => targets_to_succs_acc bmap ts' acc
      end
  end.

Fixpoint phi_pairs_to_r_acc (tmap bmap : nmap nat) (ps : list (name * value))
                            (acc : list (nat * option nat)) : list (nat * option nat) :=
  match ps with
  | [] => rev' acc
  | (lbl, v) :: ps' =>
      match nm_find lbl bmap with
      | Some bi =>
          let sv := match v with Tmp n => nm_find n tmap | _ => None end in
          phi_pairs_to_r_acc tmap bmap ps' ((bi, sv) :: acc)
      | None => phi_pairs_to_r_acc tmap bmap ps' acc
      end
  end.

Fixpoint phis_to_r_acc (tmap bmap : nmap nat) (phis : list phi)
                       (acc : list (nat * list (nat * option nat)))
  : list (nat * list (nat * option nat)) :=
  match phis with
  | [] => rev' acc
  | Phi d _ ps :: phis' =>
      match nm_find d tmap with
      | Some tid =>
          phis_to_r_acc tmap bmap phis' ((tid, phi_pairs_to_r_acc tmap bmap ps []) :: acc)
      | None => phis_to_r_acc tmap bmap phis' acc
      end
  end.

Fixpoint einsts_to_r_acc (tmap : nmap nat) (eis : list einst) (acc : list rinst) : list rinst :=
  match eis with
  | [] => rev' acc
  | ei :: eis' =>
      let ri := mkRInst (names_to_tids tmap (einst_uses ei))
                        (names_to_tids tmap (einst_defs ei))
                        (einst_call ei) in
      einsts_to_r_acc tmap eis' (ri :: acc)
  end.

Fixpoint eblocks_to_r_acc (tmap bmap : nmap nat) (idx : nat) (ebs : list eblock)
                          (acc : list rblock) : list rblock :=
  match ebs with
  | [] => rev' acc
  | eb :: ebs' =>
      let rb := mkRBlock idx
                  (targets_to_succs_acc bmap (ejump_targets (eb_jump eb)) [])
                  (phis_to_r_acc tmap bmap (eb_phis eb) [])
                  (einsts_to_r_acc tmap (eb_insts eb) [])
                  (names_to_tids tmap (ejump_uses (eb_jump eb))) in
      eblocks_to_r_acc tmap bmap (S idx) ebs' (rb :: acc)
  end.

(** ## Liveness over numbered blocks *)

Definition nset_at (k : nat) (m : ZMap.t (list nat)) : list nat :=
  match zmap_find_nat k m with Some s => s | None => [] end.

(** Keep only temporaries belonging to [keep] (`None` keeps all). *)
Fixpoint filter_keep_acc (keep : option (ZMap.t unit)) (xs acc : list nat) : list nat :=
  match xs with
  | [] => rev' acc
  | x :: xs' =>
      let ok := match keep with
                | None => true
                | Some km => match zmap_find_nat x km with Some _ => true | None => false end
                end in
      if ok then filter_keep_acc keep xs' (x :: acc)
      else filter_keep_acc keep xs' acc
  end.

(** Phi sources read on the edge `pred_bi -> rb`. *)
Fixpoint lookup_phi_edge_src (pred_bi : nat) (ps : list (nat * option nat)) : option nat :=
  match ps with
  | [] => None
  | (bi, sv) :: ps' =>
      if nat_eqb bi pred_bi then sv else lookup_phi_edge_src pred_bi ps'
  end.

Fixpoint rblock_phi_edge_uses_acc (keep : option (ZMap.t unit)) (pred_bi : nat)
                                  (phis : list (nat * list (nat * option nat)))
                                  (acc : list nat) : list nat :=
  match phis with
  | [] => nset_of_list acc
  | (_, ps) :: phis' =>
      match lookup_phi_edge_src pred_bi ps with
      | Some tid =>
          let kept := filter_keep_acc keep [tid] [] in
          rblock_phi_edge_uses_acc keep pred_bi phis' (rev_append kept acc)
      | None => rblock_phi_edge_uses_acc keep pred_bi phis' acc
      end
  end.

Fixpoint rblock_phi_defs_acc (keep : option (ZMap.t unit))
                             (phis : list (nat * list (nat * option nat)))
                             (acc : list nat) : list nat :=
  match phis with
  | [] => nset_of_list acc
  | (d, _) :: phis' =>
      let kept := filter_keep_acc keep [d] [] in
      rblock_phi_defs_acc keep phis' (rev_append kept acc)
  end.

(** Gen and Kill of one [rblock]. *)
Fixpoint gk_uses_step (uses : list nat) (defs : ZMap.t unit) (gen : list nat) : list nat :=
  match uses with
  | [] => gen
  | u :: uses' =>
      match zmap_find_nat u defs with
      | Some _ => gk_uses_step uses' defs gen
      | None => gk_uses_step uses' defs (u :: gen)
      end
  end.

Fixpoint gk_defs_step (ds : list nat) (defs : ZMap.t unit) (kill : list nat)
  : ZMap.t unit * list nat :=
  match ds with
  | [] => (defs, kill)
  | d :: ds' => gk_defs_step ds' (zmap_add_nat d tt defs) (d :: kill)
  end.

Fixpoint gk_insts_step (keep : option (ZMap.t unit)) (ris : list rinst)
                       (defs : ZMap.t unit) (gen kill : list nat)
  : ZMap.t unit * list nat * list nat :=
  match ris with
  | [] => (defs, gen, kill)
  | ri :: ris' =>
      let us := filter_keep_acc keep (ri_uses ri) [] in
      let ds := filter_keep_acc keep (ri_defs ri) [] in
      let gen1 := gk_uses_step us defs gen in
      let '(defs1, kill1) := gk_defs_step ds defs kill in
      gk_insts_step keep ris' defs1 gen1 kill1
  end.

Definition rblock_gen_kill (keep : option (ZMap.t unit)) (rb : rblock)
  : list nat * list nat :=
  let pdefs := rblock_phi_defs_acc keep (rb_phis rb) [] in
  let '(defs0, kill0) := gk_defs_step pdefs (ZMap.empty unit) [] in
  let '(defs1, gen1, kill1) := gk_insts_step keep (rb_insts rb) defs0 [] kill0 in
  let juses := filter_keep_acc keep (rb_jump_uses rb) [] in
  let gen2 := gk_uses_step juses defs1 gen1 in
  (nset_of_list gen2, nset_of_list kill1).

Fixpoint build_gk_map (keep : option (ZMap.t unit)) (rbs : list rblock)
                      (m : ZMap.t (list nat * list nat)) : ZMap.t (list nat * list nat) :=
  match rbs with
  | [] => m
  | rb :: rbs' =>
      build_gk_map keep rbs' (zmap_add_nat (rb_idx rb) (rblock_gen_kill keep rb) m)
  end.

Fixpoint build_rb_map (rbs : list rblock) (m : ZMap.t rblock) : ZMap.t rblock :=
  match rbs with
  | [] => m
  | rb :: rbs' => build_rb_map rbs' (zmap_add_nat (rb_idx rb) rb m)
  end.

(** LiveOut and LiveAcross of block `bi` given `live_in`. *)
Fixpoint succs_live_out (keep : option (ZMap.t unit)) (rbm : ZMap.t rblock)
                        (live_in : ZMap.t (list nat)) (bi : nat)
                        (succs : list (nat * bool)) (out across : list nat)
  : list nat * list nat :=
  match succs with
  | [] => (out, across)
  | (si, _) :: succs' =>
      let lin := nset_at si live_in in
      let across1 := nset_union across lin in
      let euses :=
        match zmap_find_nat si rbm with
        | Some srb => rblock_phi_edge_uses_acc keep bi (rb_phis srb) []
        | None => []
        end in
      succs_live_out keep rbm live_in bi succs' (nset_union (nset_union out lin) euses) across1
  end.

Fixpoint rlive_round_blocks (keep : option (ZMap.t unit)) (rbm : ZMap.t rblock)
                            (gkm : ZMap.t (list nat * list nat))
                            (rev_rbs : list rblock)
                            (live_in : ZMap.t (list nat)) (changed : bool)
  : ZMap.t (list nat) * bool :=
  match rev_rbs with
  | [] => (live_in, changed)
  | rb :: rest =>
      let bi := rb_idx rb in
      let '(out, _) := succs_live_out keep rbm live_in bi (rb_succs rb) [] [] in
      match zmap_find_nat bi gkm with
      | Some (gen, kill) =>
          let new_in := nset_union gen (nset_sub out kill) in
          if nset_eqb (nset_at bi live_in) new_in
          then rlive_round_blocks keep rbm gkm rest live_in changed
          else rlive_round_blocks keep rbm gkm rest (zmap_add_nat bi new_in live_in) true
      | None => rlive_round_blocks keep rbm gkm rest live_in changed
      end
  end.

Fixpoint rlive_rounds (fuel : nat) (keep : option (ZMap.t unit)) (rbm : ZMap.t rblock)
                      (gkm : ZMap.t (list nat * list nat)) (rev_rbs : list rblock)
                      (live_in : ZMap.t (list nat)) : ZMap.t (list nat) * bool :=
  match fuel with
  | O => rlive_round_blocks keep rbm gkm rev_rbs live_in false
  | S fuel' =>
      let r := rlive_rounds fuel' keep rbm gkm rev_rbs live_in in
      if snd r then rlive_rounds fuel' keep rbm gkm rev_rbs (fst r) else r
  end.

Fixpoint build_out_across_maps (keep : option (ZMap.t unit)) (rbm : ZMap.t rblock)
                               (live_in : ZMap.t (list nat)) (rbs : list rblock)
                               (outs across : ZMap.t (list nat))
  : ZMap.t (list nat) * ZMap.t (list nat) :=
  match rbs with
  | [] => (outs, across)
  | rb :: rbs' =>
      let bi := rb_idx rb in
      let '(o, a) := succs_live_out keep rbm live_in bi (rb_succs rb) [] [] in
      build_out_across_maps keep rbm live_in rbs'
        (zmap_add_nat bi o outs) (zmap_add_nat bi a across)
  end.

(** Compute `(live_in, live_out, live_across)` over [rbs]. *)
Definition rblock_liveness (keep : option (ZMap.t unit)) (rbs : list rblock)
  : option (ZMap.t (list nat) * ZMap.t (list nat) * ZMap.t (list nat)) :=
  let rbm := build_rb_map rbs (ZMap.empty rblock) in
  let gkm := build_gk_map keep rbs (ZMap.empty (list nat * list nat)) in
  let rev_rbs := rev' rbs in
  let '(live_in, still_changing) := rlive_rounds 40 keep rbm gkm rev_rbs (ZMap.empty (list nat)) in
  if still_changing then None
  else
    let '(outs, across) :=
      build_out_across_maps keep rbm live_in rbs (ZMap.empty (list nat)) (ZMap.empty (list nat)) in
    Some (live_in, outs, across).

(** ## Executable allocation validator *)

(** Check that no two temporaries in [ts] are assigned the same [hreg]
    in [rm]. *)
Fixpoint hreg_in_list (r : hreg) (rs : list hreg) : bool :=
  match rs with
  | [] => false
  | r' :: rs' => if hreg_eqb r r' then true else hreg_in_list r rs'
  end.

Fixpoint no_dup_hregs_acc (rm : ZMap.t hreg) (ts : list nat) (seen : list hreg) : bool :=
  match ts with
  | [] => true
  | t :: ts' =>
      match zmap_find_nat t rm with
      | None => no_dup_hregs_acc rm ts' seen
      | Some r =>
          if hreg_in_list r seen then false
          else no_dup_hregs_acc rm ts' (r :: seen)
      end
  end.

Definition no_dup_hregs (rm : ZMap.t hreg) (ts : list nat) : bool :=
  no_dup_hregs_acc rm ts [].

(** Check that every mapped temporary in [ts] holds a callee-saved
    register. *)
Fixpoint all_callee_saved (rm : ZMap.t hreg) (ts : list nat) : bool :=
  match ts with
  | [] => true
  | t :: ts' =>
      match zmap_find_nat t rm with
      | None => all_callee_saved rm ts'
      | Some r => if hreg_callee_saved r then all_callee_saved rm ts' else false
      end
  end.

(** Backward check over the reversed instructions of one [rblock]. *)
Fixpoint check_rinsts_rev (rm : ZMap.t hreg) (keep : option (ZMap.t unit))
                          (rev_ris : list rinst) (live : list nat) : option (list nat) :=
  match rev_ris with
  | [] => Some live
  | ri :: rest =>
      let ds := nset_of_list (filter_keep_acc keep (ri_defs ri) []) in
      let us := nset_of_list (filter_keep_acc keep (ri_uses ri) []) in
      if negb (no_dup_hregs rm (nset_union live ds)) then None
      else
        let live_mid := nset_sub live ds in
        let call_ok1 :=
          match ri_call ri with
          | RCallAfterReads => all_callee_saved rm live_mid
          | _ => true
          end in
        if negb call_ok1 then None
        else
          let live_before := nset_union live_mid us in
          let call_ok2 :=
            match ri_call ri with
            | RCallDuringReads => all_callee_saved rm live_before
            | _ => true
            end in
          if negb (call_ok2 && no_dup_hregs rm live_before) then None
          else check_rinsts_rev rm keep rest live_before
  end.

Fixpoint check_succs_polls (rm : ZMap.t hreg) (keep : option (ZMap.t unit))
                           (rbm : ZMap.t rblock) (live_in : ZMap.t (list nat))
                           (succs : list (nat * bool)) : bool :=
  match succs with
  | [] => true
  | (si, is_poll) :: succs' =>
      let lin := nset_at si live_in in
      let pdefs :=
        match zmap_find_nat si rbm with
        | Some srb => rblock_phi_defs_acc keep (rb_phis srb) []
        | None => []
        end in
      let at_header := nset_union lin pdefs in
      let ok := no_dup_hregs rm at_header
                && (if is_poll then all_callee_saved rm at_header else true) in
      if ok then check_succs_polls rm keep rbm live_in succs' else false
  end.

Fixpoint check_rblocks (rm : ZMap.t hreg) (keep : option (ZMap.t unit))
                       (rbm : ZMap.t rblock)
                       (live_in live_out : ZMap.t (list nat))
                       (rbs : list rblock) : bool :=
  match rbs with
  | [] => true
  | rb :: rbs' =>
      let bi := rb_idx rb in
      let lout := nset_at bi live_out in
      let juses := nset_of_list (filter_keep_acc keep (rb_jump_uses rb) []) in
      let live_end := nset_union lout juses in
      if negb (no_dup_hregs rm lout && no_dup_hregs rm live_end
               && check_succs_polls rm keep rbm live_in (rb_succs rb))
      then false
      else
        match check_rinsts_rev rm keep (rev' (rb_insts rb)) live_end with
        | None => false
        | Some live_after_phis =>
            let pdefs := rblock_phi_defs_acc keep (rb_phis rb) [] in
            if no_dup_hregs rm (nset_union live_after_phis pdefs)
            then check_rblocks rm keep rbm live_in live_out rbs'
            else false
        end
  end.

Fixpoint rm_domain_acc (els : list (Z * hreg)) (m : ZMap.t unit) : ZMap.t unit :=
  match els with
  | [] => m
  | (k, _) :: els' => rm_domain_acc els' (ZMap.add k tt m)
  end.

Fixpoint classes_eligible (els : list (Z * hreg)) (cmap : ZMap.t class) : bool :=
  match els with
  | [] => true
  | (k, _) :: els' =>
      match ZMap.find k cmap with
      | Some (W | L | P) => classes_eligible els' cmap
      | _ => false
      end
  end.

(** Linear-time check that [rm] assigns only `w`, `l` or `p`-address
    temporaries, has no live register collision at any instruction,
    jump, phi header or entry, and assigns only callee-saved registers
    across calls and poll edges. *)
Definition valid_alloc (cmap : ZMap.t class) (param_tids : list nat)
                       (rbs : list rblock) (rm : ZMap.t hreg) : bool :=
  let els := ZMap.elements rm in
  match els with
  | [] => true
  | _ =>
      if negb (classes_eligible els cmap) then false
      else
        let dom := Some (rm_domain_acc els (ZMap.empty unit)) in
        match rblock_liveness dom rbs with
        | None => false
        | Some (live_in, live_out, _) =>
            let rbm := build_rb_map rbs (ZMap.empty rblock) in
            let ps := nset_of_list (filter_keep_acc dom param_tids []) in
            let entry_ok :=
              match rbs with
              | [] => true
              | rb0 :: _ =>
                  let lin0 := nset_at (rb_idx rb0) live_in in
                  match nset_sub lin0 ps with
                  | [] => no_dup_hregs rm ps
                  | _ => false
                  end
              end in
            entry_ok && check_rblocks rm dom rbm live_in live_out rbs
        end
  end.

(** ## Loop depths, weights, exact intervals and priority coloring *)

(** Natural loop spans `[sj, max_bi]`, one per loop header `sj` with a
    backward edge `sj <= bi`, so multiple continue edges to one header
    count as one loop rather than nested loops. *)
Fixpoint rblock_backedges_map (bi : nat) (succs : list (nat * bool))
                              (m : ZMap.t nat) : ZMap.t nat :=
  match succs with
  | [] => m
  | (sj, _) :: succs' =>
      if nat_leb sj bi then
        let hi := match zmap_find_nat sj m with Some h0 => nat_max h0 bi | None => bi end in
        rblock_backedges_map bi succs' (zmap_add_nat sj hi m)
      else rblock_backedges_map bi succs' m
  end.

Fixpoint collect_backedges_map (rbs : list rblock) (m : ZMap.t nat) : ZMap.t nat :=
  match rbs with
  | [] => m
  | rb :: rbs' =>
      collect_backedges_map rbs' (rblock_backedges_map (rb_idx rb) (rb_succs rb) m)
  end.

Fixpoint loop_map_to_spans (els : list (Z * nat)) (acc : list (nat * nat))
  : list (nat * nat) :=
  match els with
  | [] => acc
  | (kz, hi) :: els' => loop_map_to_spans els' ((Z.to_nat kz, hi) :: acc)
  end.

Definition collect_backedges (rbs : list rblock) : list (nat * nat) :=
  loop_map_to_spans (ZMap.elements (collect_backedges_map rbs (ZMap.empty nat))) [].

Fixpoint count_spanning_loops (bi : nat) (loops : list (nat * nat)) (cnt : nat) : nat :=
  match loops with
  | [] => cnt
  | (lo, hi) :: loops' =>
      if nat_leb lo bi && nat_leb bi hi
      then count_spanning_loops bi loops' (S cnt)
      else count_spanning_loops bi loops' cnt
  end.

Definition depth_weight (d : nat) : Z :=
  match d with
  | O => 1
  | S O => 4
  | S (S O) => 16
  | S (S (S O)) => 64
  | S (S (S (S O))) => 256
  | _ => 1024
  end.

Fixpoint build_block_weights (rbs : list rblock) (loops : list (nat * nat))
                             (m : ZMap.t Z) : ZMap.t Z :=
  match rbs with
  | [] => m
  | rb :: rbs' =>
      let w := depth_weight (count_spanning_loops (rb_idx rb) loops O) in
      build_block_weights rbs' loops (zmap_add_nat (rb_idx rb) w m)
  end.

Definition add_weight (t : nat) (w : Z) (wm : ZMap.t Z) : ZMap.t Z :=
  let prev := match zmap_find_nat t wm with Some v => v | None => 0 end in
  zmap_add_nat t (prev + w) wm.

Fixpoint add_weights_list (ts : list nat) (w : Z) (wm : ZMap.t Z) : ZMap.t Z :=
  match ts with
  | [] => wm
  | t :: ts' => add_weights_list ts' w (add_weight t w wm)
  end.

Fixpoint add_weights_phi_pairs (ps : list (nat * option nat)) (bwm : ZMap.t Z)
                               (wm : ZMap.t Z) : ZMap.t Z :=
  match ps with
  | [] => wm
  | (pbi, Some stid) :: ps' =>
      let pw := match zmap_find_nat pbi bwm with Some w => w | None => 1 end in
      add_weights_phi_pairs ps' bwm (add_weight stid pw wm)
  | (_, None) :: ps' => add_weights_phi_pairs ps' bwm wm
  end.

Fixpoint add_weights_phis (phis : list (nat * list (nat * option nat)))
                          (w : Z) (bwm : ZMap.t Z) (wm : ZMap.t Z) : ZMap.t Z :=
  match phis with
  | [] => wm
  | (d, ps) :: phis' =>
      add_weights_phis phis' w bwm (add_weights_phi_pairs ps bwm (add_weight d w wm))
  end.

Fixpoint add_weights_rinsts (ris : list rinst) (w : Z) (wm : ZMap.t Z) : ZMap.t Z :=
  match ris with
  | [] => wm
  | ri :: ris' =>
      let wm1 := add_weights_list (ri_uses ri) w wm in
      let wm2 := add_weights_list (ri_defs ri) w wm1 in
      add_weights_rinsts ris' w wm2
  end.

Fixpoint compute_temp_weights (rbs : list rblock) (bwm : ZMap.t Z) (wm : ZMap.t Z)
  : ZMap.t Z :=
  match rbs with
  | [] => wm
  | rb :: rbs' =>
      let w := match zmap_find_nat (rb_idx rb) bwm with Some v => v | None => 1 end in
      let wm1 := add_weights_phis (rb_phis rb) w bwm wm in
      let wm2 := add_weights_rinsts (rb_insts rb) w wm1 in
      let wm3 := add_weights_list (rb_jump_uses rb) w wm2 in
      compute_temp_weights rbs' bwm wm3
  end.

(** Phi partner edges so loop induction variables coalesce with their
    step temporaries. *)
Definition add_partner (a b : nat) (pm : ZMap.t (list nat)) : ZMap.t (list nat) :=
  if nat_eqb a b then pm
  else zmap_add_nat a (nset_add b (nset_at a pm)) pm.

Fixpoint record_phi_pair_partners (d : nat) (ps : list (nat * option nat))
                                  (pm : ZMap.t (list nat)) : ZMap.t (list nat) :=
  match ps with
  | [] => pm
  | (_, Some s) :: ps' =>
      record_phi_pair_partners d ps' (add_partner s d (add_partner d s pm))
  | (_, None) :: ps' => record_phi_pair_partners d ps' pm
  end.

Fixpoint record_phis_partners (phis : list (nat * list (nat * option nat)))
                              (pm : ZMap.t (list nat)) : ZMap.t (list nat) :=
  match phis with
  | [] => pm
  | (d, ps) :: phis' => record_phis_partners phis' (record_phi_pair_partners d ps pm)
  end.

Fixpoint collect_phi_partners (rbs : list rblock) (pm : ZMap.t (list nat))
  : ZMap.t (list nat) :=
  match rbs with
  | [] => pm
  | rb :: rbs' => collect_phi_partners rbs' (record_phis_partners (rb_phis rb) pm)
  end.

(** Cap candidate set to the top 512 weighted eligible temporaries so
    pathological multi-thousand-temporary functions stay fast. *)
Definition candidate_cap : nat := 512%nat.

Definition eligible_class (k : class) : bool :=
  match k with W | L | P => true | _ => false end.

Fixpoint collect_eligible_weighted (els : list (Z * class)) (va_tid : option nat)
                                   (wm : ZMap.t Z) (acc : list (Z * nat))
  : list (Z * nat) :=
  match els with
  | [] => acc
  | (kz, cl) :: els' =>
      let tid := Z.to_nat kz in
      let is_va := match va_tid with Some vt => nat_eqb tid vt | None => false end in
      if eligible_class cl && negb is_va then
        let w := match ZMap.find kz wm with Some v => v | None => 0 end in
        if w >? 0 then collect_eligible_weighted els' va_tid wm ((w, tid) :: acc)
        else collect_eligible_weighted els' va_tid wm acc
      else collect_eligible_weighted els' va_tid wm acc
  end.

(** Sort `(weight, tid)` descending by weight, ties broken by smaller `tid`. *)
Definition weighted_tid_cmp (a b : Z * nat) : Datatypes.comparison :=
  match Z.compare (fst b) (fst a) with
  | Datatypes.Eq => Nat.compare (snd a) (snd b)
  | c => c
  end.

Fixpoint take_candidates_acc (n : nat) (xs : list (Z * nat))
                             (km : ZMap.t unit) (acc : list nat)
  : ZMap.t unit * list nat :=
  match n, xs with
  | O, _ | _, [] => (km, rev' acc)
  | S n', (_, tid) :: xs' =>
      take_candidates_acc n' xs' (zmap_add_nat tid tt km) (tid :: acc)
  end.

(** Build per-block `[lo, hi]` live sub-intervals and call-crossing
    flags over `keep`. *)
Definition touch_lo_hi (pt : nat) (t : nat) (lh : ZMap.t (nat * nat))
  : ZMap.t (nat * nat) :=
  match zmap_find_nat t lh with
  | None => zmap_add_nat t (pt, pt) lh
  | Some (lo, hi) => zmap_add_nat t (nat_min lo pt, nat_max hi pt) lh
  end.

Fixpoint touch_list_lo_hi (pt : nat) (ts : list nat) (lh : ZMap.t (nat * nat))
  : ZMap.t (nat * nat) :=
  match ts with
  | [] => lh
  | t :: ts' => touch_list_lo_hi pt ts' (touch_lo_hi pt t lh)
  end.

Fixpoint scan_rinsts_points (keep : option (ZMap.t unit)) (pt : nat) (ris : list rinst)
                            (lh : ZMap.t (nat * nat)) (calls : list nat)
  : nat * ZMap.t (nat * nat) * list nat :=
  match ris with
  | [] => (pt, lh, calls)
  | ri :: ris' =>
      let us := filter_keep_acc keep (ri_uses ri) [] in
      let ds := filter_keep_acc keep (ri_defs ri) [] in
      let p_use0 := pt in
      let p_call1 := S pt in
      let p_call2 := S (S pt) in
      let p_def := S (S (S pt)) in
      let lh1 := touch_list_lo_hi p_use0 us lh in
      let lh2 :=
        match ri_call ri with
        | RCallDuringReads => touch_list_lo_hi p_call2 us lh1
        | _ => lh1
        end in
      let lh3 := touch_list_lo_hi p_def ds lh2 in
      let calls1 :=
        match ri_call ri with
        | RCallNone => calls
        | RCallAfterReads => p_call2 :: calls
        | RCallDuringReads => p_call2 :: p_call1 :: calls
        end in
      scan_rinsts_points keep (S p_def) ris' lh3 calls1
  end.

Fixpoint mark_true_list (ts : list nat) (m : ZMap.t bool) : ZMap.t bool :=
  match ts with
  | [] => m
  | t :: ts' => mark_true_list ts' (zmap_add_nat t true m)
  end.

Fixpoint mark_poll_succs (keep : option (ZMap.t unit)) (rbm : ZMap.t rblock)
                         (live_in : ZMap.t (list nat)) (bi : nat)
                         (succs : list (nat * bool))
                         (p_phi_read : nat) (lh : ZMap.t (nat * nat))
                         (poll_cross : ZMap.t bool)
  : ZMap.t (nat * nat) * ZMap.t bool :=
  match succs with
  | [] => (lh, poll_cross)
  | (si, is_poll) :: succs' =>
      let euses :=
        match zmap_find_nat si rbm with
        | Some srb => rblock_phi_edge_uses_acc keep bi (rb_phis srb) []
        | None => []
        end in
      let lh1 := touch_list_lo_hi p_phi_read euses lh in
      let poll_cross1 :=
        if is_poll then
          let lin := nset_at si live_in in
          let pdefs :=
            match zmap_find_nat si rbm with
            | Some srb => rblock_phi_defs_acc keep (rb_phis srb) []
            | None => []
            end in
          mark_true_list (nset_union lin pdefs) poll_cross
        else poll_cross in
      mark_poll_succs keep rbm live_in bi succs' p_phi_read lh1 poll_cross1
  end.

Fixpoint flush_block_lh (els : list (Z * (nat * nat)))
                        (ivm : ZMap.t (list ival)) : ZMap.t (list ival) :=
  match els with
  | [] => ivm
  | (kz, seg) :: els' =>
      let prev := match ZMap.find kz ivm with Some l => l | None => [] end in
      flush_block_lh els' (ZMap.add kz (ivals_union prev [seg]) ivm)
  end.

Fixpoint build_intervals_blocks (keep : option (ZMap.t unit)) (rbm : ZMap.t rblock)
                                (live_in live_across : ZMap.t (list nat))
                                (entry_params : list nat) (is_first : bool)
                                (pt : nat) (rbs : list rblock)
                                (ivm : ZMap.t (list ival))
                                (calls : list nat) (poll_cross : ZMap.t bool)
  : ZMap.t (list ival) * list nat * ZMap.t bool :=
  match rbs with
  | [] => (ivm, nset_of_list calls, poll_cross)
  | rb :: rbs' =>
      let bi := rb_idx rb in
      let p_entry := pt in
      let lin := nset_at bi live_in in
      let pdefs := rblock_phi_defs_acc keep (rb_phis rb) [] in
      let init_ts :=
        if is_first then nset_union (nset_union lin pdefs) entry_params
        else nset_union lin pdefs in
      let lh0 := touch_list_lo_hi p_entry init_ts (ZMap.empty (nat * nat)) in
      let '(pt1, lh1, calls1) := scan_rinsts_points keep (S p_entry) (rb_insts rb) lh0 calls in
      let p_jump := pt1 in
      let p_phi_read := S p_jump in
      let p_exit := S (S p_phi_read) in
      let juses := filter_keep_acc keep (rb_jump_uses rb) [] in
      let lh2 := touch_list_lo_hi p_jump juses lh1 in
      let '(lh3, poll_cross1) :=
        mark_poll_succs keep rbm live_in bi (rb_succs rb) p_phi_read lh2 poll_cross in
      let lacross := nset_at bi live_across in
      let lh4 := touch_list_lo_hi p_exit lacross lh3 in
      let ivm1 := flush_block_lh (ZMap.elements lh4) ivm in
      build_intervals_blocks keep rbm live_in live_across [] false (S p_exit) rbs'
                             ivm1 calls1 poll_cross1
  end.

(** Priority coloring state: per-register union of assigned intervals. *)
Definition reg_slots_state : Type := list (hreg * list ival).

Definition init_reg_slots : reg_slots_state :=
  map (fun r => (r, [])) all_hregs.

Fixpoint lookup_reg_ivals (r : hreg) (st : reg_slots_state) : list ival :=
  match st with
  | [] => []
  | (r', ivs) :: st' => if hreg_eqb r r' then ivs else lookup_reg_ivals r st'
  end.

Fixpoint update_reg_ivals (r : hreg) (new_ivs : list ival) (st : reg_slots_state)
  : reg_slots_state :=
  match st with
  | [] => []
  | (r', ivs) :: st' =>
      if hreg_eqb r r' then (r', new_ivs) :: st'
      else (r', ivs) :: update_reg_ivals r new_ivs st'
  end.

Fixpoint partner_regs_acc (partners : list nat) (rm : ZMap.t hreg)
                          (need_cs : bool) (acc : list hreg) : list hreg :=
  match partners with
  | [] => rev' acc
  | p :: ps' =>
      match zmap_find_nat p rm with
      | Some r =>
          if (if need_cs then hreg_callee_saved r else true)
             && negb (hreg_in_list r acc)
          then partner_regs_acc ps' rm need_cs (r :: acc)
          else partner_regs_acc ps' rm need_cs acc
      | None => partner_regs_acc ps' rm need_cs acc
      end
  end.

Fixpoint dedup_hregs_acc (rs seen acc : list hreg) : list hreg :=
  match rs with
  | [] => rev' acc
  | r :: rs' =>
      if hreg_in_list r seen then dedup_hregs_acc rs' seen acc
      else dedup_hregs_acc rs' (r :: seen) (r :: acc)
  end.

Definition append_unique_hregs (xs ys : list hreg) : list hreg :=
  dedup_hregs_acc (xs ++ ys) [] [].

Fixpoint pick_free_hreg (order : list hreg) (ivs : list ival) (st : reg_slots_state)
  : option hreg :=
  match order with
  | [] => None
  | r :: order' =>
      if ivals_disjoint ivs (lookup_reg_ivals r st) then Some r
      else pick_free_hreg order' ivs st
  end.

Fixpoint color_candidates (cands : list nat) (ivm : ZMap.t (list ival))
                          (call_pts : list nat) (poll_cross : ZMap.t bool)
                          (partners : ZMap.t (list nat))
                          (st : reg_slots_state) (rm : ZMap.t hreg) : ZMap.t hreg :=
  match cands with
  | [] => rm
  | tid :: cands' =>
      match zmap_find_nat tid ivm with
      | None | Some [] => color_candidates cands' ivm call_pts poll_cross partners st rm
      | Some ivs =>
          let crosses_poll :=
            match zmap_find_nat tid poll_cross with Some b => b | None => false end in
          let crosses := crosses_poll || ivals_hit_points ivs call_pts in
          let pregs := partner_regs_acc (nset_at tid partners) rm crosses [] in
          let base_regs :=
            if crosses then callee_saved_hregs
            else caller_saved_hregs ++ callee_saved_hregs in
          let order := append_unique_hregs pregs base_regs in
          match pick_free_hreg order ivs st with
          | None => color_candidates cands' ivm call_pts poll_cross partners st rm
          | Some r =>
              let st' := update_reg_ivals r (ivals_union (lookup_reg_ivals r st) ivs) st in
              color_candidates cands' ivm call_pts poll_cross partners st'
                               (zmap_add_nat tid r rm)
          end
      end
  end.

(** Allocate registers for numbered blocks [rbs], returning `Some rm`
    only when [valid_alloc] accepts [rm]. *)
Definition allocate_regs (cmap : ZMap.t class) (va_tid : option nat)
                         (param_tids : list nat) (rbs : list rblock)
  : option (ZMap.t hreg) :=
  let loops := collect_backedges rbs in
  let bwm := build_block_weights rbs loops (ZMap.empty Z) in
  let wm := compute_temp_weights rbs bwm (ZMap.empty Z) in
  let weighted := collect_eligible_weighted (ZMap.elements cmap) va_tid wm [] in
  let sorted := msort weighted_tid_cmp weighted in
  let '(km, cands) := take_candidates_acc candidate_cap sorted (ZMap.empty unit) [] in
  match cands with
  | [] => Some (ZMap.empty hreg)
  | _ =>
      let keep := Some km in
      let* lv := rblock_liveness keep rbs in
      let '(live_in, _, live_across) := lv in
      let rbm := build_rb_map rbs (ZMap.empty rblock) in
      let kept_params := nset_of_list (filter_keep_acc keep param_tids []) in
      let '(ivm, call_pts, poll_cross) :=
        build_intervals_blocks keep rbm live_in live_across kept_params true O rbs
                               (ZMap.empty (list ival)) [] (ZMap.empty bool) in
      let partners := collect_phi_partners rbs (ZMap.empty (list nat)) in
      let rm := color_candidates cands ivm call_pts poll_cross partners
                                 init_reg_slots (ZMap.empty hreg) in
      if valid_alloc cmap param_tids rbs rm then Some rm else None
  end.

(** ## Parallel moves for phi edges *)

(** A parallel-move location: an allocated [hreg], a stack slot at
    `-off(%rbp)`, or the cycle-breaking scratch register `%rcx`. *)
Inductive pm_loc : Type :=
| PmReg (r : hreg)
| PmSlot (off : Z)
| PmCycleTmp.

Definition pm_loc_eqb (a b : pm_loc) : bool :=
  match a, b with
  | PmReg r1, PmReg r2 => hreg_eqb r1 r2
  | PmSlot o1, PmSlot o2 => o1 =? o2
  | PmCycleTmp, PmCycleTmp => true
  | _, _ => false
  end.

Inductive pm_src : Type :=
| PsLoc (l : pm_loc)
| PsConst (n : Z)
| PsGlobal (g : string).

Record pmove : Type := mkPMove {
  pmv_half : bool;
  pmv_src_w : bool;
  pmv_dst : pm_loc;
  pmv_src : pm_src
}.

(** Whether [m] is a true no-op: identical source and destination, and
    either 64-bit or an already zero-extended 32-bit source. *)
Definition pmove_is_nop (m : pmove) : bool :=
  match pmv_src m with
  | PsLoc l => pm_loc_eqb (pmv_dst m) l && (negb (pmv_half m) || pmv_src_w m)
  | _ => false
  end.

Fixpoint drop_nop_pmoves_acc (ms acc : list pmove) : list pmove :=
  match ms with
  | [] => rev' acc
  | m :: ms' =>
      if pmove_is_nop m then drop_nop_pmoves_acc ms' acc
      else drop_nop_pmoves_acc ms' (m :: acc)
  end.

Fixpoint loc_read_in_pmoves (l : pm_loc) (ms : list pmove) : bool :=
  match ms with
  | [] => false
  | m :: ms' =>
      let hit := match pmv_src m with PsLoc l' => pm_loc_eqb l l' | _ => false end in
      if hit then true else loc_read_in_pmoves l ms'
  end.

(** Find a move in `prefix_rev` + `rest` whose destination is read by
    no other remaining move. *)
Fixpoint pick_ready_pmove (rest prefix_rev : list pmove)
  : option (pmove * list pmove) :=
  match rest with
  | [] => None
  | m :: rest' =>
      if negb (loc_read_in_pmoves (pmv_dst m) prefix_rev)
         && negb (loc_read_in_pmoves (pmv_dst m) rest')
      then Some (m, rev_append prefix_rev rest')
      else pick_ready_pmove rest' (m :: prefix_rev)
  end.

Fixpoint subst_pmove_src (old : pm_loc) (ms acc : list pmove) : list pmove :=
  match ms with
  | [] => rev' acc
  | m :: ms' =>
      let src' :=
        match pmv_src m with
        | PsLoc l => if pm_loc_eqb l old then PsLoc PmCycleTmp else PsLoc l
        | s => s
        end in
      let m' := mkPMove (pmv_half m) (pmv_src_w m) (pmv_dst m) src' in
      if pmove_is_nop m' then subst_pmove_src old ms' acc
      else subst_pmove_src old ms' (m' :: acc)
  end.

(** Load integer constant [n] at width [half] into `(dst64, dst32)`
    without touching EFLAGS. *)
Definition load_const_reg (n : Z) (half : bool) (dst64 dst32 : string) : list line :=
  if half then
    [ins "mov" "l" [imm (n mod two32); reg dst32]]
  else
    let u := n mod two64 in
    let s := if u >=? two63 then u - two64 else u in
    if (0 <=? s) && (s <? two31) then
      [ins "mov" "l" [imm s; reg dst32]]
    else if (- two31 <=? s) && (s <? 0) then
      [ins "mov" "q" [imm s; reg dst64]]
    else
      [ins "movabs" "q" [imm s; reg dst64]].

Definition emit_save_cycle_tmp (l : pm_loc) : list line :=
  match l with
  | PmReg r => [ins "mov" "q" [reg (hreg64 r); reg "rcx"]]
  | PmSlot off => [ins "mov" "q" [mem (- off) "rbp"; reg "rcx"]]
  | PmCycleTmp => []
  end.

Definition emit_one_pmove (m : pmove) : list line :=
  let half := pmv_half m in
  let suf := class_suffix half in
  match pmv_dst m, pmv_src m with
  | PmReg rd, PsLoc (PmReg rs) =>
      [ins "mov" suf [reg (hreg_at rs half); reg (hreg_at rd half)]]
  | PmReg rd, PsLoc (PmSlot off) =>
      [ins "mov" suf [mem (- off) "rbp"; reg (hreg_at rd half)]]
  | PmReg rd, PsLoc PmCycleTmp =>
      [ins "mov" suf [reg (reg_name "c" half); reg (hreg_at rd half)]]
  | PmReg rd, PsConst n =>
      load_const_reg n half (hreg64 rd) (hreg32 rd)
  | PmReg rd, PsGlobal g =>
      [ins "lea" "q" [rip g; reg (hreg64 rd)]]
  | PmSlot off, PsLoc (PmReg rs) =>
      if half then
        [ins "mov" "l" [reg (hreg32 rs); reg "eax"];
         ins "mov" "q" [reg "rax"; mem (- off) "rbp"]]
      else
        [ins "mov" "q" [reg (hreg64 rs); mem (- off) "rbp"]]
  | PmSlot off, PsLoc (PmSlot soff) =>
      [ins "mov" suf [mem (- soff) "rbp"; reg (reg_name "a" half)];
       ins "mov" "q" [reg "rax"; mem (- off) "rbp"]]
  | PmSlot off, PsLoc PmCycleTmp =>
      if half then
        [ins "mov" "l" [reg "ecx"; reg "eax"];
         ins "mov" "q" [reg "rax"; mem (- off) "rbp"]]
      else
        [ins "mov" "q" [reg "rcx"; mem (- off) "rbp"]]
  | PmSlot off, PsConst n =>
      if negb half then
        match integer_immediate false n with
        | Some imm_v => [ins "mov" "q" [imm imm_v; mem (- off) "rbp"]]
        | None => load_const_reg n false "rax" "eax" ++ [ins "mov" "q" [reg "rax"; mem (- off) "rbp"]]
        end
      else
        load_const_reg n true "rax" "eax" ++ [ins "mov" "q" [reg "rax"; mem (- off) "rbp"]]
  | PmSlot off, PsGlobal g =>
      [ins "lea" "q" [rip g; reg "rax"];
       ins "mov" "q" [reg "rax"; mem (- off) "rbp"]]
  | PmCycleTmp, _ => todo "cycle tmp dst"
  end.

Fixpoint compile_pmoves_fuel (fuel : nat) (ms : list pmove) (acc : list line) : list line :=
  match ms with
  | [] => rev' acc
  | m0 :: _ =>
      match fuel with
      | O => rev_append acc (todo "parallel move fuel")
      | S fuel' =>
          match pick_ready_pmove ms [] with
          | Some (m, rest) =>
              compile_pmoves_fuel fuel' rest (rev_append (emit_one_pmove m) acc)
          | None =>
              let save := emit_save_cycle_tmp (pmv_dst m0) in
              let ms' := subst_pmove_src (pmv_dst m0) ms [] in
              compile_pmoves_fuel fuel' ms' (rev_append save acc)
          end
      end
  end.

Definition compile_pmoves (ms : list pmove) : list line :=
  let clean := drop_nop_pmoves_acc ms [] in
  compile_pmoves_fuel (S (2 * length clean)) clean [].

(** ## Function context and register-aware selection *)

Record rctx : Type := mkRCtx {
  rc_cx : ctx;
  rc_reg : nmap hreg;
  rc_class : nmap class;
  rc_saves : list (hreg * Z)
}.

Fixpoint place_callee_saves (rs : list hreg) (off : Z) (acc : list (hreg * Z))
  : list (hreg * Z) * Z :=
  match rs with
  | [] => (rev' acc, off)
  | r :: rs' => place_callee_saves rs' (off + eight) ((r, off + eight) :: acc)
  end.

Fixpoint hreg_in_pairs (r : hreg) (els : list (Z * hreg)) : bool :=
  match els with
  | [] => false
  | (_, r') :: els' => if hreg_eqb r r' then true else hreg_in_pairs r els'
  end.

Fixpoint collect_used_cs_acc (cs : list hreg) (els : list (Z * hreg)) (acc : list hreg)
  : list hreg :=
  match cs with
  | [] => rev' acc
  | r :: cs' =>
      if hreg_in_pairs r els then collect_used_cs_acc cs' els (r :: acc)
      else collect_used_cs_acc cs' els acc
  end.

Fixpoint build_name_reg_map (names_rev : list name) (idx : nat) (rm : ZMap.t hreg)
                            (acc : nmap hreg) : nmap hreg :=
  match names_rev with
  | [] => acc
  | d :: rest =>
      let acc' :=
        match zmap_find_nat idx rm with
        | Some r => nm_add d r acc
        | None => acc
        end in
      build_name_reg_map rest (S idx) rm acc'
  end.

Fixpoint build_name_class_map (names : list name) (idx : nat) (cmap : ZMap.t class)
                              (acc : nmap class) : nmap class :=
  match names with
  | [] => acc
  | d :: rest =>
      let acc' :=
        match zmap_find_nat idx cmap with
        | Some cl => nm_add d cl acc
        | None => acc
        end in
      build_name_class_map rest (S idx) cmap acc'
  end.

Fixpoint add_alias_slots (als : list (key * key)) (slots2 m : nmap Z) : nmap Z :=
  match als with
  | [] => m
  | (k1, k2) :: als' =>
      let m' :=
        match nm_find (key_term k2) slots2 with
        | Some off => nm_add (key_term k1) off m
        | None => m
        end in
      add_alias_slots als' slots2 m'
  end.

Fixpoint build_pblocks_phis_map (bs : list pblock) (m : nmap (list phi)) : nmap (list phi) :=
  match bs with
  | [] => m
  | b :: bs' => build_pblocks_phis_map bs' (nm_add (pb_label b) (pb_phis b) m)
  end.

(** Build the frame layout and [rctx] for [p], adding save slots for
    the callee-saved registers that [rm] uses. *)
Definition build_rctx (p : plan) (names : list name) (cmap : ZMap.t class)
                      (rm : ZMap.t hreg) : rctx :=
  let fr := pl_frame p in
  let '(slots1, locals, plain_bytes0) :=
    fold_left plain_slot (fr_plain fr) (nm_empty, nm_empty, 0) in
  let used_cs := collect_used_cs_acc callee_saved_hregs (ZMap.elements rm) [] in
  let '(saves, plain_bytes) := place_callee_saves used_cs plain_bytes0 [] in
  let base := plain_bytes + sixteen + eight * Zlength (fr_roots fr) in
  let '(slots2, _) := fold_left (lower_slot base) (fr_roots fr) (slots1, 0) in
  let slots := add_alias_slots (fr_aliases fr) slots2 slots2 in
  let phis_map := build_pblocks_phis_map (pl_blocks p) nm_empty in
  let cx := mkCtx (name_text (pl_name p)) slots locals (round16 base) base phis_map in
  mkRCtx cx (build_name_reg_map names O rm nm_empty)
         (build_name_class_map names O cmap nm_empty) saves.

Definition temp_is_w (rc : rctx) (d : name) : bool :=
  match nm_find d (rc_class rc) with Some W => true | _ => false end.

(** Load [v] at class [k] into the scratch short register [r]. *)
Definition rload (rc : rctx) (v : value) (k : class) (r : string) : list line :=
  match v, class_half k with
  | Global g, _ => [ins "lea" "q" [rip (name_text g); reg (reg64 r)]]
  | _, None => todo "load class"
  | Tmp n, Some half =>
      match nm_find n (rc_reg rc) with
      | Some hr =>
          [ins "mov" (class_suffix half) [reg (hreg_at hr half); reg (reg_name r half)]]
      | None =>
          with_slot (rc_cx rc) (KTmp n)
            (fun off => [ins "mov" (class_suffix half) [mem (- off) "rbp"; reg (reg_name r half)]])
      end
  | Const n, Some half => load_const_reg n half (reg64 r) (reg32 r)
  end.

(** Load [v] at integer width [half] into `(dst64, dst32)`. *)
Definition rload_into (rc : rctx) (v : value) (half : bool) (dst64 dst32 : string) : list line :=
  let dst := if half then dst32 else dst64 in
  match v with
  | Global g => [ins "lea" "q" [rip (name_text g); reg dst64]]
  | Const n => load_const_reg n half dst64 dst32
  | Tmp n =>
      match nm_find n (rc_reg rc) with
      | Some hr =>
          if String.eqb (hreg64 hr) dst64 && (negb half || temp_is_w rc n) then []
          else [ins "mov" (class_suffix half) [reg (hreg_at hr half); reg dst]]
      | None =>
          with_slot (rc_cx rc) (KTmp n)
            (fun off => [ins "mov" (class_suffix half) [mem (- off) "rbp"; reg dst]])
      end
  end.

Definition reg32_of_full (r64 : string) : string :=
  if String.eqb r64 "rax" then "eax"
  else if String.eqb r64 "rcx" then "ecx"
  else if String.eqb r64 "rdx" then "edx"
  else if String.eqb r64 "rsi" then "esi"
  else if String.eqb r64 "rdi" then "edi"
  else r64 ++ "d".

(** Store 64-bit register [src64] into [k] (register home or frame slot). *)
Definition rstore_key (rc : rctx) (src64 : string) (k : key) : list line :=
  match k with
  | KTmp d =>
      match nm_find d (rc_reg rc) with
      | Some hr =>
          let half := temp_is_w rc d in
          let src := if half then reg32_of_full src64 else src64 in
          [ins "mov" (class_suffix half) [reg src; reg (hreg_at hr half)]]
      | None => slot_store (rc_cx rc) src64 k
      end
  | _ => slot_store (rc_cx rc) src64 k
  end.

Definition rlower_load (rc : rctx) (v : value) (r : string) : list line :=
  lower_load (rc_cx rc) v r.

Definition rflight_load (rc : rctx) (v : value) : list line :=
  rload rc v L "a" ++ rlower_load rc v "rcx".

Definition rflight_store (rc : rctx) (d : name) : list line :=
  rstore_key rc "rax" (KTmp d) ++ slot_store (rc_cx rc) "rcx" (KLower (KTmp d)).

(** ## Prologue, epilogue and phi edges *)

Definition save_store_line (p : hreg * Z) : line :=
  ins "mov" "q" [reg (hreg64 (fst p)); mem (- snd p) "rbp"].

Definition save_restore_line (p : hreg * Z) : line :=
  ins "mov" "q" [mem (- snd p) "rbp"; reg (hreg64 (fst p))].

Definition callee_save_stores (saves : list (hreg * Z)) : list line :=
  map save_store_line saves.

Definition callee_save_restores (saves : list (hreg * Z)) : list line :=
  map save_restore_line saves.

Definition rleave_ret (rc : rctx) : list line :=
  callee_save_restores (rc_saves rc) ++ leave_ret.

Definition rincoming_word (rc : rctx) (l : location) (w : word) : list line :=
  match w with
  | Wf k (SrcSlot t) =>
      match l with
      | LocReg r => rstore_key rc (reg64 r) t
      | LocXmm x => from_xmm k x "a" ++ rstore_key rc "rax" t
      | LocStack i =>
          match class_half k with
          | Some half =>
              match t with
              | KTmp d =>
                  match nm_find d (rc_reg rc) with
                  | Some hr =>
                      let dhalf := half || temp_is_w rc d in
                      [ins "mov" (class_suffix dhalf)
                           [mem (sixteen + eight * i) "rbp"; reg (hreg_at hr dhalf)]]
                  | None =>
                      ins "mov" (class_suffix half)
                          [mem (sixteen + eight * i) "rbp"; reg (reg_name "a" half)]
                      :: slot_store (rc_cx rc) "rax" t
                  end
              | _ =>
                  ins "mov" (class_suffix half)
                      [mem (sixteen + eight * i) "rbp"; reg (reg_name "a" half)]
                  :: slot_store (rc_cx rc) "rax" t
              end
          | None => todo "incoming class"
          end
      end
  | _ => todo "incoming source"
  end.

Fixpoint rtyped_incoming_acc (rc : rctx) (ws : list word) (ls : list location)
                             (acc : list line) : list line :=
  match ws, ls with
  | w :: ws', l :: ls' =>
      rtyped_incoming_acc rc ws' ls' (rev_append (rincoming_word rc l w) acc)
  | _, _ => rev' acc
  end.

Definition rtyped_incoming (rc : rctx) (ws : list word) (ls : list location) : list line :=
  rtyped_incoming_acc rc ws ls [].

Definition rentry_lines (rc : rctx) (p : plan) : list line :=
  let cx := rc_cx rc in
  let ret := pl_return p in
  let base := cx_base cx in
  [ins "push" "q" [reg "rbp"];
   ins "mov" "q" [reg "rsp"; reg "rbp"];
   ins "sub" "q" [imm (cx_size cx); reg "rsp"]]
  ++ entry_regs_shift ret
  ++ [ins "cmp" "q" [reg "rsp"; mem thread_stack_limit "rdi"];
      ins0 "jae" [plt "filc_stack_overflow_failure"]]
  ++ callee_save_stores (rc_saves rc)
  ++ slot_store cx "rdi" KThread
  ++ match ret with Registers => [] | Buffer _ => slot_store cx "rax" KRetbuf end
  ++ lowers_zeroing (Zlength (fr_roots (pl_frame p))) base
  ++ [ins "mov" "q" [mem thread_top_frame "rdi"; reg "rax"];
      ins "mov" "q" [reg "rax"; mem (- base) "rbp"]]
  ++ origin_store cx "c"
  ++ [ins "lea" "q" [mem (- base) "rbp"; reg "rax"];
      ins "mov" "q" [reg "rax"; mem thread_top_frame "rdi"]]
  ++ (let '(ls, _, _) := typed_locations (pl_incoming p) ret in
      rtyped_incoming rc (pl_incoming p) ls).

(** Exception exit with callee-saved registers restored. *)
Definition rexc_exit_lines (rc : rctx) (ret : protocol) : list line :=
  let cx := rc_cx rc in
  frame_pop cx
  ++ match ret with
     | Registers => [ins "mov" "b" [imm 1; reg "al"]]
     | Buffer _ => slot_load cx KRetbuf "rax" ++ [ins "mov" "b" [imm 1; mem 0 "rax"]]
     end
  ++ rleave_ret rc.

Definition rsuccess (rc : rctx) (r : protocol) : list line :=
  match r with
  | Registers => ins "xor" "l" [reg "eax"; reg "eax"] :: rleave_ret rc
  | Buffer _ => todo "success of a buffered return"
  end.

(** Parallel-move construction for [phis] on edge from [from]. *)
Definition key_pm_loc (rc : rctx) (k : key) : option pm_loc :=
  match k with
  | KTmp d =>
      match nm_find d (rc_reg rc) with
      | Some hr => Some (PmReg hr)
      | None => option_map PmSlot (slot (rc_cx rc) k)
      end
  | _ => option_map PmSlot (slot (rc_cx rc) k)
  end.

Definition val_pm_src (rc : rctx) (v : value) : option (pm_src * bool) :=
  match v with
  | Const n => Some (PsConst n, true)
  | Global g => Some (PsGlobal (name_text g), false)
  | Tmp n =>
      match key_pm_loc rc (KTmp n) with
      | Some loc => Some (PsLoc loc, temp_is_w rc n)
      | None => None
      end
  end.

Definition lower_pm_src (rc : rctx) (v : value) : option pm_src :=
  match v with
  | Const _ => Some (PsConst 0)
  | Global _ => None
  | Tmp n => option_map (fun off => PsLoc (PmSlot off)) (slot (rc_cx rc) (KLower (KTmp n)))
  end.

Fixpoint build_phi_pmoves_acc (rc : rctx) (from : name) (phis : list phi)
                              (acc : list pmove) : option (list pmove) :=
  match phis with
  | [] => Some (rev' acc)
  | Phi d k pairs :: phis' =>
      let* v := pair_value from pairs in
      match k with
      | P =>
          let* dloc := key_pm_loc rc (KTmp d) in
          let* vs := val_pm_src rc v in
          let* dlloc := key_pm_loc rc (KLower (KTmp d)) in
          let* lsrc := lower_pm_src rc v in
          build_phi_pmoves_acc rc from phis'
            (mkPMove false false dlloc lsrc :: mkPMove false false dloc (fst vs) :: acc)
      | W | Single =>
          let* dloc := key_pm_loc rc (KTmp d) in
          let* vs := val_pm_src rc v in
          build_phi_pmoves_acc rc from phis' (mkPMove true (snd vs) dloc (fst vs) :: acc)
      | L | Double =>
          let* dloc := key_pm_loc rc (KTmp d) in
          let* vs := val_pm_src rc v in
          build_phi_pmoves_acc rc from phis' (mkPMove false false dloc (fst vs) :: acc)
      | _ => None
      end
  end.

Definition redge_moves (rc : rctx) (from : name) (t : target) (tag : string) : list line :=
  let cx := rc_cx rc in
  let phis := match nm_find (edge_label t) (cx_phis cx) with Some ps => ps | None => [] end in
  let moves :=
    match build_phi_pmoves_acc rc from phis [] with
    | Some ms => compile_pmoves ms
    | None => todo "phi parallel move"
    end in
  moves ++ match t with Poll _ => pollcheck cx from tag | To _ => [] end.

Definition redge (rc : rctx) (from : name) (t : target) (tag : string) : list line :=
  redge_moves rc from t tag ++ [ins0 "jmp" [sym (block_label (rc_cx rc) (edge_label t))]].

Definition rselected_edge (rc : rctx) (from : name) (t : target) (tag : string)
                          (next : option name) : list line :=
  if to_next t next then redge_moves rc from t tag else redge rc from t tag.

(** ## Direct integer, comparison, flight and access selection *)

(** Source operand for a binary integer op (`imm32`, `hreg`, or frame
    slot) when available without a scratch register. *)
Definition direct_src_operand (rc : rctx) (half : bool) (v : value) : option operand :=
  match v with
  | Const n => option_map imm (integer_immediate half n)
  | Tmp n =>
      match nm_find n (rc_reg rc) with
      | Some hr => Some (reg (hreg_at hr half))
      | None => option_map (fun off => mem (- off) "rbp") (slot (rc_cx rc) (KTmp n))
      end
  | Global _ => None
  end.

Definition val_uses_hreg (rc : rctx) (v : value) (hr : hreg) : bool :=
  match v with
  | Tmp n =>
      match nm_find n (rc_reg rc) with
      | Some hr' => hreg_eqb hr hr'
      | None => false
      end
  | _ => false
  end.

(** Compare `x` and `y` at integer class `ck`, setting EFLAGS for `c`. *)
Definition rcompare_with_reg (rc : rctx) (half : bool) (rx : string) (y : value) : list line :=
  let suf := class_suffix half in
  match direct_src_operand rc half y with
  | Some op_y => [ins "cmp" suf [op_y; reg rx]]
  | None =>
      rload rc y (if half then W else L) "c"
      ++ [ins "cmp" suf [reg (reg_name "c" half); reg rx]]
  end.

Definition rcompare_flags (rc : rctx) (ck : class) (x y : value) : list line :=
  match ck with
  | W | L =>
      let half := match ck with W => true | _ => false end in
      match x with
      | Tmp nx =>
          match nm_find nx (rc_reg rc) with
          | Some hrx => rcompare_with_reg rc half (hreg_at hrx half) y
          | None =>
              rload rc x ck "a" ++ rcompare_with_reg rc half (reg_name "a" half) y
          end
      | _ => rload rc x ck "a" ++ rcompare_with_reg rc half (reg_name "a" half) y
      end
  | _ => todo "compare class"
  end.

(** Narrow source register of `hr` for [ext_op]. *)
Definition hreg_ext_from (hr : hreg) (t : narrow) : string :=
  match t with
  | Sb | Ub => hreg8 hr
  | Sh | Uh => hreg16 hr
  | Sw | Uw => hreg32 hr
  end.

Definition rext_into (rc : rctx) (t : narrow) (k : class) (x : value)
                     (dst64 dst32 : string) : list line :=
  match ext_op t k with
  | None => todo "ext class"
  | Some (op_m, suf, to_a) =>
      let dst := if String.eqb to_a "eax" then dst32 else dst64 in
      match x with
      | Tmp nx =>
          match nm_find nx (rc_reg rc) with
          | Some hrx => [ins op_m suf [reg (hreg_ext_from hrx t); reg dst]]
          | None =>
              rload rc x W "a" ++ [ins op_m suf [reg (ext_from t); reg dst]]
          end
      | _ => rload rc x W "a" ++ [ins op_m suf [reg (ext_from t); reg dst]]
      end
  end.

(** Direct two-operand commutative ALU (`and`, `or`, `xor`) into
    `(dst64, dst32)`, where `dst_hr` is `Some hr` when targeting an
    allocatable register. *)
Definition ralu_comm_into (rc : rctx) (mnem : string) (half : bool) (x y : value)
                          (dst_hr : option hreg) (dst64 dst32 : string) : list line :=
  let suf := class_suffix half in
  let dst := if half then dst32 else dst64 in
  let k := if half then W else L in
  let swap :=
    match dst_hr with
    | Some hr => val_uses_hreg rc y hr && negb (val_uses_hreg rc x hr)
    | None =>
        match x with Const _ => true | _ => false end
        && match y with Const _ => false | _ => true end
    end in
  let '(a, b) := if swap then (y, x) else (x, y) in
  match dst_hr with
  | Some hr =>
      if val_uses_hreg rc b hr then
        rload rc b k "c"
        ++ rload_into rc a half dst64 dst32
        ++ [ins mnem suf [reg (reg_name "c" half); reg dst]]
      else
        rload_into rc a half dst64 dst32
        ++ match direct_src_operand rc half b with
           | Some op_b => [ins mnem suf [op_b; reg dst]]
           | None => rload rc b k "c" ++ [ins mnem suf [reg (reg_name "c" half); reg dst]]
           end
  | None =>
      rload_into rc a half dst64 dst32
      ++ match direct_src_operand rc half b with
         | Some op_b => [ins mnem suf [op_b; reg dst]]
         | None => rload rc b k "c" ++ [ins mnem suf [reg (reg_name "c" half); reg dst]]
         end
  end.

(** Direct integer `Add` with 3-address `lea` when operands live in
    registers distinct from the destination. *)
Definition radd_into (rc : rctx) (half : bool) (x y : value)
                     (dst_hr : option hreg) (dst64 dst32 : string) : list line :=
  let suf := class_suffix half in
  let dst := if half then dst32 else dst64 in
  let '(a, b) :=
    match x, y with
    | Const _, Tmp _ => (y, x)
    | _, _ => (x, y)
    end in
  match a, b with
  | Tmp na, Const n =>
      match nm_find na (rc_reg rc), integer_immediate half n with
      | Some hra, Some imm_v =>
          if imm_v =? 0 then rload_into rc a half dst64 dst32
          else if String.eqb (hreg64 hra) dst64 then
            [ins "add" suf [imm imm_v; reg dst]]
          else
            [ins "lea" suf [mem imm_v (hreg64 hra); reg dst]]
      | _, _ => ralu_comm_into rc "add" half x y dst_hr dst64 dst32
      end
  | Tmp na, Tmp nb =>
      match nm_find na (rc_reg rc), nm_find nb (rc_reg rc) with
      | Some hra, Some hrb =>
          if String.eqb (hreg64 hra) dst64 then
            [ins "add" suf [reg (hreg_at hrb half); reg dst]]
          else if String.eqb (hreg64 hrb) dst64 then
            [ins "add" suf [reg (hreg_at hra half); reg dst]]
          else
            [ins "lea" suf [mem_index 0 (hreg64 hra) (hreg64 hrb); reg dst]]
      | _, _ => ralu_comm_into rc "add" half x y dst_hr dst64 dst32
      end
  | _, _ => ralu_comm_into rc "add" half x y dst_hr dst64 dst32
  end.

(** Direct integer `Sub` with `lea` on constant subtrahends. *)
Definition rsub_into (rc : rctx) (half : bool) (x y : value)
                     (dst_hr : option hreg) (dst64 dst32 : string) : list line :=
  let suf := class_suffix half in
  let dst := if half then dst32 else dst64 in
  let k := if half then W else L in
  match x, y with
  | Tmp nx, Const n =>
      match nm_find nx (rc_reg rc) with
      | Some hrx =>
          if String.eqb (hreg64 hrx) dst64 then
            match integer_immediate half n with
            | Some imm_v =>
                if imm_v =? 0 then rload_into rc x half dst64 dst32
                else [ins "sub" suf [imm imm_v; reg dst]]
            | None =>
                rload rc y k "c" ++ [ins "sub" suf [reg (reg_name "c" half); reg dst]]
            end
          else
            match integer_immediate half (- n) with
            | Some neg_v =>
                if neg_v =? 0 then rload_into rc x half dst64 dst32
                else [ins "lea" suf [mem neg_v (hreg64 hrx); reg dst]]
            | None =>
                rload_into rc x half dst64 dst32
                ++ match integer_immediate half n with
                   | Some imm_v => [ins "sub" suf [imm imm_v; reg dst]]
                   | None => rload rc y k "c" ++ [ins "sub" suf [reg (reg_name "c" half); reg dst]]
                   end
            end
      | None =>
          rload_into rc x half dst64 dst32
          ++ match direct_src_operand rc half y with
             | Some op_y => [ins "sub" suf [op_y; reg dst]]
             | None => rload rc y k "c" ++ [ins "sub" suf [reg (reg_name "c" half); reg dst]]
             end
      end
  | _, _ =>
      let clobbers_y :=
        match dst_hr with Some hr => val_uses_hreg rc y hr | None => false end in
      if clobbers_y then
        rload rc y k "c"
        ++ rload_into rc x half dst64 dst32
        ++ [ins "sub" suf [reg (reg_name "c" half); reg dst]]
      else
        rload_into rc x half dst64 dst32
        ++ match direct_src_operand rc half y with
           | Some op_y => [ins "sub" suf [op_y; reg dst]]
           | None => rload rc y k "c" ++ [ins "sub" suf [reg (reg_name "c" half); reg dst]]
           end
  end.

(** Direct integer `Mul`, using 3-operand `imul $imm, src, dst` when
    multiplying by a 32-bit immediate. *)
Definition rmul_into (rc : rctx) (half : bool) (x y : value)
                     (dst_hr : option hreg) (dst64 dst32 : string) : list line :=
  let suf := class_suffix half in
  let dst := if half then dst32 else dst64 in
  let '(a, b) :=
    match x, y with
    | Const _, _ => (y, x)
    | _, _ => (x, y)
    end in
  match b with
  | Const n =>
      match integer_immediate half n with
      | Some imm_v =>
          match a with
          | Tmp na =>
              match nm_find na (rc_reg rc) with
              | Some hra => [ins "imul" suf [imm imm_v; reg (hreg_at hra half); reg dst]]
              | None =>
                  with_slot (rc_cx rc) (KTmp na)
                    (fun off => [ins "imul" suf [imm imm_v; mem (- off) "rbp"; reg dst]])
              end
          | _ =>
              rload_into rc a half dst64 dst32
              ++ [ins "imul" suf [imm imm_v; reg dst; reg dst]]
          end
      | None => ralu_comm_into rc "imul" half x y dst_hr dst64 dst32
      end
  | _ => ralu_comm_into rc "imul" half x y dst_hr dst64 dst32
  end.

(** Direct shift into `(dst64, dst32)`. *)
Definition rshift_into (rc : rctx) (mnem : string) (half : bool) (x y : value)
                       (dst64 dst32 : string) : list line :=
  let suf := class_suffix half in
  let dst := if half then dst32 else dst64 in
  match y with
  | Const n =>
      let cnt := n mod (if half then 32 else 64) in
      rload_into rc x half dst64 dst32
      ++ (if cnt =? 0 then [] else [ins mnem suf [imm cnt; reg dst]])
  | _ =>
      rload rc y W "c"
      ++ rload_into rc x half dst64 dst32
      ++ [ins mnem suf [reg "cl"; reg dst]]
  end.

(** Division, float and x87 operations through `%rax`, reading and
    writing register homes via [rload] and [rstore_key]. *)
Definition rdivision (rc : rctx) (sg : signedness) (rem_flag : bool) (k : class)
                     (args : list value) : list line :=
  match args, class_half k with
  | [x; y], Some half =>
      let s := class_suffix half in
      let a := reg_name "a" half in
      let c := reg_name "c" half in
      let d := reg_name "d" half in
      rload rc x k "a" ++ rload rc y k "c"
      ++ zero_divisor s a c d ++ minus_one_divisor sg s a c d
      ++ divide sg k s c ++ division_result rem_flag half
  | [_; _], None => todo "division class"
  | _, _ => todo "division arguments"
  end.

Definition rfloat_load (rc : rctx) (v : value) (k : class) (x : string) : list line :=
  if sse_class k then rload rc v k "a" ++ to_xmm k "a" x else todo "float class".

Definition rfloat_op (rc : rctx) (o : op) (k : class) (args : list value) : list line :=
  let cx := rc_cx rc in
  match o, args with
  | (Add | Sub | Mul | Div), [x; y] =>
      match float_arith o, float_suffix k with
      | Some insn, Some s =>
          rfloat_load rc x k "xmm0" ++ rfloat_load rc y k "xmm1"
          ++ [ins insn s [reg "xmm1"; reg "xmm0"]] ++ from_xmm k "xmm0" "a"
      | _, _ => todo "float class"
      end
  | Neg, [x] =>
      match float_bits k with
      | Some b =>
          let mask := match k with Single => single_sign | _ => double_sign end in
          let half := match k with Single => true | _ => false end in
          rload rc x k "a" ++ rload rc (Const mask) b "c"
          ++ [ins "xor" (class_suffix half) [reg (reg_name "c" half); reg (reg_name "a" half)]]
      | None => todo "float class"
      end
  | Cmp c ck, [x; y] =>
      match k, float_compare ck with
      | W, Some cmp =>
          rfloat_load rc x ck "xmm0" ++ rfloat_load rc y ck "xmm1"
          ++ [ins0 cmp [reg "xmm1"; reg "xmm0"]]
          ++ float_condition c
          ++ [ins "movzb" "l" [reg "al"; reg "eax"]]
      | _, _ => todo "float cmp class"
      end
  | ExtF Single, [x] =>
      match k with
      | Double =>
          rfloat_load rc x Single "xmm0"
          ++ [ins0 "cvtss2sd" [reg "xmm0"; reg "xmm0"]] ++ from_xmm Double "xmm0" "a"
      | _ => todo "ext class"
      end
  | Truncd, [x] =>
      match k with
      | Single =>
          rfloat_load rc x Double "xmm0"
          ++ [ins0 "cvtsd2ss" [reg "xmm0"; reg "xmm0"]] ++ from_xmm Single "xmm0" "a"
      | _ => todo "truncd class"
      end
  | Cast, [x] => rload rc x k "a"
  | FloatToInt f sg, [x] =>
      if sse_class f then rfloat_load rc x f "xmm0" ++ float_integer cx sg f k
      else todo "float op"
  | IntToFloat ik sg, [x] =>
      match ik with
      | W | L =>
          if sse_class k
          then rload rc x ik "a" ++ integer_float sg ik k ++ from_xmm k "xmm0" "a"
          else todo "float class"
      | _ => todo "float op"
      end
  | _, _ => todo "float op"
  end.

Definition rx87_push_float (rc : rctx) (f : class) (v : value) : list line :=
  match x87_suffix f with
  | Some (s, _) =>
      rload rc v f "a"
      ++ [ins "mov" "q" [reg "rax"; mem (-8) "rsp"]; ins "fld" s [mem (-8) "rsp"]]
  | None => todo "x87 ext class"
  end.

Definition rx87_fisttp (rc : rctx) (k : class) (d : name) : list line :=
  let half := match k with W => true | _ => false end in
  [ins "fisttp" "ll" [mem (-8) "rsp"];
   ins "mov" (class_suffix half) [mem (-8) "rsp"; reg (reg_name "a" half)]]
  ++ rstore_key rc "rax" (KTmp d).

Definition rx87_int_source (rc : rctx) (o : op) (a : value) : list line :=
  match o with
  | IntToFloat W Signed => rload rc a W "a" ++ [ins "movsl" "q" [reg "eax"; reg "rax"]]
  | IntToFloat W Unsigned => rload rc a W "a" ++ [ins "mov" "l" [reg "eax"; reg "eax"]]
  | IntToFloat L _ => rload rc a L "a"
  | _ => todo "x87 integer source"
  end.

Definition rx87_inst (rc : rctx) (o : op) (k : class) (args : list value) (d : name)
  : list line :=
  let cx := rc_cx rc in
  match o, k, args with
  | (Add | Sub | Mul | Div), Extended, [a; b] =>
      match x87_arith o with
      | Some insn =>
          x87_push cx b ++ x87_push cx a
          ++ [ins0 insn [reg "st(1)"; reg "st"]]
          ++ x87_pop cx d ++ [ins0 "fstp" [reg "st(0)"]]
      | None => todo "x87 op"
      end
  | Neg, Extended, [a] => x87_push cx a ++ [ins0 "fchs" []] ++ x87_pop cx d
  | Copy, Extended, [a] => x87_push cx a ++ x87_pop cx d
  | Cmp c Extended, W, [a; b] =>
      x87_push cx b ++ x87_push cx a
      ++ [ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]]
      ++ float_condition c
      ++ [ins "movzb" "l" [reg "al"; reg "eax"]]
      ++ rstore_key rc "rax" (KTmp d)
  | ExtF f, Extended, [a] => rx87_push_float rc f a ++ x87_pop cx d
  | Truncx, _, [a] =>
      match x87_suffix k with
      | Some (s, mov) =>
          x87_push cx a
          ++ [ins "fstp" s [mem (-8) "rsp"];
              ins "mov" mov [mem (-8) "rsp"; reg (if String.eqb mov "l" then "eax" else "rax")]]
          ++ rstore_key rc "rax" (KTmp d)
      | None => todo "x87 truncx class"
      end
  | FloatToInt Extended Signed, _, [a] => x87_push cx a ++ rx87_fisttp rc k d
  | FloatToInt Extended Unsigned, W, [a] => x87_push cx a ++ rx87_fisttp rc W d
  | FloatToInt Extended Unsigned, L, [a] =>
      x87_push cx a
      ++ [ins "mov" "l" [imm single_two63; mem (-12) "rsp"];
          ins "fld" "s" [mem (-12) "rsp"];
          ins0 "fucomip" [reg "st(1)"; reg "st"];
          ins0 "ja" [sym "1f"];
          ins "fsub" "s" [mem (-12) "rsp"];
          ins "fisttp" "ll" [mem (-8) "rsp"];
          ins "mov" "q" [mem (-8) "rsp"; reg "rax"];
          ins "btc" "q" [imm sixty_three; reg "rax"];
          ins0 "jmp" [sym "2f"];
          label "1";
          ins "fisttp" "ll" [mem (-8) "rsp"];
          ins "mov" "q" [mem (-8) "rsp"; reg "rax"];
          label "2"]
      ++ rstore_key rc "rax" (KTmp d)
  | IntToFloat (W | L) _, Extended, [a] =>
      rx87_int_source rc o a
      ++ [ins "mov" "q" [reg "rax"; mem (-8) "rsp"]; ins "fild" "ll" [mem (-8) "rsp"]]
      ++ x87_unsigned_fix o
      ++ x87_pop cx d
  | _, _, _ => todo "x87 op"
  end.

(** Emit integer operation [o] at class [k] into `(dst64, dst32)`. *)
Definition rint_op_into (rc : rctx) (o : op) (k : class) (args : list value)
                        (dst_hr : option hreg) (dst64 dst32 : string) : list line :=
  match class_half k with
  | None => todo "int op class"
  | Some half =>
      let suf := class_suffix half in
      let dst := if half then dst32 else dst64 in
      match o, args with
      | Copy, [x] => rload_into rc x half dst64 dst32
      | Ptoi, [p] =>
          match k with
          | L => rload_into rc p false dst64 dst32
          | _ => todo "ptoi"
          end
      | Neg, [x] =>
          rload_into rc x half dst64 dst32 ++ [ins "neg" suf [reg dst]]
      | Add, [x; y] => radd_into rc half x y dst_hr dst64 dst32
      | Sub, [x; y] => rsub_into rc half x y dst_hr dst64 dst32
      | Mul, [x; y] => rmul_into rc half x y dst_hr dst64 dst32
      | And, [x; y] => ralu_comm_into rc "and" half x y dst_hr dst64 dst32
      | Or, [x; y] => ralu_comm_into rc "or" half x y dst_hr dst64 dst32
      | Xor, [x; y] => ralu_comm_into rc "xor" half x y dst_hr dst64 dst32
      | Shl, [x; y] => rshift_into rc "shl" half x y dst64 dst32
      | Shr, [x; y] => rshift_into rc "shr" half x y dst64 dst32
      | Sar, [x; y] => rshift_into rc "sar" half x y dst64 dst32
      | Ext t, [x] => rext_into rc t k x dst64 dst32
      | Cmp c ck, [x; y] =>
          if sse_class ck then
            rfloat_op rc o k args
            ++ (if String.eqb dst64 "rax" then [] else [ins "mov" "l" [reg "eax"; reg dst32]])
          else
            match cond_code c with
            | Some cc =>
                rcompare_flags rc ck x y
                ++ [ins0 ("set" ++ cc) [reg "al"];
                    ins "movzb" "l" [reg "al"; reg dst32]]
            | None => todo "cmp condition"
            end
      | Select, [c; x; y] =>
          (* As EmitOps.v has it: y in `%rax`, x in `%rcx`, the choice
             in `%edx`; no home register is one of these. *)
          rload rc y k "a" ++ rload rc x k "c" ++ rload rc c W "d"
          ++ [ins "test" "l" [reg "edx"; reg "edx"]; ins "cmovne" "q" [reg "rcx"; reg "rax"]]
          ++ (if String.eqb dst64 "rax" then [] else [ins "mov" suf [reg (reg_name "a" half); reg dst]])
      | Div, _ =>
          rdivision rc Signed false k args
          ++ (if String.eqb dst64 "rax" then [] else [ins "mov" suf [reg (reg_name "a" half); reg dst]])
      | Rem, _ =>
          rdivision rc Signed true k args
          ++ (if String.eqb dst64 "rax" then [] else [ins "mov" suf [reg (reg_name "a" half); reg dst]])
      | Udiv, _ =>
          rdivision rc Unsigned false k args
          ++ (if String.eqb dst64 "rax" then [] else [ins "mov" suf [reg (reg_name "a" half); reg dst]])
      | Urem, _ =>
          rdivision rc Unsigned true k args
          ++ (if String.eqb dst64 "rax" then [] else [ins "mov" suf [reg (reg_name "a" half); reg dst]])
      | _, _ => todo "int op"
      end
  end.

Definition rspan_test_lines (rc : rctx) (b : name) (index : string) (lo hi : Z)
                            (p : value) (d : name) : list line :=
  let cx := rc_cx rc in
  let zero := local_label cx b index "span0" in
  let done := local_label cx b index "span1" in
  rflight_load rc p
  ++ [ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "jz" [sym zero]]
  ++ span_end lo "rdx"
  ++ [ins "cmp" "q" [reg "rcx"; reg "rdx"]; ins0 "jb" [sym zero]]
  ++ span_end hi "rax"
  ++ [ins "cmp" "q" [reg "rdx"; reg "rax"]; ins0 "jbe" [sym zero];
      ins "cmp" "q" [mem (-16) "rcx"; reg "rax"]; ins0 "ja" [sym zero];
      ins "mov" "l" [imm 1; reg "eax"];
      ins0 "jmp" [sym done];
      label zero;
      ins "xor" "l" [reg "eax"; reg "eax"];
      label done]
  ++ rstore_key rc "rax" (KTmp d).

Definition rlet_lines (rc : rctx) (b : name) (index : string) (d : name) (k : class)
                      (o : op) (args : list value) : list line :=
  let cx := rc_cx rc in
  if x87_op o k then rx87_inst rc o k args d
  else if float_compute o k then rfloat_op rc o k args ++ rstore_key rc "rax" (KTmp d)
  else
    match o with
    | Alloc align =>
        match k, args with
        | P, [n] =>
            rload rc n L "si"
            ++ slot_load cx KThread "rdi"
            ++ (if align >=? sixteen
                then [ins "mov" "l" [imm align; reg "edx"];
                      ins0 "call" [plt "filc_allocate_with_alignment"]]
                else [ins0 "call" [plt "filc_allocate"]])
            ++ [ins "lea" "q" [mem sixteen "rax"; reg "rax"];
                ins "mov" "q" [reg "rax"; reg "rcx"]]
            ++ rflight_store rc d
        | _, _ => todo "alloc"
        end
    | SpanTest lo hi =>
        match k, args with
        | W, [p] => rspan_test_lines rc b index lo hi p d
        | _, _ => todo "span_test"
        end
    | _ =>
        match nm_find d (rc_reg rc) with
        | Some hr => rint_op_into rc o k args (Some hr) (hreg64 hr) (hreg32 hr)
        | None => rint_op_into rc o k args None "rax" "eax" ++ slot_store cx "rax" (KTmp d)
        end
    end.

(** Flight address calculation into `dst64` (`%rax` or an `hreg`). *)
Definition flight_arg_val (a : flight_arg) : value :=
  match a with FAddress p => p | FValue v => v end.

Definition rflight_addr_into (rc : rctx) (o : op) (args : list flight_arg)
                             (dst_hr : option hreg) (dst64 : string) : list line :=
  let dst32 := match dst_hr with Some hr => hreg32 hr | None => "eax" end in
  match o, args with
  | Copy, [a] => rload_into rc (flight_arg_val a) false dst64 dst32
  | Add, [a; x] => radd_into rc false (flight_arg_val a) (flight_arg_val x) dst_hr dst64 dst32
  | Sub, [a; x] => rsub_into rc false (flight_arg_val a) (flight_arg_val x) dst_hr dst64 dst32
  | _, _ => todo "flight"
  end.

Definition rflight_lines (rc : rctx) (d : name) (o : op) (args : list flight_arg)
                         (lower : flight_lower) : list line :=
  let cx := rc_cx rc in
  let lower_code :=
    if shared_lower cx lower d then []
    else
      match lower with
      | LowerOf p => rlower_load rc p "rcx"
      | LowerNone => [ins "xor" "l" [reg "ecx"; reg "ecx"]]
      end
      ++ slot_store cx "rcx" (KLower (KTmp d)) in
  match nm_find d (rc_reg rc) with
  | Some hrd =>
      lower_code ++ rflight_addr_into rc o args (Some hrd) (hreg64 hrd)
  | None =>
      rflight_addr_into rc o args None "rax"
      ++ lower_code
      ++ slot_store cx "rax" (KTmp d)
  end.

(** Raw loads and stores with direct register destinations/sources. *)
Definition rraw_load (rc : rctx) (t : load_type) (k : class) (d : name) : list line :=
  let cx := rc_cx rc in
  match t with
  | LdX => ins "fld" "t" [mem 0 "rax"] :: x87_pop cx d
  | _ =>
      match load_op t k with
      | None => todo "load type"
      | Some (op_m, suf, to_a) =>
          match nm_find d (rc_reg rc) with
          | Some hrd =>
              let dst := if String.eqb to_a "eax" then hreg32 hrd else hreg64 hrd in
              [ins op_m suf [mem 0 "rax"; reg dst]]
          | None =>
              [ins op_m suf [mem 0 "rax"; reg to_a]]
              ++ slot_store cx "rax" (KTmp d)
          end
      end
  end.

Definition rraw_store (rc : rctx) (w : width) (v : value) : list line :=
  let cx := rc_cx rc in
  match w with
  | Wx => x87_push cx v ++ [ins "fstp" "t" [mem 0 "rax"]]
  | _ =>
      match width_value_class w, width_suffix w with
      | Some k, Some suf =>
          match v with
          | Tmp nv =>
              match nm_find nv (rc_reg rc) with
              | Some hrv =>
                  match hreg_width hrv w with
                  | Some rn => [ins "mov" suf [reg rn; mem 0 "rax"]]
                  | None => todo "store width"
                  end
              | None => rload rc v k "d" ++ store_insn w "d"
              end
          | Const n =>
              match w with
              | Wb => [ins "mov" "b" [imm (n mod 256); mem 0 "rax"]]
              | Wh => [ins "mov" "w" [imm (n mod 65536); mem 0 "rax"]]
              | Ww =>
                  match integer_immediate true n with
                  | Some iv => [ins "mov" "l" [imm iv; mem 0 "rax"]]
                  | None => rload rc v k "d" ++ store_insn w "d"
                  end
              | Wl =>
                  match integer_immediate false n with
                  | Some iv => [ins "mov" "q" [imm iv; mem 0 "rax"]]
                  | None => rload rc v k "d" ++ store_insn w "d"
                  end
              | _ => rload rc v k "d" ++ store_insn w "d"
              end
          | Global _ => rload rc v k "d" ++ store_insn w "d"
          end
      | _, _ => todo "store width"
      end
  end.

Definition rpointer_store_effect (rc : rctx) (b : name) (index : string) (v a : value)
                                 (e : effect) : list line :=
  let cx := rc_cx rc in
  match e with
  | AuxEnsure =>
      let haveaux := local_label cx b index "haveaux" in
      aux_of_lower
      ++ [ins0 "jnz" [sym haveaux]]
      ++ slot_load cx KThread "rdi"
      ++ [ins "lea" "q" [mem (-16) "rcx"; reg "rsi"];
          ins0 "call" [plt "filc_object_ensure_aux_ptr_outline"];
          ins "mov" "q" [reg "rax"; reg "rdx"];
          label haveaux]
      ++ slot_store cx "rdx" KAux
  | LowerBarrier =>
      let nobarrier := local_label cx b index "nobarrier" in
      rlower_load rc v "rsi"
      ++ [ins "test" "q" [reg "rsi"; reg "rsi"];
          ins0 "jz" [sym nobarrier];
          ins "mov" "q" [gotpcrel "filc_current_marking_state"; reg "rax"];
          ins "cmp" "l" [imm 0; mem 0 "rax"];
          ins0 "je" [sym nobarrier]]
      ++ slot_load cx KThread "rdi"
      ++ [ins0 "call" [plt "filc_store_barrier_for_lower_slow"]; label nobarrier]
  | RootedReload =>
      rflight_load rc a
      ++ slot_load cx KAux "rdx"
      ++ [ins "mov" "q" [reg "rax"; reg "r8"]; ins "sub" "q" [reg "rcx"; reg "r8"]]
      ++ rlower_load rc v "rsi"
      ++ rload rc v L "r9"
  | AtomicWrite =>
      [ins "mov" "q" [reg "rax"; reg "rsi"]; ins "mov" "q" [reg "rcx"; reg "rdx"]]
      ++ origin_store cx "c"
      ++ slot_load cx KThread "rdi"
      ++ rload rc v L "c"
      ++ rlower_load rc v "r8"
      ++ [ins0 "call" [plt "filc_store_ptr_atomic_outline"]]
  | LowerWrite => [ins "mov" "q" [reg "rsi"; mem_index 0 "rdx" "r8"]]
  | AddressWrite => [ins "mov" "q" [reg "r9"; mem 0 "rax"]]
  | _ => todo "pointer store effect"
  end.

Definition rraw_access (rc : rctx) (b : name) (index : string) (a : access) : list line :=
  let cx := rc_cx rc in
  match a with
  | ALoad d k t _ _ => rraw_load rc t k d
  | AStore w _ v _ => rraw_store rc w v
  | ALoadPointer d _ es _ =>
      flat_map (pointer_load_effect cx b index) es ++ rflight_store rc d
  | AStorePointer _ v (AtValue p) es => flat_map (rpointer_store_effect rc b index v p) es
  | AStorePointer _ _ (AtLocal _ _) _ => todo "pointer store at a local"
  | ATouch _ => []
  end.

Definition local_load_eff_lines (e : effect) : list line :=
  match e with
  | AuxRead => [ins "mov" "q" [mem 0 "rdx"; reg "rcx"]]
  | AddressRead => [ins "mov" "q" [mem 0 "rax"; reg "rax"]]
  | _ => todo "local load effect"
  end.

Definition local_store_eff_lines (rc : rctx) (v : value) (e : effect) : list line :=
  match e with
  | LowerWrite => rlower_load rc v "rcx" ++ [ins "mov" "q" [reg "rcx"; mem 0 "rdx"]]
  | AddressWrite => rload rc v L "si" ++ [ins "mov" "q" [reg "rsi"; mem 0 "rax"]]
  | _ => todo "local store effect"
  end.

Definition rlocal_raw_access (rc : rctx) (b : name) (index : string) (a : access) : list line :=
  match a with
  | ALoadPointer d _ es _ =>
      flat_map local_load_eff_lines es ++ rflight_store rc d
  | AStorePointer _ v _ es =>
      flat_map (local_store_eff_lines rc v) es
  | _ => rraw_access rc b index a
  end.

(** ## Calls and ABI actions *)

Definition rword_reg_load (rc : rctx) (s : source) (r : string) : list line :=
  match s with
  | SrcAddr v => rload rc v L r
  | SrcVal k v => rload rc v k r
  | SrcLower v => rlower_load rc v (reg64 r)
  | _ => todo "call word"
  end.

Fixpoint rtyped_stack_args_acc (rc : rctx) (ws : list word) (ls : list location)
                               (acc : list line) : list line :=
  match ws, ls with
  | Wf _ s :: ws', l :: ls' =>
      let cur :=
        match l with
        | LocStack i => rword_reg_load rc s "a" ++ [ins "mov" "q" [reg "rax"; mem (eight * i) "rsp"]]
        | _ => []
        end in
      rtyped_stack_args_acc rc ws' ls' (rev_append cur acc)
  | _, _ => rev' acc
  end.

Fixpoint rtyped_register_args_acc (rc : rctx) (ws : list word) (ls : list location)
                                  (acc : list line) : list line :=
  match ws, ls with
  | Wf k s :: ws', l :: ls' =>
      let cur :=
        match l with
        | LocStack _ => []
        | LocReg r => rword_reg_load rc s r
        | LocXmm x => rword_reg_load rc s "a" ++ to_xmm k "a" x
        end in
      rtyped_register_args_acc rc ws' ls' (rev_append cur acc)
  | _, _ => rev' acc
  end.

Definition rfast_call (rc : rctx) (r : protocol) (ws : list word) (callee : option operand)
  : list line :=
  let '(ls, ns, _) := typed_locations ws r in
  let pop := stack_bytes ns in
  (if pop >? 0 then [ins "sub" "q" [imm pop; reg "rsp"]] else [])
  ++ rtyped_stack_args_acc rc ws ls []
  ++ rtyped_register_args_acc rc ws ls []
  ++ entry_call (rc_cx rc) r callee pop
  ++ (if pop >? 0 then [ins "add" "q" [imm pop; reg "rsp"]] else []).

Fixpoint rreg_slot_stores_acc (rc : rctx) (ks : list key) (rs : list string)
                              (acc : list line) : list line :=
  match ks, rs with
  | [], _ => rev' acc
  | k :: ks', r :: rs' => rreg_slot_stores_acc rc ks' rs' (rev_append (rstore_key rc r k) acc)
  | _ :: _, [] => rev_append acc (todo "result registers")
  end.

Fixpoint rbuffer_slot_copies_acc (rc : rctx) (ks : list key) (off : Z)
                                 (acc : list line) : list line :=
  match ks with
  | [] => rev' acc
  | k :: ks' =>
      let cur := ins "mov" "q" [mem off "rsp"; reg "rax"] :: rstore_key rc "rax" k in
      rbuffer_slot_copies_acc rc ks' (off + eight) (rev_append cur acc)
  end.

Fixpoint rtyped_result_gprs_acc (rc : rctx) (ts : list key) (rs : list result_reg)
                                (acc : list line) : list line :=
  match ts, rs with
  | [], [] => rev' acc
  | t :: ts', r :: rs' =>
      let cur := match r with RrGpr g => rstore_key rc g t | RrXmm _ _ => [] end in
      rtyped_result_gprs_acc rc ts' rs' (rev_append cur acc)
  | _, _ => rev_append acc (todo "result registers")
  end.

Fixpoint rtyped_result_xmms_acc (rc : rctx) (ts : list key) (rs : list result_reg)
                                (acc : list line) : list line :=
  match ts, rs with
  | [], [] => rev' acc
  | t :: ts', r :: rs' =>
      let cur :=
        match r with
        | RrXmm k x => from_xmm k x "a" ++ rstore_key rc "rax" t
        | RrGpr _ => []
        end in
      rtyped_result_xmms_acc rc ts' rs' (rev_append cur acc)
  | _, _ => rev_append acc (todo "result registers")
  end.

Definition rtyped_result_stores (rc : rctx) (ks : list (class * key)) : list line :=
  match result_registers (map fst ks) ["rdx"; "rcx"] ["xmm0"; "xmm1"] with
  | Some rs => rtyped_result_gprs_acc rc (map snd ks) rs []
               ++ rtyped_result_xmms_acc rc (map snd ks) rs []
  | None => todo "result registers"
  end.

Definition rfast_result (rc : rctx) (r : protocol) (c : channels) : list line :=
  let exc := special_label (rc_cx rc) "exc" in
  let flag := [ins "test" "b" [imm 1; reg "al"]; ins0 "jnz" [sym exc]] in
  match r, c with
  | Registers, ChFloat k d => flag ++ from_xmm k "xmm0" "a" ++ rstore_key rc "rax" (KTmp d)
  | Registers, ChTyped ks => flag ++ rtyped_result_stores rc ks
  | Registers, ChSlots ks => flag ++ rreg_slot_stores_acc rc ks ["rdx"; "rcx"] []
  | Buffer _, ChSlots ks =>
      [ins "cmp" "b" [imm 0; mem 0 "rsp"]; ins0 "jne" [sym exc]]
      ++ rbuffer_slot_copies_acc rc ks eight []
  | Buffer _, _ => todo "buffered result"
  end.

Definition rgeneric_call_arg (rc : rctx) (c : cell) : list line :=
  match c with
  | Cell i k (CellValue v) lower =>
      rload rc v k "a"
      ++ match lower with
         | Some (CellValue p) => rlower_load rc p "rcx"
         | Some (CellSaved _) => todo "saved lower"
         | None => [ins "xor" "l" [reg "ecx"; reg "ecx"]]
         end
      ++ slot_load (rc_cx rc) KThread "rdx"
      ++ cell_stores i "rdx"
  | Cell _ _ (CellSaved _) _ => todo "saved cell"
  end.

Definition rgeneric_slot_copy (rc : rctx) (c : cell) : list line :=
  match c with
  | Cell i _ (CellValue (Tmp d)) lower =>
      ins "mov" "q" [mem (thread_cc_inline_buffer + eight * i) "rsi"; reg "rax"]
      :: rstore_key rc "rax" (KTmp d)
      ++ match lower with
         | Some (CellValue (Tmp l)) =>
             ins "mov" "q" [mem (thread_cc_inline_aux_buffer + eight * i) "rsi"; reg "rax"]
             :: slot_store (rc_cx rc) "rax" (KLower (KTmp l))
         | Some _ => todo "result lower"
         | None => []
         end
  | _ => todo "result cell"
  end.

Definition rgeneric_results (rc : rctx) (need : Z) (results : list cell) (retok : string)
  : list line :=
  match results with
  | [] => if need =? 0 then [] else todo "generic results"
  | _ =>
      slot_load (rc_cx rc) KThread "rsi"
      ++ [ins "cmp" "q" [imm need; reg "rdx"];
          ins0 "jae" [sym retok];
          ins "mov" "q" [reg "rdx"; reg "rdi"];
          ins "mov" "l" [imm need; reg "esi"];
          ins "xor" "l" [reg "edx"; reg "edx"];
          ins0 "call" [plt "filc_cc_rets_check_failure"];
          ins0 "ud2" [];
          label retok]
      ++ flat_map (rgeneric_slot_copy rc) results
  end.

Definition rindirect_call (rc : rctx) (b : name) (index : string) (sig : Z) (r : protocol)
                          (ws : list word) (c : channels) (size : Z) (cells : list cell)
                          (need : Z) (results : list cell) : list line :=
  let cx := rc_cx rc in
  let exc := special_label cx "exc" in
  let generic := local_label cx b index "generic" in
  let done := local_label cx b index "done" in
  [ins "movabs" "q" [imm sig; reg "rsi"];
   ins "cmp" "q" [reg "rsi"; mem function_object_signature "rcx"];
   ins0 "jne" [sym generic]]
  ++ rfast_call rc r ws None
  ++ rfast_result rc r c
  ++ [ins0 "jmp" [sym done]; label generic]
  ++ outline_ensure cx size (local_label cx b index "outline")
  ++ flat_map (rgeneric_call_arg rc) cells
  ++ slot_load cx KThread "rdi"
  ++ slot_load cx KAux "rsi"
  ++ [ins "mov" "l" [imm size; reg "edx"];
      ins "call" "q" [ind (mem function_object_generic_entry "rsi")];
      ins "test" "b" [imm 1; reg "al"];
      ins0 "jnz" [sym exc]]
  ++ rgeneric_results rc need results (local_label cx b index "retok")
  ++ [label done].

Definition rgetter_call (rc : rctx) (target : operand) (d : name) : list line :=
  let cx := rc_cx rc in
  slot_load cx KThread "rdi"
  ++ [ins "lea" "q" [rip (origin_label (cx_name cx) "c"); reg "rsi"];
      ins0 "call" [target];
      ins "mov" "q" [reg "rdx"; reg "rcx"]]
  ++ rflight_store rc d.

Definition rva_arg_load (rc : rctx) (b : name) (index : string) (k : class) (d : name)
  : list line :=
  let cx := rc_cx rc in
  match k with
  | W | Single => ins "mov" "l" [mem 0 "rax"; reg "eax"] :: rstore_key rc "rax" (KTmp d)
  | L | Double => ins "mov" "q" [mem 0 "rax"; reg "rax"] :: rstore_key rc "rax" (KTmp d)
  | Extended => ins "fld" "t" [mem 0 "rax"] :: x87_pop cx d
  | P =>
      let none := local_label cx b index "va_none" in
      let have := local_label cx b index "va_have" in
      [ins "xor" "l" [reg "ecx"; reg "ecx"];
       ins "test" "q" [reg "rdx"; reg "rdx"];
       ins0 "jz" [sym none];
       ins "mov" "q" [mem 0 "rdx"; reg "rcx"];
       ins "test" "b" [imm 1; reg "cl"];
       ins0 "jz" [sym have];
       ins "and" "q" [imm (-2); reg "rcx"];
       ins "mov" "q" [mem 8 "rcx"; reg "rcx"];
       label have; label none;
       ins "mov" "q" [mem 0 "rax"; reg "rax"]]
      ++ rflight_store rc d
  | _ => todo "va_arg class"
  end.

Definition raction_lines (rc : rctx) (b : name) (index : string) (a : action) : list line :=
  let cx := rc_cx rc in
  match a with
  | AOrigin => origin_store cx "c"
  | AReserveResult (Buffer n) => [ins "sub" "q" [imm (buffer_bytes n); reg "rsp"]]
  | AReleaseResult (Buffer n) => [ins "add" "q" [imm (buffer_bytes n); reg "rsp"]]
  | AReserveResult Registers | AReleaseResult Registers => []
  | AInvoke t r ws => rfast_call rc r ws (Some (target_operand t))
  | AResult r c => rfast_result rc r c
  | ACopyFilter _ _ _ _ | ACopyJoin => []
  | ADispatch p sig r ws c size cells need results =>
      rflight_load rc p
      ++ function_check (special_label cx "notfn")
      ++ slot_store cx "rcx" KAux
      ++ rindirect_call rc b index sig r ws c size cells need results
  | AGetter (GetLocal s) d => rgetter_call rc (sym (getter_symbol (name_text s))) d
  | AGetter (GetExternal s) d => rgetter_call rc (plt (getter_symbol (name_text s))) d
  | AGetter (GetWeak s) d =>
      let getter := getter_symbol (name_text s) in
      let null := local_label cx b index "weak_null" in
      let done := local_label cx b index "weak_done" in
      [ins "cmp" "q" [imm 0; gotpcrel getter]; ins0 "je" [sym null]]
      ++ rgetter_call rc (plt getter) d
      ++ [ins0 "jmp" [sym done]; label null;
          ins "xor" "l" [reg "eax"; reg "eax"]; ins "xor" "l" [reg "ecx"; reg "ecx"]]
      ++ rflight_store rc d
      ++ [label done]
  | ASnapshotCursor off d =>
      rflight_load rc (Tmp va_snapshot)
      ++ rload rc (Const off) L "d"
      ++ [ins "add" "q" [reg "rdx"; reg "rax"]]
      ++ rflight_store rc d
  | AConsumeVa k p size d =>
      rflight_load rc p
      ++ [ins "mov" "q" [reg "rax"; reg "rdi"];
          ins "mov" "q" [reg "rcx"; reg "rsi"];
          ins "mov" "l" [imm size; reg "edx"];
          ins "mov" "l" [imm size; reg "ecx"];
          ins0 "call" [plt "filc_get_next_ptr_bytes_for_va_arg"]]
      ++ rva_arg_load rc b index k d
  | AInitializeLocal x =>
      match nm_find x (cx_locals cx) with
      | None => todo "no local"
      | Some s =>
          let words := ls_padded s / eight in
          zero_words (Z.to_nat words) (- ls_payload s)
          ++ zero_words (Z.to_nat words) (eight - ls_aux s)
          ++ [ins "mov" "q" [imm words; mem (- ls_aux s) "rbp"];
              ins "lea" "q" [mem (- ls_aux s) "rbp"; reg "rax"]]
          ++ slot_store cx "rax" (KStackAux x)
      end
  end.

(** ## Emitting instructions, returns, branches and blocks *)

Definition rpinst_lines (rc : rctx) (b : name) (i : Z) (pi : pinst) : list line :=
  let cx := rc_cx rc in
  let index := decimal i in
  match pi with
  | PAbi acts => flat_map (raction_lines rc b index) acts
  | PInst (FPlain (Let d k o args)) => rlet_lines rc b index d k o args
  | PInst (FPlain (Flight d o args lower)) => rflight_lines rc d o args lower
  | PInst (FPlain _) => todo "plain instruction"
  | PInst (FFused (Check _ size r align) a) =>
      match access_place a with
      | AtValue p =>
          rflight_load rc p
          ++ access_check cx (mkKind size (rights_write r) align)
          ++ rraw_access rc b index a
      | AtLocal _ _ => todo "heap check at a local"
      end
  | PInst (FFused (CheckLocal x off size r align) a) =>
      local_check cx b index x off (mkKind size (rights_write r) align)
      ++ rlocal_raw_access rc b index a
  | PInst (FFused _ _) => todo "fused check"
  | PInst (FReused a) =>
      match access_place a with
      | AtValue p =>
          let off := access_offset a in
          match a with
          | ALoadPointer _ _ _ _ =>
              rflight_load rc p
              ++ (if off =? 0 then [] else [ins "add" "q" [imm off; reg "rax"]])
          | _ =>
              match p with
              | Tmp np =>
                  match nm_find np (rc_reg rc) with
                  | Some hrp => [ins "lea" "q" [mem off (hreg64 hrp); reg "rax"]]
                  | None =>
                      rload rc p L "a"
                      ++ (if off =? 0 then [] else [ins "add" "q" [imm off; reg "rax"]])
                  end
              | _ =>
                  rload rc p L "a"
                  ++ (if off =? 0 then [] else [ins "add" "q" [imm off; reg "rax"]])
              end
          end
          ++ rraw_access rc b index a
      | AtLocal _ _ => todo "reused access at a local"
      end
  | PInst (FCall _ _ _) => todo "call that is not lowered"
  end.

Definition reinst_lines (rc : rctx) (b : name) (ei : einst) : list line :=
  match ei with
  | EPlain i pi => rpinst_lines rc b i pi
  | EFlightFused _ i2 _ o args lw ck a =>
      let addr_code := rflight_addr_into rc o args None "rax" in
      let lower_code :=
        match lw with
        | LowerOf p => rlower_load rc p "rcx"
        | LowerNone => [ins "xor" "l" [reg "ecx"; reg "ecx"]]
        end in
      addr_code
      ++ lower_code
      ++ access_check (rc_cx rc) ck
      ++ rraw_access rc b (decimal i2) a
  end.

Fixpoint reinsts_lines_acc (rc : rctx) (b : name) (eis : list einst)
                           (acc : list line) : list line :=
  match eis with
  | [] => rev' acc
  | ei :: eis' => reinsts_lines_acc rc b eis' (rev_append (reinst_lines rc b ei) acc)
  end.

Definition rret_value (rc : rctx) (r : ret_type) (v : value) : list line :=
  match r with
  | RClass P => rload rc v L "d" ++ rlower_load rc v "rcx"
  | RClass W => rload rc v W "d"
  | RClass L => rload rc v L "d"
  | RClass Single => rload rc v Single "a" ++ to_xmm Single "a" "xmm0"
  | RClass Double => rload rc v Double "a" ++ to_xmm Double "a" "xmm0"
  | _ => todo "return class"
  end.

Fixpoint rtyped_return_loads_acc (rc : rctx) (ws : list ret_word) (rs : list result_reg)
                                 (acc : list line) : list line :=
  match ws, rs with
  | [], [] => rev' acc
  | w :: ws', r :: rs' =>
      let cur :=
        match w, r with
        | RwVal k v, RrXmm _ x => rload rc v k "a" ++ to_xmm k "a" x
        | RwVal k v, RrGpr g => rload rc v k g
        | RwAddr v, RrGpr g => rload rc v L g
        | RwLower v, RrGpr g => rlower_load rc v (reg64 g)
        | _, _ => todo "typed return word"
        end in
      rtyped_return_loads_acc rc ws' rs' (rev_append cur acc)
  | _, _ => rev_append acc (todo "typed return words")
  end.

Fixpoint rbuffer_words_acc (rc : rctx) (ws : list word) (off : Z) (acc : list line) : list line :=
  match ws with
  | [] => rev' acc
  | Wf _ s :: ws' =>
      let cur :=
        match s with
        | SrcLower v => rlower_load rc v "rcx" ++ [ins "mov" "q" [reg "rcx"; mem off "rax"]]
        | SrcAddr v | SrcVal _ v => rload rc v L "d" ++ [ins "mov" "q" [reg "rdx"; mem off "rax"]]
        | _ => todo "buffer word"
        end in
      rbuffer_words_acc rc ws' (off + eight) (rev_append cur acc)
  end.

Definition rselected_branch (rc : rctx) (c : cond) (t f : target) (from : name)
                            (next : option name) : list line :=
  let cx := rc_cx rc in
  let t_moves := redge_moves rc from t "t" in
  let f_moves := redge_moves rc from f "f" in
  let t_plain := match t_moves with [] => true | _ => false end in
  let f_plain := match f_moves with [] => true | _ => false end in
  let to_false := jump_if (negated c) (block_label cx (edge_label f)) in
  if to_next t next && t_plain && f_plain then to_false
  else if t_plain then
    jump_if c (block_label cx (edge_label t))
    ++ (if to_next f next then f_moves
        else f_moves ++ [ins0 "jmp" [sym (block_label cx (edge_label f))]])
  else if f_plain then
    to_false
    ++ (if to_next t next then t_moves
        else t_moves ++ [ins0 "jmp" [sym (block_label cx (edge_label t))]])
  else
    let false_label := local_label cx from "jnz" "false" in
    jump_if (negated c) false_label
    ++ t_moves ++ [ins0 "jmp" [sym (block_label cx (edge_label t))]; label false_label]
    ++ (if to_next f next then f_moves
        else f_moves ++ [ins0 "jmp" [sym (block_label cx (edge_label f))]]).

Definition rpjump_lines (rc : rctx) (from : name) (next : option name) (j : pjump)
  : list line :=
  let cx := rc_cx rc in
  match j with
  | PJump (JGoto t) => rselected_edge rc from t "j" next
  | PJump (JBranch v t f) =>
      let test_code :=
        match v with
        | Tmp nv =>
            match nm_find nv (rc_reg rc) with
            | Some hrv => [ins "test" "l" [reg (hreg32 hrv); reg (hreg32 hrv)]]
            | None => rload rc v W "a" ++ [ins "test" "l" [reg "eax"; reg "eax"]]
            end
        | _ => rload rc v W "a" ++ [ins "test" "l" [reg "eax"; reg "eax"]]
        end in
      test_code ++ rselected_branch rc Ne t f from next
  | PJump JUnreachable => [ins0 "jmp" [sym (special_label cx "unreachable")]]
  | PJump _ => todo "a return that is not lowered"
  | PReturnValue r v p => rret_value rc r v ++ frame_pop cx ++ rsuccess rc p
  | PReturnBuffer ws =>
      slot_load cx KRetbuf "rax" ++ rbuffer_words_acc rc ws eight []
      ++ [ins "mov" "b" [imm 0; mem 0 "rax"]]
      ++ frame_pop cx ++ rleave_ret rc
  | PReturnTyped ks vs =>
      let ws := typed_return_words ks vs in
      match result_registers (map ret_word_class ws) ["d"; "c"] ["xmm0"; "xmm1"] with
      | Some rs => rtyped_return_loads_acc rc ws rs []
      | None => todo "result registers"
      end
      ++ frame_pop cx ++ rsuccess rc Registers
  | PReturnRegisters [v1; v2] =>
      rload rc v1 L "d" ++ rload rc v2 L "c" ++ frame_pop cx ++ rsuccess rc Registers
  | PReturnRegisters _ => todo "return_registers"
  | PReturnVoid p => frame_pop cx ++ rsuccess rc p
  end.

Definition rejump_lines (rc : rctx) (from : name) (next : option name) (ej : ejump)
  : list line :=
  match ej with
  | EJumpPlain j => rpjump_lines rc from next j
  | EJumpCmp c ck x y t f =>
      rcompare_flags rc ck x y ++ rselected_branch rc c t f from next
  | EJumpLetCmp _ k1 o1 args1 c ck y t f =>
      let half := match ck with W => true | _ => false end in
      rint_op_into rc o1 k1 args1 None "rax" "eax"
      ++ rcompare_with_reg rc half (reg_name "a" half) y
      ++ rselected_branch rc c t f from next
  end.

Fixpoint reblocks_lines_acc (rc : rctx) (ebs : list eblock) (acc : list line) : list line :=
  match ebs with
  | [] => rev' acc
  | eb :: ebs' =>
      let next := match ebs' with eb' :: _ => Some (eb_label eb') | [] => None end in
      let from := eb_label eb in
      let blk :=
        label (block_label (rc_cx rc) from)
        :: reinsts_lines_acc rc from (eb_insts eb) []
        ++ rejump_lines rc from next (eb_jump eb) in
      reblocks_lines_acc rc ebs' (rev_append blk acc)
  end.

(** ## Top-level function and module emission *)

(** Compile [f] and its ABI [plan] [p] with register allocation,
    returning `None` if [valid_alloc] rejects the assignment. *)
Definition function_code_allocated (f : func) (p : plan) : option (list line) :=
  let bparams := body_params f in
  let '(tmap, cmap, rev_names, _) :=
    number_func_blocks (fn_blocks f)
      (number_params bparams (nm_empty, ZMap.empty class, [], O)) in
  let names := rev' rev_names in
  let reads := plan_read_counts_acc (pl_blocks p) nm_empty in
  let ebs := build_eblocks_acc reads (pl_blocks p) [] in
  let bmap := number_eblocks_labels ebs O nm_empty in
  let rbs := eblocks_to_r_acc tmap bmap O ebs [] in
  let param_tids := names_to_tids tmap (map snd bparams) in
  let va_tid := nm_find va_snapshot tmap in
  let* rm := allocate_regs cmap va_tid param_tids rbs in
  let rc := build_rctx p names cmap rm in
  let cx := rc_cx rc in
  let impl := impl_symbol (pl_sig p) (cx_name cx) in
  let bs := pl_blocks p in
  let kinds := access_check_kinds bs in
  Some ([Dir (DSection SText); p2align 4]
        ++ linkage_globl (pl_linkage p) impl
        ++ [Dir (DType (LSym impl) (LSym "function")); label impl]
        ++ rentry_lines rc p
        ++ reblocks_lines_acc rc ebs []
        ++ [label (special_label cx "exc")]
        ++ rexc_exit_lines rc (pl_return p)
        ++ flat_map (check_fail_block cx) kinds
        ++ not_function_block cx bs
        ++ unreachable_block cx bs
        ++ [Dir (DSize (LSym impl))]
        ++ function_object_lines cx p impl
        ++ origins cx p kinds
        ++ unreachable_message cx bs).

(** Lines of one module [item] under register allocation. *)
Definition item_code_allocated (sy : symbols) (it : item) : option (list line) :=
  match it with
  | IFunc f =>
      let* p := lower_function sy f in
      function_code_allocated f p
  | IOutside _ _ => None
  | IData n lk align items => Some (data_lines n lk align items)
  | IAlias n lk target => Some (alias_lines sy n lk target)
  end.

Definition wrap_single_lines (ls : list line) : list (list line) := [ls].

Definition item_piece_allocated (sy : symbols) (it : item) (_ : unit)
  : option (list (list line)) :=
  option_map wrap_single_lines (item_code_allocated sy it).

Definition thunks_piece_allocated (sy : symbols) (md : module) (_ : unit)
  : option (list (list line)) :=
  option_map (map thunk_lines) (lower_thunks sy md).

(** Pieces of a module compiled with register allocation. *)
Definition module_code_allocated (md : module)
  : list (unit -> option (list (list line))) :=
  let sy := module_symbols md in
  map (item_piece_allocated sy) md
  ++ [thunks_piece_allocated sy md; end_piece].

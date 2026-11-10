(** Fusion, the first step of the Fil-C backend (filc_amd64.pl's
    `fused_blocks/5`): each check of the checked IR and the raw
    access after it, which reads the check's proof, become one
    instruction at one index, the access now at the checked pointer
    itself. A proof is then a register value and needs no frame
    slot. A later access under the same proof is `reused`, with no
    check; a function check fuses with its raw call.

    The first version takes the checks the compiler emits without
    `-O`: `check` (a `check_ahead` is the check of its whole range),
    `check_local` and `check_function`. A function with a renewed,
    half or limit check, which only the optimizer's passes make, is
    refused, as is one the Prolog compiler throws on: an access
    without its check, or pointer arithmetic that is not a flight. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Validate Maps Cfg.
From Backend Require Import Plan.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Before fusion *)

(** As `without_locs/2` and `ahead_as_check/2`: the instructions is
    without their source positions, each `check_ahead` now the
    `check` of its whole range, whose early bytes are tested with the
    access's own. *)
Definition prepared_insts (is : list inst) : list inst :=
  flat_map (fun i => match i with
                     | Loc _ _ => []
                     | Let q A (CheckAhead lo hi r al _) ps => [Let q A (Check lo hi r al) ps]
                     | _ => [i]
                     end) is.

(** A block before fusion. *)
Definition prepared_block (b : block) : block :=
  mkBlock (b_label b) (b_phis b) (prepared_insts (b_insts b)) (b_jump b).

(** ## Proofs that hold in every block *)

(** As `temp_defs/3`, its names: every definition of a temporary, the
    parameters ps, then each block's phis and instructions. *)
Definition defined_names (ps : list (class * name)) (bs : list block) : list name :=
  map snd ps
  ++ flat_map (fun b => map (fun p => match p with Phi d _ _ => d end) (b_phis b)
                        ++ flat_map (fun i => map fst (inst_temp_defs i)) (b_insts b)) bs.

(** The names ns counted: each maps to whether it occurs more than
    once. *)
Definition counted (ns : list name) : nmap bool :=
  fold_left (fun m n => nm_add n (nm_mem n m) m) ns nm_empty.

(** Whether the name n is defined more than once. *)
Definition multiple (m : nmap bool) (n : name) : bool :=
  match nm_find n m with Some b => b | None => false end.

(** As `single_proofs/3`: the proof q mapped to its checked pointer p
    for each heap check `let(tmp(Q), a, check(...), [P])` where q has
    one definition in the function and p, if a temporary, has no more
    than one. Only these may be reused in another block: reloading p
    there gives the value that was checked. *)
Definition single_proofs (ps : list (class * name)) (bs : list block) : nmap value :=
  let multi := counted (defined_names ps bs) in
  fold_left
    (fun m b =>
       fold_left
         (fun m i =>
            match i with
            | Let q A (Check _ _ _ _) (p :: _) =>
                if multiple multi q then m
                else match p with
                     | Tmp n => if multiple multi n then m else nm_add q p m
                     | _ => nm_add q p m
                     end
            | _ => m
            end) (b_insts b) m)
    bs nm_empty.

(** ## A block's proofs *)

(** The proofs of a block so far, as `pr(ByQ, ByP)`: [by_q] maps each
    proof q to its checked pointer, and [by_p] each name n to the
    proofs once paired with `tmp(N)`, so that a new definition of n
    drops its pairs without a scan of the others. *)
Record proofs : Type := mkProofs {
  by_q : nmap value;
  by_p : nmap (list name)
}.

(** As `proofs_empty/1`. *)
Definition proofs_empty : proofs := mkProofs nm_empty nm_empty.

(** As `proofs_add/3`: pr with the proof q of the pointer p. *)
Definition proofs_add (q : name) (p : value) (pr : proofs) : proofs :=
  mkProofs (nm_add q p (by_q pr))
           (match p with
            | Tmp n =>
                nm_add n (q :: match nm_find n (by_p pr) with Some qs => qs | None => [] end)
                       (by_p pr)
            | _ => by_p pr
            end).

(** As `proofs_kill/3`: pr once d is defined again: without d's own
    pair and without each pair whose pointer is `tmp(D)`. Emission
    reloads the pointer from its slot, so its old proofs are of
    another value. *)
Definition proofs_kill (d : name) (pr : proofs) : proofs :=
  let by_q1 := nm_remove d (by_q pr) in
  match nm_find d (by_p pr) with
  | Some qs =>
      mkProofs (fold_left (fun m q => match nm_find q m with
                                      | Some (Tmp n) => if name_eqb n d then nm_remove q m else m
                                      | _ => m
                                      end) qs by_q1)
               (nm_remove d (by_p pr))
  | None => mkProofs by_q1 (by_p pr)
  end.

(** ## Accesses *)

(** Which protocols a fused pointer access may declare: a heap
    object's or a named local's. *)
Inductive storage : Type := Heap | Local.

(** As `proven_access/4` (heap) and `proven_local_access/4` (local):
    the raw access i, which reads the proof q, as the access at the
    place p. A pointer access must declare a protocol of its storage:
    the heap's or the atomic helpers', or the local's. *)
Definition proven_access (st : storage) (i : inst) (q : name) (p : place) : option access :=
  match i with
  | Let d k (RawLoad t off) [Tmp q'] =>
      if name_eqb q' q then Some (ALoad d k t off p) else None
  | RawStore w off v (Tmp q') =>
      if name_eqb q' q then Some (AStore w off v p) else None
  | Let d P (RawLoadPointer off es) [Tmp q'] =>
      if name_eqb q' q
         && match st with
            | Heap => effects_eqb es load_effects || effects_eqb es atomic_load_effects
            | Local => effects_eqb es local_load_effects
            end
      then Some (ALoadPointer d off es p) else None
  | RawStorePointer off v (Tmp q') es =>
      if name_eqb q' q
         && match st with
            | Heap => effects_eqb es store_effects || effects_eqb es atomic_store_effects
            | Local => effects_eqb es local_store_effects
            end
      then Some (AStorePointer off v p es) else None
  | _ => None
  end.

(** As `access_pointer/3`, its offset: the access a is at its place
    plus this. *)
Definition access_offset (a : access) : Z :=
  match a with
  | ALoad _ _ _ off _ | AStore _ off _ _ | ALoadPointer _ off _ _
  | AStorePointer off _ _ _ => off
  end.

(** The proof and the offset of an access that may be `reused`: a
    non-pointer raw load or store, or a pointer load by the heap's
    load protocol. *)
Definition reusable (i : inst) : option (name * Z) :=
  match i with
  | Let _ _ (RawLoad _ off) [Tmp q] => Some (q, off)
  | RawStore _ off _ (Tmp q) => Some (q, off)
  | Let _ P (RawLoadPointer off es) [Tmp q] =>
      if effects_eqb es load_effects then Some (q, off) else None
  | _ => None
  end.

(** As `unchecked_access/1` and `implicit_flight/1`, for the checked
    IR: an instruction that must not reach emission by itself: a raw
    access or call not fused with its check, a call of a pointer, or
    pointer arithmetic outside a flight. *)
Definition not_emitted (i : inst) : bool :=
  match i with
  | Call _ (Tmp _) _ | RawCall _ _ _ | RawStore _ _ _ _ | RawStorePointer _ _ _ _ => true
  | Let _ _ (RawLoad _ _) _ | Let _ _ (RawLoadPointer _ _) _ => true
  | Let _ P (Add | Sub | Itop) _ => true
  | Let _ P Copy [Tmp _] | Let _ P Copy [Const _] => true
  | _ => false
  end.

(** Whether `access_check//2` can emit the check c: of the bytes from
    the pointer up to a positive size below 2^31, aligned to 1, 2, 4
    or 8. *)
Definition emitted_check (c : op) : bool :=
  match c with
  | Check 0 size _ al =>
      (0 <? size) && (size <=? 2147483647)
      && ((al =? 1) || (al =? 2) || (al =? 4) || (al =? 8))
  | _ => false
  end.

(** ## Fusing *)

(** As `fused_inst/5`: the instruction i fused with the one after it
    in rest, if it is a check, and whether that one was taken.
    Nothing if i is a check without its access, a check the first
    version does not emit, or an instruction that is [not_emitted]. *)
Definition fused_inst (i : inst) (rest : list inst) : option (finst * bool) :=
  match i with
  | Let q A ((CheckLocal x off _ _ _) as c) [] =>
      match rest with
      | next :: _ =>
          let* a := proven_access Local next q (AtLocal x off) in
          if access_offset a =? 0 then Some (FFused c a, true) else None
      | [] => None
      end
  | Let q A c [p] =>
      match rest with
      | next :: _ =>
          let* a := proven_access Heap next q (AtValue p) in
          if emitted_check c && (access_offset a =? 0) then Some (FFused c a, true) else None
      | [] => None
      end
  | Let _ A _ _ => None
  | Let q F CheckFunction [p] =>
      match rest with
      | RawCall res (Tmp q') args :: _ =>
          if name_eqb q' q then Some (FCall res p args, true) else None
      | _ => None
      end
  | _ => if not_emitted i then None else Some (FPlain i, false)
  end.

(** One step of `fused_insts/5`: the instruction i under the block's
    proofs pr and the function's single proofs. An access whose proof
    is among them is `reused`, at the proof's pointer, if its offset
    fits 32 bits; anything else is [fused_inst]'s. *)
Definition fused_step (single : nmap value) (pr : proofs) (i : inst) (rest : list inst)
  : option (finst * bool) :=
  let found :=
    match reusable i with
    | Some (q, off) =>
        match nm_find q (by_q pr) with
        | Some p => Some (q, off, p)
        | None => match nm_find q single with
                  | Some p => Some (q, off, p)
                  | None => None
                  end
        end
    | None => None
    end in
  match found with
  | Some (q, off, p) =>
      if (-2147483648 <=? off) && (off <=? 2147483647)
      then let* a := proven_access Heap i q (AtValue p) in Some (FReused a, false)
      else None
  | None => fused_inst i rest
  end.

(** As `fused_insts/5`: the instructions is fused, in front of the
    reversed acc. Each instruction's definition first forgets the
    proofs it invalidates; a check then adds its own; and what the
    fused instruction defines, a load's destination perhaps, forgets
    again. *)
Fixpoint fused_insts (single : nmap value) (is : list inst) (pr : proofs) (acc : list finst)
  : option (list finst) :=
  match is with
  | [] => Some (rev' acc)
  | i :: rest =>
      let pr0 := match inst_def_first i with
                 | Some d => proofs_kill d pr
                 | None => pr
                 end in
      let pr1 := match i with
                 | Let q A (Check _ _ _ _) [p] => proofs_add q p pr0
                 | _ => pr0
                 end in
      let* r := fused_step single pr0 i rest in
      let fi := fst r in
      let pr2 := fold_left (fun pr d => proofs_kill (fst d) pr) (finst_defs fi) pr1 in
      match snd r, rest with
      | true, _ :: rest' => fused_insts single rest' pr2 (fi :: acc)
      | _, _ => fused_insts single rest pr2 (fi :: acc)
      end
  end.

(** A block after fusion: its instructions are [finst]s. *)
Record fblock : Type := mkFBlock {
  fb_label : name;
  fb_phis : list phi;
  fb_insts : list finst;
  fb_jump : jump
}.

(** As `fused_blocks/5`: the blocks bs of a function with the
    parameters ps, fused. `fused_blocks/5` also throws unless every
    cycle polls, which is the validator's to check here. *)
Definition fused_blocks (ps : list (class * name)) (bs : list block) : option (list fblock) :=
  let bs1 := map prepared_block bs in
  let single := single_proofs ps bs1 in
  all_some (fun b => let* is := fused_insts single (b_insts b) proofs_empty [] in
                     Some (mkFBlock (b_label b) (b_phis b) is (b_jump b))) bs1.

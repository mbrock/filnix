(** The interpreter in [CpuAbs](CpuAbs.v) follows one path of a function
    on abstract values and stops at chosen labels, which this module
    calls cuts. A function with loops needs an invariant at every cut,
    so that a path which returns to the cut can stop there. This module
    finds those invariants by running the function until the states at
    its cuts stop growing, and it then checks that every path from the
    entry or from a cut ends at a return or inside an invariant.

    This module is not proved sound, and neither is the interpreter it
    drives. It states no theorem about a program. A function that
    passes [check] has been examined by an unproved program, and the
    soundness proof is being written. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Maps.
From Glibc Require Import CpuAbs.
Import ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

(** * Liveness, as bit sets *)

Definition value_names (v : value) : list name := match v with Tmp n => [n] | _ => [] end.

Definition inst_uses (i : inst) : list name :=
  match i with
  | Let _ _ _ args => flat_map value_names args
  | Flight _ _ args lw =>
      flat_map (fun a => match a with FValue v | FAddress v => value_names v end) args
      ++ match lw with LowerOf p => value_names p | LowerNone => [] end
  | RawStore _ _ v a => value_names v ++ value_names a
  | RawStorePointer _ v a _ => value_names v ++ value_names a
  | Call _ c args | RawCall _ c args =>
      value_names c ++ flat_map (fun a => match a with Arg _ v => value_names v end) args
  | _ => []
  end.

Definition inst_defs (i : inst) : list name :=
  match i with
  | Let d _ _ _ | Flight d _ _ _ => [d]
  | Call r _ _ | RawCall r _ _ =>
      match r with CVoid => [] | CResult d _ => [d] | CTuple rs => map fst rs end
  | _ => []
  end.

Definition jump_uses (j : jump) : list name :=
  match j with
  | JBranch v _ _ | JRet v => value_names v
  | JRets vs => flat_map value_names vs
  | _ => []
  end.

Definition jump_succs (j : jump) : list name :=
  match j with
  | JGoto t => [edge_label t]
  | JBranch _ t1 t2 => [edge_label t1; edge_label t2]
  | _ => []
  end.

Definition var_table (f : func) : list name * nmap Z :=
  let add (acc : list name * nmap Z * Z) (n : name) :=
    let '(l, m, k) := acc in
    if nm_mem n m then acc else (n :: l, nm_add n k m, k + 1) in
  let defs := map snd (fn_params f)
              ++ flat_map (fun b => map (fun ph => match ph with Phi d _ _ => d end) (b_phis b)
                                    ++ flat_map inst_defs (b_insts b)) (fn_blocks f) in
  let '(l, m, _) := fold_left add defs ([], nm_empty, 0) in (l, m).

Definition bits (m : nmap Z) (ns : list name) : Z :=
  fold_left (fun acc n => match nm_find n m with Some k => Z.setbit acc k | None => acc end) ns 0.

Definition minus (a b : Z) : Z := Z.land a (Z.lnot b).

(** A block has one set of names that it reads before writing them and
    one set of names that it writes. *)
Definition block_use_def (m : nmap Z) (b : block) : Z * Z :=
  let '(u, d) := fold_left (fun acc i =>
                              let '(u, d) := acc in
                              (Z.lor u (minus (bits m (inst_uses i)) d), Z.lor d (bits m (inst_defs i))))
                           (b_insts b) (0, 0) in
  (Z.lor u (minus (bits m (jump_uses (b_jump b))) d), d).

Definition phi_defs (m : nmap Z) (b : block) : Z :=
  bits m (map (fun ph => match ph with Phi d _ _ => d end) (b_phis b)).

Definition phi_uses (m : nmap Z) (b : block) (pred : name) : Z :=
  bits m (flat_map (fun ph => match ph with
                              | Phi _ _ pairs => match lookup pred pairs with
                                                 | Some v => value_names v
                                                 | None => []
                                                 end
                              end) (b_phis b)).

Definition live_round (m : nmap Z) (f : func) (ud : list (Z * Z)) (li : nmap Z) : nmap Z * bool :=
  fold_left (fun acc bu =>
               let '(li, ch) := acc in
               let b := fst bu in
               let '(u, d) := snd bu in
               let lo := fold_left (fun acc s =>
                                      match find_block s (fn_blocks f) with
                                      | Some sb =>
                                          let ls := match nm_find s li with Some z => z | None => 0 end in
                                          Z.lor acc (Z.lor (minus ls (phi_defs m sb)) (phi_uses m sb (b_label b)))
                                      | None => acc
                                      end) (jump_succs (b_jump b)) 0 in
               let new := Z.lor u (minus lo d) in
               let old := match nm_find (b_label b) li with Some z => z | None => 0 end in
               if new =? old then (li, ch) else (nm_add (b_label b) new li, true))
            (rev (combine (fn_blocks f) ud)) (li, false).

Fixpoint live_fix (n : nat) (m : nmap Z) (f : func) (ud : list (Z * Z)) (li : nmap Z) : nmap Z :=
  match n with
  | O => li
  | Datatypes.S n' => let '(li', ch) := live_round m f ud li in
                      if ch then live_fix n' m f ud li' else li'
  end.

(** An invariant only needs the temporaries that later code reads, so
    [liveness] computes the names that are live after the phis of each block. *)
Definition liveness (f : func) : name -> list name :=
  let '(vars, m) := var_table f in
  let ud := map (block_use_def m) (fn_blocks f) in
  let li := live_fix 200 m f ud nm_empty in
  fun l => match nm_find l li with
           | Some z => filter (fun n => match nm_find n m with Some k => Z.testbit z k | None => false end) vars
           | None => []
           end.

(** * Cut labels *)

Definition pred_table (f : func) : nmap (list name) :=
  fold_left (fun acc b =>
               fold_left (fun acc s =>
                            nm_add s (b_label b :: match nm_find s acc with Some l => l | None => [] end) acc)
                         (jump_succs (b_jump b)) acc) (fn_blocks f) nm_empty.

Fixpoint before (l p : name) (bs : list block) : bool :=
  match bs with
  | [] => false
  | b :: bs' => if name_eqb (b_label b) l then true
                else if name_eqb (b_label b) p then false else before l p bs'
  end.

(** A block that two edges enter is a cut, unless it only chooses between
    them by phis and none of its predecessors follows it in the layout. *)
Definition default_cuts (f : func) : list name :=
  let pt := pred_table f in
  flat_map (fun b =>
              match nm_find (b_label b) pt with
              | Some (p1 :: p2 :: ps) =>
                  if match b_insts b with [] => false | _ => true end
                     || existsb (fun p => before (b_label b) p (fn_blocks f)) (p1 :: p2 :: ps)
                  then [b_label b] else []
              | _ => []
              end) (fn_blocks f).

(** * Joins of closed states *)

Fixpoint insert_sorted (z : Z) (l : list Z) : list Z :=
  match l with
  | [] => [z]
  | x :: l' => if z <? x then z :: l else if z =? x then l else x :: insert_sorted z l'
  end.

(** A growing interval is widened to the next threshold. The thresholds of
    a function are the constants it compares against and their neighbours. *)
Definition thresholds (f : func) : list Z :=
  fold_left (fun acc z => insert_sorted (z - 1) (insert_sorted z (insert_sorted (z + 1) acc)))
    (flat_map (fun b => flat_map (fun i => match i with
                                           | Let _ _ (Cmp _ _) [_; Const c] | Let _ _ (Cmp _ _) [Const c; _] => [c]
                                           | _ => []
                                           end) (b_insts b)) (fn_blocks f)) [].

Definition up_to (ths : list Z) (h : Z) : Z :=
  match find (fun t => h <=? t) ths with
  | Some t => t
  | None => if h <? 2 ^ 32 then 2 ^ 32 - 1 else Z.max h (2 ^ 64 - 1)
  end.

Definition down_to (ths : list Z) (l : Z) : Z :=
  match find (fun t => t <=? l) (rev ths) with Some t => Z.max 0 t | None => Z.min 0 l end.

Definition wide (w : option (list Z)) (lo hi lo' hi' : Z) : Z * Z :=
  let l := Z.min lo lo' in
  let h := Z.max hi hi' in
  match w with
  | Some ths => (if l <? lo then down_to ths l else l, if hi <? h then up_to ths h else h)
  | None => (l, h)
  end.

Definition join_val (w : option (list Z)) (a b : cval) : option cval :=
  match a, b with
  | CI lo hi, CI lo' hi' => let (l, h) := wide w lo hi lo' hi' in Some (CI l h)
  | CI _ _, CJ | CJ, CI _ _ | CJ, CJ => Some CJ
  | CP o lo hi, CP o' lo' hi' =>
      if Nat.eqb o o' then let (l, h) := wide w lo hi lo' hi' in Some (CP o l h) else Some CA
  | CN lo hi, CN lo' hi' => let (l, h) := wide w lo hi lo' hi' in Some (CN l h)
  | CF g, CF g' => if name_eqb g g' then Some a else Some CA
  | (CI _ _ | CJ), _ | _, (CI _ _ | CJ) => None
  | _, _ => Some CA
  end.

Definition st0 (osx : bool) : astate := mkSt [] [] [] [] osx.

Definition join_byte (w : option (list Z)) (osx osx' : bool) (a b : abyte) : abyte :=
  match a, b with
  | BX, _ => if byte_le (st0 osx') b BX then BX else BR
  | _, BX => if byte_le (st0 osx) a BX then BX else BR
  | (BK _ | BIn _ _), (BK _ | BIn _ _) =>
      let (lo, hi) := byte_rng (st0 false) a in
      let (lo', hi') := byte_rng (st0 false) b in
      if (lo =? lo') && (hi =? hi') then a
      else let (l, h) := wide w lo hi lo' hi' in if (0 <=? l) && (h <? 256) then BIn l h else BR
  | _, _ => BR
  end.

Definition join_aux (a b : aaux) : aaux :=
  match a, b with
  | XNone, XNone => XNone
  | XObj o, XObj o' => if Nat.eqb o o' then a else XAny
  | _, _ => XAny
  end.

Fixpoint zip2 {A : Type} (f : A -> A -> A) (xs ys : list A) : list A :=
  match xs, ys with
  | x :: xs', y :: ys' => f x y :: zip2 f xs' ys'
  | _, _ => []
  end.

Definition join_obj (w : option (list Z)) (osx osx' : bool) (a b : option aobj) : option aobj :=
  match a, b with
  | Some x, Some y =>
      if Bool.eqb (o_ro x) (o_ro y) && (o_align x =? o_align y)
         && Nat.eqb (length (o_bytes x)) (length (o_bytes y)) then
        Some (mkObj (o_ro x) (o_align x) (zip2 (join_byte w osx osx') (o_bytes x) (o_bytes y))
                (zip2 join_aux (o_aux x) (o_aux y)))
      else None
  | _, _ => None
  end.

Definition join_state (w : option (list Z)) (a b : cstate) : cstate :=
  mkCs (flat_map (fun nc => match lookup (fst nc) (cs_env b) with
                            | Some c => match join_val w (snd nc) c with
                                        | Some j => [(fst nc, j)]
                                        | None => []
                                        end
                            | None => []
                            end) (cs_env a))
       (zip2 (join_obj w (cs_osx a) (cs_osx b)) (cs_objs a) (cs_objs b))
       (cs_osx a && cs_osx b).

Definition cval_le (a b : cval) : bool :=
  match a, b with
  | CI lo hi, CI lo' hi' => (lo' <=? lo) && (hi <=? hi')
  | (CI _ _ | CJ), CJ => true
  | CP o lo hi, CP o' lo' hi' => Nat.eqb o o' && (lo' <=? lo) && (hi <=? hi')
  | CN lo hi, CN lo' hi' => (lo' <=? lo) && (hi <=? hi')
  | (CP _ _ _ | CN _ _ | CA | CF _), CA => true
  | CF g, CF g' => name_eqb g g'
  | _, _ => false
  end.

Definition cs_le (a b : cstate) : bool :=
  forallb (fun nc => match lookup (fst nc) (cs_env a) with
                     | Some c => cval_le c (snd nc)
                     | None => false
                     end) (cs_env b)
  && objs_le (st0 (cs_osx a)) (cs_objs a) (cs_objs b) && implb (cs_osx b) (cs_osx a).

Definition close_state (live : list name) (st : astate) : cstate :=
  mkCs (flat_map (fun n => match lookup n (st_env st) with
                           | Some v => [(n, close_val st v)]
                           | None => []
                           end) live)
       (map (option_map (close_obj st)) (st_objs st)) (st_osx st).

(** * Running a function from a specification *)

Section infer.
Variable gobjs : list name.
Variable fnames : list name.
Variable specs : name -> list fspec.
Variable f : func.
Variable cuts : list name.
Variable fuel : nat.

Definition pad {A : Type} (n : nat) (l : list (option A)) : list (option A) :=
  l ++ repeat None (n - length l).

Definition entry_state (sp : fspec) : astate :=
  fold_left (fun st pc =>
               let (v, st') := open_val (snd pc) st in
               bind st' (snd (fst pc)) v)
            (combine (fn_params f) (sp_args sp))
            (mkSt [] [] [] (pad (nglob gobjs + length (fn_params f)) (map (option_map open_obj) (sp_pre sp)))
                  (sp_osx sp)).

Definition entry_label : name :=
  match fn_blocks f with b :: _ => b_label b | [] => TAtom "" end.

Definition run_entry (sp : fspec) : list leaf :=
  run gobjs fnames specs f cuts fuel entry_label None (entry_state sp).

Definition run_cut (l : name) (t : cstate) : list leaf :=
  match find_block l (fn_blocks f) with
  | Some b => body gobjs fnames specs f cuts fuel l (b_insts b) (b_jump b) (open_state t)
  | None => [LFail l None (open_state t)]
  end.

Record entry : Type := mkEntry {
  e_lab : name; e_key : list (option Z); e_inv : cstate; e_dirty : bool; e_count : nat
}.

Record acc : Type := mkAcc {
  a_tab : list entry;
  a_ret : option (option cval * cstate);
  a_fail : list (name * option inst)
}.

Variable live : name -> list name.
Variable delay : nat.
Variable ths : list Z.
Variable split : list name.

(** The constants a state gives the names that keep invariants apart. *)
Definition state_key (st : astate) : list (option Z) :=
  map (fun v => match lookup v (st_env st) with
                | Some (VI a) => let (lo, hi) := rng st a in if lo =? hi then Some lo else None
                | _ => None
                end) split.

Definition key_eqb (a b : list (option Z)) : bool :=
  all2 (fun x y => match x, y with
                   | Some u, Some v => u =? v
                   | None, None => true
                   | _, _ => false
                   end) a b.

Fixpoint merge_cut (l : name) (k : list (option Z)) (c : cstate) (tab : list entry) : list entry :=
  match tab with
  | [] => [mkEntry l k c true 1]
  | e :: tab' =>
      if name_eqb (e_lab e) l && key_eqb (e_key e) k then
        if cs_le c (e_inv e) then tab
        else mkEntry l k (join_state (if Nat.ltb delay (e_count e) then Some ths else None) (e_inv e) c)
                     true (Datatypes.S (e_count e)) :: tab'
      else e :: merge_cut l k c tab'
  end.

Definition merge_ret (v : option aval) (st : astate) (r : option (option cval * cstate))
  : option (option cval * cstate) :=
  let c := close_state [] st in
  let cv := option_map (close_val st) v in
  match r with
  | None => Some (cv, c)
  | Some (cv', c') =>
      Some (match cv, cv' with
            | Some x, Some y => join_val None y x
            | _, _ => None
            end, join_state None c' c)
  end.

Definition merge_leaf (a : acc) (lf : leaf) : acc :=
  match lf with
  | LCut l st => mkAcc (merge_cut l (state_key st) (close_state (live l) st) (a_tab a)) (a_ret a) (a_fail a)
  | LRet v st => mkAcc (a_tab a) (merge_ret v st (a_ret a)) (a_fail a)
  | LFail l i _ => mkAcc (a_tab a) (a_ret a) ((l, i) :: a_fail a)
  end.

Variable pos : name -> Z.

(** The dirty entry earliest in the layout runs next, so that a loop settles
    before the code after it is run again. *)
Fixpoint pick (tab : list entry) (best : option entry) : option entry :=
  match tab with
  | [] => best
  | e :: tab' =>
      pick tab' (if e_dirty e then
                   match best with
                   | Some b => if pos (e_lab e) <? pos (e_lab b) then Some e else best
                   | None => Some e
                   end
                 else best)
  end.

Fixpoint clean (e0 : entry) (tab : list entry) : list entry :=
  match tab with
  | [] => []
  | e :: tab' =>
      if name_eqb (e_lab e) (e_lab e0) && key_eqb (e_key e) (e_key e0)
      then mkEntry (e_lab e) (e_key e) (e_inv e) false (e_count e) :: tab'
      else e :: clean e0 tab'
  end.

Fixpoint rounds (n : nat) (a : acc) : acc :=
  match n with
  | O => a
  | Datatypes.S n' =>
      match pick (a_tab a) None, a_fail a with
      | Some e, [] =>
          rounds n' (fold_left merge_leaf (run_cut (e_lab e) (e_inv e))
                               (mkAcc (clean e (a_tab a)) (a_ret a) (a_fail a)))
      | _, _ => a
      end
  end.

Definition infer (sp : fspec) (n : nat) : acc :=
  rounds n (fold_left merge_leaf (run_entry sp) (mkAcc [] None [])).

(** A finished run turns the states at its returns into the postcondition
    of the specification it started from. *)
Definition complete (sp : fspec) (a : acc) : fspec :=
  match a_ret a with
  | Some (rv, c) =>
      mkSpec (sp_args sp) (sp_pre sp) (sp_osx sp)
             (zip2 (fun p q => match p with Some _ => q | None => None end) (sp_pre sp) (cs_objs c))
             (cs_osx c) rv
  | None => sp
  end.

(** * Checking a function against a specification and its invariants *)

Definition ret_ok (sp : fspec) (v : option aval) (st : astate) : bool :=
  match v, sp_ret sp with
  | Some x, Some c => val_le st x c
  | None, None => true
  | _, _ => false
  end
  && objs_le st (st_objs st) (sp_post sp) && implb (sp_osx' sp) (st_osx st).

Definition leaf_ok (sp : fspec) (inv : list (name * cstate)) (lf : leaf) : bool :=
  match lf with
  | LCut l st => existsb (fun lt => name_eqb (fst lt) l && entails st (snd lt)) inv
  | LRet v st => ret_ok sp v st
  | LFail _ _ _ => false
  end.

Definition verify (sp : fspec) (inv : list (name * cstate)) : bool :=
  forallb (leaf_ok sp inv) (run_entry sp)
  && forallb (fun lt => forallb (leaf_ok sp inv) (run_cut (fst lt) (snd lt))) inv.

End infer.

(** The functions below infer the invariants of one function and then
    check them, in one call. *)
Definition layout (f : func) : name -> Z :=
  let m := fst (fold_left (fun acc b => (nm_add (b_label b) (snd acc) (fst acc), snd acc + 1)) (fn_blocks f)
                          (nm_empty, 0)) in
  fun l => match nm_find l m with Some k => k | None => 0 end.

Definition plan (gobjs fnames : list name) (specs : name -> list fspec) (f : func) (nocut split : list name)
    (fuel n delay : nat) (sp : fspec) : acc :=
  let cuts := filter (fun l => negb (mem_name l nocut)) (default_cuts f) in
  infer gobjs fnames specs f cuts fuel (liveness f) delay (thresholds f) split (layout f) sp n.

Definition check (gobjs fnames : list name) (specs : name -> list fspec) (f : func) (nocut split : list name)
    (fuel n delay : nat) (sp : fspec) : bool :=
  let cuts := filter (fun l => negb (mem_name l nocut)) (default_cuts f) in
  let a := plan gobjs fnames specs f nocut split fuel n delay sp in
  verify gobjs fnames specs f cuts fuel sp (map (fun e => (e_lab e, e_inv e)) (a_tab a)).

(** A caller uses the completed specification only when it passes the check. *)
Definition solve (gobjs fnames : list name) (specs : name -> list fspec) (f : func) (nocut split : list name)
    (fuel n delay : nat) (sp : fspec) : option fspec :=
  let cuts := filter (fun l => negb (mem_name l nocut)) (default_cuts f) in
  let a := plan gobjs fnames specs f nocut split fuel n delay sp in
  let sp' := complete sp a in
  match a_fail a with
  | [] => if verify gobjs fnames specs f cuts fuel sp' (map (fun e => (e_lab e, e_inv e)) (a_tab a))
          then Some sp' else None
  | _ => None
  end.

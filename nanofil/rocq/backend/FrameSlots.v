(** Stack slots for temporaries (frame_slots.pl's `temp_slots/7`,
    with shared pools): each temporary gets a slot of its pool, and
    two whose live intervals are strictly disjoint may share one.

    A temporary's interval is closed. It covers every write, even of
    a dead result, every use by an instruction, and every block
    boundary where the temporary is live in or out. One instruction
    is one point, with all its helper calls, so a result never
    overwrites its operands. The slots are found first-fit over the
    intervals in the standard order of `range(Start, End, Pool, N)`,
    which makes the layout the Prolog compiler's, slot for slot. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Validate Maps Cfg.
From Backend Require Import Order Plan Fuse Liveness.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Touches *)

(** A group of temporaries touched at one point: an instruction's
    uses or definitions, a block's phis, or the temporaries live into
    or out of a block. *)
Inductive touch : Type :=
| TouchPlain (ns : list name)
| TouchLiveIn (ns : names) (* `live(in, Ns)` *)
| TouchLiveOut (ns : names). (* `live(out, Ns)` *)

(** As `inst_ranges/5`: the touches of the instructions is from the
    point p, each instruction's uses and definitions at its own
    point, in front of acc, the last first. With them, the point
    after the last instruction. *)
Definition inst_touches (is : list finst) (p : Z) (acc : list (touch * Z))
  : Z * list (touch * Z) :=
  fold_left (fun st i =>
               let q := fst st in
               (q + 1, (TouchPlain (map fst (finst_defs i)), q)
                         :: (TouchPlain (finst_uses i), q) :: snd st))
            is (p, acc).

(** As `block_ranges/8`: the touches of the blocks bs from the point
    p, in front of acc, the last first, and the point after the last
    block. A block's live-in set and phis are at its own point, the
    jump's uses and the live-out set at its exit. The live sets keep
    only what can move a bound: the live-in set less prev_out, the
    live-out set of the block before, and the live-out set less the
    next block's live-in set. *)
Fixpoint block_touches (bs : list fblock) (live_in live_outs : nmap names) (prev_out : names)
                       (p : Z) (acc : list (touch * Z)) : Z * list (touch * Z) :=
  match bs with
  | [] => (p, acc)
  | b :: bs' =>
      let new_in := nsubtract (names_at live_in (fb_label b)) prev_out in
      let phi_names := map (fun ph => match ph with Phi d _ _ => d end) (fb_phis b) in
      let r := inst_touches (fb_insts b) (p + 1)
                            ((TouchPlain phi_names, p) :: (TouchLiveIn new_in, p) :: acc) in
      let exit := fst r in
      let out := names_at live_outs (fb_label b) in
      let next_in := match bs' with
                     | next :: _ => names_at live_in (fb_label next)
                     | [] => []
                     end in
      block_touches bs' live_in live_outs out (exit + 1)
                    ((TouchLiveOut (nsubtract out next_in), exit)
                       :: (TouchPlain (jump_uses (fb_jump b)), exit) :: snd r)
  end.

(** As `first_touches/3`: each temporary mapped to the point of its
    first touch in ts. The live-in groups are left out if skip_in,
    else the live-out ones: a live-out set never moves a first touch,
    nor a live-in set a last one. *)
Definition first_touches (skip_in : bool) (ts : list (touch * Z)) : nmap Z :=
  fold_left
    (fun m t =>
       let touched := fun ns => fold_left (fun m n => if nm_mem n m then m else nm_add n (snd t) m)
                                          ns m in
       match fst t with
       | TouchPlain ns => touched ns
       | TouchLiveIn ns => if skip_in then m else touched ns
       | TouchLiveOut ns => if skip_in then touched ns else m
       end)
    ts nm_empty.

(** ## Ranges *)

(** As `range(Start, End, Pool, N)`: the temporary n, of the pool,
    is live from the point start to the point stop, both included. *)
Record range : Type := mkRange {
  rg_start : Z;
  rg_stop : Z;
  rg_pool : pool;
  rg_name : name
}.

(** As `class_pool/3` with shared pools: the pool a temporary of the
    class k is kept in. A proof has none. *)
Definition class_pool (k : class) : option pool :=
  match k with
  | P => Some PoolPointer
  | W | L | Single | Double => Some PoolScalar
  | Extended => Some PoolWide
  | A | F => None
  end.

(** The place of a pool's atom in the standard order: `pointer`,
    `scalar`, `wide`. *)
Definition pool_rank (p : pool) : Z :=
  match p with PoolPointer => 0 | PoolScalar => 1 | PoolWide => 2 end.

(** The standard order of two `range(Start, End, Pool, N)` terms. *)
Definition range_compare (r r' : range) : Datatypes.comparison :=
  match Z.compare (rg_start r) (rg_start r') with
  | Datatypes.Eq => match Z.compare (rg_stop r) (rg_stop r') with
          | Datatypes.Eq => match Z.compare (pool_rank (rg_pool r)) (pool_rank (rg_pool r')) with
                  | Datatypes.Eq => term_compare (rg_name r) (rg_name r')
                  | c => c
                  end
          | c => c
          end
  | c => c
  end.

(** The name of a variadic function's hidden parameter, the promoted
    argument packet: `hidden(va_snapshot)`. *)
Definition va_snapshot : name := TApp "hidden" [TAtom "va_snapshot"].

(** As `temp_ranges/7`: the live range of each of temps, the
    temporaries of a function with the parameters ps and the blocks
    bs, in the standard order. The parameters are touched at point 0
    and the blocks start at 1. The hidden `va_snapshot` parameter is
    read by every `va_args`, so it is kept to the end. *)
Definition temp_ranges (ps : list (class * name)) (bs : list fblock)
                       (temps : list (name * class)) : option (list range) :=
  let* live := temp_liveness bs in
  let r := block_touches bs (fst live) (snd live) [] 1 [(TouchPlain (map snd ps), 0)] in
  let backwards :=
    if existsb (fun p => class_eqb (fst p) P && name_eqb (snd p) va_snapshot) ps
    then (TouchPlain [va_snapshot], fst r) :: snd r
    else snd r in
  let lo := first_touches false (rev' backwards) in
  let hi := first_touches true backwards in
  let* ranges := all_some (fun t => let* start := nm_find (fst t) lo in
                                      let* stop := nm_find (fst t) hi in
                                      let* pool := class_pool (snd t) in
                                      Some (mkRange start stop pool (fst t))) temps in
  Some (sort range_compare ranges).

(** ## Slots *)

(** As `reuse_slot/7`: the slot for a range from s to e among
    slots, each a slot's index and the end of the last range in it,
    of which there are n0. It is the first whose last range ends
    before s, or a new one. The result is the slots now, their
    number, and the index taken. *)
Fixpoint reuse_slot (slots : list (Z * Z)) (s e n0 : Z) : list (Z * Z) * Z * Z :=
  match slots with
  | [] => ([(n0, e)], n0 + 1, n0)
  | (i0, e0) :: slots' =>
      if e0 <? s then ((i0, e) :: slots', n0, i0)
      else match reuse_slot slots' s e n0 with
           | (tail, n, i) => ((i0, e0) :: tail, n, i)
           end
  end.

(** The slots of a function's temporaries: the slot of each, by
    name, in the order of the names, and the number of slots of each
    pool. *)
Record slots : Type := mkSlots {
  sl_aliases : list (name * (pool * Z));
  sl_scalars : Z;
  sl_pointers : Z;
  sl_wides : Z
}.

(** A pool while its ranges are allocated: its slots and their
    number. *)
Definition pool_state : Type := (list (Z * Z) * Z)%type.

(** As `allocate/6` and `wide_slot/3`: the ranges rs, in order, each
    given a slot of its pool. *)
Definition allocate (rs : list range) : slots :=
  let step :=
    fun (st : pool_state * pool_state * pool_state * list (name * (pool * Z))) (r : range) =>
      match st with
      | (sc, pt, wd, acc) =>
          let take := fun (ps : pool_state) => reuse_slot (fst ps) (rg_start r) (rg_stop r) (snd ps) in
          match rg_pool r with
          | PoolScalar => match take sc with
                          | (ss, n, i) => ((ss, n), pt, wd, (rg_name r, (PoolScalar, i)) :: acc)
                          end
          | PoolPointer => match take pt with
                           | (ss, n, i) => (sc, (ss, n), wd, (rg_name r, (PoolPointer, i)) :: acc)
                           end
          | PoolWide => match take wd with
                        | (ss, n, i) => (sc, pt, (ss, n), (rg_name r, (PoolWide, i)) :: acc)
                        end
          end
      end in
  match fold_left step rs (([], 0), ([], 0), ([], 0), []) with
  | (sc, pt, wd, acc) =>
      mkSlots (sort (fun a b => term_compare (fst a) (fst b)) acc) (snd sc) (snd pt) (snd wd)
  end.

(** As `temp_slots/7`: the slots of temps, the temporaries of a
    function with the parameters ps and the fused blocks bs. *)
Definition temp_slots (ps : list (class * name)) (bs : list fblock)
                      (temps : list (name * class)) : option slots :=
  let* rs := temp_ranges ps bs temps in
  Some (allocate rs).

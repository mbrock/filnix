(** Integer arithmetic and the evaluation of ops, transcribed from
    interp.pl's Operations section: `alu/4`, `additive_res/4` and
    `kind_res/8` for the core subset.

    Integers of class K are 0..2^bits(K)-1; signed readings, shift
    counts and divisions follow the interpreter clause by clause. Fil-C
    defines division by zero as 0 and `MIN / -1` as `MIN` (docs/ub.md),
    so integer arithmetic never has undefined behaviour here.

    `op_res` gives an op's partial result, or asks for an allocation:
    `alloc` is the only op whose result depends on a choice, the fresh
    base of its object (Memory.v's `fresh`). *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory.
Import ListNotations.
Open Scope Z_scope.

Notation "'let*' x ':=' e 'in' b" :=
  (match e with Some x => b | None => None end)
  (at level 200, x name, e at level 100, b at level 200).

(** ## Integers *)

(** `sign_extension(M, H, U, S)`: the two's-complement reading of the
    low bits of U, for a field of modulus M with sign threshold H. *)
Definition sign_extension (m h u : Z) : Z :=
  let l := u mod m in if h <=? l then l - m else l.

(** `signed(K, U, S)`. *)
Definition signed (k : class) (u : Z) : option Z :=
  let* m := modulus k in
  let* h := half_modulus k in
  Some (sign_extension m h u).

(** `extension(T, X, S)`: the low bytes of X that T names, sign- or
    zero-extended. *)
Definition extension (t : narrow) (x : Z) : Z :=
  match t with
  | Sb => sign_extension 256 128 x
  | Ub => x mod 256
  | Sh => sign_extension 65536 32768 x
  | Uh => x mod 65536
  | Sw => sign_extension (2 ^ 32) (2 ^ 31) x
  | Uw => x mod 2 ^ 32
  end.

(** `cond_bit(Cond, K, X, Y, B)`: 1 when X Cond Y holds at class K. *)
Definition cond_bit (c : cond) (k : class) (x y : Z) : option Z :=
  let bit (b : bool) := Some (if b then 1 else 0) in
  match c with
  | Eq => bit (x =? y)
  | Ne => bit (negb (x =? y))
  | Ult => bit (x <? y)
  | Ule => bit (x <=? y)
  | Ugt => bit (y <? x)
  | Uge => bit (y <=? x)
  | Slt => let* sx := signed k x in let* sy := signed k y in bit (sx <? sy)
  | Sle => let* sx := signed k x in let* sy := signed k y in bit (sx <=? sy)
  | Sgt => let* sx := signed k x in let* sy := signed k y in bit (sy <? sx)
  | Sge => let* sx := signed k x in let* sy := signed k y in bit (sy <=? sx)
  end.

(** `shift_factor(K, Y, P)`: the count is taken modulo the class width. *)
Definition shift_factor (k : class) (y : Z) : option Z :=
  let* bits := class_bits k in
  Some (2 ^ (y mod bits)).

(** `unsigned_division/4`: a zero divisor gives 0. *)
Definition unsigned_division (f : Z -> Z -> Z) (x y : Z) : Z :=
  if y =? 0 then 0 else f x y.

(** `signed_division/5`: a zero divisor gives 0, and the quotient
    truncates toward zero (Prolog's `//` and `rem`), then wraps. *)
Definition signed_division (f : Z -> Z -> Z) (k : class) (x y : Z) : option Z :=
  let* sx := signed k x in
  let* sy := signed k y in
  let* m := modulus k in
  Some (if sy =? 0 then 0 else f sx sy mod m).

(** `alu(Op, K, Xs, Res)`: the arithmetic Op of class K on Xs; add and
    sub are integer here. *)
Definition alu (o : op) (k : class) (xs : list word) : option word :=
  match o, xs with
  | Ptoi, [WPtr p] => Some (WInt (ptr_addr p))
  | Itop, [WInt x] => Some (WPtr (mkPtr x CNone))
  | Add, [WInt x; WInt y] => let* m := modulus k in Some (WInt ((x + y) mod m))
  | Sub, [WInt x; WInt y] => let* m := modulus k in Some (WInt ((x - y) mod m))
  | Mul, [WInt x; WInt y] => let* m := modulus k in Some (WInt ((x * y) mod m))
  | Neg, [WInt x] => let* m := modulus k in Some (WInt ((- x) mod m))
  | Copy, [x] => Some x
  | And, [WInt x; WInt y] => Some (WInt (Z.land x y))
  | Or, [WInt x; WInt y] => Some (WInt (Z.lor x y))
  | Xor, [WInt x; WInt y] => Some (WInt (Z.lxor x y))
  | Udiv, [WInt x; WInt y] => Some (WInt (unsigned_division Z.div x y))
  | Urem, [WInt x; WInt y] => Some (WInt (unsigned_division Z.modulo x y))
  | Div, [WInt x; WInt y] => let* r := signed_division Z.quot k x y in Some (WInt r)
  | Rem, [WInt x; WInt y] => let* r := signed_division Z.rem k x y in Some (WInt r)
  | Shl, [WInt x; WInt y] =>
      let* p := shift_factor k y in let* m := modulus k in Some (WInt ((x * p) mod m))
  | Shr, [WInt x; WInt y] =>
      let* p := shift_factor k y in Some (WInt (x / p))
  | Sar, [WInt x; WInt y] =>
      let* p := shift_factor k y in let* sx := signed k x in
      let* m := modulus k in Some (WInt ((sx / p) mod m))
  | Ext t, [WInt x] => let* m := modulus k in Some (WInt (extension t x mod m))
  | Cmp c ck, [WInt x; WInt y] => let* b := cond_bit c ck x y in Some (WInt b)
  | _, _ => None
  end.

(** `additive_res(K, Op, Xs, Res)`: pointer arithmetic keeps the
    capability; integer add and sub are `alu/4`'s. *)
Definition additive_res (k : class) (o : op) (xs : list word) : option word :=
  match k, o, xs with
  | P, Add, [WPtr p; WInt x] =>
      Some (WPtr (mkPtr ((ptr_addr p + x) mod 2 ^ 64) (ptr_cap p)))
  | P, Sub, [WPtr p; WInt x] =>
      Some (WPtr (mkPtr ((ptr_addr p - x) mod 2 ^ 64) (ptr_cap p)))
  | (W | L), _, _ => alu o k xs
  | _, _, _ => None
  end.

(** ## Checks *)

(** `checked_res(Res0, P, Res)`: a check yields P, proven, or traps. *)
Definition checked_res (r : res unit) (p : word) : res word :=
  match r with
  | RVal _ => RVal p
  | RTrap why => RTrap why
  | RUnchecked why => RUnchecked why
  end.

(** `raw_res(Res0, Res)`: a raw access is the access its check covers,
    made again without trapping; what would have trapped is unchecked. *)
Definition raw_res {X : Type} (r : res X) : res X :=
  match r with
  | RTrap why => RUnchecked why
  | _ => r
  end.

(** `renew_res(Res0, P, Mem, Res)`: a renew traps as the check it
    replaced would on a freed object or a write to a read-only one; any
    other failure means the earlier check's bounds did not cover this
    access: unchecked(span). *)
Definition renew_res (r : res unit) (p : ptr) (m : mem) : option (res word) :=
  match r with
  | RVal _ => Some (RVal (WPtr p))
  | RTrap Readonly => Some (RTrap Readonly)
  | RTrap _ =>
      match ptr_cap p with
      | Obj base =>
          let* reg := object_region base (m_regions m) in
          Some (match r_life reg with
                | Freed => RTrap OutOfBounds
                | Live => RUnchecked Span
                end)
      | _ => Some (RUnchecked Span)
      end
  | RUnchecked why => Some (RUnchecked why)
  end.

(** `half_bound(Bound, B, Size, Base, End, Life)`: the bound a half
    check tests natively. *)
Definition half_bound (bd : bound) (b size base end_ : Z) (l : life) : bool :=
  match bd with
  | Upper => b + size <=? end_
  | Lower =>
      match l with
      | Freed => false
      | Live => base <=? (if 2 ^ 63 <=? b then b - 2 ^ 64 else b)
      end
  end.

(** `half_passes(Bound, Mem, B, Size, Cap, Rights, Align, Passes)`: a
    half check's native test at B. None for a capability that is not an
    object's, whose header no half check may read. *)
Definition half_passes (bd : bound) (m : mem) (b size : Z) (c : cap)
    (r : rights) (align : Z) : option (option bool) :=
  let test base ro :=
    let* reg := object_region base (m_regions m) in
    Some (Some (half_bound bd b size base (r_end reg) (r_life reg)
                && negb (rights_eqb r Write && ro)
                && (b mod align =? 0))) in
  match c with
  | Obj base => test base false
  | Ro base => test base true
  | _ => Some None
  end.

(** `half_res(Res0, Passes, P, Res)`: where the native test and the
    check disagree, the bound taken as known was false. *)
Definition half_res (r : res unit) (passes : bool) (p : word) : res word :=
  match r, passes with
  | RVal _, true => RVal p
  | RTrap why, false => RTrap why
  | _, _ => RUnchecked Half
  end.

(** ## Loads *)

(** `extended_res(Res0, T, K, Res)` of a loaded U. *)
Definition extended (t : narrow) (k : class) (u : Z) : option word :=
  let* m := modulus k in Some (WInt (extension t u mod m)).

(** `load_op_res(T, K, filc, [ptr(A, Cap)], ...)` for an integer T: the
    access check (read, alignment 1), then the bytes, extended. *)
Definition int_load_res (t : load_type) (k : class) (m : mem) (a : Z) (c : cap)
  : option (res word) :=
  let size := match t with LdL => 8 | LdNarrow n => fst (narrow_type n) end in
  let* chk := access_res m a c size Read 1 in
  match chk with
  | RVal _ =>
      let u := load_bytes m a size in
      match t with
      | LdL => Some (RVal (WInt u))
      | LdNarrow n => let* x := extended n k u in Some (RVal x)
      end
  | RTrap why => Some (RTrap why)
  | RUnchecked why => Some (RUnchecked why)
  end.

(** The local state of a pointer load's protocol: the aux word read so
    far and the pointer being assembled (`loaded(C, P, Mem)`). *)
Definition pointer_load_effect (m : mem) (a : Z) (st : cap * ptr) (e : effect)
  : option (cap * ptr) :=
  let (c, p) := st in
  match e with
  | AuxRead => let c' := aux_at m a in Some (c', mkPtr (ptr_addr p) c')
  | LowerResolve => Some (c, mkPtr (ptr_addr p) c)
  | AddressRead => Some (c, mkPtr (load_bytes m a 8) (ptr_cap p))
  | AtomicRead =>
      let c' := aux_at m a in Some (c', mkPtr (load_bytes m a 8) c')
  | _ => None
  end.

(** `pointer_load_effects_res(ok, Effects, A, Mem0, val(P), Mem)`: run
    the protocol from `loaded(none, ptr(0, none))`. *)
Definition pointer_load_effects (m : mem) (a : Z) (es : list effect) : option ptr :=
  let* st := fold_left (fun st e => let* s := st in pointer_load_effect m a s e)
                       es (Some (CNone, mkPtr 0 CNone)) in
  Some (snd st).

(** `pointer_store_effect(A, P, Effect, Mem0, Mem)`: ensure, barrier and
    reload are identities here (no GC, no aux allocation); the writes
    happen in list order, the lower before the primary address. *)
Definition pointer_store_effect (a : Z) (x : ptr) (m : mem) (e : effect) : option mem :=
  match e with
  | AuxEnsure | LowerBarrier | RootedReload => Some m
  | LowerWrite => Some (store_aux m a (ptr_cap x))
  | AddressWrite => Some (store_bytes m a 8 (ptr_addr x))
  | AtomicWrite => Some (store_bytes (store_aux m a (ptr_cap x)) a 8 (ptr_addr x))
  | _ => None
  end.

Definition pointer_store_effects (a : Z) (x : ptr) (m : mem) (es : list effect)
  : option mem :=
  fold_left (fun m e => let* m' := m in pointer_store_effect a x m' e) es (Some m).

(** ## Ops *)

(** What an op yields: a partial result and the memory after it, or a
    request for a fresh object and what follows from its base. *)
Inductive op_out : Type :=
| OpRes (r : res word) (m : mem)
| OpAlloc (q : alloc_req) (k : Z -> word * mem).

(** `op_res(Op, K, filc, Args, S0, Res, S)` and `kind_res/8` for the
    core subset. *)
Definition op_res (o : op) (k : class) (xs : list word) (m : mem) : option op_out :=
  let pure (x : option word) := let* w := x in Some (OpRes (RVal w) m) in
  let with_mem (r : option (res word)) := let* r' := r in Some (OpRes r' m) in
  match o, k, xs with
  | Alloc align, _, [WInt size] =>
      let q := heap_req align size in
      Some (OpAlloc q (fun base => (WPtr (mkPtr base (Obj base)), allocated m q base)))
  | Check lo hi r al, A, [WPtr p] =>
      let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
      Some (OpRes (checked_res chk (WPtr p)) m)
  | CheckAhead lo hi r al ahi, A, [WPtr p] =>
      let b := raw_address (ptr_addr p) lo in
      let* need := access_res m b (ptr_cap p) (ahi - lo) r al in
      match need with
      | RTrap why => Some (OpRes (RTrap why) m)
      | _ =>
          let* whole := access_res m b (ptr_cap p) (hi - lo) r al in
          match whole with
          | RTrap why => Some (OpRes (RTrap (Early why)) m)
          | _ => Some (OpRes (RVal (WPtr p)) m)
          end
      end
  | Renew lo hi r al, A, [q1; x] =>
      match q1, x with
      | WPtr p1, WPtr p =>
          if cap_eqb (ptr_cap p1) (ptr_cap p) then
            let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
            with_mem (renew_res chk p m)
          else Some (OpRes (RUnchecked Alias) m)
      | _, _ => Some (OpRes (RUnchecked Alias) m)
      end
  | RenewHull lo hi r al, A, [ql; qh; x] =>
      match ql, qh, x with
      | WPtr pl, WPtr ph, WPtr p =>
          if cap_eqb (ptr_cap pl) (ptr_cap p) && cap_eqb (ptr_cap ph) (ptr_cap p) then
            let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
            with_mem (renew_res chk p m)
          else Some (OpRes (RUnchecked Alias) m)
      | _, _, _ => Some (OpRes (RUnchecked Alias) m)
      end
  | HalfCheck bd lo hi r al, A, [q1; x] =>
      match q1, x with
      | WPtr p1, WPtr p =>
          if cap_eqb (ptr_cap p1) (ptr_cap p) then
            let b := raw_address (ptr_addr p) lo in
            let* chk := access_res m b (ptr_cap p) (hi - lo) r al in
            let* passes := half_passes bd m b (hi - lo) (ptr_cap p) r al in
            match passes with
            | Some ok' => Some (OpRes (half_res chk ok' (WPtr p)) m)
            | None => Some (OpRes (RUnchecked Half) m)
            end
          else Some (OpRes (RUnchecked Alias) m)
      | _, _ => Some (OpRes (RUnchecked Alias) m)
      end
  | SpanTest lo hi, W, [WPtr p] =>
      let span base :=
        let* reg := object_region base (m_regions m) in
        let l := raw_address (ptr_addr p) lo in
        let h := raw_address (ptr_addr p) hi in
        Some (OpRes (RVal (WInt (if (base <=? l) && (l <? h) && (h <=? r_end reg)
                                 then 1 else 0))) m) in
      match ptr_cap p with
      | Obj base | Ro base => span base
      | _ => Some (OpRes (RVal (WInt 0)) m)
      end
  | RenewIf lo hi r al, A, [WPtr p; WInt g] =>
      let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
      if g =? 0 then Some (OpRes (checked_res chk (WPtr p)) m)
      else match chk with
           | RTrap Misaligned => Some (OpRes (RTrap Misaligned) m)
           | _ => with_mem (renew_res chk p m)
           end
  | Limit size, L, [WPtr p] => pure (Some (WLimit (ptr_cap p) size))
  | CheckLimit lo hi r al, A, [WPtr p; u] =>
      match u with
      | WLimit c size =>
          if cap_eqb c (ptr_cap p) && (size =? hi - lo) then
            let* chk := access_res m (raw_address (ptr_addr p) lo) (ptr_cap p) (hi - lo) r al in
            Some (OpRes (checked_res chk (WPtr p)) m)
          else Some (OpRes (RUnchecked WhyLimit) m)
      | _ => Some (OpRes (RUnchecked WhyLimit) m)
      end
  | RawLoad t off, _, [WPtr p] =>
      let* r := int_load_res t k m (raw_address (ptr_addr p) off) (ptr_cap p) in
      Some (OpRes (raw_res r) m)
  | RawLoadPointer off es, P, [WPtr p] =>
      let b := raw_address (ptr_addr p) off in
      let* chk := access_res m b (ptr_cap p) 8 Read 8 in
      match chk with
      | RVal _ => let* x := pointer_load_effects m b es in Some (OpRes (RVal (WPtr x)) m)
      | RTrap why | RUnchecked why => Some (OpRes (RUnchecked why) m)
      end
  | (Add | Sub), _, _ => pure (additive_res k o xs)
  | (Mul | Div | Udiv | Rem | Urem | And | Or | Xor | Sar | Shr | Shl
     | Neg | Copy | Ptoi | Itop | Cmp _ _ | Ext _), _, _ => pure (alu o k xs)
  | _, _, _ => None
  end.

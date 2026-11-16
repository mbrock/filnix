(** The abstract interpreter of [AbsRun](../../theories/exec/AbsRun.v)
    knows no system call. It asks a hook about every call of a function
    that has no body. This module is the hook for the three calls that
    `c: init_cpu_features` makes, which are `c: zcpuid`,
    `c: zcpuid_count` and `c: zxgetbv`.

    A CPUID call answers with four numbers that the processor chooses,
    so the hook treats the bytes it writes as unknown. Two facts about
    those bytes are known all the same, and they mirror the contract in
    [OsCpuid](../zsys/OsCpuid.v). The first concerns leaf 1. The ECX
    register of that answer has bit 27 set only when the kernel enabled
    XSAVE, and a call of `c: zxgetbv` is safe only then. The
    interpreter's guard stands for that fact here. The second concerns
    leaf 4, where the answer for the last subleaf describes no cache.
    The hook uses the second fact only when its user assumes that the
    leaf 4 list ends.

    Like the interpreter, this hook is not proved sound, and its
    soundness proof is being written. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics AbsRun.
Import ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

Definition is_atom (n : name) (s : string) : bool := name_eqb n (TAtom s).

(** The constant [last4] is the last subleaf that a signed 32-bit counter
    reaches before it wraps. *)
Definition last4 : Z := 2 ^ 31 - 1.

(** The four result blocks of a CPUID call must be writable four-byte
    spans that do not overlap. *)
Definition disjoint4 (ps : list (nat * Z)) : bool :=
  let fix go (ps : list (nat * Z)) :=
    match ps with
    | [] => true
    | (o, k) :: ps' =>
        forallb (fun q => negb (Nat.eqb o (fst q)) || (k + 4 <=? snd q) || (snd q + 4 <=? k)) ps' && go ps'
    end in
  go ps.

Definition cpuid_out (st : astate) (p : nat * Z) (bytes : list abyte) : option astate :=
  let (o, k) := p in
  let* ob := get_obj st o in
  if negb (o_ro ob) && (0 <=? k) && (k + 4 <=? o_size ob) then
    Some (put_obj st o (Some (mkObj (o_ro ob) (o_align ob) (splice k bytes (o_bytes ob))
                                (splice k (repeat XAny 4) (o_aux ob)))))
  else None.

Definition acpuid (leaf4 : bool) (leaf : aval) (subleaf : option aint) (ps : list aval) (st : astate) : option astate :=
  match leaf, ps with
  | VI l, [pa; pb; pc; pd] =>
      let* a := exact_ptr st pa in
      let* b := exact_ptr st pb in
      let* c := exact_ptr st pc in
      let* d := exact_ptr st pd in
      if disjoint4 [a; b; c; d] then
        let one := match rng st l with (1, 1) => true | _ => false end in
        let ends := match rng st l, subleaf with
                    | (4, 4), Some (S s) => if leaf4 then [BEnd s last4 31; BR; BR; BR] else repeat BR 4
                    | _, _ => repeat BR 4
                    end in
        let* st1 := cpuid_out st a ends in
        let* st2 := cpuid_out st1 b (repeat BR 4) in
        let* st3 := cpuid_out st2 c (if one then [BR; BR; BR; BGuard 3] else repeat BR 4) in
        cpuid_out st3 d (repeat BR 4)
      else None
  | _, _ => None
  end.

(** The hook answers the three calls and leaves every other call to the
    specifications. With [leaf4] set, it assumes that the leaf 4 list ends. *)
Definition cpu_builtin (leaf4 : bool) (g : name) (r : call_result) (xs : list aval) (st : astate)
  : option (option astate) :=
  if is_atom g "zcpuid" then
    Some match r, xs with
         | CVoid, l :: ps => acpuid leaf4 l None ps st
         | _, _ => None
         end
  else if is_atom g "zcpuid_count" then
    Some match r, xs with
         | CVoid, l :: VI s :: ps => acpuid leaf4 l (Some s) ps st
         | _, _ => None
         end
  else if is_atom g "zxgetbv" then
    Some match r, xs with
         | CResult d L, [] =>
             if st_guard st then let (s, st2) := fresh st 0 (2 ^ 64 - 1) in Some (bind st2 d (VI (S s)))
             else None
         | _, _ => None
         end
  else None.

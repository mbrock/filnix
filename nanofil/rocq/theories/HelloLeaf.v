(** GNU Hello's leaf functions through the program logic of Logic.v
    (docs/logic.md, "GNU Hello through the logic", milestone 2).

    Four small gnulib helpers of the linked module ([hello_module])
    each make one libc call and return, and each gets a Hoare triple
    from that call's triple: `mbszero` from [wp_memset]
    ([mbszero_spec]), `memeq` from [wp_memcmp] ([memeq_spec]), `streq`
    from [wp_strcmp] ([streq_spec]) and `strnlen1` from
    [wp_memchr_string] ([strnlen1_spec]). Callers in the module use
    them through [wp_call_bind], as `count_l` uses `next_l` in
    CountLogic.v.

    The triples hold in any genv that links Hello: one whose module is
    [hello_module], whose symbols include the module's own
    ([hello_globals]) and none of the libc functions it calls
    ([hello_linked]). The registry and the world interpretation are
    any that hold the contracts the calls name, so the same triples
    serve the whole program, whose world is Campaign 4's. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic LentLogic
  HelloModule.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The module's symbols and functions *)

(** The symbols laying out [hello_module] gives, from 65536 on
    ([initial_memory]): 115 of them, functions and data. *)
Definition hello_globals : list (name * ptr) := Eval vm_compute in
  match initial_memory hello_module with Some (g, _) => g | None => [] end.

(** A genv links Hello: its module is [hello_module], each of the
    module's symbols is where [hello_globals] puts it, and no libc
    function the module calls ([hello_externals]) is a symbol, so each
    such call is an [external_site]. Startup may add libc's data
    symbols, such as `program_invocation_name`. *)
Definition hello_linked (ge : genv) : Prop :=
  ge_module ge = hello_module /\
  (forall n p, lookup n hello_globals = Some p -> lookup n (ge_globals ge) = Some p) /\
  (forall s, existsb (String.eqb s) hello_externals = true -> lookup (TAtom s) (ge_globals ge) = None).

(** The module md defines no function named s ([find_fn]). *)
Definition outside (md : module) (s : String.string) : bool :=
  match find_fn (mkGenv md [] (fun _ _ => None)) (TAtom s) with
  | None => true
  | Some _ => false
  end.

(** A function md does not define is no function of a genv with
    module md: [find_fn] reads only the module. *)
Lemma outside_find ge s : outside (ge_module ge) s = true -> find_fn ge (TAtom s) = None.
Proof.
  unfold outside, find_fn. cbn [ge_module]. destruct (find_direct _ _); [discriminate|].
  destruct (find_alias _ _) as [t|]; cbn; [|reflexivity]. destruct (find_direct t _); [discriminate | reflexivity].
Qed.

(** The libc function s, one Hello calls, is no function of a genv
    with Hello's module. *)
Lemma hello_outside ge s :
  ge_module ge = hello_module -> existsb (String.eqb s) hello_externals = true ->
  find_fn ge (TAtom s) = None.
Proof.
  intros Hm Hs. apply outside_find. rewrite Hm.
  assert (H : forallb (outside hello_module) hello_externals = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply existsb_exists in Hs as (s' & Hin & Hs).
  apply String.eqb_eq in Hs. rewrite <- Hs in Hin. exact (H s Hin).
Qed.

(** The function f called with the words xs, at its entry, as
    [call_frame] makes it; a direct call to f binds this frame. *)
Definition invocation (f : func) (xs : list word) : frame :=
  match call_frame f xs with
  | Some fr => fr
  | None => mkFrame f [] [] None (Enter (TAtom "start") None)
  end.

(** Block l of f, or an empty one. *)
Definition hblk (f : func) (l : String.string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** `mbszero(p)`: memset of 8 zero bytes, gnulib's `mbstate_t` reset. *)
Definition mbszero_fn : func := Eval vm_compute in hello_fn "mbszero".
(** `memeq(p, q, n)`: memcmp, compared with 0. *)
Definition memeq_fn : func := Eval vm_compute in hello_fn "memeq".
(** `streq(p, q)`: strcmp, compared with 0. *)
Definition streq_fn : func := Eval vm_compute in hello_fn "streq".
(** `strnlen1(p, n)`: memchr for the NUL in n bytes; one past it, or n. *)
Definition strnlen1_fn : func := Eval vm_compute in hello_fn "strnlen1".
(** `xmalloc(n)`: malloc, and `xalloc_die` on null. *)
Definition xmalloc_fn : func := Eval vm_compute in hello_fn "xmalloc".

(** `mbszero`'s one block. *)
Definition z_start : block := Eval vm_compute in hblk mbszero_fn "start".
(** `memeq`'s one block. *)
Definition e_start : block := Eval vm_compute in hblk memeq_fn "start".
(** `streq`'s one block. *)
Definition q_start : block := Eval vm_compute in hblk streq_fn "start".
(** `strnlen1`'s entry: memchr, then is its result null? *)
Definition n_start : block := Eval vm_compute in hblk strnlen1_fn "start".
(** `strnlen1` after a hit: one past it. *)
Definition n_L8 : block := Eval vm_compute in hblk strnlen1_fn "L8".
(** `strnlen1` after no hit: n. *)
Definition n_L9 : block := Eval vm_compute in hblk strnlen1_fn "L9".

(** `xmalloc`'s entry: malloc, then is the result null? *)
Definition x_start : block := Eval vm_compute in hblk xmalloc_fn "start".
(** `xmalloc`'s return. *)
Definition x_join : block := Eval vm_compute in hblk xmalloc_fn "iw_1.join".

(** `mbszero` has its block. *)
Lemma find_z_start : find_block (TAtom "start") (fn_blocks mbszero_fn) = Some z_start.
Proof. vm_compute. reflexivity. Qed.
(** `memeq` has its block. *)
Lemma find_e_start : find_block (TAtom "start") (fn_blocks memeq_fn) = Some e_start.
Proof. vm_compute. reflexivity. Qed.
(** `streq` has its block. *)
Lemma find_q_start : find_block (TAtom "start") (fn_blocks streq_fn) = Some q_start.
Proof. vm_compute. reflexivity. Qed.
(** `strnlen1` has its entry. *)
Lemma find_n_start : find_block (TAtom "start") (fn_blocks strnlen1_fn) = Some n_start.
Proof. vm_compute. reflexivity. Qed.
(** `strnlen1` has its hit block. *)
Lemma find_n_L8 : find_block (TAtom "L8") (fn_blocks strnlen1_fn) = Some n_L8.
Proof. vm_compute. reflexivity. Qed.
(** `strnlen1` has its miss block. *)
Lemma find_n_L9 : find_block (TAtom "L9") (fn_blocks strnlen1_fn) = Some n_L9.
Proof. vm_compute. reflexivity. Qed.

(** `xmalloc` has its entry. *)
Lemma find_x_start : find_block (TAtom "start") (fn_blocks xmalloc_fn) = Some x_start.
Proof. vm_compute. reflexivity. Qed.
(** `xmalloc` has its return block. *)
Lemma find_x_join : find_block (TAtom "iw_1.join") (fn_blocks xmalloc_fn) = Some x_join.
Proof. vm_compute. reflexivity. Qed.

(** `mbszero`'s entry binds its pointer. *)
Lemma mbszero_entry p :
  invocation mbszero_fn [WPtr p] =
  mkFrame mbszero_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.
(** `memeq`'s entry binds its pointers and length. *)
Lemma memeq_entry p q n :
  invocation memeq_fn [WPtr p; WPtr q; WInt n] =
  mkFrame memeq_fn [(TAtom "v4", WInt n); (TAtom "v2", WPtr q); (TAtom "v0", WPtr p)] []
    None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.
(** `streq`'s entry binds its pointers. *)
Lemma streq_entry p q :
  invocation streq_fn [WPtr p; WPtr q] =
  mkFrame streq_fn [(TAtom "v2", WPtr q); (TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.
(** `strnlen1`'s entry binds its pointer and bound. *)
Lemma strnlen1_entry p n :
  invocation strnlen1_fn [WPtr p; WInt n] =
  mkFrame strnlen1_fn [(TAtom "v2", WInt n); (TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `xmalloc`'s entry binds its size. *)
Lemma xmalloc_entry n :
  invocation xmalloc_fn [WInt n] =
  mkFrame xmalloc_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** Prove a premise that names words: by computation, with the
    environment's facts. *)
Ltac word_premise := first [ reflexivity | compute_premise ].

(** Prove an address premise: drop the wraps of [raw_address] and of a
    flight's sum where arithmetic shows them the identity, then
    arithmetic. *)
Ltac addr_premise := cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; arith.

(** Hello's leaf functions over any [[runtime]] R. *)
Module HelloLeaf (R : Runtime).
Module LL := LentLogic R.
Module ML := LL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML.

Section leaves.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The genv links Hello ([hello_linked]). *)
Context (Hlinked : hello_linked ge).

(** The Iris instance of the registry and wi. *)
Local Instance leaf_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation hexpr := (language.expr (nanofil_lang registry ge)).

(** The libc function s that Hello calls is no function of the genv. *)
Lemma linked_outside s : existsb (String.eqb s) hello_externals = true -> find_fn ge (TAtom s) = None.
Proof. apply hello_outside. exact (proj1 Hlinked). Qed.

(** The libc function s that Hello calls is no symbol of the genv. *)
Lemma linked_unbound s : existsb (String.eqb s) hello_externals = true -> lookup (TAtom s) (ge_globals ge) = None.
Proof. apply (proj2 (proj2 Hlinked)). Qed.

(** `mbszero`'s triple, from [wp_memset]: owning the 8 bytes xs and
    their aux slots cs at the 8-aligned offset o of the live object b,
    at a multiple of 8, where the fill keeps the world interpretation,
    the call zeroes them and clears the slots. *)
Lemma mbszero_spec b reg o xs cs Φ :
  registry (TAtom "memset") = Some (memset_contract world) ->
  length xs = 8%nat -> length cs = 8%nat ->
  b mod 8 = 0 -> o mod 8 = 0 -> 0 <= o -> b + o + 8 <= r_end reg ->
  (forall m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) 0 8 m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate 8 0) (clear_slots o cs)) h)) ->
  live b reg -∗ bytes b o xs -∗ auxes b o cs -∗
  ▷ (live b reg -∗ bytes b o (replicate 8 0) -∗ auxes b o (clear_slots o cs) -∗ Φ RetVoid) -∗
  WP (ERun (invocation mbszero_fn [WPtr (mkPtr (b + o) (Obj b))]) : hexpr) {{ Φ }}.
Proof.
  intros Hreg Hx Hc Hb8 Ho8 Ho Hend Hwi. iIntros "Hl Hx Hcs HΦ". rewrite mbszero_entry.
  iApply wp_enter; [exact find_z_start | reflexivity |]. iNext. cbn [b_insts b_jump z_start].
  iApply (wp_memset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Hl Hx Hcs");
    [exact Hreg | apply linked_outside; reflexivity | apply linked_unbound; reflexivity |
     word_premise | word_premise | rewrite Hx; word_premise | lia | exact Hb8 | exact Ho8 | exact Ho |
     rewrite Hx; exact Hend | rewrite Hc Hx; reflexivity | rewrite Hx; exact Hwi |].
  iNext. iIntros "Hl Hx Hcs". rewrite Hx.
  iApply wp_ret_void. iNext. iApply ("HΦ" with "Hl Hx Hcs").
Qed.

(** `memeq`'s triple, from [wp_memcmp]: owning as many bytes xs and ys
    of two live objects, through read-write or read-only
    capabilities, n their count, it returns an int and hands them
    back. *)
Lemma memeq_spec b reg o xs c b' reg' o' ys c' n Φ :
  registry (TAtom "memcmp") = Some (memcmp_contract world) -> n = Z.of_nat (length xs) ->
  c = Obj b \/ c = Ro b -> c' = Obj b' \/ c' = Ro b' -> length ys = length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
  b' + o' + Z.of_nat (length xs) <= r_end reg' -> Z.of_nat (length xs) < 2 ^ 64 ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  live b reg -∗ bytes b o xs -∗ live b' reg' -∗ bytes b' o' ys -∗
  ▷ (∀ k, live b reg -∗ bytes b o xs -∗ live b' reg' -∗ bytes b' o' ys -∗ Φ (Ret (WInt k))) -∗
  WP (ERun (invocation memeq_fn [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt n]) : hexpr)
    {{ Φ }}.
Proof.
  intros Hreg -> Hc Hc' Hlen Ho Ho' Hend Hend' Hn Hx Hy. iIntros "Hl Hx Hl' Hy HΦ". rewrite memeq_entry.
  iApply wp_enter; [exact find_e_start | reflexivity |]. iNext. cbn [b_insts b_jump e_start].
  iApply (wp_memcmp with "Hl Hx Hl' Hy");
    [exact Hreg | apply linked_outside; reflexivity | apply linked_unbound; reflexivity |
     reflexivity | exact Hc | reflexivity | exact Hc' |
     cbn; rewrite Z.mod_small; [reflexivity | lia] |
     exact Hlen | exact Ho | exact Ho' | exact Hend | exact Hend' | exact Hx | exact Hy |].
  iNext. iIntros (bits) "Hl Hx Hl' Hy".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply wp_ret; [reflexivity | word_premise |]. iNext. iApply ("HΦ" with "Hl Hx Hl' Hy").
Qed.

(** `streq`'s triple, from [wp_strcmp]: owning the strings at p and q,
    it returns an int and hands them back. *)
Lemma streq_spec p b reg xs q b' reg' ys Φ :
  registry (TAtom "strcmp") = Some (strcmp_contract world) ->
  string p b reg xs -∗ string q b' reg' ys -∗
  ▷ (∀ k, string p b reg xs -∗ string q b' reg' ys -∗ Φ (Ret (WInt k))) -∗
  WP (ERun (invocation streq_fn [WPtr p; WPtr q]) : hexpr) {{ Φ }}.
Proof.
  intros Hreg. iIntros "Hs Ht HΦ". rewrite streq_entry.
  iApply wp_enter; [exact find_q_start | reflexivity |]. iNext. cbn [b_insts b_jump q_start].
  iApply (wp_strcmp with "Hs Ht");
    [exact Hreg | apply linked_outside; reflexivity | apply linked_unbound; reflexivity |
     reflexivity | reflexivity |].
  iNext. iIntros (bits) "Hs Ht".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply wp_ret; [reflexivity | word_premise |]. iNext. iApply ("HΦ" with "Hs Ht").
Qed.

(** `strnlen1`'s triple on a string, from [wp_memchr_string]: owning
    the string at p with contents bytes, a bound n returns one past
    its NUL when that lies within n bytes, and n otherwise. The bytes
    after the NUL need not exist. *)
Lemma strnlen1_spec p b reg bytes n Φ :
  registry (TAtom "memchr") = Some (memchr_contract world) -> 0 <= n < 2 ^ 64 ->
  SL.string p b reg bytes -∗
  ▷ (SL.string p b reg bytes -∗ Φ (Ret (WInt (Z.min (Z.of_nat (length bytes) + 1) n)))) -∗
  WP (ERun (invocation strnlen1_fn [WPtr p; WInt n]) : hexpr) {{ Φ }}.
Proof.
  intros Hreg Hn. iIntros "Hs HΦ". iDestruct "Hs" as "[%Hok Hs]".
  pose proof Hok as (_ & Hb0 & Hlo & Hhi & H48 & _). rewrite strnlen1_entry.
  iApply wp_enter; [exact find_n_start | reflexivity |]. iNext. cbn [b_insts b_jump n_start].
  iApply (ML.wp_memchr_string _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 n with "[$Hs //]");
    [exact Hreg | apply linked_outside; reflexivity | apply linked_unbound; reflexivity |
     reflexivity | reflexivity | lia | reflexivity | cbn; rewrite Z.mod_small; [reflexivity | lia] |
     exact Hn |].
  iNext. iIntros "Hs". unfold nul_found.
  destruct (Z.of_nat (length bytes) <? n) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_branch; [reflexivity|]. iNext.
    match goal with |- context[if ?t =? 0 then _ else _] => replace t with 1 end;
      [| cbn [ptr_addr]; rewrite !Zmod_0_l (Z.mod_small (ptr_addr p + _)); [|lia];
         rewrite (proj2 (Z.eqb_neq _ 0)); [reflexivity | lia]].
    cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_n_L8 | reflexivity |]. iNext. cbn [b_insts b_jump n_L8].
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_ret; [reflexivity | word_premise |]. iNext. cbn [ptr_addr].
    assert (Ht : forall a l, 0 <= a -> 0 <= l -> a + l + 1 < 2 ^ 64 ->
      ((((a + l) mod 2 ^ 64 - a mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 mod 2 ^ 64
      = l + 1).
    { intros a l Ha Hl Hal. rewrite (Z.mod_small (a + l)); [|lia]. rewrite (Z.mod_small a); [|lia].
      replace (a + l - a) with l by lia. rewrite (Z.mod_small l); [|lia]. rewrite (Z.mod_small l); [|lia].
      rewrite (Z.mod_small 1); [|lia]. rewrite (Z.mod_small (l + 1)); [|lia].
      rewrite (Z.mod_small (l + 1)); [reflexivity | lia]. }
    rewrite (Ht (ptr_addr p) (Z.of_nat (length bytes))); [|lia | lia | lia]. rewrite Z.min_l; [|lia].
    iApply ("HΦ" with "Hs").
  - iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_branch; [reflexivity|]. iNext.
    match goal with |- context[if ?t =? 0 then _ else _] => replace t with 0 by reflexivity end.
    cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_n_L9 | reflexivity |]. iNext. cbn [b_insts b_jump n_L9].
    iApply wp_ret; [reflexivity | word_premise |]. iNext.
    rewrite Z.min_r; [|lia]. rewrite (Z.mod_small n); [|lia]. iApply ("HΦ" with "Hs").
Qed.

(** `xmalloc`'s triple, from [wp_malloc]: for a size n, where an
    allocation keeps the world interpretation, it returns the base
    pointer of a fresh heap object of n bytes, whose pieces it owns. The
    selected malloc never returns null, so `xalloc_die`, and the `abort`
    it may reach, are never called. *)
Lemma xmalloc_spec n Φ :
  registry (TAtom "malloc") = Some (malloc_contract world) -> 0 <= n < 2 ^ 64 ->
  (forall m wd h base, fresh m (heap_req 16 n) base -> wi m wd h ->
     wi (allocated m (heap_req 16 n) base) wd (overwrite (obj_ps base (heap_req 16 n)) h)) ->
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48 /\
               n <= max_allocation_size⌝ -∗
       obj base (heap_req 16 n) -∗ Φ (Ret (WPtr (mkPtr base (Obj base))))) -∗
  WP (ERun (invocation xmalloc_fn [WInt n]) : hexpr) {{ Φ }}.
Proof.
  intros Hreg Hn Hwi. iIntros "HΦ". rewrite xmalloc_entry.
  iApply wp_enter; [exact find_x_start | reflexivity |]. iNext. cbn [b_insts b_jump x_start].
  iApply (wp_malloc _ _ _ _ _ _ _ _ _ _ _ n);
    [exact Hreg | apply linked_outside; reflexivity | apply linked_unbound; reflexivity |
     cbn; rewrite Z.mod_small; [reflexivity | lia] | exact Hn | exact Hwi |].
  iNext. iIntros (base Hb) "Hobj". destruct Hb as (Hb0 & Hb16 & Hbend & Hmax).
  assert (Hext : 0 <= req_extent (heap_req 16 n)).
  { unfold req_extent, heap_req. cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [exact find_x_join | reflexivity |]. iNext. cbn [b_insts b_jump x_join].
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HΦ" with "[%] Hobj"). auto.
Qed.

End leaves.
End HelloLeaf.

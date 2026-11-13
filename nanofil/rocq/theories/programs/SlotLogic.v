(** This module proves that the C program `slot.c` never panics and always
    returns an integer. The function `c: fill` maintains a static heap
    buffer pointer `c: slot` and its capacity `c: slot_size`, growing the
    buffer with `c: free` and `c: malloc` whenever a request does not fit,
    then filling it with `c: memset`. The caller `c: use` calls `c: fill`
    three times and reads a byte from the returned buffer after each call.

    Because `c: fill` owns the buffer across calls, the caller cannot hold
    onto the returned bytes permanently. Instead, `c: fill` temporarily
    lends the filled bytes to its caller along with a callback permission
    that restores the module invariant once the caller finishes reading.
    When `c: use` calls `c: fill` again, it must first return the borrowed
    bytes so `c: fill` can safely reuse or free the old buffer.

    The safety theorem works for any [[runtime]] R whose `free` operation
    succeeds on null and live heap pointers. We also run the theorem on the
    module's initial memory under the [[interpreter]]'s runtime. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls LibcCalls ExternalMachine Transport Pieces Heap ContractFrame Language Logic
  StringLogic LibcStringLogic MemLogic LibcMemLogic SlotCode HiLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on symbolic values stays folded during premise
    reduction so buffer sizes and offsets remain readable. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The module

    The proof verifies the compiled IR that `nanofil -O` produces for
    `slot.c`. We decode the module, record the addresses of the static
    variables `c: slot` and `c: slot_size`, precompute the basic blocks of
    both functions, and link `c: malloc` and `c: memset`. *)

(** Decoding [slot_term] extracts the compiled module for `slot.c`. *)
Definition slot_module : module :=
  match decode_module slot_term with Some md => md | None => [] end.

(** The saved compiler fixture decodes cleanly into [slot_module]. *)
Lemma slot_decodes : decode_module slot_term = Some slot_module.
Proof. vm_compute. reflexivity. Qed.

(** Selecting the i-th function from the module returns its IR definition,
    or a dummy function if the index is out of range. *)
Definition slot_nth (i : nat) : func :=
  match nth_error slot_module i with
  | Some (IFunc f) => f
  | _ => mkFunc (TAtom "none") (TAtom "export") RVoid [] []
  end.

(** The helper function `fill` grows the static buffer if needed and fills
    it with a byte value. *)
Definition fill_fn : func := Eval vm_compute in slot_nth 0.
(** The caller `use` invokes `fill` three times and reads from each
    returned buffer. *)
Definition use_fn : func := Eval vm_compute in slot_nth 1.

(** The static pointer variable `slot` lives at object address 65568. *)
Definition slot_b : Z := 65568.
(** The static size variable `slot_size` lives at object address 65600. *)
Definition size_b : Z := 65600.
(** The global [[region]] for `slot` spans 8 bytes of live global data. *)
Definition slot_reg : region := mkRegion 65568 65576 GlobalData Live.
(** The global [[region]] for `slot_size` spans 8 bytes of live global data. *)
Definition size_reg : region := mkRegion 65600 65608 GlobalData Live.

(** The global symbol table maps both static variables and both compiled
    functions to their addresses. *)
Definition slot_globals : list (name * ptr) :=
  [(TAtom "slot_size", mkPtr size_b (Obj size_b)); (TAtom "slot", mkPtr slot_b (Obj slot_b));
   (TAtom "use", mkPtr 65552 (Fn (TAtom "use"))); (TAtom "fill", mkPtr 65536 (Fn (TAtom "fill")))].

(** Laying out the module's globals produces the expected symbol table. *)
Lemma slot_layout : option_map fst (initial_memory slot_module) = Some slot_globals.
Proof. vm_compute. reflexivity. Qed.

(** Extracting block l from function f returns its instruction list and
    terminator, or an empty unreachable block if missing. *)
Definition sblk (f : func) (l : String.string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** The entry block of `fill` checks whether the existing buffer is large
    enough for the request. *)
Definition f_start : block := Eval vm_compute in sblk fill_fn "start".
(** Block `L4` of `fill` frees the old buffer and allocates a larger one. *)
Definition f_L4 : block := Eval vm_compute in sblk fill_fn "L4".
(** Block `L6` of `fill` runs `c: memset`, writes the terminating byte, and
    returns the buffer pointer. *)
Definition f_L6 : block := Eval vm_compute in sblk fill_fn "L6".
(** The single block of `use` makes three calls to `fill` and loads one
    byte after each. *)
Definition u_start : block := Eval vm_compute in sblk use_fn "start".

(** Looking up `start` in `fill` returns its precomputed entry block. *)
Lemma find_f_start : find_block (TAtom "start") (fn_blocks fill_fn) = Some f_start.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L4` in `fill` returns its precomputed growth block. *)
Lemma find_f_L4 : find_block (TAtom "L4") (fn_blocks fill_fn) = Some f_L4.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `L6` in `fill` returns its precomputed fill block. *)
Lemma find_f_L6 : find_block (TAtom "L6") (fn_blocks fill_fn) = Some f_L6.
Proof. vm_compute. reflexivity. Qed.
(** Looking up `start` in `use` returns its precomputed block. *)
Lemma find_u_start : find_block (TAtom "start") (fn_blocks use_fn) = Some u_start.
Proof. vm_compute. reflexivity. Qed.

(** Calling `fill` with byte c and size n constructs an entry frame binding
    `v0` to c and `v2` to n. *)
Definition fill_entry (c n : Z) : frame :=
  mkFrame fill_fn (put (TAtom "v2") (WInt n) (put (TAtom "v0") (WInt c) [])) [] None
    (Enter (TAtom "start") None).

(** Passing arguments c and n to `fill` enters the function at
    [fill_entry]. *)
Lemma fill_call_frame c n : call_frame fill_fn [WInt c; WInt n] = Some (fill_entry c n).
Proof. reflexivity. Qed.

(** Calling `use` constructs an entry frame with no parameters. *)
Definition use_entry : frame := mkFrame use_fn [] [] None (Enter (TAtom "start") None).

(** The external call registry links `c: malloc` and `c: memset` with an
    empty world state. *)
Definition slot_registry (symbol : name) : option (contract unit) :=
  if name_eqb symbol (TAtom "malloc") then Some (malloc_contract unit)
  else if name_eqb symbol (TAtom "memset") then Some (memset_contract unit)
  else None.

(** A freshly allocated object starts with zero bytes and empty [[aux]]
    slots across its entire extent. *)
Lemma obj_block base q :
  0 <= req_extent q ->
  obj_ps base q = block_ps base (mkRegion base (base + req_extent q) (req_kind q) Live) 0
                    (replicate (Z.to_nat (req_extent q)) 0) (replicate (Z.to_nat (req_extent q)) CNone).
Proof.
  intros Hq. unfold obj_ps, block_ps, byte_ps, aux_ps. rewrite !length_replicate Z2Nat.id; [|exact Hq].
  rewrite (zip_with_replicate_r_eq _ (Z.to_nat (req_extent q))); [|apply length_seqZ].
  rewrite (zip_with_replicate_r_eq _ (Z.to_nat (req_extent q))); [|apply length_seqZ].
  reflexivity.
Qed.

(** This tactic solves address bounds by simplifying [raw_address], dropping
    proven-safe wraps, and running integer arithmetic. *)
Ltac addr_premise := cbn [ptr_addr slot_b size_b]; unfold raw_address; drop_wraps_goal; arith.

(** This tactic discharges bounds checks for the static globals `slot` and
    `slot_size` by computation. *)
Ltac static_premise := unfold slot_b, size_b, slot_reg, size_reg; vm_compute; first [reflexivity | congruence].

(** This tactic solves word equalities by reflexivity or by looking up
    known values in the local environment. *)
Ltac word_premise := first [ reflexivity | compute_premise ].

(** Initially, `slot` holds a null pointer and `slot_size` holds zero,
    with both static objects live in memory. *)
Definition slot_ps0 : list (piece * pval) :=
  (PLive slot_b, VLive slot_reg) :: (PLive size_b, VLive size_reg) ::
  ((PAux slot_b 0, VAux CNone) :: cell slot_b 0 0) ++ cell size_b 0 0.

(** Every piece in the initial static state [slot_ps0] appears at most
    once. *)
Lemma slot_ps0_nodup : NoDup slot_ps0.*1.
Proof.
  cbv [slot_ps0 cell fmap list_fmap fst map app slot_b size_b]. cbn [Z.add].
  repeat (apply NoDup_cons_2;
          [intros Hin; repeat (apply elem_of_cons in Hin as [Hin|Hin]; [discriminate Hin|]);
           apply elem_of_nil in Hin; exact Hin|]).
  apply NoDup_nil_2.
Qed.

(** This functor constructs the Iris safety proof for `slot.c` over any
    [[runtime]] R. *)
Module SlotLogic (R : Runtime).
Module ML := LibcMemLogic R.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML.

(** The global environment links `slot.c`'s symbols with R's `free`
    handler. *)
Definition slot_ge : genv := mkGenv slot_module slot_globals R.free.

(** Looking up `fill` in [slot_ge] resolves to the compiled helper
    function. *)
Lemma find_fill : find_fn slot_ge (TAtom "fill") = Some (Defined fill_fn).
Proof. vm_compute. reflexivity. Qed.

Section proof.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris language instance pairs the external call table with an empty
    world and `slot.c`'s symbols. *)
Local Instance slot_irisGS : irisGS_gen hlc (nanofil_lang slot_registry slot_ge) Σ :=
  nanofil_irisGS slot_registry no_world slot_ge.

(** Expressions in this language run over `slot.c` with `c: malloc` and
    `c: memset` linked. *)
Local Notation sexpr := (language.expr (nanofil_lang slot_registry slot_ge)).

(** ## The module invariant

    Across calls to `fill`, the static variables `slot` and `slot_size`
    either hold null and zero or own a live heap buffer of at least
    `slot_size` bytes. When `fill` returns, it lends the caller the first
    n bytes and keeps a permission wand that rebuilds this invariant once
    the caller finishes reading. *)

(** The heap buffer predicate holds either a null pointer of size zero or a
    16-byte-aligned live heap object owning its bytes and [[aux]] slots. *)
Definition buffer (p : ptr) (sz : Z) : iProp Σ :=
  ⌜p = null /\ sz = 0⌝ ∨
  ∃ b reg xs cs, ⌜p = mkPtr b (Obj b) /\ 0 < b /\ b mod 16 = 0 /\ r_kind reg = Heap /\
                   0 < sz <= Z.of_nat (length xs) /\ length cs = length xs /\
                   b + Z.of_nat (length xs) <= r_end reg /\ r_end reg <= 2 ^ 48⌝ ∗
    live b reg ∗ bytes b 0 xs ∗ auxes b 0 cs.

(** The module invariant owns both static globals, the pointer and size they
    store, and the heap buffer described by those values. *)
Definition slot_inv : iProp Σ :=
  live slot_b slot_reg ∗ live size_b size_reg ∗
  ∃ p sz, ⌜0 <= sz < 2 ^ 48⌝ ∗ pcell slot_b 0 p ∗ icell size_b 0 sz ∗ buffer p sz.

(** After `fill` succeeds, it lends the caller the buffer's liveness and the
    n filled bytes, along with a permission to return them and restore the
    invariant. *)
Definition lent (b : Z) (reg : region) (n c : Z) : iProp Σ :=
  ⌜0 < b /\ b + n < r_end reg /\ r_end reg <= 2 ^ 48⌝ ∗ live b reg ∗ bytes b 0 (replicate (Z.to_nat n) (c mod 256)) ∗
  (live b reg -∗ bytes b 0 (replicate (Z.to_nat n) (c mod 256)) -∗ slot_inv).

(** ## Bytes

    Both `c: fill` and `c: use` work with slices of a byte array: `c: fill`
    splits the buffer into the filled prefix, the terminating zero byte, and
    the remaining capacity, while `c: use` borrows individual bytes to read.
    These helper lemmas split and reassemble byte and [[aux]] sequences. *)

(** Splitting a byte list at an element separates the prefix, that byte, and
    the suffix in separation logic. *)
Lemma bytes_split b o ys x zs :
  bytes b o (ys ++ x :: zs) ⊣⊢
  bytes b o ys ∗ ibyte b (o + Z.of_nat (length ys)) x ∗ bytes b (o + Z.of_nat (length ys) + 1) zs.
Proof.
  rewrite /bytes /ibyte /pts byte_ps_app byte_ps_cons big_sepL_app big_sepL_cons big_sepL_singleton.
  replace (o + Z.of_nat (length ys) + 1) with (o + Z.of_nat (length ys) + 1) by lia. done.
Qed.

(** Splitting an [[aux]] slot list separates the prefix slots from the
    suffix slots. *)
Lemma auxes_app b o cs1 cs2 : auxes b o (cs1 ++ cs2) ⊣⊢ auxes b o cs1 ∗ auxes b (o + Z.of_nat (length cs1)) cs2.
Proof.
  rewrite /auxes /pts -big_sepL_app. f_equiv. revert o. induction cs1 as [|c cs1 IH]; intros o.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [app]. rewrite !aux_ps_cons IH. cbn [app length].
    replace (o + Z.of_nat (S (length cs1))) with (o + 1 + Z.of_nat (length cs1)) by lia. reflexivity.
Qed.

(** Indexing into a byte sequence borrows the byte at offset i and returns
    a permission to put it back. *)
Lemma bytes_byte b o xs i x :
  xs !! i = Some x ->
  bytes b o xs -∗ ibyte b (o + Z.of_nat i) x ∗ (ibyte b (o + Z.of_nat i) x -∗ bytes b o xs).
Proof.
  intros Hx. rewrite /bytes /ibyte /pts big_sepL_singleton.
  iIntros "Hs". iDestruct (big_sepL_lookup_acc with "Hs") as "[Hb Hk]"; [exact (byte_ps_lookup _ _ _ _ _ Hx)|].
  iSplitL "Hb"; [iExact "Hb"|]. iIntros "Hb". iApply ("Hk" with "Hb").
Qed.

(** ## The buffer

    Before freeing or loading through the static `slot` pointer, the proof
    must handle the case where `slot` is still null. These two lemmas
    extract the buffer's [[capability]] liveness when non-null and dispatch
    `c: free` cleanly on both null and heap pointers. *)

(** Any buffer pointer has a valid 64-bit address and lends its object's
    [[capability]] liveness token when non-null. *)
Lemma buffer_cap p sz :
  buffer p sz -∗ ∃ reg', ⌜0 <= ptr_addr p < 2 ^ 64⌝ ∗ live_cap (ptr_cap p) reg' ∗
    (live_cap (ptr_cap p) reg' -∗ buffer p sz).
Proof.
  iIntros "[[%Hp %Hz] | (%b & %reg & %xs & %cs & %Hf & Hl & Hx & Hcs)]".
  - iExists slot_reg. subst p. iSplit; [iPureIntro; cbn; lia|]. iSplit; [done|]. iIntros "_". iLeft. done.
  - pose proof Hf as (Hpe & Hb & _ & _ & _ & _ & Hend & Hend48). subst p. iExists reg.
    iSplit; [iPureIntro; cbn; lia|]. iFrame "Hl". iIntros "Hl". iRight. iExists b, reg, xs, cs. by iFrame.
Qed.

(** Calling `c: free` on the buffer pointer releases the heap object if
    non-null and consumes the buffer ownership. *)
Lemma wp_free_buffer f e ls l v rest j p sz Φ :
  arg_x slot_ge e (Arg P v) = Some (WPtr p) ->
  buffer p sz -∗ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : sexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j)) : sexpr)
    {{ Φ }}.
Proof.
  intros Hv. iIntros "[[%Hp _] | (%b & %reg & %xs & %cs & %Hf & Hl & _ & _)] HK".
  - subst p. iApply (wp_free_null with "HK"); [exact R.free_succeeds | reflexivity | reflexivity | exact Hv].
  - destruct Hf as (-> & Hb & _ & Hk & _).
    iApply (wp_free with "Hl HK"); [exact R.free_succeeds | reflexivity | reflexivity | exact Hv | exact Hk | lia |
                                    intros; exact I].
Qed.

(** ## `fill`

    When `slot_size <= n`, `fill` frees the old buffer and allocates a
    bigger one before joining block `L6` to run `c: memset` and write the
    zero terminator. We verify the shared tail at `L6` first, then the full
    `fill` function, and finally three consecutive calls in `use`. *)

(** Starting from block `L6` with a buffer larger than n, `fill` runs
    `c: memset` on the first n bytes, writes a zero terminator, and lends the
    filled slice to the caller. *)
Lemma fill_L6 e c n b reg xs cs sz Φ :
  lookup (TAtom "v0") e = Some (WInt c) -> lookup (TAtom "v2") e = Some (WInt n) ->
  0 <= c < 2 ^ 32 -> 0 <= n < sz -> sz < 2 ^ 48 ->
  0 < b -> b mod 16 = 0 -> r_kind reg = Heap -> sz <= Z.of_nat (length xs) -> length cs = length xs ->
  b + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  live slot_b slot_reg -∗ live size_b size_reg -∗ pcell slot_b 0 (mkPtr b (Obj b)) -∗ icell size_b 0 sz -∗
  live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗
  ▷ (∀ b reg, lent b reg n c -∗ Φ (Ret (WPtr (mkPtr b (Obj b))))) -∗
  WP (ERun (mkFrame fill_fn e [] None (Exec (TAtom "L6") (b_insts f_L6) (b_jump f_L6))) : sexpr) {{ Φ }}.
Proof.
  intros Hc Hn Hc32 Hnsz Hsz Hb0 Hb16 Hk Hxs Hcs Hend Hend48.
  iIntros "Hls Hlz Hp Hz Hl Hx Hcs HΦ". cbn [b_insts b_jump f_L6].
  (* Split the buffer at n: the n bytes memset fills, the terminator, the rest. *)
  assert (Hnx : (Z.to_nat n < length xs)%nat) by lia.
  destruct (lookup_lt_is_Some_2 xs _ Hnx) as [x Hx].
  rewrite <- (take_drop_middle xs (Z.to_nat n) x Hx).
  rewrite <- (take_drop (Z.to_nat n) cs).
  iDestruct (bytes_split with "Hx") as "(Hx & Hx0 & Hxr)".
  iDestruct (auxes_app with "Hcs") as "[Hcs Hcr]".
  assert (Ht : length (take (Z.to_nat n) xs) = Z.to_nat n) by (rewrite length_take; lia).
  assert (Htc : length (take (Z.to_nat n) cs) = length (take (Z.to_nat n) xs)) by (rewrite !length_take; lia).
  rewrite Ht. assert (Hb8 : b mod 8 = 0).
  { pose proof (Z.div_mod b 16 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound b 8 ltac:(lia)). lia. }
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply (wp_check with "Hls");
    [reflexivity | word_premise | reflexivity | static_premise | static_premise | static_premise |].
  iNext. iIntros "Hls". gen_env.
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ reg with "Hls Hp Hl");
    [reflexivity | word_premise | reflexivity | static_premise | static_premise | cbn; lia |].
  iNext. iIntros "Hls Hp Hl". gen_env.
  iApply (wp_memset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Hl Hx Hcs");
    [reflexivity | reflexivity | reflexivity | rewrite Z.add_0_r; word_premise | word_premise |
     rewrite Ht Z2Nat.id; [word_premise | lia] | exact Hc32 | exact Hb8 | reflexivity | lia |
     rewrite Ht; lia | exact Htc | intros; exact I |].
  iNext. iIntros "Hl Hx Hcs". rewrite Z.add_0_r. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply (wp_check with "Hls");
    [reflexivity | word_premise | reflexivity | static_premise | static_premise | static_premise |].
  iNext. iIntros "Hls". gen_env.
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ reg with "Hls Hp Hl");
    [reflexivity | word_premise | reflexivity | static_premise | static_premise | cbn; lia |].
  iNext. iIntros "Hls Hp Hl". gen_env.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + n)); [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
  iNext. gen_env.
  iApply (wp_check with "Hl"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise | apply Z.mod_1_r |].
  iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_store_byte with "Hl Hx0");
    [word_premise | word_premise | reflexivity | addr_premise | intros; exact I |].
  iNext. iIntros "Hl Hx0". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply (wp_check with "Hls");
    [reflexivity | word_premise | reflexivity | static_premise | static_premise | static_premise |].
  iNext. iIntros "Hls". gen_env.
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ reg with "Hls Hp Hl");
    [reflexivity | word_premise | reflexivity | static_premise | static_premise | cbn; lia |].
  iNext. iIntros "Hls Hp Hl". gen_env.
  iApply wp_ret; [reflexivity | word_premise |]. iNext.
  rewrite Ht. iApply ("HΦ" $! b reg). iSplit; [iPureIntro; lia|]. iFrame "Hl Hx". iIntros "Hl Hx".
  iFrame "Hls Hlz". iExists _, sz. iFrame "Hp Hz". iSplit; [iPureIntro; lia|]. iRight.
  iExists b, reg, (replicate (Z.to_nat n) (c mod 256) ++ 0 mod 256 :: drop (S (Z.to_nat n)) xs),
    (clear_slots 0 (take (Z.to_nat n) cs) ++ drop (Z.to_nat n) cs).
  rewrite bytes_split auxes_app length_replicate length_clear_slots Htc Ht.
  iFrame "Hl Hx Hx0 Hxr Hcs Hcr". iPureIntro.
  rewrite !length_app. cbn [length]. rewrite !length_replicate length_clear_slots !length_drop !length_take.
  split; [reflexivity|]. repeat split; first [assumption | lia].
Qed.

(** Calling `fill` with byte c and size n consumes the module invariant,
    grows the buffer if `slot_size <= n`, and returns a pointer lending the
    first n bytes. *)
Lemma fill_spec c n Φ :
  0 <= c < 2 ^ 32 -> 0 <= n < 2 ^ 47 ->
  slot_inv -∗ ▷ (∀ b reg, lent b reg n c -∗ Φ (Ret (WPtr (mkPtr b (Obj b))))) -∗
  WP (ERun (fill_entry c n) : sexpr) {{ Φ }}.
Proof.
  intros Hc Hn. iIntros "(Hls & Hlz & %p & %sz & %Hsz & Hp & Hz & Hbuf) HΦ". unfold fill_entry.
  remember (put (TAtom "v2") (WInt n) (put (TAtom "v0") (WInt c) [])) as e eqn:Ee.
  assert (Hv0 : lookup (TAtom "v0") e = Some (WInt c)) by (subst e; reflexivity).
  assert (Hv2 : lookup (TAtom "v2") e = Some (WInt n)) by (subst e; reflexivity).
  clear Ee.
  iApply wp_enter; [exact find_f_start | reflexivity |]. iNext. cbn [b_insts b_jump f_start].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply (wp_check with "Hlz");
    [reflexivity | word_premise | reflexivity | static_premise | static_premise | static_premise |].
  iNext. iIntros "Hlz". gen_env.
  iApply (wp_raw_load with "Hlz Hz"); [reflexivity | word_premise | reflexivity | static_premise |].
  iNext. iIntros "Hlz Hz". gen_env.
  destruct (Z.le_gt_cases sz n) as [Hle | Hgt].
  - (* Too small: free the buffer, malloc n + 1 bytes, and store them. *)
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_f_L4 | reflexivity |]. iNext. cbn [b_insts b_jump f_L4].
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_check with "Hls");
      [reflexivity | word_premise | reflexivity | static_premise | static_premise | static_premise |].
    iNext. iIntros "Hls". gen_env.
    iDestruct (buffer_cap with "Hbuf") as (reg') "(%Hpa & Hcap & Hbuf)".
    iApply (wp_raw_load_pointer with "Hls Hp Hcap");
      [reflexivity | word_premise | reflexivity | static_premise | static_premise | exact Hpa |].
    iNext. iIntros "Hls Hp Hcap". iDestruct ("Hbuf" with "Hcap") as "Hbuf". gen_env.
    iApply (wp_free_buffer with "Hbuf"); [word_premise|]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_malloc; [reflexivity | reflexivity | reflexivity | word_premise | lia | intros; exact I |].
    iNext. iIntros (base (Hpos & Hmod & Hend & Hmax)) "Hobj". gen_env.
    iApply (wp_check with "Hls");
      [reflexivity | word_premise | reflexivity | static_premise | static_premise | static_premise |].
    iNext. iIntros "Hls". gen_env.
    iApply (wp_raw_store_pointer with "Hls Hp");
      [word_premise | word_premise | reflexivity | static_premise | static_premise | intros; exact I |].
    iNext. iIntros "Hls Hp".
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_check with "Hlz");
      [reflexivity | word_premise | reflexivity | static_premise | static_premise | static_premise |].
    iNext. iIntros "Hlz". gen_env.
    iApply (wp_raw_store with "Hlz Hz");
      [word_premise | word_premise | reflexivity | static_premise | intros; exact I |].
    iNext. iIntros "Hlz Hz".
    iApply wp_goto. iNext. iApply wp_enter; [exact find_f_L6 | reflexivity |]. iNext.
    pose proof (malloc_extent (n + 1) ltac:(lia)) as Hext.
    rewrite /obj obj_block; [|lia]. rewrite block_pts. iDestruct "Hobj" as "(Hl & Hx & Hcs)".
    iApply (fill_L6 with "Hls Hlz Hp Hz Hl Hx Hcs HΦ");
      [assumption | assumption | exact Hc | lia | lia | exact Hpos | exact Hmod | reflexivity |
       rewrite length_replicate Z2Nat.id; lia | rewrite !length_replicate; reflexivity |
       cbn [r_end]; rewrite length_replicate Z2Nat.id; lia | cbn [r_end]; lia].
  - (* Big enough: the buffer is not null; fill it. *)
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_f_L6 | reflexivity |]. iNext.
    iDestruct "Hbuf" as "[[_ %Hz0] | (%b & %reg & %xs & %cs & %Hf & Hl & Hx & Hcs)]"; [lia|].
    destruct Hf as (-> & Hb & Hb16 & Hk & Hszx & Hcx & Hend & Hend48).
    iApply (fill_L6 with "Hls Hlz Hp Hz Hl Hx Hcs HΦ");
      [assumption | assumption | exact Hc | lia | lia | exact Hb | exact Hb16 | exact Hk | lia | exact Hcx |
       exact Hend | exact Hend48].
Qed.

(** Calling `use` with the initial module invariant executes three `fill`
    calls, reads one byte after each, and safely returns an integer. *)
Lemma use_spec : slot_inv -∗ WP (ERun use_entry : sexpr) {{ o, ⌜exists k, o = Ret (WInt k)⌝ }}.
Proof.
  iIntros "Hinv". iApply wp_enter; [exact find_u_start | reflexivity |]. iNext. cbn [b_insts b_jump u_start].
  (* fill('a', 8), then a[7]. *)
  iApply wp_call_bind; [reflexivity | exact find_fill | reflexivity |]. iNext.
  iApply (fill_spec 97 8 with "Hinv"); [lia | lia |]. iNext. iIntros (b reg) "(%Hb & Hl & Hx & Hback)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + 7)); [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
  iNext. iApply (wp_check with "Hl"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise | apply Z.mod_1_r |].
  iNext. iIntros "Hl". iDestruct (bytes_byte _ _ _ 7 with "Hx") as "[Hb Hx]"; [reflexivity|].
  iApply (wp_raw_load_byte with "Hl Hb"); [reflexivity | word_premise | reflexivity | reflexivity | left; reflexivity | addr_premise |].
  iNext. iIntros "Hl Hb". iDestruct ("Hx" with "Hb") as "Hx". iDestruct ("Hback" with "Hl Hx") as "Hinv".
  (* fill('b', 3), then b[0]. *)
  iApply wp_call_bind; [reflexivity | exact find_fill | reflexivity |]. iNext.
  iApply (fill_spec 98 3 with "Hinv"); [lia | lia |]. iNext. iIntros (b2 reg2) "(%Hb2 & Hl & Hx & Hback)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply (wp_check with "Hl"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise | apply Z.mod_1_r |].
  iNext. iIntros "Hl". iDestruct (bytes_byte _ _ _ 0 with "Hx") as "[Hb Hx]"; [reflexivity|].
  iApply (wp_raw_load_byte with "Hl Hb"); [reflexivity | word_premise | reflexivity | reflexivity | left; reflexivity | addr_premise |].
  iNext. iIntros "Hl Hb". iDestruct ("Hx" with "Hb") as "Hx". iDestruct ("Hback" with "Hl Hx") as "Hinv".
  (* fill('c', 16), then c[15], and the sum. *)
  iApply wp_call_bind; [reflexivity | exact find_fill | reflexivity |]. iNext.
  iApply (fill_spec 99 16 with "Hinv"); [lia | lia |]. iNext. iIntros (b3 reg3) "(%Hb3 & Hl & Hx & _)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b3 + 15)); [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
  iNext. iApply (wp_check with "Hl"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise | apply Z.mod_1_r |].
  iNext. iIntros "Hl". iDestruct (bytes_byte _ _ _ 15 with "Hx") as "[Hb _]"; [reflexivity|].
  iApply (wp_raw_load_byte with "Hl Hb"); [reflexivity | word_premise | reflexivity | reflexivity | left; reflexivity | addr_premise |].
  iNext. iIntros "_ _".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply wp_ret; [reflexivity | word_premise |]. iNext. iPureIntro. eexists. reflexivity.
Qed.

End wp.

(** Whenever the runtime is ready and the static globals start at null and
    zero, `use` executes safely for any fuel and returns an integer if it
    finishes. *)
Theorem slot_logic_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ} m s fuel :
  R.ready s m -> live_disjoint m -> all_agree m slot_ps0 ->
  labelled_safe slot_registry slot_ge use_entry m s tt fuel (fun o => exists k, o = Ret (WInt k)).
Proof.
  intros Hr Hd Ha.
  apply (heap_labelled_safe Σ slot_registry no_world slot_ge use_entry m s tt (list_to_map slot_ps0)).
  - exact Hr.
  - exact Hd.
  - intros l v Hl. exact (all_agree_elem _ _ _ _ Ha (elem_of_list_to_map_2 _ _ _ Hl)).
  - exact I.
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact slot_ps0_nodup].
    iIntros "Hps". iApply use_spec. rewrite /slot_ps0 /pts big_sepL_cons big_sepL_cons big_sepL_app.
    iDestruct "Hps" as "(Hls & Hlz & Hp & Hz)". rewrite /slot_inv /live /pts !big_sepL_singleton.
    iFrame "Hls Hlz". iExists null, 0. iSplit; [iPureIntro; lia|].
    iSplitL "Hp"; [iExact "Hp"|]. iSplitL "Hz"; [iExact "Hz"|]. iLeft. done.
Qed.

End proof.
End SlotLogic.

(** ## The interpreter's runtime

    To verify that `c: use` runs safely from a real initial state, we
    instantiate the theorem with the [[interpreter]]'s runtime. Both static
    globals sit below the heap allocation threshold and do not overlap, so
    the initial memory satisfies every requirement. *)

(** Instantiating the Iris functor with the interpreter's runtime yields a
    concrete safety theorem for `slot.c`. *)
Module InterpSlotLogic := SlotLogic InterpRuntime.

(** The module's initial memory contains both static objects with all bytes
    set to zero and all [[aux]] slots empty. *)
Definition slot_memory : mem :=
  mkMem (fun _ => 0) [size_reg; slot_reg] (fun _ => CNone).

(** Laying out `slot_module` produces [slot_globals] and [slot_memory]. *)
Lemma slot_initial : initial_memory slot_module = Some (slot_globals, slot_memory).
Proof. vm_compute. reflexivity. Qed.

(** The interpreter runtime is ready in [slot_memory] because both static
    objects lie below the heap allocation threshold. *)
Lemma slot_memory_ready : InterpRuntime.ready InterpRuntime.start slot_memory.
Proof.
  split; [vm_compute; split; congruence|]. split; [|intros a _; split; reflexivity].
  intros b reg E. change (object_region b [size_reg; slot_reg] = Some reg) in E.
  cbn -[Z.eqb] in E. destruct (65600 =? b) eqn:E1; [|destruct (65568 =? b) eqn:E2; [|discriminate E]];
    apply Z.eqb_eq in E1 || apply Z.eqb_eq in E2; subst b; injection E as <-;
    (split; [vm_compute; split; congruence|]); (split; [vm_compute; congruence | discriminate]).
Qed.

(** The two static objects `slot` and `slot_size` occupy disjoint address
    ranges. *)
Lemma slot_memory_disjoint : live_disjoint slot_memory.
Proof.
  intros b1 r1 b2 r2 [E1 _] [E2 _] Hne.
  change (object_region b1 [size_reg; slot_reg] = Some r1) in E1.
  change (object_region b2 [size_reg; slot_reg] = Some r2) in E2.
  cbn -[Z.eqb] in E1, E2.
  destruct (65600 =? b1) eqn:F1; [|destruct (65568 =? b1) eqn:G1; [|discriminate E1]];
  (destruct (65600 =? b2) eqn:F2; [|destruct (65568 =? b2) eqn:G2; [|discriminate E2]]);
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end;
  injection E1 as <-; injection E2 as <-; cbn; lia.
Qed.

(** Every piece in [slot_ps0] matches the initial memory state
    [slot_memory]. *)
Lemma slot_memory_agrees : all_agree slot_memory slot_ps0.
Proof.
  cbv [slot_ps0 cell map app slot_b size_b]. cbn [all_agree agree_piece fst snd].
  repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- live_at _ _ _ => split; reflexivity
  | |- registered _ _ => unfold registered; vm_compute; discriminate
  | |- in_live _ _ _ _ =>
      let reg := fresh "reg" in let E := fresh "E" in
      intros reg E _; vm_compute in E; injection E as <-; cbn [r_end];
      split; [lia|]; split; [lia|]; first [left; reflexivity | reflexivity]
  end.
Qed.

(** Under the interpreter's runtime and `slot.c`'s initial memory, calling
    `use` executes safely for any amount of fuel. *)
Theorem interp_slot_logic_safe : forall fuel,
  InterpSlotLogic.L.labelled_safe slot_registry InterpSlotLogic.slot_ge use_entry slot_memory
    InterpRuntime.start tt fuel (fun o => exists k, o = Ret (WInt k)).
Proof.
  intros fuel. apply (InterpSlotLogic.slot_logic_safe hiΣ).
  - exact slot_memory_ready.
  - exact slot_memory_disjoint.
  - exact slot_memory_agrees.
Qed.

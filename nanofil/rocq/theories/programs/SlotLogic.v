(** rocq/theories/programs/slot.c through the program logic of Logic.v: a callee
    that owns memory across calls, in the shape of gnulib's quotearg.

    `fill` keeps one heap buffer in its static `slot`, with its size in
    `slot_size`. When a request does not fit it frees the buffer and
    mallocs a bigger one; then it memsets the request, terminates it,
    and returns the buffer. The caller may read the buffer until its
    next call of `fill`, which reuses it or frees it.

    That ownership is the module invariant [slot_inv]: the two static
    objects, the pointer and size they hold, and the buffer's object
    with all its bytes and [[aux]] slots ([buffer]): null and size 0
    before the first call. `fill`'s triple ([fill_spec]) takes the
    invariant and lends the filled bytes to the caller ([lent]), with a
    wand that, given them back, gives the invariant back. The caller
    cannot keep the bytes across the next call: the next call needs the
    invariant, which needs them.

    The grow path uses [wp_free] on the old buffer, whose life token
    then ends, and [wp_malloc], whose fresh object becomes the new
    buffer ([obj_block]); both paths then go through the fill in
    [fill_L6], with [wp_memset] and a byte store. `use` calls `fill`
    three times, through [wp_call_bind] and [fill_spec], and reads the
    buffer after each call ([use_spec]).

    [slot_logic_safe] is the labelled machine's safety from any memory
    whose static objects hold null and 0, over any runtime, whose free
    succeeds on null and the buffer ([R.free_succeeds]), and
    [interp_slot_logic_safe] instantiates it from the module's initial
    memory under the interpreter's runtime. *)

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

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The module *)

(** The checked module nanofil makes of slot.c ([slot_term]). *)
Definition slot_module : module :=
  match decode_module slot_term with Some md => md | None => [] end.

(** The fixture decodes to [slot_module]. *)
Lemma slot_decodes : decode_module slot_term = Some slot_module.
Proof. vm_compute. reflexivity. Qed.

(** The module's i-th function, or an empty one. *)
Definition slot_nth (i : nat) : func :=
  match nth_error slot_module i with
  | Some (IFunc f) => f
  | _ => mkFunc (TAtom "none") (TAtom "export") RVoid [] []
  end.

(** `fill`: grow the buffer if need be, fill it, lend it. *)
Definition fill_fn : func := Eval vm_compute in slot_nth 0.
(** `use`: three calls of `fill`, each read after it. *)
Definition use_fn : func := Eval vm_compute in slot_nth 1.

(** The identity of the static `slot`, which holds the buffer. *)
Definition slot_b : Z := 65568.
(** The identity of the static `slot_size`, which holds its size. *)
Definition size_b : Z := 65600.
(** `slot`'s region. *)
Definition slot_reg : region := mkRegion 65568 65576 GlobalData Live.
(** `slot_size`'s region. *)
Definition size_reg : region := mkRegion 65600 65608 GlobalData Live.

(** The module's symbols. *)
Definition slot_globals : list (name * ptr) :=
  [(TAtom "slot_size", mkPtr size_b (Obj size_b)); (TAtom "slot", mkPtr slot_b (Obj slot_b));
   (TAtom "use", mkPtr 65552 (Fn (TAtom "use"))); (TAtom "fill", mkPtr 65536 (Fn (TAtom "fill")))].

(** Laying out the module gives [slot_globals]. *)
Lemma slot_layout : option_map fst (initial_memory slot_module) = Some slot_globals.
Proof. vm_compute. reflexivity. Qed.

(** Block l of f, or an empty one. *)
Definition sblk (f : func) (l : String.string) : block :=
  match find_block (TAtom l) (fn_blocks f) with
  | Some b => b
  | None => mkBlock (TAtom l) [] [] JUnreachable
  end.

(** `fill`'s entry: does the request fit? *)
Definition f_start : block := Eval vm_compute in sblk fill_fn "start".
(** The grow path: free the old buffer, malloc a new one. *)
Definition f_L4 : block := Eval vm_compute in sblk fill_fn "L4".
(** The fill: memset, the terminator, return the buffer. *)
Definition f_L6 : block := Eval vm_compute in sblk fill_fn "L6".
(** `use`'s one block. *)
Definition u_start : block := Eval vm_compute in sblk use_fn "start".

(** `fill` has its entry. *)
Lemma find_f_start : find_block (TAtom "start") (fn_blocks fill_fn) = Some f_start.
Proof. vm_compute. reflexivity. Qed.
(** `fill` has its grow path. *)
Lemma find_f_L4 : find_block (TAtom "L4") (fn_blocks fill_fn) = Some f_L4.
Proof. vm_compute. reflexivity. Qed.
(** `fill` has its fill. *)
Lemma find_f_L6 : find_block (TAtom "L6") (fn_blocks fill_fn) = Some f_L6.
Proof. vm_compute. reflexivity. Qed.
(** `use` has its block. *)
Lemma find_u_start : find_block (TAtom "start") (fn_blocks use_fn) = Some u_start.
Proof. vm_compute. reflexivity. Qed.

(** `fill` called with the int c and the size n. *)
Definition fill_entry (c n : Z) : frame :=
  mkFrame fill_fn (put (TAtom "v2") (WInt n) (put (TAtom "v0") (WInt c) [])) [] None
    (Enter (TAtom "start") None).

(** A call of `fill` starts it at [fill_entry]. *)
Lemma fill_call_frame c n : call_frame fill_fn [WInt c; WInt n] = Some (fill_entry c n).
Proof. reflexivity. Qed.

(** `use` called. *)
Definition use_entry : frame := mkFrame use_fn [] [] None (Enter (TAtom "start") None).

(** `slot.c`'s contracts: malloc's and memset's, over no world. *)
Definition slot_registry (symbol : name) : option (contract unit) :=
  if name_eqb symbol (TAtom "malloc") then Some (malloc_contract unit)
  else if name_eqb symbol (TAtom "memset") then Some (memset_contract unit)
  else None.

(** A fresh object's pieces, all zero bytes and empty slots, are a
    block from offset 0 of its whole extent. *)
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

(** Prove an address premise: drop the wraps of [raw_address] and of a
    flight's sum where arithmetic shows them the identity, then
    arithmetic. *)
Ltac addr_premise := cbn [ptr_addr slot_b size_b]; unfold raw_address; drop_wraps_goal; arith.

(** Prove a premise about a static object's address: by computation. *)
Ltac static_premise := unfold slot_b, size_b, slot_reg, size_reg; vm_compute; first [reflexivity | congruence].

(** Prove a premise that names words: by computation, with the
    environment's facts. *)
Ltac word_premise := first [ reflexivity | compute_premise ].

(** The pieces a run of `use` starts owning: the static objects, `slot`
    holding null and `slot_size` holding 0. *)
Definition slot_ps0 : list (piece * pval) :=
  (PLive slot_b, VLive slot_reg) :: (PLive size_b, VLive size_reg) ::
  ((PAux slot_b 0, VAux CNone) :: cell slot_b 0 0) ++ cell size_b 0 0.

(** No piece of [slot_ps0] is listed twice. *)
Lemma slot_ps0_nodup : NoDup slot_ps0.*1.
Proof.
  cbv [slot_ps0 cell fmap list_fmap fst map app slot_b size_b]. cbn [Z.add].
  repeat (apply NoDup_cons_2;
          [intros Hin; repeat (apply elem_of_cons in Hin as [Hin|Hin]; [discriminate Hin|]);
           apply elem_of_nil in Hin; exact Hin|]).
  apply NoDup_nil_2.
Qed.

(** `slot.c` over any [[runtime]] R. *)
Module SlotLogic (R : Runtime).
Module ML := LibcMemLogic R.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML.

(** The linked genv: the module, its symbols, R's free. *)
Definition slot_ge : genv := mkGenv slot_module slot_globals R.free.

(** `fill` is a function of the module. *)
Lemma find_fill : find_fn slot_ge (TAtom "fill") = Some (Defined fill_fn).
Proof. vm_compute. reflexivity. Qed.

Section proof.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris instance of `slot.c`: malloc's and memset's contracts, no
    world. *)
Local Instance slot_irisGS : irisGS_gen hlc (nanofil_lang slot_registry slot_ge) Σ :=
  nanofil_irisGS slot_registry no_world slot_ge.

(** The expressions of `slot.c`'s language. *)
Local Notation sexpr := (language.expr (nanofil_lang slot_registry slot_ge)).

(** ## The module invariant *)

(** What `slot` holding p and `slot_size` holding sz own: nothing for
    null and size 0; else the heap object p's capability names, at a
    multiple of 16, live, with every byte and aux slot of its first
    length xs bytes, at least sz of them. *)
Definition buffer (p : ptr) (sz : Z) : iProp Σ :=
  ⌜p = null /\ sz = 0⌝ ∨
  ∃ b reg xs cs, ⌜p = mkPtr b (Obj b) /\ 0 < b /\ b mod 16 = 0 /\ r_kind reg = Heap /\
                   0 < sz <= Z.of_nat (length xs) /\ length cs = length xs /\
                   b + Z.of_nat (length xs) <= r_end reg /\ r_end reg <= 2 ^ 48⌝ ∗
    live b reg ∗ bytes b 0 xs ∗ auxes b 0 cs.

(** The module invariant: both static objects, the pointer and size
    they hold, and the [buffer] they describe. *)
Definition slot_inv : iProp Σ :=
  live slot_b slot_reg ∗ live size_b size_reg ∗
  ∃ p sz, ⌜0 <= sz < 2 ^ 48⌝ ∗ pcell slot_b 0 p ∗ icell size_b 0 sz ∗ buffer p sz.

(** What `fill` lends its caller: the life of the buffer b and its
    first n bytes, all c's low byte, with the byte after them inside
    its bounds; and, for those given back, the module invariant. *)
Definition lent (b : Z) (reg : region) (n c : Z) : iProp Σ :=
  ⌜0 < b /\ b + n < r_end reg /\ r_end reg <= 2 ^ 48⌝ ∗ live b reg ∗ bytes b 0 (replicate (Z.to_nat n) (c mod 256)) ∗
  (live b reg -∗ bytes b 0 (replicate (Z.to_nat n) (c mod 256)) -∗ slot_inv).

(** ## Bytes *)

(** The bytes ys, then x, then zs, are ys's, x's, then zs's. *)
Lemma bytes_split b o ys x zs :
  bytes b o (ys ++ x :: zs) ⊣⊢
  bytes b o ys ∗ ibyte b (o + Z.of_nat (length ys)) x ∗ bytes b (o + Z.of_nat (length ys) + 1) zs.
Proof.
  rewrite /bytes /ibyte /pts byte_ps_app byte_ps_cons big_sepL_app big_sepL_cons big_sepL_singleton.
  replace (o + Z.of_nat (length ys) + 1) with (o + Z.of_nat (length ys) + 1) by lia. done.
Qed.

(** The slots cs1 then cs2 are cs1's, then cs2's. *)
Lemma auxes_app b o cs1 cs2 : auxes b o (cs1 ++ cs2) ⊣⊢ auxes b o cs1 ∗ auxes b (o + Z.of_nat (length cs1)) cs2.
Proof.
  rewrite /auxes /pts -big_sepL_app. f_equiv. revert o. induction cs1 as [|c cs1 IH]; intros o.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [app]. rewrite !aux_ps_cons IH. cbn [app length].
    replace (o + Z.of_nat (S (length cs1))) with (o + 1 + Z.of_nat (length cs1)) by lia. reflexivity.
Qed.

(** The bytes xs lend their i-th, x, and take it back. *)
Lemma bytes_byte b o xs i x :
  xs !! i = Some x ->
  bytes b o xs -∗ ibyte b (o + Z.of_nat i) x ∗ (ibyte b (o + Z.of_nat i) x -∗ bytes b o xs).
Proof.
  intros Hx. rewrite /bytes /ibyte /pts big_sepL_singleton.
  iIntros "Hs". iDestruct (big_sepL_lookup_acc with "Hs") as "[Hb Hk]"; [exact (byte_ps_lookup _ _ _ _ _ Hx)|].
  iSplitL "Hb"; [iExact "Hb"|]. iIntros "Hb". iApply ("Hk" with "Hb").
Qed.

(** ## The buffer *)

(** The buffer lends the life of the object its pointer's capability
    names, if any ([live_cap]), and takes it back; its pointer's
    address is in range. *)
Lemma buffer_cap p sz :
  buffer p sz -∗ ∃ reg', ⌜0 <= ptr_addr p < 2 ^ 64⌝ ∗ live_cap (ptr_cap p) reg' ∗
    (live_cap (ptr_cap p) reg' -∗ buffer p sz).
Proof.
  iIntros "[[%Hp %Hz] | (%b & %reg & %xs & %cs & %Hf & Hl & Hx & Hcs)]".
  - iExists slot_reg. subst p. iSplit; [iPureIntro; cbn; lia|]. iSplit; [done|]. iIntros "_". iLeft. done.
  - pose proof Hf as (Hpe & Hb & _ & _ & _ & _ & Hend & Hend48). subst p. iExists reg.
    iSplit; [iPureIntro; cbn; lia|]. iFrame "Hl". iIntros "Hl". iRight. iExists b, reg, xs, cs. by iFrame.
Qed.

(** A call of `free` on the buffer's pointer, which v reads as, frees
    it if it is not null, and gives up the whole buffer. *)
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

(** ## `fill` *)

(** The fill, from L6's instructions: owning the static objects
    holding the buffer b and its size sz, more than n, and the buffer's
    bytes xs and slots cs: memset its first n bytes, terminate them,
    and return the buffer, lending the bytes. *)
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

(** `fill`'s triple: with the module invariant, called with an int c
    and a size n below 2^47, it returns the buffer, lending its first n
    bytes, each c's low byte ([lent]). From the entry: load the size,
    and if it is at most n, free the old buffer ([wp_free_buffer]),
    malloc n + 1 bytes ([wp_malloc]) and store the new buffer and its
    size; then [fill_L6]. *)
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

(** `use` is safe and returns an int: it calls `fill` three times
    through [fill_spec], each time reading a byte of the bytes lent
    ([bytes_byte]) and handing them back for the next call. *)
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

(** `use` is safe: from a ready runtime, live objects apart, and a
    memory whose static objects hold null and 0, with any fuel, no
    labelled run stops with a [failure_ending], and a run that returns
    returns an int. By [heap_labelled_safe] from [use_spec], the ghost
    heap starting with [slot_ps0]. *)
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

(** ## The interpreter's runtime *)

(** `slot.c` over the interpreter's runtime. *)
Module InterpSlotLogic := SlotLogic InterpRuntime.

(** The module's initial memory: the two static objects, every byte 0
    and every aux slot empty. *)
Definition slot_memory : mem :=
  mkMem (fun _ => 0) [size_reg; slot_reg] (fun _ => CNone).

(** Laying out the module gives [slot_memory]. *)
Lemma slot_initial : initial_memory slot_module = Some (slot_globals, slot_memory).
Proof. vm_compute. reflexivity. Qed.

(** The interpreter is ready in [slot_memory] at its start: both
    objects lie below it. *)
Lemma slot_memory_ready : InterpRuntime.ready InterpRuntime.start slot_memory.
Proof.
  split; [vm_compute; split; congruence|]. split; [|intros a _; split; reflexivity].
  intros b reg E. change (object_region b [size_reg; slot_reg] = Some reg) in E.
  cbn -[Z.eqb] in E. destruct (65600 =? b) eqn:E1; [|destruct (65568 =? b) eqn:E2; [|discriminate E]];
    apply Z.eqb_eq in E1 || apply Z.eqb_eq in E2; subst b; injection E as <-;
    (split; [vm_compute; split; congruence|]); (split; [vm_compute; congruence | discriminate]).
Qed.

(** The two static objects are apart. *)
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

(** [slot_ps0] agrees with [slot_memory]: its objects are live, every
    byte is 0 and every aux slot empty. *)
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

(** `use` is safe under the interpreter's runtime, from the module's
    initial memory ([slot_initial]). *)
Theorem interp_slot_logic_safe : forall fuel,
  InterpSlotLogic.L.labelled_safe slot_registry InterpSlotLogic.slot_ge use_entry slot_memory
    InterpRuntime.start tt fuel (fun o => exists k, o = Ret (WInt k)).
Proof.
  intros fuel. apply (InterpSlotLogic.slot_logic_safe hiΣ).
  - exact slot_memory_ready.
  - exact slot_memory_disjoint.
  - exact slot_memory_agrees.
Qed.

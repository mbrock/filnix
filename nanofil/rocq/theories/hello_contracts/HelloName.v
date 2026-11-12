(** GNU Hello's `set_program_name` through the program logic of
    Logic.v (docs/logic.md, "GNU Hello through the logic", milestone 2).

    gnulib's progname.c: the first thing `main` does. It finds the
    last `/` of argv[0] ([wp_strrchr]); if seven bytes precede the base
    name, it compares them with "/.libs/" (`memeq`, by
    [memeq_spec]); if they match, it compares the base name with "lt-"
    ([wp_strncmp]) and skips it on a match. Then it stores the chosen
    pointers into three cells: Hello's `program_name` and libc's
    `program_invocation_name` and `program_invocation_short_name`.

    The compiled function has no check that argv[0] is not null:
    gnulib declares the parameter nonnull, so clang drops its abort
    branch, and strrchr of a null pointer would break its contract.
    [set_program_name_spec] therefore owns argv[0] as a string.

    Every path is safe whatever the comparisons return; the triple
    only says that each cell ends up holding a pointer with argv[0]'s
    capability. The proof follows the blocks: [spn_start] to the
    strrchr hit, [spn_L8] from the base name, [spn_L16] for "lt-" and
    [spn_L18] for the stores. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  HelloModule HelloLeaf.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The function and its data *)

(** `set_program_name(argv0)`. *)
Definition set_program_name_fn : func := Eval vm_compute in hello_fn "set_program_name".

(** strrchr for `/`, then is there a slash? *)
Definition s_start : block := Eval vm_compute in hblk set_program_name_fn "start".
(** The base name starts after the slash. *)
Definition s_L6 : block := Eval vm_compute in hblk set_program_name_fn "L6".
(** Do seven bytes precede the base name? *)
Definition s_L8 : block := Eval vm_compute in hblk set_program_name_fn "L8".
(** Are they "/.libs/"? *)
Definition s_L25 : block := Eval vm_compute in hblk set_program_name_fn "L25".
(** Branch on that answer. *)
Definition s_L26 : block := Eval vm_compute in hblk set_program_name_fn "L26".
(** Does the base name start with "lt-"? *)
Definition s_L16 : block := Eval vm_compute in hblk set_program_name_fn "L16".
(** Skip "lt-". *)
Definition s_L35 : block := Eval vm_compute in hblk set_program_name_fn "L35".
(** Store the three names. *)
Definition s_L18 : block := Eval vm_compute in hblk set_program_name_fn "L18".

(** `set_program_name` has its entry. *)
Lemma find_s_start : find_block (TAtom "start") (fn_blocks set_program_name_fn) = Some s_start.
Proof. vm_compute. reflexivity. Qed.
(** `set_program_name` has L6. *)
Lemma find_s_L6 : find_block (TAtom "L6") (fn_blocks set_program_name_fn) = Some s_L6.
Proof. vm_compute. reflexivity. Qed.
(** `set_program_name` has L8. *)
Lemma find_s_L8 : find_block (TAtom "L8") (fn_blocks set_program_name_fn) = Some s_L8.
Proof. vm_compute. reflexivity. Qed.
(** `set_program_name` has L25. *)
Lemma find_s_L25 : find_block (TAtom "L25") (fn_blocks set_program_name_fn) = Some s_L25.
Proof. vm_compute. reflexivity. Qed.
(** `set_program_name` has L26. *)
Lemma find_s_L26 : find_block (TAtom "L26") (fn_blocks set_program_name_fn) = Some s_L26.
Proof. vm_compute. reflexivity. Qed.
(** `set_program_name` has L16. *)
Lemma find_s_L16 : find_block (TAtom "L16") (fn_blocks set_program_name_fn) = Some s_L16.
Proof. vm_compute. reflexivity. Qed.
(** `set_program_name` has L35. *)
Lemma find_s_L35 : find_block (TAtom "L35") (fn_blocks set_program_name_fn) = Some s_L35.
Proof. vm_compute. reflexivity. Qed.
(** `set_program_name` has L18. *)
Lemma find_s_L18 : find_block (TAtom "L18") (fn_blocks set_program_name_fn) = Some s_L18.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name`'s entry binds argv[0]. *)
Lemma set_program_name_entry p :
  invocation set_program_name_fn [WPtr p] =
  mkFrame set_program_name_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `memeq` is a function of a genv with Hello's module. *)
Lemma find_memeq ge : ge_module ge = hello_module -> find_fn ge (TAtom "memeq") = Some (Defined memeq_fn).
Proof. intros Hm. unfold find_fn. rewrite Hm. vm_compute. reflexivity. Qed.

(** Hello's `program_name`: an 8-byte cell at 66080. *)
Definition program_name_b : Z := 66080.
(** The literal "/.libs/" of progname.c, read-only at 66112. *)
Definition libs_ptr : ptr := mkPtr 66112 (Ro 66112).
(** Its bytes. *)
Definition libs_bytes : list Z := [47; 46; 108; 105; 98; 115; 47].
(** The literal "lt-" of progname.c, read-only at 66144. *)
Definition lt_ptr : ptr := mkPtr 66144 (Ro 66144).
(** Its bytes. *)
Definition lt_bytes : list Z := [108; 116; 45].

(** Hello's symbols put `program_name` and the two literals there. *)
Lemma progname_globals :
  lookup (TAtom "program_name") hello_globals = Some (mkPtr program_name_b (Obj program_name_b)) /\
  lookup (TAtom "progname#str.3") hello_globals = Some libs_ptr /\
  lookup (TAtom "progname#str.4") hello_globals = Some lt_ptr.
Proof. vm_compute. auto. Qed.

(** `set_program_name` over any [[runtime]] R. *)
Module HelloNameOn (R : Runtime) (LG0 : LogicSig R).
Module HL := HelloLeafOn R LG0.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML HL.

Section name.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The genv links Hello, with the contracts the function calls. *)
Context (Hlinked : hello_linked ge)
  (Hstrrchr : registry (TAtom "strrchr") = Some (strrchr_contract world))
  (Hmemcmp : registry (TAtom "memcmp") = Some (memcmp_contract world))
  (Hstrncmp : registry (TAtom "strncmp") = Some (strncmp_contract world)).

(** A pointer store into the cell at offset 0 of the object b, with
    the region reg, keeps the world interpretation, whatever it held
    and whatever it now holds ([wp_raw_store_pointer]'s premise). *)
Definition store_keeps (b : Z) (reg : region) : Prop :=
  forall x xp m wd h,
    (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b 0, VAux (ptr_cap x)) :: cell b 0 (ptr_addr x) ->
       h !! l = Some v) ->
    wi m wd h ->
    wi (store_bytes (store_aux m (b + 0) (ptr_cap xp)) (b + 0) 8 (ptr_addr xp)) wd
      (overwrite ([(PLive b, VLive reg)] ++ (PAux b 0, VAux (ptr_cap xp)) :: cell b 0 (ptr_addr xp)) h).

(** The three cells: `program_name` in the object 66080 with the region
    pn, libc's `program_invocation_name` in the object nb with nreg,
    and `program_invocation_short_name` in sb with sreg, each its own
    object, as each Fil-C global is. *)
Context (pn nreg sreg : region) (nb sb : Z)
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hpn_end : program_name_b + 8 <= r_end pn)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48)
  (Kpn : store_keeps program_name_b pn) (Knb : store_keeps nb nreg) (Ksb : store_keeps sb sreg).

(** The Iris instance of the registry and wi. *)
Local Instance name_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation nexpr := (language.expr (nanofil_lang registry ge)).

(** The three cells, holding x, x and y. *)
Definition name_cells (x0 x1 y : ptr) : iProp Σ :=
  live program_name_b pn ∗ pcell program_name_b 0 x0 ∗ live nb nreg ∗ pcell nb 0 x1 ∗
  live sb sreg ∗ pcell sb 0 y.

(** The two literals, as strings. *)
Definition literals (r3 r4 : region) : iProp Σ :=
  string libs_ptr 66112 r3 libs_bytes ∗ string lt_ptr 66144 r4 lt_bytes.

(** The genv's `program_name` and literals are Hello's. *)
Lemma name_lookups :
  lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr program_name_b (Obj program_name_b)) /\
  lookup (TAtom "progname#str.3") (ge_globals ge) = Some libs_ptr /\
  lookup (TAtom "progname#str.4") (ge_globals ge) = Some lt_ptr.
Proof.
  destruct progname_globals as (H1 & H2 & H3). destruct Hlinked as (_ & Hg & _).
  split; [exact (Hg _ _ H1)|]. split; [exact (Hg _ _ H2) | exact (Hg _ _ H3)].
Qed.

(** The stores, from L18 after its phis, where `pr.1` reads as x and
    `pr.3` as y: each cell's check passes and its store keeps the world
    interpretation. *)
Lemma spn_L18 e x y x0 x1 y0 Φ :
  lookup (TAtom "pr.1") e = Some (WPtr x) -> lookup (TAtom "pr.3") e = Some (WPtr y) ->
  name_cells x0 x1 y0 -∗ ▷ (name_cells x x y -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L18") (b_insts s_L18) (b_jump s_L18)))
        : nexpr) {{ Φ }}.
Proof.
  intros Hx Hy. destruct name_lookups as (Hpn & _ & _).
  destruct Hnb_cell as (Hn0 & Hn8 & Hnend & Hn48). destruct Hsb_cell as (Hs0 & Hs8 & Hsend & Hs48).
  iIntros "(Hlp & Hcp & Hln & Hcn & Hls & Hcs) HΦ". cbn [b_insts b_jump s_L18].
  unfold program_name_b in *.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_check with "Hlp"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
                                  addr_premise |].
  iNext. iIntros "Hlp". gen_env.
  iApply (wp_raw_store_pointer with "Hlp Hcp");
    [word_premise | word_premise | reflexivity | addr_premise | reflexivity | apply Kpn |].
  iNext. iIntros "Hlp Hcp".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_check with "Hln"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
                                  addr_premise |].
  iNext. iIntros "Hln". gen_env.
  iApply (wp_raw_store_pointer with "Hln Hcn");
    [word_premise | word_premise | reflexivity | addr_premise | addr_premise | apply Knb |].
  iNext. iIntros "Hln Hcn".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_check with "Hls"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
                                  addr_premise |].
  iNext. iIntros "Hls". gen_env.
  iApply (wp_raw_store_pointer with "Hls Hcs");
    [word_premise | word_premise | reflexivity | addr_premise | addr_premise | apply Ksb |].
  iNext. iIntros "Hls Hcs".
  iApply wp_ret_void. iNext. iApply "HΦ". iFrame.
Qed.

(** Take every branch of the goal's conditions: each path is safe. *)
Ltac all_cases :=
  repeat match goal with |- context[if ?t then _ else _] => destruct t end; cbn [edge_label].

(** The "lt-" test, from L16, with `v15` reading as the base name, the
    suffix of argv[0] from its j-th byte: strncmp of it and "lt-", and
    either answer goes on to the stores, past "lt-" or not. *)
Lemma spn_L16 e p b reg ys j r3 r4 x0 x1 y0 Φ :
  lookup (TAtom "v15") e = Some (WPtr (mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p))) ->
  (j <= length ys)%nat ->
  string p b reg ys -∗ literals r3 r4 -∗ name_cells x0 x1 y0 -∗
  ▷ (∀ x y, ⌜ptr_cap x = ptr_cap p /\ ptr_cap y = ptr_cap p⌝ -∗ string p b reg ys -∗ literals r3 r4 -∗
     name_cells x x y -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L16") (b_insts s_L16) (b_jump s_L16)))
        : nexpr) {{ Φ }}.
Proof.
  intros Hv15 Hj. destruct name_lookups as (_ & _ & Hlt).
  iIntros "Hs [Hlibs Hlt] Hc HΦ". iDestruct "Hs" as "[%Hok Hps]".
  iAssert (string p b reg ys) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hcap & Hb0 & Hb1 & Hb2 & Hb3 & _). cbn [b_insts b_jump s_L16].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iDestruct (string_suffix _ _ _ _ j with "Hs") as "[Hsuf Hback]"; [exact Hj|].
  iApply (wp_strncmp with "Hsuf Hlt");
    [exact Hstrncmp | apply linked_outside; [exact Hlinked | reflexivity] |
     apply linked_unbound; [exact Hlinked | reflexivity] | word_premise | word_premise | word_premise |
     vm_compute; intuition congruence |].
  iNext. iIntros (bits) "Hsuf Hlt". iDestruct ("Hback" with "Hsuf") as "Hs". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_branch; [word_premise|]. iNext. all_cases.
  - iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (spn_L18 with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc".
    iApply ("HΦ" with "[%] Hs [$Hlibs $Hlt] Hc"). split; reflexivity.
  - iApply wp_enter; [exact find_s_L35 | reflexivity |]. iNext. cbn [b_insts b_jump s_L35].
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat j + 3));
      [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
    iNext. gen_env. iApply wp_goto. iNext.
    iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (spn_L18 with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc".
    iApply ("HΦ" with "[%] Hs [$Hlibs $Hlt] Hc"). split; reflexivity.
Qed.

(** From L8, with `v15` reading as the base name, the suffix of argv[0]
    from its j-th byte, and `v0` as argv[0]: if seven bytes precede the
    base name, `memeq` compares them with "/.libs/"; whatever it says,
    the run goes on to the "lt-" test or to the stores. *)
Lemma spn_L8 e p b reg ys j r3 r4 x0 x1 y0 Φ :
  lookup (TAtom "v15") e = Some (WPtr (mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p))) ->
  lookup (TAtom "v0") e = Some (WPtr p) -> (j <= length ys)%nat ->
  string p b reg ys -∗ literals r3 r4 -∗ name_cells x0 x1 y0 -∗
  ▷ (∀ x y, ⌜ptr_cap x = ptr_cap p /\ ptr_cap y = ptr_cap p⌝ -∗ string p b reg ys -∗ literals r3 r4 -∗
     name_cells x x y -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L8") (b_insts s_L8) (b_jump s_L8)))
        : nexpr) {{ Φ }}.
Proof.
  intros Hv15 Hv0 Hj. destruct name_lookups as (_ & Hlibs & _).
  iIntros "Hs [Hl3 Hl4] Hc HΦ". iDestruct "Hs" as "[%Hok Hps]".
  iAssert (string p b reg ys) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hcap & Hb0 & Hb1 & Hb2 & Hb3 & Hys). cbn [b_insts b_jump s_L8].
  assert (Hjz : Z.of_nat j <= Z.of_nat (length ys)) by lia.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  destruct (Nat.lt_ge_cases j 7) as [Hj7 | Hj7].
  - (* Fewer than seven bytes precede the base name. *)
    assert (Hz7 : Z.of_nat j < 7) by lia.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L26 | reflexivity |]. iNext. cbn [b_insts b_jump s_L26]. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (spn_L18 with "Hc"); [word_premise | word_premise |]. iNext. iIntros "Hc".
    iApply ("HΦ" with "[%] Hs [$Hl3 $Hl4] Hc"). split; reflexivity.
  - (* Compare the seven bytes before it with "/.libs/". *)
    assert (Hz7 : 7 <= Z.of_nat j) by lia.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L25 | reflexivity |]. iNext. cbn [b_insts b_jump s_L25].
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + (ptr_addr p - b + Z.of_nat (j - 7))));
      [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
    iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iDestruct (string_window _ _ _ _ (j - 7) 7 with "Hs") as "(_ & Hl & Hw & Hback)"; [lia|].
    iDestruct (string_window _ _ _ _ 0 7 with "Hl3") as "(%Hok3 & Hl3 & Hw3 & Hback3)"; [cbn; lia|].
    pose proof Hok3 as (_ & _ & _ & H3end & _).
    iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ memeq_fn
              (invocation memeq_fn [WPtr (mkPtr (b + (ptr_addr p - b + Z.of_nat (j - 7))) (ptr_cap p));
                                    WPtr libs_ptr; WInt 7]));
      [word_premise | apply find_memeq; exact (proj1 Hlinked) | reflexivity |].
    iNext.
    iApply (memeq_spec registry wi ge Hlinked b reg (ptr_addr p - b + Z.of_nat (j - 7)) _ (ptr_cap p)
              66112 r3 (ptr_addr libs_ptr - 66112 + Z.of_nat 0) _ (Ro 66112) with "Hl Hw Hl3 Hw3");
      [exact Hmemcmp | rewrite length_take length_drop; lia | exact Hcap | right; reflexivity |
       rewrite !length_take !length_drop; cbn [length libs_bytes]; lia | lia | cbn; lia |
       rewrite length_take length_drop; lia |
       rewrite length_take length_drop; cbn [ptr_addr libs_ptr length libs_bytes] in H3end |- *; lia |
       rewrite length_take length_drop; lia |
       apply Forall_take, Forall_drop; eapply Forall_impl; [exact Hys | intros x Hx; cbn in Hx; lia] |
       vm_compute; repeat constructor; discriminate |].
    iNext. iIntros (k) "Hl Hw Hl3 Hw3". iDestruct ("Hback" with "Hl Hw") as "Hs".
    iDestruct ("Hback3" with "Hl3 Hw3") as "Hl3".
    iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
    iApply wp_goto. iNext.
    iApply wp_enter; [exact find_s_L26 | word_premise |]. iNext. cbn [b_insts b_jump s_L26]. gen_env.
    iApply wp_branch; [word_premise|]. iNext. all_cases.
    + iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
      iApply (spn_L18 with "Hc"); [word_premise | word_premise |]. iNext. iIntros "Hc".
      iApply ("HΦ" with "[%] Hs [$Hl3 $Hl4] Hc"). split; reflexivity.
    + iApply wp_enter; [exact find_s_L16 | reflexivity |]. iNext.
      iApply (spn_L16 with "Hs [$Hl3 $Hl4] Hc"); [word_premise | exact Hj |]. iExact "HΦ".
Qed.

(** `set_program_name`'s triple: owning argv[0] as the string at p,
    the literals and the three cells, the call is safe and each cell
    ends up holding a pointer with p's capability: the first two the
    same one. *)
Lemma set_program_name_spec p b reg ys r3 r4 x0 x1 y0 Φ :
  string p b reg ys -∗ literals r3 r4 -∗ name_cells x0 x1 y0 -∗
  ▷ (∀ x y, ⌜ptr_cap x = ptr_cap p /\ ptr_cap y = ptr_cap p⌝ -∗ string p b reg ys -∗ literals r3 r4 -∗
     name_cells x x y -∗ Φ RetVoid) -∗
  WP (ERun (invocation set_program_name_fn [WPtr p]) : nexpr) {{ Φ }}.
Proof.
  iIntros "Hs Hlit Hc HΦ". iDestruct "Hs" as "[%Hok Hps]".
  iAssert (string p b reg ys) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hcap & Hb0 & Hb1 & Hb2 & Hb3 & _). rewrite set_program_name_entry.
  iApply wp_enter; [exact find_s_start | reflexivity |]. iNext. cbn [b_insts b_jump s_start].
  iApply (wp_strrchr with "Hs");
    [exact Hstrrchr | apply linked_outside; [exact Hlinked | reflexivity] |
     apply linked_unbound; [exact Hlinked | reflexivity] | reflexivity | reflexivity |
     vm_compute; intuition congruence | vm_compute; intuition congruence |].
  iNext. iIntros (q Hq) "Hs".
  destruct Hq as [-> | (i & Hi & ->)].
  - (* No slash: the base name is argv[0]. *)
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [reflexivity|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L8 | reflexivity |]. iNext.
    iApply (spn_L8 _ _ _ _ _ 0 with "Hs Hlit Hc HΦ");
      [destruct p; cbn; rewrite Z.add_0_r; reflexivity | reflexivity | lia].
  - (* A slash at i: the base name starts after it. *)
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L6 | reflexivity |]. iNext. cbn [b_insts b_jump s_L6].
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat (S i)));
      [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |].
    iNext. iApply wp_goto. iNext.
    iApply wp_enter; [exact find_s_L8 | reflexivity |]. iNext.
    iApply (spn_L8 _ _ _ _ _ (S i) with "Hs Hlit Hc HΦ"); [reflexivity | reflexivity | lia].
Qed.

End name.
End HelloNameOn.

(** [HelloNameOn] over a Logic instance of its own. *)
Module HelloName (R : Runtime).
Module LG0 := Logic R.
Include HelloNameOn R LG0.
End HelloName.

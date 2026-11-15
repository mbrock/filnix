(** GNU Hello calls getopt_long with its argument vector and option table.
    This file proves that the call preserves the arguments and returns
    the option token. It also connects initialization to the loop's
    first block and describes the resources carried between iterations. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia Permutation.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs HelloName
  HelloProgName Startup Getopt GetoptLogic HelloVersion HelloMainStart.
Open Scope Z_scope.
Open Scope list_scope.
Import HelloMainBase.MainDefinitions.

Module HelloMainGetopt (R : Runtime).
Include HelloMainStart R.
Import HLo HL ML LG.
Import L LG SL ML LL HL.

Local Hint Opaque main_fn pts bytes auxes live pcell main_irisGS
  HP.HN.literals HP.HN.name_cells : typeclass_instances.

Section main.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

Let section_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  main_irisGS registry wi ge.
Local Existing Instance section_irisGS.
Local Hint Opaque section_irisGS : typeclass_instances.
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

Local Ltac mn_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (main_block s));
  [abstract (vm_cast_no_check (eq_refl (Some (main_block s)))) | word_premise |]; iNext;
  cbn [b_insts b_jump main_block hblk].

Context (Hlinked : hello_linked ge).

Context (Kalloc : forall q m wd h base, fresh m q base -> wi m wd h ->
     wi (allocated m q base) wd (overwrite (obj_ps base q) h)).

Context (Hmemset : registry (TAtom "memset") = Some (memset_contract libc_world))
  (Kmemset : forall b reg o xs cs m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) 0 8 m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate 8 0) (clear_slots o cs)) h)).

Context (Hstrrchr : registry (TAtom "strrchr") = Some (strrchr_contract libc_world))
  (Hmemcmp : registry (TAtom "memcmp") = Some (memcmp_contract libc_world))
  (Hstrncmp : registry (TAtom "strncmp") = Some (strncmp_contract libc_world)).

Context (pn nreg sreg : region) (nb sb : Z)
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hpn_end : program_name_b + 8 <= r_end pn)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48)
  (Kpn : HP.HN.store_keeps wi program_name_b pn) (Knb : HP.HN.store_keeps wi nb nreg)
  (Ksb : HP.HN.store_keeps wi sb sreg).

Context (rep : mem -> libc_world -> Prop) (requests : list word -> mem -> libc_world -> Z -> Z -> Prop)
  (Hsetlocale : registry (TAtom "setlocale") = Some (libc_setlocale_contract rep requests))
  (Hlent : forall m w h k p t,
     wi m w h -> live_disjoint m -> objects_fit (m_regions m) -> freed_empty (m_regions m) ->
     h !! PName k = Some (VName p t) -> lent_at m h p t)
  (Hset_pre : forall m w h c p b reg bytes, wi m w h -> In c locale_categories ->
     string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
     libc_setlocale_pre rep [WInt c; WPtr p] m w)
  (Kset : forall r args c p s m w h trace values s' m' w', wi m w h -> agrees m h -> live_disjoint m -> R.ready s m ->
     M.E.invoke (libc_setlocale_contract rep requests) r args [WInt c; WPtr p] s m w trace (CallReturn values) s' m' w' ->
     exists q (new : Z -> ptr * list Z) c', values = [WPtr q] /\ (q = mkPtr 0 CNone \/ q = (new c).1) /\
       agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\
       wi m' w' (overwrite (codec_ps c') (rename h locale_categories new))).

Context (Kpstore : forall b reg o x xp m wd h,
  (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
     h !! l = Some v) ->
  wi m wd h ->
  wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)).

Context (atexit_spec : contract libc_world)
  (Hatexit : registry (TAtom "atexit") = Some atexit_spec)
  (Hatexit_ret : contract_returns atexit_spec = RClass W)
  (Hatexit_abi : contract_abi atexit_spec (CResult (TAtom "v15") W) [Arg P (Tmp (TAtom "v14"))])
  (Hatexit_pre : forall m w h, wi m w h -> contract_pre atexit_spec [WPtr close_stdout_ptr] m w)
  (Katexit : forall r args s m w h trace values s' m' w', wi m w h -> agrees m h -> live_disjoint m ->
     R.ready s m ->
     M.E.invoke atexit_spec r args [WPtr close_stdout_ptr] s m w trace (CallReturn values) s' m' w' ->
     exists x, values = [WInt x] /\ 0 <= x < 2 ^ 32 /\ agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\
       wi m' w' h).

Local Notation main_start := (main_start registry wi ge Hlinked Kalloc Hmemset Kmemset
  Hstrrchr Hmemcmp Hstrncmp pn nreg sreg nb sb Hnb Hsb Hpn_end Hnb_cell Hsb_cell
  Kpn Knb Ksb rep requests Hsetlocale Hlent Hset_pre Kset Kpstore
  atexit_spec Hatexit Hatexit_ret Hatexit_abi Hatexit_pre Katexit).

(** ## getopt_long's call

    Main owns the argument vector and each argument string before
    calling the option parser. The call may reorder the vector, but
    preserves the strings and records the next option's position. *)

(** The aligned argument vector fits its object, including the null sentinel.
    Its positive argument count fits a C integer, and each argument is a string. *)
Context (av : Z) (ar : region) (sargs : list argument)
  (Hav : 0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length sargs) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48)
  (Hargc : 1 <= Z.of_nat (length sargs) < 2 ^ 31)
  (Hargs : Forall (fun s => string_ok (arg_ptr s) (arg_base s) (arg_region s) (arg_text s)) sargs).

(** Each argument pointer and the null sentinel occupy eight byte and auxiliary slots. *)
Local Notation argv_len := (8 * (length sargs + 1))%nat.

(** The parser contract records its initial state, allocations, and
    state changes when a call returns. *)
Context (initialized running : mem -> libc_world -> Prop)
  (grequests : list word -> mem -> libc_world -> Z -> Z -> Prop)
  (transition : list word -> mem -> libc_world -> list Z -> list event -> list word -> mem -> libc_world -> Prop)
  (Hgetopt : registry (TAtom "getopt_long") =
     Some (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition)).

(** The contract. *)
Local Notation getopt_spec :=
  (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition).

(** wi ties libc's optarg and optind cells to the parser's state and
    the getopt token, as GetoptLogic.v's reads need. *)
Context (optarg_cell optind_cell : ptr)
  (Hgetopt_wi : forall m w h, wi m w h ->
     getopt_state_at m (libc_getopt_view w) /\ getopt_optarg_cell (libc_getopt_view w) = optarg_cell /\
     getopt_optind_cell (libc_getopt_view w) = optind_cell /\ getopt_current (libc_getopt_view w) h).

(** wi keeps Hello's option literals in memory. *)
Context (Htable : forall m w h, wi m w h -> hello_table_at m).

(** The parser's private memory remains separate from the caller's
    argument vector and strings. Its input buffers remain readable. *)
Context (Hgetopt_env : forall m w h xs cs, wi m w h -> agrees m h -> live_disjoint m ->
   (forall l v, (l, v) ∈ block_ps av ar 0 xs cs ++ flat_map arg_ps sargs -> h !! l = Some v) ->
   getopt_input_at m (hello_input av sargs) ->
   libc_getopt_rep initialized m w /\
   Forall (writable_span m) (getopt_roots (libc_getopt_view w)) /\
   Forall (fun s => readable_bytes m (span_ptr s) (span_size s)) (getopt_reads (libc_getopt_view w)) /\
   getopt_separated (hello_input av sargs) (libc_getopt_view w) /\
   getopt_disjoint (getopt_public_writes (hello_input av sargs) (libc_getopt_view w)) /\
   getopt_private_owned m (hello_input av sargs) (libc_getopt_view w)).

(** getopt_long's private roots and libc's cells are apart from the
    program's objects, and it releases none of them. *)
Context (Hgetopt_apart : forall m w h, wi m w h ->
   (forall s a, In s (getopt_roots (libc_getopt_view w) ++ getopt_cells (libc_getopt_view w)) ->
      span_contains s a -> ~ owned_live h m a) /\
   ids_apart (getopt_owned (libc_getopt_view w)) h).

(** A parser call preserves the world interpretation after updating
    the argument vector and the current option's value and position. *)
Context (Kgetopt : forall r args xs s m w h trace values s' m' w' bs cs,
   M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' ->
   (forall l v, (l, v) ∈ block_ps av ar 0 bs cs -> h !! l = Some v) -> wi m w h ->
   agrees m h -> live_disjoint m -> R.ready s m ->
   wi m' w' (overwrite (block_ps av ar 0 (mem_bytes m' av argv_len) (mem_auxes m' av argv_len) ++
     getopt_ps (getopt_optarg (libc_getopt_view w')) (getopt_optind (libc_getopt_view w'))) h)).

Local Notation order_length := (order_length sargs).

Local Notation argv_slots := (argv_slots av ar sargs Hargs).
Local Notation getopt_admitted := (getopt_admitted wi av ar sargs Hav Hargc Hargs initialized
  optarg_cell optind_cell Hgetopt_wi Htable Hgetopt_env).

(** A return of getopt_long satisfies its postcondition. *)
Lemma getopt_returned r args xs s m w trace values s' m' w' :
  M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' ->
  exists born, getopt_post (hello_input av sargs) libc_getopt_view (libc_getopt_rep initialized)
    xs m w born trace (CallReturn values) m' w'.
Proof.
  intros H. apply GR.refined_invoke_base in H.
  inversion H as [trace' ending s0 m0 w0 born Habi Hpre Hp Hpost | ]; subst. exists born. exact Hpost.
Qed.

Local Notation getopt_step := (getopt_step wi transition).

(** A returning parser call makes the state transition promised by its contract. *)
Lemma getopt_stepped r args xs s m w h trace values s' m' w' a i :
  M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' -> wi m w h ->
  (forall l v, (l, v) ∈ getopt_ps a i -> h !! l = Some v) -> getopt_step a i values.
Proof.
  intros Hi Hw Kt. destruct (GR.refined_return _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Ht).
  exists xs, m, w, h, born, trace, m', w'. auto.
Qed.

(** The parser changes only the argument vector in the caller's memory.
    Updating that vector's ownership restores agreement with memory;
    the other live objects remain separate. *)
Lemma getopt_frame_ok r args s m w h trace values s' m' w' ps cs a' i' :
  M.E.invoke getopt_spec r args (getopt_words (hello_input av sargs)) s m w trace (CallReturn values) s' m' w' ->
  wi m w h -> agrees m h -> live_disjoint m -> R.ready s m ->
  length (argv_bytes ps) = argv_len -> length cs = argv_len ->
  (forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs -> h !! l = Some v) ->
  agrees m' (overwrite (block_ps av ar 0 (mem_bytes m' av argv_len) (mem_auxes m' av argv_len) ++
                        getopt_ps a' i') h) /\
  live_disjoint m' /\ R.ready s' m'.
Proof.
  intros Hi Hw Ha Hd Hr Lx Lc Kb.
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48).
  assert (Hlv : live_at m av ar).
  { apply (Ha (PLive av) (VLive ar)), Kb. apply elem_of_cons. left. reflexivity. }
  destruct (Hgetopt_apart m w h Hw) as [Hroots Hrel].
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  set (ks := (byte_ps av 0 (argv_bytes ps) ++ aux_ps av 0 cs).*1).
  set (outs := fun x => span_contains (mkSpan (mkPtr av (Obj av)) (8 * (Z.of_nat (length sargs) + 1))) x).
  assert (Hwr : contract_writes getopt_spec (getopt_words (hello_input av sargs)) m w =
                (getopt_roots (libc_getopt_view w) ++ getopt_cells (libc_getopt_view w)) ++
                  [mkSpan (mkPtr av (Obj av)) (8 * (Z.of_nat (length sargs) + 1))]).
  { rewrite <- app_assoc. reflexivity. }
  destruct (prefix_agrees_out _ _ _ _ _ _ _ _ _ _ _ h ks outs Hp Hr Hd) as (Ha' & _ & Hd' & _).
  - intros l v Hl _. exact (Ha l v Hl).
  - intros l v Hl Hm. exact (agree_piece_registered _ _ _ Hm (Ha l v Hl)).
  - rewrite Hwr. intros sp x Hin Hsp Hol. apply in_app_or in Hin as [Hin|Hin].
    + exfalso. exact (Hroots sp x Hin Hsp Hol).
    + destruct Hin as [<-|[]]. exact Hsp.
  - intros l v Hl Hk. destruct l as [b|b o|b o|k]; try exact I; intros reg Hlv' Ho' He' Hout; apply Hk;
      unfold outs, span_contains in Hout; cbn [span_ptr span_size ptr_addr] in Hout;
      (apply (block_key m av ar 0 (argv_bytes ps) cs _ b o reg Hd Hlv);
       [lia | rewrite Lx; lia | rewrite Lc Lx; reflexivity | auto | exact Hlv' | exact Ho' | exact He' |
        rewrite Lx; lia]).
  - exact Hrel.
  - assert (Hlv' : live_at m' av ar).
    { apply (Ha' (PLive av) (VLive ar)); [apply Kb; apply elem_of_cons; left; reflexivity|].
      exact (live_not_key _ _ _ _ _). }
    split; [|split; [exact Hd' | exact Hr']].
    intros l v Hl. apply lookup_overwrite in Hl as [Hin | [Hnk Hh]].
    + apply elem_of_app in Hin as [Hin|Hin].
      * pose proof (block_after m' av ar 0 argv_len l v Hlv') as H. rewrite !Z.add_0_r in H.
        apply H; [lia | lia | exact Hin].
      * apply list_elem_of_singleton in Hin. injection Hin as -> ->. exact I.
    + apply (Ha' l v Hh). intros Hk. apply Hnk. rewrite fmap_app. apply elem_of_app. left.
      pose proof (block_keys_after m' av ar 0 (argv_bytes ps) cs argv_len l Lx Lc Hk) as H.
      rewrite Z.add_0_r in H. exact H.
Qed.

(** The parser returns an option code and an updated argument order.
    It preserves every argument string and keeps its position within
    the vector. A greeting option supplies a nonnull borrowed string. *)
Lemma wp_main_getopt f e ls lab d va vv vs vl vi rest j ps cs a i Φ :
  map_option (arg_x ge e) [Arg W va; Arg P vv; Arg P vs; Arg P vl; Arg P vi] =
    Some (getopt_words (hello_input av sargs)) ->
  getopt_order (map arg_ptr sargs) ps -> argv_caps cs ps -> 0 <= i <= Z.of_nat (length sargs) ->
  pts (block_ps av ar 0 (argv_bytes ps) cs) -∗ pts (flat_map arg_ps sargs) -∗ pts (getopt_ps a i) -∗
  ▷ (∀ code ps' cs' a' i',
       ⌜getopt_order (map arg_ptr sargs) ps' /\ argv_caps cs' ps' /\ 0 <= i' <= Z.of_nat (length sargs) /\
        getopt_int code /\ (code = 103 -> getopt_borrow (hello_input av sargs) a' /\ ptr_addr a' <> 0) /\
        getopt_step a i [WInt (code mod 2 ^ 32)]⌝ -∗
       pts (block_ps av ar 0 (argv_bytes ps') cs') -∗ pts (flat_map arg_ps sargs) -∗ pts (getopt_ps a' i') -∗
       WP (ERun (mkFrame f (put d (WInt (code mod 2 ^ 32)) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
     (Exec lab (Call (CResult d W) (Global (TAtom "getopt_long"))
                  [Arg W va; Arg P vv; Arg P vs; Arg P vl; Arg P vi] :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hx Ho Hc Hi. iIntros "Hb Hs Ht HK".
  assert (Lp : length ps = length sargs) by exact (order_length ps Ho).
  assert (Lx : length (argv_bytes ps) = argv_len).
  { unfold argv_bytes. rewrite length_slots_bytes length_app Lp. cbn [length]. lia. }
  assert (Lc : length cs = argv_len).
  { destruct Hc as [Lc _]. rewrite Lc length_app Lp. cbn [length]. lia. }
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ getopt_spec (getopt_words (hello_input av sargs))
            (pts (block_ps av ar 0 (argv_bytes ps) cs) ∗ pts (flat_map arg_ps sargs) ∗ pts (getopt_ps a i))
            with "[$Hb $Hs $Ht] [HK]");
    [apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | reflexivity | exact Hgetopt | exact Hx | | |].
  - split; [right; eexists; reflexivity | do 5 eexists; reflexivity].
  - iIntros (σ) "Hσ (Hb & Hs & Ht)". iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hb") as %Kb. iDestruct (pts_lookup with "Hh Hs") as %Ks.
    iDestruct (pts_lookup with "Hh Ht") as %Kt. iPureIntro.
    exact (getopt_admitted _ _ _ _ _ _ _ Hw Ha Hd Ho Hc Hi Kb Ks Kt).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Hb & Hs & Ht)".
    destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hb") as %Kb. iDestruct (pts_lookup with "Hh Ht") as %Kt.
    destruct (getopt_returned _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & _ & Hin' & _ & _ & code & Hend & Hres).
    injection Hend as ->.
    pose proof (getopt_stepped _ _ _ _ _ _ _ _ _ _ _ _ a i Hinv Hw Kt) as Hstep.
    change (getopt_argc (hello_input av sargs)) with (Z.of_nat (length sargs)) in Hres.
    assert (E : (Z.of_nat (length sargs) =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite E in Hres. destruct Hres as (_ & _ & Hrange & Hresult).
    destruct (hello_code _ _ _ _ _ Hresult) as [Hint Hg].
    destruct Hin' as (_ & _ & (_ & _ & _ & ps' & Ho' & Hsl') & _).
    rewrite hello_input_order in Ho'.
    change (ptr_addr (getopt_argv (hello_input av sargs))) with av in Hsl'.
    assert (Lp' : length ps' = length sargs) by exact (order_length ps' Ho').
    destruct (argv_of_slots m' av ps' Hsl') as [Eb Ec].
    assert (EL : (8 * length (ps' ++ [null]))%nat = argv_len) by (rewrite length_app Lp'; reflexivity).
    rewrite EL in Eb, Ec.
    set (a' := getopt_optarg (libc_getopt_view w')). set (i' := getopt_optind (libc_getopt_view w')).
    destruct (getopt_frame_ok _ _ _ _ _ _ _ _ _ _ _ ps cs a' i' Hinv Hw Ha Hd Hr Lx Lc Kb) as (Ha' & Hd' & Hr').
    pose proof (Kgetopt _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv Kb Hw Ha Hd Hr) as Hw'.
    rewrite Eb in Ha', Hw'.
    iMod (pts_update _ (block_ps av ar 0 (argv_bytes ps) cs ++ getopt_ps a i)
            (block_ps av ar 0 (argv_bytes ps') (mem_auxes m' av argv_len) ++ getopt_ps a' i')
            with "Hh [Hb Ht]") as "[Hh Hn]".
    { rewrite !fmap_app. rewrite (block_ps_keys av ar 0 (argv_bytes ps) cs); [reflexivity | |].
      - rewrite <- Eb, length_mem_bytes. symmetry. exact Lx.
      - rewrite length_mem_auxes. symmetry. exact Lc. }
    { rewrite pts_app. iFrame. }
    iModIntro. iExists (put d (WInt (code mod 2 ^ 32)) e). iSplit.
    { iPureIntro. unfold external_env. cbn. rewrite Z.mod_mod; [reflexivity | lia]. }
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. auto.
    + rewrite pts_app. iDestruct "Hn" as "[Hb Ht]".
      iApply ("HK" $! code ps' (mem_auxes m' av argv_len) a' i' with "[%] Hb Hs Ht").
      split; [exact Ho'|]. split; [exact Ec|]. split; [exact Hrange|]. split; [exact Hint|].
      split; [exact Hg | exact Hstep].
Qed.

(** ## The option loop

    Each parser call either selects another greeting or exits the loop.
    The loop preserves the argument strings, parser state, and greeting
    cell until a continuation handles help, version output, or operands. *)

(** libc's optarg cell is the global optarg, and both cells are at
    word addresses. *)
Context (Hoptarg_g : lookup (TAtom "optarg") (ge_globals ge) = Some optarg_cell)
  (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64).

Local Notation greeting_ok := (greeting_ok av sargs).

(** Each iteration owns the argument vector, its strings, the parser
    state, and the cell holding the selected greeting. *)
Definition loop_res (b4 : Z) (ps : list ptr) (cs : list cap) (a : ptr) (i : Z) (g : ptr) : iProp Σ :=
  pts (block_ps av ar 0 (argv_bytes ps) cs) ∗ pts (flat_map arg_ps sargs) ∗ pts (getopt_ps a i) ∗
  live b4 (mkRegion b4 (b4 + 16) Heap Live) ∗ pcell b4 0 g.

Local Notation loop_facts := (loop_facts av sargs).

(** An exit continuation receives the loop's ownership and a Boolean error flag. *)
Definition loop_exit (b4 b6 : Z) (lab from : String.string)
    (Φ : language.val (nanofil_lang registry ge) → iProp Σ) : iProp Σ :=
  ∀ e ps cs a i g lose,
    ⌜loop_facts e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)⌝ -∗
    loop_res b4 ps cs a i g -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom lab) (Some (TAtom from)))) : mexpr) {{ Φ }}.

(** Splitting the argument vector exposes its first pointer and preserves the remaining slots. *)
Lemma argv_block_split b reg q rest cs :
  pts (block_ps b reg 0 (argv_bytes (q :: rest)) (ptr_cap q :: cs)) ⊣⊢
  live b reg ∗ pcell b 0 q ∗ bytes b 8 (argv_bytes rest) ∗ auxes b 1 cs.
Proof.
  rewrite block_pts /bytes /auxes /pcell /argv_bytes /slots_bytes. cbn [app flat_map].
  rewrite byte_ps_app aux_ps_cons. change (length (slot_bytes (ptr_addr q))) with 8%nat.
  change (0 + Z.of_nat 8) with 8. change (0 + 1) with 1.
  assert (E : byte_ps b 0 (slot_bytes (ptr_addr q)) = cell b 0 (ptr_addr q)) by reflexivity.
  rewrite E pts_app.
  change ((PAux b 0, VAux (ptr_cap q)) :: aux_ps b 1 cs) with ([(PAux b 0, VAux (ptr_cap q))] ++ aux_ps b 1 cs).
  change ((PAux b 0, VAux (ptr_cap q)) :: cell b 0 (ptr_addr q)) with
    ([(PAux b 0, VAux (ptr_cap q))] ++ cell b 0 (ptr_addr q)).
  rewrite !pts_app.
  iSplit; [iIntros "(Hl & [Hc Hy] & [Ha Hx])" | iIntros "(Hl & [Ha Hc] & Hy & Hx)"]; iFrame.
Qed.

(** Initialization temporarily separates the first argument to set the
    program name. It restores that argument before entering the option
    loop and transfers the remaining resources to the continuation. *)
Lemma main_to_L8 s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix Φ :
  sargs = s0 :: srest -> argv_caps cs0 (map arg_ptr sargs) -> 0 <= ix <= Z.of_nat (length sargs) ->
  pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) cs0) -∗ pts (flat_map arg_ps sargs) -∗
  pts (getopt_ps a ix) -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  ▷ (∀ e b4 b6 (i k : nat) q (new : Z -> ptr * list Z) c',
       ⌜start_vars e (Z.of_nat (length sargs)) av b4 b6 /\
        lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
        fresh_ok b4 /\ fresh_ok b6 /\ (i <= length (arg_text s0))%nat /\ (k <= length (arg_text s0))%nat /\
        (q = mkPtr 0 CNone \/ q = (new 6).1)⌝ -∗
       ⌜loop_facts e b4 b6 (map arg_ptr sargs) cs0 ix greeting_ptr⌝ -∗
       loop_res b4 (map arg_ptr sargs) cs0 a ix greeting_ptr -∗
       HP.HN.literals r3 r4 -∗
       HP.HN.name_cells pn nreg sreg nb sb
         (mkPtr (ptr_addr (arg_ptr s0) + Z.of_nat i) (ptr_cap (arg_ptr s0)))
         (mkPtr (ptr_addr (arg_ptr s0) + Z.of_nat i) (ptr_cap (arg_ptr s0)))
         (mkPtr (ptr_addr (arg_ptr s0) + Z.of_nat k) (ptr_cap (arg_ptr s0))) -∗
       ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗ pts (codec_ps c') -∗
       string empty_ptr 69968 r80 [] -∗
       bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15 CNone) -∗
       live b6 (mkRegion b6 (b6 + 16) Heap Live) -∗ bytes b6 0 (replicate 8 0) -∗
       bytes b6 8 (replicate 8 0) -∗ auxes b6 0 (clear_slots 0 (replicate 8 CNone)) -∗
       auxes b6 8 (replicate 8 CNone) -∗
       WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof.
  intros Hhd [Lc Hc] Hix. iIntros "Hb Hs Ht Hlit Hcells Hks Hcod Hs80 HK".
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48).
  assert (Hok0 : string_ok (arg_ptr s0) (arg_base s0) (arg_region s0) (arg_text s0)).
  { apply (proj1 (List.Forall_forall _ _) Hargs). rewrite Hhd. left. reflexivity. }
  assert (Ec0 : exists csr, cs0 = ptr_cap (arg_ptr s0) :: csr).
  { pose proof (Hc 0%nat (arg_ptr s0)) as H. rewrite Hhd in H. specialize (H eq_refl).
    destruct cs0 as [|c csr]; [discriminate H|]. cbn in H. injection H as ->. eauto. }
  destruct Ec0 as (csr & ->).
  assert (Eps : map arg_ptr sargs = arg_ptr s0 :: map arg_ptr srest) by (rewrite Hhd; reflexivity).
  assert (Efl : flat_map arg_ps sargs = arg_ps s0 ++ flat_map arg_ps srest) by (rewrite Hhd; reflexivity).
  iEval (rewrite Eps argv_block_split) in "Hb". iDestruct "Hb" as "(Hal & Ha0 & Hy & Hx)".
  iEval (rewrite Efl pts_app) in "Hs". iDestruct "Hs" as "[Hs0 Hsr]".
  iAssert (string (arg_ptr s0) (arg_base s0) (arg_region s0) (arg_text s0)) with "[Hs0]" as "Hstr".
  { iSplit; [iPureIntro; exact Hok0 | iExact "Hs0"]. }
  iApply (main_start with "Hal Ha0 Hstr Hlit Hcells Hks Hcod Hs80"); [lia | exact Hav8 | lia | exact Har48 |].
  iNext. iIntros (e b4 b6 i k q new c' (Hv & Hc1 & Hf4 & Hf6 & Hi & Hk & Hq))
    "Hal Ha0 Hstr Hlit Hcells Hlent Hcod Hs80 Hl4 Hp4 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  iDestruct "Hstr" as "[_ Hs0]".
  iAssert (pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) (ptr_cap (arg_ptr s0) :: csr)))
    with "[Hal Ha0 Hy Hx]" as "Hb".
  { rewrite Eps argv_block_split. iFrame. }
  iAssert (pts (flat_map arg_ps sargs)) with "[Hs0 Hsr]" as "Hs".
  { rewrite Efl pts_app. iFrame. }
  iApply ("HK" $! e b4 b6 i k q new c' with
            "[%] [%] [Hb Hs Ht Hl4 Hp4] Hlit Hcells Hlent Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
  - auto 10.
  - split; [exact Hv|]. split; [exact Hc1|]. split; [exact Hf4|].
    split; [rewrite Eps; split; [reflexivity | apply Permutation_refl]|].
    split; [split; [exact Lc | exact Hc]|]. split; [exact Hix|]. left. reflexivity.
  - rewrite /loop_res. iFrame.
Qed.

Context (exit_spec : contract libc_world)
  (Hexit : registry (TAtom "exit") = Some exit_spec)
  (Hexit_abi : forall v, contract_abi exit_spec CVoid [Arg W v])
  (Hexit_pre : forall n m w h, 0 <= n < 2 ^ 32 -> wi m w h -> contract_pre exit_spec [WInt n] m w)
  (Hexit_post : forall args n s m w tr vs s' m' w',
    M.E.invoke exit_spec CVoid args [WInt n] s m w tr (CallReturn vs) s' m' w' -> False).

(** Exit accepts every canonical status and cannot return to its caller. *)
Lemma wp_main_exit f e ls lab v rest j n Φ :
  arg_x ge e (Arg W v) = Some (WInt n) -> 0 <= n < 2 ^ 32 ->
  ⊢ WP (ERun (mkFrame f e ls None (Exec lab
    (Call CVoid (Global (TAtom "exit")) [Arg W v] :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hv Hn.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ exit_spec [WInt n] True%I with "[] []").
  - apply linked_outside; [exact Hlinked|reflexivity].
  - apply linked_unbound; [exact Hlinked|reflexivity].
  - reflexivity.
  - exact Hexit.
  - cbn [map_option]. rewrite Hv. reflexivity.
  - apply Hexit_abi.
  - iIntros (σ) "Hσ _". iDestruct "Hσ" as (h) "[_ %Hσ]". iPureIntro.
    exact (Hexit_pre _ _ _ _ Hn (proj2 (proj2 (proj2 Hσ)))).
  - done.
  - iNext. iIntros (σ tr vs s' m' w' Hi) "_ _". exfalso. exact (Hexit_post _ _ _ _ _ _ _ _ _ _ Hi).
Qed.

End main.
End HelloMainGetopt.

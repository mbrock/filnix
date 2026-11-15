(** GNU Hello's option loop tracks pointer layouts and option codes without
    depending on the runtime. These definitions remain outside the runtime
    functor so that applying it does not substitute through their bodies. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia Permutation.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics StepRules ExternalCalls LibcCalls Pieces
  Libc Heap MemLogic StringLogic GetoptLogic HelloLeaf HelloVersion HelloModule HelloConvDefs Getopt HelloMainBase.
Open Scope Z_scope.
Open Scope list_scope.
Import HelloMainBase.MainDefinitions.

Module MainFacts.

(** Initialization continues at setlocale after allocating its local cells. *)
Definition start_rest : list inst := Eval vm_compute in drop 7 (b_insts (main_block "start")).

(** Initialization binds the argument count, argument vector, local cells,
    and empty string before calling setlocale. *)
Definition start_vars (e : env) (argc : Z) (av b4 b6 : Z) : Prop :=
  lookup (TAtom "v0") e = Some (WInt argc) /\ lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) /\
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
  lookup (TAtom "v6") e = Some (WPtr (mkPtr b6 (Obj b6))) /\
  lookup (TAtom "v11") e = Some (WPtr empty_ptr).

(** A local heap cell has a positive, aligned address within the address space. *)
Definition fresh_ok (b : Z) : Prop := 0 < b /\ b mod 16 = 0 /\ b + 16 <= 2 ^ 48.

(** Reordering the argument vector preserves its length. *)
Lemma order_length sargs ps : getopt_order (map arg_ptr sargs) ps -> length ps = length sargs.
Proof.
  intros H. rewrite <- (length_map arg_ptr sargs).
  symmetry. apply Permutation_length. exact (getopt_order_inventory _ _ H).
Qed.

(** The greeting is a literal or a nonnull borrowed command-line argument. *)
Definition greeting_ok (av : Z) (sargs : list argument) (g : ptr) : Prop :=
  g = greeting_ptr \/ g = traditional_ptr \/ (getopt_borrow (hello_input av sargs) g /\ ptr_addr g <> 0).

(** Each loop iteration preserves the local cells and argument layout. *)
Definition loop_facts (av : Z) (sargs : list argument)
    (e : env) (b4 b6 : Z) (ps : list ptr) (cs : list cap) (i : Z) (g : ptr) : Prop :=
  start_vars e (Z.of_nat (length sargs)) av b4 b6 /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\ fresh_ok b4 /\
  getopt_order (map arg_ptr sargs) ps /\ argv_caps cs ps /\ 0 <= i <= Z.of_nat (length sargs) /\
  greeting_ok av sargs g.

(** The incoming edge determines whether an earlier option was invalid. *)
Definition loop_entry (from : String.string) (e : env) (lose : Z) : Prop :=
  (from = "start"%string /\ lose = 0) \/ (from = "iw_1.L52"%string /\ lose = 1) \/
  ((from = "iw_1.L35"%string \/ from = "iw_1.L42"%string) /\
   lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)).

(** A successful getopt call records its input token and resulting transition. *)
Definition getopt_step (wi : mem -> libc_world -> gmap piece pval -> Prop)
    (transition : list word -> mem -> libc_world -> list Z -> list event -> list word -> mem -> libc_world -> Prop)
    (a : ptr) (i : Z) (values : list word) : Prop :=
  exists xs m w h born trace m' w',
    wi m w h /\ (forall l v, (l, v) ∈ getopt_ps a i -> h !! l = Some v) /\
    transition xs m w born trace values m' w'.

(** The linked program places each version literal at its recorded address. *)
Lemma main_version_lookup ge (Hlinked : hello_linked ge) s :
  In s ["hello#str.70"; "hello#str.63"; "hello#str.71"; "hello#str.72";
        "hello#str.73"; "hello#str.74"; "hello#str.75"] ->
  lookup (TAtom s) (ge_globals ge) = Some (version_literal s).
Proof.
  intros Hin. apply (proj1 (proj2 Hlinked)).
  repeat destruct Hin as [<- | Hin]; try contradiction; vm_compute; reflexivity.
Qed.

Section arguments.
Context (wi : mem -> libc_world -> gmap piece pval -> Prop).
Context (av : Z) (ar : region) (sargs : list argument)
  (Hav : 0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length sargs) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48)
  (Hargc : 1 <= Z.of_nat (length sargs) < 2 ^ 31)
  (Hargs : Forall (fun s => string_ok (arg_ptr s) (arg_base s) (arg_region s) (arg_text s)) sargs).
Context (initialized : mem -> libc_world -> Prop) (optarg_cell optind_cell : ptr)
  (Hgetopt_wi : forall m w h, wi m w h ->
     getopt_state_at m (libc_getopt_view w) /\ getopt_optarg_cell (libc_getopt_view w) = optarg_cell /\
     getopt_optind_cell (libc_getopt_view w) = optind_cell /\ getopt_current (libc_getopt_view w) h)
  (Htable : forall m w h, wi m w h -> hello_table_at m)
  (Hgetopt_env : forall m w h xs cs, wi m w h -> agrees m h -> live_disjoint m ->
   (forall l v, (l, v) ∈ block_ps av ar 0 xs cs ++ flat_map arg_ps sargs -> h !! l = Some v) ->
   getopt_input_at m (hello_input av sargs) ->
   libc_getopt_rep initialized m w /\
   Forall (writable_span m) (getopt_roots (libc_getopt_view w)) /\
   Forall (fun s => readable_bytes m (span_ptr s) (span_size s)) (getopt_reads (libc_getopt_view w)) /\
   getopt_separated (hello_input av sargs) (libc_getopt_view w) /\
   getopt_disjoint (getopt_public_writes (hello_input av sargs) (libc_getopt_view w)) /\
   getopt_private_owned m (hello_input av sargs) (libc_getopt_view w)).

(** Ownership of the argument vector determines each pointer that libc reads. *)
Lemma argv_slots m h ps cs :
  agrees m h -> getopt_order (map arg_ptr sargs) ps -> argv_caps cs ps ->
  (forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ flat_map arg_ps sargs -> h !! l = Some v) ->
  getopt_slots m av ps.
Proof.
  intros Ha Ho [Lc Hc] Kb Ks.
  assert (Hlv : live_at m av ar).
  { apply (Ha (PLive av) (VLive ar)), Kb. apply elem_of_cons. left. reflexivity. }
  apply slots_of_at. intros k q Hk.
  assert (Hq : 0 <= ptr_addr q < 2 ^ 64 /\ ~ freed_in (m_regions m) (ptr_cap q)).
  { pose proof (list_elem_of_lookup_2 _ _ _ Hk) as Hq'.
    apply list_elem_of_In, in_app_or in Hq' as [Hq' | [<- | []]].
    - destruct (order_in _ _ _ Ho Hq') as (s & Hs & ->).
      pose proof (proj1 (List.Forall_forall _ _) Hargs s Hs) as (Hcap & Hb0 & Hbp & Hend & H48 & _).
      assert (Hlive : live_at m (arg_base s) (arg_region s)).
      { apply (Ha (PLive (arg_base s)) (VLive (arg_region s))), Ks. apply list_elem_of_In, in_flat_map.
        exists s. split; [exact Hs|]. unfold arg_ps, string_ps. left. reflexivity. }
      split; [lia|]. intros (b' & reg' & Hc' & E' & L'). destruct Hlive as [E1 L1].
      destruct Hcap as [Hc0|Hc0]; rewrite Hc0 in Hc'; destruct Hc' as [E0|E0]; try discriminate E0;
        injection E0 as <-; rewrite E1 in E'; injection E' as <-; congruence.
    - split; [cbn; lia|]. intros (b' & reg' & Hc' & _). destruct Hc' as [E0|E0]; discriminate E0. }
  destruct Hq as [Hr Hf]. split; [exact Hr|]. split.
  - intros i Hi.
    assert (Hin : (PByte av (0 + Z.of_nat (8 * k + Z.to_nat i)), VByte (byte_of (ptr_addr q) i)) ∈
                  block_ps av ar 0 (argv_bytes ps) cs).
    { apply elem_of_cons. right. apply elem_of_app. left.
      apply (list_elem_of_lookup_2 _ (8 * k + Z.to_nat i)%nat). apply byte_ps_lookup.
      unfold argv_bytes. rewrite (slots_bytes_lookup _ _ _ _ Hk); [|lia].
      rewrite Z2Nat.id; [reflexivity|lia]. }
    destruct (Ha _ _ (Kb _ _ Hin)) as [_ Hil]. destruct (Hil ar (proj1 Hlv) (proj2 Hlv)) as (_ & _ & Hx).
    rewrite <- Hx. f_equal. lia.
  - assert (Hin : (PAux av (0 + Z.of_nat (8 * k)), VAux (ptr_cap q)) ∈ block_ps av ar 0 (argv_bytes ps) cs).
    { apply elem_of_cons. right. apply elem_of_app. right.
      apply (list_elem_of_lookup_2 _ (8 * k)%nat). apply aux_ps_lookup. exact (Hc k q Hk). }
    destruct (Ha _ _ (Kb _ _ Hin)) as [_ Hslot].
    destruct (Hslot ar (proj1 Hlv) (proj2 Hlv)) as (_ & _ & Hh).
    replace (av + 8 * Z.of_nat k) with (av + (0 + Z.of_nat (8 * k))) by lia.
    exact (aux_holds_kept _ _ _ Hh Hf).
Qed.

(** The owned argument vector and parser token satisfy libc's input contract. *)
Lemma getopt_admitted m w h ps cs a i :
  wi m w h -> agrees m h -> live_disjoint m ->
  getopt_order (map arg_ptr sargs) ps -> argv_caps cs ps -> 0 <= i <= Z.of_nat (length sargs) ->
  (forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ flat_map arg_ps sargs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ getopt_ps a i -> h !! l = Some v) ->
  getopt_pre (hello_input av sargs) libc_getopt_view (libc_getopt_rep initialized)
    (getopt_words (hello_input av sargs)) m w.
Proof.
  intros Hw Ha Hd Ho Hc Hi Kb Ks Kt.
  assert (Hlv : live_at m av ar).
  { apply (Ha (PLive av) (VLive ar)), Kb. apply elem_of_cons. left. reflexivity. }
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48).
  assert (Hin : getopt_input_at m (hello_input av sargs)).
  { destruct (Htable m w h Hw) as (T1 & T2 & T3).
    unfold getopt_input_at, getopt_vector, getopt_strings, hello_input.
    cbn [getopt_argc getopt_argv getopt_arguments getopt_optstring getopt_short_options getopt_longopts
         getopt_options getopt_longindex].
    split; [lia|]. split; [rewrite length_map; reflexivity|].
    split.
    {
      split; [|split; [|split]].
      - unfold writable_span. cbn [span_size span_ptr ptr_addr ptr_cap]. split; [lia|].
        exists av, ar. split; [reflexivity|]. split; [exact (proj1 Hlv)|]. split; [exact (proj2 Hlv)|].
        apply (access_obj _ _ ar); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
      - cbn [ptr_addr ptr_cap]. apply (access_obj _ _ ar); [exact (proj1 Hlv) | lia | lia | exact Hav8].
      - cbn [ptr_addr ptr_cap]. apply (access_obj _ _ ar); [exact (proj1 Hlv) | lia | lia | exact Hav8].
      - exists ps. split; [rewrite map_map; exact Ho|]. exact (argv_slots m h ps cs Ha Ho Hc Kb Ks). }
    split.
    { apply List.Forall_forall. intros [q t] Hq.
      apply in_map_iff in Hq as (s & E & Hs). injection E as <- <-. cbn [fst snd].
      apply (string_c_string _ _ (arg_base s) (arg_region s)); [exact (proj1 (List.Forall_forall _ _) Hargs s Hs)|].
      apply all_agree_intro. intros l v Hl. apply Ha, Ks. apply list_elem_of_In, in_flat_map.
      exists s. split; [exact Hs | apply list_elem_of_In; exact Hl]. }
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [left; reflexivity|].
    vm_compute. reflexivity. }
  assert (Kall : forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs ++ flat_map arg_ps sargs ->
                   h !! l = Some v).
  { intros l v Hl. apply elem_of_app in Hl as [Hl|Hl]; [exact (Kb _ _ Hl) | exact (Ks _ _ Hl)]. }
  destruct (Hgetopt_env m w h _ _ Hw Ha Hd Kall Hin) as (Hrep & Hroots & Hreads & Hsep & Hdisj & Hpriv).
  destruct (Hgetopt_wi m w h Hw) as (Hst & _ & _ & Hcur).
  destruct (Hcur a i (Kt _ _ ltac:(left))) as [_ Hi'].
  split; [reflexivity|]. split; [exact Hin|]. split; [exact Hrep|]. split; [exact Hst|].
  split; [rewrite Hi'; unfold hello_input; cbn [getopt_argc]; lia|].
  split; [exact Hroots|]. split; [exact Hreads|]. split; [exact Hsep|]. split; [exact Hdisj | exact Hpriv].
Qed.
End arguments.

End MainFacts.

(** Hello's safety theorem assumes a starting state: the loaded image,
    the argument, environment and auxiliary arrays that the runtime
    builds, a runtime ready to allocate, and a world whose standard
    streams are open. A theorem with an impossible premise says nothing,
    so this module builds one such state and checks every premise of
    that kind on it. The state runs Hello as `c: hello` with an empty
    environment and an empty auxiliary vector, on the interpreter's own
    runtime, whose allocation cursor starts at 2^32.

    The loader puts the whole image below 2^20. Below that address the
    witness memory reads the image's own bytes, except in the
    constructor table, where startup saves its arguments. The four
    objects that the runtime allocates lie between 2^20 and 2^32, and
    every byte from 2^32 up is zero. So the proof never has to evaluate
    the image's bytes. *)

From Stdlib Require Import String ZArith List Lia Bool Sorting.Sorted Sorting.Permutation.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Runtime Pieces.
From Glibc Require Import OsWorld OsStart OsCpuid StartCtors StartState LocaleEnv
  HelloImageModule HelloImageLoad HelloImageEarly.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(** ## Disjoint chains of regions

    The loader lists the image's regions from the highest address down,
    each one ending at or below the start of the one before it. Such a
    chain has no two overlapping objects, and the check below decides
    whether a list is one. *)

(** A list of regions is a descending chain when each region is
    nonempty and ends at or below the start of the region before it. *)
Fixpoint desc_chain (rs : list region) : bool :=
  match rs with
  | r1 :: ((r2 :: _) as t) => (r_end r2 <=? r_base r1) && (r_base r2 <? r_end r2) && desc_chain t
  | _ => true
  end.

(** The region that a lookup finds is in the list and has that base. *)
Lemma object_region_in b rs reg : object_region b rs = Some reg -> In reg rs /\ r_base reg = b.
Proof.
  induction rs as [|r rs IH]; cbn; [discriminate|].
  destruct (Z.eqb_spec (r_base r) b) as [E|_].
  - intros [= <-]. auto.
  - intros H. destruct (IH H). auto.
Qed.

(** Every region after the head of a descending chain ends at or below
    the head's start. *)
Lemma desc_chain_below r t x : desc_chain (r :: t) = true -> In x t -> r_end x <= r_base r.
Proof.
  revert r. induction t as [|r2 t IH]; intros r H Hx; [destruct Hx|].
  cbn [desc_chain] in H. apply andb_prop in H as [H Ht]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct Hx as [<- | Hx]; [exact H1|].
  pose proof (IH r2 Ht Hx). lia.
Qed.

(** The tail of a descending chain is one too. *)
Lemma desc_chain_tail r t : desc_chain (r :: t) = true -> desc_chain t = true.
Proof. destruct t; cbn; [reflexivity|]. intros H. apply andb_prop in H as [_ H]. exact H. Qed.

(** Two regions of a descending chain with different bases do not
    overlap. *)
Lemma desc_chain_disjoint rs r1 r2 : desc_chain rs = true -> In r1 rs -> In r2 rs -> r_base r1 <> r_base r2 ->
  r_end r1 <= r_base r2 \/ r_end r2 <= r_base r1.
Proof.
  induction rs as [|r rs IH]; intros H H1 H2 Hb; [destruct H1|].
  destruct H1 as [<- | H1], H2 as [<- | H2].
  - congruence.
  - right. exact (desc_chain_below _ _ _ H H2).
  - left. exact (desc_chain_below _ _ _ H H1).
  - exact (IH (desc_chain_tail _ _ H) H1 H2 Hb).
Qed.

(** A memory whose region list is a descending chain has disjoint live
    objects. *)
Lemma desc_chain_live_disjoint m : desc_chain (m_regions m) = true -> live_disjoint m.
Proof.
  intros H b1 r1 b2 r2 [E1 _] [E2 _] Hb.
  destruct (object_region_in _ _ _ E1) as [I1 <-], (object_region_in _ _ _ E2) as [I2 <-].
  exact (desc_chain_disjoint _ _ _ H I1 I2 Hb).
Qed.

(** ## The witness state *)

(** The runtime places its four objects at these addresses: the string
    "hello", the argument array, the environment array and the
    auxiliary vector. *)
Definition w_str : Z := 2 ^ 20.
Definition w_argv : Z := 2 ^ 20 + 64.
Definition w_env : Z := 2 ^ 20 + 128.
Definition w_av : Z := 2 ^ 20 + 192.

(** The program's only argument is its name. *)
Definition w_name : list Z := [104; 101; 108; 108; 111].

(** Each of the four objects is one live 16-byte heap granule. *)
Definition w_heap (b : Z) : region := mkRegion b (b + 16) Heap Live.

(** The runtime's objects come first, highest address first, ahead of
    the image's regions. *)
Definition w_regions : list region := map w_heap [w_av; w_env; w_argv; w_str] ++ img_regions.

(** The constructor table sits at the table symbol, and it holds the
    image's constructors in the order the module lists them. *)
Definition w_tb : Z := img_addr "zrun_deferred_global_ctors#table".
Definition w_order : list name := ctor_names hello_image_module.

(** These are the 8-byte words that the start state writes: argc, argv
    and environ, then the constructor pointers, in the table, and the
    pointer to "hello" in the argument array. Each word gives its
    address, its value and the capability in its aux slot. *)
Definition w_words : list (Z * Z * cap) :=
  [(w_tb, 1, CNone); (w_tb + 8, w_argv, Obj w_argv); (w_tb + 16, w_env, Obj w_env)] ++
  map (fun '(i, f) => match lookup f img_globals with
                      | Some p => (w_tb + 24 + 8 * Z.of_nat i, ptr_addr p, ptr_cap p)
                      | None => (0, 0, CNone)
                      end) (combine (seq 0 (length w_order)) w_order) ++
  [(w_argv, w_str, Obj w_str)].

(** This function finds the written word that covers address a. *)
Definition w_word (a : Z) : option (Z * Z * cap) :=
  find (fun '(s, _, _) => (s <=? a) && (a <? s + 8)) w_words.

(** The runtime copies the bytes of "hello" into its string object. *)
Definition w_str_byte (a : Z) : Z :=
  if (w_str <=? a) && (a <? w_str + 5) then nth (Z.to_nat (a - w_str)) w_name 0 else 0.

(** The witness memory starts from the image's initial memory m0 and
    adds the written words, the string and zeros above 2^20. *)
Definition w_mem (m0 : mem) : mem :=
  mkMem
    (fun a => match w_word a with
              | Some (s, v, _) => byte_of v (a - s)
              | None => if a <? 2 ^ 20 then m_bytes m0 a else w_str_byte a
              end)
    w_regions
    (fun a => match find (fun '(s, _, _) => s =? a) w_words with
              | Some (_, _, c) => c
              | None => if a <? 2 ^ 20 then m_aux m0 a else CNone
              end).

(** The world's errno cell is the image's `c: errno` variable. *)
Definition w_errno : ptr :=
  match lookup (TAtom "__libc_errno") img_globals with Some p => p | None => mkPtr 0 CNone end.

(** The machine has stdin, stdout and stderr open, no log file, and
    CPUID leaf 4 ends its list of caches. *)
Definition w_world : os_world :=
  mkOsWorld None (mkPtr 0 CNone) None [0; 1; 2] (facts_of ["leaf4_ends"%string])
    w_errno false.

(** ## Facts about the witness memory *)

(** Every image region is nonempty and lies below 2^20. *)
Lemma img_regions_low : forallb (fun r => (r_base r <? r_end r) && (r_end r <=? 2 ^ 20)) img_regions = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_region_low reg : In reg img_regions -> r_base reg < r_end reg <= 2 ^ 20.
Proof.
  intros H. pose proof (proj1 (forallb_forall _ _) img_regions_low reg H) as E.
  apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.leb_le in E2. lia.
Qed.

(** This lemma computes the list of written words once. *)
Lemma w_words_eq : w_words =
  [(218448, 1, CNone); (218456, 1048640, Obj 1048640); (218464, 1048704, Obj 1048704);
   (218472, 91808, Fn (TAtom "glibc_stdfiles#_IO_stdfiles_init"));
   (218480, 93872, Fn (TAtom "glibc_vtables#check_stdfiles_vtables"));
   (218488, 218320, Fn (TAtom "glibc_init_first#_init_first"));
   (1048640, 1048576, Obj 1048576)].
Proof. vm_compute. reflexivity. Qed.

Lemma w_tb_eq : w_tb = 218448.
Proof. vm_compute. reflexivity. Qed.

(** An address outside a word's eight bytes does not hit it. *)
Lemma in8_false s a : ~ (s <= a < s + 8) -> (s <=? a) && (a <? s + 8) = false.
Proof. intros H. destruct (Z.leb_spec s a), (Z.ltb_spec a (s + 8)); cbn; [lia | reflexivity..]. Qed.

(** No word is written outside the table and the argument array. *)
Lemma w_word_none a : ~ (w_tb <= a < w_tb + 48) -> ~ (w_argv <= a < w_argv + 8) -> w_word a = None.
Proof.
  rewrite w_tb_eq. unfold w_word, w_argv. rewrite w_words_eq. intros H1 H2. cbn [find].
  repeat rewrite in8_false by lia. reflexivity.
Qed.

Lemma w_aux_none a : ~ (w_tb <= a < w_tb + 48) -> ~ (w_argv <= a < w_argv + 8) ->
  find (fun '(s, _, _) => s =? a) w_words = None.
Proof.
  rewrite w_tb_eq. unfold w_argv. rewrite w_words_eq. intros H1 H2. cbn [find].
  repeat rewrite (proj2 (Z.eqb_neq _ a)) by lia. reflexivity.
Qed.

(** A lookup in a joined list of regions searches the front part
    first. *)
Lemma object_region_app b hs rs :
  object_region b (hs ++ rs) = match object_region b hs with Some r => Some r | None => object_region b rs end.
Proof. induction hs as [|h hs IH]; cbn; [reflexivity|]. destruct (r_base h =? b); [reflexivity | exact IH]. Qed.

Section mem.
Variable m0 : mem.

(** The memory holds zeros and no capabilities at every address past
    the five letters of "hello", except in the argument array's first
    word. *)
Lemma w_free_byte a : w_str + 5 <= a -> ~ (w_argv <= a < w_argv + 8) ->
  m_bytes (w_mem m0) a = 0 /\ m_aux (w_mem m0) a = CNone.
Proof.
  intros H1 H2. pose proof w_tb_eq. unfold w_str in H1.
  cbn [m_bytes m_aux w_mem]. rewrite w_word_none, w_aux_none by lia.
  rewrite (proj2 (Z.ltb_ge a _)) by lia. unfold w_str_byte, w_str.
  rewrite (proj2 (Z.ltb_ge a _)) by lia. rewrite andb_false_r. split; reflexivity.
Qed.

Lemma byte_of_0 i : byte_of 0 i = 0.
Proof. unfold byte_of. rewrite Zdiv_0_l. reflexivity. Qed.

(** A free slot holds the null pointer and the integer 0. *)
Lemma w_null_slot a : w_str + 5 <= a -> ~ (w_argv - 8 < a < w_argv + 8) -> ptr_slot (w_mem m0) a (mkPtr 0 CNone).
Proof.
  intros H1 H2. split; [cbn; lia|]. split.
  - intros i Hi. rewrite (proj1 (w_free_byte (a + i) ltac:(lia) ltac:(lia))). symmetry. apply byte_of_0.
  - exact (proj2 (w_free_byte a H1 ltac:(lia))).
Qed.

Lemma w_zero_slot a : w_str + 5 <= a -> ~ (w_argv - 8 < a < w_argv + 8) -> int_slot (w_mem m0) a 0.
Proof. intros H1 H2. destruct (w_null_slot a H1 H2) as (_ & Hb & Ha). split; [lia|]. split; [exact Hb | exact Ha]. Qed.

Ltac slot_bytes :=
  intros i Hi; assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia;
  repeat destruct Hc as [-> | Hc]; try subst i; vm_compute; reflexivity.

(** Each of the runtime's four objects is a live heap granule. *)
Lemma w_heap_object b n : In b [w_av; w_env; w_argv; w_str] -> 0 <= n <= 16 -> heap_object (w_mem m0) b n.
Proof.
  intros Hb Hn. assert ((n + 15) / 16 < 2) by (apply Z.div_lt_upper_bound; lia).
  assert (0 <= (n + 15) / 16) by (apply Z.div_pos; lia).
  exists (w_heap b). split; [split; [|reflexivity]|].
  - destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity.
  - unfold w_heap; cbn [r_kind r_end]. split; [reflexivity|].
    destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; unfold w_av, w_env, w_argv, w_str; repeat split; try lia;
      vm_compute; reflexivity.
Qed.

(** The string object holds "hello" and zeros after it. *)
Lemma w_c_string : c_string (w_mem m0) w_str w_name.
Proof.
  split; [apply w_heap_object; [cbn; tauto | cbn; lia]|]. split.
  - intros i Hi. cbn in Hi. destruct i as [|[|[|[|[|i]]]]]; try lia;
      (eexists; split; [reflexivity | split; [lia | vm_compute; reflexivity]]).
  - split; [vm_compute; reflexivity|]. intros i Hi. change (5 < i < 16) in Hi.
    refine (proj1 (w_free_byte (w_str + i) _ _)); unfold w_argv, w_str; lia.
Qed.

(** The argument array holds a pointer to "hello", then null. *)
Lemma w_argv_array : string_array (w_mem m0) w_argv [(w_str, w_name)].
Proof.
  split; [apply w_heap_object; [cbn; tauto | cbn; lia]|]. split.
  - intros [|[|i]] sb s E; cbn in E; try discriminate. injection E as <- <-. split; [|exact w_c_string].
    split; [unfold w_str; cbn; lia|]. split; [slot_bytes | vm_compute; reflexivity].
  - apply w_null_slot; unfold w_argv, w_str; cbn; lia.
Qed.

(** The environment array holds only its null terminator. *)
Lemma w_env_array : string_array (w_mem m0) w_env [].
Proof.
  split; [apply w_heap_object; [cbn; tauto | cbn; lia]|]. split.
  - intros [|i] sb s E; discriminate.
  - apply w_null_slot; unfold w_env, w_argv, w_str; cbn; lia.
Qed.

(** The auxiliary vector holds only its zero key. *)
Lemma w_auxv : auxv_array (w_mem m0) w_av [].
Proof.
  split; [apply w_heap_object; [cbn; tauto | cbn; lia]|].
  split; [constructor|]. split; [constructor|]. split; [intros [|i] k v E; discriminate|].
  apply w_zero_slot; unfold w_av, w_argv, w_str; cbn; lia.
Qed.

(** The constructor table holds argc, argv, environ and the
    constructors in [w_order]. *)
Lemma w_ctor_table : ctor_table (w_mem m0) img_globals w_tb 1 (mkPtr w_argv (Obj w_argv)) (mkPtr w_env (Obj w_env)) w_order.
Proof.
  split; [split; [lia|]; split; [slot_bytes | vm_compute; reflexivity]|].
  split; [split; [unfold w_argv; cbn; lia|]; split; [slot_bytes | vm_compute; reflexivity]|].
  split; [split; [unfold w_env; cbn; lia|]; split; [slot_bytes | vm_compute; reflexivity]|].
  intros i f E. assert (Eo : w_order = [TAtom "glibc_stdfiles#_IO_stdfiles_init";
    TAtom "glibc_vtables#check_stdfiles_vtables"; TAtom "glibc_init_first#_init_first"]) by (vm_compute; reflexivity).
  rewrite Eo in E. destruct i as [|[|[|i]]]; cbn in E; [..| destruct i; discriminate];
    injection E as <-; (eexists; split; [vm_compute; reflexivity|]);
    (split; [cbn; lia|]); (split; [slot_bytes | vm_compute; reflexivity]).
Qed.

(** The interpreter's runtime is ready to allocate from 2^32 on. *)
Lemma w_regions_ok : forallb (fun r => (0 <? r_base r) && (r_base r <? r_end r) && (r_end r <=? 2 ^ 32) &&
  match r_life r with Live => true | Freed => false end) w_regions = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w_ready : InterpRuntime.ready InterpRuntime.start (w_mem m0).
Proof.
  unfold InterpRuntime.ready, InterpRuntime.start, InterpRuntime.address_end. split; [lia|]. split.
  - intros b reg E. cbn [m_regions w_mem] in E. destruct (object_region_in _ _ _ E) as [I <-].
    pose proof (proj1 (forallb_forall _ _) w_regions_ok reg I) as F.
    apply andb_prop in F as [F L]. apply andb_prop in F as [F F3]. apply andb_prop in F as [F1 F2].
    apply Z.ltb_lt in F1, F2. apply Z.leb_le in F3. split; [lia|]. split; [lia|].
    destruct (r_life reg); [discriminate | discriminate L].
  - intros a Ha. apply w_free_byte; unfold w_str, w_argv; lia.
Qed.

(** The witness memory keeps the image, except for the table. *)
Lemma w_keeps : m_regions m0 = img_regions -> keeps_image m0 (w_mem m0) w_tb (ctor_table_size (length w_order)).
Proof.
  intros Hreg. assert (Ets : ctor_table_size (length w_order) = 48) by (vm_compute; reflexivity). rewrite Ets.
  split; [|split].
  - intros b reg E. rewrite Hreg in E. destruct (object_region_in _ _ _ E) as [I <-].
    pose proof (img_region_low _ I). cbn [m_regions w_mem]. unfold w_regions. rewrite object_region_app.
    cbn [map object_region w_heap r_base]. unfold w_av, w_env, w_argv, w_str.
    repeat rewrite (proj2 (Z.eqb_neq _ _)) by lia. exact E.
  - intros b reg E N. rewrite Hreg in N. cbn [m_regions w_mem] in E. unfold w_regions in E.
    rewrite object_region_app, N in E. destruct (object_region b _) eqn:H; [|discriminate].
    injection E as <-. destruct (object_region_in _ _ _ H) as [I _].
    apply in_map_iff in I as (x & <- & _). reflexivity.
  - intros a (reg & I & Ha) Ht. rewrite Hreg in I. pose proof (img_region_low _ I).
    cbn [m_bytes m_aux w_mem]. rewrite w_word_none, w_aux_none by (unfold w_argv; lia).
    rewrite (proj2 (Z.ltb_lt a _)) by lia. split; reflexivity.
Qed.

End mem.

(** ## The witness *)

(** Some start state meets all of Hello's premises about the machine at
    once. It is a valid start state, and the interpreter's runtime is
    ready in it. Its stdout and stderr are open, its environment
    selects the C locale, and its CPU ends the list of caches. *)
Theorem hello_start_witness :
  exists w0 m s w xs,
    start_state hello_image_module w0 m w xs /\ InterpRuntime.ready s m /\
    In 1 (ow_fds w0) /\ In 2 (ow_fds w0) /\ start_c_locale m xs /\ ow_leaf4_ends w0 = true.
Proof.
  destruct hello_image_memory as (g & m0 & Hi). destruct (hello_loaded_tables g m0 Hi) as [-> Hreg].
  set (xs := [WPtr (mkPtr 68656 (Fn (TAtom "main"))); WInt 1; WPtr (mkPtr w_argv (Obj w_argv));
              WPtr (mkPtr w_env (Obj w_env)); WPtr (mkPtr w_av (Obj w_av))]).
  exists w_world, (w_mem m0), InterpRuntime.start, (start_world w_world (mkPtr 0 CNone) false false), xs.
  split; [|split; [apply w_ready|split; [cbn; tauto|split; [cbn; tauto|split; [|vm_compute; reflexivity]]]]].
  - exists img_globals, m0, (mkPtr 68656 (Fn (TAtom "main"))), w_tb, 1, (w_argv, [(w_str, w_name)]),
      (w_env, []), w_av, [], w_order.
    split; [exact Hi|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split; [exact (w_argv_array m0)|]. split; [exact (w_env_array m0)|]. split; [exact (w_auxv m0)|].
    split; [apply desc_chain_live_disjoint; vm_compute; reflexivity|].
    split; [exact (w_keeps m0 Hreg)|]. split; [apply Permutation_refl|].
    split; [exact (w_ctor_table m0)|].
    split; [split; [vm_compute; reflexivity | split; [repeat constructor; discriminate | reflexivity]]|].
    cbn. repeat constructor; cbn; intros H; repeat destruct H as [H | H]; try contradiction;
      unfold w_argv, w_env, w_av, w_str in H; lia.
  - intros b ss Hn Hs. cbn in Hn. injection Hn as Eb. subst b.
    destruct ss as [|[sb s] ss]; [exact c_locale_env_nil|].
    destruct Hs as (_ & Hs & _). destruct (Hs 0%nat sb s eq_refl) as [(_ & _ & Ha) _].
    vm_compute in Ha. discriminate.
Qed.

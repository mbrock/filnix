(** One fixed-launch Hello world. The layout below is a model witness,
    not a fabricated exported name for libc's private getopt_data.
    Identifying it with the selected native image, including errno TLS,
    remains the trusted libc/startup binding. No runtime axiom supplies it. *)
From Stdlib Require Import String ZArith List Bool Lia.
From stdpp Require Import list.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  ExternalCalls ExternalMachine Startup Locale Stdio Shutdown Getopt Libc LibcStreams
  Pieces Heap ContractFrame StringLogic MemLogic LentLogic LocaleLogic GetoptLogic
  HelloModule HelloLeaf HelloName HelloReach HelloMain HelloStdio.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Module HelloWorld.
Module Reach := HelloReach InterpRuntime.

(** Shared getopt storage is not thread-local. Only the selected errno
    cell is the current thread's TLS binding. All native identities are
    disjoint from Hello's own image and the copied launch arguments. *)
Definition parser : ptr := mkPtr 131072 (Obj 131072).
(** Public optarg cell. *)
Definition optarg_cell : ptr := mkPtr 131136 (Obj 131136).
(** Public optind cell. *)
Definition optind_cell : ptr := mkPtr 131152 (Obj 131152).
(** Public opterr cell. *)
Definition opterr_cell : ptr := mkPtr 131168 (Obj 131168).
(** Public optopt cell. *)
Definition optopt_cell : ptr := mkPtr 131184 (Obj 131184).
(** The selected thread's errno cell. *)
Definition errno_pointer : ptr := mkPtr 131200 (Obj 131200).
(** Public stdout pointer cell. *)
Definition out_cell : ptr := mkPtr 131216 (Obj 131216).
(** Public stderr pointer cell. *)
Definition err_cell : ptr := mkPtr 131232 (Obj 131232).
(** Public full invocation-name cell, handed to main. *)
Definition full_name_cell : ptr := mkPtr 131248 (Obj 131248).
(** Public short invocation-name cell, handed to main. *)
Definition short_name_cell : ptr := mkPtr 131264 (Obj 131264).
(** The synthetic stdout FILE object. *)
Definition out_handle : ptr := mkPtr 131328 (Obj 131328).
(** The synthetic stderr FILE object. *)
Definition err_handle : ptr := mkPtr 131584 (Obj 131584).
(** Borrowed initial C-locale name. *)
Definition locale_pointer : ptr := mkPtr 131840 (Ro 131840).
(** The launch's empty environment vector. *)
Definition environment_pointer : ptr := mkPtr 131856 (Obj 131856).

(** Only the actual public data imports extend Hello's symbol map. *)
Definition globals : list (name * ptr) :=
  [(TAtom "stdout", out_cell); (TAtom "stderr", err_cell);
   (TAtom "program_invocation_name", full_name_cell);
   (TAtom "program_invocation_short_name", short_name_cell);
   (TAtom "optarg", optarg_cell); (TAtom "optind", optind_cell)].
(** Hello's own symbols together with its public libc data imports. *)
Definition ge : genv := Reach.hello_genv globals.

(** The two launch strings and their copied writable vector. *)
Definition arguments : list argument :=
  [mkArgument (mkPtr 196640 (Obj 196640)) 196640
     (mkRegion 196640 196656 Heap Live) [104; 101; 108; 108; 111];
   mkArgument (mkPtr 196672 (Obj 196672)) 196672
     (mkRegion 196672 196688 Heap Live) [45; 45; 118; 101; 114; 115; 105; 111; 110]].
(** The copied argv vector's object identity. *)
Definition argv_base : Z := 196608.
(** The actual getopt arguments for this fixed launch. *)
Definition input : getopt_input := hello_input argv_base arguments.

(** Exact private inventory, not merely membership of the parser root.
    Argv is deliberately absent: it is the program-owned output. *)
Definition parser_roots : list span := [mkSpan parser 56].
(** Environment storage the parser may inspect on initialization. *)
Definition parser_reads : list span := [mkSpan environment_pointer 8].
(** Fixed identities and exact private parser inventory. *)
Definition parser_layout (g : getopt_world) : Prop :=
  getopt_optarg_cell g = optarg_cell /\ getopt_optind_cell g = optind_cell /\
  getopt_opterr_cell g = opterr_cell /\ getopt_optopt_cell g = optopt_cell /\
  getopt_errno_cell g = errno_pointer /\
  getopt_roots g = parser_roots /\ getopt_reads g = parser_reads /\ getopt_owned g = [].

(** A completed exact-option scan. The private continuation is decoded
    from memory, not named by an independent ghost phase. Bounds permit
    both the selected return and a subsequent end-of-options control. *)
Definition parser_finished (m : mem) (g : getopt_world) : Prop :=
  getopt_parser_storage parser m g /\ getopt_optind g = 2 /\
  ptr_addr (getopt_optarg g) = 0 /\
  load_bytes m (ptr_addr parser + 24) 4 = 1 /\
  pointer_slot m (ptr_addr parser + 32) null /\
  0 <= load_bytes m (ptr_addr parser + 40) 4 <= 2 /\
  exists bound, 1 <= bound <= 2 /\
    load_bytes m (ptr_addr parser + 44) 4 = bound /\
    load_bytes m (ptr_addr parser + 48) 4 = bound.

(** Ordinary coherent cutpoints for this launch only. Running resource
    prefixes do not inherit this disjunction. Errno is sampled through
    getopt_state_at; it is not frozen across locale or output calls. *)
Definition parser_completed (m : mem) (w : libc_world) : Prop :=
  parser_layout (libc_getopt_view w) /\ getopt_state_at m (libc_getopt_view w) /\
  (getopt_parser_fresh parser m (libc_getopt_view w) \/
   parser_finished m (libc_getopt_view w)).

(** Positive argument/input facts are essential here: getopt_step
    existentially quantifies a transition without requiring an invoke.
    A false argument guard must never admit a spurious return code. *)
Definition selected_transition xs m w (_ : list Z) (trace : list event) values m' w' : Prop :=
  xs = getopt_words input /\ getopt_input_at m input /\
  (getopt_parser_fresh parser m (libc_getopt_view w) ->
    values = [WInt 129] /\ ptr_addr (getopt_optarg (libc_getopt_view w')) = 0 /\
    parser_finished m' (libc_getopt_view w')) /\
  trace = [] /\
  libc_stderr_file (libc_streams (fst w')) = libc_stderr_file (libc_streams (fst w)) /\
  libc_stderr_open (libc_streams (fst w')) = libc_stderr_open (libc_streams (fst w)) /\
  libc_stderr_state (libc_streams (fst w')) = libc_stderr_state (libc_streams (fst w)).

(** The physical native component has no ghost heap, returned code or
    call-restoration law. FILE/native realization is still the libc
    trust boundary; these are the concrete model's coherent views. *)
Definition native_at (m : mem) (w : libc_world) : Prop :=
  libc_stream_ready (fun _ _ => True) m w /\
  parser_completed m w /\ libc_errno (fst w) = errno_pointer /\
  libc_stdout w = out_handle /\ libc_stderr w = err_handle /\
  exposed_pointer_cell m out_cell out_handle /\
  exposed_pointer_cell m err_cell err_handle /\
  string_vector m environment_pointer [] /\ hello_table_at m.

(** Private identities exclude caller memory pieces, including life
    pieces. This main-stage interpretation owns neither FILE lives nor
    errno bytes. Callback acquisition is a distinct later operation. *)
Definition private_sources (w : libc_world) : list span :=
  locale_private_sources (libc_locale (fst w)) ++
  file_sources (libc_stdout_file (libc_streams (fst w))) ++
  file_sources (libc_stderr_file (libc_streams (fst w))) ++
  parser_roots ++ parser_reads ++ getopt_cells (libc_getopt_view w) ++
  [mkSpan out_cell 8; mkSpan err_cell 8;
   mkSpan optstring_ptr 4; mkSpan longopts_ptr 160] ++
  map (fun o => mkSpan (option_name o) (Z.of_nat (length (option_text o)) + 1)) hello_options.

(** One composite interpretation. Current ghost names observe the same
    payload as physical locale/parser/FILE readiness. Native pools must
    stay apart from the program, but getopt's public argv writes are
    intentionally not classified as private roots. *)
Definition wi (m : mem) (w : libc_world) (h : gmap piece pval) : Prop :=
  native_at m w /\
  Forall (fun source => cap_private h (ptr_cap (span_ptr source))) (private_sources w) /\
  ids_apart (locale_owned (libc_locale (fst w)) ++
    file_owned (libc_stdout_file (libc_streams (fst w))) ++
    file_owned (libc_stderr_file (libc_streams (fst w)))) h /\
  names_current (libc_locale (fst w)) h /\ codec_current (libc_locale (fst w)) h /\
  getopt_current (libc_getopt_view w) h.

(** The initial ghost token rules out the finished cutpoint by its
    public optind, exposing the actual decoded fresh private storage. *)
Lemma first_call_fresh : forall m w h,
  wi m w h ->
  (forall l v, (l, v) ∈ getopt_ps null 1 -> h !! l = Some v) ->
  getopt_parser_fresh parser m (libc_getopt_view w).
Proof.
  intros m w h (Hnative & _ & _ & _ & _ & Hcurrent) Htoken.
  destruct Hnative as (_ & (_ & _ & [Hfresh|Hfinished]) & _); [exact Hfresh|].
  assert (Hin : (PName getopt_key, VGetopt null 1) ∈ getopt_ps null 1)
    by constructor.
  destruct (Hcurrent null 1 (Htoken _ _ Hin)) as [_ Hi].
  destruct Hfinished as (_ & Hi' & _). congruence.
Qed.

(** This is the selection implication main_to_version consumes. It
    applies to every transition witness, not only to admitted invokes. *)
Lemma first_call_selected : forall xs m w h born trace values m' w',
  wi m w h ->
  (forall l v, (l, v) ∈ getopt_ps null 1 -> h !! l = Some v) ->
  selected_transition xs m w born trace values m' w' -> values = [WInt 129].
Proof.
  intros xs m w h born trace values m' w' Hw Htoken (_ & _ & Hselected & _).
  exact (proj1 (Hselected (first_call_fresh _ _ _ Hw Htoken))).
Qed.

(** One joint model image extends, rather than replaces, the actual
    linked initializer. Its private parser starts zero-initialized;
    public optopt starts at '?' independently of that private copy. *)
Definition native_regions : list region :=
  [mkRegion 131072 131128 GlobalData Live;
   mkRegion 131136 131144 GlobalData Live;
   mkRegion 131152 131156 GlobalData Live;
   mkRegion 131168 131172 GlobalData Live;
   mkRegion 131184 131188 GlobalData Live;
   mkRegion 131200 131204 GlobalData Live;
   mkRegion 131216 131224 GlobalData Live;
   mkRegion 131232 131240 GlobalData Live;
   mkRegion 131248 131256 GlobalData Live;
   mkRegion 131264 131272 GlobalData Live;
   mkRegion 131328 131584 GlobalData Live;
   mkRegion 131584 131840 GlobalData Live;
   mkRegion 131840 131842 GlobalData Live;
   mkRegion 131856 131864 GlobalData Live].
(** Program-owned launch regions, outside the linked image. *)
Definition launch_regions : list region :=
  mkRegion argv_base (argv_base + 24) Heap Live :: map arg_region arguments.
(** Keep the linked initializer below the native/launch allocation band. *)
Definition image_seed : mem :=
  mkMem (fun a => if a <? 131072 then m_bytes hello_literal_memory a else 0)
    (native_regions ++ m_regions hello_literal_memory ++ launch_regions)
    (fun a => if a <? 131072 then m_aux hello_literal_memory a else CNone).
(** Address, width and integer value for each nonzero startup store. *)
Definition image_words : list (Z * Z * Z) :=
  [(131152, 4, 1); (131168, 4, 1); (131184, 4, 63);
   (131216, 8, 131328); (131232, 8, 131584);
   (131248, 8, 196640); (131264, 8, 196640); (131840, 1, 67);
   (196608, 8, 196640); (196616, 8, 196672);
   (196640, 1, 104); (196641, 1, 101); (196642, 1, 108);
   (196643, 1, 108); (196644, 1, 111);
   (196672, 1, 45); (196673, 1, 45); (196674, 1, 118);
   (196675, 1, 101); (196676, 1, 114); (196677, 1, 115);
   (196678, 1, 105); (196679, 1, 111); (196680, 1, 110)].
(** Capabilities written by the six nonnull pointer stores. *)
Definition image_pointers : list (Z * cap) :=
  [(131216, Obj 131328); (131232, Obj 131584);
   (131248, Obj 196640); (131264, Obj 196640);
   (196608, Obj 196640); (196616, Obj 196672)].
(** The single physical entry image; scalar folds avoid expanding memory
    records underneath symbolic addresses during certificate checking. *)
Definition entry_memory : mem :=
  mkMem
    (fun a => fold_right (fun aw old =>
      if (fst (fst aw) <=? a) && (a <? fst (fst aw) + snd (fst aw))
      then byte_of (snd aw) (a - fst (fst aw)) else old)
      (m_bytes image_seed a) image_words)
    (m_regions image_seed)
    (fun a => fold_right (fun ac old => if a =? fst ac then snd ac else old)
      (m_aux image_seed a) image_pointers).

(** Initial C-locale observation and its private name storage. *)
Definition entry_locale : locale_world :=
  mkLocaleWorld 0 (fun _ => locale_pointer) (fun _ => [67]) (TAtom "C")
    [mkSpan locale_pointer 2] [] [].
(** Public initial values and the private parser's exact authorities. *)
Definition entry_parser : getopt_world :=
  mkGetoptWorld optarg_cell optind_cell opterr_cell optopt_cell errno_pointer
    null 1 1 63 0 parser_reads parser_roots [].
(** Structural stdout representation with no pending bytes. *)
Definition entry_out : libc_file := mkLibcFile out_handle 0 [] [mkSpan out_handle 256] [].
(** Structural stderr representation with no pending bytes. *)
Definition entry_err : libc_file := mkLibcFile err_handle 0 [] [mkSpan err_handle 256] [].
(** One shared payload, errno cell and authoritative shutdown inventory. *)
Definition entry_world : libc_world :=
  (mkLibcPayload entry_locale
    (mkStdioWorld true [mkSpan out_handle 256; mkSpan errno_pointer 4]) errno_pointer
    (mkLibcStreams entry_out entry_err true stdout_initial) entry_parser,
   mkShutdown Tls 0 [] [] stdout_initial).

Local Opaque hello_literal_memory.

Local Ltac image_bounds :=
  repeat match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); cbn; try lia
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); subst; cbn; try lia
  end.

(** Outside startup writes, the seed's byte is preserved. *)
Lemma entry_bytes_unwritten : forall a,
  Forall (fun aw => a < fst (fst aw) \/ fst (fst aw) + snd (fst aw) <= a) image_words ->
  m_bytes entry_memory a = if a <? 131072 then m_bytes hello_literal_memory a else 0.
Proof.
  intros a Houtside.
  change (fold_right (fun aw old =>
    if (fst (fst aw) <=? a) && (a <? fst (fst aw) + snd (fst aw))
    then byte_of (snd aw) (a - fst (fst aw)) else old)
    (m_bytes image_seed a) image_words = m_bytes image_seed a).
  generalize dependent image_words.
  intros ws. induction ws as [|[[p n] x] ws IH]; intros Houtside; [reflexivity|].
  inversion Houtside as [|? ? Hspan Htail]; subst.
  change ((if (p <=? a) && (a <? p + n) then byte_of x (a - p)
    else fold_right (fun aw old =>
      if (fst (fst aw) <=? a) && (a <? fst (fst aw) + snd (fst aw))
      then byte_of (snd aw) (a - fst (fst aw)) else old)
      (m_bytes image_seed a) ws) = m_bytes image_seed a).
  assert (Htest : (p <=? a) && (a <? p + n) = false).
  { apply andb_false_iff. destruct Hspan as [Hspan|Hspan].
    - left. apply Z.leb_gt. exact Hspan.
    - right. apply Z.ltb_ge. exact Hspan. }
  rewrite Htest. exact (IH Htail).
Qed.

(** The entire private parser is zero-initialized, byte by byte. *)
Lemma entry_parser_zero : forall i, 0 <= i < 56 ->
  m_bytes entry_memory (ptr_addr parser + i) = 0.
Proof.
  intros i Hi. rewrite entry_bytes_unwritten.
  - unfold parser; cbn [ptr_addr].
    destruct (Z.ltb_spec (131072 + i) 131072); [lia|reflexivity].
  - change (Forall (fun aw => 131072 + i < fst (fst aw) \/
      fst (fst aw) + snd (fst aw) <= 131072 + i) image_words).
    repeat (apply List.Forall_cons; [cbn [fst snd]; lia|]). constructor.
Qed.

(** Freshness decodes the initialized word from the joint physical image. *)
Lemma entry_parser_fresh : getopt_parser_fresh parser entry_memory entry_parser.
Proof.
  split.
  - split; [left; reflexivity|]. split.
    + split; [simpl; lia|]. split.
      * exists 131072, (mkRegion 131072 131128 GlobalData Live).
        split; [left; reflexivity|]. split; reflexivity.
      * split; [reflexivity|]. intros i Hi.
        rewrite (entry_parser_zero i Hi). lia.
    + split.
      * split; [simpl; lia|].
        exists 131072, (mkRegion 131072 131128 GlobalData Live).
        repeat split; reflexivity.
      * reflexivity.
  - split; [reflexivity|].
    change (load_bytes entry_memory 131096 4 = 0).
    reflexivity.
Qed.

Local Ltac entry_writable :=
  split; [cbn [span_size]; lia|];
  eexists; eexists; split; [reflexivity|];
  split; [reflexivity|]; split; reflexivity.

Local Ltac entry_pointer :=
  split; [entry_writable|]; split; [reflexivity|]; split; [reflexivity|];
  split; [cbv [ptr_addr null out_handle err_handle entry_parser getopt_optarg]; lia|];
  split; reflexivity.

Local Ltac entry_int :=
  split; [unfold getopt_int; cbn [entry_parser getopt_optind getopt_opterr getopt_optopt getopt_errno]; lia|];
  split; [entry_writable|]; split; [reflexivity|]; split; reflexivity.

(** All public getopt observations, including sampled errno, are coherent. *)
Lemma entry_public_state : getopt_state_at entry_memory entry_parser.
Proof.
  split; [entry_pointer|]. split; [entry_int|].
  split; [entry_int|]. split; entry_int.
Qed.

(** Both imported stream cells expose the corresponding FILE capability. *)
Lemma entry_stream_cells :
  exposed_pointer_cell entry_memory out_cell out_handle /\
  exposed_pointer_cell entry_memory err_cell err_handle.
Proof. split; entry_pointer. Qed.

(** The empty environment is a readable sentinel-terminated vector. *)
Lemma entry_environment : string_vector entry_memory environment_pointer [].
Proof.
  split; [reflexivity|]. split; [cbn; lia|]. split; reflexivity.
Qed.

(** No synthetic FILE shadow slot delegates an external object. *)
Lemma entry_file_aux : forall a, 131328 <= a < 131840 -> m_aux entry_memory a = CNone.
Proof.
  intros a Ha. cbn [entry_memory image_pointers fold_right fst snd m_aux image_seed].
  image_bounds; reflexivity.
Qed.

(** Neither FILE owns or reaches the shared errno cell. *)
Lemma entry_file_errno : forall a, a = 131328 \/ a = 131584 ->
  file_errno_apart entry_memory errno_pointer
    (mkLibcFile (mkPtr a (Obj a)) 0 [] [mkSpan (mkPtr a (Obj a)) 256] []).
Proof.
  intros a Ha. split.
  - intros root [<-|[]]. unfold spans_apart. cbn [span_ptr span_size ptr_addr errno_pointer]. lia.
  - intros b [Hb|Hb]; [injection Hb as <-|discriminate]. split; [intros []|]. split.
    all: intros [Hnone|[(source & Hin & Hcap)|[(source & addr & Hin & Haddr & Hsize & _ & Haux)|(b & [] & _)]]];
      try discriminate.
    all: cbn [file_sources file_handle file_reads file_roots app] in Hin;
      destruct Hin as [<-|[<-|[]]];
      cbn [file_handle span_ptr ptr_cap span_size ptr_addr] in *;
      try discriminate; try (injection Hcap; lia).
    all: unfold span_contains in Haddr;
      cbn [file_handle span_ptr span_size ptr_addr] in Haddr; try lia.
    all: rewrite (entry_file_aux addr ltac:(lia)) in Haux; discriminate.
Qed.

(** Both synthetic FILE objects meet structural capability readiness. *)
Lemma entry_files_ready :
  libc_file_ready entry_memory errno_pointer entry_out /\
  libc_file_ready entry_memory errno_pointer entry_err.
Proof.
  assert (Hfile : forall a, a = 131328 \/ a = 131584 ->
    libc_file_ready entry_memory errno_pointer
      (mkLibcFile (mkPtr a (Obj a)) 0 [] [mkSpan (mkPtr a (Obj a)) 256] [])).
  { intros a Ha. split; [cbn; lia|]. split.
    - destruct Ha as [-> | ->]; split; [simpl; lia| |simpl; lia|]; split.
      + exists 131328, (mkRegion 131328 131584 GlobalData Live).
        split; [left; reflexivity|]. split; reflexivity.
      + split; [reflexivity|]. intros i Hi. assert (i = 0) as -> by lia.
        change (0 <= 0 < 256). lia.
      + exists 131584, (mkRegion 131584 131840 GlobalData Live).
        split; [left; reflexivity|]. split; reflexivity.
      + split; [reflexivity|]. intros i Hi. assert (i = 0) as -> by lia.
        change (0 <= 0 < 256). lia.
    - split; [simpl; lia|]. split.
      + constructor; [destruct Ha as [-> | ->]; entry_writable|constructor].
      + split; [constructor|]. split; [constructor|apply entry_file_errno; exact Ha]. }
  split; apply Hfile; auto.
Qed.

(** Exact pointer-slot capabilities, with empty interior shadow slots. *)
Definition argv_aux : list cap :=
  (Obj 196640 :: replicate 7 CNone) ++ (Obj 196672 :: replicate 7 CNone) ++ replicate 8 CNone.
(** The full three-slot argv allocation. *)
Definition argv_region : region := mkRegion argv_base (argv_base + 24) Heap Live.
(** Hello's own program_name cell, from its linked initializer. *)
Definition name_region : region := mkRegion 66080 66088 GlobalData Live.
(** The full invocation-name cell's allocation. *)
Definition full_region : region := mkRegion 131248 131256 GlobalData Live.
(** The short invocation-name cell's allocation. *)
Definition short_region : region := mkRegion 131264 131272 GlobalData Live.
(** Ownership of all three cells consumed by Hello's name setup. *)
Definition name_pieces : list (piece * pval) :=
  (PLive 66080, VLive name_region) :: cell 66080 0 0 ++ [(PAux 66080 0, VAux CNone)] ++
  (PLive 131248, VLive full_region) :: cell 131248 0 196640 ++ [(PAux 131248 0, VAux (Obj 196640))] ++
  (PLive 131264, VLive short_region) :: cell 131264 0 196640 ++ [(PAux 131264 0, VAux (Obj 196640))].
(** One resource bundle for main's selected version path. *)
Definition entry_pieces : list (piece * pval) :=
  block_ps argv_base argv_region 0 (argv_bytes (map arg_ptr arguments)) argv_aux ++
  flat_map arg_ps arguments ++ getopt_ps null 1 ++
  string_ps libs_ptr 66112 (mkRegion 66112 66120 GlobalData Live) libs_bytes ++
  string_ps lt_ptr 66144 (mkRegion 66144 66152 GlobalData Live) lt_bytes ++ name_pieces ++
  map (fun k => (PName k, VName locale_pointer [67])) locale_categories ++ codec_ps (TAtom "C") ++
  string_ps empty_ptr 69968 (mkRegion 69968 69976 GlobalData Live) [] ++ hello_output_pieces.
(** The single ghost heap holding that resource bundle. *)
Definition entry_heap : gmap piece pval := overwrite entry_pieces ∅.

Local Transparent hello_literal_memory.

(** These pieces supply main_to_version's resources, not separate
    per-contract admissions. In particular the full argv block, actual
    strings, name cells, locale names and output literals coexist. *)
Lemma entry_keys_unique : NoDup (map fst entry_pieces).
Proof.
  pose (eqp := (ltac:(intros x y; change ({x = y} + {x <> y});
    decide equality; apply Z.eq_dec) : EqDecision piece)).
  apply (@bool_decide_eq_true _ (@NoDup_dec piece eqp _)). vm_compute. reflexivity.
Qed.

(** A finite certificate checks the unique registered region rather than
    expanding a universally quantified region once per literal byte.
    Exact aux equality is sufficient for the weaker collector-aware
    agreement. This checker is only a proof device for the model image. *)
Local Definition checked_piece (m : mem) (l : piece) (v : pval) : Prop :=
  match l, v with
  | PLive b, VLive reg => live_at m b reg
  | PByte b o, VByte x =>
    match object_region b (m_regions m) with
    | Some reg => r_life reg = Live -> 0 <= o /\ b + o < r_end reg /\ m_bytes m (b + o) = x
    | None => False
    end
  | PAux b o, VAux c =>
    match object_region b (m_regions m) with
    | Some reg => r_life reg = Live -> 0 <= o /\ b + o < r_end reg /\ m_aux m (b + o) = c
    | None => False
    end
  | PName _, VName _ _ | PName _, VCodec _ | PName _, VGetopt _ _ => True
  | _, _ => False
  end.

(** The finite certificate implies the public heap agreement predicate. *)
Local Lemma checked_piece_sound m l v : checked_piece m l v -> agree_piece m l v.
Proof.
  destruct l, v; cbn [checked_piece agree_piece]; try tauto.
  - destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|tauto].
    intros H. split; [unfold registered; congruence|].
    intros reg' E' Hlive. rewrite E in E'. injection E' as <-. exact (H Hlive).
  - destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|tauto].
    intros H. split; [unfold registered; congruence|].
    intros reg' E' Hlive. rewrite E in E'. injection E' as <-.
    destruct (H Hlive) as (Ho & Hb & Ha). repeat split; try assumption. left. exact Ha.
Qed.

(** All operations in a certificate have transparent finite decisions. *)
Local Instance checked_piece_dec m l v : Decision (checked_piece m l v).
Proof.
  pose (eqr := (ltac:(intros x y; change ({x = y} + {x <> y});
    decide equality; try apply Z.eq_dec; decide equality) : EqDecision region)).
  pose (eql := (ltac:(intros x y; change ({x = y} + {x <> y});
    decide equality) : EqDecision life)).
  pose (eqt := (ltac:(intros x y; change ({x = y} + {x <> y});
    destruct (term_eqb x y) eqn:E;
      [left; apply term_eqb_eq; exact E |
       right; intros ->; rewrite term_eqb_refl in E; discriminate]) : EqDecision term)).
  pose (eqc := (ltac:(intros x y; change ({x = y} + {x <> y});
    decide equality; first [apply eqt | apply Z.eq_dec]) : EqDecision cap)).
  destruct l, v; cbn [checked_piece]; try apply _;
    destruct (object_region b (m_regions m)); apply _.
Defined.

(** Every piece in the single initial resource bundle agrees. *)
Lemma entry_pieces_agree : all_agree entry_memory entry_pieces.
Proof.
  assert (Hcheck : forallb (fun lv => bool_decide (checked_piece entry_memory lv.1 lv.2))
    entry_pieces = true) by (vm_compute; reflexivity).
  apply all_agree_intro. intros l v Hin. apply checked_piece_sound.
  rewrite forallb_forall in Hcheck.
  apply (bool_decide_eq_true_1 (checked_piece entry_memory l v)).
  apply (Hcheck (l, v)). clear Hcheck. induction Hin; cbn; auto.
Qed.

Local Opaque entry_pieces.

(** Agreement lifts from the entire resource list to its ghost heap. *)
Lemma entry_agrees : agrees entry_memory entry_heap.
Proof.
  intros l v Hlookup. apply lookup_overwrite in Hlookup as [Hin|[_ Hempty]].
  - exact (all_agree_elem _ _ _ _ entry_pieces_agree Hin).
  - rewrite lookup_empty in Hempty. discriminate.
Qed.

(** Every initial locale name is a readable aligned C string. *)
Lemma entry_locale_ready : locale_ready (fun _ _ => True) entry_memory entry_locale.
Proof.
  split; [exact I|]. split; [constructor|]. split.
  - intros k Hk. split; [discriminate|]. split; [reflexivity|].
    split; [simpl; lia|]. split; reflexivity.
  - split.
    + constructor; [|constructor]. split; [simpl; lia|]. split.
      * exists 131840, (mkRegion 131840 131842 GlobalData Live).
        split; [right; reflexivity|]. split; reflexivity.
      * split; [reflexivity|]. intros i Hi. cbn [span_size] in Hi.
        assert (i = 0 \/ i = 1) as [-> | ->] by lia;
          [change (0 <= 67 < 256)|change (0 <= 0 < 256)]; lia.
    + split; [constructor|]. intros k Hk. exists 131840.
      split; [right; reflexivity|reflexivity].
Qed.

(** Locale, FILEs, errno and shutdown are structurally coherent together. *)
Lemma entry_stream_ready : libc_stream_ready (fun _ _ => True) entry_memory entry_world.
Proof.
  split; [exact I|]. split; [exact entry_locale_ready|]. split.
  - split; [discriminate|]. split; [entry_writable|reflexivity].
  - split; [apply stdout_initial_wf|]. split; [apply stdout_initial_wf|].
    split; [constructor|]. split; [simpl; lia|]. split; [exact I|].
    split; [discriminate|]. split; [reflexivity|].
    split; [intros _; exact (proj1 entry_files_ready)|].
    split; [intros _; exact (proj2 entry_files_ready)|].
    intros p file Hfile b Hin. unfold libc_file_at in Hfile.
    destruct (same_file p (libc_stdout entry_world));
      [|destruct (same_file p (libc_stderr entry_world))];
      try discriminate; injection Hfile as <-; contradiction.
Qed.

(** Hello's actual option string and sentinel-terminated table are readable. *)
Lemma entry_table : hello_table_at entry_memory.
Proof.
  unfold hello_table_at. split.
  - vm_compute. repeat split; congruence.
  - split; [reflexivity|]. cbn [getopt_records hello_options].
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- pointer_slot _ _ _ => vm_compute; repeat split; congruence
    | |- c_string _ _ _ => vm_compute; repeat split; congruence
    | |- getopt_int _ => unfold getopt_int; cbn [option_value]; lia
    | |- getopt_optional_int _ _ => left; reflexivity
    | |- exists p, _ => exists null; vm_compute; repeat split; congruence
    | _ => vm_compute; congruence
    end.
Qed.

(** The native-view predicate has this explicit synthetic model witness. *)
Lemma entry_native : native_at entry_memory entry_world.
Proof.
  split; [exact entry_stream_ready|]. split.
  - split; [repeat split; reflexivity|]. split; [exact entry_public_state|].
    left. exact entry_parser_fresh.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (proj1 entry_stream_cells)|]. split; [exact (proj2 entry_stream_cells)|].
    split; [exact entry_environment|exact entry_table].
Qed.

(** Every initial heap lookup comes from the one joint resource bundle. *)
Lemma entry_lookup_member l v : entry_heap !! l = Some v -> (l, v) ∈ entry_pieces.
Proof.
  intros Hl. apply lookup_overwrite in Hl as [Hin|[_ Hempty]]; [exact Hin|].
  rewrite lookup_empty in Hempty. discriminate.
Qed.

(** The initial bundle's only ghost observations are the parser token,
    the locale names and the codec; none freezes native FILE contents. *)
Lemma entry_ghost_lookup k v : entry_heap !! PName k = Some v ->
  In (PName k, v) (getopt_ps null 1 ++
    map (fun k => (PName k, VName locale_pointer [67])) locale_categories ++ codec_ps (TAtom "C")).
Proof.
  intros Hl. apply entry_lookup_member in Hl. apply list_elem_of_In in Hl.
  Local Transparent entry_pieces.
  assert (Hfilter : List.filter (fun lv => match lv.1 with PName _ => true | _ => false end)
    entry_pieces = getopt_ps null 1 ++
      map (fun k => (PName k, VName locale_pointer [67])) locale_categories ++ codec_ps (TAtom "C")).
  { unfold entry_pieces. vm_compute. reflexivity. }
  Local Opaque entry_pieces.
  rewrite <- Hfilter. apply filter_In. split; [exact Hl|reflexivity].
Qed.

(** The concrete model's native capability inventories are private from
    every memory piece of main, including object lives. *)
Lemma entry_private : Forall (fun source => cap_private entry_heap (ptr_cap (span_ptr source)))
  (private_sources entry_world).
Proof.
  Local Transparent entry_pieces.
  assert (Hcheck : forallb (fun source => forallb (fun lv =>
    match lv.1, ptr_cap (span_ptr source) with
    | PName _, _ => true
    | _, Obj b | _, Ro b => negb (Z.eqb (piece_id lv.1) b)
    | _, _ => true
    end) entry_pieces) (private_sources entry_world) = true).
  { unfold entry_pieces. vm_compute. reflexivity. }
  Local Opaque entry_pieces.
  rewrite forallb_forall in Hcheck. apply List.Forall_forall. intros source Hin b Hcap.
  specialize (Hcheck source Hin). rewrite forallb_forall in Hcheck.
  intros b' l v [<-|[]] Hl Hmem. apply entry_lookup_member in Hl.
  apply list_elem_of_In in Hl. specialize (Hcheck (l, v) Hl).
  destruct Hcap as [Hcap|Hcap]; rewrite Hcap in Hcheck;
    destruct l; try contradiction; cbn [fst piece_id] in Hcheck |- *;
    apply Z.eqb_neq; apply negb_true_iff; exact Hcheck.
Qed.

(** The initial names, codec and getopt observations all agree with the
    same physical native world. *)
Lemma entry_current : names_current entry_locale entry_heap /\
  codec_current entry_locale entry_heap /\ getopt_current entry_parser entry_heap.
Proof.
  split.
  - intros k p t Hl. apply entry_ghost_lookup in Hl.
    cbn [getopt_ps getopt_key codec_ps codec_key locale_categories List.app List.map] in Hl.
    repeat destruct Hl as [E|Hl]; try contradiction; try discriminate E;
      (injection E as <- <- <-; split; [cbn; auto 30|split; reflexivity]).
  - split.
    + intros c Hl. apply entry_ghost_lookup in Hl.
      cbn [getopt_ps getopt_key codec_ps codec_key locale_categories List.app List.map] in Hl.
      repeat destruct Hl as [E|Hl]; try contradiction; try discriminate E;
        injection E as <-; reflexivity.
    + intros a i Hl. apply entry_ghost_lookup in Hl.
      cbn [getopt_ps getopt_key codec_ps codec_key locale_categories List.app List.map] in Hl.
      repeat destruct Hl as [E|Hl]; try contradiction; try discriminate E;
        injection E as <- <-; split; reflexivity.
Qed.

(** One composite world interpretation is inhabited jointly with the
    actual main resource bundle and heap agreement. This is a model
    entry witness, not native adequacy or cross-call restoration. *)
Theorem entry_inhabited : wi entry_memory entry_world entry_heap /\
  agrees entry_memory entry_heap /\ NoDup (map fst entry_pieces).
Proof.
  split.
  - split; [exact entry_native|]. split; [exact entry_private|].
    split; [intros b l v []; contradiction|]. exact entry_current.
  - split; [exact entry_agrees|exact entry_keys_unique].
Qed.

End HelloWorld.

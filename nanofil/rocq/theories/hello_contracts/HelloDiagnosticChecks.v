(** Logical controls for Hello's four-argument diagnostic binding.
    These use actual fixture literals and the supplied machine, but
    empty private native inventories. The Iris rule is partial correctness,
    not native execution or a proof of the complete close_stdout body. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run ExternalCalls LibcCalls ExternalMachine
  Stdio Shutdown Streams Formatting Libc LibcStreams Pieces Heap ContractFrame Logic
  StringLogic LibcStringLogic MemLogic LibcMemLogic LentLogic Locale LibcStreamLogic LibcErrnoLogic LibcStreamTokens
  LibcStreamAdapter LibcDiagnosticLogic HelloModule HelloLeaf HelloReach HelloStdio.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Module HelloDiagnosticChecks.
Module F := LibcStreamChecks.
Module T := StreamTokenChecks.
Module H := HelloCallbackChecks.H.
Module LG := StreamHandleChecks.LG.
Module Reach := HelloReach InterpRuntime.
Import LG LG.L.

Definition text := [119; 114; 105; 116; 101; 32; 101; 114; 114; 111; 114].
Definition memory : mem := mkMem
  (fun a => if (65680 <=? a) && (a <? 65692) then nth (Z.to_nat (a - 65680)) text 0
    else if (65744 <=? a) && (a <? 65747) then nth (Z.to_nat (a - 65744)) [37; 115] 0
    else m_bytes conversion_mem a)
  (m_regions conversion_mem ++ [mkRegion 65680 65696 GlobalData Live; mkRegion 65744 65752 GlobalData Live])
  (m_aux conversion_mem).

Lemma literals_agree : all_agree memory hello_diagnostic_pieces.
Proof.
  vm_compute. repeat split; intros;
    repeat match goal with H : Some _ = Some _ |- _ => injection H as <- end;
    vm_compute; intuition congruence.
Qed.

Definition heap (_ : bool) := overwrite hello_diagnostic_pieces HelloErrnoChecks.heap.

Lemma overwrite_owned ps (h : gmap piece pval) : base.NoDup ps.*1 ->
  forall l v, (l,v) ∈ ps -> overwrite ps h !! l = Some v.
Proof.
  induction ps as [|[k u] ps IH]; intros Hdup l v Hin; [set_solver|].
  inversion Hdup as [|? ? Hnot Htail]; subst.
  apply elem_of_cons in Hin as [E|Hin].
  - injection E as <- <-. cbn [overwrite]. apply lookup_insert_eq.
  - cbn [overwrite]. rewrite lookup_insert_ne; [apply IH; assumption|].
    simpl. intros E. subst k. apply Hnot. apply list_elem_of_fmap. exists (l,v). auto.
Qed.

Lemma heap_owned : forall opened l v, (l, v) ∈ hello_diagnostic_pieces -> heap opened !! l = Some v.
Proof.
  intros opened. apply overwrite_owned. apply NoDup_ListNoDup, hello_diagnostic_keys.
Qed.

Lemma heap_agrees : forall opened, agrees memory (heap opened).
Proof.
  intros opened l v Hl.
  destruct (lookup_overwrite hello_diagnostic_pieces HelloErrnoChecks.heap l v Hl)
    as [Hin|[_ Hold]].
  - eapply all_agree_elem; [exact literals_agree|exact Hin].
  - unfold HelloErrnoChecks.heap in Hold.
    apply elem_of_list_to_map_2 in Hold.
    eapply all_agree_elem; [|exact Hold].
    change (all_agree memory (byte_ps 5120 0 (errno_bytes memory 5120 0))).
    apply errno_bytes_agree.
    split; [discriminate|]. split; [|reflexivity].
    split; [simpl; lia|]. exists 5120, (mkRegion 5120 5128 Heap Live).
    repeat split; reflexivity.
Qed.

Lemma regions : forall b reg, object_region b (m_regions memory) = Some reg ->
  In (b,reg) [(1024,mkRegion 1024 1056 GlobalData Live); (2048,mkRegion 2048 2056 Stack Live);
    (3072,mkRegion 3072 3080 Stack Live); (4096,mkRegion 4096 4104 GlobalData Live);
    (5120,mkRegion 5120 5128 Heap Live); (65680,mkRegion 65680 65696 GlobalData Live);
    (65744,mkRegion 65744 65752 GlobalData Live)].
Proof.
  intros b reg Hreg. cbn [memory conversion_mem m_regions app object_region r_base] in Hreg.
  repeat destruct (_ =? _) eqn:? in Hreg; try discriminate;
    injection Hreg as <-;
    repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end;
    subst; simpl; tauto.
Qed.

Lemma disjoint : live_disjoint memory.
Proof.
  intros b1 r1 b2 r2 [E1 _] [E2 _] Hne. apply regions in E1, E2.
  repeat destruct E1 as [E1|E1]; try contradiction;
    injection E1 as <- <-;
    repeat destruct E2 as [E2|E2]; try contradiction;
    injection E2 as <- <-; simpl in *; lia.
Qed.

Lemma runtime_ready : InterpRuntime.ready InterpRuntime.start memory.
Proof.
  split; [change (0 < 4294967296 <= 281474976710656); lia|]. split.
  - intros b reg E. apply regions in E.
    change (0 <= b < 4294967296 /\ r_end reg <= 4294967296 /\
      (r_life reg = Freed -> r_end reg = b)).
    repeat destruct E as [E|E]; try contradiction;
      injection E as <- <-; simpl; intuition (try discriminate; lia).
  - intros a Ha. change (4294967296 <= a) in Ha.
    cbn [memory conversion_mem m_bytes m_aux].
    assert (Htext : ((65680 <=? a) && (a <? 65692)) = false).
    { apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia. }
    assert (Hfmt : ((65744 <=? a) && (a <? 65747)) = false).
    { apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia. }
    rewrite Htext Hfmt.
    repeat match goal with |- context [a =? ?b] =>
      destruct (Z.eqb_spec a b); [subst; lia|] end; auto.
Qed.

Lemma ready : forall opened, libc_stream_ready (fun _ _ => True) memory (F.world opened).
Proof.
  intros opened.
  assert (Hl : locale_ready (fun _ _ => True) memory (libc_locale (fst conversion_world))).
  { split; [exact I|]. split; [constructor|]. split.
    - intros k _. split; [discriminate|]. vm_compute. repeat split; congruence.
    - split; [constructor|]. split; [constructor|].
      intros k _. exists 4096. split; [right; reflexivity|reflexivity]. }
  assert (He : errno_cell memory (mkPtr 5120 (Obj 5120))).
  { split; [discriminate|]. split; [|reflexivity].
    split; [simpl; lia|]. exists 5120, (mkRegion 5120 5128 Heap Live). repeat split; reflexivity. }
  assert (Hfiles : libc_file_ready memory (mkPtr 5120 (Obj 5120)) F.out_file /\
    libc_file_ready memory (mkPtr 5120 (Obj 5120)) F.err_file).
  { assert (Hread : forall a, a = 1024 \/ a = 2048 -> readable_bytes memory (mkPtr a (Obj a)) 1).
    { intros a [-> | ->]; split; [simpl; lia| |simpl; lia|].
      all: split.
      1: { exists 1024, (mkRegion 1024 1056 GlobalData Live). auto. }
      2: { exists 2048, (mkRegion 2048 2056 Stack Live). auto. }
      all: split; [reflexivity|].
      all: intros i Hi; assert (i = 0) as -> by lia; vm_compute; split; congruence. }
    assert (Hapart : forall a n, a <> 5120 -> file_errno_apart memory (mkPtr 5120 (Obj 5120))
      (mkLibcFile (mkPtr a (Obj a)) n [] [] [])).
    { intros a n Hne. split; [intros root []|]. intros base [Hbase|Hbase];
      [injection Hbase as <-|discriminate]. split; [intros []|]. split;
      intros [Hnone|[(source & Hin & Hcap)|[(source & addr & Hin & Ha & Hsize & _)|(b & [] & _)]]];
      try discriminate; simpl in Hin; destruct Hin as [<-|[]]; simpl in *;
      [congruence|unfold span_contains in Ha; simpl in Ha; lia|discriminate|
       unfold span_contains in Ha; simpl in Ha; lia]. }
    split; unfold F.out_file, F.err_file, libc_file_ready; split; [discriminate| |discriminate|].
    all: split; [apply Hread; auto|].
    all: split; [simpl; lia|].
    all: split; [constructor|]. all: split; [constructor|].
    all: split; [constructor|apply Hapart; lia]. }
  split; [exact I|]. split; [exact Hl|]. split; [exact He|].
  split; [split; [destruct opened; repeat constructor; lia|reflexivity]|].
  split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|].
  split; [exact I|]. split; [simpl; lia|]. split; [destruct opened; reflexivity|].
  split; [intros _; exact (proj1 Hfiles)|]. split; [intros _; exact (proj2 Hfiles)|].
  intros p file Hfile base Hin. unfold libc_file_at in Hfile.
  destruct (same_file p (libc_stdout (F.world opened)));
    [destruct opened|destruct (same_file p (libc_stderr (F.world opened)))];
    try discriminate; injection Hfile as <-; contradiction.
Qed.

Definition native := mkDiagnosticContext libc_world
  (fun _ w => (exists file, libc_file_at w (libc_stderr w) = Some file) /\
    orientation (libc_stream_state w (libc_stderr w)) <> WideOriented)
  (fun _ _ => []) (fun _ => []) (fun _ _ _ => False)
  (fun _ _ _ body segments => segments = [body; [10]]) (fun _ _ => True).
Definition wi m w h :=
  libc_diagnostic_wi (fun _ _ => True) native T.out T.err 5120 0 m w h /\
  diagnostic_ready native m w.

Lemma names_absent : forall opened key, heap opened !! PName key = None.
Proof.
  intros. unfold heap. rewrite overwrite_out.
  - unfold HelloErrnoChecks.heap. apply not_elem_of_list_to_map_1.
    rewrite byte_ps_keys. intros Hin.
    apply list_elem_of_fmap in Hin as (i & E & _). discriminate E.
  - intros Hin. apply list_elem_of_fmap in Hin as ([l v] & E & Hin).
    apply list_elem_of_In in Hin. vm_compute in Hin.
    repeat destruct Hin as [Hin|Hin]; try contradiction;
      injection Hin as <- <-; discriminate E.
Qed.

Lemma heap_errno : forall opened l v, (l,v) ∈ byte_ps 5120 0 [0;0;0;0] ->
  heap opened !! l = Some v.
Proof.
  intros opened l v Hin. unfold heap. rewrite overwrite_out.
  - unfold HelloErrnoChecks.heap. apply elem_of_list_to_map_1; [|exact Hin].
    change (base.NoDup [PByte 5120 0; PByte 5120 1; PByte 5120 2; PByte 5120 3]).
    repeat (apply base.NoDup_cons_2; [set_solver|]). apply base.NoDup_nil_2.
  - destruct (MemLogic.byte_ps_elem _ _ _ _ _ Hin) as (i & x & Hi & -> & ->).
    clear Hin.
    intros Hkey. apply list_elem_of_fmap in Hkey as ([l v] & E & Hin).
    apply list_elem_of_In in Hin. vm_compute in Hin.
    repeat destruct Hin as [Hin|Hin]; try contradiction;
      injection Hin as <- <-; discriminate E.
Qed.

Lemma entry_wi : forall opened, wi memory (F.world opened) (heap opened).
Proof.
  intros opened.
  assert (Hoff : pieces_off (errno_keys 5120 0) (stream_data_heap 1024 2048 (heap opened))
    memory (span_contains (errno_span 5120 0))).
  { intros l v Hl Hnot. apply stream_data_lookup in Hl as [Hl _].
    destruct (lookup_overwrite hello_diagnostic_pieces HelloErrnoChecks.heap l v Hl)
      as [Hin|[_ Hold]].
    - apply list_elem_of_In in Hin. vm_compute in Hin.
      repeat destruct Hin as [Hin|Hin]; try contradiction; injection Hin as <- <-;
        cbn; try exact I;
        intros reg Hlive Hlo Hhi Hspan;
        unfold span_contains, errno_span in Hspan; simpl in Hspan; lia.
    - exfalso. apply Hnot. unfold HelloErrnoChecks.heap in Hold.
      apply elem_of_list_to_map_2 in Hold.
      change (l ∈ (byte_ps 5120 0 [0;0;0;0]).*1).
      apply list_elem_of_fmap. exists (l,v). auto. }
  assert (Hpair : stream_tokens_wi (fun _ _ => True) T.out T.err 5120 0
    memory (F.world opened) (heap opened)).
  { split; [split; [reflexivity|simpl; lia]|]. split; [split; [reflexivity|simpl; lia]|].
    split; [discriminate|]. split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold stream_current; rewrite names_absent; exact I|].
    split; [unfold stream_current; rewrite names_absent; exact I|].
    intros d [-> | ->].
    all: split; [|intros base l v Hin; destruct opened; contradiction].
    all: split; [apply ready|]. all: split; [reflexivity|].
    all: split; [intros root a Hin; destruct opened; contradiction|].
    all: split; [intros base l v Hin; destruct opened; contradiction|exact Hoff]. }
  split.
  - split; [exact Hpair|]. split; [intros root a []|].
    unfold diagnostic_name. rewrite !names_absent. auto.
  - split; [exists F.err_file; destruct opened; reflexivity|destruct opened; discriminate].
Qed.

Definition spec := libc_error_contract (fun _ _ => True)
  (fun _ _ _ _ => False) (fun _ _ _ _ _ => False) native.
Definition words := [WInt 0; WInt 0; WPtr (mkPtr 65744 (Ro 65744)); WPtr (mkPtr 65680 (Ro 65680))].

Example admitted : forall opened, contract_pre spec words memory (F.world opened).
Proof.
  intros. eapply hello_diagnostic_admitted with (h := heap opened) (file := F.err_file).
  - lia.
  - apply heap_agrees.
  - apply heap_owned.
  - exact (proj2 (entry_wi opened)).
  - apply ready.
  - constructor.
  - destruct opened; reflexivity.
  - destruct opened; discriminate.
Qed.

Lemma admission_stderr : forall m w, contract_pre spec words m w ->
  (exists file, libc_file_at w (libc_stderr w) = Some file) /\
  orientation (libc_stream_state w (libc_stderr w)) <> WideOriented.
Proof.
  intros m w [[Hfmt _] _].
  destruct Hfmt as (status & errnum & fmt & rest & format & body & info &
    Hwords & Hstatus & Herrnum & Hstring & Hformat & Hready & Hrest).
  exact (proj1 Hready).
Qed.

Example closed_stderr_rejected : forall m w,
  libc_file_at w (libc_stderr w) = None -> ~ contract_pre spec words m w.
Proof.
  intros m w Hclosed Hpre. destruct (admission_stderr m w Hpre) as [[file Hfile] _]. congruence.
Qed.

Example wide_stderr_rejected : forall m w,
  orientation (libc_stream_state w (libc_stderr w)) = WideOriented -> ~ contract_pre spec words m w.
Proof. intros m w Hwide Hpre. exact (proj2 (admission_stderr m w Hpre) Hwide). Qed.

Definition changed := store_bytes memory 5120 4 16909060.
Definition final_world (opened : bool) : libc_world :=
  (mkLibcPayload (libc_locale (fst conversion_world))
    (mkStdioWorld opened [mkSpan (libc_errno (fst conversion_world)) 4])
    (libc_errno (fst conversion_world))
    (mkLibcStreams F.out_file F.err_file true (mkStream ByteOriented (text ++ [10]) false))
    (libc_getopt (fst conversion_world)),
   mkShutdown Handlers 0 [] [] (mkStream ByteOriented [] true)).

Lemma changed_ready : forall opened,
  libc_stream_ready (fun _ _ => True) changed (final_world opened).
Proof.
  intros opened. destruct (ready true)
    as (Hrep & Hlocale & He & _ & _ & Hu & Hstatus & Hphase & Hdistinct & Hroots & Ho & Herr & Hsep).
  assert (Hfiles : libc_file_ready changed (mkPtr 5120 (Obj 5120)) F.out_file /\
    libc_file_ready changed (mkPtr 5120 (Obj 5120)) F.err_file).
  { split; [specialize (Ho eq_refl); clear Herr|specialize (Herr eq_refl); clear Ho].
    all: (destruct Ho as (Hnon & (Hn & Hreg & Haccess & Hbytes) & Hrest)
      || destruct Herr as (Hnon & (Hn & Hreg & Haccess & Hbytes) & Hrest)).
    all: split; [exact Hnon|].
    all: split; [|destruct Hrest as (Hp & _ & _ & _ & Ha);
      split; [exact Hp|]; split; [constructor|]; split; [constructor|];
      split; [constructor|exact Ha]].
    all: split; [exact Hn|]. all: split; [exact Hreg|]. all: split; [exact Haccess|].
    all: intros i Hi; assert (i = 0) as -> by lia; vm_compute; split; congruence. }
  split; [exact I|]. split.
  - destruct Hlocale as (_ & _ & _ & _ & _ & Haligned).
    split; [exact I|]. split; [constructor|]. split.
    + intros category _. vm_compute. repeat split; congruence.
    + split; [constructor|]. split; [constructor|exact Haligned].
  - split; [exact He|]. split.
    + change (stream_wf (mkStream ByteOriented [] true)).
      split; [constructor|intros _; reflexivity].
    + split.
      * change (stream_wf (mkStream ByteOriented (text ++ [10]) false)).
        cbn [stream_wf outstanding orientation text app].
        split; [repeat constructor; lia|intros _; reflexivity].
      * split; [exact Hu|]. split; [exact Hstatus|]. split; [exact Hphase|].
        split; [exact Hdistinct|]. split; [destruct opened; reflexivity|].
        split; [intros _; exact (proj1 Hfiles)|].
        split; [intros _; exact (proj2 Hfiles)|].
        intros p file Hfile base Hin. unfold libc_file_at in Hfile.
        destruct (same_file p (libc_stdout (final_world opened)));
          [destruct opened|destruct (same_file p (libc_stderr (final_world opened)))];
          try discriminate; injection Hfile as <-; contradiction.
Qed.

Definition call_args := [Arg W (Const 0); Arg W (Tmp (TAtom "errnum"));
  Arg P (Global (TAtom "closeout#str.55")); Arg P (Global (TAtom "closeout#str.53"))].

Lemma format_prefix : forall opened,
  error_format_prefix F.model libc_stdout libc_stderr (libc_diagnostic_context (fun _ _ => True) native)
    words memory (F.world opened) [] [StreamBytes 2 (text ++ [10])] changed (final_world opened).
Proof.
  intros opened.
  exists 0, 0, (mkPtr 65744 (Ro 65744)), [WPtr (mkPtr 65680 (Ro 65680))],
    [37;115], text, (mkStreamInfo 2 stdout_initial 3),
    (mkStreamInfo 2 (mkStream ByteOriented (text ++ [10]) false) 3),
    [text; [10]], [text; [10]], [Accept (text ++ [10])].
  split; [reflexivity|]. split.
  - pose proof (hello_diagnostic_owned "closeout#str.55" memory (heap opened)
      (or_introl eq_refl) (heap_owned opened) (heap_agrees opened)) as Hfmt.
    change (c_string memory (mkPtr 65744 (Ro 65744)) [37;115]) in Hfmt. exact Hfmt.
  - split.
    + rewrite <- (app_nil_r text). apply format_string; [|constructor].
      pose proof (hello_diagnostic_owned "closeout#str.53" memory (heap opened)
        (or_intror (or_introl eq_refl)) (heap_owned opened) (heap_agrees opened)) as Htext.
      change (c_string memory (mkPtr 65680 (Ro 65680)) text) in Htext. exact Htext.
    + split; [reflexivity|]. split.
      * repeat (constructor; [exists []; reflexivity|]). constructor.
      * split; [destruct opened; reflexivity|]. split.
        -- split; [apply changed_ready|]. split; [destruct opened; reflexivity|].
           split; [reflexivity|]. split.
           ++ split; [split; [repeat constructor; lia|reflexivity]|simpl; lia].
           ++ change (Forall (writable_span changed) [errno_span 5120 0]).
              constructor; [exact (proj1 (proj2 (proj1 (proj2 (proj2 (changed_ready opened))))))|constructor].
        -- split; [reflexivity|]. split; [reflexivity|]. split.
           ++ eapply stream_next; [apply stream_accept; [discriminate|repeat constructor; lia]|constructor].
           ++ split; [reflexivity|]. split.
              ** destruct opened.
                 --- exists (mkStreamInfo 1 (mkStream ByteOriented [] true) 7).
                     split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
                     split; [reflexivity|apply F.close_settles].
                 --- split; reflexivity.
              ** split.
                 --- split.
                     +++ split; [exists F.err_file; destruct opened; reflexivity|discriminate].
                     +++ apply changed_ready.
                 --- split; [split; [exact I|repeat split; reflexivity]|]. split.
                     +++ destruct opened.
                         *** split.
                             ---- intros root [E|[]]. subst root. split.
                                  ++++ right. left. exists (mkSpan (mkPtr 5120 (Obj 5120)) 0).
                                       split; [right; left; reflexivity|reflexivity].
                                  ++++ intros a Ha. left. exists (errno_span 5120 0).
                                       split; [left; reflexivity|]. split.
                                       ***** exact (proj1 (proj2 (proj1 (proj2 (proj2 (changed_ready true)))))).
                                       ***** exact Ha.
                             ---- split.
                                  ++++ intros source Hin. left. exists source. split; [exact Hin|reflexivity].
                                  ++++ intros x []; contradiction.
                         *** split; [intros root []|]. split; intros x []; contradiction.
                     +++ split.
                         *** split.
                             ---- intros root [E|[]]. subst root. split.
                                  ++++ right. left. exists (mkSpan (mkPtr 5120 (Obj 5120)) 0).
                                       split; [right; left; reflexivity|reflexivity].
                                  ++++ intros a Ha. left. exists (errno_span 5120 0).
                                       split; [left; reflexivity|]. split.
                                       ***** exact (proj1 (proj2 (proj1 (proj2 (proj2 (changed_ready opened)))))).
                                       ***** exact Ha.
                             ---- split.
                                  ++++ intros source Hin. left. exists source. split; [destruct opened; exact Hin|reflexivity].
                                  ++++ intros x []; destruct opened; contradiction.
                         *** split; [intros root []|]. split; [right; reflexivity|]. intros a _ _. reflexivity.
Qed.

Lemma returning_call : forall opened,
  H.M.E.invoke spec CVoid call_args words InterpRuntime.start memory (F.world opened)
    [StreamBytes 2 (text ++ [10])] (CallReturn []) InterpRuntime.start changed (final_world opened).
Proof.
  intros opened. eapply H.M.E.invoke_normal with (born := []).
  - split; [reflexivity|]. split.
    + split; [reflexivity|]. do 4 eexists. split; [reflexivity|].
      constructor; [eexists; left; reflexivity|constructor].
    + do 4 eexists. reflexivity.
  - apply admitted.
  - split.
    + eapply H.M.E.effects_local; [apply local_store_bytes|constructor].
      intros a Ha. left. exists (errno_span 5120 0).
      split; [apply in_or_app; right; apply in_or_app; left; destruct opened; left; reflexivity|].
      split.
      * exact (proj1 (proj2 (proj1 (proj2 (proj2 (ready opened)))))).
      * unfold span_contains, errno_span. simpl. lia.
    + split; [apply format_prefix|constructor; [reflexivity|constructor]].
  - split; [split; [apply format_prefix|reflexivity]|reflexivity].
  - intros why Hbad. discriminate Hbad.
  - intros vs Hvs. injection Hvs as <-. split; [reflexivity|constructor].
  - intros status Hbad. discriminate Hbad.
Qed.

Example combined_keys : NoDup (hello_diagnostic_pieces ++ byte_ps 5120 0 [0;0;0;0]).*1.
Proof.
  vm_compute. repeat (apply NoDup_cons;
    [simpl; intros Hbad; repeat destruct Hbad as [Hbad|Hbad]; try contradiction; discriminate|]).
  apply NoDup_nil.
Qed.

Example entry_usable : forall opened,
  agrees memory (heap opened) /\ live_disjoint memory /\ InterpRuntime.ready InterpRuntime.start memory /\
  wi memory (F.world opened) (heap opened) /\
  (forall l v, (l,v) ∈ hello_diagnostic_pieces ++ byte_ps 5120 0 [0;0;0;0] ->
    heap opened !! l = Some v).
Proof.
  intros. split; [apply heap_agrees|]. split; [apply disjoint|]. split; [apply runtime_ready|].
  split; [apply entry_wi|]. intros l v Hin. apply elem_of_app in Hin as [Hin|Hin];
    [apply heap_owned|apply heap_errno]; exact Hin.
Qed.

Example framed_return : forall opened,
  exists ys, length ys = 4%nat /\
    agrees changed (overwrite (hello_diagnostic_pieces ++ byte_ps 5120 0 ys) (heap opened)) /\
    (overwrite (hello_diagnostic_pieces ++ byte_ps 5120 0 ys) (heap opened)) !! PByte 5120 3 = Some (VByte 1) /\
    (forall l v, (l,v) ∈ hello_diagnostic_pieces ->
      (overwrite (hello_diagnostic_pieces ++ byte_ps 5120 0 ys) (heap opened)) !! l = Some v).
Proof.
  intros opened.
  destruct (entry_usable opened) as (Ha & Hd & Hr & Hw & Howned).
  destruct (H.D.error_pieces_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) native T.out T.err 5120 0 hello_diagnostic_pieces
    CVoid call_args words InterpRuntime.start memory (F.world opened) [StreamBytes 2 (text ++ [10])] []
    InterpRuntime.start changed (final_world opened) (heap opened) [0;0;0;0]
    (returning_call opened) Ha Hd Hr (proj1 Hw) eq_refl Howned
    (hello_diagnostic_errno_keys 5120 0 ltac:(lia) ltac:(lia)))
    as (ys & _ & Hlen & Hkeys & Hag & _ & _ & Hwi).
  assert (Hdup : base.NoDup (hello_diagnostic_pieces ++ byte_ps 5120 0 ys).*1).
  { rewrite Hkeys. apply NoDup_ListNoDup, combined_keys. }
  exists ys. split; [exact Hlen|]. split; [exact Hag|]. split.
  - destruct ys as [|a [|b [|c [|d rest]]]]; try discriminate Hlen.
    assert (rest = []) as -> by (destruct rest; [reflexivity|discriminate Hlen]).
    assert (Hl : overwrite (hello_diagnostic_pieces ++ byte_ps 5120 0 [a;b;c;d]) (heap opened) !!
      PByte 5120 3 = Some (VByte d)).
    { apply overwrite_owned; [exact Hdup|]. apply elem_of_app. right.
      change ((PByte 5120 3,VByte d) ∈ [(PByte 5120 0,VByte a); (PByte 5120 1,VByte b);
        (PByte 5120 2,VByte c); (PByte 5120 3,VByte d)]).
      do 3 (apply elem_of_cons; right). apply elem_of_cons. left. reflexivity. }
    destruct (Hag _ _ Hl) as [_ Hbyte].
    destruct (Hbyte (mkRegion 5120 5128 Heap Live) eq_refl eq_refl) as (_ & _ & Hvalue).
    change (1 = d) in Hvalue. rewrite Hvalue. exact Hl.
  - intros l v Hin. apply overwrite_owned; [exact Hdup|]. apply elem_of_app. left. exact Hin.
Qed.

Example overlapping_key_rejected :
  ~ (forall l v, (l,v) ∈ [(PByte 5120 3,VByte 0)] -> l ∉ errno_keys 5120 0).
Proof.
  intros H. apply (H (PByte 5120 3) (VByte 0)).
  - apply elem_of_cons. left. reflexivity.
  - change (PByte 5120 3 ∈ [PByte 5120 0; PByte 5120 1; PByte 5120 2; PByte 5120 3]).
    do 3 (apply elem_of_cons; right). apply elem_of_cons. left. reflexivity.
Qed.

Global Instance stable : SafepointStable wi.
Proof. constructor. intros s m s' m' w h [-> ->] Hw. exact Hw. Qed.

Definition registry : name -> option (contract libc_world) := fun _ => Some spec.
Definition ge := Reach.hello_genv [].
Definition stub := HelloCallbackChecks.stub.
Definition entry_env := [(TAtom "errnum", WInt 0)].

Lemma compatible : forall args words s m w tr vs s' m' w' h ys,
  H.M.E.invoke spec CVoid args words s m w tr (CallReturn vs) s' m' w' ->
  wi m w h -> length ys = 4%nat ->
  libc_diagnostic_wi (fun _ _ => True) native T.out T.err 5120 0 m' w'
    (overwrite (hello_diagnostic_pieces ++ byte_ps 5120 0 ys) h) ->
  wi m' w' (overwrite (hello_diagnostic_pieces ++ byte_ps 5120 0 ys) h).
Proof.
  intros args ws s m w tr vs s' m' w' h ys Hi _ _ Hw. split; [exact Hw|].
  destruct (H.D.error_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as [_ [born Hp]].
  destruct (proj2 Hp) as [Hfmt _].
  destruct Hfmt as (status & errnum & fmt & rest & text & body & info & info' &
    segments & pieces & actions & Hxs & Hstring & Hformat & Hsegments & Hpieces & Hinfo &
    Hopen & Hid & Hid' & Hrun & Haccepted & Hflush & Hready & Hrest).
  exact (proj1 Hready).
Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

Example diagnostic_then_return :
  pts hello_diagnostic_pieces -∗ pts (byte_ps 5120 0 [0;0;0;0]) -∗
  WP (ERun (mkFrame stub entry_env [] None (Exec (TAtom "body")
    [Call CVoid (Global (TAtom "error"))
      [Arg W (Const 0); Arg W (Tmp (TAtom "errnum"));
       Arg P (Global (TAtom "closeout#str.55")); Arg P (Global (TAtom "closeout#str.53"))]]
    (JRet (Const 0)))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ ys, ⌜result = Ret (WInt 0) /\ length ys = 4%nat⌝ ∗
      pts hello_diagnostic_pieces ∗ pts (byte_ps 5120 0 ys) }}.
Proof.
  iIntros "Hps He".
  iApply (H.wp_hello_error registry wi ge (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ _ => False) native T.out T.err 5120 0
    stub entry_env [] (TAtom "body") (Tmp (TAtom "errnum"))
    (Global (TAtom "closeout#str.55")) (Global (TAtom "closeout#str.53")) []
    (JRet (Const 0)) 0 [0;0;0;0] _ with "Hps He []").
  - intros m w h [Hwi Hnative]. split; [exact Hwi|]. split; [exact Hnative|].
    split; [constructor|exact Hnative].
  - exact compatible.
  - apply Reach.hello_genv_linked. intros s _. reflexivity.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - reflexivity.
  - iNext. iIntros (ys) "%Hlen Hps He".
    iApply (wp_ret registry wi ge stub entry_env (TAtom "body") (Const 0) W (WInt 0));
      [reflexivity|reflexivity|].
    iNext. iExists ys. iSplit.
    + iPureIntro. split; [reflexivity|exact Hlen].
    + iFrame "Hps He".
Qed.

End iris.

End HelloDiagnosticChecks.

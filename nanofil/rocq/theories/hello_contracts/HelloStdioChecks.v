(** These checks apply Hello's stream contracts to concrete close calls.
    They supply stream permissions and retain the caller's unrelated resources after each call. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run
  ExternalCalls LibcCalls ExternalMachine Stdio Shutdown Streams Formatting Libc LibcStreams LibcExit
  Pieces Heap ContractFrame Logic StringLogic LibcStringLogic LentLogic LibcStreamLogic LibcErrnoLogic
  LibcStreamTokens LibcStreamAdapter LibcDiagnosticLogic
  HelloModule HelloLeaf HelloVersion HelloClose HelloStdio.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
(** Exercise the Iris rule, not just its pure replacement map: an actual
    fclose call instruction returns closed-token and sampled-byte resources
    through the following return instruction, on the fixture's exact LG. *)
Module HelloCallbackChecks.
Module LG := StreamHandleChecks.LG.
Module H := HelloStdioOn InterpRuntime LG.
Module F := LibcStreamChecks.
Module T := StreamTokenChecks.
Import LG LG.L.

Definition close_wi := stream_tokens_wi (fun _ _ => True) T.out T.err 5120 0.
Definition registry : name -> option (contract libc_world) := fun _ => Some (fclose_contract F.model).
Definition ge := mkGenv [] [] (fun _ _ => None).
Definition stub := mkFunc (TAtom "close-control") (TAtom "local") (RClass W) [] [].
Definition entry_env := [(TAtom "p", WPtr (token_handle T.out))].

Global Instance close_stable : SafepointStable close_wi.
Proof.
  apply H.A.tokens_safepoint. intros s m s' m' w [-> ->] Hw. exact Hw.
Qed.

Example fixture_invoke_identity : @H.M.E.invoke = @T.A.M.E.invoke.
Proof. reflexivity. Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry close_wi ge.

(** Instantiate the entry wrapper itself, retaining separately owned
    errno. Freshness is true before allocation, not after it. *)
Example callback_entry_resources :
  gen_heap_interp HelloErrnoChecks.heap ∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) ==∗
    heap_interp close_wi (mkLstate conversion_mem InterpRuntime.start 64 (F.world true)) ∗
    pts (stream_ps T.out 7 [65; 66]) ∗ pts (stream_ps T.err 3 []) ∗
    pts (byte_ps 5120 0 [0; 0; 0; 0]).
Proof.
  iIntros "[Hh Herrno]".
  iMod (H.hello_callback_entry close_wi (fun _ _ => True) T.out T.err 5120 0
    (mkLstate conversion_mem InterpRuntime.start 64 (F.world true)) HelloErrnoChecks.heap
    7 [65; 66] 3 [] with "Hh") as "(Hσ & Ho & He)".
  - intros _ Hnew. exact Hnew.
  - exact HelloErrnoChecks.heap_agrees.
  - exact HelloErrnoChecks.disjoint.
  - exact HelloErrnoChecks.ready.
  - exact T.entry_wi.
  - exact T.entry_wi.
  - split; reflexivity.
  - split; reflexivity.
  - exists (mkStreamInfo 1 (mkStream ByteOriented [65; 66] true) 7). repeat split; reflexivity.
  - exists (mkStreamInfo 2 stdout_initial 3). repeat split; reflexivity.
  - exact T.entry_fresh.
  - iModIntro. iFrame.
Qed.

Example close_then_return_resources :
  pts (stream_ps T.out 7 [65; 66]) -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗
  WP (ERun (mkFrame stub entry_env [] None (Exec (TAtom "body")
    [Call (CResult (TAtom "r") W) (Global (TAtom "fclose")) [Arg P (Tmp (TAtom "p"))]]
    (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n ys, ⌜result = Ret (WInt n) /\ length ys = 4%nat⌝ ∗
      pts (closed_ps T.out) ∗ pts (byte_ps 5120 0 ys) }}.
Proof.
  iIntros "Ho Herrno".
  iApply (H.wp_hello_fclose registry close_wi ge (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ _ => False) T.out T.err 5120 0 T.out 7 [65; 66]
    [0; 0; 0; 0] stub entry_env [] (TAtom "body") (TAtom "r") (Tmp (TAtom "p")) []
    (JRet (Tmp (TAtom "r"))) _ with "Ho Herrno []").
  - intros m w h Hw. exact Hw.
  - intros s m w h tr vs s' m' w' ys Hi Hl Hw Hlen Hnew. exact Hnew.
  - left. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - iNext. iIntros (n ys) "%Hgood Ho Herrno". destruct Hgood as [Hn Hys].
    iApply (wp_ret registry close_wi ge stub _ (TAtom "body") (Tmp (TAtom "r")) W (WInt n));
      [reflexivity| |].
    + change (Some (WInt (n mod 2 ^ 32)) = Some (WInt n)).
      rewrite Z.mod_small; [reflexivity|exact Hn].
    + iNext. iExists n, ys. iFrame. auto.
Qed.

End iris.
End HelloCallbackChecks.

(** The open-only rule is exercised on the very same logic as the
    callback controls, with an inhabited paired interpretation. *)
Module HelloPermissionChecks.
Import HelloCallbackChecks.
Module P := StreamPermissionChecks.
Module T := StreamTokenChecks.
Module F := LibcStreamChecks.
Module LG := StreamHandleChecks.LG.
Import LG LG.L.

Definition close_wi := stream_tokens_wi (fun _ _ => True) P.out P.err 5120 0.
Definition registry := HelloCallbackChecks.registry.
Definition ge := HelloCallbackChecks.ge.
Definition stub := HelloCallbackChecks.stub.
Definition entry_env := HelloCallbackChecks.entry_env.

Global Instance close_stable : SafepointStable close_wi.
Proof.
  apply H.A.tokens_safepoint. intros s m s' m' w [-> ->] Hw. exact Hw.
Qed.

(** The real changed-errno call closes -4 and leaves stderr's open-only
    -5 permission, rather than manufacturing a fixed stderr snapshot. *)
Example permission_close_endpoint : forall n, n = 0 \/ n = stream_eof ->
  exists ys, length ys = 4%nat /\
    stream_tokens_wi (fun _ _ => True) P.out P.err 5120 0 T.changed_errno (F.world false)
      (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) /\
    (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) !! PName (-4) =
      Some (VStream (token_handle P.out) None) /\
    (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) !! PName (-5) =
      Some (VStreamOpen (token_handle P.err)) /\
    (overwrite (closed_ps P.out ++ byte_ps 5120 0 ys) P.heap) !! PByte 5120 3 = Some (VByte 1).
Proof.
  intros n Hn.
  destruct (H.permission_fclose_frame (fun _ _ => True) (fun _ _ _ _ => False)
    (fun _ _ _ _ _ => False) P.out P.err 5120 0 (token_handle P.out) [0; 0; 0; 0]
    CVoid [Arg P (Const 0)] InterpRuntime.start conversion_mem (F.world true) [] [WInt n]
    InterpRuntime.start T.changed_errno (F.world false) P.heap eq_refl P.heap_agrees
    HelloErrnoChecks.disjoint HelloErrnoChecks.ready P.full_wi)
      as (result & ys & Hresult & _ & Hlen & _ & Hag & _ & _ & Hw).
  - intros l v Hin. apply elem_of_app in Hin as [Hin|Hin].
    + change ((l, v) ∈ open_permission_ps P.out (token_handle P.out)) in Hin.
      unfold open_permission_ps in Hin. apply list_elem_of_In in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-.
      * unfold P.heap, StreamHandleChecks.heap.
        repeat (rewrite lookup_insert_ne; [|discriminate]). apply lookup_insert_eq.
      * unfold P.heap. apply lookup_insert_eq.
    + destruct (MemLogic.byte_ps_elem _ _ _ _ _ Hin) as (i & x & Hi & El & Ev). subst l v.
      unfold P.heap, StreamHandleChecks.heap.
      repeat (rewrite lookup_insert_ne; [|discriminate]).
      unfold HelloErrnoChecks.heap. apply elem_of_list_to_map_1; [|exact Hin].
      change (base.NoDup [PByte 5120 0; PByte 5120 1; PByte 5120 2; PByte 5120 3]).
      repeat (apply base.NoDup_cons_2; [set_solver|]). apply base.NoDup_nil_2.
  - exact (T.changed_close n Hn).
  - exists ys. split; [exact Hlen|]. split; [exact Hw|]. split.
    + rewrite overwrite_app. cbn [closed_ps overwrite P.out token_key token_base].
      rewrite lookup_insert_ne; [|discriminate]. apply lookup_insert_eq.
    + split.
      * rewrite overwrite_app. cbn [closed_ps overwrite P.out token_key token_base].
        rewrite lookup_insert_ne; [|discriminate]. rewrite lookup_insert_ne; [|discriminate].
        rewrite overwrite_out.
        -- unfold P.heap. rewrite lookup_insert_ne; [|discriminate]. apply lookup_insert_eq.
        -- rewrite byte_ps_keys. intros Hin. apply list_elem_of_fmap in Hin as (i & E & _). discriminate E.
      * destruct ys as [|a [|b [|c [|d rest]]]]; try discriminate Hlen.
        assert (rest = []) as -> by (destruct rest; [reflexivity|discriminate Hlen]).
        assert (Hl : (overwrite (closed_ps P.out ++ byte_ps 5120 0 [a; b; c; d]) P.heap) !!
          PByte 5120 3 = Some (VByte d)).
        { rewrite overwrite_app. cbn [closed_ps byte_ps overwrite].
          repeat (rewrite lookup_insert_ne; [|discriminate]). apply lookup_insert_eq. }
        destruct (Hag _ _ Hl) as [_ Hvalue].
        destruct (Hvalue (mkRegion 5120 5128 Heap Live) eq_refl eq_refl) as (_ & _ & Hv).
        change (1 = d) in Hv. rewrite Hv. exact Hl.
Qed.

Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Local Instance test_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry close_wi ge.

Example permission_close_then_return :
  pts (permission_ps P.out P.err (token_handle P.out)) -∗ pts (byte_ps 5120 0 [0; 0; 0; 0]) -∗
  WP (ERun (mkFrame stub entry_env [] None (Exec (TAtom "body")
    [Call (CResult (TAtom "r") W) (Global (TAtom "fclose")) [Arg P (Tmp (TAtom "p"))]]
    (JRet (Tmp (TAtom "r"))))) : language.expr (nanofil_lang registry ge))
  {{ result, ∃ n ys, ⌜result = Ret (WInt n) /\ length ys = 4%nat⌝ ∗
      pts (closed_ps P.out) ∗ pts (byte_ps 5120 0 ys) }}.
Proof.
  iIntros "Ho Herrno".
  iApply (H.wp_permission_fclose registry close_wi ge (fun _ _ => True)
    (fun _ _ _ _ => False) (fun _ _ _ _ _ => False) P.out P.err 5120 0 (token_handle P.out)
    [0; 0; 0; 0] stub entry_env [] (TAtom "body") (TAtom "r") (Tmp (TAtom "p")) []
    (JRet (Tmp (TAtom "r"))) _ with "Ho Herrno []").
  - intros m w h Hw. exact Hw.
  - intros s m w h tr vs s' m' w' ys Hi Hl Hw Hlen Hnew. exact Hnew.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - iNext. iIntros (n ys) "%Hgood Ho Herrno". destruct Hgood as [Hn Hys].
    iApply (wp_ret registry close_wi ge stub _ (TAtom "body") (Tmp (TAtom "r")) W (WInt n));
      [reflexivity| |].
    + change (Some (WInt (n mod 2 ^ 32)) = Some (WInt n)).
      rewrite Z.mod_small; [reflexivity|exact Hn].
    + iNext. iExists n, ys. iFrame. auto.
Qed.

End iris.
End HelloPermissionChecks.

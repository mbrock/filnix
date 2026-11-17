(** C functions often call another function before returning to their caller.
    A proof can use what is already known about each callee instead of repeating
    its execution. The tactics in this file apply those contracts and preserve
    the caller's memory. They leave unsupported steps for the programmer to prove. *)
From iris.proofmode Require Import proofmode reduction.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules.
From Glibc Require Import GlibcTactics GlibcSym GlibcSymFunc GlibcSpec GlibcProgram OsWorld.
Import ListNotations Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Ltac sym_call_fresh base :=
  let old := iTypeOf constr:(INamed base) in
  lazymatch old with
  | None => constr:(base)
  | _ => let next := eval vm_compute in (String.append base "'") in sym_call_fresh next
  end.

Ltac sym_call_save ids :=
  lazymatch ids with
  | [] => constr:(tt)
  | ?n :: ?rest =>
      let ty := iTypeOf constr:(INamed n) in
      lazymatch ty with
      | Some (false, ?P) => let tail := sym_call_save rest in constr:((n, P, tail))
      | _ => fail "sym_call: expected spatial resource" n
      end
  end.

Ltac sym_call_matches P saved :=
  lazymatch saved with
  | tt => constr:(@nil string)
  | (?n, ?Q, ?tail) =>
      let rest := sym_call_matches P tail in
      lazymatch P with Q => constr:(n :: rest) | _ => constr:(rest) end
  end.

Ltac sym_call_pure H :=
  lazymatch type of H with
  | _ /\ _ =>
      let right := fresh "Hsym_fact" in destruct H as [H right];
      sym_call_pure H; sym_call_pure right
  | _ => idtac
  end.

Ltac sym_call_post H saved :=
  let ty := iTypeOf constr:(INamed H) in
  lazymatch ty with Some (_, ?P) =>
    let matches := sym_call_matches P saved in
    first [lazymatch matches with [?n] =>
             let old := iTypeOf constr:(INamed n) in
             lazymatch old with None => iRename H into n end
           end
    | let Q := lazymatch P with
        | fs_post ?s ?x ?r =>
            let spec := eval hnf in s in
            eval cbv beta iota zeta delta [fs_post] in (fs_post spec x r)
        | _ => constr:(P)
        end in
      lazymatch Q with
      | bi_exist ?body =>
          let x := fresh "sym_result" in iDestruct H as (x) H; sym_call_post H saved
      | (bi_sep ?A ?B) =>
          let left := sym_call_fresh constr:("Hsym_post") in
          let right := sym_call_fresh constr:("Hsym_tail") in
          let pat := eval vm_compute in (String.append "[" (String.append left (String.append " " (String.append right "]")))) in
          iDestruct H as pat; sym_call_post left saved; sym_call_post right saved
      | bi_pure ?fact =>
          let Hp := fresh "Hsym_post" in iDestruct H as %Hp; sym_call_pure Hp; try subst
      | _ => idtac "sym_call retained resource:" H
      end]
  end.

Ltac sym_call_resume :=
  iExists _; iSplit; [iPureIntro; reflexivity|]; iNext;
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].

Ltac sym_call_frame ids :=
  lazymatch ids with
  | [] => idtac
  | ?n :: ?rest => try iFrame n; sym_call_frame rest
  end.

Ltac sym_call_continue saved :=
  let v := fresh "sym_out" in
  let post := sym_call_fresh constr:("Hsym_post") in
  iIntros (v); iIntros post; sym_call_post post saved;
  first [sym_call_resume | idtac "sym_call stopped: unresolved outcome or resume"].

Ltac sym_call_apply names saved rule x :=
  let Hargs := fresh "Hsym_args" in
  let T := type of (rule x) in
  lazymatch T with ?E -> _ =>
    assert (Hargs : E);
    [cbn -[put]; try first [reflexivity | eassumption | vx]
    | let T := type of (rule x Hargs) in
      lazymatch T with ⊢ ?P -∗ ?K -∗ ?Q =>
        let Hcall := fresh "Hsym_call" in pose proof (rule x Hargs) as Hcall;
        let Happly := fresh "Hsym_apply" in
        pose proof (bi.wand_elim_r' P K Q
          ltac:(iIntros "HK HP"; iApply (Hcall with "HP HK"))) as Happly;
        iApply Happly; clear Hcall Happly Hargs; cbn [fs_pre];
        let ids := eval vm_compute in (String.words names) in sym_call_frame ids;
        first [iSplitR; [try iPureIntro; try sym_lia | sym_call_continue saved]
              | sym_call_continue saved]
      end]
  end.

(** A call consumes only the named resources and uses the callee's proved contract.
    Returned resources recover their names only when the match is unique. *)
Ltac sym_call names :=
  let ids := eval vm_compute in (String.words names) in
  let saved := sym_call_save ids in
  let rule := call_spec_rule in
  let T := type of rule in
  lazymatch T with forall x : ?B, _ =>
    let B' := eval hnf in B in
    lazymatch B' with
    | unit => sym_call_apply names saved rule constr:(tt)
    | sum ?A ?C =>
        first [let a := spec_inputs A in sym_call_apply names saved rule open_constr:(inl a)
              |let c := spec_inputs C in sym_call_apply names saved rule open_constr:(inr c)]
    | _ => let x := spec_inputs B in sym_call_apply names saved rule x
    end
  end.

Ltac sym_ret_steps fuel :=
  lazymatch fuel with
  | O => fail "sym_ret: trailing-step fuel exhausted"
  | S ?rest =>
    lazymatch goal with
    | |- context [mkFrame _ _ [] None (Exec _ [] JRetVoid)] => iApply wp_ret_void; iNext
    | |- context [mkFrame _ _ [] None (Exec _ [] (JRet _))] =>
        iApply wp_ret; [reflexivity | vx | iNext]
    | |- context [mkFrame _ _ [] None (Exec _ (Let _ _ _ _ :: _) _)] => step; sym_ret_steps rest
    | |- context [mkFrame _ _ [] None (Exec _ (Flight _ _ _ _ :: _) _)] => step; sym_ret_steps rest
    end
  end.

(** A return may follow administrative instructions, but cannot cross a block boundary.
    The caller still proves the resulting postcondition. *)
Ltac sym_ret := sym_ret_steps constr:(64%nat).

Ltac sym_go_frame :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ ?fr) _) => constr:(fr)
  end.

Ltac sym_go_names ids :=
  lazymatch ids with
  | [] => constr:(EmptyString)
  | ?n :: ?rest =>
      let tail := sym_go_names rest in
      match goal with
      | _ => let ty := iTypeOf constr:(INamed n) in
             lazymatch ty with Some (false, ?P) =>
               let test := sym_quote_atom constr:(mkVal [] [] []) P in
               let joined := eval vm_compute in (String.append n (String.append " " tail)) in constr:(joined)
             end
      | _ => constr:(tail)
      end
  end.

Ltac sym_go_obligation :=
  lazymatch goal with
  | |- environments.envs_entails _ (fs_pre ?s ?x) =>
      let spec := eval hnf in s in
      let P := eval cbv beta iota zeta delta [fs_pre] in (fs_pre spec x) in
      idtac "sym_go missing precondition:" P
  | |- environments.envs_entails _ ?P => idtac "sym_go remaining obligation:" P
  | |- ?P => idtac "sym_go remaining obligation:" P
  end.

Ltac sym_go_loop names cuts fuel :=
  lazymatch fuel with
  | O => idtac "sym_go stopped: fuel exhausted"
  | S ?fuel' =>
    first [let before := sym_go_frame in
      first [lazymatch before with mkFrame _ _ _ _ (Enter ?lab _) =>
               let hit := eval vm_compute in (existsb (name_eqb lab) cuts) in
               constr_eq hit true; idtac "sym_go stopped: cut" lab
             end
      | sym_ret
      | progress (sym_call names);
        first [let after := sym_go_frame in
          first [constr_eq before after; idtac "sym_go stopped: no execution progress"
                | sym_go_loop names cuts fuel'] | sym_go_obligation]
      | let ids := eval vm_compute in (String.words names) in
        let selected := sym_go_names ids in
        sym_frun selected cuts;
        first [let after := sym_go_frame in
          first [constr_eq before after; idtac "sym_go stopped: no execution progress"
                | sym_go_loop names cuts fuel'] | sym_go_obligation]
      | idtac "sym_go stopped: unsupported instruction or missing spec"]
    | sym_go_obligation]
  end.

(** Execution alternates between symbolic runs, contract calls and returns.
    Cuts, unchanged frames and exhausted fuel stop the driver without discarding goals. *)
Ltac sym_go names cuts := sym_go_loop names cuts constr:(64%nat).

Section examples.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance call_example_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation expr := (language.expr (nanofil_lang registry ge)).

Definition sym_keep_spec (P : iProp Σ) (out : outcome) : fspec Σ :=
  FSpec unit (fun _ => []) (fun _ => P) (fun _ r => (⌜r = out⌝ ∗ P)%I).

Example sym_call_void (P : iProp Σ) g f e lab Φ
    (Hspec : HasSpec registry wi ge g (sym_keep_spec P RetVoid)) :
  P -∗ ▷ (P -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame f e [] None
    (Exec lab [Call CVoid (Global g) []] JRetVoid)) : expr) {{ Φ }}.
Proof using SafepointStable0.
  iIntros "HP HK". sym_call "HP". sym_ret. iApply ("HK" with "HP").
Qed.

Example sym_go_void (P : iProp Σ) g f e lab Φ
    (Hspec : HasSpec registry wi ge g (sym_keep_spec P RetVoid)) :
  P -∗ ▷ (P -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame f e [] None
    (Exec lab [Call CVoid (Global g) []; Call CVoid (Global g) []] JRetVoid)) : expr) {{ Φ }}.
Proof using SafepointStable0.
  iIntros "HP HK". sym_go "HP" (@nil name). iApply ("HK" with "HP").
Qed.

Example sym_call_unselected (P : iProp Σ) g f e lab Φ
    (Hspec : HasSpec registry wi ge g (sym_keep_spec P RetVoid)) :
  P -∗ ▷ (P -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame f e [] None
    (Exec lab [Call CVoid (Global g) []] JRetVoid)) : expr) {{ Φ }}.
Proof using SafepointStable0.
  iIntros "HP HK".
  assert_fails ltac:(solve [sym_go "" (@nil name); iApply ("HK" with "HP")]).
  sym_go "HP" (@nil name). iApply ("HK" with "HP").
Qed.

Example sym_call_ambiguous (P : iProp Σ) g f e lab Φ
    (Hspec : HasSpec registry wi ge g (sym_keep_spec (P ∗ P) RetVoid)) :
  P -∗ P -∗ ▷ (P ∗ P -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame f e [] None
    (Exec lab [Call CVoid (Global g) []] JRetVoid)) : expr) {{ Φ }}.
Proof using SafepointStable0.
  iIntros "HA HB HK". sym_go "HA HB" (@nil name). iApply "HK". iFrame.
Qed.

Definition sym_scalar_function : func :=
  mkFunc (TAtom "caller") (TAtom "local") (RClass W) [] [].

Example sym_go_scalar (P : iProp Σ) g e lab Φ
    (Hspec : HasSpec registry wi ge g (sym_keep_spec P (Ret (WInt 37)))) :
  P -∗ ▷ (P -∗ Φ (Ret (WInt 37))) -∗
  WP (ERun (mkFrame sym_scalar_function e [] None
    (Exec lab [Call (CResult (TAtom "answer") W) (Global g) []]
      (JRet (Tmp (TAtom "answer"))))) : expr) {{ Φ }}.
Proof using SafepointStable0.
  iIntros "HP HK". sym_go "HP" (@nil name). iApply ("HK" with "HP").
Qed.

Example sym_call_exists (P : iProp Σ) g e lab Φ
    (Hspec : HasSpec registry wi ge g
      (FSpec unit (fun _ => []) (fun _ => P)
        (fun _ r => (∃ n : Z, ⌜r = Ret (WInt n) /\ n = 37⌝ ∗ P)%I))) :
  P -∗ ▷ (P -∗ Φ (Ret (WInt 37))) -∗
  WP (ERun (mkFrame sym_scalar_function e [] None
    (Exec lab [Call (CResult (TAtom "answer") W) (Global g) []]
      (JRet (Tmp (TAtom "answer"))))) : expr) {{ Φ }}.
Proof using SafepointStable0.
  iIntros "HP HK". sym_call "HP". sym_ret. iApply ("HK" with "HP").
Qed.

Example sym_go_cut f e Φ :
  WP (ERun (mkFrame f e [] None (Enter (TAtom "cut") None)) : expr) {{ Φ }} -∗
  WP (ERun (mkFrame f e [] None (Enter (TAtom "cut") None)) : expr) {{ Φ }}.
Proof using Type.
  iIntros "HK". sym_go "" [TAtom "cut"]. iExact "HK".
Qed.

Example sym_go_unsupported Φ :
  WP (ERun (mkFrame sym_scalar_function [] [] None
    (Exec (TAtom "entry") [] JUnreachable)) : expr) {{ Φ }} -∗
  WP (ERun (mkFrame sym_scalar_function [] [] None
    (Exec (TAtom "entry") [] JUnreachable)) : expr) {{ Φ }}.
Proof using SafepointStable0.
  iIntros "HK". sym_go "" (@nil name). iExact "HK".
Qed.

Example sym_go_fuel f e lab Φ :
  WP (ERun (mkFrame f e [] None (Exec lab [] JRetVoid)) : expr) {{ Φ }} -∗
  WP (ERun (mkFrame f e [] None (Exec lab [] JRetVoid)) : expr) {{ Φ }}.
Proof using Type.
  iIntros "HK". sym_go_loop "" (@nil name) O. iExact "HK".
Qed.

End examples.

Section instance_example.
Import ProgramAbbreviations.
Context `{program : !GlibcProgram (hlc := hlc) Σ}.
Context (P : iProp Σ).
Context (Htriple : fn_triple registry (os_wi w0) ge (TAtom "sym_example") [] P
  (fun r => (⌜r = RetVoid⌝ ∗ P)%I)).
Local Instance sym_example_spec :
  HasSpec registry (os_wi w0) ge (TAtom "sym_example") (sym_keep_spec P RetVoid).
Proof using Type*. intros []. exact Htriple. Qed.

(** Instance search also finds a registered contract that was not posed as a hypothesis. *)
Example sym_go_instance f e lab Φ :
  P -∗ ▷ (P -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame f e [] None
    (Exec lab [Call CVoid (Global (TAtom "sym_example")) []] JRetVoid)) :
    language.expr (nanofil_lang registry ge)) {{ Φ }}.
Proof using Type*.
  iIntros "HP HK". sym_go "HP" (@nil name). iApply ("HK" with "HP").
Qed.
End instance_example.

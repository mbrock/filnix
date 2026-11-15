(** A layout check that accepted any address or region would let a proof
    place Hello's objects where the loader never put them.
    HelloImageLayout.v checks one choice of objects against the loaded
    image, so this file gives the same checks wrong choices and shows
    that each is refused.

    The check refuses four wrong choices of objects and two wrong
    initialized words, and it still accepts the real pointer to
    close_stdout. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith Bool.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run.
From Glibc Require Import HelloGetoptTable HelloImageEraseMem HelloImageCode HelloImageStart HelloImageLayout.
Import ListNotations.
Open Scope Z_scope.

Local Instance region_eq_dec : EqDecision region.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality; try apply Z.eq_dec; decide equality. Defined.

Local Instance cap_eq_dec : EqDecision cap.
Proof.
  intros x y. change ({x = y} + {x <> y}). decide equality; try apply Z.eq_dec.
  destruct (term_eqb f f0) eqn:E;
    [left; apply term_eqb_eq; exact E | right; intros ->; rewrite term_eqb_refl in E; discriminate].
  destruct (term_eqb n n0) eqn:E;
    [left; apply term_eqb_eq; exact E | right; intros ->; rewrite term_eqb_refl in E; discriminate].
Defined.

(** A pointer passes the function check when calling through it is
    allowed. *)
Local Definition fn_check_ok (ge : genv) (p : ptr) : bool :=
  match function_check_res ge p with Some (RVal _) => true | _ => false end.

(** The first two choices move stdout or enlarge its region. The larger
    region still meets the bound of the layout record, so only the
    comparison with the loader's region catches it. The next two give
    close_stdout the wrong capability. *)
Lemma hello_image_layout_refused :
  option_map (fun gm =>
    (lookup_obj gm.1 "stdout" 93192,
     bool_decide (object_region 93184 (m_regions gm.2) = Some (gd 93184 93200)) && (93184 + 8 <=? 93200),
     lookup_obj gm.1 "close_stdout" 65568,
     fn_check_ok (mkGenv hello_image_module gm.1 (fun _ _ => None)) (mkPtr 65568 (Fn (TAtom "main"))),
     load_bytes gm.2 93184 8 =? 91504,
     bool_decide (m_aux gm.2 (91744 + 104) = Obj 91744),
     fn_check_ok (mkGenv hello_image_module gm.1 (fun _ _ => None)) (mkPtr 65568 (Fn (TAtom "close_stdout")))))
    (initial_memory hello_image_module) = Some (false, false, false, false, false, false, true).
Proof. vm_cast_no_check (eq_refl (Some (false, false, false, false, false, false, true))). Qed.

(** The contract of `c: init_cpu_features` in
    [CpuInitSpec](CpuInitSpec.v) speaks of eighteen global objects.
    A caller must say where each one lies: its address, and the
    region of memory that the loader gave it. The addresses differ
    from one linked program to the next, because each linker places
    the globals among different neighbours.

    This module finds the eighteen objects in a loaded program. It
    takes the symbols and the regions that the loader produced, and it
    returns the record that the contract asks for. It also checks
    what the contract requires of each object: the kind of pointer,
    the alignment and the size. A program whose globals fail a check
    gets no record. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics.
From Glibc Require Import CpuInitSpec.
Import ListNotations ProgramAbbreviations.
Open Scope Z_scope.

(** ## Finding one object

    A global object is found through its symbol. The symbol gives a
    pointer, and the address of the pointer names a region. These
    definitions look one object up and test it. *)

(** A writable global has a pointer that may write its object, and a
    read-only global has a pointer that may only read it. The flag ro
    says which of the two the caller expects at address b. *)
Definition cap_fits (ro : bool) (b : Z) (c : cap) : bool :=
  match c with
  | Obj b' => negb ro && (b' =? b)
  | Ro b' => ro && (b' =? b)
  | _ => false
  end.

(** The contract expects this pointer for an object at address b. It
    reads and writes the object, or it only reads it when ro is set. *)
Definition obj_ptr (ro : bool) (b : Z) : ptr := mkPtr b (if ro then Ro b else Obj b).

(** This function finds the global named n among the symbols g and the
    regions rs. It gives the address and the region when the pointer
    is of the expected kind, the address is a multiple of al, and the
    region has room for sz bytes. *)
Definition obj_in (g : list (name * ptr)) (rs : list region) (ro : bool) (al sz : Z) (n : string)
    : option (Z * region) :=
  match lookup (TAtom n) g with
  | Some p =>
      match object_region (ptr_addr p) rs with
      | Some reg =>
          if cap_fits ro (ptr_addr p) (ptr_cap p) && (ptr_addr p mod al =? 0) && (ptr_addr p + sz <=? r_end reg)
          then Some (ptr_addr p, reg) else None
      | None => None
      end
  | None => None
  end.

(** An object that is found has the expected pointer, alignment and
    room, and its region is the one that the loader registered. *)
Lemma obj_in_ok g rs ro al sz n b reg : obj_in g rs ro al sz n = Some (b, reg) ->
  lookup (TAtom n) g = Some (obj_ptr ro b) /\ b mod al = 0 /\ b + sz <= r_end reg /\
  object_region b rs = Some reg.
Proof.
  unfold obj_in. destruct (lookup (TAtom n) g) as [[a c]|]; [|discriminate]. cbn [ptr_addr ptr_cap].
  destruct (object_region a rs) as [r|] eqn:Er; [|discriminate].
  destruct (cap_fits ro a c && (a mod al =? 0) && (a + sz <=? r_end r)) eqn:E; [|discriminate].
  intros H. injection H as <- <-. apply andb_true_iff in E as [E Hsz]. apply andb_true_iff in E as [Hc Hal].
  apply Z.eqb_eq in Hal. apply Z.leb_le in Hsz. split; [|split; [exact Hal|split; [exact Hsz|exact Er]]].
  unfold obj_ptr. destruct c as [|b'|b'|f|e]; try discriminate Hc; cbn [cap_fits] in Hc;
    apply andb_true_iff in Hc as [Hro Hb]; apply Z.eqb_eq in Hb; subst b'; destruct ro; try discriminate Hro; reflexivity.
Qed.

(** ## Finding all eighteen

    The feature structure, the tunable table and the descriptor table
    are looked up by name. The fifteen small globals are looked up in
    the order of [icf_small_globals], and each must be as aligned as
    it is large. *)

Fixpoint smalls_in (g : list (name * ptr)) (rs : list region) (gs : list (string * Z))
    : option (list (Z * region)) :=
  match gs with
  | [] => Some []
  | x :: gs' =>
      match obj_in g rs false (snd x) (snd x) (fst x), smalls_in g rs gs' with
      | Some q, Some qs => Some (q :: qs)
      | _, _ => None
      end
  end.

(** This function builds the record of the contract from a loaded
    program. *)
Definition icf_objs_in (g : list (name * ptr)) (rs : list region) : option icf_objs :=
  match obj_in g rs false 8 528 "_dl_x86_cpu_features", obj_in g rs false 8 4896 "glibc_dl_tunables#tunable_list",
        obj_in g rs true 4 544 "glibc_libc_start#intel_02_known", smalls_in g rs icf_small_globals with
  | Some cf, Some tl, Some kn, Some sm =>
      Some {| icf_cf := fst cf; icf_cfreg := snd cf; icf_tl := fst tl; icf_tlreg := snd tl;
              icf_kn := fst kn; icf_knreg := snd kn; icf_small := sm |}
  | _, _, _, _ => None
  end.

(** A definition that computes the record of one program needs a
    value for the case that the search fails. This record is that
    value. It places every object at address 0 and lists no small
    global, so it never meets the premise of the contract. *)
Definition icf_no_objs : icf_objs :=
  {| icf_cf := 0; icf_cfreg := mkRegion 0 0 GlobalData Live; icf_tl := 0; icf_tlreg := mkRegion 0 0 GlobalData Live;
     icf_kn := 0; icf_knreg := mkRegion 0 0 GlobalData Live; icf_small := [] |}.

(** These are the eighteen objects of a record, each with its region. *)
Definition icf_regions (o : icf_objs) : list (Z * region) :=
  (icf_cf o, icf_cfreg o) :: (icf_tl o, icf_tlreg o) :: (icf_kn o, icf_knreg o) :: icf_small o.

(** Every small global that is found has the expected pointer, is
    aligned and fits in its region, and that region is the one that
    the loader registered. *)
Lemma smalls_in_ok g rs : forall gs qs, smalls_in g rs gs = Some qs ->
  Forall2 (fun x q => lookup (TAtom (fst x)) g = Some (mkPtr (fst q) (Obj (fst q))) /\
                      fst q mod snd x = 0 /\ fst q + snd x <= r_end (snd q)) gs qs /\
  Forall (fun q => object_region (fst q) rs = Some (snd q)) qs.
Proof.
  induction gs as [|x gs IH]; intros qs H; cbn [smalls_in] in H.
  - injection H as <-. split; constructor.
  - destruct (obj_in g rs false (snd x) (snd x) (fst x)) as [[b reg]|] eqn:E; [|discriminate].
    destruct (smalls_in g rs gs) as [qs'|]; [|discriminate]. injection H as <-.
    destruct (obj_in_ok _ _ _ _ _ _ _ _ E) as (Hl & Hal & Hsz & Hr). destruct (IH qs' eq_refl) as [H2 Hrs].
    split; constructor; try assumption. cbn [fst snd]. split; [exact Hl|split; assumption].
Qed.

Section place.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Before a call, the contract asks that each global lies where the
    record says, is aligned, and fits in its region. A record that
    the search returns has all of that, because the search tested
    each object. *)
Lemma icf_objs_in_ok rs o : icf_objs_in (ge_globals ge) rs = Some o -> icf_ok o.
Proof using Type.
  unfold icf_objs_in.
  destruct (obj_in (ge_globals ge) rs false 8 528 "_dl_x86_cpu_features") as [[cf cfr]|] eqn:E1; [|discriminate].
  destruct (obj_in (ge_globals ge) rs false 8 4896 "glibc_dl_tunables#tunable_list") as [[tl tlr]|] eqn:E2;
    [|discriminate].
  destruct (obj_in (ge_globals ge) rs true 4 544 "glibc_libc_start#intel_02_known") as [[kn knr]|] eqn:E3;
    [|discriminate].
  destruct (smalls_in (ge_globals ge) rs icf_small_globals) as [sm|] eqn:E4; [|discriminate].
  intros H. injection H as <-.
  destruct (obj_in_ok _ _ _ _ _ _ _ _ E1) as (L1 & A1 & S1 & _).
  destruct (obj_in_ok _ _ _ _ _ _ _ _ E2) as (L2 & A2 & S2 & _).
  destruct (obj_in_ok _ _ _ _ _ _ _ _ E3) as (L3 & A3 & S3 & _).
  destruct (smalls_in_ok _ _ _ _ E4) as [H4 _].
  unfold icf_ok. cbn [icf_cf icf_cfreg icf_tl icf_tlreg icf_kn icf_knreg icf_small fst snd].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  split; [exact A1|]. split; [exact S1|]. split; [exact A2|]. split; [exact S2|].
  split; [exact A3|]. split; [exact S3|]. exact H4.
Qed.

End place.

(** Each region of the record is the one that the loader registered
    for the object, so a caller that owns the lifetimes of the
    loaded objects owns the lifetimes that the contract asks for. *)
Lemma icf_objs_in_regions g rs o : icf_objs_in g rs = Some o ->
  Forall (fun q => object_region (fst q) rs = Some (snd q)) (icf_regions o).
Proof.
  unfold icf_objs_in.
  destruct (obj_in g rs false 8 528 "_dl_x86_cpu_features") as [[cf cfr]|] eqn:E1; [|discriminate].
  destruct (obj_in g rs false 8 4896 "glibc_dl_tunables#tunable_list") as [[tl tlr]|] eqn:E2; [|discriminate].
  destruct (obj_in g rs true 4 544 "glibc_libc_start#intel_02_known") as [[kn knr]|] eqn:E3; [|discriminate].
  destruct (smalls_in g rs icf_small_globals) as [sm|] eqn:E4; [|discriminate].
  intros H. injection H as <-.
  destruct (obj_in_ok _ _ _ _ _ _ _ _ E1) as (_ & _ & _ & R1).
  destruct (obj_in_ok _ _ _ _ _ _ _ _ E2) as (_ & _ & _ & R2).
  destruct (obj_in_ok _ _ _ _ _ _ _ _ E3) as (_ & _ & _ & R3).
  destruct (smalls_in_ok _ _ _ _ E4) as [_ H4].
  unfold icf_regions. cbn [icf_cf icf_cfreg icf_tl icf_tlreg icf_kn icf_knreg icf_small fst snd].
  constructor; [exact R1|]. constructor; [exact R2|]. constructor; [exact R3|]. exact H4.
Qed.

(** Cryptographic code must not leak secret keys or plaintext through
    secret-dependent memory addresses or conditional branches. The C
    program `rocq/spikes/sbox.c` implements the 256-byte FIPS-197 AES
    S-box table alongside two functions that compute
    `SubBytes(AddRoundKey)` on 16-byte blocks (`SboxCode.v`).

    The fast version `subbytes_table` indexes the S-box directly with
    each secret byte, leaking the index through the data-cache line and
    through Fil-C's bounds check. The constant-time version
    `subbytes_ct` scans all 256 entries using an arithmetic mask so
    every branch, bounds check, and memory address stays independent of
    secret data.

    This spike exercises both functions under the [[poison]] semantics
    of `Poison.v` (`docs/poison.md`). It decodes the compiled module,
    runs Campaign 1's [[validator]], and lays out the read-only S-box
    table in memory.

    To test leak detection, the spike reproduces four poison verdicts on
    `subbytes_table`. It then lifts a single poisoned run of
    `subbytes_ct` via [prun_ct_sound] to prove universal constant-time
    noninterference across all pairs of 16-byte inputs and round keys,
    and checks both functions against the FIPS-197 Appendix B Round-1
    test vector. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Validate Memory Runtime Ops Semantics Run Transport.
From Spike Require Import SboxCode Poison.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Module decoding, validation and initial memory

    Before running any taint or functional checks, we must turn the
    serialized compiler output into an executable IR module and confirm
    that it passes structural validation. This section decodes
    [sbox_term], validates it, lays out the global read-only S-box table
    in memory, and binds handles to both C functions. *)

(** This definition decodes the checked IR module from [sbox_term]. *)
Definition sbox_module : module :=
  match decode_module sbox_term with Some md => md | None => [] end.

(** Decoding the serialized fixture yields [sbox_module]. *)
Lemma sbox_decodes : decode_module sbox_term = Some sbox_module.
Proof. vm_compute. reflexivity. Qed.

(** Campaign 1's [[validator]] accepts [sbox_module]. *)
Theorem sbox_valid : valid sbox_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** This list holds the global addresses laid out for `subbytes_table`,
    `subbytes_ct`, and the 256-byte `sbox` table. *)
Definition sbox_globals : list (name * ptr) :=
  match initial_memory sbox_module with Some (g, _) => g | None => [] end.

(** The module starts with an initial memory containing the 256-byte
    read-only `sbox` table. *)
Definition sbox_mem : mem :=
  match initial_memory sbox_module with Some (_, m) => m | None => empty_mem end.

(** Laying out [sbox_module] succeeds and produces [sbox_globals] and
    [sbox_mem]. *)
Lemma sbox_initial : initial_memory sbox_module = Some (sbox_globals, sbox_mem).
Proof.
  assert (H : option_map (fun _ => tt) (initial_memory sbox_module) = Some tt)
    by (vm_compute; reflexivity).
  unfold sbox_globals, sbox_mem.
  destruct (initial_memory sbox_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** This global environment pairs [sbox_module] and its globals with the
    concrete allocator handler [free_res]. *)
Definition sbox_ge : genv := mkGenv sbox_module sbox_globals free_res.

(** This helper looks up a defined function by name in [sbox_module]. *)
Definition sbox_fn (n : string) : func :=
  match find_fn sbox_ge (TAtom n) with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") RVoid [] []
  end.

(** The module defines `subbytes_table` in the core subset. *)
Lemma sbox_find_table :
  find_fn sbox_ge (TAtom "subbytes_table") = Some (Defined (sbox_fn "subbytes_table")).
Proof. vm_compute. reflexivity. Qed.

(** The module also defines `subbytes_ct` in the core subset. *)
Lemma sbox_find_ct :
  find_fn sbox_ge (TAtom "subbytes_ct") = Some (Defined (sbox_fn "subbytes_ct")).
Proof. vm_compute. reflexivity. Qed.

(** ## Heap fixture for 16-byte `out`, `in` and `rk` blocks

    Both AES functions take three 16-byte buffers: a writable output
    buffer, a read-only plaintext block, and a read-only round key. This
    section places those three disjoint objects above the module's
    globals, constructs their initial memory and call frames, and sets
    up the [[shadow]] poison state for their bytes. *)

(** These constants pick three disjoint, 64-byte-aligned heap addresses
    above the module's globals. *)
Definition sbox_out_base : Z := 131072.
Definition sbox_in_base  : Z := 131136.
Definition sbox_rk_base  : Z := 131200.

(** These pointers attach a writable capability to `out` and read-only
    capabilities to `in` and `rk`. *)
Definition sbox_out_ptr : ptr := mkPtr sbox_out_base (Obj sbox_out_base).
Definition sbox_in_ptr  : ptr := mkPtr sbox_in_base  (Ro sbox_in_base).
Definition sbox_rk_ptr  : ptr := mkPtr sbox_rk_base  (Ro sbox_rk_base).

(** This helper extends any base memory with three live 16-byte objects
    holding zeroed `out` and byte streams for `in` and `rk`. *)
Definition sbox_heap_on (m0 : mem) (inp rk : Z -> Z) : mem :=
  let base_bytes := m_bytes m0 in
  mkMem
    (fun b =>
       if (sbox_in_base <=? b) && (b <? sbox_in_base + 16)
       then (inp (b - sbox_in_base)) mod 256
       else if (sbox_rk_base <=? b) && (b <? sbox_rk_base + 16)
       then (rk (b - sbox_rk_base)) mod 256
       else if (sbox_out_base <=? b) && (b <? sbox_out_base + 16)
       then 0
       else base_bytes b)
    (mkRegion sbox_out_base (sbox_out_base + 16) Heap Live ::
     mkRegion sbox_in_base  (sbox_in_base + 16)  Heap Live ::
     mkRegion sbox_rk_base  (sbox_rk_base + 16)  Heap Live ::
     m_regions m0)
    (m_aux m0).

(** This function builds the initial heap on top of [sbox_mem] with
    unsigned bytes masked modulo 256. *)
Definition sbox_heap (inp rk : Z -> Z) : mem := sbox_heap_on sbox_mem inp rk.

(** This helper constructs an entry configuration for function f over an
    arbitrary base memory and fuel budget. *)
Definition sbox_cfg_on (f : func) (m0 : mem) (fuel : Z) (inp rk : Z -> Z) : config :=
  mkConfig
    (mkFrame f
             [(TAtom "v0", WPtr sbox_out_ptr);
              (TAtom "v2", WPtr sbox_in_ptr);
              (TAtom "v4", WPtr sbox_rk_ptr)]
             [] None (Enter (TAtom "start") None))
    []
    (sbox_heap_on m0 inp rk)
    fuel.

(** This helper builds an entry configuration calling `fn_name` on
    [sbox_heap] with the given block-entry fuel. *)
Definition sbox_cfg (fn_name : string) (fuel : Z) (inp rk : Z -> Z) : config :=
  sbox_cfg_on (sbox_fn fn_name) sbox_mem fuel inp rk.

(** To test which operations leak secrets, the analysis marks the bytes
    of `in` and `rk` without tainting their buffer addresses. This
    shadow state assigns `t_in` and `t_rk` to those two 16-byte buffers
    while keeping all three pointer arguments public. *)
Definition sbox_pstate (t_in t_rk : taint) : pstate :=
  mkPState
    [(TAtom "v0", WTPtr taint_bot taint_bot);
     (TAtom "v2", WTPtr taint_bot taint_bot);
     (TAtom "v4", WTPtr taint_bot taint_bot)]
    []
    (poison_range
       (poison_range (fun _ => pb_clean) sbox_in_base 16 (pb_secret t_in))
       sbox_rk_base 16 (pb_secret t_rk))
    (fun _ => taint_bot).

(** ## Four verdicts on `subbytes_table`, matching native zegarmistrz

    A table-driven S-box leaks secrets both through the memory address of
    the lookup and through the bounds check that guards it. The four
    tests below vary the poison bits on `rk` and the branch-checking
    policy to confirm that our IR semantics reproduces every verdict of
    native `zegarmistrz`. *)

(** This constant stream supplies all-zero bytes as a concrete reference
    input. *)
Definition zero_bytes (_ : Z) : Z := 0.

(** A secret key used as an array index should pass the bounds check
    when only memory indexing is forbidden. Under [pol_strict] with `rk`
    carrying only index poison, `subbytes_table` passes Fil-C's bounds
    check at step 19 and traps at the raw load on step 20. *)
Theorem subbytes_table_check_passes_on_index_only :
  match prun pol_strict sbox_ge 19
             (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
             (sbox_pstate taint_bot taint_index) with
  | PNext _ _ => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Theorem subbytes_table_traps_cannot_index :
  prun pol_strict sbox_ge 20
       (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
       (sbox_pstate taint_bot taint_index) = PTrap CannotIndex.
Proof. vm_compute. reflexivity. Qed.

(** Branching on a secret key inside Fil-C's bounds check violates
    constant-time discipline even before the table load runs. With `rk`
    carrying only branch poison under [pol_strict], `subbytes_table`
    traps at step 19, matching native `zegarmistrz`. *)
Theorem subbytes_table_traps_cannot_branch :
  prun pol_strict sbox_ge 19
       (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
       (sbox_pstate taint_bot taint_branch) = PTrap CannotBranch.
Proof. vm_compute. reflexivity. Qed.

(** If bounds checks are statically erased under [pol_erased],
    branch-only poison misses the secret table index and all 16
    iterations finish cleanly. *)
Theorem subbytes_table_erased_branch_misses :
  prun pol_erased sbox_ge 500
       (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
       (sbox_pstate taint_bot taint_branch) = PDone RetVoid [].
Proof. vm_compute. reflexivity. Qed.

(** Under the same check-erased policy [pol_erased], index poison still
    catches the secret-indexed load at step 20 and raises
    [CannotIndex]. *)
Theorem subbytes_table_erased_index_traps :
  prun pol_erased sbox_ge 20
       (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
       (sbox_pstate taint_bot taint_index) = PTrap CannotIndex.
Proof. vm_compute. reflexivity. Qed.

(** ## Universal constant-time noninterference for `subbytes_ct`

    To show that `subbytes_ct` leaks no secret data on any input, we do
    not need to enumerate all 2^512 combinations of plaintext and key.
    Instead, we execute one all-zero run with every secret byte marked
    with full poison, then apply [prun_ct_sound] to prove that every
    other input pair emits the identical leakage trace. *)

(** These constants set the step budget and block-entry fuel above the
    61,815 transitions and 8,259 block entries needed by `subbytes_ct`. *)
Definition sbox_ct_steps : nat := Z.to_nat 65000.
Definition sbox_ct_fuel  : Z := 10000.

(** This helper builds the entry configuration of `subbytes_ct` for
    arbitrary plaintext and round-key streams. *)
Definition sbox_ct_cfg (inp rk : Z -> Z) : config :=
  sbox_cfg "subbytes_ct" sbox_ct_fuel inp rk.

(** This poison state marks every byte of both `in` and `rk` with
    [taint_all], forbidding secret branches, indexing, and variable-time
    ops. *)
Definition sbox_ct_ps : pstate := sbox_pstate taint_all taint_all.

(** Running `subbytes_ct` on all-zero bytes under [pol_strict] completes
    all 61,815 transitions cleanly without triggering any poison fault. *)
Theorem subbytes_ct_ref_runs :
  prun pol_strict sbox_ge sbox_ct_steps
       (sbox_ct_cfg zero_bytes zero_bytes) sbox_ct_ps = PDone RetVoid [].
Proof. vm_compute. reflexivity. Qed.

(** This definition captures the leakage trace produced by the
    all-zero reference run of `subbytes_ct`. *)
Definition sbox_ct_ref_trace : option (list leak_event) :=
  prun_trace pol_strict sbox_ge sbox_ct_steps
             (sbox_ct_cfg zero_bytes zero_bytes) sbox_ct_ps.

(** Any poisoned run that finishes with [PDone] produces a well-defined
    leakage trace without re-evaluating [prun_trace] by computation. *)
Lemma prun_pdone_trace : forall pol ge steps c ps o ots,
  prun pol ge steps c ps = PDone o ots ->
  exists tr, prun_trace pol ge steps c ps = Some tr.
Proof.
  intros pol ge steps.
  induction steps as [|n IH]; intros c ps o ots Hrun; cbn in *.
  - discriminate Hrun.
  - destruct (pstep pol ge c ps) as [c' ps' | o' ots' | | | ] eqn:Ep; try discriminate Hrun.
    + destruct (IH c' ps' o ots Hrun) as [rest Erest].
      rewrite Erest. eexists. reflexivity.
    + eexists. reflexivity.
Qed.

(** To lift the single reference trace to all inputs, every input pair
    must be indistinguishable outside the secret buffers. Any plaintext
    and round-key streams satisfy [ct_rel] against the all-zero
    reference because their memories differ only inside the two fully
    poisoned 16-byte regions. *)
Lemma sbox_cfg_on_rel : forall (f : func) (m0 : mem) (fuel : Z) (inp rk : Z -> Z),
  ct_rel (sbox_cfg_on f m0 fuel zero_bytes zero_bytes)
         (sbox_cfg_on f m0 fuel inp rk) sbox_ct_ps.
Proof.
  intros f m0 fuel inp rk.
  unfold ct_rel, sbox_cfg_on, sbox_heap_on, sbox_pstate, sbox_ct_ps; cbn.
  repeat split; auto.
  - intros x; unfold lookup, name_eqb; cbn -[term_eqb].
    destruct (term_eqb x (TAtom "v0")).
    + right; exists (WPtr sbox_out_ptr), (WPtr sbox_out_ptr), (WTPtr taint_bot taint_bot).
      cbn; repeat split; intros Hne; congruence.
    + destruct (term_eqb x (TAtom "v2")).
      * right; exists (WPtr sbox_in_ptr), (WPtr sbox_in_ptr), (WTPtr taint_bot taint_bot).
        cbn; repeat split; intros Hne; congruence.
      * destruct (term_eqb x (TAtom "v4")).
        -- right; exists (WPtr sbox_rk_ptr), (WPtr sbox_rk_ptr), (WTPtr taint_bot taint_bot).
           cbn; repeat split; intros Hne; congruence.
        -- left; split; reflexivity.
  - intros b Hne.
    unfold poison_range, sbox_rk_base, sbox_in_base, sbox_out_base in *; cbn in *.
    destruct ((131200 <=? b) && (b <? 131216)) eqn:Erk.
    + cbn. apply taint_join_all_r.
    + destruct ((131136 <=? b) && (b <? 131152)) eqn:Ein.
      * reflexivity.
      * exfalso; apply Hne; reflexivity.
  - intros b Hne; exfalso; apply Hne; reflexivity.
Qed.

Lemma sbox_ct_cfg_rel : forall (inp rk : Z -> Z),
  ct_rel (sbox_ct_cfg zero_bytes zero_bytes) (sbox_ct_cfg inp rk) sbox_ct_ps.
Proof.
  intros inp rk. exact (sbox_cfg_on_rel (sbox_fn "subbytes_ct") sbox_mem sbox_ct_fuel inp rk).
Qed.

(** Combining the single poisoned execution [subbytes_ct_ref_runs] with
    [prun_ct_sound] proves universal constant-time noninterference for
    `subbytes_ct`. Every pair of 16-byte plaintexts and round keys runs
    without trapping and emits the exact same leakage trace. *)
Theorem subbytes_ct_constant_time :
  exists tr,
    sbox_ct_ref_trace = Some tr /\
    forall (inp1 rk1 inp2 rk2 : Z -> Z),
      prun_trace pol_strict sbox_ge sbox_ct_steps (sbox_ct_cfg inp1 rk1) sbox_ct_ps = Some tr /\
      prun_trace pol_strict sbox_ge sbox_ct_steps (sbox_ct_cfg inp2 rk2) sbox_ct_ps = Some tr.
Proof.
  destruct (prun_pdone_trace _ _ _ _ _ _ _ subbytes_ct_ref_runs) as [tr Etr].
  exists tr; split; [exact Etr|].
  intros inp1 rk1 inp2 rk2; split.
  - exact (prun_ct_sound pol_strict sbox_ge sbox_ct_steps
             (sbox_ct_cfg zero_bytes zero_bytes) (sbox_ct_cfg inp1 rk1)
             sbox_ct_ps RetVoid [] tr
             eq_refl eq_refl (sbox_ct_cfg_rel inp1 rk1) (or_introl eq_refl)
             subbytes_ct_ref_runs Etr).
  - exact (prun_ct_sound pol_strict sbox_ge sbox_ct_steps
             (sbox_ct_cfg zero_bytes zero_bytes) (sbox_ct_cfg inp2 rk2)
             sbox_ct_ps RetVoid [] tr
             eq_refl eq_refl (sbox_ct_cfg_rel inp2 rk2) (or_introl eq_refl)
             subbytes_ct_ref_runs Etr).
Qed.

(** ## Functional check on the FIPS-197 Appendix B Round-1 vector

    Constant-time execution is useless if the masked scan computes the
    wrong bytes. This section runs both `subbytes_table` and
    `subbytes_ct` on the standard FIPS-197 Appendix B Round-1 vector to
    verify that they produce the expected AES state. *)

(** This list holds the FIPS-197 Appendix B 128-bit input block in
    decimal. *)
Definition fips197_in_list : list Z :=
  [50; 67; 246; 168; 136; 90; 48; 141;
   49; 49; 152; 162; 224; 55; 7; 52].

(** This list holds the FIPS-197 Appendix B 128-bit cipher key in
    decimal. *)
Definition fips197_rk_list : list Z :=
  [43; 126; 21; 22; 40; 174; 210; 166;
   171; 247; 21; 136; 9; 207; 79; 60].

(** This list holds the expected FIPS-197 Appendix B Round-1 output
    right after `SubBytes(AddRoundKey)`. *)
Definition fips197_subbytes_expected : list Z :=
  [212; 39; 17; 174; 224; 191; 152; 241;
   184; 180; 93; 229; 30; 65; 82; 48].

(** This helper turns a 16-byte list into a total byte stream. *)
Definition of_byte_list (xs : list Z) (i : Z) : Z :=
  nth (Z.to_nat i) xs 0.

(** This helper steps the concrete semantics up to n times and returns
    memory when the call finishes with `RetVoid`. *)
Fixpoint step_n (ge : genv) (n : nat) (c : config) : option mem :=
  match n with
  | O => None
  | S n' =>
      match step ge c with
      | Next c' => step_n ge n' c'
      | Done RetVoid => Some (c_mem c)
      | _ => None
      end
  end.

Definition read_16 (m : mem) (base : Z) : list Z :=
  map (fun k => m_bytes m (base + Z.of_nat k)) (seq 0 16).

(** Both `subbytes_table` and `subbytes_ct` produce the exact FIPS-197
    Appendix B Round-1 `SubBytes(AddRoundKey)` output block. *)
Theorem subbytes_table_fips197 :
  option_map (fun m => read_16 m sbox_out_base)
    (step_n sbox_ge 500
       (sbox_cfg "subbytes_table" 100
          (of_byte_list fips197_in_list) (of_byte_list fips197_rk_list))) =
  Some fips197_subbytes_expected.
Proof. vm_compute. reflexivity. Qed.

Theorem subbytes_ct_fips197 :
  option_map (fun m => read_16 m sbox_out_base)
    (step_n sbox_ge sbox_ct_steps
       (sbox_ct_cfg
          (of_byte_list fips197_in_list) (of_byte_list fips197_rk_list))) =
  Some fips197_subbytes_expected.
Proof. vm_compute. reflexivity. Qed.

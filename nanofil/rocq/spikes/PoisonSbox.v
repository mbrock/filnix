(** AES SubBytes(AddRoundKey) under Zegarmistrz's poison semantics:
    [SboxCode.v], compiled by `nanofil -O --inline=none` from
    `rocq/spikes/sbox.c` and checked current by `rocq/spikes/code.sh`,
    exercised and proved against [Poison.v] (docs/poison.md).

    `sbox.c` holds the 256-byte FIPS-197 AES S-box table and two
    functions with the same behavior on 16-byte blocks:

    - `subbytes_table(out, in, rk)` indexes `sbox[in[i] ^ rk[i]]`
      directly, leaking `in[i] ^ rk[i]` through both the data-cache
      line touched by [RawLoad] and, when Fil-C's bounds check is
      present, the branch inside [Check];
    - `subbytes_ct(out, in, rk)` scans all 256 entries with an
      arithmetic mask `-(unsigned int)(idx == (unsigned int)j)`, keeping
      every branch, bounds check and memory address independent of `in`
      and `rk`.

    This file proves:

    1. [sbox_module] decodes, passes Campaign 1's [[validator]]
       ([sbox_valid]), and lays out its global read-only `sbox` table
       ([sbox_initial]);
    2. on `subbytes_table`, poisoning `rk` with [taint_index] (`0x08`)
       under [pol_strict] passes Fil-C's [Check] and traps at [RawLoad]
       with `PTrap CannotIndex` ([subbytes_table_traps_cannot_index]),
       poisoning `rk` with [taint_branch] (`0x04`) traps one step
       earlier inside [Check] with `PTrap CannotBranch`
       ([subbytes_table_traps_cannot_branch]), and discharging checks
       under [pol_erased] lets branch-only poison miss the table lookup
       while index poison still catches it
       ([subbytes_table_erased_branch_misses],
       [subbytes_table_erased_index_traps]);
    3. on `subbytes_ct`, running **one** reference input (`0^16`,
       `0^16`) with both `in` and `rk` marked [taint_all] (`0x4C`)
       under [pol_strict] finishes cleanly ([subbytes_ct_ref_runs]),
       and [prun_ct_sound] lifts that single poisoned run to **every**
       pair of 16-byte inputs and round keys: all 2^512 pairs emit the
       exact same instruction-level leakage trace
       ([subbytes_ct_constant_time]) and finish without trapping;
    4. on the FIPS-197 Appendix B Round-1 test vector, `subbytes_ct`
       and `subbytes_table` both produce the expected 16-byte output
       state `[0xd4; 0x27; 0x11; 0xae; ...]` ([subbytes_ct_fips197]). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Validate Memory Runtime Ops Semantics Run Transport.
From Spike Require Import SboxCode Poison.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Module decoding, validation and initial memory *)

(** The checked module decoded from [sbox_term]. *)
Definition sbox_module : module :=
  match decode_module sbox_term with Some md => md | None => [] end.

(** [sbox_term] decodes to [sbox_module]. *)
Lemma sbox_decodes : decode_module sbox_term = Some sbox_module.
Proof. vm_compute. reflexivity. Qed.

(** Campaign 1's [[validator]] accepts [sbox_module]. *)
Theorem sbox_valid : valid sbox_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** The globals laid out by [initial_memory]: `subbytes_table`,
    `subbytes_ct` and the 256-byte read-only `sbox` table. *)
Definition sbox_globals : list (name * ptr) :=
  match initial_memory sbox_module with Some (g, _) => g | None => [] end.

(** The module's initial memory holding the 256-byte `sbox` table. *)
Definition sbox_mem : mem :=
  match initial_memory sbox_module with Some (_, m) => m | None => empty_mem end.

(** Laying out [sbox_module] succeeds. *)
Lemma sbox_initial : initial_memory sbox_module = Some (sbox_globals, sbox_mem).
Proof.
  assert (H : option_map (fun _ => tt) (initial_memory sbox_module) = Some tt)
    by (vm_compute; reflexivity).
  unfold sbox_globals, sbox_mem.
  destruct (initial_memory sbox_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The module's [genv] paired with [free_res]. *)
Definition sbox_ge : genv := mkGenv sbox_module sbox_globals free_res.

(** Named function lookup in [sbox_module]. *)
Definition sbox_fn (n : string) : func :=
  match find_fn sbox_ge (TAtom n) with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") RVoid [] []
  end.

(** `subbytes_table` is a defined core-subset function in [sbox_module]. *)
Lemma sbox_find_table :
  find_fn sbox_ge (TAtom "subbytes_table") = Some (Defined (sbox_fn "subbytes_table")).
Proof. vm_compute. reflexivity. Qed.

(** `subbytes_ct` is a defined core-subset function in [sbox_module]. *)
Lemma sbox_find_ct :
  find_fn sbox_ge (TAtom "subbytes_ct") = Some (Defined (sbox_fn "subbytes_ct")).
Proof. vm_compute. reflexivity. Qed.

(** ## Heap fixture for 16-byte `out`, `in` and `rk` blocks *)

(** Disjoint 64-byte-aligned heap bases above the module's globals
    (`[65536, 66000)`). *)
Definition sbox_out_base : Z := 131072.
Definition sbox_in_base  : Z := 131136.
Definition sbox_rk_base  : Z := 131200.

(** Capabilities for the three 16-byte blocks (`out` writable, `in` and
    `rk` read-only). *)
Definition sbox_out_ptr : ptr := mkPtr sbox_out_base (Obj sbox_out_base).
Definition sbox_in_ptr  : ptr := mkPtr sbox_in_base  (Ro sbox_in_base).
Definition sbox_rk_ptr  : ptr := mkPtr sbox_rk_base  (Ro sbox_rk_base).

(** Generic heap extension over any base memory [m0]. *)
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

(** Memory state extending [sbox_mem] with three live 16-byte objects
    holding zeroed `out` and byte streams `inp` and `rk` (masked to
    unsigned bytes `mod 256`). *)
Definition sbox_heap (inp rk : Z -> Z) : mem := sbox_heap_on sbox_mem inp rk.

(** Generic entry frame for any function [f] and base memory [m0]. *)
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

(** Entry frame calling `fn_name(out, in, rk)` on [sbox_heap inp rk]
    with [fuel] block-entry units. *)
Definition sbox_cfg (fn_name : string) (fuel : Z) (inp rk : Z -> Z) : config :=
  sbox_cfg_on (sbox_fn fn_name) sbox_mem fuel inp rk.

(** Shadow [pstate] where `out`, `in` and `rk` pointers themselves are
    public (`taint_bot`), the 16 bytes at [sbox_in_base] carry `t_in`,
    and the 16 bytes at [sbox_rk_base] carry `t_rk`. *)
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

(** ## Four verdicts on `subbytes_table`, matching native zegarmistrz *)

(** Zero byte stream used as the concrete reference input. *)
Definition zero_bytes (_ : Z) : Z := 0.

(** 1. With `rk` poisoned `cannot-index` only ([taint_index], `0x08`)
    under [pol_strict] (`pol_check_branches = true`), `subbytes_table`
    passes Fil-C's `Check` on `sbox + (in[0] ^ rk[0])` (step 19 reaches
    `PNext`) and faults at the very next instruction (`RawLoad`, step
    20) with `PTrap CannotIndex` — matching native `zegarmistrz`. *)
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

(** 2. With `rk` poisoned `cannot-branch` only ([taint_branch], `0x04`)
    under [pol_strict] (`pol_check_branches = true`), `subbytes_table`
    traps **one step earlier** (step 19), inside Fil-C's `Check` on
    `sbox + (in[0] ^ rk[0])`, with `PTrap CannotBranch` — matching
    native `zegarmistrz`'s `cmp + jb/ja` fault on the bounds check. *)
Theorem subbytes_table_traps_cannot_branch :
  prun pol_strict sbox_ge 19
       (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
       (sbox_pstate taint_bot taint_branch) = PTrap CannotBranch.
Proof. vm_compute. reflexivity. Qed.

(** 3. Once bounds checks are statically discharged ([pol_erased],
    `pol_check_branches = false`), `cannot-branch` alone (`0x04`)
    **misses** the pure table-index leak: all 16 iterations run to
    `PDone RetVoid []`. *)
Theorem subbytes_table_erased_branch_misses :
  prun pol_erased sbox_ge 500
       (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
       (sbox_pstate taint_bot taint_branch) = PDone RetVoid [].
Proof. vm_compute. reflexivity. Qed.

(** 4. Under the same check-erased policy [pol_erased], `cannot-index`
    ([taint_index], `0x08`) still catches the secret-indexed load at
    step 20 with `PTrap CannotIndex`. *)
Theorem subbytes_table_erased_index_traps :
  prun pol_erased sbox_ge 20
       (sbox_cfg "subbytes_table" 100 zero_bytes zero_bytes)
       (sbox_pstate taint_bot taint_index) = PTrap CannotIndex.
Proof. vm_compute. reflexivity. Qed.

(** ## Universal constant-time noninterference for `subbytes_ct` *)

(** Step budget and block-entry fuel for `subbytes_ct` (the 16 * 256
    scan finishes in 61,815 transitions and 8,259 block entries; both
    [prun] and [prun_trace] halt immediately on [PDone]). *)
Definition sbox_ct_steps : nat := Z.to_nat 65000.
Definition sbox_ct_fuel  : Z := 10000.

(** Configuration of `subbytes_ct` on arbitrary byte streams `inp` and
    `rk`. *)
Definition sbox_ct_cfg (inp rk : Z -> Z) : config :=
  sbox_cfg "subbytes_ct" sbox_ct_fuel inp rk.

(** Strictest poison state: both `in` and `rk` are marked [taint_all]
    (`0x4C` = `cannot_branch | cannot_index | cannot_var_time_op`). *)
Definition sbox_ct_ps : pstate := sbox_pstate taint_all taint_all.

(** One concrete poisoned execution on `(zero_bytes, zero_bytes)` under
    [pol_strict] (`VTEverything`, `pol_check_branches = true`) runs all
    61,815 steps cleanly to `PDone RetVoid []`. *)
Theorem subbytes_ct_ref_runs :
  prun pol_strict sbox_ge sbox_ct_steps
       (sbox_ct_cfg zero_bytes zero_bytes) sbox_ct_ps = PDone RetVoid [].
Proof. vm_compute. reflexivity. Qed.

(** Reference leakage trace of `subbytes_ct` on `(zero_bytes, zero_bytes)`. *)
Definition sbox_ct_ref_trace : option (list leak_event) :=
  prun_trace pol_strict sbox_ge sbox_ct_steps
             (sbox_ct_cfg zero_bytes zero_bytes) sbox_ct_ps.

(** Any run that terminates cleanly with [PDone] produces a well-defined
    [prun_trace] without re-running the trace in `vm_compute`. *)
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

(** Every choice of byte streams `(inp, rk)` stands in [ct_rel] to the
    reference `(zero_bytes, zero_bytes)` configuration under
    [sbox_ct_ps], because their memories differ only inside
    `[sbox_in_base, sbox_in_base + 16)` and
    `[sbox_rk_base, sbox_rk_base + 16)`, where every byte carries
    [taint_all]. *)
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

(** **Main spike theorem (`subbytes_ct_constant_time`)**: one concrete
    [taint_all] run ([subbytes_ct_ref_runs]) plus [prun_ct_sound]
    establishes **universal 2-run constant-time noninterference** across
    all pairs of 16-byte plaintexts and 16-byte round keys (`2^256 *
    2^256 = 2^512` input pairs): every input pair runs without any
    Fil-C trap or poison fault under [pol_strict] and emits the exact
    same sequence of leakage events! *)
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

(** ## Functional check on the FIPS-197 Appendix B Round-1 vector *)

(** FIPS-197 Appendix B 128-bit input block (`32 43 f6 a8 88 5a 30 8d
    31 31 98 a2 e0 37 07 34` in decimal). *)
Definition fips197_in_list : list Z :=
  [50; 67; 246; 168; 136; 90; 48; 141;
   49; 49; 152; 162; 224; 55; 7; 52].

(** FIPS-197 Appendix B 128-bit cipher key (`2b 7e 15 16 28 ae d2 a6
    ab f7 15 88 09 cf 4f 3c` in decimal). *)
Definition fips197_rk_list : list Z :=
  [43; 126; 21; 22; 40; 174; 210; 166;
   171; 247; 21; 136; 9; 207; 79; 60].

(** FIPS-197 Appendix B Round-1 state right after `SubBytes(AddRoundKey)`
    (`d4 27 11 ae e0 bf 98 f1 b8 b4 5d e5 1e 41 52 30` in decimal). *)
Definition fips197_subbytes_expected : list Z :=
  [212; 39; 17; 174; 224; 191; 152; 241;
   184; 180; 93; 229; 30; 65; 82; 48].

(** Byte stream backed by a 16-byte list. *)
Definition of_byte_list (xs : list Z) (i : Z) : Z :=
  nth (Z.to_nat i) xs 0.

(** Read 16 output bytes from `[sbox_out_base, sbox_out_base + 16)` in
    a finished [Semantics.step] run of [n] steps. *)
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

(** Both `subbytes_table` and `subbytes_ct` compute the exact FIPS-197
    Appendix B Round-1 `SubBytes(AddRoundKey)` output block! *)
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

(** This file states the library obligations that remain in GNU Hello's
    safety proof. Milestone M4 covers option parsing, narrow output and
    the close callback. Milestone M6 covers locale and wide-character
    conversion and output. The [HelloDebts] record gives each call a
    [[separation logic]] contract over the concrete OS world.

    These contracts describe the actual streams, strings and global
    cells used by the program. The remaining callees may also own private
    state. Whoever discharges the contracts chooses that state, and the
    initial heap must supply it. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic HelloName.
From Glibc Require Import OsBlocks OsWorld OsRegistry WordString FileInv SysWrappers AtexitLogic AllocLogic
  LibioLogic HelloGlibcProgCells HelloGlibcMainStreams HelloGlibcMainAlloc.
Import ListNotations.
Open Scope Z_scope.

(** The linked program supplies the stream, name, option, allocator and
    exit-state objects read by the proof. This record identifies their
    addresses and bounds without fixing a particular memory layout. *)
Record hello_objs : Type := mkHelloObjs {
  ho_out : ptr; ho_err : ptr; ho_in : ptr;
  ho_so : Z; ho_soreg : region; ho_se : Z; ho_sereg : region;
  ho_oa : Z; ho_oareg : region; ho_oi : Z; ho_oireg : region;
  ho_vb : Z; ho_vreg : region; ho_sb : Z; ho_sreg : region; ho_eb : Z; ho_ereg : region;
  ho_x : exit_objs; ho_el : Z; ho_elr : region; ho_cp : ptr; ho_fcp : ptr;
  ho_mp : Z; ho_mpreg : region; ho_tc : Z; ho_tcreg : region; ho_dm : Z; ho_dmreg : region;
  ho_pb : Z; ho_nb : Z; ho_nsb : Z; ho_preg : region; ho_nreg : region; ho_nsreg : region;
  ho_lp : ptr; ho_tp : ptr
}.

(** These symbols identify the literals passed by main to its callees. *)
Definition hello_lits : list string :=
  ["hello#str.54"; "hello#str.55"; "hello#str.56"; "hello#str.57"; "hello#str.58"; "hello#str.59";
   "hello#str.60"; "hello#str.61"; "hello#str.62"; "hello#str.63"; "hello#str.69";
   "hello#parse_options.longopts.64"; "hello#str.70"; "hello#str.71"; "hello#str.72"; "hello#str.73";
   "hello#str.74"; "hello#str.75"; "hello#str.76"; "hello#str.77"; "hello#str.78"; "hello#str.79";
   "hello#str.80"; "hello#str.81"; "hello#str.82"; "hello#str.83"]%string.

(** The entry contract names the globals read by main and records their
    cell bounds. These facts do not depend on a logic instance. *)
Record hello_layout (ge : genv) (o : hello_objs) : Prop := mkHelloLayout {
  hy_lits : forall s, In s hello_lits -> lookup (TAtom s) (ge_globals ge) = Some (sym_ptr ge s);
  hy_cp : lookup (TAtom "close_stdout") (ge_globals ge) = Some (ho_cp o);
  hy_so : lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr (ho_so o) (Obj (ho_so o)));
  hy_so_at : 0 <= ho_so o /\ ho_so o mod 8 = 0 /\ ho_so o + 8 <= r_end (ho_soreg o) /\ r_end (ho_soreg o) <= 2 ^ 48;
  hy_se : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr (ho_se o) (Obj (ho_se o)));
  hy_se_at : 0 <= ho_se o /\ ho_se o mod 8 = 0 /\ ho_se o + 8 <= r_end (ho_sereg o) /\ r_end (ho_sereg o) <= 2 ^ 48;
  hy_oa : lookup (TAtom "optarg") (ge_globals ge) = Some (mkPtr (ho_oa o) (Obj (ho_oa o)));
  hy_oa_at : 0 <= ho_oa o /\ ho_oa o mod 8 = 0 /\ ho_oa o + 8 <= r_end (ho_oareg o) /\ r_end (ho_oareg o) <= 2 ^ 48;
  hy_oi : lookup (TAtom "optind") (ge_globals ge) = Some (mkPtr (ho_oi o) (Obj (ho_oi o)));
  hy_oi_at : 0 <= ho_oi o /\ ho_oi o + 4 <= r_end (ho_oireg o) /\ r_end (ho_oireg o) <= 2 ^ 48;
  hy_pb : lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr (ho_pb o) (Obj (ho_pb o)));
  hy_pb_at : 0 <= ho_pb o /\ ho_pb o mod 8 = 0 /\ ho_pb o + 8 <= r_end (ho_preg o) /\ r_end (ho_preg o) <= 2 ^ 48;
  hy_eb_at : 0 < ho_eb o /\ ho_eb o + 4 <= r_end (ho_ereg o) /\ r_end (ho_ereg o) <= 2 ^ 48
}.

(** These literals form the help text printed by fputs. *)
Definition fputs_lits : list string :=
  ["hello#str.55"; "hello#str.56"; "hello#str.57"; "hello#str.58"; "hello#str.59"; "hello#str.60"]%string.

(** These literals name the authors printed by the version branch. *)
Definition author_lits : list string := ["hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"]%string.

(** A terminated wide string contains four zero bytes at a four-byte boundary. *)
Definition wide_terminated (ws : list Z) : Prop :=
  exists k, (4 * k + 4 <= length ws)%nat /\ take 4 (drop (4 * k) ws) = [0; 0; 0; 0].

(** The wide buffer requests n bytes with sixteen-byte alignment. *)
Definition wreq (n : Z) : alloc_req := heap_req 16 n.

(** These definitions share one [[runtime]] and logic instance. *)
Module HelloGlibcDebtsOn (R : Runtime) (LG0 : LogicSig R).
(** The flush interface supplies the concrete stream predicates needed at exit. *)
Module FB := HelloGlibcMainStreamsOn R LG0.
(** The resource namespace shares file ownership and OS preservation rules. *)
Module SW.
(** File ownership includes the thread cleanup fields. *)
Module FI := FileInvOn R LG0.
(** The OS interpretation supplies its safepoint rules. *)
Module OW := HelloGlibcWorldOn R LG0.
(** The step rules support checked reads of shared stream cells. *)
Module ST := LibioStepOn R LG0.
End SW.
(** The allocation interface supplies ownership of the idle tcache. *)
Module AL := HelloGlibcMainAllocOn R LG0.
Import FB SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI.

Section debts.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs).

(** [os_wi] w0 survives safepoints. *)
Local Instance debts_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance debts_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** The function bound to g takes arguments xs and runs from P to Q. *)
Definition fn_triple (g : name) (xs : list word) (P : iProp Σ) (Q : outcome -> iProp Σ) : Prop :=
  exists gf, find_fn ge g = Some (Defined gf) /\ is_Some (call_frame gf xs) /\
    forall fr Φ, call_frame gf xs = Some fr -> ⊢ P -∗ (∀ r, Q r -∗ Φ r) -∗ WP (ERun fr : gexpr) {{ Φ }}.

(** The caller resumes with the outcome established by the callee's contract. *)
Lemma wp_call_fn g xs P Q f e ls lab r args rest j Ψ :
  fn_triple g xs P Q -> map_option (arg_x ge e) args = Some xs ->
  P -∗ (∀ v, Q v -∗ ∃ cf', ⌜resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) v = Some cf'⌝ ∗
                          ▷ WP (ERun cf' : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros (gf & Hg & [fr Hfr] & Ht) Hx. iIntros "HP HK".
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ xs gf fr); [exact Hx | exact Hg | exact Hfr |]. iNext.
  iApply (Ht fr _ Hfr with "HP"). iIntros (v) "HQ". iApply ("HK" with "HQ").
Qed.

(** The pointer identifies a read-only string whose bytes need not be specified. *)
Definition str_ro (q : ptr) : iProp Σ := ∃ s, word_string DfracDiscarded q s.

(** A call argument may be an integer, null, a standard stream or a read-only string. *)
Definition arg_ro (x : word) : iProp Σ :=
  match x with
  | WPtr q => ⌜ptr_addr q = 0 \/ q = ho_out o \/ q = ho_err o⌝ ∨
              ∃ p s k, ⌜q = ptr_add p (Z.of_nat k) /\ (k <= length s)%nat⌝ ∗ word_string DfracDiscarded p s
  | _ => True
  end.

(** The thread owns the standard streams, their open-stream list,
    its cleanup fields and the bytes of errno. *)
Definition hello_stdio : iProp Σ :=
  file_inv (ho_vb o) (ow_self w0) (ho_out o) ∗ file_inv (ho_vb o) (ow_self w0) (ho_err o) ∗
  file_inv (ho_vb o) (ow_self w0) (ho_in o) ∗ io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗
  tcb_cleanup_inv (ow_self w0) ∗ errno_any (ho_eb o).

(** Calls share read-only ownership of the linked constants, stream
    pointers, errno lifetime, allocator prelude and program literals. *)
Definition hello_ro : iProp Σ :=
  vtables_ro ge (ho_vb o) (ho_vreg o) ∗ single_ro ge (ho_sb o) (ho_sreg o) ∗
  liveq DfracDiscarded (ho_so o) (ho_soreg o) ∗ pcellq DfracDiscarded (ho_so o) 0 (ho_out o) ∗
  liveq DfracDiscarded (ho_se o) (ho_sereg o) ∗ pcellq DfracDiscarded (ho_se o) 0 (ho_err o) ∗
  liveq DfracDiscarded (ho_eb o) (ho_ereg o) ∗
  AL.tcache_idle DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o) ∗
  word_string DfracDiscarded (ho_lp o) libs_bytes ∗ word_string DfracDiscarded (ho_tp o) lt_bytes ∗
  [∗ list] s ∈ hello_lits, str_ro (sym_ptr ge s).

(** [hello_ro] is persistent. *)
Global Instance hello_ro_persistent : Persistent hello_ro.
Proof. rewrite /hello_ro /str_ro /AL.tcache_idle /liveq /pcellq /icellq. apply _. Qed.

(** Final cleanup owns stdin as the only remaining open stream.
    Its output buffer is empty, and the thread still owns its cleanup fields. *)
Definition exit_io : iProp Σ :=
  single_ro ge (ho_sb o) (ho_sreg o) ∗ tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge [ho_in o] ∗
  [∗ list] g ∈ [ho_in o], stream_life g ∗ exit_stream false g.

(** The option globals hold the argument pointer a and the index i. *)
Definition getopt_cells (a : ptr) (i : Z) : iProp Σ :=
  live (ho_oa o) (ho_oareg o) ∗ pcell (ho_oa o) 0 a ∗ live (ho_oi o) (ho_oireg o) ∗ int_cell (ho_oi o) 0 i.

(** The aligned argv object holds the argument pointers followed by null.
    The argument count fits in a signed C integer. *)
Definition argv_own (av : Z) (ar : region) (ps : list ptr) : iProp Σ :=
  ⌜0 < av /\ av mod 8 = 0 /\ Z.of_nat (length ps) < 2 ^ 31 /\ av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar /\
   r_end ar <= 2 ^ 48⌝ ∗ live av ar ∗ [∗ list] k ↦ q ∈ ps ++ [null], pcell av (8 * Z.of_nat k) q.

(** The greeting object stores its string pointer in the first eight bytes. *)
Definition gcell (b4 : Z) (g : ptr) : iProp Σ :=
  live b4 (mkRegion b4 (b4 + 16) Heap Live) ∗ pcell b4 0 g ∗ bytes b4 8 (replicate 8 0) ∗
  auxes b4 1 (replicate 15 CNone).

(** The allocated wide buffer holds the byte sequence ws. *)
Definition wbuf (bd n : Z) (ws : list Z) : iProp Σ :=
  ∃ cs, ⌜length ws = Z.to_nat (req_extent (wreq n)) /\ length cs = length ws⌝ ∗
    live bd (mkRegion bd (bd + req_extent (wreq n)) Heap Live) ∗ bytes bd 0 ws ∗ auxes bd 0 cs.

(** Main prints help text to stdout and the usage hint to stderr. *)
Definition print_site (g : name) (xs : list word) : Prop :=
  (g = TAtom "fputs" /\ exists s, In s fputs_lits /\ xs = [WPtr (sym_ptr ge s); WPtr (ho_out o)]) \/
  (g = TAtom "fprintf" /\ exists q, xs = [WPtr (ho_out o); WPtr (sym_ptr ge "hello#str.54"); WPtr q]) \/
  (g = TAtom "fprintf" /\
     xs = [WPtr (ho_out o); WPtr (sym_ptr ge "hello#str.62"); WPtr (sym_ptr ge "hello#str.63")]) \/
  (g = TAtom "fprintf" /\ exists q, xs = [WPtr (ho_err o); WPtr (sym_ptr ge "hello#str.79"); WPtr q]).

(** An integer-returning call preserves the state P. *)
Definition ret_int (P : iProp Σ) (r : outcome) : iProp Σ := ∃ n, ⌜r = Ret (WInt n) /\ 0 <= n < 2 ^ 32⌝ ∗ P.

(** The three program-name globals hold the pointers x, y and z. *)
Definition ncells (x y z : ptr) : iProp Σ :=
  live (ho_pb o) (ho_preg o) ∗ pcell (ho_pb o) 0 x ∗ live (ho_nb o) (ho_nreg o) ∗ pcell (ho_nb o) 0 y ∗
  live (ho_nsb o) (ho_nsreg o) ∗ pcell (ho_nsb o) 0 z.

(** Error reporting reads three name cells that point to read-only strings. *)
Definition names : iProp Σ := ∃ x y z, ncells x y z ∗ str_ro x ∗ str_ro y ∗ str_ro z.

(** The remaining milestones must prove these call contracts while
    preserving the standard streams and the callees' private state.
    Milestone M6 covers locale queries, conversion and wide output.
    Milestone M4 covers the other calls, including the close callback.
    Fatal error reporting never returns. Error reporting and the close
    callback may read the program-name cells. *)
Record HelloDebts : Type := mkHelloDebts {
  hd_priv : iProp Σ;
  hd_setlocale_all :
    fn_triple (TAtom "setlocale") [WInt 6; WPtr (sym_ptr ge "hello#str.80")]
      (hello_ro ∗ hello_stdio ∗ hd_priv)%I (fun r => ∃ q, ⌜r = Ret (WPtr q)⌝ ∗ hello_stdio ∗ hd_priv)%I;
  hd_setlocale_query :
    fn_triple (TAtom "setlocale") [WInt 5; WPtr null]
      (hello_ro ∗ hello_stdio ∗ hd_priv)%I
      (fun r => ∃ q, ⌜r = Ret (WPtr q)⌝ ∗ hello_stdio ∗ hd_priv ∗ (⌜ptr_addr q = 0⌝ ∨ str_ro q))%I;
  hd_getopt : forall av ar ps a i,
    fn_triple (TAtom "getopt_long")
      [WInt (Z.of_nat (length ps)); WPtr (mkPtr av (Obj av)); WPtr (sym_ptr ge "hello#str.69");
       WPtr (sym_ptr ge "hello#parse_options.longopts.64"); WPtr null]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ argv_own av ar ps ∗ ([∗ list] q ∈ ps, str_ro q) ∗ getopt_cells a i)%I
      (fun r => ∃ code ps' a' i', ⌜r = Ret (WInt code) /\ 0 <= code < 2 ^ 32 /\ Permutation ps ps' /\
                                   0 <= i' <= Z.of_nat (length ps)⌝ ∗
                  hello_stdio ∗ hd_priv ∗ argv_own av ar ps' ∗ getopt_cells a' i' ∗
                  (if code =? 103 then str_ro a' else True))%I;
  hd_proper_name : forall s, In s author_lits ->
    fn_triple (TAtom "proper_name") [WPtr (sym_ptr ge s)] (hello_ro ∗ hello_stdio ∗ hd_priv)%I
      (fun r => ∃ q, ⌜r = Ret (WPtr q)⌝ ∗ hello_stdio ∗ hd_priv ∗ str_ro q)%I;
  hd_version_etc : forall q1 q2 q3 q4,
    fn_triple (TAtom "version_etc")
      [WPtr (ho_out o); WPtr (sym_ptr ge "hello#str.70"); WPtr (sym_ptr ge "hello#str.63");
       WPtr (sym_ptr ge "hello#str.71"); WPtr q1; WPtr q2; WPtr q3; WPtr q4; WPtr null]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ str_ro q1 ∗ str_ro q2 ∗ str_ro q3 ∗ str_ro q4)%I
      (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio ∗ hd_priv)%I;
  hd_print : forall g xs, print_site g xs ->
    fn_triple g xs (hello_ro ∗ hello_stdio ∗ hd_priv ∗ [∗ list] x ∈ xs, arg_ro x)%I
      (ret_int (hello_stdio ∗ hd_priv))%I;
  hd_emit_bug :
    fn_triple (TAtom "emit_bug_reporting_address") [] (hello_ro ∗ hello_stdio ∗ hd_priv)%I
      (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio ∗ hd_priv)%I;
  hd_error_operand : forall q,
    fn_triple (TAtom "error")
      [WInt 0; WInt 0; WPtr (sym_ptr ge "hello#str.77"); WPtr (sym_ptr ge "hello#str.78"); WPtr q]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ names ∗ arg_ro (WPtr q))%I
      (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio ∗ hd_priv ∗ names)%I;
  hd_error_conv : forall n,
    fn_triple (TAtom "error") [WInt 1; WInt n; WPtr (sym_ptr ge "hello#str.82")]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ names)%I (fun _ => False)%I;
  hd_mbsrtowcs : forall bd b4 b6 g gs,
    let n := 4 * (Z.of_nat (length gs) + 1) in
    fn_triple (TAtom "rpl_mbsrtowcs")
      [WPtr (mkPtr bd (Obj bd)); WPtr (mkPtr b4 (Obj b4)); WInt (Z.of_nat (length gs) + 1);
       WPtr (mkPtr b6 (Obj b6))]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ wbuf bd n (replicate (Z.to_nat (req_extent (wreq n))) 0) ∗
       gcell b4 g ∗ word_string DfracDiscarded g gs ∗ obj b6 (heap_req 4 8))%I
      (fun r => ∃ k ws, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 64 /\ (k <> 2 ^ 64 - 1 -> wide_terminated ws)⌝ ∗
                  hello_stdio ∗ hd_priv ∗ wbuf bd n ws)%I;
  hd_wprintf : forall bd n ws,
    wide_terminated ws ->
    fn_triple (TAtom "wprintf") [WPtr (sym_ptr ge "hello#str.83"); WPtr (mkPtr bd (Obj bd))]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ wbuf bd n ws)%I (ret_int (hello_stdio ∗ hd_priv ∗ wbuf bd n ws))%I;
  hd_close_stdout :
    fn_triple (TAtom "close_stdout") [] (hello_ro ∗ hello_stdio ∗ hd_priv ∗ names)%I
      (fun r => ⌜r = RetVoid⌝ ∗ exit_io)%I
}.

(** The concrete library bridges establish these call contracts.
    Registration changes the exit-handler state from X0 to X, and exit
    consumes X while invoking the close callback. HelloGlibcMainLibs.v
    constructs this record from the proved glibc implementations. *)
Record HelloLibs (priv X0 X : iProp Σ) : Prop := mkHelloLibs {
  hl_mbszero : forall b, 0 < b -> b mod 16 = 0 -> b + 16 <= 2 ^ 48 ->
    fn_triple (TAtom "mbszero") [WPtr (mkPtr b (Obj b))] (obj b (heap_req 4 8))
      (fun r => ⌜r = RetVoid⌝ ∗ obj b (heap_req 4 8))%I;
  hl_name : forall p s x y z,
    fn_triple (TAtom "set_program_name") [WPtr p] (hello_ro ∗ word_string DfracDiscarded p s ∗ ncells x y z)
      (fun r => ⌜r = RetVoid⌝ ∗ ncells (ptr_add p (Z.of_nat (name_idx s))) (ptr_add p (Z.of_nat (name_idx s)))
                  (ptr_add p (Z.of_nat (short_idx s))))%I;
  hl_atexit : fn_triple (TAtom "atexit") [WPtr (ho_cp o)] X0
    (fun r => ∃ k, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 32⌝ ∗ X)%I;
  hl_xmalloc : forall n, 0 <= n < 2 ^ 64 ->
    fn_triple (TAtom "xmalloc") [WInt n] hello_ro
      (fun r => ∃ b, ⌜r = Ret (WPtr (mkPtr b (Obj b))) /\ 0 < b /\ b mod 16 = 0 /\
                      b + req_extent (wreq n) <= 2 ^ 48⌝ ∗ obj b (wreq n))%I;
  hl_strlen : forall dq p s,
    fn_triple (TAtom "strlen") [WPtr p] (word_string dq p s)
      (fun r => ⌜r = Ret (WInt (Z.of_nat (length s)))⌝ ∗ word_string dq p s)%I;
  hl_strncmp : forall p1 p2 s1 s2,
    fn_triple (TAtom "strncmp") [WPtr p1; WPtr p2; WInt 3]
      (word_string DfracDiscarded p1 s1 ∗ word_string DfracDiscarded p2 s2)
      (fun r => ∃ k, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 32⌝)%I;
  hl_errno : fn_triple (TAtom "__errno_location") [] True
    (fun r => ⌜r = Ret (WPtr (mkPtr (ho_eb o) (Obj (ho_eb o))))⌝)%I;
  hl_free : forall b reg, r_kind reg = Heap -> b <> 0 ->
    fn_triple (TAtom "free") [WPtr (mkPtr b (Obj b))] (live b reg) (fun r => ⌜r = RetVoid⌝)%I;
  hl_exit : forall n,
    fn_triple (TAtom "exit") [WInt n] (hello_ro ∗ hello_stdio ∗ priv ∗ names ∗ X) (fun _ => False)%I
}.

End debts.
End HelloGlibcDebtsOn.

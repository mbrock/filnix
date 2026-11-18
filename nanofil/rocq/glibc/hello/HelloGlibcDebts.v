(** This file states the library obligations that remain in GNU Hello's
    safety proof. Milestone M4 covers option parsing, narrow output and
    the close callback. Milestone M6 covers locale and wide-character
    conversion and output. The [HelloCore] record gives each call a
    [[separation logic]] contract over the concrete OS world.

    These contracts describe the actual streams, strings and global
    cells used by the program. The remaining callees may also own private
    state. Whoever discharges the contracts chooses that state, and the
    initial heap must supply it. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic HelloName.
From Glibc Require Import OsBlocks OsWorld OsRegistry WordString FileInv FileIdle SysWrappers AtexitLogic AllocLogic
  LibioLogic HelloGlibcProgCells HelloGlibcMainStreams HelloGlibcMainAlloc HelloVersionLits PrintfSpec.
From Glibc Require FileInv LibioLogic.
From Glibc Require Import Fix.
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

(** These are the formats that main hands to glibc's formatter, each
    with its bytes before the terminating zero. *)
Definition print_fmts : list (string * list Z) :=
  [("hello#str.77", [37; 115; 58; 32; 37; 115]);
   ("hello#str.54", [85; 115; 97; 103; 101; 58; 32; 37; 115; 32; 91; 79; 80; 84; 73; 79; 78; 93; 46; 46; 46; 10]);
   ("hello#str.62",
    [82; 101; 112; 111; 114; 116; 32; 37; 115; 32; 116; 114; 97; 110; 115; 108; 97; 116; 105; 111; 110; 32; 98; 117; 103; 115; 32; 116; 111; 32; 60; 104; 116; 116; 112; 115; 58; 47; 47; 116; 114; 97; 110; 115; 108; 97; 116; 105; 111; 110; 112; 114; 111; 106; 101; 99; 116; 46; 111; 114; 103; 47; 116; 101; 97; 109; 47; 62; 10]);
   ("hello#str.79", [84; 114; 121; 32; 39; 37; 115; 32; 45; 45; 104; 101; 108; 112; 39; 32; 102; 111; 114; 32; 109; 111; 114; 101; 32; 105; 110; 102; 111; 114; 109; 97; 116; 105; 111; 110; 46; 10])]%string.

(** These literals name the authors printed by the version branch. *)
Definition author_lits : list string := ["hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"]%string.

(** A terminated wide string contains four zero bytes at a four-byte boundary. *)
Definition wide_terminated (ws : list Z) : Prop :=
  exists k, (4 * k + 4 <= length ws)%nat /\ take 4 (drop (4 * k) ws) = [0; 0; 0; 0].

(** The wide text that `c: mbsrtowcs` produces in the C locale is a
    run of wide characters, each four bytes, ended by a zero character.
    Gnulib's replacement maps every byte that the C locale rejects to
    its own value, so each character lies between 1 and 255. *)
Definition wide_text (ws : list Z) : Prop :=
  exists cs, Forall (fun c => 0 < c < 256) cs /\ (4 * length cs + 4 <= length ws)%nat /\
    take (4 * length cs + 4) ws = flat_map (fun c => [c; 0; 0; 0]) cs ++ [0; 0; 0; 0].

(** The wide buffer requests n bytes with sixteen-byte alignment. *)
Definition wreq (n : Z) : alloc_req := heap_req 16 n.


(** The flush interface supplies the concrete stream predicates needed at exit. *)
Module FB := HelloGlibcMainStreamsOn.
(** The resource namespace shares file ownership and OS preservation rules. *)
Module SW.
(** File ownership includes the thread cleanup fields. *)
Module FI := FileInv.
(** The OS interpretation supplies its safepoint rules. *)
Module OW := HelloGlibcWorldOn.
(** The step rules support checked reads of shared stream cells. *)
Module ST := LibioLogic.
End SW.
(** The allocation interface supplies ownership of the idle tcache. *)
Module AL := HelloGlibcMainAllocOn.
Import FB SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI.

Section debts.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs).

(** The proof rules need to know that the world invariant holds again
    after a safepoint. This instance says so for the invariant of the
    world w0. *)
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
Proof using Type.
  intros (gf & Hg & [fr Hfr] & Ht) Hx. iIntros "HP HK".
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ xs gf fr); [exact Hx | exact Hg | exact Hfr |]. iNext.
  iApply (Ht fr _ Hfr with "HP"). iIntros (v) "HQ". iApply ("HK" with "HQ").
Qed.

(** The pointer identifies a read-only string whose bytes need not be specified. *)
Definition str_ro (q : ptr) : iProp Σ := ∃ s, word_string DfracDiscarded q s.

(** glibc's `c: error` counts the errors it reports in the global
    `c: error_message_count`. Each report adds one, so the thread owns
    the cell at whatever count it holds. *)
Definition error_count : iProp Σ :=
  ∃ cb creg n, ⌜lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr cb (Obj cb)) /\
      cb mod 4 = 0 /\ cb + 4 <= r_end creg /\ r_end creg <= 2 ^ 63⌝ ∗
    live cb creg ∗ int_cell cb 0 n.

(** glibc's `c: error` prints the program name itself unless the
    global `c: error_print_progname` names a function to do it. Hello
    never sets that global, so it stays null and is read-only. *)
Definition error_progname_ro : iProp Σ :=
  ∃ pb preg, ⌜lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) /\
      pb mod 8 = 0 /\ pb + 8 <= r_end preg /\ r_end preg <= 2 ^ 63⌝ ∗
    liveq DfracDiscarded pb preg ∗ pcellq DfracDiscarded pb 0 null.

(** Main prints through four formats: `"%s: %s"` for an extra
    operand, the usage line, the translation-bugs line and the hint to
    try `--help`. The formatter's contract parses a format's bytes, so
    the read-only promise holds each of these strings with its exact
    bytes, and [print_fmts] lists them. *)
Definition print_fmt_ro : iProp Σ :=
  [∗ list] ns ∈ print_fmts, word_string DfracDiscarded (sym_ptr ge ns.1) ns.2.

(** The callback global is persistent. Stating the instance here keeps
    proof search from unfolding the program's globals. *)
Global Instance error_progname_ro_persistent : Persistent error_progname_ro.
Proof using Type. rewrite /error_progname_ro /liveq /pcellq. apply _. Qed.

(** Between two library calls, the thread owns the three standard
    streams and the list that links them. It also owns its cleanup
    fields, errno and the count of reported errors. Stdout and stderr
    are idle on descriptors 1 and 2. Hello never reads stdin, so stdin
    stays in the form that the exit path's cleanup reads. *)
Definition hello_stdio : iProp Σ :=
  file_idle (ho_vb o) (ow_self w0) (ho_out o) 1 ∗ file_idle (ho_vb o) (ow_self w0) (ho_err o) 2 ∗
  (stream_life (ho_in o) ∗ exit_stream false (ho_in o)) ∗ io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗
  tcb_cleanup_inv (ow_self w0) ∗ errno_any (ho_eb o) ∗ error_count.

(** Once a call orients stdout wide, the thread owns the wide stream
    out in place of stdout's narrow [file_idle], and the rest of
    [hello_stdio] as before. *)
Definition hello_stdio_wide (out : iProp Σ) : iProp Σ :=
  out ∗ file_idle (ho_vb o) (ow_self w0) (ho_err o) 2 ∗
  (stream_life (ho_in o) ∗ exit_stream false (ho_in o)) ∗ io_list_inv ge [ho_err o; ho_out o; ho_in o] ∗
  tcb_cleanup_inv (ow_self w0) ∗ errno_any (ho_eb o) ∗ error_count.

(** The strings of gnulib's version text and bug-report lines, listed
    in [HelloVersionLits](HelloVersionLits.v), are read-only and hold
    their exact bytes. *)
Definition version_ro : iProp Σ :=
  [∗ list] ns ∈ version_lits, word_string DfracDiscarded (sym_ptr ge ns.1) ns.2.

(** The strings are persistent. *)
Global Instance version_ro_persistent : Persistent version_ro.
Proof using Type. rewrite /version_ro. apply _. Qed.

(** The formatter's read-only tables, [printf_ro], read only the
    linked program, so any world gives the same tables. This world is
    the one [hello_ro] names them in. *)
Definition ro_world : os_world := mkOsWorld None null None [] (fun _ => false) null false.
Definition hello_printf_ro : iProp Σ := printf_ro (glibc_program := program_of ro_world glibc_os_registry ge).

(** The tables are persistent. *)
Global Instance hello_printf_ro_persistent : Persistent hello_printf_ro.
Proof using Type. apply printf_ro_persistent. Qed.

(** Calls share read-only ownership of the linked constants, stream
    pointers, errno lifetime, allocator prelude, program literals and
    the null callback of the error reporter. *)
Definition hello_ro : iProp Σ :=
  vtables_ro ge (ho_vb o) (ho_vreg o) ∗ single_ro ge (ho_sb o) (ho_sreg o) ∗
  liveq DfracDiscarded (ho_so o) (ho_soreg o) ∗ pcellq DfracDiscarded (ho_so o) 0 (ho_out o) ∗
  liveq DfracDiscarded (ho_se o) (ho_sereg o) ∗ pcellq DfracDiscarded (ho_se o) 0 (ho_err o) ∗
  liveq DfracDiscarded (ho_eb o) (ho_ereg o) ∗
  AL.tcache_idle DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o) ∗
  word_string DfracDiscarded (ho_lp o) libs_bytes ∗ word_string DfracDiscarded (ho_tp o) lt_bytes ∗
  ([∗ list] s ∈ hello_lits, str_ro (sym_ptr ge s)) ∗ version_ro ∗ hello_printf_ro ∗ error_progname_ro ∗
  print_fmt_ro.

(** [hello_ro] is persistent. *)
Global Instance hello_ro_persistent : Persistent hello_ro.
Proof using Type. rewrite /hello_ro /version_ro /str_ro /error_progname_ro /print_fmt_ro /AL.tcache_idle /liveq /pcellq /icellq. apply _. Qed.

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

(** Main prints help text to stdout and the usage hint to stderr. Each
    site passes a stream and a literal first. A site of `c: fprintf`
    passes one more argument, the string that `%s` prints. *)
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
    Printing the greeting orients stdout wide, so close_stdout takes
    stdout in either orientation.
    Milestone M4 covers the other calls, including the close callback.
    In the C locale the conversion of the greeting cannot fail, so main
    never reaches its fatal error report. The close callback may read
    the program-name cells, and so may an error report. glibc's option parser is
    proved over its own code, so its contract is not a field here. *)
Record HelloCore : Type := mkHelloCore {
  hd_priv : iProp Σ;
  (* The state of stdout once `c: wprintf` has oriented it wide: its
     wide data, its wide buffer, its mode and its conversion steps. The
     caller chooses it, like hd_priv, and close_stdout consumes it. *)
  hd_wide : iProp Σ;
  hd_setlocale_all :
    fn_triple (TAtom "setlocale") [WInt 6; WPtr (sym_ptr ge "hello#str.80")]
      (hello_ro ∗ hello_stdio ∗ hd_priv)%I (fun r => ∃ q, ⌜r = Ret (WPtr q)⌝ ∗ hello_stdio ∗ hd_priv)%I;
  hd_setlocale_query :
    fn_triple (TAtom "setlocale") [WInt 5; WPtr null]
      (hello_ro ∗ hello_stdio ∗ hd_priv)%I
      (fun r => ∃ q, ⌜r = Ret (WPtr q)⌝ ∗ hello_stdio ∗ hd_priv ∗ (⌜ptr_addr q = 0⌝ ∨ str_ro q))%I;
  hd_mbsrtowcs : forall bd b4 b6 g gs,
    let n := 4 * (Z.of_nat (length gs) + 1) in
    fn_triple (TAtom "rpl_mbsrtowcs")
      [WPtr (mkPtr bd (Obj bd)); WPtr (mkPtr b4 (Obj b4)); WInt (Z.of_nat (length gs) + 1);
       WPtr (mkPtr b6 (Obj b6))]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ wbuf bd n (replicate (Z.to_nat (req_extent (wreq n))) 0) ∗
       gcell b4 g ∗ word_string DfracDiscarded g gs ∗ obj b6 (heap_req 4 8))%I
      (fun r => ∃ k ws, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 64 /\ k <> 2 ^ 64 - 1 /\ wide_text ws⌝ ∗
                  hello_stdio ∗ hd_priv ∗ wbuf bd n ws)%I;
  hd_wprintf : forall bd n ws,
    wide_text ws ->
    fn_triple (TAtom "wprintf") [WPtr (sym_ptr ge "hello#str.83"); WPtr (mkPtr bd (Obj bd))]
      (hello_ro ∗ hello_stdio ∗ hd_priv ∗ wbuf bd n ws)%I
      (ret_int (hello_stdio_wide hd_wide ∗ hd_priv ∗ wbuf bd n ws))%I;
  hd_close_stdout : forall wide : bool,
    fn_triple (TAtom "close_stdout") []
      (hello_ro ∗ (if wide then hello_stdio_wide hd_wide else hello_stdio) ∗ hd_priv ∗ names)%I
      (fun r => ⌜r = RetVoid⌝ ∗ exit_io)%I
}.

(** The version text and the bug-report address are printed with
    `c: fprintf`, `c: printf` and `c: fputs`. An extra operand is
    reported with `c: error`, which reads the program-name cells and
    flushes both streams with `c: fflush`. The help text, the usage
    line and the hint to try `--help` are printed with `c: fputs` and
    `c: fprintf`. These calls are proved from the image's code over the
    contracts of the calls they make.
    The record [HelloPrints] states them for any private state priv of
    the callees, because the calls do not touch it. *)
Record HelloPrints (priv : iProp Σ) : Prop := mkHelloPrints {
  hp_version_etc : forall q1 q2 q3 q4,
    fn_triple (TAtom "version_etc")
      [WPtr (ho_out o); WPtr (sym_ptr ge "hello#str.70"); WPtr (sym_ptr ge "hello#str.63");
       WPtr (sym_ptr ge "hello#str.71"); WPtr q1; WPtr q2; WPtr q3; WPtr q4; WPtr null]
      (hello_ro ∗ hello_stdio ∗ priv ∗ str_ro q1 ∗ str_ro q2 ∗ str_ro q3 ∗ str_ro q4)%I
      (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio ∗ priv)%I;
  hp_emit_bug :
    fn_triple (TAtom "emit_bug_reporting_address") [] (hello_ro ∗ hello_stdio ∗ priv)%I
      (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio ∗ priv)%I;
  hp_error_operand : forall q,
    fn_triple (TAtom "error")
      [WInt 0; WInt 0; WPtr (sym_ptr ge "hello#str.77"); WPtr (sym_ptr ge "hello#str.78"); WPtr q]
      (hello_ro ∗ hello_stdio ∗ priv ∗ names ∗ str_arg (WPtr q))%I
      (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio ∗ priv ∗ names)%I;
  hp_print : forall g xs, print_site g xs ->
    fn_triple g xs (hello_ro ∗ hello_stdio ∗ priv ∗ [∗ list] x ∈ skipn 2 xs, str_arg x)%I
      (ret_int (hello_stdio ∗ priv))%I
}.

(** The record [HelloLibs] holds the contracts of the library calls
    that are already proved from glibc's code. Registering the close
    callback changes the exit-handler state from X0 to X, and
    `c: exit` consumes X when it invokes the callback.
    HelloGlibcMainLibs.v builds this record from the proofs of the
    glibc functions. *)
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
  hl_exit : forall n (S : iProp Σ),
    fn_triple (TAtom "close_stdout") [] (hello_ro ∗ S ∗ priv ∗ names) (fun r => ⌜r = RetVoid⌝ ∗ exit_io)%I ->
    fn_triple (TAtom "exit") [WInt n] (hello_ro ∗ S ∗ priv ∗ names ∗ X) (fun _ => False)%I;
  hl_proper_name : forall p, fn_triple (TAtom "proper_name") [WPtr p] True (fun r => ⌜r = Ret (WPtr p)⌝)%I;
  hl_prints : HelloPrints priv
}.

End debts.

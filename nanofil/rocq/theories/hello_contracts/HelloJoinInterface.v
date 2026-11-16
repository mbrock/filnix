(** Printing the greeting requires initialized memory and character conversion.
    This interface lets separate proofs use those operations without repeatedly checking their implementations. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs
  HelloName HelloProgName HelloClose HelloVersion Startup Getopt GetoptLogic.
Open Scope Z_scope.
Open Scope list_scope.

From Nanofil Require Import HelloMainBase HelloMainFacts.
Import MainDefinitions MainFacts.
Module Type HelloJoinBase (R : Runtime).
Module HM.
Declare Module LG0 : LogicSig R.
Import LG0 LG0.L.
Module HLo.
Module HL.
Parameter linked_outside :
  forall (ge : genv) (_ : hello_linked ge) (s : String.string) (_ : @eq bool (@existsb String.string
  (String.eqb s) hello_externals) true), @eq (option fn_def) (find_fn ge (TAtom s)) (@None fn_def).
Arguments linked_outside ge Hlinked s%_string_scope _.
Parameter linked_unbound :
  forall (ge : genv) (_ : hello_linked ge) (s : String.string) (_ : @eq bool (@existsb String.string
  (String.eqb s) hello_externals) true), @eq (option ptr) (@lookup ptr (TAtom s) (ge_globals ge)) (@None ptr).
Arguments linked_unbound ge Hlinked s%_string_scope _.
Module ML.
Definition bytes {Σ} `{!gen_heapGS piece pval Σ} (b o : Z) (xs : list Z) : iProp Σ := pts (byte_ps b o xs).
Definition auxes {Σ} `{!gen_heapGS piece pval Σ} (b o : Z) (cs : list cap) : iProp Σ := pts (aux_ps b o cs).
Definition libc_mem_irisGS {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) (ge : genv) := nanofil_irisGS registry wi ge.
Module CSL.
Definition string {Σ} `{!gen_heapGS piece pval Σ} (p : ptr) (b : Z) (reg : region) (bs : list Z) : iProp Σ :=
  ⌜string_ok p b reg bs⌝ ∗ pts (string_ps p b reg bs).
Definition string_irisGS {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) (ge : genv) := nanofil_irisGS registry wi ge.
Parameter string_suffix :
  forall {Σ : gFunctors} {gen_heapGS0 : @gen_heapGS piece pval Σ piece_eq_dec piece_countable} (p : ptr) (b :
  Z) (reg : region) (bytes : list Z) (i : nat) (_ : le i (@length Z bytes)), @bi_emp_valid natSI (uPredI
  (iResUR Σ)) (@bi_wand _ (uPredI (iResUR Σ)) (@string Σ gen_heapGS0 p b reg bytes) (@bi_sep _ (uPredI (iResUR
  Σ)) (@string Σ gen_heapGS0 (mkPtr (Z.add (ptr_addr p) (Z.of_nat i)) (ptr_cap p)) b reg (@skipn Z i bytes))
  (@bi_wand _ (uPredI (iResUR Σ)) (@string Σ gen_heapGS0 (mkPtr (Z.add (ptr_addr p) (Z.of_nat i)) (ptr_cap p))
  b reg (@skipn Z i bytes)) (@string Σ gen_heapGS0 p b reg bytes)))).
Arguments string_suffix {Σ gen_heapGS0} p b%_Z_scope reg bytes%_list_scope i%_nat_scope _.
Parameter wp_strlen :
  forall {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : @gen_heapGS piece pval Σ
  piece_eq_dec piece_countable} {world : Type} (registry : forall _ : name, option (contract world)) (wi :
  forall (_ : mem) (_ : world) (_ : @gmap piece piece_eq_dec piece_countable pval), Prop) {_ :
  @LG0.SafepointStable world wi} (ge : genv) (f : func) (e : env) (ls : list (prod name (option Z))) (lab d :
  name) (v : value) (rest : list inst) (j : jump) (p : ptr) (b : Z) (reg : region) (bytes : list Z) (Φ :
  forall _ : val (@L.nanofil_lang world registry ge), @bi_car _ (uPredI (iResUR Σ))) (_ : @eq (option
  (contract world)) (registry (TAtom (String (Ascii.Ascii true true false false true true true false) (String
  (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii false true false false true
  true true false) (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true
  false true false false true true false) (String (Ascii.Ascii false true true true false true true false)
  EmptyString)))))))) (@Some (contract world) (strlen_contract world))) (_ : @eq (option fn_def) (find_fn ge
  (TAtom (String (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false
  true false true true true false) (String (Ascii.Ascii false true false false true true true false) (String
  (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true false true false false
  true true false) (String (Ascii.Ascii false true true true false true true false) EmptyString)))))))) (@None
  fn_def)) (_ : @eq (option ptr) (@lookup ptr (TAtom (String (Ascii.Ascii true true false false true true true
  false) (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii false true
  false false true true true false) (String (Ascii.Ascii false false true true false true true false) (String
  (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii false true true true false
  true true false) EmptyString))))))) (ge_globals ge)) (@None ptr)) (_ : @eq (option word) (arg_x ge e (Arg P
  v)) (@Some word (WPtr p))), @bi_emp_valid natSI (uPredI (iResUR Σ)) (@bi_wand _ (uPredI (iResUR Σ)) (@string
  Σ gen_heapGS0 p b reg bytes) (@bi_wand _ (uPredI (iResUR Σ)) (@bi_later _ (uPredI (iResUR Σ)) (@bi_wand _
  (uPredI (iResUR Σ)) (@string Σ gen_heapGS0 p b reg bytes) (@wp (@bi_car _ (uPredI (iResUR Σ)))
  (language.expr (@L.nanofil_lang world registry ge)) (val (@L.nanofil_lang world registry ge)) stuckness
  (@wp' hlc (@L.nanofil_lang world registry ge) Σ (@string_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry
  wi ge)) NotStuck (@top coPset coPset_top) (L.ERun (mkFrame f (@put word d (WInt (Z.of_nat (@length Z
  bytes))) e) ls (@None reason) (Exec lab rest j)) : language.expr (@L.nanofil_lang world registry ge)) Φ)))
  (@wp (@bi_car _ (uPredI (iResUR Σ))) (language.expr (@L.nanofil_lang world registry ge)) (val
  (@L.nanofil_lang world registry ge)) stuckness (@wp' hlc (@L.nanofil_lang world registry ge) Σ
  (@string_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry wi ge)) NotStuck (@top coPset coPset_top)
  (L.ERun (mkFrame f e ls (@None reason) (Exec lab (@cons inst (Call (CResult d L) (Global (TAtom (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false false true true false true true false) (String (Ascii.Ascii true false true false false true true
  false) (String (Ascii.Ascii false true true true false true true false) EmptyString)))))))) (@cons arg (Arg
  P v) (@nil arg))) rest) j)) : language.expr (@L.nanofil_lang world registry ge)) Φ))).
Arguments wp_strlen {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge f e ls%_list_scope lab d v rest%_list_scope j p b%_Z_scope reg bytes%_list_scope
  Φ%_function_scope _ _ _ _.
End CSL.
Parameter block_pts :
  forall {Σ : gFunctors} {gen_heapGS0 : @gen_heapGS piece pval Σ piece_eq_dec piece_countable} (b : Z) (reg :
  region) (o : Z) (xs : list Z) (cs : list cap), @equiv (@bi_car _ (uPredI (iResUR Σ))) (@ofe_equiv _
  (@bi_ofeO natSI (uPredI (iResUR Σ)))) (@pts Σ gen_heapGS0 (block_ps b reg o xs cs)) (@bi_sep _ (uPredI
  (iResUR Σ)) (@LG0.live Σ gen_heapGS0 b reg) (@bi_sep _ (uPredI (iResUR Σ)) (@bytes Σ gen_heapGS0 b o xs)
  (@auxes Σ gen_heapGS0 b o cs))).
Arguments block_pts {Σ gen_heapGS0} b%_Z_scope reg o%_Z_scope (xs cs)%_list_scope.
Parameter bytes_take_drop :
  forall {Σ : gFunctors} {gen_heapGS0 : @gen_heapGS piece pval Σ piece_eq_dec piece_countable} (b o : Z) (xs :
  list Z) (n : nat) (_ : le n (@length Z xs)), @equiv (@bi_car _ (uPredI (iResUR Σ))) (@ofe_equiv _ (@bi_ofeO
  natSI (uPredI (iResUR Σ)))) (@bytes Σ gen_heapGS0 b o xs) (@bi_sep _ (uPredI (iResUR Σ)) (@bytes Σ
  gen_heapGS0 b o (@firstn Z n xs)) (@bytes Σ gen_heapGS0 b (Z.add o (Z.of_nat n)) (@skipn Z n xs))).
Arguments bytes_take_drop {Σ gen_heapGS0} (b o)%_Z_scope xs%_list_scope n%_nat_scope _.
Parameter auxes_take_drop :
  forall {Σ : gFunctors} {gen_heapGS0 : @gen_heapGS piece pval Σ piece_eq_dec piece_countable} (b o : Z) (cs :
  list cap) (n : nat) (_ : le n (@length cap cs)), @equiv (@bi_car _ (uPredI (iResUR Σ))) (@ofe_equiv _
  (@bi_ofeO natSI (uPredI (iResUR Σ)))) (@auxes Σ gen_heapGS0 b o cs) (@bi_sep _ (uPredI (iResUR Σ)) (@auxes Σ
  gen_heapGS0 b o (@firstn cap n cs)) (@auxes Σ gen_heapGS0 b (Z.add o (Z.of_nat n)) (@skipn cap n cs))).
Arguments auxes_take_drop {Σ gen_heapGS0} (b o)%_Z_scope cs%_list_scope n%_nat_scope _.
Parameter obj_zero_block :
  forall {Σ : gFunctors} {gen_heapGS0 : @gen_heapGS piece pval Σ piece_eq_dec piece_countable} (b : Z) (q :
  alloc_req) (_ : Z.le Z0 (req_extent q)), @equiv (@bi_car _ (uPredI (iResUR Σ))) (@ofe_equiv _ (@bi_ofeO
  natSI (uPredI (iResUR Σ)))) (@LG0.obj Σ gen_heapGS0 b q) (@bi_sep _ (uPredI (iResUR Σ)) (@LG0.live Σ
  gen_heapGS0 b (mkRegion b (Z.add b (req_extent q)) (req_kind q) Live)) (@bi_sep _ (uPredI (iResUR Σ))
  (@bytes Σ gen_heapGS0 b Z0 (@replicate Z (Z.to_nat (req_extent q)) Z0)) (@auxes Σ gen_heapGS0 b Z0
  (@replicate cap (Z.to_nat (req_extent q)) CNone)))).
Arguments obj_zero_block {Σ gen_heapGS0} b%_Z_scope q _.
Parameter wp_malloc :
  forall {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : @gen_heapGS piece pval Σ
  piece_eq_dec piece_countable} {world : Type} (registry : forall _ : name, option (contract world)) (wi :
  forall (_ : mem) (_ : world) (_ : @gmap piece piece_eq_dec piece_countable pval), Prop) {_ :
  @LG0.SafepointStable world wi} (ge : genv) (f : func) (e : env) (ls : list (prod name (option Z))) (lab d :
  name) (v : value) (rest : list inst) (j : jump) (n : Z) (Φ : forall _ : val (@L.nanofil_lang world registry
  ge), @bi_car _ (uPredI (iResUR Σ))) (_ : @eq (option (contract world)) (registry (TAtom (String (Ascii.Ascii
  true false true true false true true false) (String (Ascii.Ascii true false false false false true true
  false) (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii false false
  true true false true true false) (String (Ascii.Ascii true true true true false true true false) (String
  (Ascii.Ascii true true false false false true true false) EmptyString)))))))) (@Some (contract world)
  (malloc_contract world))) (_ : @eq (option fn_def) (find_fn ge (TAtom (String (Ascii.Ascii true false true
  true false true true false) (String (Ascii.Ascii true false false false false true true false) (String
  (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii false false true true false
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true
  true false false false true true false) EmptyString)))))))) (@None fn_def)) (_ : @eq (option ptr) (@lookup
  ptr (TAtom (String (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii true false
  false false false true true false) (String (Ascii.Ascii false false true true false true true false) (String
  (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true true false
  true true false) (String (Ascii.Ascii true true false false false true true false) EmptyString)))))))
  (ge_globals ge)) (@None ptr)) (_ : @eq (option word) (arg_x ge e (Arg L v)) (@Some word (WInt n))) (_ : and
  (Z.le Z0 n) (Z.lt n (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xO (xO xH)))))))))) (_ : forall (m : mem)
  (wd : world) (h : @gmap piece piece_eq_dec piece_countable pval) (base : Z) (_ : fresh m (heap_req (Zpos (xO
  (xO (xO (xO xH))))) n) base) (_ : wi m wd h), wi (allocated m (heap_req (Zpos (xO (xO (xO (xO xH))))) n)
  base) wd (overwrite (obj_ps base (heap_req (Zpos (xO (xO (xO (xO xH))))) n)) h)), @bi_emp_valid natSI
  (uPredI (iResUR Σ)) (@bi_wand _ (uPredI (iResUR Σ)) (@bi_later _ (uPredI (iResUR Σ)) (@bi_forall _ (uPredI
  (iResUR Σ)) Z (fun base : Z => @bi_wand _ (uPredI (iResUR Σ)) (@bi_pure _ (uPredI (iResUR Σ)) (and (Z.lt Z0
  base) (and (@eq Z (Z.modulo base (Zpos (xO (xO (xO (xO xH)))))) Z0) (and (Z.le (Z.add base (req_extent
  (heap_req (Zpos (xO (xO (xO (xO xH))))) n))) (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xI xH))))))))
  (Z.le n max_allocation_size))))) (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.obj Σ gen_heapGS0 base (heap_req
  (Zpos (xO (xO (xO (xO xH))))) n)) (@wp (@bi_car _ (uPredI (iResUR Σ))) (language.expr (@L.nanofil_lang world
  registry ge)) (val (@L.nanofil_lang world registry ge)) stuckness (@wp' hlc (@L.nanofil_lang world registry
  ge) Σ (@libc_mem_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry wi ge)) NotStuck (@top coPset
  coPset_top) (L.ERun (mkFrame f (@put word d (WPtr (mkPtr base (Obj base))) e) ls (@None reason) (Exec lab
  rest j)) : language.expr (@L.nanofil_lang world registry ge)) Φ))))) (@wp (@bi_car _ (uPredI (iResUR Σ)))
  (language.expr (@L.nanofil_lang world registry ge)) (val (@L.nanofil_lang world registry ge)) stuckness
  (@wp' hlc (@L.nanofil_lang world registry ge) Σ (@libc_mem_irisGS hlc Σ invGS_gen0 gen_heapGS0 world
  registry wi ge)) NotStuck (@top coPset coPset_top) (L.ERun (mkFrame f e ls (@None reason) (Exec lab (@cons
  inst (Call (CResult d P) (Global (TAtom (String (Ascii.Ascii true false true true false true true false)
  (String (Ascii.Ascii true false false false false true true false) (String (Ascii.Ascii false false true
  true false true true false) (String (Ascii.Ascii false false true true false true true false) (String
  (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true true false false false
  true true false) EmptyString)))))))) (@cons arg (Arg L v) (@nil arg))) rest) j)) : language.expr
  (@L.nanofil_lang world registry ge)) Φ)).
Arguments wp_malloc {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge f e ls%_list_scope lab d v rest%_list_scope j n%_Z_scope Φ%_function_scope
  _ _ _ _ _ _%_function_scope.
End ML.
Module LL.
Definition lent {Σ} `{!gen_heapGS piece pval Σ} (k : Z) (p : ptr) (t : list Z) : iProp Σ :=
  ⌜0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length t) < 2 ^ 64 /\ Forall (fun x => 0 < x < 256) t⌝ ∗
  pointsto (PName k) DfracDiscarded (VName p t).
Definition named {Σ} `{!gen_heapGS piece pval Σ} (k : Z) (p : ptr) (t : list Z) : iProp Σ :=
  pointsto (PName k) (DfracOwn 1) (VName p t).
End LL.
End HL.
End HLo.
Import HLo.HL HLo.HL.ML HLo.HL.ML.CSL HLo.HL.LL.
Module HP.
Module HN.
Parameter store_keeps :
  forall {world : Type} (_ : forall (_ : mem) (_ : world) (_ : @gmap piece piece_eq_dec piece_countable pval),
  Prop) (_ : Z) (_ : region), Prop.
Arguments store_keeps {world}%_type_scope wi%_function_scope b%_Z_scope reg.
Parameter literals :
  forall {Σ : gFunctors} {_ : @gen_heapGS piece pval Σ piece_eq_dec piece_countable} (_ : region) (_ :
  region), uPred (iResUR Σ).
Arguments literals {Σ gen_heapGS0} r3 r4.
Parameter name_cells :
  forall {Σ : gFunctors} {_ : @gen_heapGS piece pval Σ piece_eq_dec piece_countable} (_ : region) (_ : region)
  (_ : region) (_ : Z) (_ : Z) (_ : ptr) (_ : ptr) (_ : ptr), uPred (iResUR Σ).
Arguments name_cells {Σ gen_heapGS0} pn nreg sreg (nb sb)%_Z_scope x0 x1 y.
End HN.
End HP.
Module HV.
Parameter version_main_args :
  forall _ : ptr, list word.
Arguments version_main_args stream.
End HV.
Definition fresh_ok := MainFacts.fresh_ok.
Definition greeting_ok := MainFacts.greeting_ok.
Definition main_irisGS {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) (ge : genv) := nanofil_irisGS registry wi ge.
Definition loop_res {Σ} `{!gen_heapGS piece pval Σ} (av : Z) (ar : region) (sargs : list argument)
  (b4 : Z) (ps : list ptr) (cs : list cap) (a : ptr) (i : Z) (g : ptr) : iProp Σ :=
  pts (block_ps av ar 0 (argv_bytes ps) cs) ∗ pts (flat_map arg_ps sargs) ∗ pts (getopt_ps a i) ∗
  live b4 (mkRegion b4 (b4 + 16) Heap Live) ∗ pcell b4 0 g.
Definition operand_exit :=
fun (hlc : has_lc) (Σ : gFunctors) (invGS_gen0 : invGS_gen hlc Σ)
  (gen_heapGS0 : @gen_heapGS piece pval Σ piece_eq_dec piece_countable)
  (registry : forall _ : name, option (contract libc_world))
  (wi : forall (_ : mem) (_ : libc_world) (_ : @gmap piece piece_eq_dec piece_countable pval), Prop)
  (ge : genv) =>
let main_irisGS : irisGS_gen hlc (@nanofil_lang libc_world registry ge) Σ :=
  @main_irisGS hlc Σ invGS_gen0 gen_heapGS0 registry wi ge in
fun (av : Z) (ar : region) (sargs : list argument) (b4 b6 : Z)
  (lab from : String.string) (P : forall (_ : Z) (_ : Z), Prop)
  (Φ : forall _ : val (@nanofil_lang libc_world registry ge), uPred (iResUR Σ)) =>
@bi_forall _ (uPredI (iResUR Σ)) env
  (fun e : env =>
   @bi_forall _ (uPredI (iResUR Σ)) (list ptr)
     (fun ps : list ptr =>
      @bi_forall _ (uPredI (iResUR Σ)) (list cap)
        (fun cs : list cap =>
         @bi_forall _ (uPredI (iResUR Σ)) ptr
           (fun a : ptr =>
            @bi_forall _ (uPredI (iResUR Σ)) Z
              (fun i : Z =>
               @bi_forall _ (uPredI (iResUR Σ)) ptr
                 (fun g : ptr =>
                  @bi_forall _ (uPredI (iResUR Σ)) Z
                    (fun lose : Z =>
                     @bi_wand _ (uPredI (iResUR Σ))
                       (@bi_pure _ (uPredI (iResUR Σ))
                          (and (loop_facts av sargs e b4 b6 ps cs i g)
                             (and
                                (@eq (option word)
                                   (@lookup word
                                      (TAtom
                                         (String (Ascii.Ascii true false false true false true true false)
                                            (String (Ascii.Ascii true true true false true true true false)
                                               (String (Ascii.Ascii true true true true true false true false)
                                                  (String (Ascii.Ascii true false false false true true false false)
                                                     (String (Ascii.Ascii false true true true false true false false)
                                                        (String
                                                           (Ascii.Ascii false false false false true true true false)
                                                           (String
                                                              (Ascii.Ascii false true false false true true true false)
                                                              (String
                                                                 (Ascii.Ascii false true true true false true false
                                                                    false)
                                                                 (String
                                                                    (Ascii.Ascii false true false false true true false
                                                                       false)
                                                                    EmptyString))))))))))
                                      e)
                                   (@Some word (WInt lose)))
                                (P lose i))))
                       (@bi_wand _ (uPredI (iResUR Σ)) (@loop_res Σ gen_heapGS0 av ar sargs b4 ps cs a i g)
                          (@wp (uPred (iResUR Σ)) (language.expr (@nanofil_lang libc_world registry ge))
                             (val (@nanofil_lang libc_world registry ge)) stuckness
                             (@wp' hlc (@nanofil_lang libc_world registry ge) Σ main_irisGS) NotStuck
                             (@top coPset coPset_top)
                             (ERun
                                (mkFrame main_fn e (@nil (prod name (option Z)))
                                   (@None reason) (Enter (TAtom lab) (@Some term (TAtom from))))
                              :
                              language.expr (@nanofil_lang libc_world registry ge))
                             Φ))))))))).
Arguments operand_exit {hlc Σ invGS_gen0 gen_heapGS0} registry wi ge av ar sargs b4 b6 lab from P Φ.
Parameter main_to_join :
  forall {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : @gen_heapGS piece pval Σ
  piece_eq_dec piece_countable} (registry : forall _ : name, option (contract libc_world)) (wi : forall (_ :
  mem) (_ : libc_world) (_ : @gmap piece piece_eq_dec piece_countable pval), Prop) {_ : @LG0.SafepointStable
  libc_world wi} (ge : genv) (_ : hello_linked ge) (_ : forall (q : alloc_req) (m : mem) (wd : libc_world) (h
  : @gmap piece piece_eq_dec piece_countable pval) (base : Z) (_ : fresh m q base) (_ : wi m wd h), wi
  (allocated m q base) wd (overwrite (obj_ps base q) h)) (_ : @eq (option (contract libc_world)) (registry
  (TAtom (String (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii true false true
  false false true true false) (String (Ascii.Ascii true false true true false true true false) (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii true false true false false
  true true false) (String (Ascii.Ascii false false true false true true true false) EmptyString))))))))
  (@Some (contract libc_world) (memset_contract libc_world))) (_ : forall (b : Z) (reg : region) (o : Z) (xs :
  list Z) (cs : list cap) (m m' : mem) (wd : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval)
  (_ : memset_result m (mkPtr (Z.add b o) (Obj b)) Z0 (Zpos (xO (xO (xO xH)))) m') (_ : forall (l : piece) (v
  : pval) (_ : @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair
  piece pval l v) (block_ps b reg o xs cs)), @eq (option pval) (@base.lookup piece pval (@gmap piece
  piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some pval
  v)) (_ : wi m wd h), wi m' wd (overwrite (block_ps b reg o (@replicate Z (S (S (S (S (S (S (S (S O))))))))
  Z0) (clear_slots o cs)) h)) (_ : @eq (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii
  true true false false true true true false) (String (Ascii.Ascii false false true false true true true
  false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii false true
  false false true true true false) (String (Ascii.Ascii true true false false false true true false) (String
  (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii false true false false true
  true true false) EmptyString))))))))) (@Some (contract libc_world) (strrchr_contract libc_world))) (_ : @eq
  (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true false true true false true true
  false) (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii true false
  true true false true true false) (String (Ascii.Ascii true true false false false true true false) (String
  (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii false false false false true
  true true false) EmptyString)))))))) (@Some (contract libc_world) (memcmp_contract libc_world))) (_ : @eq
  (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true true false false true true true
  false) (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii false true
  false false true true true false) (String (Ascii.Ascii false true true true false true true false) (String
  (Ascii.Ascii true true false false false true true false) (String (Ascii.Ascii true false true true false
  true true false) (String (Ascii.Ascii false false false false true true true false) EmptyString)))))))))
  (@Some (contract libc_world) (strncmp_contract libc_world))) (pn nreg sreg : region) (nb sb : Z) (_ : @eq
  (option ptr) (@lookup ptr (TAtom (String (Ascii.Ascii false false false false true true true false) (String
  (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii true true true true false
  true true false) (String (Ascii.Ascii true true true false false true true false) (String (Ascii.Ascii false
  true false false true true true false) (String (Ascii.Ascii true false false false false true true false)
  (String (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii true true true true
  true false true false) (String (Ascii.Ascii true false false true false true true false) (String
  (Ascii.Ascii false true true true false true true false) (String (Ascii.Ascii false true true false true
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true
  true false false false true true false) (String (Ascii.Ascii true false false false false true true false)
  (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii true false false true
  false true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii
  false true true true false true true false) (String (Ascii.Ascii true true true true true false true false)
  (String (Ascii.Ascii false true true true false true true false) (String (Ascii.Ascii true false false false
  false true true false) (String (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii
  true false true false false true true false) EmptyString)))))))))))))))))))))))) (ge_globals ge)) (@Some ptr
  (mkPtr nb (Obj nb)))) (_ : @eq (option ptr) (@lookup ptr (TAtom (String (Ascii.Ascii false false false false
  true true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  true true true true false true true false) (String (Ascii.Ascii true true true false false true true false)
  (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii true false false
  false false true true false) (String (Ascii.Ascii true false true true false true true false) (String
  (Ascii.Ascii true true true true true false true false) (String (Ascii.Ascii true false false true false
  true true false) (String (Ascii.Ascii false true true true false true true false) (String (Ascii.Ascii false
  true true false true true true false) (String (Ascii.Ascii true true true true false true true false)
  (String (Ascii.Ascii true true false false false true true false) (String (Ascii.Ascii true false false
  false false true true false) (String (Ascii.Ascii false false true false true true true false) (String
  (Ascii.Ascii true false false true false true true false) (String (Ascii.Ascii true true true true false
  true true false) (String (Ascii.Ascii false true true true false true true false) (String (Ascii.Ascii true
  true true true true false true false) (String (Ascii.Ascii true true false false true true true false)
  (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii true true true true
  false true true false) (String (Ascii.Ascii false true false false true true true false) (String
  (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii true true true true true
  false true false) (String (Ascii.Ascii false true true true false true true false) (String (Ascii.Ascii true
  false false false false true true false) (String (Ascii.Ascii true false true true false true true false)
  (String (Ascii.Ascii true false true false false true true false) EmptyString))))))))))))))))))))))))))))))
  (ge_globals ge)) (@Some ptr (mkPtr sb (Obj sb)))) (_ : Z.le (Z.add program_name_b (Zpos (xO (xO (xO xH)))))
  (r_end pn)) (_ : and (Z.le Z0 nb) (and (@eq Z (Z.modulo nb (Zpos (xO (xO (xO xH))))) Z0) (and (Z.le (Z.add
  nb (Zpos (xO (xO (xO xH))))) (r_end nreg)) (Z.le (r_end nreg) (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO
  (xI xH))))))))))) (_ : and (Z.le Z0 sb) (and (@eq Z (Z.modulo sb (Zpos (xO (xO (xO xH))))) Z0) (and (Z.le
  (Z.add sb (Zpos (xO (xO (xO xH))))) (r_end sreg)) (Z.le (r_end sreg) (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO
  (xO (xI xH))))))))))) (_ : @HP.HN.store_keeps libc_world wi program_name_b pn) (_ : @HP.HN.store_keeps
  libc_world wi nb nreg) (_ : @HP.HN.store_keeps libc_world wi sb sreg) (rep : forall (_ : mem) (_ :
  libc_world), Prop) (requests : forall (_ : list word) (_ : mem) (_ : libc_world) (_ : Z) (_ : Z), Prop) (_ :
  @eq (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true true false false true true
  true false) (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii false
  false true false true true true false) (String (Ascii.Ascii false false true true false true true false)
  (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true true false false
  false true true false) (String (Ascii.Ascii true false false false false true true false) (String
  (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true false true false false
  true true false) EmptyString))))))))))) (@Some (contract libc_world) (libc_setlocale_contract rep
  requests))) (_ : forall (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (k :
  Z) (p : ptr) (t : list Z) (_ : wi m w h) (_ : live_disjoint m) (_ : objects_fit (m_regions m)) (_ :
  freed_empty (m_regions m)) (_ : @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec
  piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) (PName k) h) (@Some pval (VName
  p t))), lent_at m h p t) (_ : forall (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec
  piece_countable pval) (c : Z) (p : ptr) (b : Z) (reg : region) (bytes : list Z) (_ : wi m w h) (_ : @In Z c
  locale_categories) (_ : string_ok p b reg bytes) (_ : all_agree m (string_ps p b reg bytes)),
  libc_setlocale_pre rep (@cons word (WInt c) (@cons word (WPtr p) (@nil word))) m w) (_ : forall (r :
  call_result) (args : list arg) (c : Z) (p : ptr) (s : R.state) (m : mem) (w : libc_world) (h : @gmap piece
  piece_eq_dec piece_countable pval) (trace : list event) (values : list word) (s' : R.state) (m' : mem) (w' :
  libc_world) (_ : wi m w h) (_ : agrees m h) (_ : live_disjoint m) (_ : R.ready s m) (_ : @M.E.invoke
  libc_world (libc_setlocale_contract rep requests) r args (@cons word (WInt c) (@cons word (WPtr p) (@nil
  word))) s m w trace (CallReturn values) s' m' w'), @ex ptr (fun q : ptr => @ex (forall _ : Z, prod ptr (list
  Z)) (fun new : forall _ : Z, prod ptr (list Z) => @ex term (fun c' : term => and (@eq (list word) values
  (@cons word (WPtr q) (@nil word))) (and (or (@eq ptr q (mkPtr Z0 CNone)) (@eq ptr q (@fst ptr (list Z) (new
  c)))) (and (agrees m' h) (and (live_disjoint m') (and (R.ready s' m') (wi m' w' (overwrite (codec_ps c')
  (rename h locale_categories new))))))))))) (_ : forall (b : Z) (reg : region) (o : Z) (x xp : ptr) (m : mem)
  (wd : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : forall (l : piece) (v : pval) (_
  : @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l
  v) (@app (prod piece pval) (@cons (prod piece pval) (@pair piece pval (PLive b) (VLive reg)) (@nil (prod
  piece pval))) (@cons (prod piece pval) (@pair piece pval (PAux b o) (VAux (ptr_cap x))) (cell b o (ptr_addr
  x))))), @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable pval)
  (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some pval v)) (_ : wi m wd h), wi (store_bytes
  (store_aux m (Z.add b o) (ptr_cap xp)) (Z.add b o) (Zpos (xO (xO (xO xH)))) (ptr_addr xp)) wd (overwrite
  (@app (prod piece pval) (@cons (prod piece pval) (@pair piece pval (PLive b) (VLive reg)) (@nil (prod piece
  pval))) (@cons (prod piece pval) (@pair piece pval (PAux b o) (VAux (ptr_cap xp))) (cell b o (ptr_addr
  xp)))) h)) (atexit_spec : contract libc_world) (_ : @eq (option (contract libc_world)) (registry (TAtom
  (String (Ascii.Ascii true false false false false true true false) (String (Ascii.Ascii false false true
  false true true true false) (String (Ascii.Ascii true false true false false true true false) (String
  (Ascii.Ascii false false false true true true true false) (String (Ascii.Ascii true false false true false
  true true false) (String (Ascii.Ascii false false true false true true true false) EmptyString))))))))
  (@Some (contract libc_world) atexit_spec)) (_ : @eq ret_type (@contract_returns libc_world atexit_spec)
  (RClass W)) (_ : @contract_abi libc_world atexit_spec (CResult (TAtom (String (Ascii.Ascii false true true
  false true true true false) (String (Ascii.Ascii true false false false true true false false) (String
  (Ascii.Ascii true false true false true true false false) EmptyString)))) W) (@cons arg (Arg P (Tmp (TAtom
  (String (Ascii.Ascii false true true false true true true false) (String (Ascii.Ascii true false false false
  true true false false) (String (Ascii.Ascii false false true false true true false false) EmptyString))))))
  (@nil arg))) (_ : forall (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ :
  wi m w h), @contract_pre libc_world atexit_spec (@cons word (WPtr close_stdout_ptr) (@nil word)) m w) (_ :
  forall (r : call_result) (args : list arg) (s : R.state) (m : mem) (w : libc_world) (h : @gmap piece
  piece_eq_dec piece_countable pval) (trace : list event) (values : list word) (s' : R.state) (m' : mem) (w' :
  libc_world) (_ : wi m w h) (_ : agrees m h) (_ : live_disjoint m) (_ : R.ready s m) (_ : @M.E.invoke
  libc_world atexit_spec r args (@cons word (WPtr close_stdout_ptr) (@nil word)) s m w trace (CallReturn
  values) s' m' w'), @ex Z (fun x : Z => and (@eq (list word) values (@cons word (WInt x) (@nil word))) (and
  (and (Z.le Z0 x) (Z.lt x (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xO xH))))))))) (and (agrees m' h) (and
  (live_disjoint m') (and (R.ready s' m') (wi m' w' h))))))) (av : Z) (ar : region) (sargs : list argument) (_
  : and (Z.lt Z0 av) (and (@eq Z (Z.modulo av (Zpos (xO (xO (xO xH))))) Z0) (and (Z.le (Z.add av (Z.mul (Zpos
  (xO (xO (xO xH)))) (Z.add (Z.of_nat (@length argument sargs)) (Zpos xH)))) (r_end ar)) (Z.le (r_end ar)
  (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xI xH))))))))))) (_ : and (Z.le (Zpos xH) (Z.of_nat (@length
  argument sargs))) (Z.lt (Z.of_nat (@length argument sargs)) (Z.pow (Zpos (xO xH)) (Zpos (xI (xI (xI (xI
  xH)))))))) (_ : @Forall argument (fun s : argument => string_ok (arg_ptr s) (arg_base s) (arg_region s)
  (arg_text s)) sargs) (initialized running : forall (_ : mem) (_ : libc_world), Prop) (grequests : forall (_
  : list word) (_ : mem) (_ : libc_world) (_ : Z) (_ : Z), Prop) (transition : forall (_ : list word) (_ :
  mem) (_ : libc_world) (_ : list Z) (_ : list event) (_ : list word) (_ : mem) (_ : libc_world), Prop) (_ :
  @eq (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true true true false false true
  true false) (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii false
  false true false true true true false) (String (Ascii.Ascii true true true true false true true false)
  (String (Ascii.Ascii false false false false true true true false) (String (Ascii.Ascii false false true
  false true true true false) (String (Ascii.Ascii true true true true true false true false) (String
  (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true true false
  true true false) (String (Ascii.Ascii false true true true false true true false) (String (Ascii.Ascii true
  true true false false true true false) EmptyString))))))))))))) (@Some (contract libc_world)
  (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition)))
  (optarg_cell optind_cell : ptr) (_ : forall (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec
  piece_countable pval) (_ : wi m w h), and (getopt_state_at m (libc_getopt_view w)) (and (@eq ptr
  (getopt_optarg_cell (libc_getopt_view w)) optarg_cell) (and (@eq ptr (getopt_optind_cell (libc_getopt_view
  w)) optind_cell) (getopt_current (libc_getopt_view w) h)))) (_ : forall (m : mem) (w : libc_world) (h :
  @gmap piece piece_eq_dec piece_countable pval) (_ : wi m w h), hello_table_at m) (_ : forall (m : mem) (w :
  libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (xs : list Z) (cs : list cap) (_ : wi m w h)
  (_ : agrees m h) (_ : live_disjoint m) (_ : forall (l : piece) (v : pval) (_ : @elem_of (prod piece pval)
  (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l v) (@app (prod piece pval)
  (block_ps av ar Z0 xs cs) (@flat_map argument (prod piece pval) arg_ps sargs))), @eq (option pval)
  (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec
  piece_countable pval) l h) (@Some pval v)) (_ : getopt_input_at m (hello_input av sargs)), and
  (libc_getopt_rep initialized m w) (and (@Forall span (writable_span m) (getopt_roots (libc_getopt_view w)))
  (and (@Forall span (fun s : span => readable_bytes m (span_ptr s) (span_size s)) (getopt_reads
  (libc_getopt_view w))) (and (getopt_separated (hello_input av sargs) (libc_getopt_view w)) (and
  (getopt_disjoint (getopt_public_writes (hello_input av sargs) (libc_getopt_view w))) (getopt_private_owned m
  (hello_input av sargs) (libc_getopt_view w))))))) (_ : forall (m : mem) (w : libc_world) (h : @gmap piece
  piece_eq_dec piece_countable pval) (_ : wi m w h), and (forall (s : span) (a : Z) (_ : @In span s (@app span
  (getopt_roots (libc_getopt_view w)) (getopt_cells (libc_getopt_view w)))) (_ : span_contains s a), not
  (owned_live h m a)) (ids_apart (getopt_owned (libc_getopt_view w)) h)) (_ : forall (r : call_result) (args :
  list arg) (xs : list word) (s : R.state) (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec
  piece_countable pval) (trace : list event) (values : list word) (s' : R.state) (m' : mem) (w' : libc_world)
  (bs : list Z) (cs : list cap) (_ : @M.E.invoke libc_world (libc_getopt_refined_contract (hello_input av
  sargs) initialized running grequests transition) r args xs s m w trace (CallReturn values) s' m' w') (_ :
  forall (l : piece) (v : pval) (_ : @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod
  piece pval)) (@pair piece pval l v) (block_ps av ar Z0 bs cs)), @eq (option pval) (@base.lookup piece pval
  (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) l h)
  (@Some pval v)) (_ : wi m w h) (_ : agrees m h) (_ : live_disjoint m) (_ : R.ready s m), wi m' w' (overwrite
  (@app (prod piece pval) (block_ps av ar Z0 (mem_bytes m' av (Init.Nat.mul (S (S (S (S (S (S (S (S O))))))))
  (Init.Nat.add (@length argument sargs) (S O)))) (mem_auxes m' av (Init.Nat.mul (S (S (S (S (S (S (S (S
  O)))))))) (Init.Nat.add (@length argument sargs) (S O))))) (getopt_ps (getopt_optarg (libc_getopt_view w'))
  (getopt_optind (libc_getopt_view w')))) h)) (_ : @eq (option ptr) (@lookup ptr (TAtom (String (Ascii.Ascii
  true true true true false true true false) (String (Ascii.Ascii false false false false true true true
  false) (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii true false
  false false false true true false) (String (Ascii.Ascii false true false false true true true false) (String
  (Ascii.Ascii true true true false false true true false) EmptyString))))))) (ge_globals ge)) (@Some ptr
  optarg_cell)) (_ : and (and (Z.le Z0 (ptr_addr optarg_cell)) (Z.lt (ptr_addr optarg_cell) (Z.pow (Zpos (xO
  xH)) (Zpos (xO (xO (xO (xO (xO (xO xH)))))))))) (and (Z.le Z0 (ptr_addr optind_cell)) (Z.lt (ptr_addr
  optind_cell) (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xO (xO xH))))))))))) (_ : @eq (option ptr)
  (@lookup ptr (TAtom (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii
  false false false false true true true false) (String (Ascii.Ascii false false true false true true true
  false) (String (Ascii.Ascii true false false true false true true false) (String (Ascii.Ascii false true
  true true false true true false) (String (Ascii.Ascii false false true false false true true false)
  EmptyString))))))) (ge_globals ge)) (@Some ptr optind_cell)) (exit_spec : contract libc_world) (_ : @eq
  (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true false true false false true true
  false) (String (Ascii.Ascii false false false true true true true false) (String (Ascii.Ascii true false
  false true false true true false) (String (Ascii.Ascii false false true false true true true false)
  EmptyString)))))) (@Some (contract libc_world) exit_spec)) (_ : forall v : value, @contract_abi libc_world
  exit_spec CVoid (@cons arg (Arg W v) (@nil arg))) (_ : forall (n : Z) (m : mem) (w : libc_world) (h : @gmap
  piece piece_eq_dec piece_countable pval) (_ : and (Z.le Z0 n) (Z.lt n (Z.pow (Zpos (xO xH)) (Zpos (xO (xO
  (xO (xO (xO xH))))))))) (_ : wi m w h), @contract_pre libc_world exit_spec (@cons word (WInt n) (@nil word))
  m w) (_ : forall (args : list arg) (n : Z) (s : R.state) (m : mem) (w : libc_world) (tr : list event) (vs :
  list word) (s' : R.state) (m' : mem) (w' : libc_world) (_ : @M.E.invoke libc_world exit_spec CVoid args
  (@cons word (WInt n) (@nil word)) s m w tr (CallReturn vs) s' m' w'), False) (stdout_cell stream : ptr) (_ :
  @eq (option ptr) (@lookup ptr (TAtom (String (Ascii.Ascii true true false false true true true false)
  (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii false false true
  false false true true false) (String (Ascii.Ascii true true true true false true true false) (String
  (Ascii.Ascii true false true false true true true false) (String (Ascii.Ascii false false true false true
  true true false) EmptyString))))))) (ge_globals ge)) (@Some ptr stdout_cell)) (_ : forall (m : mem) (w :
  libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : wi m w h), and (@eq (option (res unit))
  (access_res m (raw_address (ptr_addr stdout_cell) Z0) (ptr_cap stdout_cell) (Zpos (xO (xO (xO xH)))) Read
  (Zpos (xO (xO (xO xH))))) (@Some (res unit) (@RVal unit tt))) (@eq (option ptr) (pointer_load_effects m
  (raw_address (ptr_addr stdout_cell) Z0) (@cons effect AuxRead (@cons effect LowerResolve (@cons effect
  AddressRead (@nil effect))))) (@Some ptr stream))) (version_ps : list (prod piece pval)) (author_reg :
  forall _ : String.string, region) (_ : forall (s : String.string) (_ : @In String.string s (@cons
  String.string (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii true
  false true false false true true false) (String (Ascii.Ascii false false true true false true true false)
  (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true true
  false true true false) (String (Ascii.Ascii true true false false false true false false) (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true false false) (String (Ascii.Ascii true true true false true true false
  false) (String (Ascii.Ascii false true false false true true false false) EmptyString)))))))))))) (@cons
  String.string (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii true
  false true false false true true false) (String (Ascii.Ascii false false true true false true true false)
  (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true true
  false true true false) (String (Ascii.Ascii true true false false false true false false) (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true false false) (String (Ascii.Ascii true true true false true true false
  false) (String (Ascii.Ascii true true false false true true false false) EmptyString)))))))))))) (@cons
  String.string (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii true
  false true false false true true false) (String (Ascii.Ascii false false true true false true true false)
  (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true true
  false true true false) (String (Ascii.Ascii true true false false false true false false) (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true false false) (String (Ascii.Ascii true true true false true true false
  false) (String (Ascii.Ascii false false true false true true false false) EmptyString)))))))))))) (@cons
  String.string (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii true
  false true false false true true false) (String (Ascii.Ascii false false true true false true true false)
  (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true true
  false true true false) (String (Ascii.Ascii true true false false false true false false) (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true false false) (String (Ascii.Ascii true true true false true true false
  false) (String (Ascii.Ascii true false true false true true false false) EmptyString)))))))))))) (@nil
  String.string)))))), @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval))
  (@pair piece pval (PLive (ptr_addr (version_literal s))) (VLive (author_reg s))) version_ps) (version_spec :
  forall _ : name, contract libc_world) (_ : forall (g : name) (xs : list word) (_ : @In (prod name (list
  word)) (@pair name (list word) g xs) (version_output_args stream)), @eq (option (contract libc_world))
  (registry g) (@Some (contract libc_world) (version_spec g))) (_ : forall (g : name) (xs : list word) (_ :
  @In (prod name (list word)) (@pair name (list word) g xs) (version_output_args stream)), @eq ret_type
  (@contract_returns libc_world (version_spec g)) (RClass W)) (_ : forall (g : name) (xs : list word) (d :
  name) (args : list arg) (_ : @In (prod name (list word)) (@pair name (list word) g xs) (version_output_args
  stream)) (_ : @eq (list class) (@map arg class (fun a : arg => match a return class with | Arg k _ => k end)
  args) (version_output_classes xs)), @contract_abi libc_world (version_spec g) (CResult d W) args) (_ :
  forall (g : name) (xs : list word) (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable
  pval) (_ : @In (prod name (list word)) (@pair name (list word) g xs) (version_output_args stream)) (_ :
  forall (l : piece) (v : pval) (_ : @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod
  piece pval)) (@pair piece pval l v) version_ps), @eq (option pval) (@base.lookup piece pval (@gmap piece
  piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some pval
  v)) (_ : agrees m h) (_ : wi m w h), @contract_pre libc_world (version_spec g) xs m w) (_ : forall (g :
  name) (xs : list word) (r : call_result) (args : list arg) (s : R.state) (m : mem) (w : libc_world) (h :
  @gmap piece piece_eq_dec piece_countable pval) (trace : list event) (values : list word) (s' : R.state) (m'
  : mem) (w' : libc_world) (_ : @In (prod name (list word)) (@pair name (list word) g xs) (version_output_args
  stream)) (_ : agrees m h) (_ : live_disjoint m) (_ : R.ready s m) (_ : wi m w h) (_ : @M.E.invoke libc_world
  (version_spec g) r args xs s m w trace (CallReturn values) s' m' w'), and (agrees m' h) (and (live_disjoint
  m') (and (R.ready s' m') (and (wi m' w' h) (@ex Z (fun n : Z => and (@eq (list word) values (@cons word
  (WInt n) (@nil word))) (and (Z.le Z0 n) (Z.lt n (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xO
  xH))))))))))))))) (_ : forall (size : Z) (m : mem) (wd : libc_world) (h : @gmap piece piece_eq_dec
  piece_countable pval) (base : Z) (_ : @In Z size (@cons Z (Zpos (xO (xO (xO (xI xH))))) (@cons Z (Zpos (xO
  (xO (xO (xO (xI (xO xH))))))) (@nil Z)))) (_ : fresh m (heap_req (Zpos (xO (xO (xO xH)))) size) base) (_ :
  wi m wd h), wi (allocated m (heap_req (Zpos (xO (xO (xO xH)))) size) base) wd (overwrite (obj_ps base
  (heap_req (Zpos (xO (xO (xO xH)))) size)) h)) (_ : forall (b : Z) (reg : region) (o : Z) (x xp : ptr) (m :
  mem) (wd : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : forall (k : piece) (v :
  pval) (_ : @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair
  piece pval k v) (@app (prod piece pval) (@cons (prod piece pval) (@pair piece pval (PLive b) (VLive reg))
  (@nil (prod piece pval))) (@cons (prod piece pval) (@pair piece pval (PAux b o) (VAux (ptr_cap x))) (cell b
  o (ptr_addr x))))), @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable
  pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) k h) (@Some pval v)) (_ : wi m wd h), wi
  (store_bytes (store_aux m (Z.add b o) (ptr_cap xp)) (Z.add b o) (Zpos (xO (xO (xO xH)))) (ptr_addr xp)) wd
  (overwrite (@app (prod piece pval) (@cons (prod piece pval) (@pair piece pval (PLive b) (VLive reg)) (@nil
  (prod piece pval))) (@cons (prod piece pval) (@pair piece pval (PAux b o) (VAux (ptr_cap xp))) (cell b o
  (ptr_addr xp)))) h)) (_ : forall (cb : Z) (cr : region) (sb0 off : Z) (m : mem) (wd : libc_world) (h : @gmap
  piece piece_eq_dec piece_countable pval) (_ : forall (k : piece) (v : pval) (_ : @elem_of (prod piece pval)
  (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval k v) (va_cursor_ps cb cr (mkPtr
  (Z.add sb0 off) (Ro sb0)))), @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec
  piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) k h) (@Some pval v)) (_ : wi m
  wd h), wi (store_bytes m cb (Zpos (xO (xO (xO xH)))) (Z.add (Z.add sb0 off) (Zpos (xO (xO (xO xH)))))) wd
  (overwrite (va_cursor_ps cb cr (mkPtr (Z.add (Z.add sb0 off) (Zpos (xO (xO (xO xH))))) (Ro sb0))) h)) (_ :
  forall (m : mem) (wd : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (sb0 : Z) (_ : fresh
  m (heap_req (Zpos (xO (xO (xO (xO xH))))) (Zpos (xO (xO (xO (xI (xO (xO xH)))))))) sb0) (_ : wi m wd h), wi
  (snapshot_values (HV.version_main_args stream) sb0 (allocated m (heap_req (Zpos (xO (xO (xO (xO xH)))))
  (Zpos (xO (xO (xO (xI (xO (xO xH)))))))) sb0)) wd (overwrite (snapshot_ps (HV.version_main_args stream) sb0
  (heap_req (Zpos (xO (xO (xO (xO xH))))) (Zpos (xO (xO (xO (xI (xO (xO xH))))))))) h)) (_ : forall (m : mem)
  (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (p : ptr) (t : list Z) (_ : wi m w h)
  (_ : @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable pval)
  (@gmap_lookup piece piece_eq_dec piece_countable pval) (PName (Zpos (xI (xO xH)))) h) (@Some pval (VName p
  t))), @contract_pre libc_world (libc_setlocale_contract rep requests) (@cons word (WInt (Zpos (xI (xO xH))))
  (@cons word (WPtr null) (@nil word))) m w) (_ : forall (r : call_result) (args : list arg) (s : R.state) (m
  : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (p : ptr) (t : list Z) (trace :
  list event) (ending : call_end) (s' : R.state) (m' : mem) (w' : libc_world) (_ : wi m w h) (_ : @eq (option
  pval) (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece
  piece_eq_dec piece_countable pval) (PName (Zpos (xI (xO xH)))) h) (@Some pval (VName p t))) (_ : @M.E.invoke
  libc_world (libc_setlocale_contract rep requests) r args (@cons word (WInt (Zpos (xI (xO xH)))) (@cons word
  (WPtr null) (@nil word))) s m w trace ending s' m' w'), and (@eq R.state s' s) (and (@eq mem m' m) (and (@eq
  libc_world w' w) (@eq call_end ending (CallReturn (@cons word (WPtr p) (@nil word))))))) (stderr_cell
  errstream : ptr) (_ : @eq (option ptr) (@lookup ptr (TAtom (String (Ascii.Ascii true true false false true
  true true false) (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii
  false false true false false true true false) (String (Ascii.Ascii true false true false false true true
  false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii false true
  false false true true true false) EmptyString))))))) (ge_globals ge)) (@Some ptr stderr_cell)) (_ : forall
  (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : wi m w h), and (@eq
  (option (res unit)) (access_res m (raw_address (ptr_addr stderr_cell) Z0) (ptr_cap stderr_cell) (Zpos (xO
  (xO (xO xH)))) Read (Zpos (xO (xO (xO xH))))) (@Some (res unit) (@RVal unit tt))) (@eq (option ptr)
  (pointer_load_effects m (raw_address (ptr_addr stderr_cell) Z0) (@cons effect AuxRead (@cons effect
  LowerResolve (@cons effect AddressRead (@nil effect))))) (@Some ptr errstream))) (help_ps : list (prod piece
  pval)) (output_spec : forall _ : name, contract libc_world) (_ : forall (pname : ptr) (g : name) (xs : list
  word) (_ : @In (prod name (list word)) (@pair name (list word) g xs) (main_output_args stream errstream
  pname)), @eq (option (contract libc_world)) (registry g) (@Some (contract libc_world) (output_spec g))) (_ :
  forall (pname : ptr) (g : name) (xs : list word) (_ : @In (prod name (list word)) (@pair name (list word) g
  xs) (main_output_args stream errstream pname)), @eq ret_type (@contract_returns libc_world (output_spec g))
  (RClass W)) (_ : forall (pname : ptr) (g : name) (xs : list word) (d : name) (args : list arg) (_ : @In
  (prod name (list word)) (@pair name (list word) g xs) (main_output_args stream errstream pname)) (_ : @eq
  (list class) (@map arg class (fun a : arg => match a return class with | Arg k _ => k end) args) (@replicate
  class (@length word xs) P)), @contract_abi libc_world (output_spec g) (CResult d W) args) (_ : forall (pname
  : ptr) (g : name) (xs : list word) (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable
  pval) (_ : name_ok sargs pname) (_ : @In (prod name (list word)) (@pair name (list word) g xs)
  (main_output_args stream errstream pname)) (_ : forall (l : piece) (v : pval) (_ : @elem_of (prod piece
  pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l v) (@app (prod piece
  pval) help_ps (@flat_map argument (prod piece pval) arg_ps sargs))), @eq (option pval) (@base.lookup piece
  pval (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval)
  l h) (@Some pval v)) (_ : agrees m h) (_ : wi m w h), @contract_pre libc_world (output_spec g) xs m w) (_ :
  forall (pname : ptr) (g : name) (xs : list word) (r : call_result) (args : list arg) (s : R.state) (m : mem)
  (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (trace : list event) (values : list
  word) (s' : R.state) (m' : mem) (w' : libc_world) (_ : @In (prod name (list word)) (@pair name (list word) g
  xs) (main_output_args stream errstream pname)) (_ : agrees m h) (_ : live_disjoint m) (_ : R.ready s m) (_ :
  wi m w h) (_ : @M.E.invoke libc_world (output_spec g) r args xs s m w trace (CallReturn values) s' m' w'),
  and (agrees m' h) (and (live_disjoint m') (and (R.ready s' m') (and (wi m' w' h) (@ex Z (fun n : Z => and
  (@eq (list word) values (@cons word (WInt n) (@nil word))) (and (Z.le Z0 n) (Z.lt n (Z.pow (Zpos (xO xH))
  (Zpos (xO (xO (xO (xO (xO xH))))))))))))))) (_ : forall (g : name) (xs : list word) (_ : @In (prod name
  (list word)) (@pair name (list word) g xs) (emit_output_args stream)), @eq (option (contract libc_world))
  (registry g) (@Some (contract libc_world) (output_spec g))) (_ : forall (g : name) (xs : list word) (_ : @In
  (prod name (list word)) (@pair name (list word) g xs) (emit_output_args stream)), @eq ret_type
  (@contract_returns libc_world (output_spec g)) (RClass W)) (_ : forall (g : name) (xs : list word) (d :
  name) (args : list arg) (_ : @In (prod name (list word)) (@pair name (list word) g xs) (emit_output_args
  stream)) (_ : @eq (list class) (@map arg class (fun a : arg => match a return class with | Arg k _ => k end)
  args) (@replicate class (@length word xs) P)), @contract_abi libc_world (output_spec g) (CResult d W) args)
  (_ : forall (g : name) (xs : list word) (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec
  piece_countable pval) (_ : @In (prod name (list word)) (@pair name (list word) g xs) (emit_output_args
  stream)) (_ : forall (l : piece) (v : pval) (_ : @elem_of (prod piece pval) (list (prod piece pval))
  (@list_elem_of (prod piece pval)) (@pair piece pval l v) help_ps), @eq (option pval) (@base.lookup piece
  pval (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval)
  l h) (@Some pval v)) (_ : agrees m h) (_ : wi m w h), @contract_pre libc_world (output_spec g) xs m w) (_ :
  forall (g : name) (xs : list word) (r : call_result) (args : list arg) (s : R.state) (m : mem) (w :
  libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (trace : list event) (values : list word)
  (s' : R.state) (m' : mem) (w' : libc_world) (_ : @In (prod name (list word)) (@pair name (list word) g xs)
  (emit_output_args stream)) (_ : agrees m h) (_ : live_disjoint m) (_ : R.ready s m) (_ : wi m w h) (_ :
  @M.E.invoke libc_world (output_spec g) r args xs s m w trace (CallReturn values) s' m' w'), and (agrees m'
  h) (and (live_disjoint m') (and (R.ready s' m') (and (wi m' w' h) (@ex Z (fun n : Z => and (@eq (list word)
  values (@cons word (WInt n) (@nil word))) (and (Z.le Z0 n) (Z.lt n (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO
  (xO (xO xH))))))))))))))) (diag_spec : contract libc_world) (_ : @eq (option (contract libc_world))
  (registry (TAtom (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii
  false true false false true true true false) (String (Ascii.Ascii false true false false true true true
  false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii false true false
  false true true true false) EmptyString))))))) (@Some (contract libc_world) diag_spec)) (_ : @eq ret_type
  (@contract_returns libc_world diag_spec) RVoid) (_ : forall (args : list arg) (_ : @eq (list class) (@map
  arg class (fun a : arg => match a return class with | Arg k _ => k end) args) (@cons class W (@cons class W
  (@cons class P (@cons class P (@cons class P (@nil class))))))), @contract_abi libc_world diag_spec CVoid
  args) (_ : forall (q : ptr) (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval)
  (_ : @In ptr q (@map argument ptr arg_ptr sargs)) (_ : forall (l : piece) (v : pval) (_ : @elem_of (prod
  piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l v) (@app (prod
  piece pval) help_ps (@flat_map argument (prod piece pval) arg_ps sargs))), @eq (option pval) (@base.lookup
  piece pval (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable
  pval) l h) (@Some pval v)) (_ : agrees m h) (_ : wi m w h), @contract_pre libc_world diag_spec (@cons word
  (WInt Z0) (@cons word (WInt Z0) (@cons word (WPtr (version_literal (String (Ascii.Ascii false false false
  true false true true false) (String (Ascii.Ascii true false true false false true true false) (String
  (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii false false true true false
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true
  true false false false true false false) (String (Ascii.Ascii true true false false true true true false)
  (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii false true false
  false true true true false) (String (Ascii.Ascii false true true true false true false false) (String
  (Ascii.Ascii true true true false true true false false) (String (Ascii.Ascii true true true false true true
  false false) EmptyString)))))))))))))) (@cons word (WPtr (version_literal (String (Ascii.Ascii false false
  false true false true true false) (String (Ascii.Ascii true false true false false true true false) (String
  (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii false false true true false
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true
  true false false false true false false) (String (Ascii.Ascii true true false false true true true false)
  (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii false true false
  false true true true false) (String (Ascii.Ascii false true true true false true false false) (String
  (Ascii.Ascii true true true false true true false false) (String (Ascii.Ascii false false false true true
  true false false) EmptyString)))))))))))))) (@cons word (WPtr q) (@nil word)))))) m w) (_ : forall (q : ptr)
  (args : list arg) (s : R.state) (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable
  pval) (tr : list event) (vs : list word) (s' : R.state) (m' : mem) (w' : libc_world) (_ : @In ptr q (@map
  argument ptr arg_ptr sargs)) (_ : agrees m h) (_ : live_disjoint m) (_ : R.ready s m) (_ : wi m w h) (_ :
  @M.E.invoke libc_world diag_spec CVoid args (@cons word (WInt Z0) (@cons word (WInt Z0) (@cons word (WPtr
  (version_literal (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii
  true false true false false true true false) (String (Ascii.Ascii false false true true false true true
  false) (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true
  true false true true false) (String (Ascii.Ascii true true false false false true false false) (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true false false) (String (Ascii.Ascii true true true false true true false
  false) (String (Ascii.Ascii true true true false true true false false) EmptyString)))))))))))))) (@cons
  word (WPtr (version_literal (String (Ascii.Ascii false false false true false true true false) (String
  (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii false false true true false
  true true false) (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true
  true true true false true true false) (String (Ascii.Ascii true true false false false true false false)
  (String (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false
  true true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true false false) (String (Ascii.Ascii true true true false true true false
  false) (String (Ascii.Ascii false false false true true true false false) EmptyString)))))))))))))) (@cons
  word (WPtr q) (@nil word)))))) s m w tr (CallReturn vs) s' m' w'), and (@eq (list word) vs (@nil word)) (and
  (agrees m' h) (and (live_disjoint m') (and (R.ready s' m') (wi m' w' h))))) (s0 : argument) (srest : list
  argument) (r3 r4 : region) (x0 x1 y0 : ptr) (old : forall _ : Z, prod ptr (list Z)) (c0 : term) (r80 :
  region) (cs0 : list cap) (a : ptr) (ix b61 : Z) (r61 : region) (Φ : forall _ : val (@nanofil_lang libc_world
  registry ge), uPred (iResUR Σ)) (_ : @eq (list argument) sargs (@cons argument s0 srest)) (_ : argv_caps cs0
  (@map argument ptr arg_ptr sargs)) (_ : and (Z.le Z0 ix) (Z.le ix (Z.of_nat (@length argument sargs)))),
  @bi_emp_valid natSI (uPredI (iResUR Σ)) (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 (block_ps av ar
  Z0 (argv_bytes (@map argument ptr arg_ptr sargs)) cs0)) (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0
  (@flat_map argument (prod piece pval) arg_ps sargs)) (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0
  (getopt_ps a ix)) (@bi_wand _ (uPredI (iResUR Σ)) (@HP.HN.literals Σ gen_heapGS0 r3 r4) (@bi_wand _ (uPredI
  (iResUR Σ)) (@HP.HN.name_cells Σ gen_heapGS0 pn nreg sreg nb sb x0 x1 y0) (@bi_wand _ (uPredI (iResUR Σ))
  (@big_opL natSI (@bi_ofeO natSI (uPredI (iResUR Σ))) (@bi_sep _ (uPredI (iResUR Σ))) (@bi_emp _ (uPredI
  (iResUR Σ))) (@monoid_ops natSI natSI (@bi_ofeO natSI (uPredI (iResUR Σ))) (@bi_sep _ (uPredI (iResUR Σ)))
  (@bi_emp _ (uPredI (iResUR Σ))) (@bi.bi_sep_monoid natSI (uPredI (iResUR Σ)))) Z (fun (_ : nat) (k : Z) =>
  @named Σ gen_heapGS0 k (@fst ptr (list Z) (old k)) (@snd ptr (list Z) (old k))) locale_categories) (@bi_wand
  _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 (codec_ps c0)) (@bi_wand _ (uPredI (iResUR Σ)) (@string Σ
  gen_heapGS0 empty_ptr (Zpos (xO (xO (xO (xO (xI (xO (xI (xO (xI (xO (xO (xO (xI (xO (xO (xO
  xH))))))))))))))))) r80 (@nil Z)) (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 version_ps) (@bi_wand
  _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 help_ps) (@bi_wand _ (uPredI (iResUR Σ)) (@string Σ gen_heapGS0
  (version_literal (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii
  true false true false false true true false) (String (Ascii.Ascii false false true true false true true
  false) (String (Ascii.Ascii false false true true false true true false) (String (Ascii.Ascii true true true
  true false true true false) (String (Ascii.Ascii true true false false false true false false) (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true false false) (String (Ascii.Ascii false true true false true true false
  false) (String (Ascii.Ascii true false false false true true false false) EmptyString))))))))))))) b61 r61
  (@cons Z (Zpos (xI (xO (xI (xO (xO (xI xH))))))) (@cons Z (Zpos (xO (xI (xI (xI (xO (xI xH))))))) (@cons Z
  (Zpos (xI (xI (xI (xI (xI (xO xH))))))) (@nil Z))))) (@bi_wand _ (uPredI (iResUR Σ)) (@bi_later _ (uPredI
  (iResUR Σ)) (@bi_forall _ (uPredI (iResUR Σ)) env (fun e : env => @bi_forall _ (uPredI (iResUR Σ)) Z (fun b4
  : Z => @bi_forall _ (uPredI (iResUR Σ)) Z (fun b6 : Z => @bi_forall _ (uPredI (iResUR Σ)) nat (fun i : nat
  => @bi_forall _ (uPredI (iResUR Σ)) nat (fun k : nat => @bi_forall _ (uPredI (iResUR Σ)) ptr (fun q : ptr =>
  @bi_forall _ (uPredI (iResUR Σ)) (forall _ : Z, prod ptr (list Z)) (fun new : forall _ : Z, prod ptr (list
  Z) => @bi_forall _ (uPredI (iResUR Σ)) term (fun c' : term => @bi_wand _ (uPredI (iResUR Σ)) (@bi_pure _
  (uPredI (iResUR Σ)) (and (start_vars e (Z.of_nat (@length argument sargs)) av b4 b6) (and (@eq (option word)
  (@lookup word (TAtom (String (Ascii.Ascii true true false false false true true false) (String (Ascii.Ascii
  false false false true false true true false) (String (Ascii.Ascii true true false true false true true
  false) (String (Ascii.Ascii true false false false true true false false) EmptyString))))) e) (@Some word
  (WPtr (mkPtr b4 (Obj b4))))) (and (fresh_ok b4) (and (fresh_ok b6) (and (le i (@length Z (arg_text s0)))
  (and (le k (@length Z (arg_text s0))) (or (@eq ptr q (mkPtr Z0 CNone)) (@eq ptr q (@fst ptr (list Z) (new
  (Zpos (xO (xI xH)))))))))))))) (@bi_wand _ (uPredI (iResUR Σ)) (@HP.HN.literals Σ gen_heapGS0 r3 r4)
  (@bi_wand _ (uPredI (iResUR Σ)) (@big_opL natSI (@bi_ofeO natSI (uPredI (iResUR Σ))) (@bi_sep _ (uPredI
  (iResUR Σ))) (@bi_emp _ (uPredI (iResUR Σ))) (@monoid_ops natSI natSI (@bi_ofeO natSI (uPredI (iResUR Σ)))
  (@bi_sep _ (uPredI (iResUR Σ))) (@bi_emp _ (uPredI (iResUR Σ))) (@bi.bi_sep_monoid natSI (uPredI (iResUR
  Σ)))) Z (fun (_ : nat) (k0 : Z) => @lent Σ gen_heapGS0 k0 (@fst ptr (list Z) (new k0)) (@snd ptr (list Z)
  (new k0))) locale_categories) (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 (codec_ps c')) (@bi_wand _
  (uPredI (iResUR Σ)) (@string Σ gen_heapGS0 empty_ptr (Zpos (xO (xO (xO (xO (xI (xO (xI (xO (xI (xO (xO (xO
  (xI (xO (xO (xO xH))))))))))))))))) r80 (@nil Z)) (@bi_wand _ (uPredI (iResUR Σ)) (@bytes Σ gen_heapGS0 b4
  (Zpos (xO (xO (xO xH)))) (@replicate Z (S (S (S (S (S (S (S (S O)))))))) Z0)) (@bi_wand _ (uPredI (iResUR
  Σ)) (@auxes Σ gen_heapGS0 b4 (Zpos xH) (@replicate cap (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
  O))))))))))))))) CNone)) (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.live Σ gen_heapGS0 b6 (mkRegion b6 (Z.add b6
  (Zpos (xO (xO (xO (xO xH)))))) Heap Live)) (@bi_wand _ (uPredI (iResUR Σ)) (@bytes Σ gen_heapGS0 b6 Z0
  (@replicate Z (S (S (S (S (S (S (S (S O)))))))) Z0)) (@bi_wand _ (uPredI (iResUR Σ)) (@bytes Σ gen_heapGS0
  b6 (Zpos (xO (xO (xO xH)))) (@replicate Z (S (S (S (S (S (S (S (S O)))))))) Z0)) (@bi_wand _ (uPredI (iResUR
  Σ)) (@auxes Σ gen_heapGS0 b6 Z0 (clear_slots Z0 (@replicate cap (S (S (S (S (S (S (S (S O)))))))) CNone)))
  (@bi_wand _ (uPredI (iResUR Σ)) (@auxes Σ gen_heapGS0 b6 (Zpos (xO (xO (xO xH)))) (@replicate cap (S (S (S
  (S (S (S (S (S O)))))))) CNone)) (@operand_exit hlc Σ invGS_gen0 gen_heapGS0 registry wi ge av ar sargs b4
  b6 (String (Ascii.Ascii true false false true false true true false) (String (Ascii.Ascii true true true
  false true true true false) (String (Ascii.Ascii true true true true true false true false) (String
  (Ascii.Ascii true false false false true true false false) (String (Ascii.Ascii false true true true false
  true false false) (String (Ascii.Ascii false true false true false true true false) (String (Ascii.Ascii
  true true true true false true true false) (String (Ascii.Ascii true false false true false true true false)
  (String (Ascii.Ascii false true true true false true true false) EmptyString))))))))) (String (Ascii.Ascii
  true false false true false true true false) (String (Ascii.Ascii true true true false true true true false)
  (String (Ascii.Ascii true true true true true false true false) (String (Ascii.Ascii true false false false
  true true false false) (String (Ascii.Ascii false true true true false true false false) (String
  (Ascii.Ascii false false true true false false true false) (String (Ascii.Ascii false true true false true
  true false false) (String (Ascii.Ascii false false false false true true false false) EmptyString))))))))
  (fun lose i0 : Z => and (@eq Z lose Z0) (@eq Z i0 (Z.of_nat (@length argument sargs))))
  Φ)))))))))))))))))))))) (@wp (uPred (iResUR Σ)) (language.expr (@nanofil_lang libc_world registry ge)) (val
  (@nanofil_lang libc_world registry ge)) stuckness (@wp' hlc (@nanofil_lang libc_world registry ge) Σ
  (@main_irisGS hlc Σ invGS_gen0 gen_heapGS0 registry wi ge)) NotStuck (@top coPset coPset_top) (ERun
  (invocation main_fn (@cons word (WInt (Z.of_nat (@length argument sargs))) (@cons word (WPtr (mkPtr av (Obj
  av))) (@nil word)))) : language.expr (@nanofil_lang libc_world registry ge)) Φ))))))))))))).
Arguments main_to_join {hlc Σ invGS_gen0 gen_heapGS0} (registry wi)%_function_scope {SafepointStable0}
  ge Hlinked Kalloc%_function_scope Hmemset Kmemset%_function_scope Hstrrchr Hmemcmp Hstrncmp
  pn nreg sreg (nb sb)%_Z_scope Hnb Hsb Hpn_end Hnb_cell Hsb_cell Kpn Knb Ksb (rep requests)%_function_scope
  Hsetlocale (Hlent Hset_pre Kset Kpstore)%_function_scope atexit_spec Hatexit Hatexit_ret
  Hatexit_abi (Hatexit_pre Katexit)%_function_scope av%_Z_scope ar sargs%_list_scope Hav Hargc
  Hargs (initialized running grequests transition)%_function_scope Hgetopt optarg_cell optind_cell
  (Hgetopt_wi Htable Hgetopt_env Hgetopt_apart Kgetopt)%_function_scope Hoptarg_g Hcells Hoptind_g
  exit_spec Hexit (Hexit_abi Hexit_pre Hexit_post)%_function_scope stdout_cell stream Hstdout_g
  wi_stdout%_function_scope version_ps%_list_scope
  (author_reg Hauthor_live version_spec Hversion_reg Hversion_ret Hversion_abi Hversion_pre Hversion_frame
   Kversion_alloc Kversion_store Kversion_cursor Kversion_snapshot Hquery_pre Hquery)%_function_scope
  stderr_cell errstream Hstderr_g wi_stderr%_function_scope help_ps%_list_scope
  (output_spec Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame Houtput_reg Houtput_ret Houtput_abi Houtput_pre
   Houtput_frame)%_function_scope
  diag_spec Hdiag_reg Hdiag_ret (Hdiag_abi Hdiag_pre Hdiag_post)%_function_scope s0 srest%_list_scope
  r3 r4 x0 x1 y0 old%_function_scope c0 r80 cs0%_list_scope a (ix b61)%_Z_scope r61 Φ%_function_scope
  _ _ _.
End HM.
Import HM HM.LG0 HM.LG0.L HM.HLo.HL HM.HLo.HL.ML HM.HLo.HL.ML.CSL.
Module HC.
Module LB.
Definition errno_contract (rep : mem -> libc_world -> Prop) : contract libc_world :=
  errno_location_contract libc_world (fun w => libc_errno (fst w)) (libc_ready rep).
End LB.
Definition mbs_post (l : nat) (r : Z) (ws xe : list Z) : Prop :=
  (r = 2 ^ 64 - 1 /\ le_value xe = 84) \/
  (exists k : nat, r = Z.of_nat k /\ (k <= l)%nat /\ wide_ok (take (4 * k) ws) /\
     le_value (take 4 (drop (4 * k) ws)) = 0).
Definition conv_irisGS {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) (ge : genv) := nanofil_irisGS registry wi ge.
Parameter rpl_mbsrtowcs_spec :
  forall {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : @gen_heapGS piece pval Σ
  piece_eq_dec piece_countable} (registry : forall _ : name, option (contract libc_world)) (wi : forall (_ :
  mem) (_ : libc_world) (_ : @gmap piece piece_eq_dec piece_countable pval), Prop) {_ : @LG0.SafepointStable
  libc_world wi} (ge : genv) (valid : forall (_ : term) (_ : list Z), Prop) (audit : forall _ : term, option
  audited_codec) (rep : forall (_ : mem) (_ : libc_world), Prop) (requests : forall (_ : list word) (_ : mem)
  (_ : libc_world) (_ : Z) (_ : Z), Prop) (_ : @eq (option (contract libc_world)) (registry (TAtom (String
  (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii false true false false false
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false false true false true true true false) (String (Ascii.Ascii true true true true false true true false)
  (String (Ascii.Ascii true true true false true true true false) (String (Ascii.Ascii true true false false
  false true true false) EmptyString))))))))) (@Some (contract libc_world) (mbrtowc_contract valid audit rep
  requests))) (_ : mbstate_zero_valid valid) (_ : mbstate_valid_bytes valid) (errno : ptr) (_ : forall (m :
  mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : wi m w h), and (libc_ready
  rep m w) (and (codec_current (libc_locale (@fst libc_payload Shutdown.shutdown_state w)) h) (and (@eq ptr
  (libc_errno (@fst libc_payload Shutdown.shutdown_state w)) errno) (libc_private m w h)))) (_ : forall (m :
  mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : wi m w h),
  hello_codec_profile audit w) (_ : forall (r : call_result) (args : list arg) (out src : ptr) (n : Z) (state
  : ptr) (s : R.state) (m : mem) (w : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (trace :
  list event) (values : list word) (s' : R.state) (m' : mem) (w' : libc_world) (bo : Z) (ro : region) (oo : Z)
  (xo : list Z) (co : list cap) (bs : Z) (rs : region) (os : Z) (ys : list Z) (cs : list cap) (be : Z) (re :
  region) (oe : Z) (xe : list Z) (ce : list cap) (_ : @L.M.E.invoke libc_world (mbrtowc_contract valid audit
  rep requests) r args (@cons word (WPtr out) (@cons word (WPtr src) (@cons word (WInt n) (@cons word (WPtr
  state) (@nil word))))) s m w trace (CallReturn values) s' m' w') (_ : forall (l : piece) (v : pval) (_ :
  @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l v)
  (@app (prod piece pval) (block_ps bo ro oo xo co) (@app (prod piece pval) (block_ps bs rs os ys cs)
  (block_ps be re oe xe ce)))), @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec
  piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some pval v)) (_ : wi m
  w h), wi m' w' (overwrite (@app (prod piece pval) (block_ps bo ro oo (mem_bytes m' (Z.add bo oo) (S (S (S (S
  O))))) (mem_auxes m' (Z.add bo oo) (S (S (S (S O)))))) (@app (prod piece pval) (block_ps bs rs os (mem_bytes
  m' (Z.add bs os) (S (S (S (S (S (S (S (S O))))))))) (mem_auxes m' (Z.add bs os) (S (S (S (S (S (S (S (S
  O)))))))))) (block_ps be re oe (mem_bytes m' (Z.add be oe) (S (S (S (S O))))) (mem_auxes m' (Z.add be oe) (S
  (S (S (S O)))))))) h)) (_ : hello_linked ge) (_ : forall (m : mem) (w : libc_world) (h : @gmap piece
  piece_eq_dec piece_countable pval) (k : Z) (p : ptr) (t : list Z) (_ : wi m w h) (_ : live_disjoint m) (_ :
  objects_fit (m_regions m)) (_ : freed_empty (m_regions m)) (_ : @eq (option pval) (@base.lookup piece pval
  (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval)
  (PName k) h) (@Some pval (VName p t))), lent_at m h p t) (set_spec : contract libc_world) (_ : @eq (option
  (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true true false false true true true false)
  (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii false false true
  false true true true false) (String (Ascii.Ascii false false true true false true true false) (String
  (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true true false false false
  true true false) (String (Ascii.Ascii true false false false false true true false) (String (Ascii.Ascii
  false false true true false true true false) (String (Ascii.Ascii true false true false false true true
  false) EmptyString))))))))))) (@Some (contract libc_world) set_spec)) (_ : @eq ret_type (@contract_returns
  libc_world set_spec) (RClass P)) (_ : forall (d : name) (c v : value), @contract_abi libc_world set_spec
  (CResult d P) (@cons arg (Arg W c) (@cons arg (Arg P v) (@nil arg)))) (_ : forall (m : mem) (w : libc_world)
  (h : @gmap piece piece_eq_dec piece_countable pval) (k : Z) (p : ptr) (t : list Z) (z : ptr) (_ : wi m w h)
  (_ : @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable pval)
  (@gmap_lookup piece piece_eq_dec piece_countable pval) (PName k) h) (@Some pval (VName p t))) (_ : @eq Z
  (ptr_addr z) Z0), @contract_pre libc_world set_spec (@cons word (WInt k) (@cons word (WPtr z) (@nil word)))
  m w) (_ : forall (r : call_result) (args : list arg) (s : R.state) (m : mem) (w : libc_world) (h : @gmap
  piece piece_eq_dec piece_countable pval) (k : Z) (p : ptr) (t : list Z) (z : ptr) (trace : list event)
  (ending : call_end) (s' : R.state) (m' : mem) (w' : libc_world) (_ : wi m w h) (_ : @eq (option pval)
  (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec
  piece_countable pval) (PName k) h) (@Some pval (VName p t))) (_ : @eq Z (ptr_addr z) Z0) (_ : @L.M.E.invoke
  libc_world set_spec r args (@cons word (WInt k) (@cons word (WPtr z) (@nil word))) s m w trace ending s' m'
  w'), and (@eq R.state s' s) (and (@eq mem m' m) (and (@eq libc_world w' w) (@eq call_end ending (CallReturn
  (@cons word (WPtr p) (@nil word))))))) (_ : @eq (option (contract libc_world)) (registry (TAtom (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false false true true false true true false) (String (Ascii.Ascii true false true false false true true
  false) (String (Ascii.Ascii false true true true false true true false) EmptyString)))))))) (@Some (contract
  libc_world) (strlen_contract libc_world))) (_ : @eq (option (contract libc_world)) (registry (TAtom (String
  (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii true false true false false
  true true false) (String (Ascii.Ascii true false true true false true true false) (String (Ascii.Ascii true
  true false false false true true false) (String (Ascii.Ascii false false false false true true true false)
  (String (Ascii.Ascii true false false true true true true false) EmptyString)))))))) (@Some (contract
  libc_world) (memcpy_contract libc_world))) (_ : @eq (option (contract libc_world)) (registry (TAtom (String
  (Ascii.Ascii true true false false true true true false) (String (Ascii.Ascii false false true false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii true
  true false false false true true false) (String (Ascii.Ascii true false true true false true true false)
  (String (Ascii.Ascii false false false false true true true false) EmptyString)))))))) (@Some (contract
  libc_world) (strcmp_contract libc_world))) (_ : forall (b : Z) (reg : region) (o : Z) (xs : list Z) (cs :
  list cap) (s : ptr) (n : Z) (m m' : mem) (wd : libc_world) (h : @gmap piece piece_eq_dec piece_countable
  pval) (ys : list Z) (_ : copy_result m (mkPtr (Z.add b o) (Obj b)) s n m') (_ : forall (l : piece) (v :
  pval) (_ : @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair
  piece pval l v) (block_ps b reg o xs cs)), @eq (option pval) (@base.lookup piece pval (@gmap piece
  piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some pval
  v)) (_ : wi m wd h) (_ : @eq nat (@length Z ys) (@length Z xs)), wi m' wd (overwrite (block_ps b reg o ys
  (slots_after m' b o (@length Z xs))) h)) (_ : forall (b : Z) (reg : region) (o x y : Z) (m : mem) (wd :
  libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : forall (l : piece) (v : pval) (_ :
  @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l v)
  (@cons (prod piece pval) (@pair piece pval (PLive b) (VLive reg)) (@cons (prod piece pval) (@pair piece pval
  (PByte b o) (VByte x)) (@nil (prod piece pval))))), @eq (option pval) (@base.lookup piece pval (@gmap piece
  piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some pval
  v)) (_ : wi m wd h), wi (store_bytes m (Z.add b o) (Zpos xH) y) wd (overwrite (@cons (prod piece pval)
  (@pair piece pval (PLive b) (VLive reg)) (@cons (prod piece pval) (@pair piece pval (PByte b o) (VByte
  (Z.modulo y (Zpos (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))) (@nil (prod piece pval)))) h)) (_ : forall
  (b : Z) (reg : region) (o : Z) (xs : list Z) (y : Z) (m : mem) (wd : libc_world) (h : @gmap piece
  piece_eq_dec piece_countable pval) (_ : forall (l : piece) (v : pval) (_ : @elem_of (prod piece pval) (list
  (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l v) (@cons (prod piece pval) (@pair
  piece pval (PLive b) (VLive reg)) (byte_ps b o xs))), @eq (option pval) (@base.lookup piece pval (@gmap
  piece piece_eq_dec piece_countable pval) (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some
  pval v)) (_ : wi m wd h), wi (store_bytes m (Z.add b o) (Zpos (xO (xO xH))) y) wd (overwrite (@cons (prod
  piece pval) (@pair piece pval (PLive b) (VLive reg)) (byte_ps b o (le_bytes y (S (S (S (S O))))))) h)) (_ :
  forall (q : alloc_req) (m : mem) (wd : libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (base
  : Z) (_ : fresh m q base) (_ : wi m wd h), wi (allocated m q base) wd (overwrite (obj_ps base q) h)) (_ :
  @eq (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true false true true false true
  true false) (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii true
  false true true false true true false) (String (Ascii.Ascii true true false false false true true false)
  (String (Ascii.Ascii false false false true false true true false) (String (Ascii.Ascii false true false
  false true true true false) EmptyString)))))))) (@Some (contract libc_world) (memchr_contract libc_world)))
  (_ : @eq (option (contract libc_world)) (registry (TAtom (String (Ascii.Ascii true true true true true false
  true false) (String (Ascii.Ascii true true true true true false true false) (String (Ascii.Ascii true false
  true false false true true false) (String (Ascii.Ascii false true false false true true true false) (String
  (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii false true true true false
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true
  true true true true false true false) (String (Ascii.Ascii false false true true false true true false)
  (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true true false false
  false true true false) (String (Ascii.Ascii true false false false false true true false) (String
  (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii true false false true false
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii false
  true true true false true true false) EmptyString)))))))))))))))))) (@Some (contract libc_world)
  (LB.errno_contract rep))) (_ : forall (b : Z) (reg : region) (o : Z) (x xp : ptr) (m : mem) (wd :
  libc_world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : forall (l : piece) (v : pval) (_ :
  @elem_of (prod piece pval) (list (prod piece pval)) (@list_elem_of (prod piece pval)) (@pair piece pval l v)
  (@app (prod piece pval) (@cons (prod piece pval) (@pair piece pval (PLive b) (VLive reg)) (@nil (prod piece
  pval))) (@cons (prod piece pval) (@pair piece pval (PAux b o) (VAux (ptr_cap x))) (cell b o (ptr_addr
  x))))), @eq (option pval) (@base.lookup piece pval (@gmap piece piece_eq_dec piece_countable pval)
  (@gmap_lookup piece piece_eq_dec piece_countable pval) l h) (@Some pval v)) (_ : wi m wd h), wi (store_bytes
  (store_aux m (Z.add b o) (ptr_cap xp)) (Z.add b o) (Zpos (xO (xO (xO xH)))) (ptr_addr xp)) wd (overwrite
  (@app (prod piece pval) (@cons (prod piece pval) (@pair piece pval (PLive b) (VLive reg)) (@nil (prod piece
  pval))) (@cons (prod piece pval) (@pair piece pval (PAux b o) (VAux (ptr_cap xp))) (cell b o (ptr_addr
  xp)))) h)) (p : ptr) (b : Z) (reg : region) (bs : list Z) (bd : Z) (rd : region) (ws : list Z) (cws : list
  cap) (sb : Z) (sr : region) (so : Z) (ys : list Z) (cs : list cap) (be : Z) (re : region) (oe : Z) (xe :
  list Z) (ce : list cap) (spb : Z) (spr : region) (spo : Z) (codec : term) (dq : dfrac) (p0 : ptr) (t0 : list
  Z) (rc rp : region) (Φ : forall _ : outcome, @bi_car _ (uPredI (iResUR Σ))) (_ : @eq ptr errno (mkPtr (Z.add
  be oe) (Obj be))) (_ : Z.lt Z0 bd) (_ : @eq Z (Z.modulo bd (Zpos (xO (xO xH)))) Z0) (_ : Z.le (Z.add bd
  (Z.mul (Zpos (xO (xO xH))) (Z.add (Z.of_nat (@length Z bs)) (Zpos xH)))) (r_end rd)) (_ : Z.le (r_end rd)
  (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xI xH)))))))) (_ : Z.lt Z0 sb) (_ : Z.le Z0 so) (_ : @eq Z
  (Z.modulo (Z.add sb so) (Zpos (xO (xO xH)))) Z0) (_ : Z.le (Z.add (Z.add sb so) (Zpos (xO (xO (xO xH)))))
  (r_end sr)) (_ : Z.le (r_end sr) (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xI xH)))))))) (_ : Z.lt Z0
  spb) (_ : Z.le Z0 spo) (_ : @eq Z (Z.modulo (Z.add spb spo) (Zpos (xO (xO (xO xH))))) Z0) (_ : Z.le (Z.add
  (Z.add spb spo) (Zpos (xO (xO (xO xH))))) (r_end spr)) (_ : Z.le (r_end spr) (Z.pow (Zpos (xO xH)) (Zpos (xO
  (xO (xO (xO (xI xH)))))))) (_ : Z.lt Z0 be) (_ : Z.le Z0 oe) (_ : Z.le (Z.add (Z.add be oe) (Zpos (xO (xO
  xH)))) (r_end re)) (_ : Z.le (r_end re) (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xI xH)))))))) (_ : @eq
  nat (@length Z ws) (Init.Nat.mul (S (S (S (S O)))) (Init.Nat.add (@length Z bs) (S O)))) (_ : @eq nat
  (@length cap cws) (Init.Nat.mul (S (S (S (S O)))) (Init.Nat.add (@length Z bs) (S O)))) (_ : valid codec ys)
  (_ : @eq Z (le_value (@firstn Z (S (S (S (S O)))) ys)) Z0) (_ : @eq nat (@length Z ys) (S (S (S (S (S (S (S
  (S O))))))))) (_ : @eq nat (@length cap cs) (S (S (S (S (S (S (S (S O))))))))) (_ : @eq nat (@length Z xe)
  (S (S (S (S O))))) (_ : @eq nat (@length cap ce) (S (S (S (S O))))), @bi_emp_valid natSI (uPredI (iResUR Σ))
  (@bi_wand _ (uPredI (iResUR Σ)) (@LL.lent Σ gen_heapGS0 Z0 p0 t0) (@bi_wand _ (uPredI (iResUR Σ))
  (@CSL.string Σ gen_heapGS0 c_ptr (Zpos (xO (xO (xO (xO (xO (xI (xO (xO (xI (xO (xO (xO (xO (xO (xO (xO
  xH))))))))))))))))) rc c_bytes) (@bi_wand _ (uPredI (iResUR Σ)) (@CSL.string Σ gen_heapGS0 posix_ptr (Zpos
  (xO (xO (xO (xO (xO (xO (xI (xO (xI (xO (xO (xO (xO (xO (xO (xO xH))))))))))))))))) rp posix_bytes)
  (@bi_wand _ (uPredI (iResUR Σ)) (@pointsto piece piece_eq_dec piece_countable pval Σ gen_heapGS0 (PName
  codec_key) dq (VCodec codec)) (@bi_wand _ (uPredI (iResUR Σ)) (@CSL.string Σ gen_heapGS0 p b reg bs)
  (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.live Σ gen_heapGS0 bd rd) (@bi_wand _ (uPredI (iResUR Σ)) (@ML.bytes Σ
  gen_heapGS0 bd Z0 ws) (@bi_wand _ (uPredI (iResUR Σ)) (@ML.auxes Σ gen_heapGS0 bd Z0 cws) (@bi_wand _
  (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 (block_ps sb sr so ys cs)) (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ
  gen_heapGS0 (block_ps be re oe xe ce)) (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.live Σ gen_heapGS0 spb spr)
  (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.pcell Σ gen_heapGS0 spb spo p) (@bi_wand _ (uPredI (iResUR Σ))
  (@bi_forall _ (uPredI (iResUR Σ)) Z (fun r : Z => @bi_forall _ (uPredI (iResUR Σ)) (list Z) (fun ws' : list
  Z => @bi_forall _ (uPredI (iResUR Σ)) (list cap) (fun cws' : list cap => @bi_forall _ (uPredI (iResUR Σ))
  (list Z) (fun ys' : list Z => @bi_forall _ (uPredI (iResUR Σ)) (list cap) (fun cs' : list cap => @bi_forall
  _ (uPredI (iResUR Σ)) (list Z) (fun xe' : list Z => @bi_forall _ (uPredI (iResUR Σ)) (list cap) (fun ce' :
  list cap => @bi_forall _ (uPredI (iResUR Σ)) ptr (fun x' : ptr => @bi_wand _ (uPredI (iResUR Σ)) (@bi_pure _
  (uPredI (iResUR Σ)) (and (mbs_post (@length Z bs) r ws' xe') (and (@eq nat (@length Z ws') (Init.Nat.mul
  (S (S (S (S O)))) (Init.Nat.add (@length Z bs) (S O)))) (@eq nat (@length Z xe') (S (S (S (S O))))))))
  (@bi_wand _ (uPredI (iResUR Σ)) (@CSL.string Σ gen_heapGS0 c_ptr (Zpos (xO (xO (xO (xO (xO (xI (xO (xO (xI
  (xO (xO (xO (xO (xO (xO (xO xH))))))))))))))))) rc c_bytes) (@bi_wand _ (uPredI (iResUR Σ)) (@CSL.string Σ
  gen_heapGS0 posix_ptr (Zpos (xO (xO (xO (xO (xO (xO (xI (xO (xI (xO (xO (xO (xO (xO (xO (xO
  xH))))))))))))))))) rp posix_bytes) (@bi_wand _ (uPredI (iResUR Σ)) (@pointsto piece piece_eq_dec
  piece_countable pval Σ gen_heapGS0 (PName codec_key) dq (VCodec codec)) (@bi_wand _ (uPredI (iResUR Σ))
  (@CSL.string Σ gen_heapGS0 p b reg bs) (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.live Σ gen_heapGS0 bd rd)
  (@bi_wand _ (uPredI (iResUR Σ)) (@ML.bytes Σ gen_heapGS0 bd Z0 ws') (@bi_wand _ (uPredI (iResUR Σ))
  (@ML.auxes Σ gen_heapGS0 bd Z0 cws') (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 (block_ps sb sr so
  ys' cs')) (@bi_wand _ (uPredI (iResUR Σ)) (@pts Σ gen_heapGS0 (block_ps be re oe xe' ce')) (@bi_wand _
  (uPredI (iResUR Σ)) (@LG0.live Σ gen_heapGS0 spb spr) (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.pcell Σ
  gen_heapGS0 spb spo x') (Φ (Ret (WInt r))))))))))))))))))))))) (@wp (@bi_car _ (uPredI (iResUR Σ)))
  (language.expr (@L.nanofil_lang libc_world registry ge)) outcome stuckness (@wp' hlc (@L.nanofil_lang
  libc_world registry ge) Σ (@conv_irisGS hlc Σ invGS_gen0 gen_heapGS0 registry wi ge)) NotStuck (@top
  coPset coPset_top) (L.ERun (invocation mbs_fn (@cons word (WPtr (mkPtr bd (Obj bd))) (@cons word (WPtr
  (mkPtr (Z.add spb spo) (Obj spb))) (@cons word (WInt (Z.add (Z.of_nat (@length Z bs)) (Zpos xH))) (@cons
  word (WPtr (mkPtr (Z.add sb so) (Obj sb))) (@nil word)))))) : language.expr (@L.nanofil_lang libc_world
  registry ge)) Φ)))))))))))))).
Arguments rpl_mbsrtowcs_spec {hlc Σ invGS_gen0 gen_heapGS0} (registry wi)%_function_scope
  {SafepointStable0} ge (valid audit rep requests)%_function_scope Hmbrtowc Hvalid0 Hbytes
  errno (Hlibc Haudit Kmbrtowc)%_function_scope Hlinked wi_lent%_function_scope set_spec Hset
  Hset_ret (Hset_abi Hset_pre Hset_query)%_function_scope Hstrlen Hmemcpy Hstrcmp
  (Kcopy Kbyte Kstore Kalloc)%_function_scope Hmemchr Herrno_reg Kpstore%_function_scope p
  b%_Z_scope reg bs%_list_scope bd%_Z_scope rd (ws cws)%_list_scope sb%_Z_scope sr so%_Z_scope
  (ys cs)%_list_scope be%_Z_scope re oe%_Z_scope (xe ce)%_list_scope spb%_Z_scope spr spo%_Z_scope
  codec dq p0 t0%_list_scope rc rp Φ%_function_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  _ _ _ _ _ _ _ _.
End HC.
Module HCl.
Definition close_irisGS {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) (ge : genv) := nanofil_irisGS registry wi ge.
Parameter wp_close_errno :
  forall {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : @gen_heapGS piece pval Σ
  piece_eq_dec piece_countable} {world : Type} (registry : forall _ : name, option (contract world)) (wi :
  forall (_ : mem) (_ : world) (_ : @gmap piece piece_eq_dec piece_countable pval), Prop) {_ :
  @LG0.SafepointStable world wi} (ge : genv) (eb eo : Z) (cell : forall _ : world, ptr) (rep : forall (_ :
  mem) (_ : world), Prop) (_ : @eq (option (contract world)) (registry (TAtom (String (Ascii.Ascii true true
  true true true false true false) (String (Ascii.Ascii true true true true true false true false) (String
  (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii false true false false true
  true true false) (String (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii
  false true true true false true true false) (String (Ascii.Ascii true true true true false true true false)
  (String (Ascii.Ascii true true true true true false true false) (String (Ascii.Ascii false false true true
  false true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii
  true true false false false true true false) (String (Ascii.Ascii true false false false false true true
  false) (String (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii true false
  false true false true true false) (String (Ascii.Ascii true true true true false true true false) (String
  (Ascii.Ascii false true true true false true true false) EmptyString)))))))))))))))))) (@Some (contract
  world) (errno_location_contract world cell rep))) (_ : hello_linked ge) (_ : forall (m : mem) (w : world) (h
  : @gmap piece piece_eq_dec piece_countable pval) (_ : wi m w h), @eq ptr (cell w) (mkPtr (Z.add eb eo) (Obj
  eb))) (_ : forall (m : mem) (w : world) (h : @gmap piece piece_eq_dec piece_countable pval) (_ : wi m w h),
  and (rep m w) (errno_cell m (cell w))) (f : func) (e : list (prod name word)) (ls : list (prod name (option
  Z))) (lab d : name) (rest : list inst) (j : jump) (Φ : forall _ : val (@L.nanofil_lang world registry ge),
  @bi_car _ (uPredI (iResUR Σ))), @bi_emp_valid natSI (uPredI (iResUR Σ)) (@bi_wand _ (uPredI (iResUR Σ))
  (@bi_later _ (uPredI (iResUR Σ)) (@wp (@bi_car _ (uPredI (iResUR Σ))) (language.expr (@L.nanofil_lang world
  registry ge)) (val (@L.nanofil_lang world registry ge)) stuckness (@wp' hlc (@L.nanofil_lang world registry
  ge) Σ (@close_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry wi ge)) NotStuck (@top coPset
  coPset_top) (L.ERun (mkFrame f (@put word d (WPtr (mkPtr (Z.add eb eo) (Obj eb))) e) ls (@None reason) (Exec
  lab rest j)) : language.expr (@L.nanofil_lang world registry ge)) Φ)) (@wp (@bi_car _ (uPredI (iResUR Σ)))
  (language.expr (@L.nanofil_lang world registry ge)) (val (@L.nanofil_lang world registry ge)) stuckness
  (@wp' hlc (@L.nanofil_lang world registry ge) Σ (@close_irisGS hlc Σ invGS_gen0 gen_heapGS0 world
  registry wi ge)) NotStuck (@top coPset coPset_top) (L.ERun (mkFrame f e ls (@None reason) (Exec lab (@cons
  inst (Call (CResult d P) (Global (TAtom (String (Ascii.Ascii true true true true true false true false)
  (String (Ascii.Ascii true true true true true false true false) (String (Ascii.Ascii true false true false
  false true true false) (String (Ascii.Ascii false true false false true true true false) (String
  (Ascii.Ascii false true false false true true true false) (String (Ascii.Ascii false true true true false
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true
  true true true true false true false) (String (Ascii.Ascii false false true true false true true false)
  (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii true true false false
  false true true false) (String (Ascii.Ascii true false false false false true true false) (String
  (Ascii.Ascii false false true false true true true false) (String (Ascii.Ascii true false false true false
  true true false) (String (Ascii.Ascii true true true true false true true false) (String (Ascii.Ascii false
  true true true false true true false) EmptyString)))))))))))))))))) (@nil arg)) rest) j)) : language.expr
  (@L.nanofil_lang world registry ge)) Φ)).
Arguments wp_close_errno {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge (eb eo)%_Z_scope (cell rep)%_function_scope Herrno Hlinked (Hcell Hrep)%_function_scope
  f (e ls)%_list_scope lab d rest%_list_scope j Φ%_function_scope.
Parameter wp_close_load_w :
  forall {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : @gen_heapGS piece pval Σ
  piece_eq_dec piece_countable} {world : Type} (registry : forall _ : name, option (contract world)) (wi :
  forall (_ : mem) (_ : world) (_ : @gmap piece piece_eq_dec piece_countable pval), Prop) {_ :
  @LG0.SafepointStable world wi} (ge : genv) (f : func) (e : env) (ls : list (prod name (option Z))) (lab d :
  name) (v : value) (rest : list inst) (j : jump) (b : Z) (reg : region) (o : Z) (xs : list Z) (Φ : forall _ :
  val (@L.nanofil_lang world registry ge), @bi_car _ (uPredI (iResUR Σ))) (_ : @eq (option word) (value_x ge e
  A v) (@Some word (WPtr (mkPtr (Z.add b o) (Obj b))))) (_ : and (Z.le Z0 (Z.add b o)) (Z.lt (Z.add b o)
  (Z.pow (Zpos (xO xH)) (Zpos (xO (xO (xO (xO (xO (xO xH)))))))))) (_ : @eq nat (@length Z xs) (S (S (S (S
  O))))), @bi_emp_valid natSI (uPredI (iResUR Σ)) (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.live Σ gen_heapGS0 b
  reg) (@bi_wand _ (uPredI (iResUR Σ)) (@ML.bytes Σ gen_heapGS0 b o xs) (@bi_wand _ (uPredI (iResUR Σ))
  (@bi_later _ (uPredI (iResUR Σ)) (@bi_wand _ (uPredI (iResUR Σ)) (@LG0.live Σ gen_heapGS0 b reg) (@bi_wand _
  (uPredI (iResUR Σ)) (@ML.bytes Σ gen_heapGS0 b o xs) (@wp (@bi_car _ (uPredI (iResUR Σ))) (language.expr
  (@L.nanofil_lang world registry ge)) (val (@L.nanofil_lang world registry ge)) stuckness (@wp' hlc
  (@L.nanofil_lang world registry ge) Σ (@close_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry wi ge))
  NotStuck (@top coPset coPset_top) (L.ERun (mkFrame f (@put word d (WInt (close_w xs)) e) ls (@None reason)
  (Exec lab rest j)) : language.expr (@L.nanofil_lang world registry ge)) Φ)))) (@wp (@bi_car _ (uPredI
  (iResUR Σ))) (language.expr (@L.nanofil_lang world registry ge)) (val (@L.nanofil_lang world registry ge))
  stuckness (@wp' hlc (@L.nanofil_lang world registry ge) Σ (@close_irisGS hlc Σ invGS_gen0 gen_heapGS0
  world registry wi ge)) NotStuck (@top coPset coPset_top) (L.ERun (mkFrame f e ls (@None reason) (Exec lab
  (@cons inst (Let d W (RawLoad (LdNarrow Sw) Z0) (@cons value v (@nil value))) rest) j)) : language.expr
  (@L.nanofil_lang world registry ge)) Φ)))).
Arguments wp_close_load_w {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge f e ls%_list_scope lab d v rest%_list_scope j b%_Z_scope reg o%_Z_scope
  xs%_list_scope Φ%_function_scope _ _ _.
End HCl.
Definition join_irisGS (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) (ge : genv)
  {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} := nanofil_irisGS registry wi ge.
End HelloJoinBase.

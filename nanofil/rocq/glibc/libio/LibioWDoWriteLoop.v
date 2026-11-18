(** The wide flush `c: _IO_wdo_write` converts the wide characters of a
    stream's buffer into bytes and writes them to the descriptor:

    ```
    do {
      if (fp->_IO_buf_end - fp->_IO_write_ptr < sizeof (mb_buf))
        { write_ptr = write_base = mb_buf; buf_end = mb_buf + sizeof (mb_buf); }
      else
        { write_ptr = fp->_IO_write_ptr; write_base = fp->_IO_write_base;
          buf_end = fp->_IO_buf_end; }
      result = __libio_codecvt_out (cc, &fp->_wide_data->_IO_state, data,
                                    data + to_do, &new_data, write_ptr, buf_end,
                                    &write_ptr);
      if (_IO_new_do_write (fp, write_base, write_ptr - write_base) == EOF)
        return WEOF;
      to_do -= new_data - data;
      if (result != __codecvt_ok && (result != __codecvt_partial || new_data - data == 0))
        break;
      data = new_data;
    } while (to_do > 0);
    ```

    Before converting the first character, the flush writes out any
    pending bytes if the narrow buffer is full. Each pass converts into
    that buffer if it has at least sixteen bytes free. Otherwise the
    pass converts into a sixteen-byte array on the stack. In either
    case it writes the bytes from the chosen buffer to the descriptor. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics GlibcSymFunc.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic VariadicLogic.
From Glibc Require Import CodePrelude HelloImageCode125 Fix OsBlocks OsWorld OsRegistry SysCode FileInv FileIdle
  LibioLogic LibioReadCode LibioDoWriteCode LibioPutsInv LibioCloseSteps LibioWIdle LibioWXsputnWindow
  LibioWXsputnRoom LibioWOverflowWrite LibioWDoWriteStream LibioWDoWriteTail CBlocks SysWrappers.
Module WdVL := VariadicLogicOn R LG0.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps WdVL.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation objp b := (mkPtr b (Obj b)).

(* Calls borrow whole fields. Frame those fields without searching inside
   the descriptors and pointer cells for individual bytes. *)
Local Typeclasses Opaque iconv_cell pcell icell bytes auxes live.

(** To read the conversion instructions that Hello actually runs, we
    look up the function in its linked image. *)
Definition codecvt_out_fn := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_125])) "__libio_codecvt_out".

(** ## The wide characters as words

    The conversion reads the wide buffer as a list of 32-bit words, but
    the stream owns that buffer as a list of bytes. Any four bytes are
    the little-endian encoding of some word, so the bytes of a whole
    number of characters always read as a list of words. *)

Local Lemma split256 a X : 0 <= a < 256 -> (a + 256 * X) mod 256 = a /\ (a + 256 * X) / 256 = X.
Proof.
  intros. rewrite (Z.mul_comm 256). split.
  - rewrite Z.mod_add; [apply Z.mod_small|]; lia.
  - rewrite Z.div_add; [rewrite Z.div_small; lia|lia].
Qed.

(** Four bytes are the encoding of the word they spell. *)
Lemma le_bytes_word a b c d : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  le_bytes (of_bytes [a; b; c; d]) 4 = [a; b; c; d].
Proof.
  intros Ha Hb Hc Hd. unfold le_bytes, of_bytes, byte_of. cbn.
  change (2 ^ (8 * 0%nat)) with 1. change (2 ^ (8 * 1%nat)) with 256.
  change (2 ^ (8 * 2%nat)) with (256 * 256). change (2 ^ (8 * 3%nat)) with (256 * 256 * 256).
  rewrite <- !Z.div_div by lia. rewrite Z.div_1_r.
  destruct (split256 a (b + 256 * (c + 256 * (d + 0))) Ha) as [-> ->].
  destruct (split256 b (c + 256 * (d + 0)) Hb) as [-> ->].
  destruct (split256 c (d + 0) Hc) as [-> ->]. rewrite Z.add_0_r Z.mod_small; [done|lia].
Qed.

(** The bytes of n characters are the encoding of n words. *)
Lemma bytes_words n xs : length xs = (4 * n)%nat -> Forall (fun x => 0 <= x < 256) xs ->
  ∃ ws, length ws = n /\ Forall (fun c => 0 <= c < 2 ^ 32) ws /\ xs = flat_map (fun c => le_bytes c 4) ws.
Proof.
  revert xs. induction n as [|n IH]; intros xs L V.
  - destruct xs; [|discriminate]. exists []. done.
  - do 4 (destruct xs as [|? xs]; [cbn in L; lia|]). cbn [length] in L.
    assert (L' : length xs = (4 * n)%nat) by lia.
    apply Forall_cons_1 in V as [Va V]. apply Forall_cons_1 in V as [Vb V].
    apply Forall_cons_1 in V as [Vc V]. apply Forall_cons_1 in V as [Vd V].
    destruct (IH xs L' V) as (ws & Lw & Vw & ->).
    exists (of_bytes [z; z0; z1; z2] :: ws). split; [cbn; lia|]. split.
    + constructor; [|exact Vw]. unfold of_bytes. cbn. lia.
    + cbn [flat_map]. rewrite le_bytes_word //.
Qed.

Section view.
Context `{!gen_heapGS piece pval Σ}.

(** Two lives that one owner holds belong to two objects. *)
Lemma live_ne b reg b' reg' : live b reg -∗ live b' reg' -∗ ⌜b <> b'⌝.
Proof using Type.
  rewrite /live /pts !big_sepL_cons. iIntros "[Hl _] [Hs _]".
  iDestruct (pointsto_ne with "Hl Hs") as %Hne. iPureIntro. intros <-. apply Hne. reflexivity.
Qed.

(** The conversion reads r characters of the wide buffer from index c.
    For a heap buffer they lie in that buffer's own object, and for the
    short buffer they lie inside the wide data object. Either way the
    flush lends the converter the bytes as words and gets them back
    unchanged. *)
Lemma wide_source wd wr w sbs c r :
  0 < wd -> wd + 232 <= r_end wr -> r_end wr <= 2 ^ 63 -> length sbs = 4%nat -> Forall (fun x => 0 <= x < 256) sbs ->
  0 <= c -> 0 < r -> c + r <= window_size w ->
  live wd wr -∗ wbuf_idle w -∗ bytes wd woff_shortbuf sbs -∗
  ∃ sb so sreg ws, ⌜wpos wd w c = mkPtr (sb + so) (Obj sb) /\ Z.of_nat (length ws) = r /\
      Forall (fun x => 0 <= x < 2 ^ 32) ws /\ 0 < sb /\ 0 <= so /\ sb + so + 4 * r <= r_end sreg /\
      r_end sreg <= 2 ^ 63 /\ (sb = wd -> sreg = wr)⌝ ∗
    live wd wr ∗ (if decide (sb = wd) then True else live sb sreg) ∗ bytes sb so (flat_map (fun x => le_bytes x 4) ws) ∗
    (live wd wr -∗ (if decide (sb = wd) then True else live sb sreg) -∗ bytes sb so (flat_map (fun x => le_bytes x 4) ws) -∗
     live wd wr ∗ wbuf_idle w ∗ bytes wd woff_shortbuf sbs).
Proof using Type.
  intros Hwd Hwe Hwr Ls Vs Hc Hr Hcr. iIntros "Hwl Hwb Hsb".
  destruct w as [| |wb wsz]; cbn [window_size] in Hcr; [lia| |].
  - assert (c = 0) as -> by lia. assert (r = 1) as -> by lia.
    destruct (bytes_words 1 sbs ltac:(lia) Vs) as (ws & Lw & Vw & Ew).
    iExists wd, woff_shortbuf, wr, ws. rewrite decide_True //. rewrite -Ew. iFrame "Hwl Hsb".
    iSplit. { iPureIntro. unfold wpos, window_base, woff_shortbuf. cbn [ptr_addr ptr_cap]. split_and!; try lia; try done.
      f_equal. lia. }
    iIntros "Hwl _ Hsb". iFrame.
  - iDestruct "Hwb" as (wreg xs cs (Hk & He & Hre & Hb0 & Ha & Hsz & Hm4 & Lx & Vx & Lc)) "(Hl & Hxs & Hcs)".
    pose proof (Z.div_mod wsz 4 ltac:(lia)) as Dm.
    iDestruct (live_ne with "Hwl Hl") as %Hne.
    rewrite -(take_drop (Z.to_nat (4 * c)) xs). iDestruct (bytes_app with "Hxs") as "[Hx0 Hx]".
    rewrite -(take_drop (Z.to_nat (4 * r)) (drop _ xs)). iDestruct (bytes_app with "Hx") as "[Hx Hx2]".
    assert (L1 : length (take (Z.to_nat (4 * c)) xs) = Z.to_nat (4 * c)) by (rewrite length_take; lia).
    assert (L2 : length (take (Z.to_nat (4 * r)) (drop (Z.to_nat (4 * c)) xs)) = (4 * Z.to_nat r)%nat)
      by (rewrite length_take length_drop; lia).
    destruct (bytes_words (Z.to_nat r) _ L2 ltac:(apply Forall_take, Forall_drop, Vx)) as (ws & Lw & Vw & Ew).
    iExists wb, (4 * c), wreg, ws. rewrite decide_False //. rewrite L1 Z2Nat.id; [|lia]. rewrite -Ew.
    iFrame "Hwl Hl Hx". iSplit.
    { iPureIntro. unfold wpos, window_base. cbn [ptr_addr ptr_cap]. split_and!; try lia; try done; intros ->; congruence. }
    iIntros "Hwl Hl Hx". iFrame "Hwl Hsb". iExists wreg, xs, cs. iSplit; [done|]. iFrame "Hl Hcs".
    iEval (rewrite -(take_drop (Z.to_nat (4 * c)) xs) bytes_app).
    iEval (rewrite -(take_drop (Z.to_nat (4 * r)) (drop (Z.to_nat (4 * c)) xs)) bytes_app).
    rewrite L1 Z2Nat.id; [|lia]. iEval (rewrite -(Z.add_0_l (4 * c))) in "Hx". iFrame.
Qed.

(** The cursor that the converter hands back points into the wide
    buffer, so loading it needs the life of the buffer's object. That
    life is the wide data object's own for the short buffer and the
    heap buffer's for a heap one. *)
Lemma wide_base_life vb tw tm wd w wr ps s0 : ptr_cap (window_base wd w) = Obj s0 ->
  wide_data_at vb tw tm wd w wr ps -∗ ∃ sreg, live s0 sreg ∗ (live s0 sreg -∗ wide_data_at vb tw tm wd w wr ps).
Proof using Type.
  intros Hc. iIntros "(%ib & %ie & %ob & %oe & %ifl & %ic & %ofl & %oc & %sb & %sc & %H & Hl & Hps & Hst & Ha & Hin & Hout & Hsb & Hpad & Hsc & Hvt & Hb)".
  destruct w as [| |wb wsz]; cbn in Hc; try discriminate Hc; injection Hc as <-.
  - iExists wr. iSplitL "Hl"; [iExact "Hl"|]. iIntros "Hl".
    iExists ib, ie, ob, oe, ifl, ic, ofl, oc, sb, sc. iSplitR; [done|]. iSplitL "Hl"; [iExact "Hl"|]. iSplitL "Hps"; [iExact "Hps"|]. iSplitL "Hst"; [iExact "Hst"|].
    iSplitL "Ha"; [iExact "Ha"|]. iSplitL "Hin"; [iExact "Hin"|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "Hsb"; [iExact "Hsb"|].
    iSplitL "Hpad"; [iExact "Hpad"|]. iSplitL "Hsc"; [iExact "Hsc"|]. iSplitL "Hvt"; [iExact "Hvt"|]. iExact "Hb".
  - iDestruct "Hb" as (wreg xs cs Hb) "(Hwl & Hxs & Hcs)". iExists wreg. iSplitL "Hwl"; [iExact "Hwl"|]. iIntros "Hwl".
    iExists ib, ie, ob, oe, ifl, ic, ofl, oc, sb, sc. iSplitR; [done|]. iSplitL "Hl"; [iExact "Hl"|]. iSplitL "Hps"; [iExact "Hps"|]. iSplitL "Hst"; [iExact "Hst"|].
    iSplitL "Ha"; [iExact "Ha"|]. iSplitL "Hin"; [iExact "Hin"|]. iSplitL "Hout"; [iExact "Hout"|]. iSplitL "Hsb"; [iExact "Hsb"|].
    iSplitL "Hpad"; [iExact "Hpad"|]. iSplitL "Hsc"; [iExact "Hsc"|]. iSplitL "Hvt"; [iExact "Hvt"|].
    iExists wreg, xs, cs. iSplitR; [done|]. iSplitL "Hwl"; [iExact "Hwl"|]. iSplitL "Hxs"; [iExact "Hxs"|]. iExact "Hcs".
Qed.

(** The pass counts the characters the converter consumed by dividing
    the distance its source cursor moved by four. The lemma
    [consumed_quot] says that this machine arithmetic gives back the
    count k when the cursor stays within the address space. *)
Lemma consumed_quot q k : 0 < q -> 0 <= k -> q + 4 * k <= 2 ^ 63 ->
  (if sign_extension (2 ^ 64) (2 ^ 63) (4 mod 2 ^ 64) =? 0 then 0 else
   (sign_extension (2 ^ 64) (2 ^ 63) ((((q + 4 * k) mod 2 ^ 64 - q mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)
     ÷ sign_extension (2 ^ 64) (2 ^ 63) (4 mod 2 ^ 64)) mod 2 ^ 64) = k.
Proof.
  intros Hq Hk Hb. change (sign_extension (2 ^ 64) (2 ^ 63) (4 mod 2 ^ 64)) with 4. cbn [Z.eqb].
  rewrite (Z.mod_small (q + 4 * k)); [|lia]. rewrite (Z.mod_small q); [|lia].
  replace (q + 4 * k - q) with (4 * k) by lia. rewrite !(Z.mod_small (4 * k)); try lia.
  assert (sign_extension (2 ^ 64) (2 ^ 63) (4 * k) = 4 * k) as ->.
  { unfold sign_extension. rewrite (Z.mod_small (4 * k)); [|lia]. destruct (Z.leb_spec (2 ^ 63) (4 * k)); lia. }
  rewrite Z.mul_comm. rewrite Z.quot_mul; [|lia]. apply Z.mod_small; lia.
Qed.

End view.

Section loop.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The conversion

    The conversion function `c: __libio_codecvt_out` turns wide
    characters into bytes through the stream's output descriptor. Its
    proof belongs to another file, so this section takes its rule as a
    hypothesis. The rule reads the characters from a borrowed source,
    writes bytes into a borrowed destination, and reports how many
    characters it consumed and how many bytes it produced. *)

(** The rule [codecvt_out_rule] CR L says that the conversion runs
    safely with the persistent read-only tables CR and the locale L. It
    consumes k of the n characters ws and produces j of the m bytes of
    the destination, whose other bytes may also change. Its result is 0
    when it converted everything, 1 when it ran out of room, and 2 on
    an illegal character. *)
Definition codecvt_out_rule (CR L : iProp Σ) : Prop :=
  forall fr tm wd wreg ob oe fl cnt sb sreg dq sc so ws tb treg to xs nb nreg n0 tpb tpreg t0 Φ,
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length xs) in
  call_frame codecvt_out_fn [WPtr (mkPtr (wd + woff_cd_in) (Obj wd)); WPtr (mkPtr (wd + woff_state) (Obj wd));
    WPtr (mkPtr (sb + so) sc); WPtr (mkPtr (sb + so + 4 * n) sc); WPtr (mkPtr nb (Obj nb));
    WPtr (mkPtr (tb + to) (Obj tb)); WPtr (mkPtr (tb + to + m) (Obj tb)); WPtr (mkPtr tpb (Obj tpb))] = Some fr ->
  lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) = Some tm ->
  fl = 9 \/ fl = Z.lor 9 (2 ^ 30) ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  (sc = Obj sb \/ sc = Ro sb) -> 0 < sb -> 0 <= so -> sb + so + 4 * n <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  (sb = wd -> sreg = wreg) -> Forall (fun c => 0 <= c < 2 ^ 32) ws ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2 ^ 63 -> Forall (fun x => 0 <= x < 256) xs ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 < tpb -> tpb mod 8 = 0 -> tpb + 8 <= r_end tpreg -> r_end tpreg <= 2 ^ 63 ->
  ⊢ CR -∗ L -∗ live wd wreg -∗ iconv_cell wd woff_cd_out tm ob oe fl cnt -∗
    bytes wd woff_state (replicate 16 0) -∗ (if decide (sb = wd) then True else liveq dq sb sreg) -∗
    bytesq dq sb so (flat_map (fun c => le_bytes c 4) ws) -∗ live tb treg -∗ bytes tb to xs -∗
    live nb nreg -∗ pcell nb 0 n0 -∗ live tpb tpreg -∗ pcell tpb 0 t0 -∗
    ▷ (∀ k j zs res ob' oe' fl' cnt',
         ⌜0 <= k <= n /\ length zs = length xs /\ 0 <= j <= m /\ Forall (fun z => 0 <= z < 256) zs /\
          (res = 0 \/ res = 1 \/ res = 2) /\ (fl' = fl \/ fl' = Z.lor fl (2 ^ 30))⌝ -∗
       L -∗ live wd wreg -∗ iconv_cell wd woff_cd_out tm ob' oe' fl' cnt' -∗
       bytes wd woff_state (replicate 16 0) -∗ (if decide (sb = wd) then True else liveq dq sb sreg) -∗
       bytesq dq sb so (flat_map (fun c => le_bytes c 4) ws) -∗ live tb treg -∗ bytes tb to zs -∗
       live nb nreg -∗ pcell nb 0 (mkPtr (sb + so + 4 * k) sc) -∗
       live tpb tpreg -∗ pcell tpb 0 (mkPtr (tb + to + j) (Obj tb)) -∗ Φ (Ret (WInt res))) -∗
    WP (ERun fr : sexpr) {{ Φ }}.

Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__GI___write" glibc___libc_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).
Context `{Hdw : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write} `{Hcvf : !Defines ge "__libio_codecvt_out" codecvt_out_fn}.
Context (CR L : iProp Σ) `{!Persistent CR} (Hcv : codecvt_out_rule CR L).
Context (fd vb fb : Z) (vr freg : region) (eb wd : Z) (w : wbuf) (tw tm : ptr).
Context (Hfd : In fd (ow_fds w0)) (Herr : ow_errno w0 = Some (objp eb)).
Local Abbreviation ok st nb := (wide_file_ok ge vb (objp fb) fd fb freg st nb wd w tw tm).

(** ## What the flush promises

    The flush returns 0 when it wrote every character and `c: WEOF`
    otherwise. Either way the caller gets back the same stream with the
    same lock, buffers and descriptors. The wide pointers either stay
    as they were or mark an empty buffer; after success they always
    mark an empty one. *)

(** The predicate [wdo_post] lk nb wr i j Φ is the caller's continuation
    for a flush of the stream with the lock lk, the narrow buffer nb
    and the wide data region wr. *)
Definition wdo_post (lk : ptr) (nb : nbuf) (wr : region) (i j : Z) (Φ : outcome -> iProp Σ) : iProp Σ :=
  ∀ r st k j', ⌜(r = 0 \/ r = 2 ^ 32 - 1) /\ ok st nb /\ fs_lock st = lk /\
      0 <= k <= window_size w /\ 0 <= j' <= window_size w /\ (r = 0 -> k = 0)⌝ -∗
    L -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗
    wide_data_at vb tw tm wd w wr (window_slots wd w k j') -∗ Φ (Ret (WInt r)).

(** Every way out of the flush ends in block `c: L12` with the count r
    of characters it did not convert. The lemma [wp_wdo_exit] runs that
    tail from the stream's fields and hands the caller the result. *)
Lemma wp_wdo_exit nb lk wr i j e r st Φ :
  window_bound w -> 0 <= i <= window_size w -> 0 <= j <= window_size w ->
  reg e "v0" (WPtr (objp fb)) -> reg e "chk0" (WPtr (mkPtr (fb + 152) (Obj fb))) -> reg e "pr.2" (WInt r) ->
  0 <= r < 2 ^ 64 -> ok st nb -> fs_lock st = lk ->
  L -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗
  wide_data_at vb tw tm wd w wr (window_slots wd w i j) -∗ wdo_post lk nb wr i j Φ -∗
  WP (ERun (mkFrame wdo_write_fn e [] None (body_at wdo_write_fn "L12")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros B Hi Hj Rv0 Rc0 Rr2 Hr H Hlk.
  iIntros "HL Herr Hf Hfields Hnb Hwide HK".
  pose proof H as (_ & Hal & Hfb & Hend & Hfreg & F & I & Hm & Hvtb & Bp & S & U & Hwd & Hcd & Htwl & Html & Hnw).
  unfold file_size in Hend.
  iDestruct "Hfields" as "(%Lp & Hfl & Hps & Hfdc & Hfl2 & Hold & %Lc & Hcol & Hlk & Hoff & Hcvp & Hwdp & Hfrl & Hfrb & Hmd & Htw & Hvtp)".
  iDestruct "Hwide" as (ib ie ob oe ifl icnt ofl ocnt sb scs Hw) "(Hwl & Hws & Hst & Hsta & Hin & Hout & Hsb & Hpad & Hscs & Hwvtp & Hwb)".
  pose proof Hw as (Hw0 & Hwa & Hwe & Hwr & _ & Hifl & Hofl & Lsb & Vsb & Lscs).
  iEval (rewrite Hwd) in "Hwdp".
  iApply (wp_wdo_tail _ fb freg wd wr w i j r (fs_flags st) with "Hf Hfl Hwdp Hwl [Hws] Hwb");
    try first [reflexivity | lia | assumption].
  { destruct F; lia. }
  { iExact "Hws". }
  iNext. iIntros (j' Hj') "Hf Hfl Hwdp Hwl Hws Hwb".
  iApply ("HK" $! _ st 0 j' with "[%] HL Herr Hf [-Hnb Hws Hwl Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb] Hnb [Hws Hwl Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb]").
  { split_and!; try first [assumption | reflexivity | lia]. destruct (r =? 0); [left|right]; reflexivity. }
  { iEval (rewrite -Hwd) in "Hwdp". iFrame. done. }
  iExists ib, ie, ob, oe, ifl, icnt, ofl, ocnt, sb, scs. iFrame. iPureIntro. split_and!; try assumption.
  apply window_ptrs_ok; [assumption|lia|lia].
Qed.

(** ## The loop

    The flush converts its characters a batch at a time, and each batch
    is one pass of a loop. A pass starts at block `c: L60` with r of the
    i characters still to convert. It keeps the stream, the wide data
    and the three stack objects of the flush: the cell for the
    converter's source cursor, the sixteen-byte array mb_buf, and the
    cell for its destination cursor. *)

(** The predicate [loop_regs] says what the registers hold when a pass
    begins. *)
Definition loop_regs (e : list (name * word)) (a64 mb a67 i r : Z) : Prop :=
  reg e "v0" (WPtr (objp fb)) /\ reg e "chk0" (WPtr (mkPtr (fb + 152) (Obj fb))) /\
  reg e "chk2" (WPtr (mkPtr (fb + 40) (Obj fb))) /\ reg e "v9" (WPtr (mkPtr (wd + 104) (Obj wd))) /\
  reg e "v64" (WPtr (objp a64)) /\ reg e "v65" (WPtr (objp mb)) /\ reg e "v67" (WPtr (objp a67)) /\
  reg e "pr.3" (WInt r) /\ reg e "pr.1" (WPtr (wpos wd w (i - r))).

(** The predicate [loop_stack] owns the three stack objects of the
    flush, whatever they hold. *)
Definition loop_stack (a64 : Z) (r64 : region) (mb : Z) (rmb : region) (a67 : Z) (r67 : region) : iProp Σ :=
  live a64 r64 ∗ (∃ p, pcell a64 0 p) ∗ live mb rmb ∗
  (∃ ys, ⌜length ys = 16%nat /\ Forall (fun y => 0 <= y < 256) ys⌝ ∗ bytes mb 0 ys) ∗
  live a67 r67 ∗ (∃ p, pcell a67 0 p).

(** If a pass leaves characters to convert, the next pass needs the
    same buffers but starts at the new source cursor. The proof uses
    [[later-modality|Löb induction]] to apply this rule again there. *)
Definition loop_wp nb lk wr i j a64 r64 mb rmb a67 r67 Φ : iProp Σ :=
  ∀ e r st, ⌜loop_regs e a64 mb a67 i r /\ 0 < r <= i /\ ok st nb /\ fs_lock st = lk⌝ -∗
    L -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗
    wide_data_at vb tw tm wd w wr (window_slots wd w i j) -∗ loop_stack a64 r64 mb rmb a67 r67 -∗
    ▷ wdo_post lk nb wr i j Φ -∗
    WP (ERun (mkFrame wdo_write_fn e [] None (body_at wdo_write_fn "L60")) : sexpr) {{ Φ }}.

(** After the narrow write succeeds, the pass counts the characters the
    converter consumed and decides whether to go round again. It stops
    when no characters remain, when the converter failed, or when it ran
    out of room without consuming anything. *)
Lemma wp_wdo_next nb lk wr i j a64 r64 mb rmb a67 r67 Φ e r st s0 so k res :
  window_bound w -> 0 < i <= window_size w -> 0 <= j <= window_size w ->
  0 < a64 -> a64 mod 8 = 0 -> a64 + 8 <= r_end r64 -> r_end r64 <= 2 ^ 63 ->
  loop_regs e a64 mb a67 i r -> 0 < r <= i -> ok st nb -> fs_lock st = lk ->
  reg e "v104" (WInt res) -> (res = 0 \/ res = 1 \/ res = 2) -> 0 <= k <= r ->
  wpos wd w (i - r) = mkPtr (s0 + so) (Obj s0) -> 0 < s0 -> 0 <= so -> s0 + so + 4 * r <= 2 ^ 63 ->
  L -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗
  wide_data_at vb tw tm wd w wr (window_slots wd w i j) -∗
  live a64 r64 -∗ pcell a64 0 (mkPtr (s0 + so + 4 * k) (Obj s0)) -∗ live mb rmb -∗
  (∃ ys, ⌜length ys = 16%nat /\ Forall (fun y => 0 <= y < 256) ys⌝ ∗ bytes mb 0 ys) -∗
  live a67 r67 -∗ (∃ p, pcell a67 0 p) -∗
  ▷ wdo_post lk nb wr i j Φ -∗ ▷ loop_wp nb lk wr i j a64 r64 mb rmb a67 r67 Φ -∗
  WP (ERun (mkFrame wdo_write_fn e [] None (body_at wdo_write_fn "L107")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros B Hi Hj H64 A64 E64 R64 Hregs Hr H Hlk Hres Hres3 Hk Hsrc Hs0 Hso Hse.
  iIntros "HL Herr Hf Hfields Hnb Hwide H64 C64 Hmb Bmb H67 C67 HK IH".
  destruct Hregs as (Rv0 & Rc0 & Rc2 & Rv9 & Q64 & Qmb & Q67 & Rr & Rd).
  body_start wdo_write_fn "L107"%string.
  assert (Hcap : ptr_cap (window_base wd w) = Obj s0) by (pose proof (f_equal ptr_cap Hsrc) as Hc; exact Hc).
  assert (Ha : ptr_addr (window_base wd w) + 4 * (i - r) = s0 + so) by exact (f_equal ptr_addr Hsrc).
  iDestruct (wide_base_life vb tw tm wd w wr _ s0 Hcap with "Hwide") as (sreg) "[Hsl Hback]".
  check "H64". load "H64" "C64" "Hsl". step. step. step. step. step. step.
  rewrite Ha. rewrite consumed_quot; [|lia..]. rewrite (Z.mod_small r); [|lia]. rewrite (Z.mod_small k); [|lia]. rewrite (Z.mod_small (r - k)); [|lia].
  destruct Hres3 as [-> | [-> | ->]].
  - branch. step. branch. step.
    load "H64" "C64" "Hsl". step.
    destruct (Z.eq_dec k r) as [-> | Hkr].
    { rewrite Z.sub_diag. branch. step.
      iApply (wp_wdo_exit nb lk wr i j _ 0 st with "HL Herr Hf Hfields Hnb [Hback Hsl] HK");
        try first [lia | assumption | (lookups; first [reflexivity | eassumption])].
      iApply ("Hback" with "Hsl"). }
    rewrite (Z.mod_small (r - k)); [|lia]. rewrite Zmod_0_l.
    replace (0 <? r - k) with true by (symmetry; apply Z.ltb_lt; lia). branch. step.
    iApply ("IH" $! _ (r - k) st with "[%] HL Herr Hf Hfields Hnb [Hback Hsl] [H64 C64 Hmb Bmb H67 C67] HK").
    { rewrite (Z.mod_small (r - k)); [|lia]. unfold loop_regs. split_and!; try (lookups; first [reflexivity | eassumption]); try lia.
      lookups. unfold wpos. cbv zeta. rewrite Hcap. do 3 f_equal. lia. }
    { iApply ("Hback" with "Hsl"). }
    iFrame "H64 Hmb H67 Bmb C67". iExists _. iExact "C64".
  - branch. step. step. branch. step. load "H64" "C64" "Hsl". step. step. step. step.
    rewrite consumed_quot; [|lia..]. step. step. destruct (Z.eq_dec k 0) as [-> | Hk0].
    + branch. step.
      iApply (wp_wdo_exit nb lk wr i j _ ((r - 0) mod 2 ^ 64) st with "HL Herr Hf Hfields Hnb [Hback Hsl] HK");
        try first [lia | assumption | (lookups; first [reflexivity | eassumption]) | (apply Z.mod_pos_bound; lia)].
      iApply ("Hback" with "Hsl").
    + rewrite (Z.mod_small k); [|lia]. rewrite Zmod_0_l. rewrite (proj2 (Z.eqb_neq k 0) Hk0). branch. step.
      load "H64" "C64" "Hsl". step.
      destruct (Z.eq_dec k r) as [-> | Hkr].
      { rewrite Z.sub_diag. branch. step.
        iApply (wp_wdo_exit nb lk wr i j _ 0 st with "HL Herr Hf Hfields Hnb [Hback Hsl] HK");
          try first [lia | assumption | (lookups; first [reflexivity | eassumption])].
        iApply ("Hback" with "Hsl"). }
      rewrite (Z.mod_small (r - k)); [|lia]. rewrite Zmod_0_l.
      replace (0 <? r - k) with true by (symmetry; apply Z.ltb_lt; lia). branch. step.
      iApply ("IH" $! _ (r - k) st with "[%] HL Herr Hf Hfields Hnb [Hback Hsl] [H64 C64 Hmb Bmb H67 C67] HK").
      { rewrite (Z.mod_small (r - k)); [|lia]. unfold loop_regs. split_and!; try (lookups; first [reflexivity | eassumption]); try lia.
        lookups. unfold wpos. cbv zeta. rewrite Hcap. do 3 f_equal. lia. }
      { iApply ("Hback" with "Hsl"). }
      iFrame "H64 Hmb H67 Bmb C67". iExists _. iExact "C64".
  - branch. step. step. branch. step. branch. step.
    iApply (wp_wdo_exit nb lk wr i j _ ((r - k) mod 2 ^ 64) st with "HL Herr Hf Hfields Hnb [Hback Hsl] HK");
      try first [lia | assumption | (lookups; first [reflexivity | eassumption]) | (apply Z.mod_pos_bound; lia)].
    iApply ("Hback" with "Hsl").
Qed.

(** The loop runs from its head to the end of the flush. *)
Lemma wp_wdo_loop nb lk wr i j a64 r64 mb rmb a67 r67 Φ :
  window_bound w -> 0 < i <= window_size w -> 0 <= j <= window_size w ->
  0 < a64 -> a64 mod 8 = 0 -> a64 + 8 <= r_end r64 -> r_end r64 <= 2 ^ 63 ->
  0 < mb -> mb + 16 <= r_end rmb -> r_end rmb <= 2 ^ 63 ->
  0 < a67 -> a67 mod 8 = 0 -> a67 + 8 <= r_end r67 -> r_end r67 <= 2 ^ 63 ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ CR -∗
  ∀ e r st, ⌜loop_regs e a64 mb a67 i r /\ 0 < r <= i /\ ok st nb /\ fs_lock st = lk⌝ -∗
    L -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗ buf_idle nb -∗
    wide_data_at vb tw tm wd w wr (window_slots wd w i j) -∗ loop_stack a64 r64 mb rmb a67 r67 -∗
    ▷ wdo_post lk nb wr i j Φ -∗
    WP (ERun (mkFrame wdo_write_fn e [] None (body_at wdo_write_fn "L60")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros B Hi Hj H64 A64 E64 R64 Hmb Emb Rmb H67 A67 E67 R67.
  iIntros "#Hvt #Hwvt #HCR". iLöb as "IH".
  iIntros (e r st (Hregs & Hr & H & Hlk)) "HL Herr Hf Hfields Hnb Hwide Hstack HK".
  destruct Hregs as (Rv0 & Rc0 & Rc2 & Rv9 & Q64 & Qmb & Q67 & Rr & Rd).
  pose proof H as (_ & Hal & Hfb & Hend & Hfreg & F & I & Hm & Hvtb & Bp & S & U & Hwd & Hcd & Htwl & Html & Hnw).
  unfold file_size in Hend.
  iDestruct "Hfields" as "(%Lp & Hfl & Hps & Hfdc & Hfl2 & Hold & %Lc & Hcol & Hlk & Hoff & Hcvp & Hwdp & Hfrl & Hfrb & Hmd & Htw & Hvtp)".
  pose proof I as (_ & Hfdeq & _ & _ & _ & _ & E01 & E13 & L34 & Hput & _ & Happ & _ & Hf2 & _ & Hcol0 & _).
  pose proof S as (Hnwp & Snb). pose proof Bp as Bp'.
  unfold with_mode0, fs_ptr in *. cbn [fs_flags fs_flags2 fs_fileno fs_column fs_ptrs] in *.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps;
    try discriminate Lp.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  body_start wdo_write_fn "L60"%string.
  destruct nb as [| |bb sz|b]; [exfalso; rewrite (Hnw eq_refl) in Hi; cbn in Hi; lia| | |iDestruct "Hnb" as "[]"].
  - cbn [buf_ptrs_ok nth take] in Bp'. destruct Bp' as (E6 & E7 & Hall). destruct Snb as (Hub & E43 & E36). cbn [nth] in E43, E36, E13, E01.
    clear E01. rewrite E36 in E13, E43. subst p1 p4 p3 p6 p7.
    step. check "Hf".
    iDestruct "Hstack" as "(H64 & [%c64 C64] & Hmb & (%ys & %Hys & Bmb) & H67 & [%c67 C67])".
    load_self_using wp_raw_load_pointer_self "Hf P7". step. check "Hf". load_self_using wp_raw_load_pointer_self "Hf P4".
    step. step. step. step. branch_as false. step. check "H67". store "H67" "C67". step. step.
    iDestruct "Hwide" as (ib ie ob oe ifl icnt ofl ocnt sb scs Hw) "(Hwl & Hws & Hst & Hsta & Hin & Hout & Hsb & Hpad & Hscs & Hwvtp & Hwb)".
    pose proof Hw as (Hw0 & Hwa & Hwe & Hwr & _ & Hifl & Hofl & Lsb & Vsb & Lscs).
    iEval (rewrite Hwd) in "Hwdp".
    step. step. check "Hf". load "Hf" "Hwdp" "Hwl". step. step. step. check "H67". load "H67" "C67" "Hmb".
    iDestruct (wide_source wd wr w sb (i - r) r Hw0 Hwe Hwr Lsb Vsb ltac:(lia) ltac:(lia) ltac:(lia) with "Hwl Hwb Hsb")
    as (s0 so sreg ws (Hsrc & Lws & Vws & Hs0 & Hso & Hse & Hsr & Hsw)) "(Hwl & Hsl & Hsx & Hback)".
    rewrite Hsrc. norm.
    change (2 ^ (2 mod 64)) with 4. norm.
    iApply wp_call_bind; [vx | exact Hcvf | reflexivity |]. iNext.
    iApply (Hcv _ tm wd wr ob oe ofl ocnt s0 sreg (DfracOwn 1) (Obj s0) so ws mb rmb 0 ys a64 r64 c64 a67 r67 (objp mb)
    with "HCR HL Hwl Hout Hst Hsl Hsx Hmb Bmb H64 C64 H67 C67").
    { rewrite Hsrc Lws (proj1 Hys) !Z.add_0_r (Z.mul_comm 4 r). reflexivity. }
    { exact Html. }
    { destruct Hofl as [-> | ->]; [left|right]; reflexivity. }
    all: try first [lia | assumption | (left; reflexivity) | (destruct Hys; lia) | (apply Hys)].
    iNext. iIntros (k jj zs res ob' oe' fl' cnt' (Hk & Lzs & Hjj & Vzs & Hres & Hfl')) "HL Hwl Hout Hst Hsl Hsx Hmb Bmb H64 C64 H67 C67".
    resume. check "H67". load "H67" "C67" "Hmb". step. step. step. norm.
    assert (jj <= 16) by (destruct Hys as [Ly _]; lia). rewrite Z.add_0_r. norm.
    replace (mb + jj - mb) with jj by lia.
    iDestruct ("Hback" with "Hwl Hsl Hsx") as "(Hwl & Hwb & Hsb)".
    iAssert (file_fields fb st) with "[Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfdc Hfl2 Hold Hcol Hlk Hoff Hcvp Hwdp Hfrl Hfrb Hmd Htw Hvtp]" as "Hfields".
    { rewrite /file_fields Hps Hwd. cbn [big_opL]. iFrame. done. }
    iAssert (wide_data_at vb tw tm wd w wr (window_slots wd w i j)) with "[Hwl Hws Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb]" as "Hwide".
    { iExists ib, ie, ob', oe', ifl, icnt, fl', cnt', sb, scs. iFrame. iPureIntro. split_and!; try assumption.
    - apply window_ptrs_ok; [assumption|lia|lia].
    - destruct Hofl as [-> | ->], Hfl' as [-> | ->]; [left|right|right|right]; reflexivity. }
    iDestruct (bytes_take_drop _ _ zs (Z.to_nat jj) with "Bmb") as "[Bmb Bmb2]"; [lia|].
    iApply wp_call_bind; [vx | exact Hdw | reflexivity |]. iNext.
    iApply (wp_wnarrow_short Hreg Hext Hfw fd vb fb vr freg eb wd w tw tm Hfd Herr _ st mb rmb 0 (take (Z.to_nat jj) zs)
    with "Hvt Hwvt Herr Hf Hfields Hmb Bmb").
    { replace (Z.of_nat (length (take (Z.to_nat jj) zs))) with jj by (rewrite length_take; lia). rewrite Z.add_0_r (Z.mod_small jj (2 ^ 64)); [reflexivity|lia]. }
    { exact H. }
    all: try (rewrite length_take; lia). all: try lia. { apply Forall_take, Vzs. }
    iNext. iIntros (r' st' (Hr' & H' & Hlk')) "Herr Hf Hfields Hmb Bmb". resume. step.
    iDestruct (bytes_take_drop _ _ zs (Z.to_nat jj) with "[$Bmb $Bmb2]") as "Bmb"; [lia|].
    destruct Hr' as [-> | ->].
    + branch. step. rewrite (Z.mod_small res (2 ^ 32)); [|lia].
    iApply (wp_wdo_next NbShort lk wr i j a64 r64 mb rmb a67 r67 Φ _ r st' s0 so k res
      with "HL Herr Hf Hfields Hnb Hwide H64 C64 Hmb [Bmb] H67 [C67] HK IH");
      try first [lia | assumption | (rewrite Hlk'; assumption)].
    { split_and!; try (lookups; first [reflexivity | eassumption]); lia. }
    { lookups. reflexivity. }
    { iExists zs. iFrame "Bmb". iPureIntro. split; [lia|exact Vzs]. }
    { iExists _. iExact "C67". }
    + branch. step.
    iApply wp_ret; [reflexivity | vx |]; iNext.
    lazymatch goal with |- environments.envs_entails _ (_ (Ret (WInt ?x))) => let y := eval vm_compute in x in change x with y end.
    change (WInt 4294967295) with (WInt (2 ^ 32 - 1)).
    iApply ("HK" $! _ st' i j with "[%] HL Herr Hf Hfields Hnb Hwide").
    split_and!; try first [right; reflexivity | assumption | lia | congruence].
  - cbn [buf_ptrs_ok nth take] in Bp'. destruct Bp' as (E6 & E7 & Hall). destruct Snb as (Hub & E26 & E36).
    cbn [nth] in E26, E36, E13, E01. subst p6 p7. subst p2 p3.
    subst p1. subst p0. cbn [nth] in L34, Hput. simpl in L34, Hput.
    pose proof (proj1 (Forall_forall _ _) Hall p4 ltac:(cbn; tauto)) as (C4 & A4).
    destruct p4 as [a4 c4]. cbn [ptr_addr ptr_cap] in C4, A4, L34, Hput. subst c4.
    iDestruct "Hnb" as (breg xs cs (Hbk & Hbe & Hbr & Hbb & Hba & Hsz & Lxs & Vxs & Lcs)) "(Hbl & Hxs & Hcs)".
    step. check "Hf".
    iDestruct "Hstack" as "(H64 & [%c64 C64] & Hmb & (%ys & %Hys & Bmb) & H67 & [%c67 C67])".
    load "Hf" "P7" "Hbl". step. check "Hf". load "Hf" "P4" "Hbl".
    step. step. step. step.
    rewrite (Z.mod_small (bb + sz)); [|lia]. rewrite (Z.mod_small a4); [|lia]. rewrite !(Z.mod_small (bb + sz - a4)); [|lia..].
    change (16 mod 2 ^ 64) with 16. iEval (cbn [ptr_cap live_cap]) in "Hbl".
    destruct (Z.ltb_spec (bb + sz - a4) 16) as [Hlt | Hge].
    + branch. step. check "H67". store "H67" "C67". step. step.
      iDestruct "Hwide" as (ib ie ob oe ifl icnt ofl ocnt sb scs Hw) "(Hwl & Hws & Hst & Hsta & Hin & Hout & Hsb & Hpad & Hscs & Hwvtp & Hwb)".
      pose proof Hw as (Hw0 & Hwa & Hwe & Hwr & _ & Hifl & Hofl & Lsb & Vsb & Lscs).
      iEval (rewrite Hwd) in "Hwdp".
      step. step. check "Hf". load "Hf" "Hwdp" "Hwl". step. step. step. check "H67". load "H67" "C67" "Hmb".
      iDestruct (wide_source wd wr w sb (i - r) r Hw0 Hwe Hwr Lsb Vsb ltac:(lia) ltac:(lia) ltac:(lia) with "Hwl Hwb Hsb")
        as (s0 so sreg ws (Hsrc & Lws & Vws & Hs0 & Hso & Hse & Hsr & Hsw)) "(Hwl & Hsl & Hsx & Hback)".
      rewrite Hsrc. norm.
      change (2 ^ (2 mod 64)) with 4. norm.
      iApply wp_call_bind; [vx | exact Hcvf | reflexivity |]. iNext.
      iApply (Hcv _ tm wd wr ob oe ofl ocnt s0 sreg (DfracOwn 1) (Obj s0) so ws mb rmb 0 ys a64 r64 c64 a67 r67 (objp mb)
        with "HCR HL Hwl Hout Hst Hsl Hsx Hmb Bmb H64 C64 H67 C67").
      { rewrite Hsrc Lws (proj1 Hys) !Z.add_0_r (Z.mul_comm 4 r). reflexivity. }
      { exact Html. }
      { destruct Hofl as [-> | ->]; [left|right]; reflexivity. }
      all: try first [lia | assumption | (left; reflexivity) | (destruct Hys; lia) | (apply Hys)].
      iNext. iIntros (k jj zs res ob' oe' fl' cnt' (Hk & Lzs & Hjj & Vzs & Hres & Hfl')) "HL Hwl Hout Hst Hsl Hsx Hmb Bmb H64 C64 H67 C67".
      resume. check "H67". load "H67" "C67" "Hmb". step. step. step. norm.
      assert (jj <= 16) by (destruct Hys as [Ly _]; lia). rewrite Z.add_0_r. norm.
      replace (mb + jj - mb) with jj by lia.
      iDestruct ("Hback" with "Hwl Hsl Hsx") as "(Hwl & Hwb & Hsb)".
      iAssert (file_fields fb st) with "[Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfdc Hfl2 Hold Hcol Hlk Hoff Hcvp Hwdp Hfrl Hfrb Hmd Htw Hvtp]" as "Hfields".
      { rewrite /file_fields Hps Hwd. cbn [big_opL]. iFrame. done. }
      iAssert (wide_data_at vb tw tm wd w wr (window_slots wd w i j)) with "[Hwl Hws Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb]" as "Hwide".
      { iExists ib, ie, ob', oe', ifl, icnt, fl', cnt', sb, scs. iFrame. iPureIntro. split_and!; try assumption.
        - apply window_ptrs_ok; [assumption|lia|lia].
        - destruct Hofl as [-> | ->], Hfl' as [-> | ->]; [left|right|right|right]; reflexivity. }
      iDestruct (bytes_take_drop _ _ zs (Z.to_nat jj) with "Bmb") as "[Bmb Bmb2]"; [lia|].
      iDestruct (live_ne with "Hmb Hbl") as %Hmbb.
      iApply wp_call_bind; [vx | exact Hdw | reflexivity |]. iNext.
      iApply (wp_wnarrow_heap Hreg Hext Hfw fd vb fb vr freg eb wd w tw tm Hfd Herr _ st bb sz breg mb rmb 0 (take (Z.to_nat jj) zs)
        with "Hvt Hwvt Herr Hf Hfields Hbl [Hmb] Bmb").
      { replace (Z.of_nat (length (take (Z.to_nat jj) zs))) with jj by (rewrite length_take; lia). rewrite Z.add_0_r (Z.mod_small jj (2 ^ 64)); [reflexivity|lia]. }
      { exact H. }
      all: try (rewrite length_take; lia). all: try first [lia | (intros; lia)]. { apply Forall_take, Vzs. }
      { rewrite decide_False //. }
      iNext. iIntros (r' st' (Hr' & H' & Hlk')) "Herr Hf Hfields Hbl Hmb Bmb". resume. step.
      iEval (rewrite decide_False //) in "Hmb".
      iDestruct (bytes_take_drop _ _ zs (Z.to_nat jj) with "[$Bmb $Bmb2]") as "Bmb"; [lia|].
      iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hxs Hcs]" as "Hnb".
      { iExists breg, xs, cs. iFrame. iPureIntro. split_and!; assumption. }
      destruct Hr' as [-> | ->].
      * branch. step. rewrite (Z.mod_small res (2 ^ 32)); [|lia].
        iApply (wp_wdo_next (NbHeap bb sz) lk wr i j a64 r64 mb rmb a67 r67 Φ _ r st' s0 so k res
          with "HL Herr Hf Hfields Hnb Hwide H64 C64 Hmb [Bmb] H67 [C67] HK IH");
          try first [lia | assumption | (rewrite Hlk'; assumption)].
        { split_and!; try (lookups; first [reflexivity | eassumption]); lia. }
        { lookups. reflexivity. }
        { iExists zs. iFrame "Bmb". iPureIntro. split; [lia|exact Vzs]. }
        { iExists _. iExact "C67". }
      * branch. step.
        iApply wp_ret; [reflexivity | vx |]; iNext.
        lazymatch goal with |- environments.envs_entails _ (_ (Ret (WInt ?x))) => let y := eval vm_compute in x in change x with y end.
        change (WInt 4294967295) with (WInt (2 ^ 32 - 1)).
        iApply ("HK" $! _ st' i j with "[%] HL Herr Hf Hfields Hnb Hwide").
        split_and!; try first [right; reflexivity | assumption | lia | congruence].
    + branch. step. step. load "Hf" "P4" "Hbl". check "H67". store "H67" "C67". step.
      iEval (cbn [ptr_cap live_cap]) in "Hbl". check "Hf". load "Hf" "P3" "Hbl". step. check "Hf". load "Hf" "P7" "Hbl". step. step.
      iDestruct "Hwide" as (ib ie ob oe ifl icnt ofl ocnt sb scs Hw) "(Hwl & Hws & Hst & Hsta & Hin & Hout & Hsb & Hpad & Hscs & Hwvtp & Hwb)".
      pose proof Hw as (Hw0 & Hwa & Hwe & Hwr & _ & Hifl & Hofl & Lsb & Vsb & Lscs).
      iEval (rewrite Hwd) in "Hwdp".
      step. check "Hf". load "Hf" "Hwdp" "Hwl". step. step. step. check "H67". load "H67" "C67" "Hbl".
      iDestruct (wide_source wd wr w sb (i - r) r Hw0 Hwe Hwr Lsb Vsb ltac:(lia) ltac:(lia) ltac:(lia) with "Hwl Hwb Hsb")
        as (s0 so sreg ws (Hsrc & Lws & Vws & Hs0 & Hso & Hse & Hsr & Hsw)) "(Hwl & Hsl & Hsx & Hback)".
      rewrite Hsrc. norm.
      change (2 ^ (2 mod 64)) with 4. norm.
      iDestruct (bytes_take_drop _ _ xs (Z.to_nat (a4 - bb)) with "Hxs") as "[Hx0 Hx1]"; [lia|].
      rewrite Z2Nat.id; [|lia]. rewrite Z.add_0_l.
      iApply wp_call_bind; [vx | exact Hcvf | reflexivity |]. iNext.
      iApply (Hcv _ tm wd wr ob oe ofl ocnt s0 sreg (DfracOwn 1) (Obj s0) so ws bb breg (a4 - bb) (drop (Z.to_nat (a4 - bb)) xs)
          a64 r64 c64 a67 r67 (mkPtr a4 (Obj bb))
        with "HCR HL Hwl Hout Hst Hsl Hsx Hbl Hx1 H64 C64 H67 C67").
      { rewrite Hsrc Lws length_drop Lxs. replace (bb + (a4 - bb)) with a4 by lia.
        replace (a4 + Z.of_nat (Z.to_nat sz - Z.to_nat (a4 - bb))) with (bb + sz) by lia.
        rewrite (Z.mul_comm 4 r). reflexivity. }
      { exact Html. }
      { destruct Hofl as [-> | ->]; [left|right]; reflexivity. }
      all: try first [lia | assumption | (left; reflexivity) | (apply Forall_drop; exact Vxs) | (rewrite length_drop; lia)].
      iNext. iIntros (k jj zs res ob' oe' fl' cnt' (Hk & Lzs & Hjj & Vzs & Hres & Hfl')) "HL Hwl Hout Hst Hsl Hsx Hbl Hx1 H64 C64 H67 C67".
      rewrite length_drop Lxs in Hjj Lzs.
      resume. check "H67". load "H67" "C67" "Hbl". step. step. step. norm.
      replace (bb + (a4 - bb) + jj - bb) with (a4 - bb + jj) by lia.
      iDestruct ("Hback" with "Hwl Hsl Hsx") as "(Hwl & Hwb & Hsb)".
      iAssert (file_fields fb st) with "[Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfdc Hfl2 Hold Hcol Hlk Hoff Hcvp Hwdp Hfrl Hfrb Hmd Htw Hvtp]" as "Hfields".
      { rewrite /file_fields Hps Hwd. cbn [big_opL]. iFrame. done. }
      iAssert (wide_data_at vb tw tm wd w wr (window_slots wd w i j)) with "[Hwl Hws Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb]" as "Hwide".
      { iExists ib, ie, ob', oe', ifl, icnt, fl', cnt', sb, scs. iFrame. iPureIntro. split_and!; try assumption.
        - apply window_ptrs_ok; [assumption|lia|lia].
        - destruct Hofl as [-> | ->], Hfl' as [-> | ->]; [left|right|right|right]; reflexivity. }
      iDestruct (bytes_take_drop _ _ zs (Z.to_nat jj) with "Hx1") as "[Hz0 Hz1]"; [lia|].
      assert (Lold : length (take (Z.to_nat (a4 - bb)) xs) = Z.to_nat (a4 - bb))
        by (apply length_take_le; clear -A4 Lxs; lia).
      assert (Lnew : length (take (Z.to_nat jj) zs) = Z.to_nat jj)
        by (apply length_take_le; clear -Hjj Lzs; lia).
      iDestruct (bytes_app _ _ (take (Z.to_nat (a4 - bb)) xs) (take (Z.to_nat jj) zs) with "[Hx0 Hz0]") as "Hw".
      { iFrame "Hx0". rewrite Lold Z.add_0_l Z2Nat.id; [iExact "Hz0"|lia]. }
      iApply wp_call_bind; [vx | exact Hdw | reflexivity |]. iNext.
      iApply (wp_wnarrow_heap Hreg Hext Hfw fd vb fb vr freg eb wd w tw tm Hfd Herr _ st bb sz breg bb breg 0
          (take (Z.to_nat (a4 - bb)) xs ++ take (Z.to_nat jj) zs)
        with "Hvt Hwvt Herr Hf Hfields Hbl [] Hw").
      { rewrite length_app Lold Lnew Nat2Z.inj_add !Z2Nat.id Z.add_0_r; try lia.
        rewrite (Z.mod_small (a4 - bb + jj) (2 ^ 64)); [reflexivity|lia]. }
      { exact H. }
      all: try (rewrite length_app Lold Lnew; lia). all: try first [lia | (intros; reflexivity)].
      { apply Forall_app; split; apply Forall_take; assumption. }
      { rewrite decide_True //. }
      iNext. iIntros (r' st' (Hr' & H' & Hlk')) "Herr Hf Hfields Hbl _ Hw". resume. step.
      iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hw Hz1 Hcs]" as "Hnb".
      { iExists breg, ((take (Z.to_nat (a4 - bb)) xs ++ take (Z.to_nat jj) zs) ++ drop (Z.to_nat jj) zs)%list, cs.
        iFrame "Hbl Hcs". iSplitR.
        { iPureIntro. split_and!; try assumption.
          - rewrite !length_app length_drop Lold Lnew. clear -Lzs Hjj A4 Lxs; lia.
          - apply Forall_app; split; [apply Forall_app; split; apply Forall_take; assumption|apply Forall_drop; assumption]. }
        iApply bytes_app. iFrame "Hw". rewrite length_app Lold Lnew Nat2Z.inj_add Z.add_0_l (Z2Nat.id (a4 - bb)); [|lia].
        iExact "Hz1". }
      destruct Hr' as [-> | ->].
      * branch. step. rewrite (Z.mod_small res (2 ^ 32)); [|lia].
        iApply (wp_wdo_next (NbHeap bb sz) lk wr i j a64 r64 mb rmb a67 r67 Φ _ r st' s0 so k res
          with "HL Herr Hf Hfields Hnb Hwide H64 C64 Hmb [Bmb] H67 [C67] HK IH");
          try first [lia | assumption | (rewrite Hlk'; assumption)].
        { split_and!; try (lookups; first [reflexivity | eassumption]); lia. }
        { lookups. reflexivity. }
        { iExists ys. iFrame "Bmb". iPureIntro. exact Hys. }
        { iExists _. iExact "C67". }
      * branch. step.
        iApply wp_ret; [reflexivity | vx |]; iNext.
        lazymatch goal with |- environments.envs_entails _ (_ (Ret (WInt ?x))) => let y := eval vm_compute in x in change x with y end.
        change (WInt 4294967295) with (WInt (2 ^ 32 - 1)).
        iApply ("HK" $! _ st' i j with "[%] HL Herr Hf Hfields Hnb Hwide").
        split_and!; try first [right; reflexivity | assumption | lia | congruence].
Qed.

(** The rule [wp_wdo_write] is the whole flush of i characters from
    the base of the wide buffer. The caller holds the stream's fields and
    does not need its lock. The flush may first write the pending narrow
    bytes, and then runs the loop. *)
Lemma wp_wdo_write fr st nb wr i j Φ :
  call_frame wdo_write_fn [WPtr (objp fb); WPtr (window_base wd w); WInt i] = Some fr ->
  ok st nb -> window_bound w -> 0 <= i <= window_size w -> 0 <= j <= window_size w ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ CR -∗ L -∗ errno_any eb -∗ live fb freg -∗ file_fields fb st -∗
  buf_idle nb -∗ wide_data_at vb tw tm wd w wr (window_slots wd w i j) -∗
  ▷ wdo_post (fs_lock st) nb wr i j Φ -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr H B Hi Hj. injection Hfr as <-.
  iIntros "#Hvt #Hwvt #HCR HL Herr Hf Hfields Hnb Hwide HK".
  step.
  Local Ltac alloc b H := iApply wp_alloc; [vm_compute; reflexivity|vm_compute; congruence|vm_compute; congruence|
    intros ? ? ? ? Hfresh Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hfresh Hw)|]; iNext; iIntros (b H) "Hobj".
  alloc a64 Ha64. iDestruct (obj_zero_block with "Hobj") as "(H64 & Hb & Ha)"; [vm_compute; congruence|].
  iEval (change (Z.to_nat (req_extent (heap_req 8 8))) with (8 + 8)%nat) in "Hb Ha".
  iDestruct (zero_cell_prefix a64 0 8 with "Hb Ha") as "(C64 & _ & _)".
  alloc mb Hmb. iDestruct (obj_zero_block with "Hobj") as "(Hmb & Bmb & _)"; [vm_compute; congruence|].
  alloc a67 Ha67. iDestruct (obj_zero_block with "Hobj") as "(H67 & Hb & Ha)"; [vm_compute; congruence|].
  iEval (change (Z.to_nat (req_extent (heap_req 8 8))) with (8 + 8)%nat) in "Hb Ha".
  iDestruct (zero_cell_prefix a67 0 8 with "Hb Ha") as "(C67 & _ & _)".
  cbv [req_extent heap_req req_align req_kind] in Ha64, Hmb, Ha67.
  pose proof H as (_ & Hal & Hfb & Hend & Hfreg & F & I & Hm & Hvtb & Bp & S & U & Hwd & Hcd & Htwl & Html & Hnw).
  unfold file_size in Hend.
  iDestruct "Hfields" as "(%Lp & Hfl & Hps & Hfdc & Hfl2 & Hold & %Lc & Hcol & Hlk & Hoff & Hcvp & Hwdp & Hfrl & Hfrb & Hmd & Htw & Hvtp)".
  iDestruct "Hwide" as (ib ie ob oe ifl icnt ofl ocnt sb scs Hw) "(Hwl & Hws & Hst & Hsta & Hin & Hout & Hsb & Hpad & Hscs & Hwvtp & Hwb)".
  pose proof Hw as (Hw0 & Hwa & Hwe & Hwr & _ & Hifl & Hofl & Lsb & Vsb & Lscs).
  unfold woff_cd_in in Hcd. iEval (rewrite Hcd) in "Hcvp". iEval (rewrite Hwd) in "Hwdp".
  step. check "Hf". load "Hf" "Hcvp" "Hwl". step.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  { branch_as true. step.
    iApply (wp_wdo_tail _ fb freg wd wr w 0 j 0 (fs_flags st) with "Hf Hfl Hwdp Hwl [Hws] Hwb");
      try first [reflexivity | lia | assumption | (lookups; norm; reflexivity)].
    { destruct F; lia. }
    { iExact "Hws". }
    iNext. iIntros (j' Hj') "Hf Hfl Hwdp Hwl Hws Hwb".
    iApply ("HK" $! 0 st 0 j' with "[%] HL Herr Hf [-Hnb Hws Hwl Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb] Hnb [Hws Hwl Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb]").
    { split_and!; try first [left; reflexivity | assumption | reflexivity | lia]. }
    { rewrite /file_fields Hcd Hwd. by iFrame. }
    iExists ib, ie, ob, oe, ifl, icnt, ofl, ocnt, sb, scs. iFrame. iPureIntro. split_and!; try assumption.
    apply window_ptrs_ok; [assumption|lia|lia]. }
  assert (Hi63 : i < 2 ^ 62).
  { clear -Hi B. destruct w as [| |wb wsz]; cbn in Hi, B; try lia.
    assert (wsz / 4 <= wsz / 2) by (apply Z.div_le_compat_l; lia).
    assert (wsz / 2 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia. }
  change (req_extent (heap_req 8 8)) with 16 in *. change (req_extent (heap_req 4 16)) with 16 in *.
  iEval (change (req_extent (heap_req 8 8)) with 16) in "H64 H67". iEval (change (req_extent (heap_req 4 16)) with 16) in "Hmb Bmb".
  change (Z.to_nat 16) with 16%nat.
  pose proof I as (_ & Hfdeq & _ & _ & _ & _ & E01 & E13 & L34 & Hput & _ & Happ & _ & Hf2 & _ & Hcol0 & _).
  pose proof S as (Hnwp & Snb). pose proof Bp as Bp'.
  unfold with_mode0, fs_ptr in *. cbn [fs_flags fs_flags2 fs_fileno fs_column fs_ptrs] in *.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps;
    try discriminate Lp.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  rewrite (Z.mod_small i); [|lia]. change (0 mod 2 ^ 64) with 0.
  replace (0 <? i) with true by (symmetry; apply Z.ltb_lt; lia). branch. step.
  destruct Ha64 as (Ha64 & Ma64 & Ea64), Hmb as (Hmb0 & Mmb & Emb), Ha67 as (Ha67 & Ma67 & Ea67).
  change (8 `max` 16) with 16 in Ma64, Ma67. change (4 `max` 16) with 16 in Mmb.
  change ((8 + 15) / 16 * 16) with 16 in Ea64, Ea67. change ((16 + 15) / 16 * 16) with 16 in Emb.
  assert (A64 : a64 mod 8 = 0) by (clear -Ma64; apply Z.mod_divide in Ma64; [|lia]; apply Z.mod_divide; [lia|]; destruct Ma64 as [q ->]; exists (2 * q); lia).
  assert (A67 : a67 mod 8 = 0) by (clear -Ma67; apply Z.mod_divide in Ma67; [|lia]; apply Z.mod_divide; [lia|]; destruct Ma67 as [q ->]; exists (2 * q); lia).
  iAssert (wide_data_at vb tw tm wd w wr (window_slots wd w i j)) with
    "[Hwl Hws Hst Hsta Hin Hout Hsb Hpad Hscs Hwvtp Hwb]" as "Hwide".
  { iExists ib, ie, ob, oe, ifl, icnt, ofl, ocnt, sb, scs. by iFrame. }
  set (r64 := mkRegion a64 (a64 + 16) (req_kind (heap_req 8 8)) Live).
  set (rmb := mkRegion mb (mb + 16) (req_kind (heap_req 4 16)) Live).
  set (r67 := mkRegion a67 (a67 + 16) (req_kind (heap_req 8 8)) Live).
  iAssert (loop_stack a64 r64 mb rmb a67 r67) with "[H64 C64 Hmb Bmb H67 C67]" as "Hstack".
  { iFrame "H64 Hmb H67". iSplitL "C64"; [iExists _; iExact "C64"|]. iSplitL "Bmb"; [|iExists _; iExact "C67"].
    iExists _. iFrame "Bmb". iPureIntro. split; [reflexivity|apply Forall_replicate; lia]. }
  iPoseProof (wp_wdo_loop nb (fs_lock st) wr i j a64 r64 mb rmb a67 r67 Φ
    with "Hvt Hwvt HCR") as "Hloop"; try solve [assumption | cbn [r64 rmb r67 r_end]; lia].
  Local Ltac first_pass i :=
    rewrite (Z.mod_small i (2 ^ 64)); [|lia]; unfold loop_regs; split_and!;
    try (lookups; first [reflexivity | eassumption | (norm; reflexivity)]); try first [lia | assumption | congruence];
    lookups; rewrite Z.sub_diag wpos_zero; reflexivity.
  destruct nb as [| |bb sz|b]; [exfalso; rewrite (Hnw eq_refl) in Hi; cbn in Hi; lia| | |iDestruct "Hnb" as "[]"].
  - cbn [buf_ptrs_ok nth take] in Bp'. destruct Bp' as (E6 & E7 & Hall). destruct Snb as (Hub & E43 & E36). cbn [nth] in E43, E36, E13, E01.
    clear E01. rewrite E36 in E13, E43. subst p1 p4 p3 p6 p7.
    pose proof (proj1 (Forall_forall _ _) Hall p5 ltac:(cbn; tauto)) as (C5 & A5).
    destruct p5 as [a5 c5]. cbn [ptr_addr ptr_cap] in C5, A5. subst c5.
    step. check "Hf". load_self_using wp_raw_load_pointer_self "Hf P5". step. check "Hf". load_self_using wp_raw_load_pointer_self "Hf P4".
    step. step. step.
    destruct (Z.eq_dec a5 (fb + 131)) as [-> | Ha5];
      [ rewrite Z.eqb_refl; branch; step; step; load_self_using wp_raw_load_pointer_self "Hf P5"; step; check "Hf"; load_self_using wp_raw_load_pointer_self "Hf P3";
        step; step; step; step; step; rewrite Z.eqb_refl; branch; step
      | rewrite (Z.mod_small a5); [|lia]; rewrite (Z.mod_small (fb + 131)); [|lia]; rewrite (proj2 (Z.eqb_neq _ _) Ha5); branch; step; branch; step ].
    all: iApply ("Hloop" $! _ i st with "[%] HL Herr Hf [-Hnb Hwide Hstack HK] Hnb Hwide Hstack HK");
      [first_pass i | rewrite /file_fields Hps Hcd Hwd; cbn [big_opL]; by iFrame].
  - cbn [buf_ptrs_ok nth take] in Bp'. destruct Bp' as (E6 & E7 & Hall). destruct Snb as (Hub & E26 & E36).
    cbn [nth] in E26, E36, E13, E01. subst p6 p7. subst p2 p3. subst p1. subst p0.
    pose proof (proj1 (Forall_forall _ _) Hall p4 ltac:(cbn; tauto)) as (C4 & A4).
    destruct p4 as [a4 c4]. cbn [ptr_addr ptr_cap] in C4, A4. subst c4.
    pose proof (proj1 (Forall_forall _ _) Hall p5 ltac:(cbn; tauto)) as (C5 & A5).
    destruct p5 as [a5 c5]. cbn [ptr_addr ptr_cap] in C5, A5. subst c5.
    iDestruct "Hnb" as (breg xs cs (Hbk & Hbe & Hbr & Hbb & Hba & Hsz & Lxs & Vxs & Lcs)) "(Hbl & Hxs & Hcs)".
    step. check "Hf". load "Hf" "P5" "Hbl". iEval (cbn [ptr_cap live_cap]) in "Hbl".
    step. check "Hf". load "Hf" "P4" "Hbl". iEval (cbn [ptr_cap live_cap]) in "Hbl". step. step. step.
    rewrite (Z.mod_small a5 (2 ^ 64)); [|lia]. rewrite (Z.mod_small a4 (2 ^ 64)); [|lia].
    destruct (Z.eq_dec a5 a4) as [-> | Ha5].
    2: { rewrite (proj2 (Z.eqb_neq _ _) Ha5). branch. step. branch. step.
      iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hxs Hcs]" as "Hnb".
      { iExists breg, xs, cs. iFrame. iPureIntro. split_and!; assumption. }
      iApply ("Hloop" $! _ i st with "[%] HL Herr Hf [-Hnb Hwide Hstack HK] Hnb Hwide Hstack HK"); [first_pass i|].
      { rewrite /file_fields Hps Hcd Hwd. cbn [big_opL]. iFrame. done. }
    }
    rewrite Z.eqb_refl. branch. step. step. load "Hf" "P5" "Hbl". iEval (cbn [ptr_cap live_cap]) in "Hbl".
    step. check "Hf". load "Hf" "P3" "Hbl". step. step. step. step. step.
    rewrite (Z.mod_small a4 (2 ^ 64)); [|lia]. rewrite (Z.mod_small bb (2 ^ 64)); [|lia].
    destruct (Z.eq_dec a4 bb) as [-> | Ha4].
    { rewrite Z.eqb_refl. branch. step.
      iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hxs Hcs]" as "Hnb".
      { iExists breg, xs, cs. iFrame. iPureIntro. split_and!; assumption. }
      iApply ("Hloop" $! _ i st with "[%] HL Herr Hf [-Hnb Hwide Hstack HK] Hnb Hwide Hstack HK"); [first_pass i|].
      { rewrite /file_fields Hps Hcd Hwd. cbn [big_opL]. iFrame. done. }
    }
    rewrite (proj2 (Z.eqb_neq _ _) Ha4). branch. step. step. check "Hf". load "Hf" "P3" "Hbl". step.
    load "Hf" "P4" "Hbl". load "Hf" "P3" "Hbl". step. step. step. norm.
    iAssert (file_fields fb st) with "[Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfdc Hfl2 Hold Hcol Hlk Hoff Hcvp Hwdp Hfrl Hfrb Hmd Htw Hvtp]" as "Hfields".
    { rewrite /file_fields Hps Hcd Hwd. cbn [big_opL]. iFrame. done. }
    iDestruct (bytes_take_drop _ _ xs (Z.to_nat (a4 - bb)) with "Hxs") as "[Hx0 Hx1]"; [lia|].
    iApply wp_call_bind; [vx | exact Hdw | reflexivity |]. iNext.
    iApply (wp_wnarrow_heap Hreg Hext Hfw fd vb fb vr freg eb wd w tw tm Hfd Herr _ st bb sz breg bb breg 0
        (take (Z.to_nat (a4 - bb)) xs) with "Hvt Hwvt Herr Hf Hfields Hbl [] Hx0").
    { rewrite length_take Z.add_0_r. replace (Z.of_nat (Z.to_nat (a4 - bb) `min` length xs)) with (a4 - bb) by lia.
      rewrite (Z.mod_small (a4 - bb) (2 ^ 64)); [reflexivity|lia]. }
    { exact H. }
    all: try (rewrite length_take; lia). all: try first [lia | (intros; reflexivity)].
    { apply Forall_take; assumption. }
    { rewrite decide_True //. }
    iNext. iIntros (r' st' (Hr' & H' & Hlk')) "Herr Hf Hfields Hbl _ Hx0". resume. step.
    iDestruct (bytes_take_drop _ _ xs (Z.to_nat (a4 - bb)) with "[$Hx0 $Hx1]") as "Hxs"; [lia|].
    iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hxs Hcs]" as "Hnb".
    { iExists breg, xs, cs. iFrame. iPureIntro. split_and!; assumption. }
    destruct Hr' as [-> | ->].
    + branch. step.
      iApply ("Hloop" $! _ i st' with "[%] HL Herr Hf Hfields Hnb Hwide Hstack HK"). first_pass i.
    + branch. step.
      iApply wp_ret; [reflexivity | vx |]; iNext.
      lazymatch goal with |- environments.envs_entails _ (_ (Ret (WInt ?x))) => let y := eval vm_compute in x in change x with y end.
      change (WInt 4294967295) with (WInt (2 ^ 32 - 1)).
      iApply ("HK" $! _ st' i j with "[%] HL Herr Hf Hfields Hnb Hwide").
      { split_and!; try first [right; reflexivity | assumption | lia | congruence]. }
Qed.

End loop.

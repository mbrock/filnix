(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___GI___underflow : func :=
  mkFunc (a "__GI___underflow") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v24") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v24")]);
      (Let (a "v25") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v26") W (Cmp Eq W) [(t "v25"); (Const 0)])] (JBranch (t "v26") (To (a "L20")) (To (a "L22"))));
  (mkBlock (a "L20") [] [(Flight (a "v28") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk1") A (Renew 0 4 Write 1) [(t "chk0"); (t "v28")]);
      (RawStore Ww 0 (Const 4294967295) (t "chk1"))] (JGoto (To (a "L22"))));
  (mkBlock (a "L22") [] [(Flight (a "v31") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v32") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v55") W (Cmp Ne W) [(t "v32"); (Const 4294967295)])] (JBranch (t "v55") (To (a "L2")) (To (a "L4"))));
  (mkBlock (a "L2") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L4") [] [(Flight (a "v64") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v65") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v66") W (Cmp Eq W) [(t "v65"); (Const 0)])] (JBranch (t "v66") (To (a "L69")) (To (a "L62"))));
  (mkBlock (a "L69") [] [(Flight (a "v83") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v84") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v85") W (Cmp Eq W) [(t "v84"); (Const 0)])] (JBranch (t "v85") (To (a "L79")) (To (a "L81"))));
  (mkBlock (a "L79") [] [(Flight (a "v87") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "chk5") A (Renew 0 4 Write 1) [(t "chk0"); (t "v87")]);
      (RawStore Ww 0 (Const 4294967295) (t "chk5"))] (JGoto (To (a "L81"))));
  (mkBlock (a "L81") [] [(Flight (a "v90") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
      (Let (a "v91") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")])] (JGoto (To (a "L62"))));
  (mkBlock (a "L62") [] [(Let (a "chk7") A (HalfCheck Lower 0 4 Read 1) [(t "chk0"); (t "v0")]);
      (Let (a "v117") W (RawLoad (LdNarrow Sw) 0) [(t "chk7")]);
      (Let (a "v118") W And [(t "v117"); (Const 2048)])] (JBranch (t "v118") (To (a "L113")) (To (a "L115"))));
  (mkBlock (a "L113") [] [(Call (CResult (a "v123") W) (Global (a "__GI__IO_switch_to_get_mode")) [(Arg P (t "v0"))]);
      (Let (a "v125") W (Cmp Eq W) [(t "v123"); (Const 4294967295)])] (JBranch (t "v125") (To (a "L119")) (To (a "L115"))));
  (mkBlock (a "L119") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L115") [] [(Flight (a "v132") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk8") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v132")]);
      (Let (a "v133") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Flight (a "v135") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk9") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v135")]);
      (Let (a "v136") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Let (a "v137") L Ptoi [(t "v133")]);
      (Let (a "v138") L Ptoi [(t "v136")]);
      (Let (a "v139") W (Cmp Ult L) [(t "v137"); (t "v138")])] (JBranch (t "v139") (To (a "L128")) (To (a "L130"))));
  (mkBlock (a "L128") [] [(Flight (a "v141") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v142") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk11") A (Check 0 1 Read 1) [(t "v142")]);
      (Let (a "v143") W (RawLoad (LdNarrow Ub) 0) [(t "chk11")])] (JRet (t "v143")));
  (mkBlock (a "L130") [] [(Let (a "chk12") A (Renew 0 4 Read 1) [(t "chk7"); (t "v0")]);
      (Let (a "v149") W (RawLoad (LdNarrow Sw) 0) [(t "chk12")]);
      (Let (a "v150") W And [(t "v149"); (Const 256)])] (JBranch (t "v150") (To (a "L145")) (To (a "L147"))));
  (mkBlock (a "L145") [] [(Call CVoid (Global (a "_IO_switch_to_main_get_area")) [(Arg P (t "v0"))]);
      (Flight (a "v156") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk13") A (Renew 0 8 Read 8) [(t "chk8"); (t "v156")]);
      (Let (a "v157") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk13")]);
      (Flight (a "v159") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk14") A (Renew 0 8 Read 8) [(t "chk9"); (t "v159")]);
      (Let (a "v160") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Let (a "v161") L Ptoi [(t "v157")]);
      (Let (a "v162") L Ptoi [(t "v160")]);
      (Let (a "v163") W (Cmp Ult L) [(t "v161"); (t "v162")])] (JBranch (t "v163") (To (a "L152")) (To (a "L147"))));
  (mkBlock (a "L152") [] [(Flight (a "v165") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v166") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk13")]);
      (Let (a "chk16") A (Check 0 1 Read 1) [(t "v166")]);
      (Let (a "v167") W (RawLoad (LdNarrow Ub) 0) [(t "chk16")])] (JRet (t "v167")));
  (mkBlock (a "L147") [] [(Flight (a "v173") Add [(FAddress (t "v0")); (FValue (Const 96))] (LowerOf (t "v0")));
      (Let (a "chk17") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v173")]);
      (Let (a "v174") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk17")]);
      (Let (a "v175") L Ptoi [(t "v174")]);
      (Let (a "v176") L Ptoi [(Const 0)]);
      (Let (a "v177") W (Cmp Ne L) [(t "v175"); (t "v176")])] (JBranch (t "v177") (To (a "L169")) (To (a "L170"))));
  (mkBlock (a "L169") [] [(Flight (a "v183") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk18") A (Renew 0 8 Read 8) [(t "chk9"); (t "v183")]);
      (Let (a "v184") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk18")]);
      (Call (CResult (a "v185") W) (Global (a "glibc_genops#save_for_backup")) [(Arg P (t "v0")); (Arg P (t "v184"))])] (JBranch (t "v185") (To (a "L178")) (To (a "L171"))));
  (mkBlock (a "L178") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L170") [] [(Flight (a "v192") Add [(FAddress (t "v0")); (FValue (Const 80))] (LowerOf (t "v0")));
      (Let (a "chk19") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v192")]);
      (Let (a "v193") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk19")]);
      (Let (a "v194") L Ptoi [(t "v193")]);
      (Let (a "v196") W (Cmp Ne L) [(t "v194"); (t "v176")])] (JBranch (t "v196") (To (a "L188")) (To (a "L171"))));
  (mkBlock (a "L188") [] [(Call CVoid (Global (a "__GI__IO_free_backup_area")) [(Arg P (t "v0"))])] (JGoto (To (a "L171"))));
  (mkBlock (a "L171") [] [(Flight (a "v199") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "chk20") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v199")]);
      (Let (a "v200") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk20")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v200")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v202") Add [(FAddress (t "v200")); (FValue (Const 32))] (LowerOf (t "v200")));
      (Let (a "chk21") A (Check 0 8 Read 8) [(t "v202")]);
      (Let (a "v203") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Let (a "chk22") F CheckFunction [(t "v203")]);
      (RawCall (CResult (a "v205") W) (t "chk22") [(Arg P (t "v0"))])] (JRet (t "v205")))].

Definition hello_image_fn_glibc_iopopen'23unlock : func :=
  mkFunc (a "glibc_iopopen#unlock") (a "local") RVoid [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v8") P Copy [(Global (a "__libc_single_threaded_internal"))]);
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v8")]);
      (Let (a "v9") W (RawLoad (LdNarrow Sb) 0) [(t "chk0")]);
      (Let (a "v10") W (Cmp Ne W) [(t "v9"); (Const 0)])] (JBranch (t "v10") (To (a "L11")) (To (a "L12"))));
  (mkBlock (a "L11") [] [(Let (a "v13") P Copy [(Global (a "glibc_iopopen#proc_file_chain_lock"))]);
      (Flight (a "v14") Add [(FAddress (t "v13")); (FValue (Const 4))] (LowerOf (t "v13")));
      (Let (a "chk1") A (Check 0 4 Read 1) [(t "v14")]);
      (Let (a "v15") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Let (a "v16") W (Cmp Eq W) [(t "v15"); (Const 0)])] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [(Phi (a "v18") W [((a "start"), (Const 0)); ((a "L11"), (t "v16"))])] [] (JBranch (t "v18") (To (a "L5")) (To (a "L6"))));
  (mkBlock (a "L5") [] [(Let (a "v19") P Copy [(Global (a "glibc_iopopen#proc_file_chain_lock"))]);
      (Flight (a "v20") Add [(FAddress (t "v19")); (FValue (Const 8))] (LowerOf (t "v19")));
      (Let (a "chk2") A (Check 0 8 Write 8) [(t "v20")]);
      (RawStorePointer 0 (Const 0) (t "chk2") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v21") P Copy [(Global (a "glibc_iopopen#proc_file_chain_lock"))]);
      (Let (a "chk3") A (Check 0 4 Write 1) [(t "v21")]);
      (RawStore Ww 0 (Const 0) (t "chk3"))] (JGoto (To (a "L4"))));
  (mkBlock (a "L6") [] [(Let (a "v25") P Copy [(Global (a "glibc_iopopen#proc_file_chain_lock"))]);
      (Flight (a "v26") Add [(FAddress (t "v25")); (FValue (Const 4))] (LowerOf (t "v25")));
      (Let (a "chk4") A (Check 0 4 Read 1) [(t "v26")]);
      (Let (a "v27") W (RawLoad (LdNarrow Sw) 0) [(t "chk4")]);
      (Let (a "v28") W (Cmp Eq W) [(t "v27"); (Const 0)])] (JBranch (t "v28") (To (a "L22")) (To (a "L23"))));
  (mkBlock (a "L22") [] [(Let (a "v29") P Copy [(Global (a "glibc_iopopen#proc_file_chain_lock"))]);
      (Flight (a "v30") Add [(FAddress (t "v29")); (FValue (Const 8))] (LowerOf (t "v29")));
      (Let (a "chk5") A (Check 0 8 Write 8) [(t "v30")]);
      (RawStorePointer 0 (Const 0) (t "chk5") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "v32") P Copy [(Global (a "glibc_iopopen#proc_file_chain_lock"))]);
      (Let (a "chk6") A (Check 0 4 Read 1) [(t "v32")]);
      (Let (a "v36") W (RawLoad (LdNarrow Sw) 0) [(t "chk6")])] (JGoto (To (a "L37"))));
  (mkBlock (a "L37") [(Phi (a "v39") W [((a "L22"), (t "v36")); ((a "L37"), (t "v40"))])] [(Let (a "chk7") A (HalfCheck Lower 0 4 Write 4) [(t "chk6"); (t "v32")]);
      (Let (a "v40") W (RawCas (CasNarrow Sw) 0) [(t "chk7"); (t "v39"); (Const 0)]);
      (Let (a "v41") W (Cmp Eq W) [(t "v40"); (t "v39")])] (JBranch (t "v41") (To (a "L38")) (Poll (a "L37"))));
  (mkBlock (a "L38") [] [(Let (a "v46") W (Cmp Sgt W) [(t "v39"); (Const 1)])] (JBranch (t "v46") (To (a "L49")) (To (a "L4"))));
  (mkBlock (a "L49") [] [(Call CVoid (Global (a "__GI___lll_lock_wake_private")) [(Arg P (t "v32"))])] (JGoto (To (a "L4"))));
  (mkBlock (a "L23") [] [(Let (a "v60") P Copy [(Global (a "glibc_iopopen#proc_file_chain_lock"))]);
      (Flight (a "v61") Add [(FAddress (t "v60")); (FValue (Const 4))] (LowerOf (t "v60")));
      (Let (a "chk8") A (Check 0 4 Read 1) [(t "v61")]);
      (Let (a "v62") W (RawLoad (LdNarrow Sw) 0) [(t "chk8")]);
      (Let (a "v63") W Sub [(t "v62"); (Const 1)]);
      (Let (a "chk9") A (Renew 0 4 Write 1) [(t "chk8"); (t "v61")]);
      (RawStore Ww 0 (t "v63") (t "chk9"))] (JGoto (To (a "L4"))));
  (mkBlock (a "L4") [] [] JRetVoid)].

Definition hello_image_fn_glibc_unwind'23unwind_stop : func :=
  mkFunc (a "glibc_unwind#unwind_stop") (a "local") (RClass W) [(W, (a "v0")); (W, (a "v2")); (L, (a "v4")); (P, (a "v6")); (P, (a "v8")); (P, (a "v10"))] [(mkBlock (a "start") [] [(Call (CResult (a "v15") P) (Global (a "zthread_self_cookie")) []);
      (Flight (a "v18") Add [(FAddress (t "v15")); (FValue (Const 776))] (LowerOf (t "v15")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v18")]);
      (Let (a "v19") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Flight (a "v23") Add [(FAddress (t "v15")); (FValue (Const 1712))] (LowerOf (t "v15")));
      (Let (a "chk1") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v23")]);
      (Let (a "v24") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "v25") L Ptoi [(t "v24")]);
      (Flight (a "v27") Add [(FAddress (t "v15")); (FValue (Const 1720))] (LowerOf (t "v15")));
      (Let (a "chk2") A (HalfCheck Upper 0 8 Read 1) [(t "chk0"); (t "v27")]);
      (Let (a "v28") L (RawLoad LdL 0) [(t "chk2")]);
      (Let (a "v29") L Add [(t "v25"); (t "v28")]);
      (Let (a "v34") W And [(t "v2"); (Const 16)])] (JBranch (t "v34") (To (a "L36")) (To (a "L35"))));
  (mkBlock (a "L35") [] [(Call (CResult (a "v38") L) (Global (a "_Unwind_GetCFA")) [(Arg P (t "v8"))]);
      (Flight (a "v39") Copy [(FValue (t "v38"))] LowerNone);
      (Let (a "v40") L Ptoi [(t "v39")]);
      (Let (a "v42") L Sub [(t "v40"); (t "v29")]);
      (Let (a "chk3") A (Check 0 8 Read 8) [(t "v10")]);
      (Let (a "iw_1.iw_1.v3") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk3")]);
      (Call (CResult (a "iw_1.iw_1.v4") P) (Global (a "zget_jmp_buf_impl_frame")) [(Arg P (t "iw_1.iw_1.v3"))]);
      (Let (a "iw_1.v4") L Ptoi [(t "iw_1.iw_1.v4")]);
      (Let (a "v47") L Sub [(t "iw_1.v4"); (t "v29")]);
      (Let (a "v49") W (Cmp Uge L) [(t "v42"); (t "v47")])] (JGoto (To (a "L36"))));
  (mkBlock (a "L36") [(Phi (a "v51") W [((a "start"), (Const 1)); ((a "L35"), (t "v49"))])] [] (JBranch (t "v51") (To (a "L32")) (To (a "L31"))));
  (mkBlock (a "L31") [] [] (JGoto (To (a "L32"))));
  (mkBlock (a "L32") [(Phi (a "pr.1") W [((a "L31"), (Const 0)); ((a "L36"), (Const 1))])] [(Let (a "v59") L Ptoi [(t "v19")]);
      (Let (a "v61") W (Cmp Eq L) [(t "v59"); (Const 0)])] (JBranch (t "v61") (To (a "L54")) (To (a "L57"))));
  (mkBlock (a "L57") [] [(Let (a "v63") P Copy [(Global (a "glibc_unwind#str.287"))]);
      (Let (a "v64") P Copy [(Global (a "glibc_unwind#str.288"))]);
      (Let (a "v65") P Copy [(Global (a "glibc_unwind#str.289"))]);
      (Let (a "v66") P Copy [(Global (a "glibc_unwind#str.290"))]);
      (Call CVoid (Global (a "zerrorf")) [(Arg P (t "v63")); (Arg P (t "v64")); (Arg W (Const 64)); (Arg P (t "v65")); (Arg P (t "v66"))])] (JGoto (To (a "L54"))));
  (mkBlock (a "L54") [] [] (JBranch (t "pr.1") (To (a "L67")) (To (a "L69"))));
  (mkBlock (a "L67") [] [(Call CVoid (Global (a "__libc_longjmp")) [(Arg P (t "v10")); (Arg W (Const 1))])] (JGoto (To (a "L69"))));
  (mkBlock (a "L69") [] [] (JRet (Const 0)))].

Definition hello_image_fn_glibc_unwind'23unwind_cleanup : func :=
  mkFunc (a "glibc_unwind#unwind_cleanup") (a "local") RVoid [(W, (a "v0")); (P, (a "v2"))] [(mkBlock (a "start") [] [(Let (a "v4") P Copy [(Global (a "glibc_unwind#str.291"))]);
      (Call CVoid (Global (a "__GI___libc_fatal")) [(Arg P (t "v4"))])] JRetVoid)].

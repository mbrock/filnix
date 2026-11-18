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

Definition hello_image_fn___GI___uflow : func :=
  mkFunc (a "__GI___uflow") (a "export") (RClass W) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Flight (a "v24") Add [(FAddress (t "v0")); (FValue (Const 192))] (LowerOf (t "v0")));
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
      (Flight (a "v143") Add [(FAddress (t "v142")); (FValue (Const 1))] (LowerOf (t "v142")));
      (Let (a "chk11") A (Renew 0 8 Write 8) [(t "chk8"); (t "v141")]);
      (RawStorePointer 0 (t "v143") (t "chk11") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk12") A (Check 0 1 Read 1) [(t "v142")]);
      (Let (a "v144") W (RawLoad (LdNarrow Ub) 0) [(t "chk12")])] (JRet (t "v144")));
  (mkBlock (a "L130") [] [(Let (a "chk13") A (Renew 0 4 Read 1) [(t "chk7"); (t "v0")]);
      (Let (a "v150") W (RawLoad (LdNarrow Sw) 0) [(t "chk13")]);
      (Let (a "v151") W And [(t "v150"); (Const 256)])] (JBranch (t "v151") (To (a "L146")) (To (a "L148"))));
  (mkBlock (a "L146") [] [(Call CVoid (Global (a "_IO_switch_to_main_get_area")) [(Arg P (t "v0"))]);
      (Flight (a "v157") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "chk14") A (Renew 0 8 Read 8) [(t "chk8"); (t "v157")]);
      (Let (a "v158") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Flight (a "v160") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk15") A (Renew 0 8 Read 8) [(t "chk9"); (t "v160")]);
      (Let (a "v161") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk15")]);
      (Let (a "v162") L Ptoi [(t "v158")]);
      (Let (a "v163") L Ptoi [(t "v161")]);
      (Let (a "v164") W (Cmp Ult L) [(t "v162"); (t "v163")])] (JBranch (t "v164") (To (a "L153")) (To (a "L148"))));
  (mkBlock (a "L153") [] [(Flight (a "v166") Add [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
      (Let (a "v167") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk14")]);
      (Flight (a "v168") Add [(FAddress (t "v167")); (FValue (Const 1))] (LowerOf (t "v167")));
      (Let (a "chk17") A (Renew 0 8 Write 8) [(t "chk8"); (t "v166")]);
      (RawStorePointer 0 (t "v168") (t "chk17") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk18") A (Check 0 1 Read 1) [(t "v167")]);
      (Let (a "v169") W (RawLoad (LdNarrow Ub) 0) [(t "chk18")])] (JRet (t "v169")));
  (mkBlock (a "L148") [] [(Flight (a "v175") Add [(FAddress (t "v0")); (FValue (Const 96))] (LowerOf (t "v0")));
      (Let (a "chk19") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v175")]);
      (Let (a "v176") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk19")]);
      (Let (a "v177") L Ptoi [(t "v176")]);
      (Let (a "v178") L Ptoi [(Const 0)]);
      (Let (a "v179") W (Cmp Ne L) [(t "v177"); (t "v178")])] (JBranch (t "v179") (To (a "L171")) (To (a "L172"))));
  (mkBlock (a "L171") [] [(Flight (a "v185") Add [(FAddress (t "v0")); (FValue (Const 16))] (LowerOf (t "v0")));
      (Let (a "chk20") A (Renew 0 8 Read 8) [(t "chk9"); (t "v185")]);
      (Let (a "v186") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk20")]);
      (Call (CResult (a "v187") W) (Global (a "glibc_genops#save_for_backup")) [(Arg P (t "v0")); (Arg P (t "v186"))])] (JBranch (t "v187") (To (a "L180")) (To (a "L173"))));
  (mkBlock (a "L180") [] [] (JRet (Const 4294967295)));
  (mkBlock (a "L172") [] [(Flight (a "v194") Add [(FAddress (t "v0")); (FValue (Const 80))] (LowerOf (t "v0")));
      (Let (a "chk21") A (HalfCheck Lower 0 8 Read 8) [(t "chk0"); (t "v194")]);
      (Let (a "v195") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk21")]);
      (Let (a "v196") L Ptoi [(t "v195")]);
      (Let (a "v198") W (Cmp Ne L) [(t "v196"); (t "v178")])] (JBranch (t "v198") (To (a "L190")) (To (a "L173"))));
  (mkBlock (a "L190") [] [(Call CVoid (Global (a "__GI__IO_free_backup_area")) [(Arg P (t "v0"))])] (JGoto (To (a "L173"))));
  (mkBlock (a "L173") [] [(Flight (a "v201") Add [(FAddress (t "v0")); (FValue (Const 216))] (LowerOf (t "v0")));
      (Let (a "chk22") A (HalfCheck Upper 0 8 Read 8) [(t "chk0"); (t "v201")]);
      (Let (a "v202") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk22")]);
      (Let (a "iw_1.v4") L Ptoi [(t "v202")]);
      (Let (a "iw_1.v7") P Copy [(Global (a "__io_vtables"))]);
      (Let (a "iw_1.v8") L Ptoi [(t "iw_1.v7")]);
      (Let (a "iw_1.v9") L Sub [(t "iw_1.v4"); (t "iw_1.v8")]);
      (Let (a "iw_1.v15") W (Cmp Uge L) [(t "iw_1.v9"); (Const 2352)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L10")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L10") [] [(Call CVoid (Global (a "_IO_vtable_check")) [])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [] [(Flight (a "v204") Add [(FAddress (t "v202")); (FValue (Const 40))] (LowerOf (t "v202")));
      (Let (a "chk23") A (Check 0 8 Read 8) [(t "v204")]);
      (Let (a "v205") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk23")]);
      (Let (a "chk24") F CheckFunction [(t "v205")]);
      (RawCall (CResult (a "v207") W) (t "chk24") [(Arg P (t "v0"))])] (JRet (t "v207")))].
